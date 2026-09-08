import GFNBounds

/-!
# The fact extractor

Walks the environment and writes `docs/lean-facts.json`: for every declaration of every
`GFNBounds.*` module, its kind, module, line, pretty-printed type, docstring, the axioms it
rests on, and — the point of the exercise — the **project declarations its proof term actually
invokes**, from `Expr.getUsedConstants`.

That last field is ground truth about how the development proves what it proves, and it is what
`scripts/appendix.py --lint` checks the written proof sketches against: a sketch may not cite a
lemma the proof does not use, and may not silently omit one it does.

Dependencies from the *type* and from the *value* are kept apart. A theorem's type is its
statement, so its constants are vocabulary; its value is the proof, so its constants are the
argument.

Run by `make appendix`, through `lake env lean scripts/lean_facts.lean`.
-/

open Lean Meta

namespace LeanFacts

/-- The project namespace. Everything outside it is Mathlib or core, and is counted, not named. -/
def proj : Name := `GFNBounds

def isProject (n : Name) : Bool := proj.isPrefixOf n

/-- Equation lemmas, match auxiliaries and the rest of the elaborator's bookkeeping. -/
def isNoise (n : Name) : Bool :=
  n.isInternalDetail || n.isImplementationDetail ||
    (n.components.any fun c =>
      let s := c.toString
      s.startsWith "_" || s == "proof_1" || s == "eq_def" || s == "match_1")

def kindOf : ConstantInfo → String
  | .axiomInfo _ => "axiom"
  | .defnInfo _ => "def"
  | .thmInfo _ => "theorem"
  | .opaqueInfo _ => "opaque"
  | .quotInfo _ => "quot"
  | .inductInfo _ => "inductive"
  | .ctorInfo _ => "ctor"
  | .recInfo _ => "rec"

/-- The project constants an expression mentions, sorted and deduplicated. -/
def projUses (e : Expr) : Array String :=
  let names := e.getUsedConstants.filter fun n => isProject n && !isNoise n
  let strs := names.map (·.toString)
  (strs.qsort (· < ·)).foldl (init := #[]) fun acc s =>
    if acc.back? == some s then acc else acc.push s

def externCount (e : Expr) : Nat :=
  (e.getUsedConstants.filter fun n => !isProject n).size

/-- The Mathlib and core constants an expression mentions, sorted and deduplicated.

Written to `docs/lean-externals.json`, never into `lean-facts.json`: that file is committed and
is the input to six `scripts/appendix.py --lint` gates, and the proof-term externals alone run
to ~94,000 occurrences. This is applied to the *statement* only, which is what a reader of a
statement can use. -/
def externUses (e : Expr) : Array String :=
  let names := e.getUsedConstants.filter fun n => !isProject n && !isNoise n
  let strs := names.map (·.toString)
  (strs.qsort (· < ·)).foldl (init := #[]) fun acc s =>
    if acc.back? == some s then acc else acc.push s

/-- The proof term, or the body of a definition.

`ConstantInfo.value?` withholds theorem values at this Lean version — it answers `none` for a
`thmInfo` whose proof is present — so the projection has to be written out. Getting this wrong
is silent: every `uses_value` comes back empty and the dependency graph looks like a set of
isolated theorems. -/
def valueOf : ConstantInfo → Option Expr
  | .thmInfo v => some v.value
  | .defnInfo v => some v.value
  | .opaqueInfo v => some v.value
  | _ => none

end LeanFacts

open LeanFacts in
#eval show MetaM Unit from do
  let env ← getEnv
  let std : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let mut entries : Array (String × Json) := #[]
  let mut externs : Array (String × Json) := #[]
  let mut skipped := 0
  for idx in [0:env.header.moduleNames.size] do
    let modName := env.header.moduleNames[idx]!
    unless proj.isPrefixOf modName do continue
    for n in env.header.moduleData[idx]!.constNames do
      if isNoise n then
        skipped := skipped + 1
        continue
      let some ci := env.find? n | continue
      let type ← try (return (← ppExpr ci.type).pretty) catch _ => pure ""
      let doc := (← findDocString? env n).getD ""
      let line : Nat ← do
        match ← findDeclarationRanges? n with
        | some r => pure r.range.pos.line
        | none => pure 0
      let axs ← collectAxioms n
      let extra := axs.filter fun a => !(std.contains a)
      let usesValue := match valueOf ci with
        | some v => projUses v
        | none => #[]
      let extCount := match valueOf ci with
        | some v => externCount v
        | none => 0
      entries := entries.push (n.toString, Json.mkObj [
        ("kind", Json.str (kindOf ci)),
        ("module", Json.str modName.toString),
        ("line", Json.num line),
        ("type", Json.str type),
        ("doc", Json.str doc),
        ("uses_type", Json.arr ((projUses ci.type).map Json.str)),
        ("uses_value", Json.arr (usesValue.map Json.str)),
        ("uses_external", Json.num extCount),
        ("axioms", Json.arr ((axs.map (·.toString)).map Json.str)),
        ("nonstandard_axioms", Json.arr ((extra.map (·.toString)).map Json.str))])
      externs := externs.push (n.toString,
        Json.arr ((externUses ci.type).map Json.str))
  let out := Json.mkObj [
    ("declarations", Json.mkObj entries.toList)]
  IO.FS.writeFile "docs/lean-facts.json" (out.pretty ++ "\n")
  -- A separate, git-ignored file on purpose: lean-facts.json stays byte-identical, so
  -- nothing that lints against it can be disturbed by this.
  IO.FS.writeFile "docs/lean-externals.json"
    ((Json.mkObj [("declarations", Json.mkObj externs.toList)]).pretty ++ "\n")
  IO.println s!"lean_facts: {entries.size} declarations written to docs/lean-facts.json \
    ({skipped} internal names skipped)"
