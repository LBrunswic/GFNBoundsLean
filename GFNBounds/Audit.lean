import GFNBounds.Doubling.CutBalance
import GFNBounds.Doubling.Drift

/-!
# Axiom audit

Every declaration of `GFNBounds` that certifies a statement of `app_doubling.tex` is listed here
under `#print axioms`. `scripts/axiom_audit.py` parses the build log and fails if any of them
reports `sorryAx`, or any axiom outside `{propext, Classical.choice, Quot.sound}`.

This is the anti-laundering check. `sorry` is already a compile error inside `GFNBounds` (the
library is built with `warningAsError := true`), but that only catches a `sorry` written *here*.
It would not catch a closed theorem resting on a tagged `sorry` that had been imported from
`GFNBoundsScaffold` — which is why `GFNBounds` never imports it, and why this file exists as the
second lock rather than the first.

Convention copied from `~/LeanAI/library/LeanAILibrary/DiffusionGaussianCore.lean`.
-/

namespace GFNBounds.Doubling

-- `lem:doubling_range` — app_doubling.tex:86
#print axioms epsCS_antitone
#print axioms epsCS_one_lt_one
#print axioms one_sub_epsCS_one_pos
#print axioms Setting.ofFamily

-- `prop:doubling_drift` — app_doubling.tex:379
#print axioms height_pstar_sub
#print axioms drift_family
#print axioms drift_family_at_one
#print axioms drift_const_iff

-- `lem:doubling_percut`, Step 2 (`eq:doubling_step1`) — app_doubling.tex:1848
#print axioms percut_id

-- `prop:doubling_cut` (`eq:doubling_cut`) — app_doubling.tex:641
#print axioms cut_balance
#print axioms cutBalanceSeq_of_stat

-- the definitional layer (`def:doubling_setting` — app_doubling.tex:13)
#print axioms pstar_const
#print axioms Stat.tsum_sub_pstar

end GFNBounds.Doubling
