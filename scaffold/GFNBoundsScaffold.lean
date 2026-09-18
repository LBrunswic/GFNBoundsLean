/-!
# The scaffold holds no `sorry`

Since 2026-09-18 it holds four sorry-free drafts written on the laptop on 2026-09-14 and never
audited: `Balance/ClosuresA.lean` (`theo:training_speed_full` whole, `theo:universality_graphs`'
closing paragraph), `Balance/RemarksA.lean` (`rem:freezing`, `rem:visit_ratio`,
`rem:graphs_vs_L2`), `Silva/Remarks.lean` (`rem:silva_hypotheses`, `rem:silva_model_constant`,
`rem:path_space`) and `Graph/LooseEnds.lean`. They graduate the usual way, after a reading by an
agent that did not write them.


This library exists to hold statements the strict library `GFNBounds` states but does not yet
prove, each carrying a tagged `sorry` that `scripts/sorry_audit.py` tracks. **It currently holds
none.** Every statement `GFNBounds` makes is proved there, and `GFNBounds` is built with
`warningAsError := true`, so a `sorry` in it is a compile error.

The firewall stays in place for the next unproved statement: `GFNBounds` never imports this
library, so graduation remains a file move and the sorry list can only shrink.

The last Appendix-H entry to leave was `lem:doubling_weight` (tag id `b4bec702`), discharged by
`GFNBounds.Doubling.Decay.weight_bound` with effective constants `c₃ = 32c₅cτ` and
`ℓ₃ = max(1, ⌈16cτ⌉, ⌈96cτ/γ²⌉)`. The `Core/` layer — `lem:sigma_mixing` and
`theo:universality_L2_full` — was written here on 2026-09-08 and graduated the same day, having
never needed a `sorry`.
-/
