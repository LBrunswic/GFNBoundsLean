/-!
# The scaffold holds no `sorry`

Since 2026-09-18 it holds two sorry-free drafts written on the laptop on 2026-09-14, audited and
held back: `Balance/ClosuresA.lean` (`theo:training_speed_full` whole, `theo:universality_graphs`'
closing paragraph) must be rebased on `Core/FamilyUniversality.lean`, whose `fmDefectE`,
`graphResidual`, `memberFlow`, `outStar` and `fwdStarE` it re-defines, and its item-3(b) branch
must call `DiscreteGlobal.training_speed_gd_minPos_ennreal`; `Graph/LooseEnds.lean` cites no label
and graduates split three ways (the path law into `Doubling/Remarks.lean` for
`rem:doubling_two_constants`, the induced flow into `Graph/CycleRemarks.lean` for
`rem:cycle_no_stalemate`, the C³ flow-matching instance beside `Graph/MorozovDB.lean`), its
`internal` replaced by `MarkedGraph.internal`. Their companions `Balance/RemarksA.lean` and
`Silva/Remarks.lean` graduated the same day.


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
