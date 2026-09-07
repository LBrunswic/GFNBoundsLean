/-!
# The scaffold is empty

This library exists to hold statements of `app_doubling.tex` that `GFNBounds` states but does not
yet prove, each carrying a tagged `sorry` that `scripts/sorry_audit.py` tracks. **It currently
holds none.** Every statement the library makes about Appendix H is proved in `GFNBounds`, which
is built with `warningAsError := true`, so a `sorry` there is a compile error.

The firewall stays in place for the next unproved statement: `GFNBounds` never imports this
library, so graduation remains a file move and the sorry list can only shrink.

The last entry to leave was `lem:doubling_weight` (tag id `b4bec702`), discharged by
`GFNBounds.Doubling.Decay.weight_bound` with effective constants `c₃ = 32c₅cτ` and
`ℓ₃ = max(1, ⌈16cτ⌉, ⌈96cτ/γ²⌉)`.
-/
