import GFNBounds.Doubling.CutBalance
import GFNBounds.Doubling.Cramer
import GFNBounds.Doubling.Descent
import GFNBounds.Doubling.Excursion
import GFNBounds.Doubling.Family
import GFNBounds.Doubling.Supersolution
import GFNBounds.Doubling.Tail
import GFNBounds.Doubling.Drift
import GFNBounds.Doubling.Irreducible
import GFNBounds.Doubling.PerCutNorms
import GFNBounds.Doubling.Ramp
import GFNBounds.Doubling.Ratios
import GFNBounds.Doubling.Unbounded

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

-- `lem:doubling_percut`, Steps 1, 3, 4 — app_doubling.tex:1848
#print axioms mass_cutFn
#print axioms mass_cutFn_le_mid
#print axioms mass_cutFn_le_two
#print axioms Stat.tsum_centredTail
#print axioms Stat.mass_centredTail
#print axioms Stat.mass_two_centredTail
#print axioms centredTail_defect
#print axioms Stat.mass_defect_le
#print axioms Stat.tailMass_mul_coTail_pos
#print axioms Stat.rayleigh_two_le'

-- `prop:doubling_cut` (`eq:doubling_cut`) — app_doubling.tex:641
#print axioms cut_balance
#print axioms cutBalanceSeq_of_stat
#print axioms Stat.hasSum_flux
#print axioms Stat.lam_double_ge
#print axioms Stat.lam_le_prev

-- `lem:doubling_cramer_root` — app_doubling.tex:711
#print axioms psi_strictConvexOn
#print axioms cramer_root_unique
#print axioms cramer_root_exists
#print axioms psi_pos_of_log_eq
#print axioms cramer_root_gt_one
#print axioms cramer_lt_one_of_root_gt_one
#print axioms cramer_root_pos_iff
#print axioms cramer_form
#print axioms cramer_kernel_integral
#print axioms cramer_ineq

-- `lem:doubling_irreducible` — app_doubling.tex:101
#print axioms edge_pstar_pos
#print axioms reach_all_none
#print axioms PreStat.pos_of_irreducible
#print axioms PreStat.toStatNone

-- `lem:doubling_truncation_irreducible` (Steps 1–3) — app_doubling.tex:1805
#print axioms reach_one_lad
#print axioms reach_all_some
#print axioms PreStat.toStatSome

-- `theo:doubling_unbounded` — app_doubling.tex:1945
#print axioms Stat.tailMass_succ
#print axioms Stat.tailMass_tendsto_zero
#print axioms Stat.lam_pow_two_ge
#print axioms Stat.exists_tailRatio_gt
#print axioms Stat.mass_ratio_bound
#print axioms Stat.exists_small_mass_ratio
#print axioms Stat.no_bounded_inverse
#print axioms growthCond_of_family

-- `lem:doubling_ramp` — app_doubling.tex:2021
#print axioms ramp_defect_bounded
#print axioms Stat.tsum_centredRamp
#print axioms Stat.exists_centredRamp_ge
#print axioms Stat.no_bounded_inverse_infty
#print axioms gamma_family

-- `rem:doubling_geometric` — app_doubling.tex:2183
#print axioms geometric_sum
#print axioms not_growthCond_geometric

-- `lem:doubling_excursion` — app_doubling.tex:398
#print axioms LadderStep.le_succ_add_one
#print axioms excursion_le

-- `lem:doubling_supersolution` — app_doubling.tex:426
#print axioms pstar_mono
#print axioms linSuper_eq
#print axioms linSuper_ge
#print axioms hitExp_le_linSuper
#print axioms hitExp_mono
#print axioms hitExp_iSup_le
#print axioms sigmaBar_le

-- `def:doubling_decay_notation` — app_doubling.tex:789
#print axioms Decay.p_gt_one
#print axioms Decay.tau_gt_two
#print axioms Decay.cramer
#print axioms Decay.one_sub_eps_pos
#print axioms Decay.wm_pos
#print axioms Decay.cutBal_of_setting

-- `lem:doubling_averaging` — app_doubling.tex:814
#print axioms Decay.avg_of_cutBal
#print axioms Decay.uavg_of_avg
#print axioms Decay.uavg_of_cutBal

-- `lem:doubling_descent` — app_doubling.tex:965
#print axioms Decay.descW
#print axioms Decay.descW_of_ge
#print axioms Decay.le_of_mem_window_of_ge
#print axioms Decay.descW_uu
#print axioms Decay.descW_between

-- `theo:doubling_decay` — app_doubling.tex:1155
#print axioms Decay.decay_block
#print axioms Decay.uu_bounded
#print axioms Decay.decay_two_sided

-- `cor:doubling_tail` — app_doubling.tex:1230
#print axioms rpow_ge_tangent
#print axioms incr_le
#print axioms le_incr
#print axioms powerTail_ge
#print axioms powerTail_le
#print axioms Decay.tail_bounds
#print axioms Decay.tail_ratio_ge

-- `cor:doubling_family` — app_doubling.tex:2087
#print axioms Stat.tailSeq_eq_tailMass
#print axioms Stat.rayleigh_family
#print axioms Stat.exists_rayleigh_family

-- the definitional layer (`def:doubling_setting` — app_doubling.tex:13)
#print axioms pstar_const
#print axioms Stat.tsum_sub_pstar

end GFNBounds.Doubling
