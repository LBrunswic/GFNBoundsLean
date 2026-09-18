import GFNBounds.Doubling.CutBalance
import GFNBounds.Doubling.Cramer
import GFNBounds.Doubling.Descent
import GFNBounds.Doubling.Excursion
import GFNBounds.Doubling.Family
import GFNBounds.Doubling.Supersolution
import GFNBounds.Doubling.Tail
import GFNBounds.Doubling.Constant
import GFNBounds.Doubling.ConstantFunctional
import GFNBounds.Doubling.Expansion
import GFNBounds.Doubling.Exponent
import GFNBounds.Doubling.FixedPoints
import GFNBounds.Doubling.Main
import GFNBounds.Doubling.Operator
import GFNBounds.Doubling.R0Bound
import GFNBounds.Doubling.WindowSum
import GFNBounds.Doubling.Drift
import GFNBounds.Doubling.Irreducible
import GFNBounds.Doubling.AdjointL2
import GFNBounds.Doubling.OperatorL2
import GFNBounds.Doubling.PhaseEmpty
import GFNBounds.Doubling.PhaseExists
import GFNBounds.Doubling.SharpFull
import GFNBounds.Doubling.Weight
import GFNBounds.Doubling.Adjoint
import GFNBounds.Doubling.Coupling
import GFNBounds.Doubling.Doeblin
import GFNBounds.Doubling.Escape
import GFNBounds.Doubling.FixedPointsP
import GFNBounds.Doubling.Length
import GFNBounds.Doubling.LpContraction
import GFNBounds.Doubling.LpLayer
import GFNBounds.Doubling.Lyapunov
import GFNBounds.Doubling.OperatorFinite
import GFNBounds.Doubling.PointwiseInv
import GFNBounds.Doubling.Product
import GFNBounds.Doubling.Sharp
import GFNBounds.Doubling.SharpRate
import GFNBounds.Doubling.Sojourn
import GFNBounds.Doubling.StatExists
import GFNBounds.Doubling.Summable
import GFNBounds.Doubling.TotalVariation
import GFNBounds.Doubling.TruncationStat
import GFNBounds.Doubling.Unsolvable
import GFNBounds.Doubling.Kac
import GFNBounds.Doubling.Truncation
import GFNBounds.Doubling.PerCutNorms
import GFNBounds.Doubling.Ramp
import GFNBounds.Doubling.Ratios
import GFNBounds.Doubling.Unbounded
import GFNBounds.Doubling.RayleighBridge
import GFNBounds.Doubling.UnboundedL2
import GFNBounds.Balance.WeightedL2Norm
import GFNBounds.Balance.LocalConvergenceClauses
import GFNBounds.Balance.LocalConvergenceMixing
import GFNBounds.Balance.SqGenerator
import GFNBounds.Balance.FreezingGeneral
import GFNBounds.Core.UniversalityKernelBound
import GFNBounds.Doubling.OperatorFiniteSum
import GFNBounds.Doubling.DescentStatement
import GFNBounds.Graph.CycleBlowup
import GFNBounds.Doubling.TruncationBhat
import GFNBounds.Doubling.MainPackaging
import GFNBounds.Graph.FrozenUnstableDB
import GFNBounds.Balance.GlobalConvergence
import GFNBounds.Balance.FlowExistence
import GFNBounds.Balance.C3Wrappers
import GFNBounds.Doubling.ExpansionSecond
import GFNBounds.Doubling.WeightFull
import GFNBounds.Balance.LiftFinite
import GFNBounds.Balance.DiscreteGlobal
import GFNBounds.Doubling.Remarks
import GFNBounds.Balance.TrainingSpeedAssembled
import GFNBounds.Graph.CycleRemarks
import GFNBounds.Core.FamilyUniversality
import GFNBounds.Core.SigmaMixing
import GFNBounds.Graph.MorozovDB
import GFNBounds.Core.UniversalityBody

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
#print axioms Decay.tail_sharp

-- `cor:doubling_family` — app_doubling.tex:2087
#print axioms Stat.tailSeq_eq_tailMass
#print axioms Stat.rayleigh_family
#print axioms Stat.exists_rayleigh_family

-- `prop:doubling_constant`, Step 1 — app_doubling.tex:1702
#print axioms Decay.extend_cutBal
#print axioms Decay.extend_unique
#print axioms Decay.extend_pos
#print axioms Decay.extend_add
#print axioms Decay.extend_smul
#print axioms Decay.extend_congr_high

-- `lem:doubling_expansion`, Step 4, and `rem:doubling_parity` — app_doubling.tex:848, :955
#print axioms Decay.A_one_eq
#print axioms Decay.A_gap
#print axioms Decay.Gamma_pos
#print axioms Decay.Gamma_lt_one
#print axioms Decay.A_zero_pos
#print axioms Decay.A_one_neg

-- `lem:doubling_fixed_points`, the `P_star` half — app_doubling.tex:130
#print axioms sq_pstar_le
#print axioms pstar_sq_gap
#print axioms Stat.jensen_gap_zero
#print axioms Stat.fixed_const

-- `lem:doubling_operator`(3) — app_doubling.tex:166
#print axioms one_sub_mul_partialSum
#print axioms partialSum_mul_one_sub
#print axioms tendsto_pow
#print axioms resolvent_identities
#print axioms resolvent_inverse
#print axioms resolvent_norm_le

-- `theo:doubling_main`, assembled — app_doubling.tex:275
#print axioms main_unbounded
#print axioms main_unbounded_infty
#print axioms main_sigmaBar_le
#print axioms main_rate
#print axioms main_truncation_irreducible
#print axioms main_irreducible

-- `eq:doubling_R0`, effectivized — app_doubling.tex:965 (in `lem:doubling_descent`)
#print axioms incr_le'
#print axioms le_incr'
#print axioms telescope_Ico
#print axioms sum_window_ge
#print axioms sum_window_le
#print axioms Decay.R0_eq
#print axioms Decay.foot_rpow_le
#print axioms Decay.le_foot_rpow
#print axioms Decay.R0_sub_one_le
#print axioms Decay.R0_between

-- `prop:doubling_exponent` — app_doubling.tex:693
#print axioms sum_Ico_rpow_sub_integral_le
#print axioms integral_rpow_window
#print axioms tendsto_foot_ratio
#print axioms tendsto_windowPower
#print axioms tendsto_windowV
#print axioms exponent_is_cramer_root

-- `cor:doubling_truncation`, Step 6 (Kac's formula) — app_doubling.tex:2199
#print axioms hitExp_le_nat
#print axioms Stat.hasSum_flux_pt
#print axioms pstar_ptFn_sink
#print axioms Stat.lam_sink_eq_src
#print axioms Stat.lam_src_le_lam_one
#print axioms hitExp_defect
#print axioms Stat.hitInt_succ_sub
#print axioms Stat.kac_identity
#print axioms Stat.lam_one_ge

-- `cor:doubling_truncation` — app_doubling.tex:2199
#print axioms Stat.percut_K
#print axioms Stat.finset_sum_le_tailMass
#print axioms Stat.tail_lower
#print axioms Stat.hitInt_le
#print axioms Stat.sqrtK
#print axioms Stat.lam_ge_prev
#print axioms Stat.lam_chain_up
#print axioms Stat.lam_chain_down
#print axioms Stat.block_ratio
#print axioms Stat.cutBalanceSeq_trunc
#print axioms Stat.decayK

-- ── the 2026-09-07 workflow round ──────────────────────────────────────────────

-- the `L^p` layer (no paper label of its own; the layer `lem:doubling_operator`,
-- `lem:doubling_fixed_points` and `prop:doubling_unsolvable` all need)
#print axioms Stat.mu
#print axioms Stat.ae_iff_eq
#print axioms Stat.pstarL2
#print axioms Stat.fixed_const_memLp

-- `lem:doubling_operator`(1), the contraction clause — app_doubling.tex:166
#print axioms Stat.eLpNorm_pstar_le_of_memLp
#print axioms Stat.dens
#print axioms Stat.tsum_dens_mul_sq

-- `lem:doubling_fixed_points`, both halves — app_doubling.tex:130
#print axioms Stat.ker_eq_const

-- `prop:doubling_length` — app_doubling.tex:476
#print axioms hitExp_iSup_eq
#print axioms sbar_iSup_eq

-- `prop:doubling_phase`(3), row (b) — app_doubling.tex:510
#print axioms exists_stat_none
#print axioms exists_stat_of_family
#print axioms inv_of_pointwise
#print axioms Wpow_drift_expansion

-- `lem:doubling_escape` — app_doubling.tex:1026
#print axioms Decay.escape_of_level
#print axioms Decay.sojourn_block

-- `lem:doubling_product` — app_doubling.tex:1110
#print axioms Decay.prodW_two_sided_paper
#print axioms Decay.prodW_R0_eq_descOne

-- `theo:doubling_decay`, now unconditional — app_doubling.tex:1155
#print axioms Decay.decay_block_of_cutBal
#print axioms Decay.decay_two_sided_of_cutBal

-- `lem:doubling_doeblin` — app_doubling.tex:1385
#print axioms Decay.doeblin

-- `lem:doubling_coupling` — app_doubling.tex:1475
#print axioms Decay.coupling
#print axioms Decay.coupling_above

-- `theo:doubling_sharp` (conditional on `lem:doubling_weight`) — app_doubling.tex:1323
#print axioms Decay.cutBal_unique
#print axioms Decay.sharp

-- `lem:doubling_truncation_irreducible`, Step 4 — app_doubling.tex:1805
#print axioms exists_stat
#print axioms stat_unique

-- `prop:doubling_unsolvable` — app_doubling.tex:2126
#print axioms doubling_unsolvable

-- ── the 2026-09-07 second workflow round ───────────────────────────────────────

-- `lem:doubling_weight`, Weight.lean's consequence form — app_doubling.tex:1357
#print axioms Decay.c3
#print axioms Decay.ell3
#print axioms Decay.weight_bound

-- `theo:doubling_sharp`, now unconditional — app_doubling.tex:1323
#print axioms Decay.uu_bounded_of_cutBal
#print axioms Decay.sharp_of_cutBal

-- `lem:doubling_operator`(1), the adjoint clause — app_doubling.tex:166
#print axioms Stat.densL2
#print axioms Stat.adjoint_densL2_pow_sub_piL2
#print axioms Stat.norm_pstarL2_pow_sub_piL2
#print axioms Stat.betaHat

-- `lem:doubling_operator`(2) and `B̂_K < ∞` — app_doubling.tex:166, :1805
#print axioms Stat.evalChain_injective
#print axioms Stat.exists_diffusionOp
#print axioms Stat.exists_bhat

-- `prop:doubling_phase`, rows (b) and (f) — app_doubling.tex:510
#print axioms exists_stat_of_threshold
#print axioms exists_threshold_family
#print axioms exists_stat_of_family_gt_one
#print axioms exists_stat_of_family_one

-- `prop:doubling_phase`, rows (a), (c), (e) — app_doubling.tex:510
#print axioms cut_tail_ge
#print axioms isEmpty_stat_of_supercritical
#print axioms isEmpty_stat_of_family_ge_one
#print axioms isEmpty_stat_of_family_lt_one

-- the definitional layer (`def:doubling_setting` — app_doubling.tex:13)
#print axioms pstar_const
#print axioms Stat.tsum_sub_pstar

-- ── the 2026-09-07 evening round: the umbrella assembled ───────────────────────

-- the `L²(λ)` Rayleigh bridge (no paper label of its own)
#print axioms Stat.memLp_two_of_bounded
#print axioms Stat.rayleigh_of_leftInverse
#print axioms Stat.mass_le_of_rayleighL2
#print axioms Stat.mass_le_of_leftInverse

-- `theo:doubling_unbounded`(2), the `p = 2` clauses — app_doubling.tex:1945
#print axioms Stat.no_diffusionOp
#print axioms Stat.not_tendsto_partialSum
#print axioms Stat.not_summable_betaHat

-- `cor:doubling_tail_sharp`, first line as a limit — app_doubling.tex:1672
#print axioms Decay.tendsto_tail_sharp
#print axioms Decay.tendsto_tail_ratio_sharp

-- `cor:doubling_tail`, the ratio's upper half and the two limits — app_doubling.tex:1230
#print axioms Decay.tail_ratio_le
#print axioms Decay.tendsto_tailSeq_zero
#print axioms Decay.tendsto_tail_ratio_atTop

-- `theo:doubling_decay`(2) with the constants written out — app_doubling.tex:1155
#print axioms Decay.uu_bounded_explicit
#print axioms Decay.decay_two_sided_explicit

-- `theo:doubling_sharp` with `c₆` written out — app_doubling.tex:1323
#print axioms Decay.sharp_rate_explicit
#print axioms Decay.levelL
#print axioms Decay.c6
#print axioms Decay.sharp_explicit

-- `theo:doubling_main`, assembled item by item — app_doubling.tex:275
#print axioms Decay.ofC
#print axioms main_phase
#print axioms main_invariant_measure
#print axioms main_constant_determined
#print axioms main_unbounded_two
#print axioms main_sigmaBar_eq
#print axioms main_unsolvable
#print axioms main_truncation_bhat
#print axioms main_truncation_sqrtK

-- `prop:doubling_constant`, Steps 2 and 3 — app_doubling.tex:1702
#print axioms Decay.nu
#print axioms Decay.extend_nonneg
#print axioms Decay.tendsto_extend
#print axioms Decay.climit_eq_sum
#print axioms Decay.tendsto_of_cutBal
#print axioms Decay.constant_eq
#print axioms Decay.nu_nonneg
#print axioms Decay.sum_nu_pos
#print axioms Decay.nu_eq_zero
#print axioms Decay.constant_functional
#print axioms main_constant_functional

end GFNBounds.Doubling

/-! ## Wave 1 (2026-09-13): the first non-Doubling certificates

Balance, Core, Graph and the new Doubling files graduated from the scaffold on 2026-09-13.
Before this section `Audit.lean` checked Doubling only; these modules were covered solely by
`scripts/AxiomSweep.lean`. Names are fully qualified. -/

-- `lem:sigma_mixing` — GFNBounds/Core/SigmaMixing.lean
#print axioms GFNBounds.Core.isBoundedDensityAction_two
#print axioms GFNBounds.Core.norm_one_sub_meanProj_eq_one
#print axioms GFNBounds.Core.lem_sigma_mixing
#print axioms GFNBounds.Core.lem_sigma_mixing_polish
#print axioms GFNBounds.Core.sigma_mixing_witness

-- `theo/lem:sigma_mixing + prop:nonlinear_freezing(2)` — GFNBounds/Balance/WeightedL2Norm.lean
#print axioms GFNBounds.Balance.one_sub_meanOp_ne_zero
#print axioms GFNBounds.Balance.norm_one_sub_meanOp
#print axioms GFNBounds.Balance.beta_zero_densOp_meanOp
#print axioms GFNBounds.Balance.one_le_B_densOp
#print axioms GFNBounds.Balance.rho_densOp_le
#print axioms GFNBounds.Balance.twoState_mixing_densOp
#print axioms GFNBounds.Balance.twoState_mixing_coefficients
#print axioms GFNBounds.Balance.twoState_rho_eq
#print axioms GFNBounds.Balance.twoState_rho_freezing

-- `theo:local_convergence_full clauses` — GFNBounds/Balance/LocalConvergenceClauses.lean
#print axioms GFNBounds.Balance.eps0_le_a_div
#print axioms GFNBounds.Balance.eps0_mem_Ioc
#print axioms GFNBounds.Balance.one_le_max_C7
#print axioms GFNBounds.Balance.local_convergence_full_C
#print axioms GFNBounds.Balance.gamma0_pos
#print axioms GFNBounds.Balance.Lgd_pos
#print axioms GFNBounds.Balance.gamma0_pos_of_weights
#print axioms GFNBounds.Balance.local_convergence_gd_window
#print axioms GFNBounds.Balance.abs_ratio_sub_one_le_two_a_div_three
#print axioms GFNBounds.Balance.hasDerivAt_loss_local
#print axioms GFNBounds.Balance.hasDerivAt_loss_ipL2_local
#print axioms GFNBounds.Balance.local_convergence_gd_welldefined

-- `theo:local_convergence_full at Core.Mixing.B` — GFNBounds/Balance/LocalConvergenceMixing.lean
#print axioms GFNBounds.Balance.local_convergence_full_mixing
#print axioms GFNBounds.Balance.local_convergence_gd_mixing
#print axioms GFNBounds.Balance.eps0_mem_Ioc_mixing
#print axioms GFNBounds.Balance.local_convergence_full_C_mixing
#print axioms GFNBounds.Balance.gamma0_pos_of_weights_mixing
#print axioms GFNBounds.Balance.local_convergence_gd_welldefined_mixing
#print axioms GFNBounds.Balance.mixing_densOp_iff_summable
#print axioms GFNBounds.Balance.meanOp_eq_of_densOp_eq
#print axioms GFNBounds.Balance.eq_const_of_densAct_eq

-- `prop:no_distant_equilibrium(3) for (x-1)^2` — GFNBounds/Balance/SqGenerator.lean
#print axioms GFNBounds.Balance.sqDeriv_mul_one_sub_le_sharp
#print axioms GFNBounds.Balance.sqDeriv_mul_one_sub_le
#print axioms GFNBounds.Balance.le_abs_sqDeriv_mul_one_sub
#print axioms GFNBounds.Balance.sqDeriv_mul_one_sub_nonpos
#print axioms GFNBounds.Balance.no_distant_equilibrium_three_far_of
#print axioms GFNBounds.Balance.no_distant_equilibrium_three_sq

-- `prop:nonlinear_freezing(1) widened` — GFNBounds/Balance/FreezingGeneral.lean
#print axioms GFNBounds.Balance.const_on_band_of_deriv_zero
#print axioms GFNBounds.Balance.FreezingBands.pos_of_mem_bands
#print axioms GFNBounds.Balance.eventually_loss_eq_of
#print axioms GFNBounds.Balance.loss_pos_of
#print axioms GFNBounds.Balance.loss_pos_of_nonneg
#print axioms GFNBounds.Balance.hasFDerivAt_loss_zero_of
#print axioms GFNBounds.Balance.freezing_item_one_general
#print axioms GFNBounds.Balance.freezing_hasDerivAt_zero_general
#print axioms GFNBounds.Balance.freezing_item_one_of_general

-- `theo:universality_L2_full at the kernel` — GFNBounds/Core/UniversalityKernelBound.lean
#print axioms GFNBounds.Core.coeFn_liftedOutflow
#print axioms GFNBounds.Core.truncation_eq_zero_top
#print axioms GFNBounds.Core.tendsto_truncation_norm_all
#print axioms GFNBounds.Core.residuals_le_of_kernel
#print axioms GFNBounds.Core.tendsto_residuals_of_kernel
#print axioms GFNBounds.Core.defect_eq_zero_of_kernel_top
#print axioms GFNBounds.Core.residuals_eq_zero_of_kernel_top

-- `lem:doubling_operator(3), rem:doubling_two_constants` — GFNBounds/Doubling/OperatorFiniteSum.lean
#print axioms GFNBounds.Doubling.resolvent_eq_tsum_of_bdd
#print axioms GFNBounds.Doubling.inverse_sub_le_of_bdd
#print axioms GFNBounds.Doubling.Stat.bhat_le_sum_betaHat
#print axioms GFNBounds.Doubling.Stat.sub_piL2_eq_tsum
#print axioms GFNBounds.Doubling.Stat.inverse_sub_piL2_le_sum_betaHat
#print axioms GFNBounds.Doubling.Stat.inverse_sub_piL2_eq_tsum

-- `lem:doubling_descent` — GFNBounds/Doubling/DescentStatement.lean
#print axioms GFNBounds.Doubling.Decay.c4_pos
#print axioms GFNBounds.Doubling.Decay.lt_ell1
#print axioms GFNBounds.Doubling.Decay.thr_of_ell1
#print axioms GFNBounds.Doubling.Decay.R0_between_of_ell1
#print axioms GFNBounds.Doubling.Decay.R0_sub_one_le_c4
#print axioms GFNBounds.Doubling.Decay.descent_item1_path
#print axioms GFNBounds.Doubling.Decay.descent_item2_path
#print axioms GFNBounds.Doubling.Decay.descent_Z_pos
#print axioms GFNBounds.Doubling.Decay.exitLaw_eq_zero_of_notMem
#print axioms GFNBounds.Doubling.Decay.descZ_eq_descW
#print axioms GFNBounds.Doubling.Decay.exists_descentPath
#print axioms GFNBounds.Doubling.Decay.doubling_descent

-- `rem:cycle_no_stalemate` — GFNBounds/Graph/CycleBlowup.lean
#print axioms GFNBounds.Graph.CycleExample.bhatSigma_cycle_tendsto
#print axioms GFNBounds.Graph.CycleExample.bhatSigma_blowup_paper_form
#print axioms GFNBounds.Graph.CycleExample.sigmaBar_blowup
#print axioms GFNBounds.Graph.CycleExample.blowupDelta_pos
#print axioms GFNBounds.Graph.CycleExample.lt_three_div_of_blowupDelta

-- `cor:doubling_truncation` — GFNBounds/Doubling/TruncationBhat.lean
#print axioms GFNBounds.Doubling.Stat.diffOpK_resolvent
#print axioms GFNBounds.Doubling.Stat.percut_leftInverse
#print axioms GFNBounds.Doubling.Stat.percut_bhatK
#print axioms GFNBounds.Doubling.Stat.withEpsMax_lam
#print axioms GFNBounds.Doubling.Decay.one_le_c9Of
#print axioms GFNBounds.Doubling.Decay.c8Of_pos
#print axioms GFNBounds.Doubling.Stat.decayK_explicit
#print axioms GFNBounds.Doubling.Stat.sqrtK_explicit
#print axioms GFNBounds.Doubling.Stat.sqrtK_bhatK
#print axioms GFNBounds.Doubling.truncation_explicit
#print axioms GFNBounds.Doubling.main_truncation

-- `theo:doubling_main packaging` — GFNBounds/Doubling/MainPackaging.lean
#print axioms GFNBounds.Doubling.card_chainFinset
#print axioms GFNBounds.Doubling.main_truncation_states
#print axioms GFNBounds.Doubling.Decay.c7Of_congr
#print axioms GFNBounds.Doubling.Decay.c7Of_pos
#print axioms GFNBounds.Doubling.Stat.mass_defect_centredTail_pos
#print axioms GFNBounds.Doubling.Stat.rate_explicit
#print axioms GFNBounds.Doubling.main_rate_explicit
#print axioms GFNBounds.Doubling.main_c7_congr
#print axioms GFNBounds.Doubling.main_truncation_explicit

-- `prop:frozen_unstable_full` (DB half, eq:def_stability) — GFNBounds/Graph/FrozenUnstableDB.lean
#print axioms GFNBounds.Graph.not_stable_of_witness
#print axioms GFNBounds.Graph.BackwardPolicy.edgeFlow_one_eq_edgeMeasure
#print axioms GFNBounds.Graph.BackwardPolicy.phat_pos_of_hatEdge
#print axioms GFNBounds.Graph.BackwardPolicy.phat_eq_zero_of_not_hatEdge
#print axioms GFNBounds.Graph.BackwardPolicy.edgeFlow_eq_zero_of_not_hatEdge
#print axioms GFNBounds.Graph.BackwardPolicy.circ_eq_zero_of_not_hatEdge
#print axioms GFNBounds.Graph.BackwardPolicy.perturbedFlow_eq_zero_of_not_hatEdge
#print axioms GFNBounds.Graph.BackwardPolicy.perturbedFlow_pos_of_hatEdge
#print axioms GFNBounds.Graph.BackwardPolicy.perturbedFlow_isEdgeflow
#print axioms GFNBounds.Graph.BackwardPolicy.invariant_edgeInflow_of_pushEdge_eq
#print axioms GFNBounds.Graph.BackwardPolicy.pushEdge_perturbedFlow_ne
#print axioms GFNBounds.Graph.BackwardPolicy.perturbedFlow_isFlow
#print axioms GFNBounds.Graph.BackwardPolicy.epsCirc_isZeroFlow
#print axioms GFNBounds.Graph.BackwardPolicy.edgeMeasure_pos_iff_hatEdge
#print axioms GFNBounds.Graph.BackwardPolicy.dbLoss_eq_edgeRatio
#print axioms GFNBounds.Graph.BackwardPolicy.dbLoss_sub_eq_of_support
#print axioms GFNBounds.Graph.BackwardPolicy.dbLoss_eq_zero_of
#print axioms GFNBounds.Graph.BackwardPolicy.dbLoss_pos_of
#print axioms GFNBounds.Graph.BackwardPolicy.dbRatio_edgeFlow_eq_one
#print axioms GFNBounds.Graph.BackwardPolicy.dbRatio_perturbedFlow_pos
#print axioms GFNBounds.Graph.BackwardPolicy.frozen_unstable_full_db
#print axioms GFNBounds.Graph.BackwardPolicy.frozen_not_stable_fm
#print axioms GFNBounds.Graph.BackwardPolicy.frozen_not_stable_db

-- `prop:no_distant_equilibrium`(3) and `theo:global_dichotomy_full`(1), convergence for (log x)^2 — GFNBounds/Balance/GlobalConvergence.lean
#print axioms GFNBounds.Balance.continuous_nrmL2
#print axioms GFNBounds.Balance.no_distant_equilibrium_three_converges
#print axioms GFNBounds.Balance.global_dichotomy_full_one_converges

-- `prop:no_distant_equilibrium`(3), existence and uniqueness of the gradient flow — GFNBounds/Balance/FlowExistence.lean
#print axioms GFNBounds.Balance.FlowGenerator.exists_flow
#print axioms GFNBounds.Balance.FlowGenerator.existsUnique_flow
#print axioms GFNBounds.Balance.isGradientFlow_unique
#print axioms GFNBounds.Balance.reach_of_uniqueInvariant
#print axioms GFNBounds.Balance.existsUnique_flow_logSq_of_ergodic
#print axioms GFNBounds.Balance.existsUnique_flow_sq_of_ergodic
#print axioms GFNBounds.Balance.existsUnique_flow_logSq
#print axioms GFNBounds.Balance.existsUnique_flow_sq
#print axioms GFNBounds.Balance.existsUnique_flow_logSq_graph
#print axioms GFNBounds.Balance.existsUnique_flow_sq_graph
#print axioms GFNBounds.Balance.no_distant_equilibrium_three_of_init
#print axioms GFNBounds.Balance.uFloor_logSq_eq_uMin
#print axioms GFNBounds.Balance.twoState_uniqueInvariant
#print axioms GFNBounds.Balance.twoState_flow_exists_check
#print axioms GFNBounds.Balance.twoState_flow_exists_check_sq
#print axioms GFNBounds.Balance.cycle_flow_converges_check

-- `theo:local_convergence_full` C^3 wrapper and DB instance; `theo:training_speed_full` items 1-2 at Gamma_3 — GFNBounds/Balance/C3Wrappers.lean
#print axioms GFNBounds.Balance.taylor_of_C3
#print axioms GFNBounds.Balance.local_convergence_full_C3
#print axioms GFNBounds.Balance.local_convergence_gd_C3
#print axioms GFNBounds.Balance.constC3_bounds
#print axioms GFNBounds.Balance.constC3_congr
#print axioms GFNBounds.Balance.local_convergence_full_DB
#print axioms GFNBounds.Balance.local_convergence_gd_DB
#print axioms GFNBounds.Balance.loss_edgeE_eq_db
#print axioms GFNBounds.Balance.edgeKernel_mem_edgeSet
#print axioms GFNBounds.Balance.edgeKernelE_isMarkovOn
#print axioms GFNBounds.Balance.edgeMeasureE_isInvariant
#print axioms GFNBounds.Balance.edgeMeasureE_pos
#print axioms GFNBounds.Balance.edgeMeasureE_total
#print axioms GFNBounds.Balance.Gamma3_logSq
#print axioms GFNBounds.Balance.eps0_antitone_M3
#print axioms GFNBounds.Balance.eps0Gamma3_le_eps0Sq
#print axioms GFNBounds.Balance.eps0Gamma3_le_sqrt
#print axioms GFNBounds.Balance.training_speed_full_Gamma3
#print axioms GFNBounds.Balance.coer_edgeU
#print axioms GFNBounds.Balance.local_convergence_full_DB_witness

-- `lem:doubling_expansion` (eq:doubling_Rexp) and `rem:doubling_parity` — GFNBounds/Doubling/ExpansionSecond.lean
#print axioms GFNBounds.Doubling.Decay.Rexp
#print axioms GFNBounds.Doubling.Decay.Rexp_isBigO
#print axioms GFNBounds.Doubling.Decay.cR_congr
#print axioms GFNBounds.Doubling.Decay.parity_thresholds_congr
#print axioms GFNBounds.Doubling.Decay.wm_le_foot
#print axioms GFNBounds.Doubling.Decay.wm_foot_expansion
#print axioms GFNBounds.Doubling.Decay.R0_gt_one_of_even
#print axioms GFNBounds.Doubling.Decay.R0_lt_one_of_odd
#print axioms GFNBounds.Doubling.Decay.Ralpha_zero_gt_one_of_even
#print axioms GFNBounds.Doubling.Decay.Ralpha_zero_lt_one_of_odd
#print axioms GFNBounds.Doubling.Decay.not_isSupersolution_Phi_zero
#print axioms GFNBounds.Doubling.Decay.not_isSubsolution_Phi_zero
#print axioms GFNBounds.Doubling.Decay.isSupersolution_two_pow
#print axioms GFNBounds.Doubling.Decay.isSubsolution_inv_factorial_sq
#print axioms GFNBounds.Doubling.Decay.nonempty_decay

-- `lem:doubling_weight` in the paper's form — GFNBounds/Doubling/WeightFull.lean
#print axioms GFNBounds.Doubling.Decay.doubling_weight
#print axioms GFNBounds.Doubling.Decay.doubling_weight_paths
#print axioms GFNBounds.Doubling.Decay.doubling_weight_of_ceils
#print axioms GFNBounds.Doubling.Decay.doubling_weight_transform
#print axioms GFNBounds.Doubling.Decay.weightDev_eq_sum_paths
#print axioms GFNBounds.Doubling.Decay.descJoint_eq_sum_paths
#print axioms GFNBounds.Doubling.Decay.sum_pathProb
#print axioms GFNBounds.Doubling.Decay.mem_descPaths_iff
#print axioms GFNBounds.Doubling.Decay.trajOf_mem_descPaths
#print axioms GFNBounds.Doubling.Decay.exists_descentPath_of_mem
#print axioms GFNBounds.Doubling.Decay.weightDev_le_c3

-- `lem:lift_mixing` (equality) and `lem:lift_coercivity`, finite forms — GFNBounds/Balance/LiftFinite.lean
#print axioms GFNBounds.Balance.lift_mixing_dens
#print axioms GFNBounds.Balance.lift_mixing_beta
#print axioms GFNBounds.Balance.lift_mixing_opNorm_eq
#print axioms GFNBounds.Balance.lift_mixing_ge
#print axioms GFNBounds.Balance.opBound_opNorm
#print axioms GFNBounds.Balance.opNorm_densDeviation
#print axioms GFNBounds.Balance.lift_coercivity_finite
#print axioms GFNBounds.Balance.lift_coercivity_edgeSupport
#print axioms GFNBounds.Balance.lift_coercivity_graph
#print axioms GFNBounds.Balance.lift_coercivity_twoState
#print axioms GFNBounds.Balance.twoState_lift_beta_one

-- `theo:training_speed_full` item 3, the discrete global phase — GFNBounds/Balance/DiscreteGlobal.lean
#print axioms GFNBounds.Balance.DiscreteGlobal.training_speed_gd
#print axioms GFNBounds.Balance.DiscreteGlobal.training_speed_gd_minPos
#print axioms GFNBounds.Balance.DiscreteGlobal.training_speed_gd_minPos_ennreal
#print axioms GFNBounds.Balance.DiscreteGlobal.no_uniform_step
#print axioms GFNBounds.Balance.DiscreteGlobal.no_uniform_step_graph
#print axioms GFNBounds.Balance.DiscreteGlobal.descent_step
#print axioms GFNBounds.Balance.DiscreteGlobal.traj_a
#print axioms GFNBounds.Balance.DiscreteGlobal.traj_b
#print axioms GFNBounds.Balance.DiscreteGlobal.traj_entry
#print axioms GFNBounds.Balance.DiscreteGlobal.traj_c
#print axioms GFNBounds.Balance.DiscreteGlobal.traj_d
#print axioms GFNBounds.Balance.DiscreteGlobal.k0real_eq
#print axioms GFNBounds.Balance.DiscreteGlobal.gammaStar_pos
#print axioms GFNBounds.Balance.DiscreteGlobal.exists_descent_seq
#print axioms GFNBounds.Balance.DiscreteGlobal.training_speed_gd_inhabited
#print axioms GFNBounds.Balance.DiscreteGlobal.cycle_training_speed_gd_nonvacuous
#print axioms GFNBounds.Balance.DiscreteGlobal.Gamma3_logSq_eq_Gamma3Val
#print axioms GFNBounds.Balance.DiscreteGlobal.eps0At_Gamma3Val_eq
#print axioms GFNBounds.Balance.DiscreteGlobal.gamma0At_Gamma3Val_eq

-- `rem:doubling_renewal` and `rem:doubling_two_constants` — GFNBounds/Doubling/Remarks.lean
#print axioms GFNBounds.Doubling.Remarks.renewal_limit
#print axioms GFNBounds.Doubling.Remarks.renewal_G_const
#print axioms GFNBounds.Doubling.Remarks.renewal_hasDerivAt_G
#print axioms GFNBounds.Doubling.Remarks.renewal_lipschitz
#print axioms GFNBounds.Doubling.Remarks.renewal_rhs_lipschitz
#print axioms GFNBounds.Doubling.Remarks.kernMean_eq
#print axioms GFNBounds.Doubling.Remarks.integral_kbar_eq_kernMean
#print axioms GFNBounds.Doubling.Remarks.kernMeasure_nonlattice
#print axioms GFNBounds.Doubling.Remarks.kernMeasure_univ
#print axioms GFNBounds.Doubling.Remarks.kern_boundedVariationOn
#print axioms GFNBounds.Doubling.Remarks.renewal_limit_check
#print axioms GFNBounds.Doubling.Remarks.bhat_le_mixing_sum
#print axioms GFNBounds.Doubling.Remarks.diffusion_apply_eq_series
#print axioms GFNBounds.Doubling.Remarks.two_constants_flip_three_quarters
#print axioms GFNBounds.Doubling.Remarks.two_constants_flip_half
#print axioms GFNBounds.Doubling.Remarks.bhat_le_mixing_sum_check
#print axioms GFNBounds.Doubling.Remarks.diffusion_series_converges_check

-- `theo:local_convergence_full` (one-sided C^3, existence) and `theo:training_speed_full` items 1-2 as printed — GFNBounds/Balance/TrainingSpeedAssembled.lean
#print axioms GFNBounds.Balance.taylor_of_C3On
#print axioms GFNBounds.Balance.C3On_of_C3
#print axioms GFNBounds.Balance.Gamma3W_logSq
#print axioms GFNBounds.Balance.eps0W_logSq
#print axioms GFNBounds.Balance.local_convergence_full_C3On
#print axioms GFNBounds.Balance.constW_bounds
#print axioms GFNBounds.Balance.local_convergence_gd_C3On
#print axioms GFNBounds.Balance.sup_bootstrap_step_on
#print axioms GFNBounds.Balance.local_convergence_full_exists
#print axioms GFNBounds.Balance.local_convergence_full_DB_exists
#print axioms GFNBounds.Balance.local_convergence_gd_DB_C3On
#print axioms GFNBounds.Balance.global_phase_exact
#print axioms GFNBounds.Balance.training_speed_full_paper
#print axioms GFNBounds.Balance.kinkGen_C3On_not_C3
#print axioms GFNBounds.Balance.twoState_exists_check
#print axioms GFNBounds.Balance.cycle_training_speed_paper_check

-- `lem:cycle_counterexample` items (1)-(2) and `rem:cycle_no_stalemate` — GFNBounds/Graph/CycleRemarks.lean
#print axioms GFNBounds.Graph.CycleRemarks.cycle_counterexample
#print axioms GFNBounds.Graph.CycleRemarks.cycle_counterexample_check
#print axioms GFNBounds.Graph.CycleRemarks.inflation_force_max_mono
#print axioms GFNBounds.Graph.CycleRemarks.not_critical
#print axioms GFNBounds.Graph.CycleRemarks.rescaled_flow
#print axioms GFNBounds.Graph.CycleRemarks.entryTimes_scale
#print axioms GFNBounds.Graph.CycleRemarks.cycle_rescaled_flow
#print axioms GFNBounds.Graph.CycleRemarks.cycle_rescaled_flow_sq
#print axioms GFNBounds.Graph.CycleRemarks.cycle_rescaled_flow_check
#print axioms GFNBounds.Graph.CycleRemarks.mixing_sum_endpoints
#print axioms GFNBounds.Graph.CycleRemarks.mixing_sum_gt
#print axioms GFNBounds.Graph.CycleRemarks.mixing_sum_tendsto_top
#print axioms GFNBounds.Graph.CycleRemarks.betaCyc_summable
#print axioms GFNBounds.Graph.CycleRemarks.betaCyc_le_geometric
#print axioms GFNBounds.Graph.CycleRemarks.mixing_cycle
#print axioms GFNBounds.Graph.CycleRemarks.mixing_B_coercive
#print axioms GFNBounds.Graph.CycleRemarks.mixing_B_tendsto_atTop
#print axioms GFNBounds.Graph.CycleRemarks.rho_mixing_tendsto
#print axioms GFNBounds.Graph.CycleRemarks.rhoSigma_cycle_tendsto
#print axioms GFNBounds.Graph.CycleRemarks.kappa_cycle_tendsto
#print axioms GFNBounds.Graph.CycleRemarks.kappa_cycle_tendsto_gen
#print axioms GFNBounds.Graph.CycleRemarks.kappa_cycle_tendsto_fixed_measure
#print axioms GFNBounds.Graph.CycleRemarks.cycle_no_stalemate_limits
#print axioms GFNBounds.Graph.CycleRemarks.betaCyc_eq

-- `def:universality` for an arbitrary family, and `rem:partial_support` — GFNBounds/Core/FamilyUniversality.lean
#print axioms GFNBounds.Core.Family.realizes_of_le
#print axioms GFNBounds.Core.Family.StronglyUniversal.realizes_of_le
#print axioms GFNBounds.Core.Family.mass_gap_div_le_iInf
#print axioms GFNBounds.Core.Family.iInf_pos_of_mass_ne
#print axioms GFNBounds.Core.Family.weaklyUniversal_fixedPolicyFamily_iff
#print axioms GFNBounds.Core.Family.stronglyUniversal_fixedPolicyFamily_iff
#print axioms GFNBounds.Core.Family.weaklyUniversal_const_kernel
#print axioms GFNBounds.Core.Family.stronglyUniversal_const_kernel_top
#print axioms GFNBounds.Graph.PartialSupport.subGraph_pathConnected
#print axioms GFNBounds.Graph.PartialSupport.restrict_policy
#print axioms GFNBounds.Graph.PartialSupport.partial_support_exact
#print axioms GFNBounds.Graph.PartialSupport.partial_support_not_in_G
#print axioms GFNBounds.Graph.PartialSupport.member_dichotomy
#print axioms GFNBounds.Graph.PartialSupport.member_epsTarget
#print axioms GFNBounds.Graph.PartialSupport.iInf_graphResidual_eq_zero
#print axioms GFNBounds.Graph.PartialSupport.not_attained
#print axioms GFNBounds.Graph.PartialSupport.graphResidual_ne_zero
#print axioms GFNBounds.Graph.PartialSupport.not_attained_of_not_edge_src_snk
#print axioms GFNBounds.Graph.PartialSupport.graphResidual_ne_zero_of_not_edge_src_snk
#print axioms GFNBounds.Graph.PartialSupport.triangle_attained
#print axioms GFNBounds.Graph.PartialSupport.diamond_partial_support

-- `prop:morozov_rate` DB half of (3) and the leveled paragraph — GFNBounds/Graph/MorozovDB.lean
#print axioms GFNBounds.Graph.morozov_rate_three_DB
#print axioms GFNBounds.Graph.stable_frozen_discrete_DB_sigma
#print axioms GFNBounds.Graph.stable_frozen_decay_DB_sigma
#print axioms GFNBounds.Graph.local_convergence_full_DB_sigma
#print axioms GFNBounds.Graph.local_convergence_gd_DB_sigma
#print axioms GFNBounds.Graph.edge_reach_all
#print axioms GFNBounds.Graph.Leveled.one_le_beta
#print axioms GFNBounds.Graph.Leveled.mixing_sum_eq_top
#print axioms GFNBounds.Graph.Leveled.not_mixing
#print axioms GFNBounds.Graph.Leveled.periodic
#print axioms GFNBounds.Graph.Leveled.bhatSigma_leveled_eq
#print axioms GFNBounds.Graph.exists_linFlow
#print axioms GFNBounds.Graph.ar_DB_check
#print axioms GFNBounds.Graph.ar_stable_frozen_DB_witness
#print axioms GFNBounds.Graph.ar_leveled_mixing_check
#print axioms GFNBounds.Graph.arEps0_pos
#print axioms GFNBounds.Graph.ar_local_convergence_DB_witness
#print axioms GFNBounds.Graph.tri_leveled_mixing_check

-- `theo:universality_L2_body`, the EGF theorem with Stern's bound as a named hypothesis — GFNBounds/Core/UniversalityBody.lean
#print axioms GFNBounds.Core.EGF.universality_L2_body
#print axioms GFNBounds.Core.EGF.universality_L2_body_display
#print axioms GFNBounds.Core.EGF.tendsto_residuals_L2_body
#print axioms GFNBounds.Core.EGF.weaklyUniversalAt_L2_body
#print axioms GFNBounds.Core.EGF.universality_L2_body_of_full
#print axioms GFNBounds.Core.EGF.universality_L2_body_of_stern
#print axioms GFNBounds.Core.EGF.sternBound_of_rnDeriv_le
#print axioms GFNBounds.Core.EGF.IsEGFPolicy.isBoundedDensityAction
#print axioms GFNBounds.Core.EGF.IsEGFPolicy.one_le_sum_stern
#print axioms GFNBounds.Core.EGF.universality_L2_body_coin
