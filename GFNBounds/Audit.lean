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
import GFNBounds.Balance.RemarksA
import GFNBounds.Silva.Remarks
import GFNBounds.Graph.MorozovFM
import GFNBounds.Graph.UniversalityClosing
import GFNBounds.Core.Sampling
import GFNBounds.Graph.Sampling
import GFNBounds.Graph.SamplerWiring
import GFNBounds.Doubling.ExpansionTrapezoid
import GFNBounds.Doubling.WeightChain
import GFNBounds.Balance.TBGradient
import GFNBounds.Core.NegativeControl
import GFNBounds.Balance.GlobalConvergenceFinite
import GFNBounds.Core.RLBound
import GFNBounds.Core.ILBoundFull
import GFNBounds.Graph.PartialSupportClose
import GFNBounds.Silva.PathSpaceMarkov
import GFNBounds.Doubling.RenewalClose
import GFNBounds.Balance.LocalConvergenceClose
import GFNBounds.Doubling.RecurrenceClass
import GFNBounds.Doubling.PhaseRecurrence

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
-- `theo:training_speed_full` whole: item 3 with the paper's quantifiers, and items 1–3 conjoined
#print axioms GFNBounds.Balance.DiscreteGlobal.gammaStar_ofReal
#print axioms GFNBounds.Balance.DiscreteGlobal.gamma0W_logSq_eq_gamma0At
#print axioms GFNBounds.Balance.DiscreteGlobal.eps0W_logSq_eq_eps0At
#print axioms GFNBounds.Balance.DiscreteGlobal.training_speed_gd_exact
#print axioms GFNBounds.Balance.DiscreteGlobal.training_speed_full_complete
#print axioms GFNBounds.Balance.DiscreteGlobal.cycle_training_speed_complete_check

-- the dropped renewal remark and `rem:doubling_two_constants` — GFNBounds/Doubling/Remarks.lean
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
#print axioms GFNBounds.Doubling.Remarks.paths
#print axioms GFNBounds.Doubling.Remarks.trajMass
#print axioms GFNBounds.Doubling.Remarks.condExp
#print axioms GFNBounds.Doubling.Remarks.paths_eq_map
#print axioms GFNBounds.Doubling.Remarks.condExp_eq_sum_cons
#print axioms GFNBounds.Doubling.Remarks.trajMass_cons_cons
#print axioms GFNBounds.Doubling.Remarks.condExp_succ
#print axioms GFNBounds.Doubling.Remarks.condExp_zero
#print axioms GFNBounds.Doubling.Remarks.condExp_eq_iterate
#print axioms GFNBounds.Doubling.Remarks.trajMass_nonneg
#print axioms GFNBounds.Doubling.Remarks.sum_trajMass
#print axioms GFNBounds.Doubling.Remarks.condExp_one_eq_funAct
#print axioms GFNBounds.Doubling.Remarks.unwtL2_funOp_pow_wtL2
#print axioms GFNBounds.Doubling.Remarks.diffusion_apply_eq_series_condExp
#print axioms GFNBounds.Doubling.Remarks.flip_condExp_series_check

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
#print axioms GFNBounds.Graph.CycleRemarks.sum_univ_eq_internal_add
#print axioms GFNBounds.Graph.CycleRemarks.snk_inflow
#print axioms GFNBounds.Graph.CycleRemarks.internal_flow_eq
#print axioms GFNBounds.Graph.CycleRemarks.flow_eq_of_snk_eq
#print axioms GFNBounds.Graph.CycleRemarks.internal_cyc
#print axioms GFNBounds.Graph.CycleRemarks.cycle_internal_flow
#print axioms GFNBounds.Graph.CycleRemarks.cycle_flow_values
#print axioms GFNBounds.Graph.CycleRemarks.cycle_internal_flow_check

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
#print axioms GFNBounds.Balance.RemarksA.convex_no_flat_band
#print axioms GFNBounds.Balance.RemarksA.convex_small_deriv
#print axioms GFNBounds.Balance.RemarksA.analytic_const_of_flat
#print axioms GFNBounds.Balance.RemarksA.analytic_admissible_no_flat
#print axioms GFNBounds.Balance.RemarksA.deriv_deriv_logSq
#print axioms GFNBounds.Balance.RemarksA.deriv_deriv_logSq_neg
#print axioms GFNBounds.Balance.RemarksA.logSq_not_convexOn
#print axioms GFNBounds.Balance.RemarksA.tendsto_logSqDeriv_atTop
#print axioms GFNBounds.Balance.RemarksA.tendsto_abs_logSqDeriv_nhdsGT_zero
#print axioms GFNBounds.Balance.RemarksA.logSq_critical_balanced
#print axioms GFNBounds.Balance.RemarksA.freezing_two_frozen
#print axioms GFNBounds.Balance.RemarksA.freezing_two_example
#print axioms GFNBounds.Balance.RemarksA.third_deriv_bound
#print axioms GFNBounds.Balance.RemarksA.third_deriv_sSup
#print axioms GFNBounds.Balance.RemarksA.radius_not_uniform_in_generator
#print axioms GFNBounds.Balance.RemarksA.eps0C3_deltaBands_small
#print axioms GFNBounds.Balance.RemarksA.freezing_three_multiplier
#print axioms GFNBounds.Balance.RemarksA.freezing_three_generator
#print axioms GFNBounds.Balance.RemarksA.freezing_three_item_one
#print axioms GFNBounds.Balance.RemarksA.freezing_three_invisible
#print axioms GFNBounds.Balance.RemarksA.freezing_g_ne_sq_near_one
#print axioms GFNBounds.Balance.RemarksA.freezing_four_critical
#print axioms GFNBounds.Balance.RemarksA.freezing_four_logSq_converges
#print axioms GFNBounds.Balance.RemarksA.thetaOK_twoStateBands
#print axioms GFNBounds.Balance.RemarksA.deltaBands_third_deriv
#print axioms GFNBounds.Balance.RemarksA.visit_ratio_mass_lower
#print axioms GFNBounds.Balance.RemarksA.visit_ratio_norm_S_le
#print axioms GFNBounds.Balance.RemarksA.leveled_bsigma_finite_mixing_infinite
#print axioms GFNBounds.Balance.RemarksA.path_witness
#print axioms GFNBounds.Balance.RemarksA.triangle_witness
#print axioms GFNBounds.Balance.RemarksA.graphs_vs_L2_periodic
#print axioms GFNBounds.Balance.RemarksA.pathPolicy_phat
#print axioms GFNBounds.Balance.RemarksA.mixing_of_aperiodic
#print axioms GFNBounds.Balance.RemarksA.graphs_vs_L2_aperiodic
#print axioms GFNBounds.Balance.RemarksA.graphs_vs_L2_rate
#print axioms GFNBounds.Balance.RemarksA.graphs_vs_L2_rate_sigma
#print axioms GFNBounds.Balance.RemarksA.graphs_vs_L2_balanced_ray
#print axioms GFNBounds.Balance.RemarksA.graphs_vs_L2_mass_monotone
#print axioms GFNBounds.Balance.RemarksA.periodicAt_iff_setGcd
#print axioms GFNBounds.Silva.Remarks.chiSqE_unif_eq_top
#print axioms GFNBounds.Silva.Remarks.rhsE_eq_top_of_not_full_support
#print axioms GFNBounds.Silva.Remarks.one_add_chiSqE_eq_top
#print axioms GFNBounds.Silva.Remarks.tv_le_rhsE
#print axioms GFNBounds.Silva.Remarks.chiSqE_eq_ofReal
#print axioms GFNBounds.Silva.Remarks.residualE_eq_ofReal
#print axioms GFNBounds.Silva.Remarks.residualE_eq_top_of_pF_zero
#print axioms GFNBounds.Silva.Remarks.tv_le_rhsE_of_pF_zero
#print axioms GFNBounds.Silva.Remarks.identity_iff_domination
#print axioms GFNBounds.Silva.Remarks.identity_of_uniformBackward
#print axioms GFNBounds.Silva.Remarks.identity_fails_without_domination
#print axioms GFNBounds.Silva.Remarks.mPrime_le_fixedGraph
#print axioms GFNBounds.Silva.Remarks.star_mVal_lt_piInf
#print axioms GFNBounds.Silva.Remarks.inhabit_star
#print axioms GFNBounds.Silva.Remarks.inhabit_not_full_support
#print axioms GFNBounds.Silva.Remarks.inhabit_pF_zero
#print axioms GFNBounds.Silva.Remarks.inhabit_uniformBackward
#print axioms GFNBounds.Silva.Remarks.mPrime_le_fixedGraph_of_prob
#print axioms GFNBounds.Silva.Remarks.tree_pB_eq_one
#print axioms GFNBounds.Silva.Remarks.tree_mVal_le_one
#print axioms GFNBounds.Silva.Remarks.ladder_mVal_exceeds_one
#print axioms GFNBounds.Silva.Remarks.card_ladderTraj
#print axioms GFNBounds.Silva.Remarks.ladderPB_eq
#print axioms GFNBounds.Silva.Remarks.ladder_mPrime_le
#print axioms GFNBounds.Silva.Remarks.ladder_balanced
#print axioms GFNBounds.Silva.Remarks.ladder_mVal_ge
#print axioms GFNBounds.Silva.Remarks.tendsto_ladder_term
#print axioms GFNBounds.Silva.Remarks.tendsto_ladder_residual_eps
#print axioms GFNBounds.Silva.Remarks.ladder_sSup_ge
#print axioms GFNBounds.Silva.Remarks.ladder_pF_ne_zero_of_residualE_ne_top
#print axioms GFNBounds.Silva.Remarks.ladder_no_uniform_constant
#print axioms GFNBounds.Silva.Remarks.cycle_no_model_free_bound
#print axioms GFNBounds.Silva.Remarks.cycle_no_bound_along_Fk
#print axioms GFNBounds.Silva.Remarks.residual_not_divergence_FM_loss
#print axioms GFNBounds.Silva.Remarks.inhabit_cycle_no_bound
#print axioms GFNBounds.Silva.Remarks.inhabit_tree
#print axioms GFNBounds.Silva.Remarks.exists_pB_le_inv_pathCount
#print axioms GFNBounds.Silva.Remarks.sup_pathCount_div_le_inv_wMin
#print axioms GFNBounds.Silva.Remarks.sup_pathCount_le_sSup_mPrime_markov
#print axioms GFNBounds.Silva.Remarks.sup_pathCount_le_sSup_mPrime
#print axioms GFNBounds.Silva.Remarks.walksInto_infinite
#print axioms GFNBounds.Silva.Remarks.iInf_pB_walksInto_eq_zero
#print axioms GFNBounds.Silva.Remarks.doubling_terminal_infinite
#print axioms GFNBounds.Silva.Remarks.not_hasSum_const_one
#print axioms GFNBounds.Silva.Remarks.cycle_flows_target
#print axioms GFNBounds.Silva.Remarks.cycle_no_bound_punctured
#print axioms GFNBounds.Silva.Remarks.exists_ratio_gt_walksInto
#print axioms GFNBounds.Silva.Remarks.ladder_sSup_mPrime_eq
#print axioms GFNBounds.Silva.Remarks.inhabit_markov_diamond
#print axioms GFNBounds.Silva.Remarks.inhabit_cycle_walks
#print axioms GFNBounds.Silva.Remarks.inhabit_cycle_ratio
#print axioms GFNBounds.Silva.Remarks.inhabit_geometric
#print axioms GFNBounds.Graph.local_convergence_sigma_C3On
#print axioms GFNBounds.Graph.local_convergence_gd_sigma_C3On
#print axioms GFNBounds.Graph.arEps0FM
#print axioms GFNBounds.Graph.arEps0FM_pos
#print axioms GFNBounds.Graph.arSnkInd
#print axioms GFNBounds.Graph.ar_local_convergence_FM_witness
#print axioms GFNBounds.Graph.UniversalityClosing.universality_graphs_closing
#print axioms GFNBounds.Graph.UniversalityClosing.universality_graphs_strongly_universal
#print axioms GFNBounds.Graph.UniversalityClosing.freezeSink
#print axioms GFNBounds.Graph.UniversalityClosing.IsFullTarget
#print axioms GFNBounds.Graph.UniversalityClosing.IsFullTarget.isTarget
#print axioms GFNBounds.Graph.UniversalityClosing.freezeSink_positiveOnEdges_iff
#print axioms GFNBounds.Graph.UniversalityClosing.frozenBalance_eq_off
#print axioms GFNBounds.Graph.UniversalityClosing.invProb_unique_off
#print axioms GFNBounds.Graph.UniversalityClosing.breach_all_off
#print axioms GFNBounds.Graph.UniversalityClosing.graphResidual_eq_zero_of_defect
#print axioms GFNBounds.Graph.UniversalityClosing.frozenUnion_eq_iUnion
#print axioms GFNBounds.Graph.UniversalityClosing.item_three_masses_on_internal
#print axioms GFNBounds.Graph.UniversalityClosing.triSrcSnk_check
#print axioms GFNBounds.Core.Sampling.FlowData.sampling_theorem
#print axioms GFNBounds.Core.Sampling.FlowData.expectedTau_le
#print axioms GFNBounds.Core.Sampling.FlowData.mass_eq
#print axioms GFNBounds.Core.Sampling.FlowData.law_true_tendsto
#print axioms GFNBounds.Core.Sampling.Parked.strict
#print axioms GFNBounds.Core.Sampling.Parked.inhabited
#print axioms GFNBounds.Graph.Sampling.sampler_law
#print axioms GFNBounds.Graph.Sampling.sampler_termLaw
#print axioms GFNBounds.Graph.Sampling.sampler_Fk
#print axioms GFNBounds.Doubling.EMTrap.em_window
#print axioms GFNBounds.Doubling.EMTrap.em_window_bounds
#print axioms GFNBounds.Doubling.EMTrap.trap_unit_lower
#print axioms GFNBounds.Doubling.EMTrap.trap_unit_upper
#print axioms GFNBounds.Doubling.Decay.doubling_weight_chain
#print axioms GFNBounds.Doubling.Decay.integral_chainDev
#print axioms GFNBounds.Doubling.Decay.integrable_chainDev
#print axioms GFNBounds.Doubling.Decay.exists_descentChain
#print axioms GFNBounds.Doubling.Decay.sum_pathProb_matches
#print axioms GFNBounds.Balance.TBGradient.hasFDerivAt_loss
#print axioms GFNBounds.Balance.TBGradient.loss_contDiffOn
#print axioms GFNBounds.Balance.TBGradient.grad_unique
#print axioms GFNBounds.Balance.TBGradient.rho_telescope
#print axioms GFNBounds.Balance.TBGradient.marg_pos
#print axioms GFNBounds.Balance.TBGradient.ratio_pos
#print axioms GFNBounds.Balance.TBGradient.K2_row_sum
#print axioms GFNBounds.Balance.TBGradient.lam2_pos
#print axioms GFNBounds.Balance.TBGradient.lam2_invariant
#print axioms GFNBounds.Balance.TBGradient.reversal_row_sum
#print axioms GFNBounds.Balance.TBGradient.psi_eq
#print axioms GFNBounds.Balance.TBGradient.psi_one
#print axioms GFNBounds.Balance.TBGradient.grad_one
#print axioms GFNBounds.Balance.TBGradient.witness
#print axioms GFNBounds.Graph.SamplerWiring.IsSamplerLaw
#print axioms GFNBounds.Graph.SamplerWiring.Terminates
#print axioms GFNBounds.Graph.SamplerWiring.IsSamplerLaw.unique
#print axioms GFNBounds.Graph.SamplerWiring.samplerLaw
#print axioms GFNBounds.Graph.SamplerWiring.sampler_general
#print axioms GFNBounds.Graph.SamplerWiring.samplerLaw_nonneg
#print axioms GFNBounds.Graph.SamplerWiring.sum_samplerLaw
#print axioms GFNBounds.Graph.SamplerWiring.isSamplerLaw_prob
#print axioms GFNBounds.Graph.SamplerWiring.isSamplerLaw_termLaw
#print axioms GFNBounds.Graph.SamplerWiring.tvFin_le_one
#print axioms GFNBounds.Graph.SamplerWiring.samplerTV_le_one
#print axioms GFNBounds.Graph.SamplerWiring.sum_internal_snk
#print axioms GFNBounds.Graph.SamplerWiring.cyc_no_edge_src_snk
#print axioms GFNBounds.Graph.SamplerWiring.cyc_hss
#print axioms GFNBounds.Graph.SamplerWiring.cycle_sampler
#print axioms GFNBounds.Graph.SamplerWiring.Fk_termMass_pos
#print axioms GFNBounds.Graph.SamplerWiring.Fk_sampler
#print axioms GFNBounds.Graph.SamplerWiring.Fk_sampler_tv
#print axioms GFNBounds.Graph.SamplerWiring.cycle_counterexample_full
#print axioms GFNBounds.Graph.SamplerWiring.cycle_counterexample_full_check
#print axioms GFNBounds.Graph.SamplerWiring.no_bound_divergence_sampler
#print axioms GFNBounds.Graph.SamplerWiring.targetC_eq_extT
#print axioms GFNBounds.Graph.SamplerWiring.tvSet
#print axioms GFNBounds.Graph.SamplerWiring.extT_nonneg
#print axioms GFNBounds.Graph.SamplerWiring.sum_extT
#print axioms GFNBounds.Graph.SamplerWiring.sSup_tvSet
#print axioms GFNBounds.Graph.SamplerWiring.no_bound_divergence_minimax
#print axioms GFNBounds.Graph.SamplerWiring.cycle_flows_target_sampler
#print axioms GFNBounds.Graph.SamplerWiring.cycle_no_model_free_bound_sampler
#print axioms GFNBounds.Graph.SamplerWiring.cycle_no_bound_along_Fk_sampler
#print axioms GFNBounds.Graph.SamplerWiring.cycle_no_bound_punctured_sampler
#print axioms GFNBounds.Graph.SamplerWiring.cutFlow
#print axioms GFNBounds.Graph.SamplerWiring.cutFlow_nonneg
#print axioms GFNBounds.Graph.SamplerWiring.cutFlow_supp
#print axioms GFNBounds.Graph.SamplerWiring.cutFlow_cons
#print axioms GFNBounds.Graph.SamplerWiring.graphFlow_cutFlow
#print axioms GFNBounds.Graph.SamplerWiring.graphFlow_edgeFlow_finit
#print axioms GFNBounds.Graph.SamplerWiring.graphFlow_edgeFlow_fterm
#print axioms GFNBounds.Graph.SamplerWiring.outflowStar_eq_sum_internal
#print axioms GFNBounds.Graph.SamplerWiring.graphFlow_edgeFlow_fout
#print axioms GFNBounds.Graph.SamplerWiring.graphFlow_edgeFlow_P
#print axioms GFNBounds.Graph.SamplerWiring.sum_internal_termFlow
#print axioms GFNBounds.Graph.SamplerWiring.reach_src_eq
#print axioms GFNBounds.Graph.SamplerWiring.pb_snk_src_lt_one
#print axioms GFNBounds.Graph.SamplerWiring.edgeFlow_sampler
#print axioms GFNBounds.Graph.SamplerWiring.universality_graphs_sampler
#print axioms GFNBounds.Graph.SamplerWiring.universality_graphs_sampler_iff
#print axioms GFNBounds.Graph.SamplerWiring.universality_graphs_closing_sampler
#print axioms GFNBounds.Graph.SamplerWiring.sampler_check_triangle
#print axioms GFNBounds.Graph.SamplerWiring.closing_sampler_check_triangle
#print axioms GFNBounds.Graph.SamplerWiring.isSamplerLaw_subprob
#print axioms GFNBounds.Graph.SamplerWiring.samplerTV_le_one_general
#print axioms GFNBounds.Core.NegativeControl.defect
#print axioms GFNBounds.Core.NegativeControl.dInit
#print axioms GFNBounds.Core.NegativeControl.dTerm
#print axioms GFNBounds.Core.NegativeControl.hatInit
#print axioms GFNBounds.Core.NegativeControl.hatTerm
#print axioms GFNBounds.Core.NegativeControl.sampler
#print axioms GFNBounds.Core.NegativeControl.matched
#print axioms GFNBounds.Core.NegativeControl.errFlow
#print axioms GFNBounds.Core.NegativeControl.dInit_nonneg
#print axioms GFNBounds.Core.NegativeControl.dTerm_nonneg
#print axioms GFNBounds.Core.NegativeControl.defect_eq
#print axioms GFNBounds.Core.NegativeControl.matched_flowMatching
#print axioms GFNBounds.Core.NegativeControl.sampler_isGenFlow
#print axioms GFNBounds.Core.NegativeControl.matched_isGenFlow
#print axioms GFNBounds.Core.NegativeControl.errFlow_isGenFlow
#print axioms GFNBounds.Core.NegativeControl.sum_mul_div_sum
#print axioms GFNBounds.Core.NegativeControl.mixture
#print axioms GFNBounds.Core.NegativeControl.law_true_mono
#print axioms GFNBounds.Core.NegativeControl.sum_law_true_le_one
#print axioms GFNBounds.Core.NegativeControl.law_true_le_one
#print axioms GFNBounds.Core.NegativeControl.scaled_sum_law_true_le
#print axioms GFNBounds.Core.NegativeControl.sum_pos_of_ne_zero
#print axioms GFNBounds.Core.NegativeControl.negative_control
#print axioms GFNBounds.Core.NegativeControl.emass
#print axioms GFNBounds.Core.NegativeControl.inference
#print axioms GFNBounds.Core.NegativeControl.inference_dInit
#print axioms GFNBounds.Core.NegativeControl.inference_hatTerm
#print axioms GFNBounds.Core.NegativeControl.sampler_inference
#print axioms GFNBounds.Core.NegativeControl.sum_emass
#print axioms GFNBounds.Core.NegativeControl.eDens
#print axioms GFNBounds.Core.NegativeControl.mul_max_div
#print axioms GFNBounds.Core.NegativeControl.integral_posPart_eDens
#print axioms GFNBounds.Core.NegativeControl.integral_negPart_eDens
#print axioms GFNBounds.Core.NegativeControl.integral_eDens
#print axioms GFNBounds.Core.NegativeControl.tvD_count_form
#print axioms GFNBounds.Core.NegativeControl.negative_control_hNC
#print axioms GFNBounds.Core.NegativeControl.tv_le_two_fmL1_finite
#print axioms GFNBounds.Core.NegativeControl.Tight.flow
#print axioms GFNBounds.Core.NegativeControl.Tight.isGenFlow
#print axioms GFNBounds.Core.NegativeControl.Tight.finit_ne
#print axioms GFNBounds.Core.NegativeControl.Tight.hatTerm_eq
#print axioms GFNBounds.Core.NegativeControl.Tight.dInit_eq
#print axioms GFNBounds.Core.NegativeControl.Tight.law_succ_false
#print axioms GFNBounds.Core.NegativeControl.Tight.law_true
#print axioms GFNBounds.Core.NegativeControl.Tight.bound_attained
#print axioms GFNBounds.Balance.const_of_balanced_of_uniqueInvariant
#print axioms GFNBounds.Balance.eq_const_of_balanced_of_uniqueInvariant
#print axioms GFNBounds.Balance.continuous_meanL2
#print axioms GFNBounds.Balance.continuousAt_massVel
#print axioms GFNBounds.Balance.FlowGenerator.tendsto_of_flow
#print axioms GFNBounds.Balance.FlowGenerator.flow_floor
#print axioms GFNBounds.Balance.FlowGenerator.flow_pos
#print axioms GFNBounds.Balance.FlowGenerator.converges
#print axioms GFNBounds.Balance.FlowGenerator.existsUnique_converges
#print axioms GFNBounds.Balance.no_distant_equilibrium_three_logSq_of_ergodic
#print axioms GFNBounds.Balance.no_distant_equilibrium_three_sq_of_ergodic
#print axioms GFNBounds.Balance.no_distant_equilibrium_three_converges_logSq_of_ergodic
#print axioms GFNBounds.Balance.no_distant_equilibrium_three_converges_sq_of_ergodic
#print axioms GFNBounds.Balance.global_dichotomy_full_one_converges_of_ergodic
#print axioms GFNBounds.Balance.lossVal_sq_eq_zero_iff_balanced
#print axioms GFNBounds.Balance.entry_time_sq
#print axioms GFNBounds.Balance.twoState_sq_converges_check
#print axioms GFNBounds.Balance.lazyRotK
#print axioms GFNBounds.Balance.lazyRotLam
#print axioms GFNBounds.Balance.lazyRotU
#print axioms GFNBounds.Balance.lazyRotK_nonneg
#print axioms GFNBounds.Balance.lazyRotK_row
#print axioms GFNBounds.Balance.lazyRotK_invariant
#print axioms GFNBounds.Balance.lazyRotLam_pos
#print axioms GFNBounds.Balance.lazyRotU_pos
#print axioms GFNBounds.Balance.lazyRot_not_reversible
#print axioms GFNBounds.Balance.lazyRot_uniqueInvariant
#print axioms GFNBounds.Balance.lazyRot_converges_check
#print axioms GFNBounds.Core.RLBound.holderConst_nonneg
#print axioms GFNBounds.Core.RLBound.holderConst_top
#print axioms GFNBounds.Core.RLBound.one_sub_inv_nonneg
#print axioms GFNBounds.Core.RLBound.lintegral_enorm_le_holderConst
#print axioms GFNBounds.Core.RLBound.integral_abs_le_holderConst
#print axioms GFNBounds.Core.RLBound.stableLoss_eq_toReal_eLpNorm
#print axioms GFNBounds.Core.RLBound.mass_floorE
#print axioms GFNBounds.Core.RLBound.stable_boundE
#print axioms GFNBounds.Core.RLBound.eFn
#print axioms GFNBounds.Core.RLBound.defectFn_eq_eFn_sub
#print axioms GFNBounds.Core.RLBound.integrable_eFn
#print axioms GFNBounds.Core.RLBound.integral_eFn
#print axioms GFNBounds.Core.RLBound.mass_floor_kernel
#print axioms GFNBounds.Core.RLBound.stable_bound_kernel
#print axioms GFNBounds.Core.RLBound.stable_bound_finite
#print axioms GFNBounds.Core.RLBound.conjExp
#print axioms GFNBounds.Core.RLBound.holderConjugate_conjExp
#print axioms GFNBounds.Core.RLBound.rho
#print axioms GFNBounds.Core.RLBound.transferConst
#print axioms GFNBounds.Core.RLBound.transferConst_ne_top
#print axioms GFNBounds.Core.RLBound.memLp_rho_top
#print axioms GFNBounds.Core.RLBound.eLpNorm_le_transferConst
#print axioms GFNBounds.Core.RLBound.eLpNorm_defectFn_le_residual
#print axioms GFNBounds.Core.RLBound.loss_le_transferConst_mul_residual
#print axioms GFNBounds.Core.RLBound.inf_loss_eq_zero
#print axioms GFNBounds.Core.RLBound.inf_loss_eq_zero_top
#print axioms GFNBounds.Core.RLBound.IsInitialFamily
#print axioms GFNBounds.Core.RLBound.massSet
#print axioms GFNBounds.Core.RLBound.massSetLp
#print axioms GFNBounds.Core.RLBound.massSetLp_eq_massSet
#print axioms GFNBounds.Core.RLBound.ofReal_mass_gap_le
#print axioms GFNBounds.Core.RLBound.joint_inf_eq_zero
#print axioms GFNBounds.Core.RLBound.mem_closure_of_joint_inf
#print axioms GFNBounds.Core.RLBound.joint_infimum
#print axioms GFNBounds.Core.RLBound.memLp_rho_self
#print axioms GFNBounds.Core.RLBound.inf_loss_eq_zero_const_kernel
#print axioms GFNBounds.Core.ILBoundFull.padeAux_mono
#print axioms GFNBounds.Core.ILBoundFull.padeAux_sign
#print axioms GFNBounds.Core.ILBoundFull.pollardAux
#print axioms GFNBounds.Core.ILBoundFull.pollardAux_hasDerivAt
#print axioms GFNBounds.Core.ILBoundFull.continuous_pollardAux
#print axioms GFNBounds.Core.ILBoundFull.pollard_ineq
#print axioms GFNBounds.Core.ILBoundFull.pollard_two
#print axioms GFNBounds.Core.ILBoundFull.pinsker_pointwise
#print axioms GFNBounds.Core.ILBoundFull.pinsker
#print axioms GFNBounds.Core.ILBoundFull.lqNormE
#print axioms GFNBounds.Core.ILBoundFull.lqNormE_nonneg
#print axioms GFNBounds.Core.ILBoundFull.lqNormE_eq_lqNormD
#print axioms GFNBounds.Core.ILBoundFull.wklfmLossE
#print axioms GFNBounds.Core.ILBoundFull.wklfmLossE_eq_wklfmLoss
#print axioms GFNBounds.Core.ILBoundFull.il_holderE
#print axioms GFNBounds.Core.ILBoundFull.crossEntropy_decomposition
#print axioms GFNBounds.Core.ILBoundFull.lossE_sub_selfEntropy_ge
#print axioms GFNBounds.Core.ILBoundFull.il_bullet_one_dens
#print axioms GFNBounds.Core.ILBoundFull.LossFinite
#print axioms GFNBounds.Core.ILBoundFull.ilLoss
#print axioms GFNBounds.Core.ILBoundFull.ilLoss_of_finite
#print axioms GFNBounds.Core.ILBoundFull.finite_of_ilLoss_ne_top
#print axioms GFNBounds.Core.ILBoundFull.crossEntropy_posPart_integrable
#print axioms GFNBounds.Core.ILBoundFull.InflowAC
#print axioms GFNBounds.Core.ILBoundFull.eFlow
#print axioms GFNBounds.Core.ILBoundFull.inflowAC_of_bind_ac
#print axioms GFNBounds.Core.ILBoundFull.densityAction_of_inflowAC
#print axioms GFNBounds.Core.ILBoundFull.eFlow_integral
#print axioms GFNBounds.Core.ILBoundFull.rnNorm
#print axioms GFNBounds.Core.ILBoundFull.il_first_bullet_dens
#print axioms GFNBounds.Core.ILBoundFull.il_first_bullet
#print axioms GFNBounds.Core.ILBoundFull.il_tv_le_sqrt
#print axioms GFNBounds.Core.ILBoundFull.crossEntropy_integrable_of_domination
#print axioms GFNBounds.Core.ILBoundFull.il_member_le
#print axioms GFNBounds.Core.ILBoundFull.ereal_le_of_forall_pos
#print axioms GFNBounds.Core.ILBoundFull.il_iInf_eq
#print axioms GFNBounds.Core.ILBoundFull.il_attained
#print axioms GFNBounds.Core.ILBoundFull.il_attained_of_stronglyUniversal
#print axioms GFNBounds.Core.ILBoundFull.il_first_bullet_finite
#print axioms GFNBounds.Core.ILBoundFull.Example.flow
#print axioms GFNBounds.Core.ILBoundFull.Example.ilLoss_ne_top
#print axioms GFNBounds.Graph.PartialSupportClose.IsTargetI
#print axioms GFNBounds.Graph.PartialSupportClose.IsTargetI.isTarget
#print axioms GFNBounds.Graph.PartialSupportClose.Deleted
#print axioms GFNBounds.Graph.PartialSupportClose.subGraphI
#print axioms GFNBounds.Graph.PartialSupportClose.subGraphI_edge_iff_of_not_edge
#print axioms GFNBounds.Graph.PartialSupportClose.subGraph_edge_imp
#print axioms GFNBounds.Graph.PartialSupportClose.subGraphI_pathConnected
#print axioms GFNBounds.Graph.PartialSupportClose.mem_subVerts_of_not_deleted
#print axioms GFNBounds.Graph.PartialSupportClose.IsSinkRowI
#print axioms GFNBounds.Graph.PartialSupportClose.restrictWithI
#print axioms GFNBounds.Graph.PartialSupportClose.restrictWithI_pb_of_ne_snk
#print axioms GFNBounds.Graph.PartialSupportClose.restrictWithI_pb_snk
#print axioms GFNBounds.Graph.PartialSupportClose.restrictWithI_positiveOnEdges
#print axioms GFNBounds.Graph.PartialSupportClose.sinkMassI
#print axioms GFNBounds.Graph.PartialSupportClose.renormRowI
#print axioms GFNBounds.Graph.PartialSupportClose.sinkMassI_pos
#print axioms GFNBounds.Graph.PartialSupportClose.isSinkRowI_renormRowI
#print axioms GFNBounds.Graph.PartialSupportClose.restrict_policyI
#print axioms GFNBounds.Graph.PartialSupportClose.frozenRow
#print axioms GFNBounds.Graph.PartialSupportClose.IsSrcWeight
#print axioms GFNBounds.Graph.PartialSupportClose.exists_srcWeight
#print axioms GFNBounds.Graph.PartialSupportClose.frozenRow_of_ne_src
#print axioms GFNBounds.Graph.PartialSupportClose.isSinkRowI_frozenRow
#print axioms GFNBounds.Graph.PartialSupportClose.partial_support_exactI
#print axioms GFNBounds.Graph.PartialSupportClose.partial_support_not_in_GI
#print axioms GFNBounds.Graph.PartialSupportClose.unifI
#print axioms GFNBounds.Graph.PartialSupportClose.epsTargetI
#print axioms GFNBounds.Graph.PartialSupportClose.unifI_nonneg
#print axioms GFNBounds.Graph.PartialSupportClose.card_terminating_pos
#print axioms GFNBounds.Graph.PartialSupportClose.unifI_le_one
#print axioms GFNBounds.Graph.PartialSupportClose.unifI_pos
#print axioms GFNBounds.Graph.PartialSupportClose.unifI_eq_zero
#print axioms GFNBounds.Graph.PartialSupportClose.sum_unifI
#print axioms GFNBounds.Graph.PartialSupportClose.exists_terminatingI
#print axioms GFNBounds.Graph.PartialSupportClose.isTargetI_epsTargetI
#print axioms GFNBounds.Graph.PartialSupportClose.epsTargetI_pos
#print axioms GFNBounds.Graph.PartialSupportClose.sum_epsTargetI
#print axioms GFNBounds.Graph.PartialSupportClose.member_epsTargetI
#print axioms GFNBounds.Graph.PartialSupportClose.iInf_graphResidual_eq_zeroI
#print axioms GFNBounds.Graph.PartialSupportClose.graphResidual_ne_zeroI
#print axioms GFNBounds.Graph.PartialSupportClose.diamondE
#print axioms GFNBounds.Graph.PartialSupportClose.diamondETarget
#print axioms GFNBounds.Graph.PartialSupportClose.diamondE_check
#print axioms GFNBounds.Graph.PartialSupportClose.diamondE_partial_support
#print axioms GFNBounds.Silva.PathSpaceMarkov.cycTail
#print axioms GFNBounds.Silva.PathSpaceMarkov.cycTraj
#print axioms GFNBounds.Silva.PathSpaceMarkov.cycTail_succ
#print axioms GFNBounds.Silva.PathSpaceMarkov.cycTail_eq_cons
#print axioms GFNBounds.Silva.PathSpaceMarkov.length_cycTail
#print axioms GFNBounds.Silva.PathSpaceMarkov.cycTail_eq_append
#print axioms GFNBounds.Silva.PathSpaceMarkov.cycTraj_eq_append
#print axioms GFNBounds.Silva.PathSpaceMarkov.cycTraj_injective
#print axioms GFNBounds.Silva.PathSpaceMarkov.edge_xC_iff
#print axioms GFNBounds.Silva.PathSpaceMarkov.edge_srcC_iff
#print axioms GFNBounds.Silva.PathSpaceMarkov.natCast_succ_fin
#print axioms GFNBounds.Silva.PathSpaceMarkov.isChain_cycTail
#print axioms GFNBounds.Silva.PathSpaceMarkov.isChain_cycTraj
#print axioms GFNBounds.Silva.PathSpaceMarkov.eq_cycTail_of_walk
#print axioms GFNBounds.Silva.PathSpaceMarkov.eq_cycTraj
#print axioms GFNBounds.Silva.PathSpaceMarkov.cycPol
#print axioms GFNBounds.Silva.PathSpaceMarkov.cycPol_src
#print axioms GFNBounds.Silva.PathSpaceMarkov.cycPol_x_snk
#print axioms GFNBounds.Silva.PathSpaceMarkov.cycPol_x_x
#print axioms GFNBounds.Silva.PathSpaceMarkov.cycPol_x_src
#print axioms GFNBounds.Silva.PathSpaceMarkov.cycPol_snk
#print axioms GFNBounds.Silva.PathSpaceMarkov.cycPol_nonneg
#print axioms GFNBounds.Silva.PathSpaceMarkov.cycPol_pos_of_edge
#print axioms GFNBounds.Silva.PathSpaceMarkov.cycPol_supp
#print axioms GFNBounds.Silva.PathSpaceMarkov.cycPol_row_sum
#print axioms GFNBounds.Silva.PathSpaceMarkov.pathProb_cycTail
#print axioms GFNBounds.Silva.PathSpaceMarkov.pathProb_cycTraj
#print axioms GFNBounds.Silva.PathSpaceMarkov.hasSum_cycTraj
#print axioms GFNBounds.Silva.PathSpaceMarkov.pathProb_cycTraj_ge
#print axioms GFNBounds.Silva.PathSpaceMarkov.natCast_fin_add_mul
#print axioms GFNBounds.Silva.PathSpaceMarkov.exists_mul_lt
#print axioms GFNBounds.Silva.PathSpaceMarkov.cycle_exists_ratio_gt_markov
#print axioms GFNBounds.Silva.PathSpaceMarkov.cycle_ratio_not_bddAbove_markov
#print axioms GFNBounds.Silva.PathSpaceMarkov.inhabit_markov_cycle
#print axioms GFNBounds.Doubling.RenewalClose.kernInf
#print axioms GFNBounds.Doubling.RenewalClose.kernInf_pos
#print axioms GFNBounds.Doubling.RenewalClose.kern_ge
#print axioms GFNBounds.Doubling.RenewalClose.kbar_le_one
#print axioms GFNBounds.Doubling.RenewalClose.sup_mul_sub_G_le
#print axioms GFNBounds.Doubling.RenewalClose.neg_solution
#print axioms GFNBounds.Doubling.RenewalClose.Gfun_neg
#print axioms GFNBounds.Doubling.RenewalClose.renewal_solution_const
#print axioms GFNBounds.Doubling.RenewalClose.renewal_limit_trivial
#print axioms GFNBounds.Balance.lamMinOf
#print axioms GFNBounds.Balance.supAbsOf
#print axioms GFNBounds.Balance.lamMinOf_le
#print axioms GFNBounds.Balance.exists_lamMinOf_eq
#print axioms GFNBounds.Balance.lamMinOf_pos
#print axioms GFNBounds.Balance.abs_le_supAbsOf
#print axioms GFNBounds.Balance.exists_supAbsOf_eq
#print axioms GFNBounds.Balance.tendsto_of_exp_decay
#print axioms GFNBounds.Balance.local_convergence_full_paper
#print axioms GFNBounds.Balance.local_convergence_full_DB_paper
#print axioms GFNBounds.Balance.twoState_DB_exists_check
#print axioms GFNBounds.Doubling.pstar_const_mul
#print axioms GFNBounds.Doubling.pstar_one_sub
#print axioms GFNBounds.Doubling.pstar_ge_ptFn_mul
#print axioms GFNBounds.Doubling.pstar_iterate_mono
#print axioms GFNBounds.Doubling.pstar_iterate_nonneg
#print axioms GFNBounds.Doubling.pstar_iterate_const_mul
#print axioms GFNBounds.Doubling.pstar_iterate_ge_ptFn_mul
#print axioms GFNBounds.Doubling.fpass
#print axioms GFNBounds.Doubling.fpass_zero
#print axioms GFNBounds.Doubling.fpass_succ
#print axioms GFNBounds.Doubling.fpass_succ_self
#print axioms GFNBounds.Doubling.fpass_succ_of_ne
#print axioms GFNBounds.Doubling.fpass_nonneg
#print axioms GFNBounds.Doubling.hitP
#print axioms GFNBounds.Doubling.hitP_zero
#print axioms GFNBounds.Doubling.hitP_nonneg
#print axioms GFNBounds.Doubling.hitP_mono
#print axioms GFNBounds.Doubling.hitP_succ
#print axioms GFNBounds.Doubling.hitP_self
#print axioms GFNBounds.Doubling.hitP_succ_of_ne
#print axioms GFNBounds.Doubling.hitP_le_one
#print axioms GFNBounds.Doubling.hitP_bdd
#print axioms GFNBounds.Doubling.hitProb
#print axioms GFNBounds.Doubling.tendsto_hitP
#print axioms GFNBounds.Doubling.hitP_le_hitProb
#print axioms GFNBounds.Doubling.hitProb_nonneg
#print axioms GFNBounds.Doubling.hitProb_le_one
#print axioms GFNBounds.Doubling.hitProb_self
#print axioms GFNBounds.Doubling.hitProb_solution
#print axioms GFNBounds.Doubling.hitP_le_of_super
#print axioms GFNBounds.Doubling.hitProb_le_of_super
#print axioms GFNBounds.Doubling.retP
#print axioms GFNBounds.Doubling.retProb
#print axioms GFNBounds.Doubling.retP_nonneg
#print axioms GFNBounds.Doubling.retP_le_one
#print axioms GFNBounds.Doubling.retP_mono
#print axioms GFNBounds.Doubling.tendsto_retP
#print axioms GFNBounds.Doubling.retP_le_retProb
#print axioms GFNBounds.Doubling.retProb_le_one
#print axioms GFNBounds.Doubling.retProb_nonneg
#print axioms GFNBounds.Doubling.hitT
#print axioms GFNBounds.Doubling.hitT_zero
#print axioms GFNBounds.Doubling.hitT_succ
#print axioms GFNBounds.Doubling.hitT_self
#print axioms GFNBounds.Doubling.hitT_succ_sub
#print axioms GFNBounds.Doubling.hitT_nonneg
#print axioms GFNBounds.Doubling.hitT_mono_succ
#print axioms GFNBounds.Doubling.hitT_mono
#print axioms GFNBounds.Doubling.hitT_le_nat
#print axioms GFNBounds.Doubling.hitT_bounded
#print axioms GFNBounds.Doubling.hitT_le_of_super
#print axioms GFNBounds.Doubling.hitTime_solution
#print axioms GFNBounds.Doubling.retT
#print axioms GFNBounds.Doubling.retT_zero
#print axioms GFNBounds.Doubling.retT_succ_sub
#print axioms GFNBounds.Doubling.retT_mono
#print axioms GFNBounds.Doubling.one_le_retT
#print axioms GFNBounds.Doubling.IsRecurrentAt
#print axioms GFNBounds.Doubling.IsTransientAt
#print axioms GFNBounds.Doubling.IsPosRecurrentAt
#print axioms GFNBounds.Doubling.IsNullRecurrentAt
#print axioms GFNBounds.Doubling.IsPositiveRecurrent
#print axioms GFNBounds.Doubling.IsNullRecurrent
#print axioms GFNBounds.Doubling.IsRecurrent
#print axioms GFNBounds.Doubling.IsTransient
#print axioms GFNBounds.Doubling.isTransientAt_iff_not_recurrent
#print axioms GFNBounds.Doubling.isRecurrentAt_of_bdd
#print axioms GFNBounds.Doubling.Stat.summable_mul_sub_pstar
#print axioms GFNBounds.Doubling.Stat.kac_hitP
#print axioms GFNBounds.Doubling.Stat.lam_mul_retT_le
#print axioms GFNBounds.Doubling.Stat.retT_bdd
#print axioms GFNBounds.Doubling.Stat.isPosRecurrentAt
#print axioms GFNBounds.Doubling.Stat.isPositiveRecurrent
#print axioms GFNBounds.Doubling.hitProb_eq_one_of_reach
#print axioms GFNBounds.Doubling.reach_iterate_pos
#print axioms GFNBounds.Doubling.Stat.kac_eq
#print axioms GFNBounds.Doubling.Stat.lam_eq_inv
#print axioms GFNBounds.Doubling.stat_unique_none
#print axioms GFNBounds.Doubling.renewal_green_le
#print axioms GFNBounds.Doubling.renewal_green_unbdd
#print axioms GFNBounds.Doubling.renewal_summed
#print axioms GFNBounds.Doubling.renewal_green_ge
#print axioms GFNBounds.Doubling.renewal_green_sublinear
#print axioms GFNBounds.Doubling.uRet
#print axioms GFNBounds.Doubling.fRet
#print axioms GFNBounds.Doubling.rTail
#print axioms GFNBounds.Doubling.uRet_nonneg
#print axioms GFNBounds.Doubling.fRet_nonneg
#print axioms GFNBounds.Doubling.retP_eq_sum
#print axioms GFNBounds.Doubling.rTail_zero
#print axioms GFNBounds.Doubling.rTail_succ
#print axioms GFNBounds.Doubling.rTail_nonneg
#print axioms GFNBounds.Doubling.rTail_le_one
#print axioms GFNBounds.Doubling.rTail_anti
#print axioms GFNBounds.Doubling.retT_eq_sum
#print axioms GFNBounds.Doubling.iter_ptFn_eq
#print axioms GFNBounds.Doubling.uRet_succ
#print axioms GFNBounds.Doubling.renewal_key
#print axioms GFNBounds.Doubling.green
#print axioms GFNBounds.Doubling.green_le_of_transient
#print axioms GFNBounds.Doubling.green_unbdd_of_recurrent
#print axioms GFNBounds.Doubling.green_ge_of_posRecurrent
#print axioms GFNBounds.Doubling.green_sublinear_of_not_bdd
#print axioms GFNBounds.Doubling.uRet_comparison
#print axioms GFNBounds.Doubling.green_comparison
#print axioms GFNBounds.Doubling.exists_comparison_const
#print axioms GFNBounds.Doubling.recurrent_solidarity
#print axioms GFNBounds.Doubling.transient_solidarity
#print axioms GFNBounds.Doubling.posRecurrent_solidarity
#print axioms GFNBounds.Doubling.nullRecurrent_solidarity
#print axioms GFNBounds.Doubling.sv
#print axioms GFNBounds.Doubling.sv_zero
#print axioms GFNBounds.Doubling.sv_succ
#print axioms GFNBounds.Doubling.sv_nonneg
#print axioms GFNBounds.Doubling.sv_src
#print axioms GFNBounds.Doubling.ladT_one_succ
#print axioms GFNBounds.Doubling.ladT_stepCost_le
#print axioms GFNBounds.Doubling.sv_le_one
#print axioms GFNBounds.Doubling.sv_anti_succ
#print axioms GFNBounds.Doubling.sv_anti
#print axioms GFNBounds.Doubling.tendsto_ladT
#print axioms GFNBounds.Doubling.ladT_affine
#print axioms GFNBounds.Doubling.pdown
#print axioms GFNBounds.Doubling.pdown_pos
#print axioms GFNBounds.Doubling.pdown_le_one
#print axioms GFNBounds.Doubling.pdown_anti
#print axioms GFNBounds.Doubling.sv_le_pdown
#print axioms GFNBounds.Doubling.LDom
#print axioms GFNBounds.Doubling.ldom_refl
#print axioms GFNBounds.Doubling.ldom_trans
#print axioms GFNBounds.Doubling.ldom_double
#print axioms GFNBounds.Doubling.ldom_dec
#print axioms GFNBounds.Doubling.ldom_down
#print axioms GFNBounds.Doubling.ldom_all
#print axioms GFNBounds.Doubling.sv_ldom
#print axioms GFNBounds.Doubling.ladder_recurrent
#print axioms GFNBounds.Doubling.ladder_survival_ge
#print axioms GFNBounds.Doubling.hitLad_ge_min
#print axioms GFNBounds.Doubling.hitLad_ge_iterate
#print axioms GFNBounds.Doubling.hitLad_bdd_of_ldom
#print axioms GFNBounds.Doubling.hitLad_unbdd
#print axioms GFNBounds.Doubling.one_sub_hitP_src
#print axioms GFNBounds.Doubling.one_sub_retP_src
#print axioms GFNBounds.Doubling.hitT_src_lad
#print axioms GFNBounds.Doubling.retT_src_succ
#print axioms GFNBounds.Doubling.pstar_lad_eq_ladT
#print axioms GFNBounds.Doubling.recurrent_src_of_sv
#print axioms GFNBounds.Doubling.transient_src_of_sv
#print axioms GFNBounds.Doubling.not_posRecurrent_src
#print axioms GFNBounds.Doubling.transient_of_Wpow
#print axioms GFNBounds.Doubling.recurrent_of_logHeight
#print axioms GFNBounds.Doubling.phase_gt_one
#print axioms GFNBounds.Doubling.phase_lt_one
#print axioms GFNBounds.Doubling.phase_one_lt
#print axioms GFNBounds.Doubling.phase_one_ge
#print axioms GFNBounds.Doubling.phase_one_recurrent
#print axioms GFNBounds.Doubling.phase_one_null
#print axioms GFNBounds.Doubling.phase_one_transient
#print axioms GFNBounds.Doubling.exists_family_setting
#print axioms GFNBounds.Doubling.prop_doubling_phase
#print axioms GFNBounds.Doubling.main_phase_classes
#print axioms GFNBounds.Doubling.main_invariant_unique
