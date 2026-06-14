import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaZeroTail.ZetaZeroMultiplicitySummability.ZetaZeroMultiplicityCounting.ZetaCompletedZeroJensen.ZetaEntireJensen.EntireJensenFormula.LogSineCircleKernel.Owner

/-!
# Boundary zero-factor decomposition

This file is a sequential owner sublayer split from the Jensen formula owner.
Declaration order is preserved so downstream import behavior remains routed
through `EntireJensenFormula.Owner`.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open scoped Topology

theorem entireFunction_unitCircle_boundaryZero_log_mean_zero_ownerRoot
    (α : ℝ) :
    (2 * Real.pi)⁻¹ *
        (∫ θ in (0 : ℝ)..(2 * Real.pi),
          Real.log ‖1 - Complex.exp ((θ - α) * Complex.I)‖) =
      0 := by
  exact unitCircleLogKernel_translated_mean_zero α

/-- Boundary zero single-factor mean.

When `‖a‖ = ρ`, the Jensen boundary factor
`θ ↦ log ‖1 - ρ e^{iθ} / a‖` has normalized mean zero.  This is the
boundary-zero counterpart of the strict-interior single-factor theorem.  The
local logarithmic singularity at the unique boundary parameter is handled by
the finite logarithmic-singularity machinery later in this file. -/
theorem entireFunction_singleZeroFactor_boundaryAverage_eq_zero_of_norm_eq_radius_ownerRoot
    {a : ℂ}
    {ρ : ℝ}
    (ha0 : a ≠ 0)
    (haρ : ‖a‖ = ρ) :
    (2 * Real.pi)⁻¹ *
        (∫ θ in (0 : ℝ)..(2 * Real.pi),
          Real.log
            ‖1 - (((ρ : ℂ) * Complex.exp (θ * Complex.I)) / a)‖) =
      0 := by
  have hρ_pos : 0 < ρ :=
    Eq.subst (motive := fun x : ℝ => 0 < x) haρ
      (norm_pos_iff.mpr ha0)
  let α : ℝ := Complex.arg a
  have hρ_ne : (ρ : ℂ) ≠ 0 :=
    ofReal_ne_zero.mpr hρ_pos.ne'
  have ha_eq : a = (ρ : ℂ) * Complex.exp (α * Complex.I) := by
    have hpolar :
        a = (‖a‖ : ℂ) * Complex.exp (α * Complex.I) := by
      have hexp_log : Complex.exp (Complex.log a) = a :=
        Complex.exp_log ha0
      have hlog :
          Complex.log a = (Real.log ‖a‖ : ℂ) + α * Complex.I := by
        rfl
      have hexp_split :
          Complex.exp (Complex.log a) =
            Complex.exp (Real.log ‖a‖ : ℂ) *
              Complex.exp (α * Complex.I) := by
        exact Eq.trans
          (congrArg Complex.exp hlog)
          (Complex.exp_add (Real.log ‖a‖ : ℂ) (α * Complex.I))
      have hexp_re :
          Complex.exp (Real.log ‖a‖ : ℂ) = (‖a‖ : ℂ) := by
        exact Complex.ofReal_exp (Real.log ‖a‖) ▸
          congrArg (fun x : ℝ => (x : ℂ))
            (Real.exp_log (norm_pos_iff.mpr ha0))
      exact Eq.trans hexp_log.symm
        (Eq.trans hexp_split
          (congrArg (fun x : ℂ => x * Complex.exp (α * Complex.I)) hexp_re))
    have hnorm_eq : (‖a‖ : ℂ) = (ρ : ℂ) :=
      congrArg (fun x : ℝ => (x : ℂ)) haρ
    exact Eq.trans hpolar
      (congrArg (fun x : ℂ => x * Complex.exp (α * Complex.I)) hnorm_eq)
  have hintegrand :
      (fun θ : ℝ =>
        Real.log
          ‖1 - (((ρ : ℂ) * Complex.exp (θ * Complex.I)) / a)‖) =
      (fun θ : ℝ =>
        Real.log ‖1 - Complex.exp ((θ - α) * Complex.I)‖) := by
    funext θ
    have hdiv :
        (((ρ : ℂ) * Complex.exp (θ * Complex.I)) / a) =
          Complex.exp ((θ - α) * Complex.I) := by
      calc
        (((ρ : ℂ) * Complex.exp (θ * Complex.I)) / a) =
            ((ρ : ℂ) * Complex.exp (θ * Complex.I)) /
              ((ρ : ℂ) * Complex.exp (α * Complex.I)) := by
          exact congrArg (fun x : ℂ => ((ρ : ℂ) * Complex.exp (θ * Complex.I)) / x) ha_eq
        _ =
            (((ρ : ℂ) * Complex.exp (θ * Complex.I)) *
              (((ρ : ℂ) * Complex.exp (α * Complex.I))⁻¹)) := by
          exact div_eq_mul_inv
            ((ρ : ℂ) * Complex.exp (θ * Complex.I))
            ((ρ : ℂ) * Complex.exp (α * Complex.I))
        _ =
            ((ρ : ℂ) * Complex.exp (θ * Complex.I)) *
              ((ρ : ℂ)⁻¹ * (Complex.exp (α * Complex.I))⁻¹) := by
          exact congrArg
            (fun x : ℂ => ((ρ : ℂ) * Complex.exp (θ * Complex.I)) * x)
            (mul_inv_rev (ρ : ℂ) (Complex.exp (α * Complex.I)))
        _ =
            (((ρ : ℂ) * (ρ : ℂ)⁻¹) *
              (Complex.exp (θ * Complex.I) *
                (Complex.exp (α * Complex.I))⁻¹)) := by
          calc
            ((ρ : ℂ) * Complex.exp (θ * Complex.I)) *
                ((ρ : ℂ)⁻¹ * (Complex.exp (α * Complex.I))⁻¹) =
                (ρ : ℂ) *
                  (Complex.exp (θ * Complex.I) *
                    ((ρ : ℂ)⁻¹ * (Complex.exp (α * Complex.I))⁻¹)) := by
              exact mul_assoc (ρ : ℂ) (Complex.exp (θ * Complex.I))
                ((ρ : ℂ)⁻¹ * (Complex.exp (α * Complex.I))⁻¹)
            _ =
                (ρ : ℂ) *
                  ((Complex.exp (θ * Complex.I) * (ρ : ℂ)⁻¹) *
                    (Complex.exp (α * Complex.I))⁻¹) := by
              exact congrArg (fun x : ℂ => (ρ : ℂ) * x)
                (mul_assoc (Complex.exp (θ * Complex.I)) (ρ : ℂ)⁻¹
                  (Complex.exp (α * Complex.I))⁻¹)
            _ =
                (ρ : ℂ) *
                  (((ρ : ℂ)⁻¹ * Complex.exp (θ * Complex.I)) *
                    (Complex.exp (α * Complex.I))⁻¹) := by
              exact congrArg
                (fun x : ℂ =>
                  (ρ : ℂ) * (x * (Complex.exp (α * Complex.I))⁻¹))
                (mul_comm (Complex.exp (θ * Complex.I)) (ρ : ℂ)⁻¹)
            _ =
                ((ρ : ℂ) * (ρ : ℂ)⁻¹) *
                  (Complex.exp (θ * Complex.I) *
                    (Complex.exp (α * Complex.I))⁻¹) := by
              exact (mul_assoc (ρ : ℂ) (ρ : ℂ)⁻¹
                (Complex.exp (θ * Complex.I) *
                  (Complex.exp (α * Complex.I))⁻¹)).symm
        _ =
            1 *
              (Complex.exp (θ * Complex.I) *
                (Complex.exp (α * Complex.I))⁻¹) := by
          exact congrArg
            (fun x : ℂ =>
              x *
                (Complex.exp (θ * Complex.I) *
                  (Complex.exp (α * Complex.I))⁻¹))
            (mul_inv_cancel₀ hρ_ne)
        _ =
            Complex.exp (θ * Complex.I) *
              (Complex.exp (α * Complex.I))⁻¹ := by
          exact one_mul
            (Complex.exp (θ * Complex.I) *
              (Complex.exp (α * Complex.I))⁻¹)
        _ =
            Complex.exp (θ * Complex.I) *
              Complex.exp (-(α * Complex.I)) := by
          exact congrArg (fun x : ℂ => Complex.exp (θ * Complex.I) * x)
            (Complex.exp_neg (α * Complex.I)).symm
        _ =
            Complex.exp (θ * Complex.I + -(α * Complex.I)) := by
          exact (Complex.exp_add (θ * Complex.I) (-(α * Complex.I))).symm
        _ =
            Complex.exp ((θ - α) * Complex.I) := by
          have harg :
              θ * Complex.I + -(α * Complex.I) = (θ - α) * Complex.I := by
            calc
              θ * Complex.I + -(α * Complex.I) =
                  θ * Complex.I + (-α) * Complex.I := by
                exact congrArg (fun x : ℂ => θ * Complex.I + x)
                  (neg_mul_eq_neg_mul (α : ℂ) Complex.I).symm
              _ = ((θ : ℂ) + (-α : ℂ)) * Complex.I := by
                exact (add_mul (θ : ℂ) (-α : ℂ) Complex.I).symm
              _ = (θ - α) * Complex.I := by
                exact congrArg (fun x : ℂ => x * Complex.I) (sub_eq_add_neg θ α).symm
          exact congrArg Complex.exp harg
    exact congrArg (fun x : ℂ => Real.log ‖1 - x‖) hdiv
  exact Eq.subst
    (motive := fun f : ℝ → ℝ =>
      (2 * Real.pi)⁻¹ * (∫ θ in (0 : ℝ)..(2 * Real.pi), f θ) = 0)
    hintegrand.symm
    (entireFunction_unitCircle_boundaryZero_log_mean_zero_ownerRoot α)

/-- A closed-boundary support factor has zero normalized boundary mean. -/
theorem entireFunction_standardJensenFormula_nonzeroAtOrigin_closedDiskBoundarySupportFiniteZeroDivisor_boundaryAverage_eq_zero
    (F : ℂ → ℂ)
    (hF : ∀ z : ℂ, AnalyticAt ℂ F z)
    (hF0 : F 0 ≠ 0)
    (ρ : ℝ)
    (z : EntireFunctionZero F)
    (hz :
      z ∈
        entireFunction_standardJensenFormula_nonzeroAtOrigin_closedDiskBoundarySupportFiniteZeroDivisor
          F hF hF0 ρ) :
    (2 * Real.pi)⁻¹ *
        (∫ θ in (0 : ℝ)..(2 * Real.pi),
          Real.log
            ‖1 - (((ρ : ℂ) * Complex.exp (θ * Complex.I)) / (z : ℂ))‖) =
      0 := by
  have hz_closed :
      z ∈
        entireFunction_standardJensenFormula_nonzeroAtOrigin_closedDiskSupportFiniteZeroDivisor
          F hF hF0 ρ :=
    (Finset.mem_filter.1 hz).1
  have hz0 : (z : ℂ) ≠ 0 :=
    entireFunction_standardJensenFormula_nonzeroAtOrigin_closedDiskSupportFiniteZeroDivisor_mem_ne_zero
      F hF hF0 ρ z hz_closed
  have hnorm :
      ‖(z : ℂ)‖ = ρ :=
    entireFunction_standardJensenFormula_nonzeroAtOrigin_closedDiskBoundarySupportFiniteZeroDivisor_mem_norm_eq
      F hF hF0 ρ z hz
  exact
    entireFunction_singleZeroFactor_boundaryAverage_eq_zero_of_norm_eq_radius_ownerRoot
      (a := (z : ℂ)) (ρ := ρ) hz0 hnorm

/-- Boundary support factors contribute zero to the normalized boundary-factor
sum. -/
theorem entireFunction_standardJensenFormula_nonzeroAtOrigin_closedDiskBoundarySupportFiniteZeroDivisor_boundaryFactorSum_eq_zero
    (F : ℂ → ℂ)
    (hF : ∀ z : ℂ, AnalyticAt ℂ F z)
    (hF0 : F 0 ≠ 0)
    (ρ : ℝ) :
    (∑ z in
      entireFunction_standardJensenFormula_nonzeroAtOrigin_closedDiskBoundarySupportFiniteZeroDivisor
        F hF hF0 ρ,
      (entireFunctionZeroMultiplicity F hF (z : ℂ) : ℝ) *
        ((2 * Real.pi)⁻¹ *
          (∫ θ in (0 : ℝ)..(2 * Real.pi),
            Real.log
              ‖1 - (((ρ : ℂ) * Complex.exp (θ * Complex.I)) / (z : ℂ))‖))) =
      0 := by
  exact
    Finset.sum_eq_zero
      (fun z hz =>
        calc
          (entireFunctionZeroMultiplicity F hF (z : ℂ) : ℝ) *
              ((2 * Real.pi)⁻¹ *
                (∫ θ in (0 : ℝ)..(2 * Real.pi),
                  Real.log
                    ‖1 - (((ρ : ℂ) * Complex.exp (θ * Complex.I)) / (z : ℂ))‖)) =
              (entireFunctionZeroMultiplicity F hF (z : ℂ) : ℝ) * 0 := by
            exact congrArg
              (fun x : ℝ => (entireFunctionZeroMultiplicity F hF (z : ℂ) : ℝ) * x)
              (entireFunction_standardJensenFormula_nonzeroAtOrigin_closedDiskBoundarySupportFiniteZeroDivisor_boundaryAverage_eq_zero
                F hF hF0 ρ z hz)
          _ = 0 := by
            exact mul_zero (entireFunctionZeroMultiplicity F hF (z : ℂ) : ℝ))

/-- The closed-disk interior support is the closed support filtered by strict
interiority. -/
theorem entireFunction_standardJensenFormula_nonzeroAtOrigin_closedDiskInteriorSupportFiniteZeroDivisor_def
    (F : ℂ → ℂ)
    (hF : ∀ z : ℂ, AnalyticAt ℂ F z)
    (hF0 : F 0 ≠ 0)
    (ρ : ℝ) :
    entireFunction_standardJensenFormula_nonzeroAtOrigin_closedDiskInteriorSupportFiniteZeroDivisor
        F hF hF0 ρ =
      (entireFunction_standardJensenFormula_nonzeroAtOrigin_closedDiskSupportFiniteZeroDivisor
        F hF hF0 ρ).filter
        (fun z : EntireFunctionZero F => ‖(z : ℂ)‖ < ρ) := by
  rfl

/-- The closed-disk boundary support is the closed support filtered by the
non-strict radial condition. -/
theorem entireFunction_standardJensenFormula_nonzeroAtOrigin_closedDiskBoundarySupportFiniteZeroDivisor_def
    (F : ℂ → ℂ)
    (hF : ∀ z : ℂ, AnalyticAt ℂ F z)
    (hF0 : F 0 ≠ 0)
    (ρ : ℝ) :
    entireFunction_standardJensenFormula_nonzeroAtOrigin_closedDiskBoundarySupportFiniteZeroDivisor
        F hF hF0 ρ =
      (entireFunction_standardJensenFormula_nonzeroAtOrigin_closedDiskSupportFiniteZeroDivisor
        F hF hF0 ρ).filter
        (fun z : EntireFunctionZero F => ¬ ‖(z : ℂ)‖ < ρ) := by
  rfl

/-- Closed-disk support splits into strict-interior and boundary parts. -/
theorem entireFunction_standardJensenFormula_nonzeroAtOrigin_closedDiskSupportFiniteZeroDivisor_eq_interior_union_boundary
    (F : ℂ → ℂ)
    (hF : ∀ z : ℂ, AnalyticAt ℂ F z)
    (hF0 : F 0 ≠ 0)
    (ρ : ℝ) :
    entireFunction_standardJensenFormula_nonzeroAtOrigin_closedDiskSupportFiniteZeroDivisor
        F hF hF0 ρ =
      entireFunction_standardJensenFormula_nonzeroAtOrigin_closedDiskInteriorSupportFiniteZeroDivisor
        F hF hF0 ρ ∪
      entireFunction_standardJensenFormula_nonzeroAtOrigin_closedDiskBoundarySupportFiniteZeroDivisor
        F hF hF0 ρ := by
  apply Finset.ext
  intro z
  constructor
  · intro hz
    by_cases hzρ : ‖(z : ℂ)‖ < ρ
    · exact Finset.mem_union.2
        (Or.inl (Finset.mem_filter.2 ⟨hz, hzρ⟩))
    · exact Finset.mem_union.2
        (Or.inr (Finset.mem_filter.2 ⟨hz, hzρ⟩))
  · intro hz
    rcases Finset.mem_union.1 hz with hz_int | hz_bd
    · exact (Finset.mem_filter.1 hz_int).1
    · exact (Finset.mem_filter.1 hz_bd).1

/-- A nonzero zero strictly inside the Jensen circle has nonzero radial-gap
summand. -/
theorem entireFunctionJensenRadialGapSummand_ne_zero_of_ne_zero_norm_lt_ownerRoot
    (F : ℂ → ℂ)
    (hF : ∀ z : ℂ, AnalyticAt ℂ F z)
    (hF0 : F 0 ≠ 0)
    (ρ : ℝ)
    (z : EntireFunctionZero F)
    (hz0 : (z : ℂ) ≠ 0)
    (hzρ : ‖(z : ℂ)‖ < ρ) :
    entireFunctionJensenRadialGapSummand F hF ρ z ≠ 0 := by
  have hvalue :
      entireFunctionJensenRadialGapSummand F hF ρ z =
        (entireFunctionZeroMultiplicity F hF (z : ℂ) : ℝ) *
          Real.log (ρ / ‖(z : ℂ)‖) :=
    entireFunction_standardJensenFormula_nonzeroAtOrigin_zeroFactor_radialContribution_identity
      F hF ρ z hz0 hzρ
  have hmult_nat_ne :
      entireFunctionZeroMultiplicity F hF (z : ℂ) ≠ 0 :=
    entireFunctionZeroMultiplicity_ne_zero_of_zero_of_nontrivial
      F hF ⟨0, hF0⟩ z.property
  have hmult_real_ne :
      (entireFunctionZeroMultiplicity F hF (z : ℂ) : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr hmult_nat_ne
  have hnorm_pos : 0 < ‖(z : ℂ)‖ :=
    norm_pos_iff.mpr hz0
  have hdiv_gt_one : 1 < ρ / ‖(z : ℂ)‖ :=
    (one_lt_div hnorm_pos).mpr hzρ
  have hlog_ne : Real.log (ρ / ‖(z : ℂ)‖) ≠ 0 :=
    (Real.log_pos hdiv_gt_one).ne'
  have hproduct_ne :
      (entireFunctionZeroMultiplicity F hF (z : ℂ) : ℝ) *
          Real.log (ρ / ‖(z : ℂ)‖) ≠ 0 :=
    mul_ne_zero hmult_real_ne hlog_ne
  intro hzero
  exact hproduct_ne (Eq.trans hvalue.symm hzero)

/-- A closed-disk interior support member is a radial-gap support member. -/
theorem entireFunction_standardJensenFormula_nonzeroAtOrigin_closedDiskInteriorSupportFiniteZeroDivisor_subset_radialGapSupportFiniteZeroDivisor_ownerRoot
    (F : ℂ → ℂ)
    (hF : ∀ z : ℂ, AnalyticAt ℂ F z)
    (hF0 : F 0 ≠ 0)
    (ρ : ℝ) :
    (entireFunction_standardJensenFormula_nonzeroAtOrigin_closedDiskInteriorSupportFiniteZeroDivisor
      F hF hF0 ρ : Set (EntireFunctionZero F)) ⊆
      (entireFunction_standardJensenFormula_nonzeroAtOrigin_radialGapSupportFiniteZeroDivisor
        F hF hF0 ρ : Set (EntireFunctionZero F)) := by
  intro z hz
  have hz_closed :
      z ∈
        entireFunction_standardJensenFormula_nonzeroAtOrigin_closedDiskSupportFiniteZeroDivisor
          F hF hF0 ρ :=
    (Finset.mem_filter.1 hz).1
  have hzρ : ‖(z : ℂ)‖ < ρ :=
    (Finset.mem_filter.1 hz).2
  have hz0 : (z : ℂ) ≠ 0 :=
    entireFunction_standardJensenFormula_nonzeroAtOrigin_closedDiskSupportFiniteZeroDivisor_mem_ne_zero
      F hF hF0 ρ z hz_closed
  have hsupport :
      z ∈ Function.support
        (fun w : EntireFunctionZero F =>
          entireFunctionJensenRadialGapSummand F hF ρ w) :=
    entireFunctionJensenRadialGapSummand_ne_zero_of_ne_zero_norm_lt_ownerRoot
      F hF hF0 ρ z hz0 hzρ
  exact
    entireFunction_standardJensenFormula_nonzeroAtOrigin_radialGapSupportFiniteZeroDivisor_contains_support
      F hF hF0 ρ hsupport

/-- A nonzero zero in the closed disk has nonzero nonzero-closed-disk
multiplicity summand. -/
theorem entireFunctionNonzeroZeroMultiplicityClosedDiskSummand_ne_zero_of_ne_zero_norm_le_ownerRoot
    (F : ℂ → ℂ)
    (hF : ∀ z : ℂ, AnalyticAt ℂ F z)
    (hF0 : F 0 ≠ 0)
    (ρ : ℝ)
    (z : EntireFunctionZero F)
    (hz0 : (z : ℂ) ≠ 0)
    (hzρ : ‖(z : ℂ)‖ ≤ ρ) :
    entireFunctionNonzeroZeroMultiplicityClosedDiskSummand F hF ρ z ≠ 0 := by
  have hvalue :
      entireFunctionNonzeroZeroMultiplicityClosedDiskSummand F hF ρ z =
        (entireFunctionZeroMultiplicity F hF (z : ℂ) : ℝ) := by
    unfold entireFunctionNonzeroZeroMultiplicityClosedDiskSummand
    unfold entireFunctionZeroMultiplicityClosedDiskSummand
    exact Eq.trans (if_neg hz0) (if_pos hzρ)
  have hmult_nat_ne :
      entireFunctionZeroMultiplicity F hF (z : ℂ) ≠ 0 :=
    entireFunctionZeroMultiplicity_ne_zero_of_zero_of_nontrivial
      F hF ⟨0, hF0⟩ z.property
  have hmult_real_ne :
      (entireFunctionZeroMultiplicity F hF (z : ℂ) : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr hmult_nat_ne
  intro hzero
  exact hmult_real_ne (Eq.trans hvalue.symm hzero)

/-- A radial-gap support member is a closed-disk interior support member. -/
theorem entireFunction_standardJensenFormula_nonzeroAtOrigin_radialGapSupportFiniteZeroDivisor_subset_closedDiskInteriorSupportFiniteZeroDivisor
    (F : ℂ → ℂ)
    (hF : ∀ z : ℂ, AnalyticAt ℂ F z)
    (hF0 : F 0 ≠ 0)
    (ρ : ℝ) :
    (entireFunction_standardJensenFormula_nonzeroAtOrigin_radialGapSupportFiniteZeroDivisor
      F hF hF0 ρ : Set (EntireFunctionZero F)) ⊆
      (entireFunction_standardJensenFormula_nonzeroAtOrigin_closedDiskInteriorSupportFiniteZeroDivisor
        F hF hF0 ρ : Set (EntireFunctionZero F)) := by
  intro z hz
  have hz0 : (z : ℂ) ≠ 0 :=
    entireFunction_standardJensenFormula_nonzeroAtOrigin_radialGapSupportFiniteZeroDivisor_mem_ne_zero
      F hF hF0 ρ z hz
  have hzρ : ‖(z : ℂ)‖ < ρ :=
    entireFunction_standardJensenFormula_nonzeroAtOrigin_radialGapSupportFiniteZeroDivisor_mem_norm_lt
      F hF hF0 ρ z hz
  have hclosed_support :
      z ∈ Function.support
        (fun w : EntireFunctionZero F =>
          entireFunctionNonzeroZeroMultiplicityClosedDiskSummand F hF ρ w) := by
    have hzle : ‖(z : ℂ)‖ ≤ ρ :=
      le_of_lt hzρ
    exact
      entireFunctionNonzeroZeroMultiplicityClosedDiskSummand_ne_zero_of_ne_zero_norm_le_ownerRoot
        F hF hF0 ρ z hz0 hzle
  have hz_closed :
      z ∈
        entireFunction_standardJensenFormula_nonzeroAtOrigin_closedDiskSupportFiniteZeroDivisor
          F hF hF0 ρ :=
    entireFunction_standardJensenFormula_nonzeroAtOrigin_closedDiskSupportFiniteZeroDivisor_contains_support
      F hF hF0 ρ hclosed_support
  exact Finset.mem_filter.2 ⟨hz_closed, hzρ⟩

/-- The strict-interior part of the closed-disk support agrees with the
radial-gap support. -/
theorem entireFunction_standardJensenFormula_nonzeroAtOrigin_closedDiskInteriorSupportFiniteZeroDivisor_eq_radialGapSupportFiniteZeroDivisor_ownerRoot
    (F : ℂ → ℂ)
    (hF : ∀ z : ℂ, AnalyticAt ℂ F z)
    (hF0 : F 0 ≠ 0)
    (ρ : ℝ) :
    entireFunction_standardJensenFormula_nonzeroAtOrigin_closedDiskInteriorSupportFiniteZeroDivisor
        F hF hF0 ρ =
      entireFunction_standardJensenFormula_nonzeroAtOrigin_radialGapSupportFiniteZeroDivisor
        F hF hF0 ρ := by
  apply Finset.ext
  intro z
  constructor
  · intro hz
    exact
      entireFunction_standardJensenFormula_nonzeroAtOrigin_closedDiskInteriorSupportFiniteZeroDivisor_subset_radialGapSupportFiniteZeroDivisor_ownerRoot
        F hF hF0 ρ hz
  · intro hz
    exact
      entireFunction_standardJensenFormula_nonzeroAtOrigin_radialGapSupportFiniteZeroDivisor_subset_closedDiskInteriorSupportFiniteZeroDivisor
        F hF hF0 ρ hz

/-- The radial-gap summand has the finite product divisor sum as its infinite
sum. -/
theorem entireFunction_standardJensenFormula_nonzeroAtOrigin_radialGapSummand_hasSum_supportFiniteProductRadialGapSum
    (F : ℂ → ℂ)
    (hF : ∀ z : ℂ, AnalyticAt ℂ F z)
    (hF0 : F 0 ≠ 0)
    (ρ : ℝ) :
    HasSum
      (fun z : EntireFunctionZero F =>
        entireFunctionJensenRadialGapSummand F hF ρ z)
      (entireFunction_standardJensenFormula_nonzeroAtOrigin_finiteProductRadialGapSum
        F hF ρ
        (entireFunction_standardJensenFormula_nonzeroAtOrigin_radialGapSupportFiniteZeroDivisor
          F hF hF0 ρ)) := by
  unfold entireFunction_standardJensenFormula_nonzeroAtOrigin_finiteProductRadialGapSum
  exact hasSum_sum_of_ne_finset_zero
    (s :=
      entireFunction_standardJensenFormula_nonzeroAtOrigin_radialGapSupportFiniteZeroDivisor
        F hF hF0 ρ)
    (f := fun z : EntireFunctionZero F =>
      entireFunctionJensenRadialGapSummand F hF ρ z)
    (fun z hz_not_mem => by
      by_contra hz_ne
      have hz_support :
          z ∈ Function.support
            (fun w : EntireFunctionZero F =>
              entireFunctionJensenRadialGapSummand F hF ρ w) :=
        hz_ne
      have hz_mem :
          z ∈
            entireFunction_standardJensenFormula_nonzeroAtOrigin_radialGapSupportFiniteZeroDivisor
              F hF hF0 ρ :=
        entireFunction_standardJensenFormula_nonzeroAtOrigin_radialGapSupportFiniteZeroDivisor_contains_support
          F hF hF0 ρ hz_support
      exact hz_not_mem hz_mem)

/-- The infinite Jensen radial-gap sum is the finite product sum over the
support divisor. -/
theorem entireFunction_standardJensenFormula_nonzeroAtOrigin_radialGapSum_eq_supportFiniteProductRadialGapSum
    (F : ℂ → ℂ)
    (hF : ∀ z : ℂ, AnalyticAt ℂ F z)
    (hF0 : F 0 ≠ 0)
    (ρ : ℝ) :
    entireFunctionJensenRadialGapSum F hF ρ =
      entireFunction_standardJensenFormula_nonzeroAtOrigin_finiteProductRadialGapSum
        F hF ρ
        (entireFunction_standardJensenFormula_nonzeroAtOrigin_radialGapSupportFiniteZeroDivisor
          F hF hF0 ρ) := by
  exact
    entireFunctionJensenRadialGapSum_eq_finiteProductRadialGapSum_of_support_subset
      F hF ρ
      (entireFunction_standardJensenFormula_nonzeroAtOrigin_radialGapSupportFiniteZeroDivisor
        F hF hF0 ρ)
      (entireFunction_standardJensenFormula_nonzeroAtOrigin_radialGapSupportFiniteZeroDivisor_contains_support
        F hF hF0 ρ)

/-- The support finite product sum expands into the explicit zero-factor
radial contributions. -/
theorem entireFunction_standardJensenFormula_nonzeroAtOrigin_supportFiniteProduct_explicit_sum_identity
    (F : ℂ → ℂ)
    (hF : ∀ z : ℂ, AnalyticAt ℂ F z)
    (hF0 : F 0 ≠ 0)
    (ρ : ℝ) :
    entireFunction_standardJensenFormula_nonzeroAtOrigin_finiteProductRadialGapSum
        F hF ρ
        (entireFunction_standardJensenFormula_nonzeroAtOrigin_radialGapSupportFiniteZeroDivisor
          F hF hF0 ρ) =
      ∑ z in
        entireFunction_standardJensenFormula_nonzeroAtOrigin_radialGapSupportFiniteZeroDivisor
          F hF hF0 ρ,
        if (z : ℂ) = 0 then
          0
        else if ‖(z : ℂ)‖ < ρ then
          (entireFunctionZeroMultiplicity F hF (z : ℂ) : ℝ) *
            Real.log (ρ / ‖(z : ℂ)‖)
        else
          0 := by
  exact
    entireFunction_standardJensenFormula_nonzeroAtOrigin_finiteProduct_explicit_sum_identity
      F hF ρ
      (entireFunction_standardJensenFormula_nonzeroAtOrigin_radialGapSupportFiniteZeroDivisor
        F hF hF0 ρ)

/-- The infinite radial-gap sum is the explicit finite zero-factor sum over its
support divisor. -/
theorem entireFunction_standardJensenFormula_nonzeroAtOrigin_radialGapSum_eq_supportFiniteProduct_explicit_sum
    (F : ℂ → ℂ)
    (hF : ∀ z : ℂ, AnalyticAt ℂ F z)
    (hF0 : F 0 ≠ 0)
    (ρ : ℝ) :
    entireFunctionJensenRadialGapSum F hF ρ =
      ∑ z in
        entireFunction_standardJensenFormula_nonzeroAtOrigin_radialGapSupportFiniteZeroDivisor
          F hF hF0 ρ,
        if (z : ℂ) = 0 then
          0
        else if ‖(z : ℂ)‖ < ρ then
          (entireFunctionZeroMultiplicity F hF (z : ℂ) : ℝ) *
            Real.log (ρ / ‖(z : ℂ)‖)
        else
          0 := by
  exact Eq.trans
    (entireFunction_standardJensenFormula_nonzeroAtOrigin_radialGapSum_eq_supportFiniteProductRadialGapSum
      F hF hF0 ρ)
    (entireFunction_standardJensenFormula_nonzeroAtOrigin_supportFiniteProduct_explicit_sum_identity
      F hF hF0 ρ)

/-- The logarithmic norm of a complex exponential is the real part of the
exponent. -/

end
end LFunctions
end Boundary
