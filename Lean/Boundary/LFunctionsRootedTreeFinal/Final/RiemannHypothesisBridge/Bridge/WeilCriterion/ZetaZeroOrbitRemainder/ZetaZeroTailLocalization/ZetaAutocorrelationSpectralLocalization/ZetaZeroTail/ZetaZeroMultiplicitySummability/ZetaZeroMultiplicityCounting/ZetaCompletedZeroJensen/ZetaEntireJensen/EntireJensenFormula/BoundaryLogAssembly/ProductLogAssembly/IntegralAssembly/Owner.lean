import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaZeroTail.ZetaZeroMultiplicitySummability.ZetaZeroMultiplicityCounting.ZetaCompletedZeroJensen.ZetaEntireJensen.EntireJensenFormula.BoundaryLogAssembly.ProductLogAssembly.Pointwise.Owner

/-!
# Boundary product-log assembly for Jensen formula

This owner layer was split from `BoundaryLogAssembly.ProductLogAssembly.Owner` without changing public declaration names.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open scoped Topology

/-- Interval-integrability of the closed-support product-log summands with
finite boundary exceptions. -/
theorem entireFunction_standardJensenFormula_nonzeroAtOrigin_closedDiskSupportFiniteProduct_boundaryLog_finiteException_intervalIntegrable_ownerRoot
    (F Q : ℂ → ℂ)
    (hF : ∀ z : ℂ, AnalyticAt ℂ F z)
    (hF0 : F 0 ≠ 0)
    (ρ : ℝ)
    (hρ : 1 ≤ ρ)
    (hfactor :
      ∀ w : ℂ,
        ‖w‖ ≤ ρ →
        F w =
          Q w *
            entireFunction_standardJensenFormula_nonzeroAtOrigin_closedDiskSupportFiniteZeroDivisorProduct
              F hF hF0 ρ w)
    (hzero : ∀ w : ℂ, ‖w‖ ≤ ρ → Q w ≠ 0) :
    IntervalIntegrable
      (fun θ : ℝ =>
        Real.log ‖Q ((ρ : ℂ) * Complex.exp (θ * Complex.I))‖ +
          (∑ z in
            entireFunction_standardJensenFormula_nonzeroAtOrigin_closedDiskSupportFiniteZeroDivisor
              F hF hF0 ρ,
            (entireFunctionZeroMultiplicity F hF (z : ℂ) : ℝ) *
              Real.log
                ‖1 - (((ρ : ℂ) * Complex.exp (θ * Complex.I)) / (z : ℂ))‖))
      MeasureTheory.volume
      0
      (2 * Real.pi) := by
  have hρ_pos : 0 < ρ :=
    lt_of_lt_of_le zero_lt_one hρ
  have hF_nontrivial : ∃ z : ℂ, F z ≠ 0 :=
    ⟨0, hF0⟩
  have hzeros : Set.Finite {z : ℂ | ‖z‖ = ρ ∧ F z = 0} :=
    entireFunction_circleZeros_finite F hF hF_nontrivial ρ
  have hF_int :
      IntervalIntegrable
        (entireFunctionJensenBoundaryLogIntegrand F ρ)
        MeasureTheory.volume
        0
        (2 * Real.pi) :=
    entireFunction_boundaryLogIntegrand_intervalIntegrable_of_finiteCircleZeros
      F hF hF_nontrivial hρ_pos hzeros
  have hae :
      entireFunctionJensenBoundaryLogIntegrand F ρ =ᵐ[
          MeasureTheory.volume.restrict (Ι (0 : ℝ) (2 * Real.pi))]
        (fun θ : ℝ =>
          Real.log ‖Q ((ρ : ℂ) * Complex.exp (θ * Complex.I))‖ +
            (∑ z in
              entireFunction_standardJensenFormula_nonzeroAtOrigin_closedDiskSupportFiniteZeroDivisor
                F hF hF0 ρ,
              (entireFunctionZeroMultiplicity F hF (z : ℂ) : ℝ) *
                Real.log
                  ‖1 - (((ρ : ℂ) * Complex.exp (θ * Complex.I)) / (z : ℂ))‖)) :=
    entireFunction_standardJensenFormula_nonzeroAtOrigin_closedDiskSupportFiniteProduct_boundaryLog_aeEq_from_pointwise_offException_ownerRoot
      F Q hF hF0 ρ hρ hfactor hzero
  exact hF_int.congr hae

/-- Interval-integrability of a single normalized boundary factor.

This is the analytic single-factor sink consumed by the finite product-log
exchange.  It is the finite-log-singularity theorem applied to the entire
function `w ↦ 1 - w / a`; its circle zeros are finite, and the displayed
integrand is definitionally the Jensen boundary logarithmic integrand for that
factor. -/
theorem entireFunction_normalizedSingleFactor_boundaryLog_intervalIntegrable_ownerRoot
    {a : ℂ}
    {ρ : ℝ}
    (ha0 : a ≠ 0)
    (hρ : 0 < ρ) :
    IntervalIntegrable
      (fun θ : ℝ =>
        Real.log
          ‖1 - (((ρ : ℂ) * Complex.exp (θ * Complex.I)) / a)‖)
      MeasureTheory.volume
      0
      (2 * Real.pi) := by
  let G : ℂ → ℂ := fun w => 1 - w / a
  have hG : ∀ w : ℂ, AnalyticAt ℂ G w := by
    intro w
    exact analyticAt_const.sub (analyticAt_id.mul analyticAt_const)
  have hnontrivial : ∃ w : ℂ, G w ≠ 0 := by
    have hG0_eq_one : G 0 = 1 := by
      calc
        G 0 = 1 - 0 / a := rfl
        _ = 1 - 0 := congrArg (fun x : ℂ => 1 - x) (zero_div a)
        _ = 1 := sub_zero 1
    exact
      ⟨0,
        fun hG0 =>
          one_ne_zero (Eq.trans hG0_eq_one.symm hG0)⟩
  have hzeros : Set.Finite {w : ℂ | ‖w‖ = ρ ∧ G w = 0} :=
    entireFunction_finite_circle_zeros G hG hnontrivial ρ
  have hInt :
      IntervalIntegrable
        (entireFunctionJensenBoundaryLogIntegrand G ρ)
        MeasureTheory.volume
        (0 : ℝ)
        (2 * Real.pi) :=
    entireFunction_boundaryLogIntegrand_intervalIntegrable_of_finiteCircleZeros
      G hG hnontrivial hρ hzeros
  exact hInt

/-- Interval-integrability of one closed-support boundary logarithmic factor.

This is the single-factor input for exchanging the finite closed-support sum
with the interval integral.  Interior factors are continuous; boundary factors
have one logarithmic singularity on the fundamental interval and are handled by
the finite logarithmic-singularity API. -/
theorem entireFunction_standardJensenFormula_nonzeroAtOrigin_closedDiskSupportFiniteProduct_boundaryLog_singleFactor_intervalIntegrable_ownerRoot
    (F : ℂ → ℂ)
    (hF : ∀ z : ℂ, AnalyticAt ℂ F z)
    (hF0 : F 0 ≠ 0)
    (ρ : ℝ)
    (z : EntireFunctionZero F)
    (hz :
      z ∈
        entireFunction_standardJensenFormula_nonzeroAtOrigin_closedDiskSupportFiniteZeroDivisor
          F hF hF0 ρ) :
    IntervalIntegrable
      (fun θ : ℝ =>
        (entireFunctionZeroMultiplicity F hF (z : ℂ) : ℝ) *
          Real.log
            ‖1 - (((ρ : ℂ) * Complex.exp (θ * Complex.I)) / (z : ℂ))‖)
      MeasureTheory.volume
      0
      (2 * Real.pi) := by
  have hz0 : (z : ℂ) ≠ 0 :=
    entireFunction_standardJensenFormula_nonzeroAtOrigin_closedDiskSupportFiniteZeroDivisor_mem_ne_zero
      F hF hF0 ρ z hz
  have hz_norm_le : ‖(z : ℂ)‖ ≤ ρ :=
    entireFunction_standardJensenFormula_nonzeroAtOrigin_closedDiskSupportFiniteZeroDivisor_mem_norm_le
      F hF hF0 ρ z hz
  have hρ_pos : 0 < ρ :=
    lt_of_lt_of_le (norm_pos_iff.mpr hz0) hz_norm_le
  have hfactor_int :
      IntervalIntegrable
        (fun θ : ℝ =>
          Real.log
            ‖1 - (((ρ : ℂ) * Complex.exp (θ * Complex.I)) / (z : ℂ))‖)
        MeasureTheory.volume
        0
        (2 * Real.pi) :=
    entireFunction_normalizedSingleFactor_boundaryLog_intervalIntegrable_ownerRoot
      hz0 hρ_pos
  exact hfactor_int.const_mul
    (entireFunctionZeroMultiplicity F hF (z : ℂ) : ℝ)

/-- Finite sum/integral exchange for the closed-support boundary factor sum. -/
theorem entireFunction_standardJensenFormula_nonzeroAtOrigin_closedDiskSupportFiniteProduct_boundaryLog_sum_integral_exchange_ownerRoot
    (F : ℂ → ℂ)
    (hF : ∀ z : ℂ, AnalyticAt ℂ F z)
    (hF0 : F 0 ≠ 0)
    (ρ : ℝ) :
    (∫ θ in (0 : ℝ)..(2 * Real.pi),
      (∑ z in
        entireFunction_standardJensenFormula_nonzeroAtOrigin_closedDiskSupportFiniteZeroDivisor
          F hF hF0 ρ,
        (entireFunctionZeroMultiplicity F hF (z : ℂ) : ℝ) *
          Real.log
            ‖1 - (((ρ : ℂ) * Complex.exp (θ * Complex.I)) / (z : ℂ))‖)) =
      ∑ z in
        entireFunction_standardJensenFormula_nonzeroAtOrigin_closedDiskSupportFiniteZeroDivisor
          F hF hF0 ρ,
        (entireFunctionZeroMultiplicity F hF (z : ℂ) : ℝ) *
          (∫ θ in (0 : ℝ)..(2 * Real.pi),
            Real.log
              ‖1 - (((ρ : ℂ) * Complex.exp (θ * Complex.I)) / (z : ℂ))‖) := by
  calc
    (∫ θ in (0 : ℝ)..(2 * Real.pi),
      (∑ z in
        entireFunction_standardJensenFormula_nonzeroAtOrigin_closedDiskSupportFiniteZeroDivisor
          F hF hF0 ρ,
        (entireFunctionZeroMultiplicity F hF (z : ℂ) : ℝ) *
          Real.log
            ‖1 - (((ρ : ℂ) * Complex.exp (θ * Complex.I)) / (z : ℂ))‖)) =
        ∑ z in
          entireFunction_standardJensenFormula_nonzeroAtOrigin_closedDiskSupportFiniteZeroDivisor
            F hF hF0 ρ,
          ∫ θ in (0 : ℝ)..(2 * Real.pi),
            (entireFunctionZeroMultiplicity F hF (z : ℂ) : ℝ) *
              Real.log
                ‖1 - (((ρ : ℂ) * Complex.exp (θ * Complex.I)) / (z : ℂ))‖ := by
      exact
        intervalIntegral.integral_finset_sum
          (fun z hz =>
            entireFunction_standardJensenFormula_nonzeroAtOrigin_closedDiskSupportFiniteProduct_boundaryLog_singleFactor_intervalIntegrable_ownerRoot
              F hF hF0 ρ z hz)
    _ =
      ∑ z in
        entireFunction_standardJensenFormula_nonzeroAtOrigin_closedDiskSupportFiniteZeroDivisor
          F hF hF0 ρ,
        (entireFunctionZeroMultiplicity F hF (z : ℂ) : ℝ) *
          (∫ θ in (0 : ℝ)..(2 * Real.pi),
            Real.log
              ‖1 - (((ρ : ℂ) * Complex.exp (θ * Complex.I)) / (z : ℂ))‖) := by
      exact
        Finset.sum_congr rfl
          (fun z _hz =>
            intervalIntegral.integral_const_mul
              (entireFunctionZeroMultiplicity F hF (z : ℂ) : ℝ)
              (fun θ : ℝ =>
                Real.log
                  ‖1 - (((ρ : ℂ) * Complex.exp (θ * Complex.I)) / (z : ℂ))‖))

/-- Finite interval-integrability gluing for a closed-support boundary factor
sum.

This is purely measure-theoretic: a finite sum of interval-integrable
single-factor logarithmic terms is interval-integrable on the same interval. -/
def entireFunction_standardJensenFormula_nonzeroAtOrigin_closedDiskSupportFiniteProduct_boundaryLog_factorSum
    (F : ℂ → ℂ)
    (hF : ∀ z : ℂ, AnalyticAt ℂ F z)
    (hF0 : F 0 ≠ 0)
    (ρ : ℝ) :
    ℝ → ℝ :=
  fun θ : ℝ =>
    ∑ z in
      entireFunction_standardJensenFormula_nonzeroAtOrigin_closedDiskSupportFiniteZeroDivisor
        F hF hF0 ρ,
      (entireFunctionZeroMultiplicity F hF (z : ℂ) : ℝ) *
        Real.log
          ‖1 - (((ρ : ℂ) * Complex.exp (θ * Complex.I)) / (z : ℂ))‖

theorem intervalIntegrable_finiteRealSum_from_singleFactors
    {α : Type}
    [DecidableEq α]
    (S : Finset α)
    (φ : α → ℝ → ℝ)
    (a b : ℝ)
    (hφ :
      ∀ z : α,
        z ∈ S →
          IntervalIntegrable (φ z) MeasureTheory.volume a b) :
    IntervalIntegrable
      (fun θ : ℝ => ∑ z in S, φ z θ)
      MeasureTheory.volume
      a
      b := by
  exact
    (Finset.induction_on
      (p := fun T : Finset α =>
        (∀ z : α,
          z ∈ T →
            IntervalIntegrable (φ z) MeasureTheory.volume a b) →
          IntervalIntegrable
            (fun θ : ℝ => ∑ z in T, φ z θ)
            MeasureTheory.volume
            a
            b)
      S
      (fun _hφ_empty => by
        show
          IntervalIntegrable (fun _θ : ℝ => (0 : ℝ)) MeasureTheory.volume a b
        exact intervalIntegrable_const)
      (fun x s hx ih hφ_insert =>
        have hx_int :
            IntervalIntegrable (φ x) MeasureTheory.volume a b :=
          hφ_insert x (Finset.mem_insert_self x s)
        have hs_int :
            IntervalIntegrable
              (fun θ : ℝ => ∑ z in s, φ z θ)
              MeasureTheory.volume
              a
              b :=
          ih
            (fun z hz =>
              hφ_insert z (Finset.mem_insert_of_mem hz))
        have hsum_eq :
            (fun θ : ℝ => ∑ z in insert x s, φ z θ) =
              (fun θ : ℝ => φ x θ + ∑ z in s, φ z θ) :=
          funext
            (fun θ => Finset.sum_insert hx)
        Eq.subst
          (motive := fun ψ : ℝ → ℝ =>
            IntervalIntegrable ψ MeasureTheory.volume a b)
          hsum_eq.symm
          (hx_int.add hs_int))
      hφ)

/-- Quotient boundary logarithm integrability from the product-log a.e. split.

The a.e. identity writes the boundary logarithm of `F` as the quotient
logarithm plus the finite factor-sum logarithm.  Since the left side and the
finite factor sum are interval-integrable, the quotient term is
interval-integrable. -/
theorem entireFunction_standardJensenFormula_nonzeroAtOrigin_closedDiskSupportFiniteProduct_boundaryLog_quotientTerm_intervalIntegrable_from_productSplit
    (F Q : ℂ → ℂ)
    (hF : ∀ z : ℂ, AnalyticAt ℂ F z)
    (hF0 : F 0 ≠ 0)
    (ρ : ℝ)
    (hρ : 1 ≤ ρ)
    (hfactor :
      ∀ w : ℂ,
        ‖w‖ ≤ ρ →
        F w =
          Q w *
            entireFunction_standardJensenFormula_nonzeroAtOrigin_closedDiskSupportFiniteZeroDivisorProduct
              F hF hF0 ρ w)
    (hzero : ∀ w : ℂ, ‖w‖ ≤ ρ → Q w ≠ 0) :
    IntervalIntegrable
      (fun θ : ℝ =>
        Real.log ‖Q ((ρ : ℂ) * Complex.exp (θ * Complex.I))‖)
      MeasureTheory.volume
      0
      (2 * Real.pi) := by
  let q : ℝ → ℝ :=
    fun θ : ℝ =>
      Real.log ‖Q ((ρ : ℂ) * Complex.exp (θ * Complex.I))‖
  let fs : ℝ → ℝ :=
    entireFunction_standardJensenFormula_nonzeroAtOrigin_closedDiskSupportFiniteProduct_boundaryLog_factorSum
      F hF hF0 ρ
  have hcombined :
      IntervalIntegrable
        (fun θ : ℝ => q θ + fs θ)
        MeasureTheory.volume
        0
        (2 * Real.pi) :=
    entireFunction_standardJensenFormula_nonzeroAtOrigin_closedDiskSupportFiniteProduct_boundaryLog_finiteException_intervalIntegrable_ownerRoot
      F Q hF hF0 ρ hρ hfactor hzero
  have hfs :
      IntervalIntegrable fs MeasureTheory.volume 0 (2 * Real.pi) :=
    let S : Finset (EntireFunctionZero F) :=
      entireFunction_standardJensenFormula_nonzeroAtOrigin_closedDiskSupportFiniteZeroDivisor
        F hF hF0 ρ
    let φ : EntireFunctionZero F → ℝ → ℝ :=
      fun z θ =>
        (entireFunctionZeroMultiplicity F hF (z : ℂ) : ℝ) *
          Real.log ‖1 - (((ρ : ℂ) * Complex.exp (θ * Complex.I)) / (z : ℂ))‖
    let hφ :
        ∀ z : EntireFunctionZero F,
          z ∈ S →
            IntervalIntegrable (φ z) MeasureTheory.volume 0 (2 * Real.pi) :=
      fun z hz =>
        entireFunction_standardJensenFormula_nonzeroAtOrigin_closedDiskSupportFiniteProduct_boundaryLog_singleFactor_intervalIntegrable_ownerRoot
          F hF hF0 ρ z hz
    intervalIntegrable_finiteRealSum_from_singleFactors S φ 0 (2 * Real.pi) hφ
  have hdiff :
      IntervalIntegrable
        (fun θ : ℝ => (q θ + fs θ) - fs θ)
        MeasureTheory.volume
        0
        (2 * Real.pi) :=
    hcombined.sub hfs
  have hpoint :
      (fun θ : ℝ => (q θ + fs θ) - fs θ) =ᵐ[
          MeasureTheory.volume.restrict (Ι (0 : ℝ) (2 * Real.pi))]
        q :=
    Filter.Eventually.of_forall
      (fun θ : ℝ => add_sub_cancel_right (q θ) (fs θ))
  exact hdiff.congr hpoint

/-- Interval-integrability of the quotient boundary logarithm after the
closed-support product-log split.

The quotient term is obtained from the interval-integrable combined product-log
integrand by subtracting the finite factor-sum term. -/
theorem entireFunction_standardJensenFormula_nonzeroAtOrigin_closedDiskSupportFiniteProduct_boundaryLog_quotientTerm_intervalIntegrable_ownerRoot
    (F Q : ℂ → ℂ)
    (hF : ∀ z : ℂ, AnalyticAt ℂ F z)
    (hF0 : F 0 ≠ 0)
    (ρ : ℝ)
    (hρ : 1 ≤ ρ)
    (hfactor :
      ∀ w : ℂ,
        ‖w‖ ≤ ρ →
        F w =
          Q w *
            entireFunction_standardJensenFormula_nonzeroAtOrigin_closedDiskSupportFiniteZeroDivisorProduct
              F hF hF0 ρ w)
    (hzero : ∀ w : ℂ, ‖w‖ ≤ ρ → Q w ≠ 0) :
    IntervalIntegrable
      (fun θ : ℝ =>
        Real.log ‖Q ((ρ : ℂ) * Complex.exp (θ * Complex.I))‖)
      MeasureTheory.volume
      0
      (2 * Real.pi) := by
  exact
    entireFunction_standardJensenFormula_nonzeroAtOrigin_closedDiskSupportFiniteProduct_boundaryLog_quotientTerm_intervalIntegrable_from_productSplit
      F Q hF hF0 ρ hρ hfactor hzero

/-- Integral assembly for the closed-support product-log decomposition.

This is the final measure-theoretic step: restricted-a.e. equality replaces the
boundary log of `F` by the quotient term plus the finite factor sum, the
integral of the sum is split, and the finite factor sum is exchanged with the
interval integral. -/
theorem entireFunction_standardJensenFormula_nonzeroAtOrigin_closedDiskSupportFiniteProduct_boundaryLog_integralAssembly_from_aeEq_and_exchange
    (F Q : ℂ → ℂ)
    (hF : ∀ z : ℂ, AnalyticAt ℂ F z)
    (hF0 : F 0 ≠ 0)
    (ρ : ℝ)
    (hρ : 1 ≤ ρ)
    (hfactor :
      ∀ w : ℂ,
        ‖w‖ ≤ ρ →
        F w =
          Q w *
            entireFunction_standardJensenFormula_nonzeroAtOrigin_closedDiskSupportFiniteZeroDivisorProduct
              F hF hF0 ρ w)
    (hzero : ∀ w : ℂ, ‖w‖ ≤ ρ → Q w ≠ 0) :
    entireFunctionJensenBoundaryLogAverage F ρ =
      (2 * Real.pi)⁻¹ *
        (∫ θ in (0 : ℝ)..(2 * Real.pi),
          Real.log ‖Q ((ρ : ℂ) * Complex.exp (θ * Complex.I))‖) +
        (∑ z in
          entireFunction_standardJensenFormula_nonzeroAtOrigin_closedDiskSupportFiniteZeroDivisor
            F hF hF0 ρ,
          (entireFunctionZeroMultiplicity F hF (z : ℂ) : ℝ) *
            ((2 * Real.pi)⁻¹ *
              (∫ θ in (0 : ℝ)..(2 * Real.pi),
                Real.log
                  ‖1 - (((ρ : ℂ) * Complex.exp (θ * Complex.I)) / (z : ℂ))‖))) := by
  let q : ℝ → ℝ :=
    fun θ : ℝ =>
      Real.log ‖Q ((ρ : ℂ) * Complex.exp (θ * Complex.I))‖
  let fs : ℝ → ℝ :=
    entireFunction_standardJensenFormula_nonzeroAtOrigin_closedDiskSupportFiniteProduct_boundaryLog_factorSum
      F hF hF0 ρ
  let c : ℝ := (2 * Real.pi)⁻¹
  have hae :
      entireFunctionJensenBoundaryLogIntegrand F ρ =ᵐ[
          MeasureTheory.volume.restrict (Ι (0 : ℝ) (2 * Real.pi))]
        (fun θ : ℝ => q θ + fs θ) :=
    entireFunction_standardJensenFormula_nonzeroAtOrigin_closedDiskSupportFiniteProduct_boundaryLog_aeEq_from_pointwise_offException_ownerRoot
      F Q hF hF0 ρ hρ hfactor hzero
  have hq_int :
      IntervalIntegrable q MeasureTheory.volume 0 (2 * Real.pi) :=
    entireFunction_standardJensenFormula_nonzeroAtOrigin_closedDiskSupportFiniteProduct_boundaryLog_quotientTerm_intervalIntegrable_ownerRoot
      F Q hF hF0 ρ hρ hfactor hzero
  have hfs_int :
      IntervalIntegrable fs MeasureTheory.volume 0 (2 * Real.pi) :=
    let S : Finset (EntireFunctionZero F) :=
      entireFunction_standardJensenFormula_nonzeroAtOrigin_closedDiskSupportFiniteZeroDivisor
        F hF hF0 ρ
    let φ : EntireFunctionZero F → ℝ → ℝ :=
      fun z θ =>
        (entireFunctionZeroMultiplicity F hF (z : ℂ) : ℝ) *
          Real.log ‖1 - (((ρ : ℂ) * Complex.exp (θ * Complex.I)) / (z : ℂ))‖
    let hφ :
        ∀ z : EntireFunctionZero F,
          z ∈ S →
            IntervalIntegrable (φ z) MeasureTheory.volume 0 (2 * Real.pi) :=
      fun z hz =>
        entireFunction_standardJensenFormula_nonzeroAtOrigin_closedDiskSupportFiniteProduct_boundaryLog_singleFactor_intervalIntegrable_ownerRoot
          F hF hF0 ρ z hz
    intervalIntegrable_finiteRealSum_from_singleFactors S φ 0 (2 * Real.pi) hφ
  have hcongr :
      (∫ θ in (0 : ℝ)..(2 * Real.pi),
        entireFunctionJensenBoundaryLogIntegrand F ρ θ) =
        ∫ θ in (0 : ℝ)..(2 * Real.pi), q θ + fs θ := by
    exact
      intervalIntegral.integral_congr_ae
        ((MeasureTheory.ae_restrict_iff' measurableSet_uIoc).1 hae)
  have hadd :
      (∫ θ in (0 : ℝ)..(2 * Real.pi), q θ + fs θ) =
        (∫ θ in (0 : ℝ)..(2 * Real.pi), q θ) +
          (∫ θ in (0 : ℝ)..(2 * Real.pi), fs θ) := by
    exact intervalIntegral.integral_add hq_int hfs_int
  have hexchange :
      (∫ θ in (0 : ℝ)..(2 * Real.pi), fs θ) =
        ∑ z in
          entireFunction_standardJensenFormula_nonzeroAtOrigin_closedDiskSupportFiniteZeroDivisor
            F hF hF0 ρ,
          (entireFunctionZeroMultiplicity F hF (z : ℂ) : ℝ) *
            (∫ θ in (0 : ℝ)..(2 * Real.pi),
              Real.log
                ‖1 - (((ρ : ℂ) * Complex.exp (θ * Complex.I)) / (z : ℂ))‖) :=
    entireFunction_standardJensenFormula_nonzeroAtOrigin_closedDiskSupportFiniteProduct_boundaryLog_sum_integral_exchange_ownerRoot
      F hF hF0 ρ
  have hscale :
      c *
        (∑ z in
          entireFunction_standardJensenFormula_nonzeroAtOrigin_closedDiskSupportFiniteZeroDivisor
            F hF hF0 ρ,
          (entireFunctionZeroMultiplicity F hF (z : ℂ) : ℝ) *
            (∫ θ in (0 : ℝ)..(2 * Real.pi),
              Real.log
                ‖1 - (((ρ : ℂ) * Complex.exp (θ * Complex.I)) / (z : ℂ))‖)) =
        ∑ z in
          entireFunction_standardJensenFormula_nonzeroAtOrigin_closedDiskSupportFiniteZeroDivisor
            F hF hF0 ρ,
          (entireFunctionZeroMultiplicity F hF (z : ℂ) : ℝ) *
            (c *
              (∫ θ in (0 : ℝ)..(2 * Real.pi),
                Real.log
                  ‖1 - (((ρ : ℂ) * Complex.exp (θ * Complex.I)) / (z : ℂ))‖)) :=
    finiteReal_sum_scalar_mul_weighted_integrals
      (entireFunction_standardJensenFormula_nonzeroAtOrigin_closedDiskSupportFiniteZeroDivisor
        F hF hF0 ρ)
      c
      (fun z : EntireFunctionZero F =>
        (entireFunctionZeroMultiplicity F hF (z : ℂ) : ℝ))
      (fun z : EntireFunctionZero F =>
        ∫ θ in (0 : ℝ)..(2 * Real.pi),
          Real.log
            ‖1 - (((ρ : ℂ) * Complex.exp (θ * Complex.I)) / (z : ℂ))‖)
  calc
    entireFunctionJensenBoundaryLogAverage F ρ =
        c *
          (∫ θ in (0 : ℝ)..(2 * Real.pi),
            entireFunctionJensenBoundaryLogIntegrand F ρ θ) := by
      rfl
    _ = c * (∫ θ in (0 : ℝ)..(2 * Real.pi), q θ + fs θ) := by
      exact congrArg (fun x : ℝ => c * x) hcongr
    _ =
        c *
          ((∫ θ in (0 : ℝ)..(2 * Real.pi), q θ) +
            (∫ θ in (0 : ℝ)..(2 * Real.pi), fs θ)) := by
      exact congrArg (fun x : ℝ => c * x) hadd
    _ =
        c * (∫ θ in (0 : ℝ)..(2 * Real.pi), q θ) +
          c * (∫ θ in (0 : ℝ)..(2 * Real.pi), fs θ) := by
      exact mul_add c
        (∫ θ in (0 : ℝ)..(2 * Real.pi), q θ)
        (∫ θ in (0 : ℝ)..(2 * Real.pi), fs θ)
    _ =
        c * (∫ θ in (0 : ℝ)..(2 * Real.pi), q θ) +
          c *
            (∑ z in
              entireFunction_standardJensenFormula_nonzeroAtOrigin_closedDiskSupportFiniteZeroDivisor
                F hF hF0 ρ,
              (entireFunctionZeroMultiplicity F hF (z : ℂ) : ℝ) *
                (∫ θ in (0 : ℝ)..(2 * Real.pi),
                  Real.log
                    ‖1 - (((ρ : ℂ) * Complex.exp (θ * Complex.I)) / (z : ℂ))‖)) := by
      exact congrArg
        (fun x : ℝ => c * (∫ θ in (0 : ℝ)..(2 * Real.pi), q θ) + c * x)
        hexchange
    _ =
        c * (∫ θ in (0 : ℝ)..(2 * Real.pi), q θ) +
          (∑ z in
            entireFunction_standardJensenFormula_nonzeroAtOrigin_closedDiskSupportFiniteZeroDivisor
              F hF hF0 ρ,
            (entireFunctionZeroMultiplicity F hF (z : ℂ) : ℝ) *
              (c *
                (∫ θ in (0 : ℝ)..(2 * Real.pi),
                  Real.log
                    ‖1 - (((ρ : ℂ) * Complex.exp (θ * Complex.I)) / (z : ℂ))‖))) := by
      exact congrArg
        (fun x : ℝ => c * (∫ θ in (0 : ℝ)..(2 * Real.pi), q θ) + x)
        hscale
    _ =
      (2 * Real.pi)⁻¹ *
        (∫ θ in (0 : ℝ)..(2 * Real.pi),
          Real.log ‖Q ((ρ : ℂ) * Complex.exp (θ * Complex.I))‖) +
        (∑ z in
          entireFunction_standardJensenFormula_nonzeroAtOrigin_closedDiskSupportFiniteZeroDivisor
            F hF hF0 ρ,
          (entireFunctionZeroMultiplicity F hF (z : ℂ) : ℝ) *
            ((2 * Real.pi)⁻¹ *
              (∫ θ in (0 : ℝ)..(2 * Real.pi),
                Real.log
                  ‖1 - (((ρ : ℂ) * Complex.exp (θ * Complex.I)) / (z : ℂ))‖))) := by
      rfl

/-- Assembly of the closed-support finite-exception product-log integral from
the a.e. pointwise split and the finite sum/integral exchange. -/
theorem entireFunction_standardJensenFormula_nonzeroAtOrigin_closedDiskSupportFiniteProduct_boundaryLog_productSplit_integralAssembly_ownerRoot
    (F Q : ℂ → ℂ)
    (hF : ∀ z : ℂ, AnalyticAt ℂ F z)
    (hF0 : F 0 ≠ 0)
    (ρ : ℝ)
    (hρ : 1 ≤ ρ)
    (hfactor :
      ∀ w : ℂ,
        ‖w‖ ≤ ρ →
        F w =
          Q w *
            entireFunction_standardJensenFormula_nonzeroAtOrigin_closedDiskSupportFiniteZeroDivisorProduct
              F hF hF0 ρ w)
    (hzero : ∀ w : ℂ, ‖w‖ ≤ ρ → Q w ≠ 0) :
    entireFunctionJensenBoundaryLogAverage F ρ =
      (2 * Real.pi)⁻¹ *
        (∫ θ in (0 : ℝ)..(2 * Real.pi),
          Real.log ‖Q ((ρ : ℂ) * Complex.exp (θ * Complex.I))‖) +
        (∑ z in
          entireFunction_standardJensenFormula_nonzeroAtOrigin_closedDiskSupportFiniteZeroDivisor
            F hF hF0 ρ,
          (entireFunctionZeroMultiplicity F hF (z : ℂ) : ℝ) *
            ((2 * Real.pi)⁻¹ *
              (∫ θ in (0 : ℝ)..(2 * Real.pi),
                Real.log
                  ‖1 - (((ρ : ℂ) * Complex.exp (θ * Complex.I)) / (z : ℂ))‖))) := by
  exact
    entireFunction_standardJensenFormula_nonzeroAtOrigin_closedDiskSupportFiniteProduct_boundaryLog_integralAssembly_from_aeEq_and_exchange
      F Q hF hF0 ρ hρ hfactor hzero

/-- Finite-exception product-log splitting for a closed-support divisor.

This is the analytic integration sink behind the closed-support boundary-log
decomposition.  The proof is pointwise product-log splitting away from the
finite set of boundary parameters where extracted boundary factors vanish,
followed by finite logarithmic-singularity interval-integrability and a.e.
congruence of interval integrals. -/
theorem entireFunction_standardJensenFormula_nonzeroAtOrigin_closedDiskSupportFiniteProduct_boundaryLog_productSplit_finiteException_ownerRoot
    (F Q : ℂ → ℂ)
    (hF : ∀ z : ℂ, AnalyticAt ℂ F z)
    (hF0 : F 0 ≠ 0)
    (ρ : ℝ)
    (hρ : 1 ≤ ρ)
    (hfactor :
      ∀ w : ℂ,
        ‖w‖ ≤ ρ →
        F w =
          Q w *
            entireFunction_standardJensenFormula_nonzeroAtOrigin_closedDiskSupportFiniteZeroDivisorProduct
              F hF hF0 ρ w)
    (hzero : ∀ w : ℂ, ‖w‖ ≤ ρ → Q w ≠ 0) :
    entireFunctionJensenBoundaryLogAverage F ρ =
      (2 * Real.pi)⁻¹ *
        (∫ θ in (0 : ℝ)..(2 * Real.pi),
          Real.log ‖Q ((ρ : ℂ) * Complex.exp (θ * Complex.I))‖) +
        (∑ z in
          entireFunction_standardJensenFormula_nonzeroAtOrigin_closedDiskSupportFiniteZeroDivisor
            F hF hF0 ρ,
          (entireFunctionZeroMultiplicity F hF (z : ℂ) : ℝ) *
            ((2 * Real.pi)⁻¹ *
              (∫ θ in (0 : ℝ)..(2 * Real.pi),
                Real.log
                  ‖1 - (((ρ : ℂ) * Complex.exp (θ * Complex.I)) / (z : ℂ))‖))) := by
  exact
    entireFunction_standardJensenFormula_nonzeroAtOrigin_closedDiskSupportFiniteProduct_boundaryLog_productSplit_integralAssembly_ownerRoot
      F Q hF hF0 ρ hρ hfactor hzero


end
end LFunctions
end Boundary
