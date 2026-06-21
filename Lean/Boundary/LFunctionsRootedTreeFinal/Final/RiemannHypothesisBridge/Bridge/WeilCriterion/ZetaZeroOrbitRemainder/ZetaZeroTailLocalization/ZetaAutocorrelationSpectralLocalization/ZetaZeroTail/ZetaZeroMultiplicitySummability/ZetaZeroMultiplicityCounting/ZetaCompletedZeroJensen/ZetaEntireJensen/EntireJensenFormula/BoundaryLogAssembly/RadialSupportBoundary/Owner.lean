import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaZeroTail.ZetaZeroMultiplicitySummability.ZetaZeroMultiplicityCounting.ZetaCompletedZeroJensen.ZetaEntireJensen.EntireJensenFormula.BoundaryLogAssembly.ClosedSupportBoundary.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaZeroTail.ZetaZeroMultiplicitySummability.ZetaZeroMultiplicityCounting.ZetaCompletedZeroJensen.ZetaEntireJensen.EntireJensenFormula.ZeroFreePrimitive.Owner

/-!
# Boundary-log assembly for Jensen formula

This owner layer was split from `BoundaryLogAssembly.Owner` without changing public declaration names.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open scoped Topology

/-- Radial-gap boundary logarithm decomposition after the closed-support
quotient has been constructed.

This is no longer the zero-free quotient construction itself.  The zero-free
quotient is owned by the closed-disk support package above; this theorem is the
downstream comparison from the closed-support boundary factor sum to the
strictly interior radial-gap support, with boundary-zero factors handled
separately. -/
theorem entireFunction_standardJensenFormula_nonzeroAtOrigin_supportFiniteProduct_boundaryLog_decomposition_ownerRoot
    (F : ℂ → ℂ)
    (hF : ∀ z : ℂ, AnalyticAt ℂ F z)
    (hF0 : F 0 ≠ 0)
    (ρ : ℝ)
    (hρ : 1 ≤ ρ) :
    entireFunctionJensenBoundaryLogAverage F ρ =
      Real.log ‖F 0‖ +
        (∑ z in
          entireFunction_standardJensenFormula_nonzeroAtOrigin_radialGapSupportFiniteZeroDivisor
            F hF hF0 ρ,
          (entireFunctionZeroMultiplicity F hF (z : ℂ) : ℝ) *
            ((2 * Real.pi)⁻¹ *
              (∫ θ in (0 : ℝ)..(2 * Real.pi),
                Real.log
                  ‖1 - (((ρ : ℂ) * Complex.exp (θ * Complex.I)) / (z : ℂ))‖))) := by
  let closedFactors : ℝ :=
    ∑ z in
      entireFunction_standardJensenFormula_nonzeroAtOrigin_closedDiskSupportFiniteZeroDivisor
        F hF hF0 ρ,
      (entireFunctionZeroMultiplicity F hF (z : ℂ) : ℝ) *
        ((2 * Real.pi)⁻¹ *
          (∫ θ in (0 : ℝ)..(2 * Real.pi),
            Real.log
              ‖1 - (((ρ : ℂ) * Complex.exp (θ * Complex.I)) / (z : ℂ))‖))
  let radialFactors : ℝ :=
    ∑ z in
      entireFunction_standardJensenFormula_nonzeroAtOrigin_radialGapSupportFiniteZeroDivisor
        F hF hF0 ρ,
      (entireFunctionZeroMultiplicity F hF (z : ℂ) : ℝ) *
        ((2 * Real.pi)⁻¹ *
          (∫ θ in (0 : ℝ)..(2 * Real.pi),
            Real.log
              ‖1 - (((ρ : ℂ) * Complex.exp (θ * Complex.I)) / (z : ℂ))‖))
  match
    entireFunction_standardJensenFormula_nonzeroAtOrigin_closedDiskSupportFiniteProduct_factorization_zeroFreeOnClosedDisk_ownerRoot
      F hF hF0 ρ hρ
  with
  | ⟨Q, _hfactor, _hzero, hboundary, horigin⟩ =>
    have hclosed_to_radial :
        closedFactors = radialFactors :=
      entireFunction_standardJensenFormula_nonzeroAtOrigin_closedDiskSupport_boundaryFactorSum_eq_radialGapSum_ownerRoot
        F hF hF0 ρ
    calc
      entireFunctionJensenBoundaryLogAverage F ρ =
          Real.log ‖Q 0‖ + closedFactors := by
        exact hboundary
      _ = Real.log ‖F 0‖ + closedFactors := by
        exact congrArg (fun x : ℝ => x + closedFactors) horigin
      _ = Real.log ‖F 0‖ + radialFactors := by
        exact congrArg (fun x : ℝ => Real.log ‖F 0‖ + x) hclosed_to_radial
      _ =
        Real.log ‖F 0‖ +
          (∑ z in
            entireFunction_standardJensenFormula_nonzeroAtOrigin_radialGapSupportFiniteZeroDivisor
              F hF hF0 ρ,
            (entireFunctionZeroMultiplicity F hF (z : ℂ) : ℝ) *
              ((2 * Real.pi)⁻¹ *
                (∫ θ in (0 : ℝ)..(2 * Real.pi),
                  Real.log
                    ‖1 - (((ρ : ℂ) * Complex.exp (θ * Complex.I)) / (z : ℂ))‖))) := by
        rfl

/-- Radial-support boundary logarithm comparison for an already zero-free
quotient.

This theorem does not construct a radial-support quotient that is zero-free on
the closed disk.  It only records the radial-factor boundary formula under the
explicit hypotheses `hfactor` and `hzero`; the owner construction of a
zero-free closed-disk quotient now lives in the closed-support package. -/
theorem entireFunction_standardJensenFormula_nonzeroAtOrigin_supportFiniteRemovableQuotient_boundaryLog_decomposition_ownerRoot
    (F Q : ℂ → ℂ)
    (hF : ∀ z : ℂ, AnalyticAt ℂ F z)
    (hF0 : F 0 ≠ 0)
    (ρ : ℝ)
    (hρ : 1 ≤ ρ)
    (_hQ_an : ∀ w : ℂ, ‖w‖ ≤ ρ → AnalyticAt ℂ Q w)
    (hfactor :
      ∀ w : ℂ,
        ‖w‖ ≤ ρ →
        F w =
          Q w *
            entireFunction_standardJensenFormula_nonzeroAtOrigin_supportFiniteZeroDivisorProduct
              F hF hF0 ρ w)
    (_hzero : ∀ w : ℂ, ‖w‖ ≤ ρ → Q w ≠ 0) :
    entireFunctionJensenBoundaryLogAverage F ρ =
      Real.log ‖Q 0‖ +
        (∑ z in
          entireFunction_standardJensenFormula_nonzeroAtOrigin_radialGapSupportFiniteZeroDivisor
            F hF hF0 ρ,
          (entireFunctionZeroMultiplicity F hF (z : ℂ) : ℝ) *
            ((2 * Real.pi)⁻¹ *
              (∫ θ in (0 : ℝ)..(2 * Real.pi),
                Real.log
                  ‖1 - (((ρ : ℂ) * Complex.exp (θ * Complex.I)) / (z : ℂ))‖))) := by
  have hboundary :
      entireFunctionJensenBoundaryLogAverage F ρ =
        Real.log ‖F 0‖ +
          (∑ z in
            entireFunction_standardJensenFormula_nonzeroAtOrigin_radialGapSupportFiniteZeroDivisor
              F hF hF0 ρ,
            (entireFunctionZeroMultiplicity F hF (z : ℂ) : ℝ) *
              ((2 * Real.pi)⁻¹ *
                (∫ θ in (0 : ℝ)..(2 * Real.pi),
                  Real.log
                    ‖1 - (((ρ : ℂ) * Complex.exp (θ * Complex.I)) / (z : ℂ))‖))) :=
    entireFunction_standardJensenFormula_nonzeroAtOrigin_supportFiniteProduct_boundaryLog_decomposition_ownerRoot
      F hF hF0 ρ hρ
  have horigin :
      Real.log ‖Q 0‖ = Real.log ‖F 0‖ :=
    entireFunction_standardJensenFormula_nonzeroAtOrigin_supportFiniteRemovableQuotient_origin_log_norm_ownerRoot
      F Q hF hF0 ρ hρ hfactor
  calc
    entireFunctionJensenBoundaryLogAverage F ρ =
        Real.log ‖F 0‖ +
          (∑ z in
            entireFunction_standardJensenFormula_nonzeroAtOrigin_radialGapSupportFiniteZeroDivisor
              F hF hF0 ρ,
            (entireFunctionZeroMultiplicity F hF (z : ℂ) : ℝ) *
              ((2 * Real.pi)⁻¹ *
                (∫ θ in (0 : ℝ)..(2 * Real.pi),
                  Real.log
                    ‖1 - (((ρ : ℂ) * Complex.exp (θ * Complex.I)) / (z : ℂ))‖))) := by
      exact hboundary
    _ =
        Real.log ‖Q 0‖ +
          (∑ z in
            entireFunction_standardJensenFormula_nonzeroAtOrigin_radialGapSupportFiniteZeroDivisor
              F hF hF0 ρ,
            (entireFunctionZeroMultiplicity F hF (z : ℂ) : ℝ) *
              ((2 * Real.pi)⁻¹ *
                (∫ θ in (0 : ℝ)..(2 * Real.pi),
                  Real.log
                    ‖1 - (((ρ : ℂ) * Complex.exp (θ * Complex.I)) / (z : ℂ))‖))) := by
      exact
        congrArg
          (fun x : ℝ =>
            x +
              (∑ z in
                entireFunction_standardJensenFormula_nonzeroAtOrigin_radialGapSupportFiniteZeroDivisor
                  F hF hF0 ρ,
                (entireFunctionZeroMultiplicity F hF (z : ℂ) : ℝ) *
                  ((2 * Real.pi)⁻¹ *
                    (∫ θ in (0 : ℝ)..(2 * Real.pi),
                      Real.log
                        ‖1 - (((ρ : ℂ) * Complex.exp (θ * Complex.I)) / (z : ℂ))‖))))
          horigin.symm

/-- Origin normalization for the finite quotient in Jensen's product
factorization. -/
theorem entireFunction_standardJensenFormula_nonzeroAtOrigin_supportFiniteZeroDivisorQuotient_origin_log_norm
    (F : ℂ → ℂ)
    (hF : ∀ z : ℂ, AnalyticAt ℂ F z)
    (hF0 : F 0 ≠ 0)
    (ρ : ℝ)
    (_hρ : 1 ≤ ρ) :
    Real.log
        ‖entireFunction_standardJensenFormula_nonzeroAtOrigin_supportFiniteZeroDivisorQuotient
            F hF hF0 ρ 0‖ =
      Real.log ‖F 0‖ := by
  exact
    entireFunction_standardJensenFormula_nonzeroAtOrigin_supportFiniteZeroDivisorQuotient_origin_log_norm_from_def
      F hF hF0 ρ

/-- The finite support divisor sum of single-factor boundary averages is the
support finite radial-gap product sum. -/
theorem entireFunction_standardJensenFormula_nonzeroAtOrigin_supportFiniteProduct_singleFactorBoundaryAverageSum_eq_radialGapSum
    (F : ℂ → ℂ)
    (hF : ∀ z : ℂ, AnalyticAt ℂ F z)
    (hF0 : F 0 ≠ 0)
    (ρ : ℝ) :
    (∑ z in
      entireFunction_standardJensenFormula_nonzeroAtOrigin_radialGapSupportFiniteZeroDivisor
        F hF hF0 ρ,
      (entireFunctionZeroMultiplicity F hF (z : ℂ) : ℝ) *
        ((2 * Real.pi)⁻¹ *
          (∫ θ in (0 : ℝ)..(2 * Real.pi),
            Real.log
              ‖1 - (((ρ : ℂ) * Complex.exp (θ * Complex.I)) / (z : ℂ))‖))) =
      entireFunction_standardJensenFormula_nonzeroAtOrigin_finiteProductRadialGapSum
        F hF ρ
        (entireFunction_standardJensenFormula_nonzeroAtOrigin_radialGapSupportFiniteZeroDivisor
          F hF hF0 ρ) := by
  exact
    (entireFunction_standardJensenFormula_nonzeroAtOrigin_supportFiniteProductRadialGapSum_eq_singleFactorBoundaryAverageSum
      F hF hF0 ρ).symm

/-- Finite-product boundary-average identity over the support divisor.

This is the quotient/product construction in the assembly chain.  Its proof is
the classical finite divisor factorization on the Jensen disk, construction of
the zero-free quotient, analytic-log mean value for the quotient term, boundary
log decomposition into the quotient and the extracted linear factors, and the
finite single-factor average theorem above.  Cf. Titchmarsh, *The Theory of
Functions*, §5. -/
theorem entireFunction_standardJensenFormula_nonzeroAtOrigin_supportFiniteProduct_boundaryAverage_identity_ownerRoot
    (F : ℂ → ℂ)
    (hF : ∀ z : ℂ, AnalyticAt ℂ F z)
    (hF0 : F 0 ≠ 0)
    (ρ : ℝ)
    (hρ : 1 ≤ ρ) :
    entireFunctionJensenBoundaryLogAverage F ρ =
      Real.log ‖F 0‖ +
        entireFunction_standardJensenFormula_nonzeroAtOrigin_finiteProductRadialGapSum
        F hF ρ
        (entireFunction_standardJensenFormula_nonzeroAtOrigin_radialGapSupportFiniteZeroDivisor
          F hF hF0 ρ) := by
  have hboundary :
      entireFunctionJensenBoundaryLogAverage F ρ =
        Real.log ‖F 0‖ +
          (∑ z in
            entireFunction_standardJensenFormula_nonzeroAtOrigin_radialGapSupportFiniteZeroDivisor
              F hF hF0 ρ,
            (entireFunctionZeroMultiplicity F hF (z : ℂ) : ℝ) *
              ((2 * Real.pi)⁻¹ *
                (∫ θ in (0 : ℝ)..(2 * Real.pi),
                  Real.log
                    ‖1 - (((ρ : ℂ) * Complex.exp (θ * Complex.I)) / (z : ℂ))‖))) :=
    entireFunction_standardJensenFormula_nonzeroAtOrigin_supportFiniteProduct_boundaryLog_decomposition_ownerRoot
      F hF hF0 ρ hρ
  have hsum :
      (∑ z in
        entireFunction_standardJensenFormula_nonzeroAtOrigin_radialGapSupportFiniteZeroDivisor
          F hF hF0 ρ,
        (entireFunctionZeroMultiplicity F hF (z : ℂ) : ℝ) *
          ((2 * Real.pi)⁻¹ *
            (∫ θ in (0 : ℝ)..(2 * Real.pi),
              Real.log
                ‖1 - (((ρ : ℂ) * Complex.exp (θ * Complex.I)) / (z : ℂ))‖))) =
        entireFunction_standardJensenFormula_nonzeroAtOrigin_finiteProductRadialGapSum
          F hF ρ
          (entireFunction_standardJensenFormula_nonzeroAtOrigin_radialGapSupportFiniteZeroDivisor
            F hF hF0 ρ) :=
    entireFunction_standardJensenFormula_nonzeroAtOrigin_supportFiniteProduct_singleFactorBoundaryAverageSum_eq_radialGapSum
      F hF hF0 ρ
  let S : ℝ :=
    ∑ z in
      entireFunction_standardJensenFormula_nonzeroAtOrigin_radialGapSupportFiniteZeroDivisor
        F hF hF0 ρ,
      (entireFunctionZeroMultiplicity F hF (z : ℂ) : ℝ) *
        ((2 * Real.pi)⁻¹ *
          (∫ θ in (0 : ℝ)..(2 * Real.pi),
            Real.log
              ‖1 - (((ρ : ℂ) * Complex.exp (θ * Complex.I)) / (z : ℂ))‖))
  have hboundaryS :
      entireFunctionJensenBoundaryLogAverage F ρ =
        Real.log ‖F 0‖ + S :=
    hboundary
  have hsumS :
      S =
        entireFunction_standardJensenFormula_nonzeroAtOrigin_finiteProductRadialGapSum
          F hF ρ
          (entireFunction_standardJensenFormula_nonzeroAtOrigin_radialGapSupportFiniteZeroDivisor
            F hF hF0 ρ) :=
    hsum
  calc
    entireFunctionJensenBoundaryLogAverage F ρ =
        Real.log ‖F 0‖ + S := by
      exact hboundaryS
    _ =
        Real.log ‖F 0‖ +
          entireFunction_standardJensenFormula_nonzeroAtOrigin_finiteProductRadialGapSum
          F hF ρ
          (entireFunction_standardJensenFormula_nonzeroAtOrigin_radialGapSupportFiniteZeroDivisor
            F hF hF0 ρ) := by
      exact congrArg (fun x : ℝ => Real.log ‖F 0‖ + x) hsum

/-- Support-controlled finite-product boundary identity implies the standard
Jensen boundary mean-log identity by replacing the finite support divisor sum
with the infinite radial-gap sum. -/
theorem entireFunction_standardJensenFormula_nonzeroAtOrigin_zeroFreeQuotient_boundaryMeanLog_identity_from_supportFiniteProduct_boundaryAverage
    (F : ℂ → ℂ)
    (hF : ∀ z : ℂ, AnalyticAt ℂ F z)
    (hF0 : F 0 ≠ 0)
    (ρ : ℝ)
    (hboundary :
      entireFunctionJensenBoundaryLogAverage F ρ =
        Real.log ‖F 0‖ +
          entireFunction_standardJensenFormula_nonzeroAtOrigin_finiteProductRadialGapSum
          F hF ρ
          (entireFunction_standardJensenFormula_nonzeroAtOrigin_radialGapSupportFiniteZeroDivisor
            F hF hF0 ρ)) :
    entireFunctionJensenRadialGapSum F hF ρ =
      entireFunctionJensenBoundaryLogAverage F ρ - Real.log ‖F 0‖ := by
  have hsupport :
      entireFunctionJensenRadialGapSum F hF ρ =
        entireFunction_standardJensenFormula_nonzeroAtOrigin_finiteProductRadialGapSum
          F hF ρ
          (entireFunction_standardJensenFormula_nonzeroAtOrigin_radialGapSupportFiniteZeroDivisor
            F hF hF0 ρ) :=
    entireFunction_standardJensenFormula_nonzeroAtOrigin_radialGapSum_eq_supportFiniteProductRadialGapSum
      F hF hF0 ρ
  calc
    entireFunctionJensenRadialGapSum F hF ρ =
        entireFunction_standardJensenFormula_nonzeroAtOrigin_finiteProductRadialGapSum
          F hF ρ
          (entireFunction_standardJensenFormula_nonzeroAtOrigin_radialGapSupportFiniteZeroDivisor
            F hF hF0 ρ) := by
      exact hsupport
    _ =
        (Real.log ‖F 0‖ +
          entireFunction_standardJensenFormula_nonzeroAtOrigin_finiteProductRadialGapSum
            F hF ρ
            (entireFunction_standardJensenFormula_nonzeroAtOrigin_radialGapSupportFiniteZeroDivisor
              F hF hF0 ρ)) -
          Real.log ‖F 0‖ := by
      exact
        (add_sub_cancel_left
          (Real.log ‖F 0‖)
          (entireFunction_standardJensenFormula_nonzeroAtOrigin_finiteProductRadialGapSum
            F hF ρ
            (entireFunction_standardJensenFormula_nonzeroAtOrigin_radialGapSupportFiniteZeroDivisor
              F hF hF0 ρ))).symm
    _ = entireFunctionJensenBoundaryLogAverage F ρ - Real.log ‖F 0‖ := by
      exact congrArg (fun x : ℝ => x - Real.log ‖F 0‖) hboundary.symm

end
end LFunctions
end Boundary
