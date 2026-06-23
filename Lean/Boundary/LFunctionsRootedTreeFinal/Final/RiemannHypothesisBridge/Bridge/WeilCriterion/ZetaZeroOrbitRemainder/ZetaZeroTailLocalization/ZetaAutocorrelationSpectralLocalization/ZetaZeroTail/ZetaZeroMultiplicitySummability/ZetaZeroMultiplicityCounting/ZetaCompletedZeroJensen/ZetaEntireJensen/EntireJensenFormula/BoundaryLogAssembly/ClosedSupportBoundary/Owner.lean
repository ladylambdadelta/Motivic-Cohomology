import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaZeroTail.ZetaZeroMultiplicitySummability.ZetaZeroMultiplicityCounting.ZetaCompletedZeroJensen.ZetaEntireJensen.EntireJensenFormula.BoundaryLogAssembly.ProductLogAssembly.Owner

/-!
# Boundary-log assembly for Jensen formula

This owner layer was split from `BoundaryLogAssembly.Owner` without changing public declaration names.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open scoped Topology

/-- Closed-support finite-product boundary-log decomposition with finite
boundary exceptions made explicit.

This is the exact product-log sink: restrict the factorization
`F = Q * P_closed` to the boundary circle, split `log ‖Q * P_closed‖` into the
quotient boundary term and the finite sum of extracted single-zero factor
terms, and interchange the finite sum with the interval integral.  Boundary
zeros are allowed: the finitely many singular parameters are handled by
finite-exception interval-integrability and a.e. congruence. -/
theorem entireFunction_standardJensenFormula_nonzeroAtOrigin_closedDiskSupportFiniteProduct_boundaryLog_decomposition_finiteException_ownerRoot
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
    entireFunction_standardJensenFormula_nonzeroAtOrigin_closedDiskSupportFiniteProduct_boundaryLog_productSplit_finiteException_ownerRoot
      F Q hF hF0 ρ hρ hfactor hzero

/-- Closed-support finite-product boundary-log decomposition before applying
the zero-free quotient mean theorem. -/
theorem entireFunction_standardJensenFormula_nonzeroAtOrigin_closedDiskSupportFiniteProduct_boundaryLog_decomposition_from_factorization_ownerRoot
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
    entireFunction_standardJensenFormula_nonzeroAtOrigin_closedDiskSupportFiniteProduct_boundaryLog_decomposition_finiteException_ownerRoot
      F Q hF hF0 ρ hρ hfactor hzero

/-- Boundary logarithm decomposition for the closed-disk removable quotient.

This is the correct product form for closed-disk zero-freeness: all nonzero
zeros with `‖z‖ ≤ ρ`, including boundary zeros, have been extracted. -/
theorem entireFunction_standardJensenFormula_nonzeroAtOrigin_closedDiskSupportFiniteRemovableQuotient_boundaryLog_decomposition_ownerRoot
    (F Q : ℂ → ℂ)
    (hF : ∀ z : ℂ, AnalyticAt ℂ F z)
    (hF0 : F 0 ≠ 0)
    (ρ : ℝ)
    (hρ : 1 ≤ ρ)
    (hQ_an : ∀ w : ℂ, ‖w‖ ≤ ρ → AnalyticAt ℂ Q w)
    (hfactor :
      ∀ w : ℂ,
        ‖w‖ ≤ ρ →
        F w =
          Q w *
            entireFunction_standardJensenFormula_nonzeroAtOrigin_closedDiskSupportFiniteZeroDivisorProduct
              F hF hF0 ρ w)
    (hzero : ∀ w : ℂ, ‖w‖ ≤ ρ → Q w ≠ 0) :
    entireFunctionJensenBoundaryLogAverage F ρ =
      Real.log ‖Q 0‖ +
        (∑ z in
          entireFunction_standardJensenFormula_nonzeroAtOrigin_closedDiskSupportFiniteZeroDivisor
            F hF hF0 ρ,
          (entireFunctionZeroMultiplicity F hF (z : ℂ) : ℝ) *
            ((2 * Real.pi)⁻¹ *
              (∫ θ in (0 : ℝ)..(2 * Real.pi),
                Real.log
                  ‖1 - (((ρ : ℂ) * Complex.exp (θ * Complex.I)) / (z : ℂ))‖))) := by
  let quotientBoundary : ℝ :=
    (2 * Real.pi)⁻¹ *
      (∫ θ in (0 : ℝ)..(2 * Real.pi),
        Real.log ‖Q ((ρ : ℂ) * Complex.exp (θ * Complex.I))‖)
  let factorBoundary : ℝ :=
    ∑ z in
      entireFunction_standardJensenFormula_nonzeroAtOrigin_closedDiskSupportFiniteZeroDivisor
        F hF hF0 ρ,
      (entireFunctionZeroMultiplicity F hF (z : ℂ) : ℝ) *
        ((2 * Real.pi)⁻¹ *
          (∫ θ in (0 : ℝ)..(2 * Real.pi),
            Real.log
              ‖1 - (((ρ : ℂ) * Complex.exp (θ * Complex.I)) / (z : ℂ))‖))
  have hsplit :
      entireFunctionJensenBoundaryLogAverage F ρ =
        quotientBoundary + factorBoundary :=
    entireFunction_standardJensenFormula_nonzeroAtOrigin_closedDiskSupportFiniteProduct_boundaryLog_decomposition_from_factorization_ownerRoot
      F Q hF hF0 ρ hρ hfactor hzero
  have hquotient_mean :
      quotientBoundary = Real.log ‖Q 0‖ :=
    entireFunction_zeroFreeOnClosedDisk_boundaryLogAverage_eq_origin_log_norm_ownerRoot
      Q ρ hρ hQ_an hzero
  calc
    entireFunctionJensenBoundaryLogAverage F ρ =
        quotientBoundary + factorBoundary := hsplit
    _ = Real.log ‖Q 0‖ + factorBoundary := by
      exact congrArg (fun x : ℝ => x + factorBoundary) hquotient_mean
    _ =
      Real.log ‖Q 0‖ +
        (∑ z in
          entireFunction_standardJensenFormula_nonzeroAtOrigin_closedDiskSupportFiniteZeroDivisor
            F hF hF0 ρ,
          (entireFunctionZeroMultiplicity F hF (z : ℂ) : ℝ) *
            ((2 * Real.pi)⁻¹ *
              (∫ θ in (0 : ℝ)..(2 * Real.pi),
                Real.log
                  ‖1 - (((ρ : ℂ) * Complex.exp (θ * Complex.I)) / (z : ℂ))‖))) := by
      rfl

/-- Closed-disk product boundary factors split into the radial-gap factors plus
the boundary-zero factors.

Boundary-zero factors are present in the closed-disk quotient but have zero
radial-gap contribution; the final radial assembly must account for them by
this comparison rather than by asserting that they are absent. -/
theorem entireFunction_standardJensenFormula_nonzeroAtOrigin_closedDiskSupport_boundaryFactorSum_eq_radialGapSum_plus_boundaryZeroFactors_ownerRoot
    (F : ℂ → ℂ)
    (hF : ∀ z : ℂ, AnalyticAt ℂ F z)
    (hF0 : F 0 ≠ 0)
    (ρ : ℝ)
    [∀ z : EntireFunctionZero F, Decidable (‖(z : ℂ)‖ < ρ)] :
    (∑ z in
      entireFunction_standardJensenFormula_nonzeroAtOrigin_closedDiskSupportFiniteZeroDivisor
        F hF hF0 ρ,
      (entireFunctionZeroMultiplicity F hF (z : ℂ) : ℝ) *
        ((2 * Real.pi)⁻¹ *
          (∫ θ in (0 : ℝ)..(2 * Real.pi),
            Real.log
              ‖1 - (((ρ : ℂ) * Complex.exp (θ * Complex.I)) / (z : ℂ))‖))) =
      (∑ z in
        entireFunction_standardJensenFormula_nonzeroAtOrigin_radialGapSupportFiniteZeroDivisor
          F hF hF0 ρ,
        (entireFunctionZeroMultiplicity F hF (z : ℂ) : ℝ) *
          ((2 * Real.pi)⁻¹ *
            (∫ θ in (0 : ℝ)..(2 * Real.pi),
              Real.log
                ‖1 - (((ρ : ℂ) * Complex.exp (θ * Complex.I)) / (z : ℂ))‖))) +
        (∑ z in
          entireFunction_standardJensenFormula_nonzeroAtOrigin_closedDiskBoundarySupportFiniteZeroDivisor
            F hF hF0 ρ,
          (entireFunctionZeroMultiplicity F hF (z : ℂ) : ℝ) *
            ((2 * Real.pi)⁻¹ *
              (∫ θ in (0 : ℝ)..(2 * Real.pi),
                Real.log
                  ‖1 - (((ρ : ℂ) * Complex.exp (θ * Complex.I)) / (z : ℂ))‖))) := by
  let φ : EntireFunctionZero F → ℝ :=
    fun z =>
      (entireFunctionZeroMultiplicity F hF (z : ℂ) : ℝ) *
        ((2 * Real.pi)⁻¹ *
          (∫ θ in (0 : ℝ)..(2 * Real.pi),
            Real.log
              ‖1 - (((ρ : ℂ) * Complex.exp (θ * Complex.I)) / (z : ℂ))‖))
  have hsplit_set :
      entireFunction_standardJensenFormula_nonzeroAtOrigin_closedDiskSupportFiniteZeroDivisor
          F hF hF0 ρ =
        entireFunction_standardJensenFormula_nonzeroAtOrigin_closedDiskInteriorSupportFiniteZeroDivisor
            F hF hF0 ρ ∪
          entireFunction_standardJensenFormula_nonzeroAtOrigin_closedDiskBoundarySupportFiniteZeroDivisor
            F hF hF0 ρ :=
    entireFunction_standardJensenFormula_nonzeroAtOrigin_closedDiskSupportFiniteZeroDivisor_eq_interior_union_boundary
      F hF hF0 ρ
  have hclosed_sum :
      (∑ z in
        entireFunction_standardJensenFormula_nonzeroAtOrigin_closedDiskSupportFiniteZeroDivisor
          F hF hF0 ρ,
        φ z) =
        (∑ z in
          entireFunction_standardJensenFormula_nonzeroAtOrigin_closedDiskInteriorSupportFiniteZeroDivisor
              F hF hF0 ρ ∪
            entireFunction_standardJensenFormula_nonzeroAtOrigin_closedDiskBoundarySupportFiniteZeroDivisor
              F hF hF0 ρ,
          φ z) :=
    congrArg (fun s : Finset (EntireFunctionZero F) => ∑ z in s, φ z)
      hsplit_set
  have hdisjoint :
      Disjoint
        (entireFunction_standardJensenFormula_nonzeroAtOrigin_closedDiskInteriorSupportFiniteZeroDivisor
          F hF hF0 ρ)
        (entireFunction_standardJensenFormula_nonzeroAtOrigin_closedDiskBoundarySupportFiniteZeroDivisor
          F hF hF0 ρ) :=
    Finset.disjoint_left.2
      (fun z hz_int hz_bd =>
        (Finset.mem_filter.1 hz_bd).2 (Finset.mem_filter.1 hz_int).2)
  have hunion_sum :
      (∑ z in
        entireFunction_standardJensenFormula_nonzeroAtOrigin_closedDiskInteriorSupportFiniteZeroDivisor
            F hF hF0 ρ ∪
          entireFunction_standardJensenFormula_nonzeroAtOrigin_closedDiskBoundarySupportFiniteZeroDivisor
            F hF hF0 ρ,
        φ z) =
        (∑ z in
          entireFunction_standardJensenFormula_nonzeroAtOrigin_closedDiskInteriorSupportFiniteZeroDivisor
            F hF hF0 ρ,
          φ z) +
          (∑ z in
            entireFunction_standardJensenFormula_nonzeroAtOrigin_closedDiskBoundarySupportFiniteZeroDivisor
              F hF hF0 ρ,
            φ z) :=
    Finset.sum_union hdisjoint
  have hinterior_radial :
      (∑ z in
        entireFunction_standardJensenFormula_nonzeroAtOrigin_closedDiskInteriorSupportFiniteZeroDivisor
          F hF hF0 ρ,
        φ z) =
        (∑ z in
          entireFunction_standardJensenFormula_nonzeroAtOrigin_radialGapSupportFiniteZeroDivisor
            F hF hF0 ρ,
          φ z) :=
    congrArg (fun s : Finset (EntireFunctionZero F) => ∑ z in s, φ z)
      (entireFunction_standardJensenFormula_nonzeroAtOrigin_closedDiskInteriorSupportFiniteZeroDivisor_eq_radialGapSupportFiniteZeroDivisor_ownerRoot
        F hF hF0 ρ)
  calc
    (∑ z in
      entireFunction_standardJensenFormula_nonzeroAtOrigin_closedDiskSupportFiniteZeroDivisor
        F hF hF0 ρ,
      (entireFunctionZeroMultiplicity F hF (z : ℂ) : ℝ) *
        ((2 * Real.pi)⁻¹ *
          (∫ θ in (0 : ℝ)..(2 * Real.pi),
            Real.log
              ‖1 - (((ρ : ℂ) * Complex.exp (θ * Complex.I)) / (z : ℂ))‖))) =
        (∑ z in
          entireFunction_standardJensenFormula_nonzeroAtOrigin_closedDiskSupportFiniteZeroDivisor
            F hF hF0 ρ,
          φ z) := by
      rfl
    _ =
        (∑ z in
          entireFunction_standardJensenFormula_nonzeroAtOrigin_closedDiskInteriorSupportFiniteZeroDivisor
              F hF hF0 ρ ∪
            entireFunction_standardJensenFormula_nonzeroAtOrigin_closedDiskBoundarySupportFiniteZeroDivisor
              F hF hF0 ρ,
          φ z) := hclosed_sum
    _ =
        (∑ z in
          entireFunction_standardJensenFormula_nonzeroAtOrigin_closedDiskInteriorSupportFiniteZeroDivisor
            F hF hF0 ρ,
          φ z) +
          (∑ z in
            entireFunction_standardJensenFormula_nonzeroAtOrigin_closedDiskBoundarySupportFiniteZeroDivisor
              F hF hF0 ρ,
            φ z) := hunion_sum
    _ =
        (∑ z in
          entireFunction_standardJensenFormula_nonzeroAtOrigin_radialGapSupportFiniteZeroDivisor
            F hF hF0 ρ,
          φ z) +
          (∑ z in
            entireFunction_standardJensenFormula_nonzeroAtOrigin_closedDiskBoundarySupportFiniteZeroDivisor
              F hF hF0 ρ,
            φ z) := by
      exact congrArg
        (fun x : ℝ =>
          x +
            (∑ z in
              entireFunction_standardJensenFormula_nonzeroAtOrigin_closedDiskBoundarySupportFiniteZeroDivisor
                F hF hF0 ρ,
              φ z))
        hinterior_radial
    _ =
      (∑ z in
        entireFunction_standardJensenFormula_nonzeroAtOrigin_radialGapSupportFiniteZeroDivisor
          F hF hF0 ρ,
        (entireFunctionZeroMultiplicity F hF (z : ℂ) : ℝ) *
          ((2 * Real.pi)⁻¹ *
            (∫ θ in (0 : ℝ)..(2 * Real.pi),
              Real.log
                ‖1 - (((ρ : ℂ) * Complex.exp (θ * Complex.I)) / (z : ℂ))‖))) +
        (∑ z in
          entireFunction_standardJensenFormula_nonzeroAtOrigin_closedDiskBoundarySupportFiniteZeroDivisor
            F hF hF0 ρ,
          (entireFunctionZeroMultiplicity F hF (z : ℂ) : ℝ) *
            ((2 * Real.pi)⁻¹ *
              (∫ θ in (0 : ℝ)..(2 * Real.pi),
                Real.log
                  ‖1 - (((ρ : ℂ) * Complex.exp (θ * Complex.I)) / (z : ℂ))‖))) := by
      rfl

/-- Closed-support boundary-factor sum reduces to the radial-gap factor sum
because the boundary-zero factor sum is zero. -/
theorem entireFunction_standardJensenFormula_nonzeroAtOrigin_closedDiskSupport_boundaryFactorSum_eq_radialGapSum_ownerRoot
    (F : ℂ → ℂ)
    (hF : ∀ z : ℂ, AnalyticAt ℂ F z)
    (hF0 : F 0 ≠ 0)
    (ρ : ℝ) :
    (∑ z in
      entireFunction_standardJensenFormula_nonzeroAtOrigin_closedDiskSupportFiniteZeroDivisor
        F hF hF0 ρ,
      (entireFunctionZeroMultiplicity F hF (z : ℂ) : ℝ) *
        ((2 * Real.pi)⁻¹ *
          (∫ θ in (0 : ℝ)..(2 * Real.pi),
            Real.log
              ‖1 - (((ρ : ℂ) * Complex.exp (θ * Complex.I)) / (z : ℂ))‖))) =
      (∑ z in
        entireFunction_standardJensenFormula_nonzeroAtOrigin_radialGapSupportFiniteZeroDivisor
          F hF hF0 ρ,
        (entireFunctionZeroMultiplicity F hF (z : ℂ) : ℝ) *
          ((2 * Real.pi)⁻¹ *
            (∫ θ in (0 : ℝ)..(2 * Real.pi),
              Real.log
                ‖1 - (((ρ : ℂ) * Complex.exp (θ * Complex.I)) / (z : ℂ))‖))) := by
  have hsplit :
      (∑ z in
        entireFunction_standardJensenFormula_nonzeroAtOrigin_closedDiskSupportFiniteZeroDivisor
          F hF hF0 ρ,
        (entireFunctionZeroMultiplicity F hF (z : ℂ) : ℝ) *
          ((2 * Real.pi)⁻¹ *
            (∫ θ in (0 : ℝ)..(2 * Real.pi),
              Real.log
                ‖1 - (((ρ : ℂ) * Complex.exp (θ * Complex.I)) / (z : ℂ))‖))) =
        (∑ z in
          entireFunction_standardJensenFormula_nonzeroAtOrigin_radialGapSupportFiniteZeroDivisor
            F hF hF0 ρ,
          (entireFunctionZeroMultiplicity F hF (z : ℂ) : ℝ) *
            ((2 * Real.pi)⁻¹ *
              (∫ θ in (0 : ℝ)..(2 * Real.pi),
                Real.log
                  ‖1 - (((ρ : ℂ) * Complex.exp (θ * Complex.I)) / (z : ℂ))‖))) +
          (∑ z in
            entireFunction_standardJensenFormula_nonzeroAtOrigin_closedDiskBoundarySupportFiniteZeroDivisor
              F hF hF0 ρ,
            (entireFunctionZeroMultiplicity F hF (z : ℂ) : ℝ) *
              ((2 * Real.pi)⁻¹ *
                (∫ θ in (0 : ℝ)..(2 * Real.pi),
                  Real.log
                    ‖1 - (((ρ : ℂ) * Complex.exp (θ * Complex.I)) / (z : ℂ))‖))) :=
    entireFunction_standardJensenFormula_nonzeroAtOrigin_closedDiskSupport_boundaryFactorSum_eq_radialGapSum_plus_boundaryZeroFactors_ownerRoot
      F hF hF0 ρ
  have hboundary_zero :
      (∑ z in
        entireFunction_standardJensenFormula_nonzeroAtOrigin_closedDiskBoundarySupportFiniteZeroDivisor
          F hF hF0 ρ,
        (entireFunctionZeroMultiplicity F hF (z : ℂ) : ℝ) *
          ((2 * Real.pi)⁻¹ *
            (∫ θ in (0 : ℝ)..(2 * Real.pi),
              Real.log
                ‖1 - (((ρ : ℂ) * Complex.exp (θ * Complex.I)) / (z : ℂ))‖))) =
        0 :=
    entireFunction_standardJensenFormula_nonzeroAtOrigin_closedDiskBoundarySupportFiniteZeroDivisor_boundaryFactorSum_eq_zero
      F hF hF0 ρ
  calc
    (∑ z in
      entireFunction_standardJensenFormula_nonzeroAtOrigin_closedDiskSupportFiniteZeroDivisor
        F hF hF0 ρ,
      (entireFunctionZeroMultiplicity F hF (z : ℂ) : ℝ) *
        ((2 * Real.pi)⁻¹ *
          (∫ θ in (0 : ℝ)..(2 * Real.pi),
            Real.log
              ‖1 - (((ρ : ℂ) * Complex.exp (θ * Complex.I)) / (z : ℂ))‖))) =
        (∑ z in
          entireFunction_standardJensenFormula_nonzeroAtOrigin_radialGapSupportFiniteZeroDivisor
            F hF hF0 ρ,
          (entireFunctionZeroMultiplicity F hF (z : ℂ) : ℝ) *
            ((2 * Real.pi)⁻¹ *
              (∫ θ in (0 : ℝ)..(2 * Real.pi),
                Real.log
                  ‖1 - (((ρ : ℂ) * Complex.exp (θ * Complex.I)) / (z : ℂ))‖))) +
          (∑ z in
            entireFunction_standardJensenFormula_nonzeroAtOrigin_closedDiskBoundarySupportFiniteZeroDivisor
              F hF hF0 ρ,
            (entireFunctionZeroMultiplicity F hF (z : ℂ) : ℝ) *
              ((2 * Real.pi)⁻¹ *
                (∫ θ in (0 : ℝ)..(2 * Real.pi),
                  Real.log
                    ‖1 - (((ρ : ℂ) * Complex.exp (θ * Complex.I)) / (z : ℂ))‖))) := by
      exact hsplit
    _ =
        (∑ z in
          entireFunction_standardJensenFormula_nonzeroAtOrigin_radialGapSupportFiniteZeroDivisor
            F hF hF0 ρ,
          (entireFunctionZeroMultiplicity F hF (z : ℂ) : ℝ) *
            ((2 * Real.pi)⁻¹ *
              (∫ θ in (0 : ℝ)..(2 * Real.pi),
                Real.log
                  ‖1 - (((ρ : ℂ) * Complex.exp (θ * Complex.I)) / (z : ℂ))‖))) +
          0 := by
      exact congrArg
        (fun x : ℝ =>
          (∑ z in
            entireFunction_standardJensenFormula_nonzeroAtOrigin_radialGapSupportFiniteZeroDivisor
              F hF hF0 ρ,
            (entireFunctionZeroMultiplicity F hF (z : ℂ) : ℝ) *
              ((2 * Real.pi)⁻¹ *
                (∫ θ in (0 : ℝ)..(2 * Real.pi),
                  Real.log
                    ‖1 - (((ρ : ℂ) * Complex.exp (θ * Complex.I)) / (z : ℂ))‖))) +
            x)
        hboundary_zero
    _ =
        (∑ z in
          entireFunction_standardJensenFormula_nonzeroAtOrigin_radialGapSupportFiniteZeroDivisor
            F hF hF0 ρ,
          (entireFunctionZeroMultiplicity F hF (z : ℂ) : ℝ) *
            ((2 * Real.pi)⁻¹ *
              (∫ θ in (0 : ℝ)..(2 * Real.pi),
                Real.log
                  ‖1 - (((ρ : ℂ) * Complex.exp (θ * Complex.I)) / (z : ℂ))‖))) := by
      exact add_zero
        (∑ z in
          entireFunction_standardJensenFormula_nonzeroAtOrigin_radialGapSupportFiniteZeroDivisor
            F hF hF0 ρ,
          (entireFunctionZeroMultiplicity F hF (z : ℂ) : ℝ) *
            ((2 * Real.pi)⁻¹ *
              (∫ θ in (0 : ℝ)..(2 * Real.pi),
                Real.log
                  ‖1 - (((ρ : ℂ) * Complex.exp (θ * Complex.I)) / (z : ℂ))‖)))

/-- Removable quotient after extracting the closed-disk Jensen support divisor.

This is the owner-level removable-singularity factor theorem needed by the
closed-disk finite-product Jensen proof.  The quotient is supplied existentially, not by
globally choosing the raw expression `F / P`; at the support zeros the raw
division expression has the wrong value because division sends `0 / 0` to `0`.
The construction removes those singularities with the matched local
multiplicities for all nonzero zeros with `‖z‖ ≤ ρ`, including boundary zeros,
and returns the closed-support boundary decomposition used downstream.
Cf. Titchmarsh, *The Theory of Functions*, §5. -/
theorem entireFunction_standardJensenFormula_nonzeroAtOrigin_closedDiskSupportFiniteRemovableQuotient_exists_ownerRoot
    (F : ℂ → ℂ)
    (hF : ∀ z : ℂ, AnalyticAt ℂ F z)
    (hF0 : F 0 ≠ 0)
    (ρ : ℝ)
    (hρ : 1 ≤ ρ) :
    ∃ Q : ℂ → ℂ,
      (∀ w : ℂ,
        ‖w‖ ≤ ρ →
        F w =
          Q w *
            entireFunction_standardJensenFormula_nonzeroAtOrigin_closedDiskSupportFiniteZeroDivisorProduct
              F hF hF0 ρ w) ∧
      (∀ w : ℂ, ‖w‖ ≤ ρ → Q w ≠ 0) ∧
      (entireFunctionJensenBoundaryLogAverage F ρ =
        Real.log ‖Q 0‖ +
          (∑ z in
            entireFunction_standardJensenFormula_nonzeroAtOrigin_closedDiskSupportFiniteZeroDivisor
              F hF hF0 ρ,
            (entireFunctionZeroMultiplicity F hF (z : ℂ) : ℝ) *
              ((2 * Real.pi)⁻¹ *
                (∫ θ in (0 : ℝ)..(2 * Real.pi),
                  Real.log
                    ‖1 - (((ρ : ℂ) * Complex.exp (θ * Complex.I)) / (z : ℂ))‖)))) ∧
      (Real.log ‖Q 0‖ = Real.log ‖F 0‖) := by
  match
      entireFunction_standardJensenFormula_nonzeroAtOrigin_closedDiskSupportFiniteRemovableQuotient_extension_ownerRoot
        F hF hF0 ρ hρ with
  | ⟨Q, hQ_an, hfactor, horigin_value⟩ =>
      have hzero : ∀ w : ℂ, ‖w‖ ≤ ρ → Q w ≠ 0 :=
        entireFunction_standardJensenFormula_nonzeroAtOrigin_closedDiskSupportFiniteRemovableQuotient_zeroFree_ownerRoot
          F Q hF hF0 ρ hQ_an hfactor
      have hboundary :
          entireFunctionJensenBoundaryLogAverage F ρ =
            Real.log ‖Q 0‖ +
              (∑ z in
                entireFunction_standardJensenFormula_nonzeroAtOrigin_closedDiskSupportFiniteZeroDivisor
                  F hF hF0 ρ,
                (entireFunctionZeroMultiplicity F hF (z : ℂ) : ℝ) *
                  ((2 * Real.pi)⁻¹ *
                    (∫ θ in (0 : ℝ)..(2 * Real.pi),
                      Real.log
                        ‖1 - (((ρ : ℂ) * Complex.exp (θ * Complex.I)) / (z : ℂ))‖))) :=
        entireFunction_standardJensenFormula_nonzeroAtOrigin_closedDiskSupportFiniteRemovableQuotient_boundaryLog_decomposition_ownerRoot
          F Q hF hF0 ρ hρ hQ_an hfactor hzero
      have horigin :
          Real.log ‖Q 0‖ = Real.log ‖F 0‖ :=
        congrArg (fun x : ℝ => Real.log x) (congrArg norm horigin_value)
      exact ⟨Q, hfactor, hzero, hboundary, horigin⟩

/-- Canonical closed-support finite product factorization on Jensen's closed disk.

The quotient is obtained by locally destructing the closed-disk removable
quotient package; no global choice of a raw quotient is made. -/
theorem entireFunction_standardJensenFormula_nonzeroAtOrigin_closedDiskSupportFiniteProduct_factorization_zeroFreeOnClosedDisk_ownerRoot
    (F : ℂ → ℂ)
    (hF : ∀ z : ℂ, AnalyticAt ℂ F z)
    (hF0 : F 0 ≠ 0)
    (ρ : ℝ)
    (hρ : 1 ≤ ρ) :
    ∃ Q : ℂ → ℂ,
      (∀ w : ℂ,
        ‖w‖ ≤ ρ →
        F w =
          Q w *
            entireFunction_standardJensenFormula_nonzeroAtOrigin_closedDiskSupportFiniteZeroDivisorProduct
              F hF hF0 ρ w) ∧
      (∀ w : ℂ, ‖w‖ ≤ ρ → Q w ≠ 0) ∧
      (entireFunctionJensenBoundaryLogAverage F ρ =
        Real.log ‖Q 0‖ +
          (∑ z in
            entireFunction_standardJensenFormula_nonzeroAtOrigin_closedDiskSupportFiniteZeroDivisor
              F hF hF0 ρ,
            (entireFunctionZeroMultiplicity F hF (z : ℂ) : ℝ) *
              ((2 * Real.pi)⁻¹ *
                (∫ θ in (0 : ℝ)..(2 * Real.pi),
                  Real.log
                    ‖1 - (((ρ : ℂ) * Complex.exp (θ * Complex.I)) / (z : ℂ))‖)))) ∧
      (Real.log ‖Q 0‖ = Real.log ‖F 0‖) := by
  match
      entireFunction_standardJensenFormula_nonzeroAtOrigin_closedDiskSupportFiniteRemovableQuotient_exists_ownerRoot
        F hF hF0 ρ hρ with
  | ⟨Q, hfactor, hzero, hboundary, horigin⟩ =>
      exact ⟨Q, hfactor, hzero, hboundary, horigin⟩

/-- There is a closed-support removable finite divisor quotient which is
zero-free on Jensen's closed disk. -/
theorem entireFunction_standardJensenFormula_nonzeroAtOrigin_closedDiskSupportFiniteRemovableQuotient_zeroFreeOnClosedDisk
    (F : ℂ → ℂ)
    (hF : ∀ z : ℂ, AnalyticAt ℂ F z)
    (hF0 : F 0 ≠ 0)
    (ρ : ℝ)
    (hρ : 1 ≤ ρ) :
    ∃ Q : ℂ → ℂ,
      ∀ w : ℂ, ‖w‖ ≤ ρ → Q w ≠ 0 := by
  match
      entireFunction_standardJensenFormula_nonzeroAtOrigin_closedDiskSupportFiniteProduct_factorization_zeroFreeOnClosedDisk_ownerRoot
        F hF hF0 ρ hρ with
  | ⟨Q, _hfactor, hzero, _hboundary, _horigin⟩ =>
      exact ⟨Q, hzero⟩


end
end LFunctions
end Boundary
