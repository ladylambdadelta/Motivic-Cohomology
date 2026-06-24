import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaExplicitFormulaVerticalChannels.OwnerParts.CorrectionAffineValues
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaExplicitFormulaVerticalChannels.OwnerParts.InverseGammaAffineKernelEstimate
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaExplicitFormulaVerticalChannels.OwnerParts.ArchimedeanGammaBinetLineCore

/-!
# One-sided inverse-Gamma affine values

This file owns the one-sided whole-line values for the inverse-Gamma
completion affine kernels.  These are stronger than the already proved
right-minus-left inverse-Gamma normalization: they must be proved directly from
the Binet logarithm on each affine line and the Cauchy/Laplace pole
normalizations, not recovered from the downstream archimedean line values.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open Complex
open Filter
open LSeries ArithmeticFunction
open MeasureTheory
open scoped ArithmeticFunction
open scoped Topology

namespace ZetaAdmissibleFunction

/-- Integral recombination on the right affine line from the pointwise identity
`archimedean + correction = inverseGamma`.

This lemma is only the measure-theoretic and algebraic transport step.  The
analytic Binet input is the archimedean whole-line value supplied as
`harch_value`; the elementary correction value is already owned by
`CorrectionAffineValues`. -/
theorem zetaCompletedExplicitFormulaInverseGammaRightAffineKernel_integral_eq_archimedeanValue_add_correctionRightValue
    (f : ZetaAdmissibleFunction)
    (F : ExplicitFormulaVerticallyRegularContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F.toContourFamily)
    (harch_integrable :
      Integrable
        (zetaCompletedExplicitFormulaArchimedeanRightAffineKernel
          f F.toContourFamily)
        (volume : Measure ℝ))
    (harch_value :
      (∫ t : ℝ,
        zetaCompletedExplicitFormulaArchimedeanRightAffineKernel
          f F.toContourFamily t) =
        zetaCompletedExplicitFormulaPhi f 0) :
    (∫ t : ℝ,
      zetaCompletedExplicitFormulaInverseGammaRightAffineKernel
        f F.toContourFamily t) =
      zetaCompletedExplicitFormulaPhi f 0 +
        zetaCompletedExplicitFormulaCorrectionRightZeroPoleVerticalInversionValue f := by
  have hcorrection_value :
      (∫ t : ℝ,
        zetaCompletedExplicitFormulaCorrectionRightAffineKernel
          f F.toContourFamily t) =
        zetaCompletedExplicitFormulaCorrectionRightZeroPoleVerticalInversionValue f :=
    zetaCompletedExplicitFormulaCorrectionRightAffineKernel_integral_eq_value_ownerCorrectionAffineValues
      f F.toContourFamily h
  have hzero_int :
      Integrable
        (zetaCompletedExplicitFormulaCorrectionRightZeroPoleAffineKernel
          f F.toContourFamily)
        (volume : Measure ℝ) :=
    zetaCompletedExplicitFormulaCorrectionRightZeroPoleAffineKernel_integrable_ownerBounds
      f F.toContourFamily h
  have hone_int :
      Integrable
        (zetaCompletedExplicitFormulaCorrectionRightOnePoleAffineKernel
          f F.toContourFamily)
        (volume : Measure ℝ) :=
    zetaCompletedExplicitFormulaCorrectionRightOnePoleAffineKernel_integrable_ownerBounds
      f F.toContourFamily h
  have hcorrection_point :
      (zetaCompletedExplicitFormulaCorrectionRightAffineKernel
          f F.toContourFamily) =ᵐ[volume]
        fun t : ℝ =>
          zetaCompletedExplicitFormulaCorrectionRightZeroPoleAffineKernel
              f F.toContourFamily t +
            zetaCompletedExplicitFormulaCorrectionRightOnePoleAffineKernel
              f F.toContourFamily t :=
    Filter.Eventually.of_forall
      (fun t =>
        zetaCompletedExplicitFormulaCorrectionRightAffineKernel_eq_zeroPole_add_onePole
          f F.toContourFamily t)
  have hcorrection_integrable :
      Integrable
        (zetaCompletedExplicitFormulaCorrectionRightAffineKernel
          f F.toContourFamily)
        (volume : Measure ℝ) :=
    (hzero_int.add hone_int).congr hcorrection_point.symm
  have hsum :
      (∫ t : ℝ,
        zetaCompletedExplicitFormulaArchimedeanRightAffineKernel
            f F.toContourFamily t +
          zetaCompletedExplicitFormulaCorrectionRightAffineKernel
            f F.toContourFamily t) =
        (∫ t : ℝ,
          zetaCompletedExplicitFormulaArchimedeanRightAffineKernel
            f F.toContourFamily t) +
          ∫ t : ℝ,
            zetaCompletedExplicitFormulaCorrectionRightAffineKernel
              f F.toContourFamily t :=
    integral_add harch_integrable hcorrection_integrable
  have hinverse_point :
      (zetaCompletedExplicitFormulaInverseGammaRightAffineKernel
          f F.toContourFamily) =ᵐ[volume]
        fun t : ℝ =>
          zetaCompletedExplicitFormulaArchimedeanRightAffineKernel
              f F.toContourFamily t +
            zetaCompletedExplicitFormulaCorrectionRightAffineKernel
              f F.toContourFamily t :=
    Filter.Eventually.of_forall
      (fun t =>
        (zetaCompletedExplicitFormulaArchimedeanRightAffineKernel_add_correction_eq_inverseGamma
          f F.toContourFamily t).symm)
  calc
    (∫ t : ℝ,
      zetaCompletedExplicitFormulaInverseGammaRightAffineKernel
        f F.toContourFamily t) =
        ∫ t : ℝ,
          zetaCompletedExplicitFormulaArchimedeanRightAffineKernel
              f F.toContourFamily t +
            zetaCompletedExplicitFormulaCorrectionRightAffineKernel
              f F.toContourFamily t := by
      exact integral_congr_ae hinverse_point
    _ =
        (∫ t : ℝ,
          zetaCompletedExplicitFormulaArchimedeanRightAffineKernel
            f F.toContourFamily t) +
          ∫ t : ℝ,
            zetaCompletedExplicitFormulaCorrectionRightAffineKernel
              f F.toContourFamily t := by
      exact hsum
    _ =
        zetaCompletedExplicitFormulaPhi f 0 +
          ∫ t : ℝ,
            zetaCompletedExplicitFormulaCorrectionRightAffineKernel
              f F.toContourFamily t := by
      exact congrArg
        (fun z : ℂ =>
          z +
            ∫ t : ℝ,
              zetaCompletedExplicitFormulaCorrectionRightAffineKernel
                f F.toContourFamily t)
        harch_value
    _ =
        zetaCompletedExplicitFormulaPhi f 0 +
          zetaCompletedExplicitFormulaCorrectionRightZeroPoleVerticalInversionValue f := by
      exact congrArg
        (fun z : ℂ => zetaCompletedExplicitFormulaPhi f 0 + z)
        hcorrection_value

/-- Integral recombination on the left affine line from the pointwise identity
`archimedean + correction = inverseGamma`.

This is the left-line analogue of the right recombination lemma above.  It
keeps the shifted Binet value as the only analytic input and consumes the
already-proved left elementary correction affine value. -/
theorem zetaCompletedExplicitFormulaInverseGammaLeftAffineKernel_integral_eq_archimedeanValue_add_correctionLeftValue
    (f : ZetaAdmissibleFunction)
    (F : ExplicitFormulaVerticallyRegularContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F.toContourFamily)
    (harch_integrable :
      Integrable
        (zetaCompletedExplicitFormulaArchimedeanLeftAffineKernel
          f F.toContourFamily)
        (volume : Measure ℝ))
    (harch_value :
      (∫ t : ℝ,
        zetaCompletedExplicitFormulaArchimedeanLeftAffineKernel
          f F.toContourFamily t) =
        -(zetaCompletedExplicitFormulaPhi f 0)) :
    (∫ t : ℝ,
      zetaCompletedExplicitFormulaInverseGammaLeftAffineKernel
        f F.toContourFamily t) =
      -(zetaCompletedExplicitFormulaPhi f 0) +
        (((2 * (Real.pi : ℂ) * Complex.I) *
          (-zetaCompletedExplicitFormulaPhi f (1 / 2))) * Complex.I) := by
  let B : ℂ :=
    ((2 * (Real.pi : ℂ) * Complex.I) *
      (-zetaCompletedExplicitFormulaPhi f (1 / 2))) * Complex.I
  have hcorrection_value :
      (∫ t : ℝ,
        zetaCompletedExplicitFormulaCorrectionLeftAffineKernel
          f F.toContourFamily t) = B :=
    zetaCompletedExplicitFormulaCorrectionLeftAffineKernel_integral_eq_standardResidue_ownerCorrectionAffineValues
      f F.toContourFamily h
  have hzero_int :
      Integrable
        (zetaCompletedExplicitFormulaCorrectionLeftZeroPoleAffineKernel
          f F.toContourFamily)
        (volume : Measure ℝ) :=
    zetaCompletedExplicitFormulaCorrectionLeftZeroPoleAffineKernel_integrable_ownerBounds
      f F.toContourFamily h
  have hone_int :
      Integrable
        (zetaCompletedExplicitFormulaCorrectionLeftOnePoleAffineKernel
          f F.toContourFamily)
        (volume : Measure ℝ) :=
    zetaCompletedExplicitFormulaCorrectionLeftOnePoleAffineKernel_integrable_ownerBounds
      f F.toContourFamily h
  have hcorrection_point :
      (zetaCompletedExplicitFormulaCorrectionLeftAffineKernel
          f F.toContourFamily) =ᵐ[volume]
        fun t : ℝ =>
          zetaCompletedExplicitFormulaCorrectionLeftZeroPoleAffineKernel
              f F.toContourFamily t +
            zetaCompletedExplicitFormulaCorrectionLeftOnePoleAffineKernel
              f F.toContourFamily t :=
    Filter.Eventually.of_forall
      (fun t =>
        zetaCompletedExplicitFormulaCorrectionLeftAffineKernel_eq_zeroPole_add_onePole
          f F.toContourFamily t)
  have hcorrection_integrable :
      Integrable
        (zetaCompletedExplicitFormulaCorrectionLeftAffineKernel
          f F.toContourFamily)
        (volume : Measure ℝ) :=
    (hzero_int.add hone_int).congr hcorrection_point.symm
  have hsum :
      (∫ t : ℝ,
        zetaCompletedExplicitFormulaArchimedeanLeftAffineKernel
            f F.toContourFamily t +
          zetaCompletedExplicitFormulaCorrectionLeftAffineKernel
            f F.toContourFamily t) =
        (∫ t : ℝ,
          zetaCompletedExplicitFormulaArchimedeanLeftAffineKernel
            f F.toContourFamily t) +
          ∫ t : ℝ,
            zetaCompletedExplicitFormulaCorrectionLeftAffineKernel
              f F.toContourFamily t :=
    integral_add harch_integrable hcorrection_integrable
  have hinverse_point :
      (zetaCompletedExplicitFormulaInverseGammaLeftAffineKernel
          f F.toContourFamily) =ᵐ[volume]
        fun t : ℝ =>
          zetaCompletedExplicitFormulaArchimedeanLeftAffineKernel
              f F.toContourFamily t +
            zetaCompletedExplicitFormulaCorrectionLeftAffineKernel
              f F.toContourFamily t :=
    Filter.Eventually.of_forall
      (fun t =>
        (zetaCompletedExplicitFormulaArchimedeanLeftAffineKernel_add_correction_eq_inverseGamma
          f F.toContourFamily t).symm)
  calc
    (∫ t : ℝ,
      zetaCompletedExplicitFormulaInverseGammaLeftAffineKernel
        f F.toContourFamily t) =
        ∫ t : ℝ,
          zetaCompletedExplicitFormulaArchimedeanLeftAffineKernel
              f F.toContourFamily t +
            zetaCompletedExplicitFormulaCorrectionLeftAffineKernel
              f F.toContourFamily t := by
      exact integral_congr_ae hinverse_point
    _ =
        (∫ t : ℝ,
          zetaCompletedExplicitFormulaArchimedeanLeftAffineKernel
            f F.toContourFamily t) +
          ∫ t : ℝ,
            zetaCompletedExplicitFormulaCorrectionLeftAffineKernel
              f F.toContourFamily t := by
      exact hsum
    _ =
        -(zetaCompletedExplicitFormulaPhi f 0) +
          ∫ t : ℝ,
            zetaCompletedExplicitFormulaCorrectionLeftAffineKernel
              f F.toContourFamily t := by
      exact congrArg
        (fun z : ℂ =>
          z +
            ∫ t : ℝ,
              zetaCompletedExplicitFormulaCorrectionLeftAffineKernel
                f F.toContourFamily t)
        harch_value
    _ =
        -(zetaCompletedExplicitFormulaPhi f 0) + B := by
      exact congrArg
        (fun z : ℂ => -(zetaCompletedExplicitFormulaPhi f 0) + z)
        hcorrection_value
    _ =
        -(zetaCompletedExplicitFormulaPhi f 0) +
          (((2 * (Real.pi : ℂ) * Complex.I) *
            (-zetaCompletedExplicitFormulaPhi f (1 / 2))) * Complex.I) := by
      exact Eq.refl _

/-- Non-circular inverse-Gamma right one-sided assembly from upstream
Gamma/Binet full-line component values.

This is an assembly theorem only.  The analytic content remains the
Gamma/Binet owner proof of the right main-plus-remainder affine value. -/
theorem zetaCompletedExplicitFormulaInverseGammaRightAffineKernel_integral_eq_phiZero_add_correctionRightValue_of_fullLineBinetValues_ownerOneSidedValues
    (f : ZetaAdmissibleFunction)
    (F : ExplicitFormulaVerticallyRegularContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F.toContourFamily)
    (hcoh : Complex.gammaBinetPrincipalLogCoherence)
    (hmain_value :
      (∫ t : ℝ,
        zetaCompletedExplicitFormulaArchimedeanRightBinetMainKernel
          f F.toContourFamily t) =
        zetaCompletedExplicitFormulaPhi f 0)
    (hremainder_value :
      (∫ t : ℝ,
        zetaCompletedExplicitFormulaArchimedeanRightBinetRemainderKernel
          f F.toContourFamily t) =
        0) :
    (∫ t : ℝ,
      zetaCompletedExplicitFormulaInverseGammaRightAffineKernel
        f F.toContourFamily t) =
      zetaCompletedExplicitFormulaPhi f 0 +
        zetaCompletedExplicitFormulaCorrectionRightZeroPoleVerticalInversionValue f := by
  have harch_integrable :
      Integrable
        (zetaCompletedExplicitFormulaArchimedeanRightAffineKernel
          f F.toContourFamily)
        (volume : Measure ℝ) :=
    zetaCompletedExplicitFormulaArchimedeanRightAffineKernel_integrable_ownerGammaBinetLineValue
      f F h hcoh
  have harch_value :
      (∫ t : ℝ,
        zetaCompletedExplicitFormulaArchimedeanRightAffineKernel
          f F.toContourFamily t) =
        zetaCompletedExplicitFormulaPhi f 0 :=
    zetaCompletedExplicitFormulaArchimedeanRightAffineKernel_integral_eq_phiZero_of_fullLineBinetValues
      f F h hcoh hmain_value hremainder_value
  exact
    zetaCompletedExplicitFormulaInverseGammaRightAffineKernel_integral_eq_archimedeanValue_add_correctionRightValue
      f F h harch_integrable harch_value

/-- Non-circular inverse-Gamma left one-sided assembly from upstream
Gamma/Binet full-line component values.

This is an assembly theorem only.  The analytic content remains the shifted
Gamma/Binet owner proof of the left main-plus-remainder affine value. -/
theorem zetaCompletedExplicitFormulaInverseGammaLeftAffineKernel_integral_eq_negPhiZero_add_correctionLeftValue_of_fullLineBinetValues_ownerOneSidedValues
    (f : ZetaAdmissibleFunction)
    (F : ExplicitFormulaVerticallyRegularContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F.toContourFamily)
    (hcoh : Complex.gammaBinetPrincipalLogCoherence)
    (hmain_value :
      (∫ t : ℝ,
        zetaCompletedExplicitFormulaArchimedeanLeftBinetMainKernel
          f F.toContourFamily t) =
        -(zetaCompletedExplicitFormulaPhi f 0))
    (hremainder_value :
      (∫ t : ℝ,
        zetaCompletedExplicitFormulaArchimedeanLeftBinetRemainderKernel
          f F.toContourFamily t) =
        0) :
    (∫ t : ℝ,
      zetaCompletedExplicitFormulaInverseGammaLeftAffineKernel
        f F.toContourFamily t) =
      -(zetaCompletedExplicitFormulaPhi f 0) +
        (((2 * (Real.pi : ℂ) * Complex.I) *
          (-zetaCompletedExplicitFormulaPhi f (1 / 2))) * Complex.I) := by
  have harch_integrable :
      Integrable
        (zetaCompletedExplicitFormulaArchimedeanLeftAffineKernel
          f F.toContourFamily)
        (volume : Measure ℝ) :=
    zetaCompletedExplicitFormulaArchimedeanLeftAffineKernel_integrable_ownerGammaBinetLineValue
      f F h hcoh
  have harch_value :
      (∫ t : ℝ,
        zetaCompletedExplicitFormulaArchimedeanLeftAffineKernel
          f F.toContourFamily t) =
        -(zetaCompletedExplicitFormulaPhi f 0) :=
    zetaCompletedExplicitFormulaArchimedeanLeftAffineKernel_integral_eq_neg_phiZero_of_fullLineBinetValues
      f F h hcoh hmain_value hremainder_value
  exact
    zetaCompletedExplicitFormulaInverseGammaLeftAffineKernel_integral_eq_archimedeanValue_add_correctionLeftValue
      f F h harch_integrable harch_value

/-- Owner analytic leaf: whole-line value of the right inverse-Gamma affine
kernel.

Proof target:
differentiate the right-line Binet logarithm for `Γℝ`, pair the full
main-plus-remainder expression with the Paley-Wiener transform, and add the
right zero-pole Cauchy/Laplace normalization.  This is the one-sided value
whose subtraction of the correction right affine value gives `Phi_f(0)`. -/
theorem zetaCompletedExplicitFormulaInverseGammaRightAffineKernel_integral_eq_phiZero_add_correctionRightValue_ownerOneSidedValues
    (f : ZetaAdmissibleFunction)
    (F : ExplicitFormulaVerticallyRegularContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F.toContourFamily)
    (hcoh : Complex.gammaBinetPrincipalLogCoherence) :
    (∫ t : ℝ,
      zetaCompletedExplicitFormulaInverseGammaRightAffineKernel
        f F.toContourFamily t) =
      zetaCompletedExplicitFormulaPhi f 0 +
        zetaCompletedExplicitFormulaCorrectionRightZeroPoleVerticalInversionValue f := by
  have harch_integrable :
      Integrable
        (zetaCompletedExplicitFormulaArchimedeanRightAffineKernel
          f F.toContourFamily)
        (volume : Measure ℝ) :=
    zetaCompletedExplicitFormulaArchimedeanRightAffineKernel_integrable_ownerGammaBinetLineValue
      f F h hcoh
  have harch_value :
      (∫ t : ℝ,
        zetaCompletedExplicitFormulaArchimedeanRightAffineKernel
          f F.toContourFamily t) =
        zetaCompletedExplicitFormulaPhi f 0 :=
    zetaCompletedExplicitFormulaArchimedeanRightAffineKernel_integral_eq_phiZero_ownerGammaBinetLineCore
      f F h hcoh
  exact
    zetaCompletedExplicitFormulaInverseGammaRightAffineKernel_integral_eq_archimedeanValue_add_correctionRightValue
      f F h harch_integrable harch_value

/-- Owner analytic leaf: whole-line value of the left inverse-Gamma affine
kernel.

Proof target:
differentiate the shifted left-line Binet logarithm for `Γℝ`, pair the full
main-plus-remainder expression with the Paley-Wiener transform, and add the
left standard one-pole correction residue.  This is the one-sided value whose
subtraction of the correction left affine value gives `-Phi_f(0)`. -/
theorem zetaCompletedExplicitFormulaInverseGammaLeftAffineKernel_integral_eq_negPhiZero_add_correctionLeftValue_ownerOneSidedValues
    (f : ZetaAdmissibleFunction)
    (F : ExplicitFormulaVerticallyRegularContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F.toContourFamily)
    (hcoh : Complex.gammaBinetPrincipalLogCoherence) :
    (∫ t : ℝ,
      zetaCompletedExplicitFormulaInverseGammaLeftAffineKernel
        f F.toContourFamily t) =
      -(zetaCompletedExplicitFormulaPhi f 0) +
        (((2 * (Real.pi : ℂ) * Complex.I) *
          (-zetaCompletedExplicitFormulaPhi f (1 / 2))) * Complex.I) := by
  have harch_integrable :
      Integrable
        (zetaCompletedExplicitFormulaArchimedeanLeftAffineKernel
          f F.toContourFamily)
        (volume : Measure ℝ) :=
    zetaCompletedExplicitFormulaArchimedeanLeftAffineKernel_integrable_ownerGammaBinetLineValue
      f F h hcoh
  have harch_value :
      (∫ t : ℝ,
        zetaCompletedExplicitFormulaArchimedeanLeftAffineKernel
          f F.toContourFamily t) =
        -(zetaCompletedExplicitFormulaPhi f 0) :=
    zetaCompletedExplicitFormulaArchimedeanLeftAffineKernel_integral_eq_neg_phiZero_ownerGammaBinetLineCore
      f F h hcoh
  exact
    zetaCompletedExplicitFormulaInverseGammaLeftAffineKernel_integral_eq_archimedeanValue_add_correctionLeftValue
      f F h harch_integrable harch_value

/-- Right inverse-Gamma one-sided value in the subtraction-normalized form
consumed by the archimedean line-value owner. -/
theorem zetaCompletedExplicitFormulaInverseGammaRightAffineKernel_integral_sub_correctionRightValue_eq_phiZero_ownerOneSidedValues
    (f : ZetaAdmissibleFunction)
    (F : ExplicitFormulaVerticallyRegularContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F.toContourFamily)
    (hcoh : Complex.gammaBinetPrincipalLogCoherence) :
    (∫ t : ℝ,
      zetaCompletedExplicitFormulaInverseGammaRightAffineKernel
        f F.toContourFamily t) -
        zetaCompletedExplicitFormulaCorrectionRightZeroPoleVerticalInversionValue f =
      zetaCompletedExplicitFormulaPhi f 0 := by
  calc
    (∫ t : ℝ,
      zetaCompletedExplicitFormulaInverseGammaRightAffineKernel
        f F.toContourFamily t) -
        zetaCompletedExplicitFormulaCorrectionRightZeroPoleVerticalInversionValue f =
        (zetaCompletedExplicitFormulaPhi f 0 +
          zetaCompletedExplicitFormulaCorrectionRightZeroPoleVerticalInversionValue f) -
          zetaCompletedExplicitFormulaCorrectionRightZeroPoleVerticalInversionValue f := by
      exact congrArg
        (fun z : ℂ =>
          z - zetaCompletedExplicitFormulaCorrectionRightZeroPoleVerticalInversionValue f)
        (zetaCompletedExplicitFormulaInverseGammaRightAffineKernel_integral_eq_phiZero_add_correctionRightValue_ownerOneSidedValues
          f F h hcoh)
    _ = zetaCompletedExplicitFormulaPhi f 0 := by
      exact add_sub_cancel
        (zetaCompletedExplicitFormulaPhi f 0)
        (zetaCompletedExplicitFormulaCorrectionRightZeroPoleVerticalInversionValue f)

/-- Left inverse-Gamma one-sided value in the subtraction-normalized form
consumed by the archimedean line-value owner. -/
theorem zetaCompletedExplicitFormulaInverseGammaLeftAffineKernel_integral_sub_correctionLeftValue_eq_negPhiZero_ownerOneSidedValues
    (f : ZetaAdmissibleFunction)
    (F : ExplicitFormulaVerticallyRegularContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F.toContourFamily)
    (hcoh : Complex.gammaBinetPrincipalLogCoherence) :
    (∫ t : ℝ,
      zetaCompletedExplicitFormulaInverseGammaLeftAffineKernel
        f F.toContourFamily t) -
        (((2 * (Real.pi : ℂ) * Complex.I) *
          (-zetaCompletedExplicitFormulaPhi f (1 / 2))) * Complex.I) =
      -(zetaCompletedExplicitFormulaPhi f 0) := by
  calc
    (∫ t : ℝ,
      zetaCompletedExplicitFormulaInverseGammaLeftAffineKernel
        f F.toContourFamily t) -
        (((2 * (Real.pi : ℂ) * Complex.I) *
          (-zetaCompletedExplicitFormulaPhi f (1 / 2))) * Complex.I) =
        (-(zetaCompletedExplicitFormulaPhi f 0) +
          (((2 * (Real.pi : ℂ) * Complex.I) *
            (-zetaCompletedExplicitFormulaPhi f (1 / 2))) * Complex.I)) -
          (((2 * (Real.pi : ℂ) * Complex.I) *
            (-zetaCompletedExplicitFormulaPhi f (1 / 2))) * Complex.I) := by
      exact congrArg
        (fun z : ℂ =>
          z -
            (((2 * (Real.pi : ℂ) * Complex.I) *
              (-zetaCompletedExplicitFormulaPhi f (1 / 2))) * Complex.I))
        (zetaCompletedExplicitFormulaInverseGammaLeftAffineKernel_integral_eq_negPhiZero_add_correctionLeftValue_ownerOneSidedValues
          f F h hcoh)
    _ = -(zetaCompletedExplicitFormulaPhi f 0) := by
      exact add_sub_cancel
        (-(zetaCompletedExplicitFormulaPhi f 0))
        (((2 * (Real.pi : ℂ) * Complex.I) *
          (-zetaCompletedExplicitFormulaPhi f (1 / 2))) * Complex.I)

end ZetaAdmissibleFunction

end
end LFunctions
end Boundary
