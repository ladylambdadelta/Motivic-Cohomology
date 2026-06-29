import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaExplicitFormulaVerticalChannels.OwnerParts.InverseGammaAffineKernelEstimate
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaExplicitFormulaVerticalChannels.OwnerParts.ArchimedeanAffineValue
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaExplicitFormulaVerticalChannels.OwnerParts.LeftZeroPoleAffineInversionTransport
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaExplicitFormulaVerticalChannels.OwnerParts.OnePoleAffineInversionTransport
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaExplicitFormulaVerticalChannels.OwnerParts.OnePoleAffineKernelIntegrability
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaExplicitFormulaVerticalChannels.OwnerParts.PoleCauchyInversion
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaExplicitFormulaVerticalChannels.OwnerParts.ZeroPoleAffineKernelIntegrability

/-!
# Component normalizations for the inverse-Gamma affine kernel

This file owns the two component whole-line normalizations whose sum is the
right-minus-left inverse-Gamma completion normalization: the archimedean
logarithmic-derivative part and the elementary correction part.
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

/-- Component-normalization alias for the archimedean affine-kernel
integrability theorem owned in `ArchimedeanAffineValue`. -/
theorem zetaCompletedExplicitFormulaArchimedeanDifferenceAffineKernel_integrable_of_verticallyRegular_gammaBinet_ownerNormalization
    (f : ZetaAdmissibleFunction)
    (F : ExplicitFormulaVerticallyRegularContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F.toContourFamily)
    (hcoh : Complex.gammaBinetPrincipalLogCoherence) :
    Integrable
      (zetaCompletedExplicitFormulaArchimedeanDifferenceAffineKernel
        f F.toContourFamily)
      (volume : Measure ℝ) := by
  exact
    zetaCompletedExplicitFormulaArchimedeanDifferenceAffineKernel_integrable_of_verticallyRegular_gammaBinet_ownerAffineValue
      f F h hcoh

/-- Component-normalization alias for the archimedean affine-kernel value
theorem owned in `ArchimedeanAffineValue`. -/
theorem zetaCompletedExplicitFormulaArchimedeanDifferenceAffineKernel_integral_eq_archimedeanContribution_of_verticallyRegular_gammaBinet_ownerNormalization
    (f : ZetaAdmissibleFunction)
    (F : ExplicitFormulaVerticallyRegularContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F.toContourFamily)
    (hcoh : Complex.gammaBinetPrincipalLogCoherence) :
    (∫ t : ℝ,
      zetaCompletedExplicitFormulaArchimedeanDifferenceAffineKernel
        f F.toContourFamily t) =
      zetaCompletedExplicitFormulaArchimedeanContribution f := by
  exact
    zetaCompletedExplicitFormulaArchimedeanDifferenceAffineKernel_integral_eq_archimedeanContribution_ownerAffineValue
      f F h hcoh

/-- Owner analytic leaf: whole-line value of the archimedean part of the
right-minus-left inverse-Gamma difference kernel, bundled with the integrability
needed for additive recombination.

This theorem is not a consequence of the combined inverse-Gamma normalization;
the component value is proved by the Binet/Stirling decomposition of
`Γ'/Γ`, the Paley-Wiener decay of `Φ_f`, and the archimedean contour
normalization.  The combined theorem below may add this result to the
correction component, but must not be used to prove it.

Proof chain:
`Binet decomposition of inverseGammaCompletionLogDeriv`
`-> integrable majorants for right and left archimedean affine kernels`
`-> symmetric whole-line exhaustion`
`-> archimedean contribution normalization`. -/
theorem zetaCompletedExplicitFormulaArchimedeanDifferenceAffineKernel_integrable_and_integral_eq_archimedeanContribution_of_verticallyRegular_gammaBinet_ownerNormalization
    (f : ZetaAdmissibleFunction)
    (F : ExplicitFormulaVerticallyRegularContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F.toContourFamily)
    (hcoh : Complex.gammaBinetPrincipalLogCoherence) :
    Integrable
        (zetaCompletedExplicitFormulaArchimedeanDifferenceAffineKernel
          f F.toContourFamily)
        (volume : Measure ℝ) ∧
      (∫ t : ℝ,
        zetaCompletedExplicitFormulaArchimedeanDifferenceAffineKernel
          f F.toContourFamily t) =
        zetaCompletedExplicitFormulaArchimedeanContribution f := by
  exact
    And.intro
      (zetaCompletedExplicitFormulaArchimedeanDifferenceAffineKernel_integrable_of_verticallyRegular_gammaBinet_ownerNormalization
        f F h hcoh)
      (zetaCompletedExplicitFormulaArchimedeanDifferenceAffineKernel_integral_eq_archimedeanContribution_of_verticallyRegular_gammaBinet_ownerNormalization
        f F h hcoh)

/-- The elementary correction zero-pole difference kernel, written as a local
function so that the correction component can integrate it independently of the
one-pole part. -/
noncomputable def zetaCompletedExplicitFormulaCorrectionZeroPoleDifferenceAffineKernel
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily) :
    ℝ → ℂ :=
  fun t : ℝ =>
    zetaCompletedExplicitFormulaCorrectionRightZeroPoleAffineKernel f F t -
      zetaCompletedExplicitFormulaCorrectionLeftZeroPoleAffineKernel f F t

/-- The elementary correction one-pole difference kernel, written as a local
function so that the correction component can integrate it independently of the
zero-pole part. -/
noncomputable def zetaCompletedExplicitFormulaCorrectionOnePoleDifferenceAffineKernel
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily) :
    ℝ → ℂ :=
  fun t : ℝ =>
    zetaCompletedExplicitFormulaCorrectionRightOnePoleAffineKernel f F t -
      zetaCompletedExplicitFormulaCorrectionLeftOnePoleAffineKernel f F t

/-- Pointwise decomposition of the elementary correction difference kernel into
its zero-pole and one-pole difference pieces. -/
theorem zetaCompletedExplicitFormulaCorrectionDifferenceAffineKernel_eq_zeroPoleDifference_add_onePoleDifference
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily) (t : ℝ) :
    zetaCompletedExplicitFormulaCorrectionDifferenceAffineKernel f F t =
      zetaCompletedExplicitFormulaCorrectionZeroPoleDifferenceAffineKernel f F t +
        zetaCompletedExplicitFormulaCorrectionOnePoleDifferenceAffineKernel f F t :=
  zetaCompletedExplicitFormulaCorrectionDifferenceAffineKernel_eq_zeroPole_add_onePole
    f F t

/-- Whole-line integral splitting for the elementary correction difference
kernel.  This contains only integration algebra; the zero-pole and one-pole
normalizations remain separate analytic inputs. -/
theorem zetaCompletedExplicitFormulaCorrectionDifferenceAffineKernel_integral_eq_zeroPoleIntegral_add_onePoleIntegral
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (hzero :
      Integrable
        (zetaCompletedExplicitFormulaCorrectionZeroPoleDifferenceAffineKernel f F)
        (volume : Measure ℝ))
    (hone :
      Integrable
        (zetaCompletedExplicitFormulaCorrectionOnePoleDifferenceAffineKernel f F)
        (volume : Measure ℝ)) :
    (∫ t : ℝ,
      zetaCompletedExplicitFormulaCorrectionDifferenceAffineKernel f F t) =
      (∫ t : ℝ,
        zetaCompletedExplicitFormulaCorrectionZeroPoleDifferenceAffineKernel f F t) +
        ∫ t : ℝ,
          zetaCompletedExplicitFormulaCorrectionOnePoleDifferenceAffineKernel f F t := by
  have hpoint :
      (fun t : ℝ =>
        zetaCompletedExplicitFormulaCorrectionDifferenceAffineKernel f F t) =ᵐ[volume]
        fun t : ℝ =>
          zetaCompletedExplicitFormulaCorrectionZeroPoleDifferenceAffineKernel f F t +
            zetaCompletedExplicitFormulaCorrectionOnePoleDifferenceAffineKernel f F t :=
    Filter.Eventually.of_forall
      (fun t =>
        zetaCompletedExplicitFormulaCorrectionDifferenceAffineKernel_eq_zeroPoleDifference_add_onePoleDifference
          f F t)
  exact Eq.trans
    (integral_congr_ae hpoint)
    (integral_add hzero hone)

/-- Owner analytic leaf: integrability of the elementary zero-pole correction
difference kernel. -/
theorem zetaCompletedExplicitFormulaCorrectionZeroPoleDifferenceAffineKernel_integrable_of_verticallyRegular_ownerNormalization
    (f : ZetaAdmissibleFunction)
    (F : ExplicitFormulaVerticallyRegularContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F.toContourFamily) :
    Integrable
      (zetaCompletedExplicitFormulaCorrectionZeroPoleDifferenceAffineKernel
        f F.toContourFamily)
      (volume : Measure ℝ) := by
  have hright :
      Integrable
        (zetaCompletedExplicitFormulaCorrectionRightZeroPoleAffineKernel
          f F.toContourFamily)
        (volume : Measure ℝ) :=
    zetaCompletedExplicitFormulaCorrectionRightZeroPoleAffineKernel_integrable_ownerBounds
      f F.toContourFamily h
  have hleft :
      Integrable
        (zetaCompletedExplicitFormulaCorrectionLeftZeroPoleAffineKernel
          f F.toContourFamily)
        (volume : Measure ℝ) :=
    zetaCompletedExplicitFormulaCorrectionLeftZeroPoleAffineKernel_integrable_ownerBounds
      f F.toContourFamily h
  exact hright.sub hleft

/-- Owner analytic leaf: integrability of the elementary one-pole correction
difference kernel. -/
theorem zetaCompletedExplicitFormulaCorrectionOnePoleDifferenceAffineKernel_integrable_of_verticallyRegular_ownerNormalization
    (f : ZetaAdmissibleFunction)
    (F : ExplicitFormulaVerticallyRegularContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F.toContourFamily) :
    Integrable
      (zetaCompletedExplicitFormulaCorrectionOnePoleDifferenceAffineKernel
        f F.toContourFamily)
      (volume : Measure ℝ) := by
  have hright :
      Integrable
        (zetaCompletedExplicitFormulaCorrectionRightOnePoleAffineKernel
          f F.toContourFamily)
        (volume : Measure ℝ) :=
    zetaCompletedExplicitFormulaCorrectionRightOnePoleAffineKernel_integrable_ownerBounds
      f F.toContourFamily h
  have hleft :
      Integrable
        (zetaCompletedExplicitFormulaCorrectionLeftOnePoleAffineKernel
          f F.toContourFamily)
        (volume : Measure ℝ) :=
    zetaCompletedExplicitFormulaCorrectionLeftOnePoleAffineKernel_integrable_ownerBounds
      f F.toContourFamily h
  exact hright.sub hleft

/-- Owner analytic leaf: integrability of the elementary correction
right-minus-left affine kernel.

This should be proved by decomposing
`explicitFormulaCorrectionLogDerivative s = -1 / s - 1 / (s - 1)` into the
zero-pole and one-pole affine kernels via
`zetaCompletedExplicitFormulaCorrectionDifferenceAffineKernel_eq_zeroPole_add_onePole`,
proving each pole kernel integrable by the Cauchy-kernel majorant estimates,
and recombining with `Integrable.sub` and `Integrable.add`. -/
theorem zetaCompletedExplicitFormulaCorrectionDifferenceAffineKernel_integrable_of_verticallyRegular_gammaBinet_ownerNormalization
    (f : ZetaAdmissibleFunction)
    (F : ExplicitFormulaVerticallyRegularContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F.toContourFamily)
    (hcoh : Complex.gammaBinetPrincipalLogCoherence) :
    Integrable
      (zetaCompletedExplicitFormulaCorrectionDifferenceAffineKernel
        f F.toContourFamily)
      (volume : Measure ℝ) := by
  have hzero :
      Integrable
        (zetaCompletedExplicitFormulaCorrectionZeroPoleDifferenceAffineKernel
          f F.toContourFamily)
        (volume : Measure ℝ) :=
    zetaCompletedExplicitFormulaCorrectionZeroPoleDifferenceAffineKernel_integrable_of_verticallyRegular_ownerNormalization
      f F h
  have hone :
      Integrable
        (zetaCompletedExplicitFormulaCorrectionOnePoleDifferenceAffineKernel
          f F.toContourFamily)
        (volume : Measure ℝ) :=
    zetaCompletedExplicitFormulaCorrectionOnePoleDifferenceAffineKernel_integrable_of_verticallyRegular_ownerNormalization
      f F h
  have hsum :
      Integrable
        (fun t : ℝ =>
          zetaCompletedExplicitFormulaCorrectionZeroPoleDifferenceAffineKernel
            f F.toContourFamily t +
            zetaCompletedExplicitFormulaCorrectionOnePoleDifferenceAffineKernel
              f F.toContourFamily t)
        (volume : Measure ℝ) :=
    hzero.add hone
  have hpoint :
      (fun t : ℝ =>
        zetaCompletedExplicitFormulaCorrectionDifferenceAffineKernel
          f F.toContourFamily t) =ᵐ[volume]
        fun t : ℝ =>
          zetaCompletedExplicitFormulaCorrectionZeroPoleDifferenceAffineKernel
            f F.toContourFamily t +
            zetaCompletedExplicitFormulaCorrectionOnePoleDifferenceAffineKernel
              f F.toContourFamily t :=
    Filter.Eventually.of_forall
      (fun t =>
        zetaCompletedExplicitFormulaCorrectionDifferenceAffineKernel_eq_zeroPoleDifference_add_onePoleDifference
          f F.toContourFamily t)
  exact hsum.congr hpoint.symm

/-- Owner analytic leaf: whole-line value of the elementary zero-pole
correction difference kernel. -/
theorem zetaCompletedExplicitFormulaCorrectionZeroPoleDifferenceAffineKernel_integral_eq_zeroPoleContribution_of_verticallyRegular_ownerNormalization
    (f : ZetaAdmissibleFunction)
    (F : ExplicitFormulaVerticallyRegularContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F.toContourFamily) :
    (∫ t : ℝ,
      zetaCompletedExplicitFormulaCorrectionZeroPoleDifferenceAffineKernel
        f F.toContourFamily t) =
      zetaCompletedExplicitFormulaCorrectionRightZeroPoleVerticalInversionValue f := by
  have hright_int :
      Integrable
        (zetaCompletedExplicitFormulaCorrectionRightZeroPoleAffineKernel
          f F.toContourFamily)
        (volume : Measure ℝ) :=
    zetaCompletedExplicitFormulaCorrectionRightZeroPoleAffineKernel_integrable_ownerBounds
      f F.toContourFamily h
  have hleft_int :
      Integrable
        (zetaCompletedExplicitFormulaCorrectionLeftZeroPoleAffineKernel
          f F.toContourFamily)
        (volume : Measure ℝ) :=
    zetaCompletedExplicitFormulaCorrectionLeftZeroPoleAffineKernel_integrable_ownerBounds
      f F.toContourFamily h
  have hsplit :
      (∫ t : ℝ,
        zetaCompletedExplicitFormulaCorrectionZeroPoleDifferenceAffineKernel
          f F.toContourFamily t) =
        (∫ t : ℝ,
          zetaCompletedExplicitFormulaCorrectionRightZeroPoleAffineKernel
            f F.toContourFamily t) -
          ∫ t : ℝ,
            zetaCompletedExplicitFormulaCorrectionLeftZeroPoleAffineKernel
              f F.toContourFamily t :=
    integral_sub hright_int hleft_int
  have hright_value :
      (∫ t : ℝ,
        zetaCompletedExplicitFormulaCorrectionRightZeroPoleAffineKernel
          f F.toContourFamily t) =
        zetaCompletedExplicitFormulaCorrectionRightZeroPoleVerticalInversionValue f :=
    zetaCompletedExplicitFormulaCorrectionRightZeroPoleAffineKernel_integral_eq_value_ownerCauchyInversion
      f F.toContourFamily h
  have hleft_value :
      (∫ t : ℝ,
        zetaCompletedExplicitFormulaCorrectionLeftZeroPoleAffineKernel
          f F.toContourFamily t) =
        0 :=
    zetaCompletedExplicitFormulaCorrectionLeftZeroPoleAffineKernel_integral_eq_zero_ownerTransport
      f F.toContourFamily h
  calc
    (∫ t : ℝ,
      zetaCompletedExplicitFormulaCorrectionZeroPoleDifferenceAffineKernel
        f F.toContourFamily t) =
        (∫ t : ℝ,
          zetaCompletedExplicitFormulaCorrectionRightZeroPoleAffineKernel
            f F.toContourFamily t) -
          ∫ t : ℝ,
            zetaCompletedExplicitFormulaCorrectionLeftZeroPoleAffineKernel
              f F.toContourFamily t := hsplit
    _ =
        zetaCompletedExplicitFormulaCorrectionRightZeroPoleVerticalInversionValue f -
          ∫ t : ℝ,
            zetaCompletedExplicitFormulaCorrectionLeftZeroPoleAffineKernel
              f F.toContourFamily t := by
        exact congrArg
          (fun z : ℂ =>
            z -
              ∫ t : ℝ,
                zetaCompletedExplicitFormulaCorrectionLeftZeroPoleAffineKernel
                  f F.toContourFamily t)
          hright_value
    _ =
        zetaCompletedExplicitFormulaCorrectionRightZeroPoleVerticalInversionValue f -
          0 := by
        exact congrArg
          (fun z : ℂ =>
            zetaCompletedExplicitFormulaCorrectionRightZeroPoleVerticalInversionValue f - z)
          hleft_value
    _ =
        zetaCompletedExplicitFormulaCorrectionRightZeroPoleVerticalInversionValue f := by
        exact sub_zero
          (zetaCompletedExplicitFormulaCorrectionRightZeroPoleVerticalInversionValue f)

/-- Owner analytic leaf: whole-line value of the elementary one-pole
correction difference kernel. -/
theorem zetaCompletedExplicitFormulaCorrectionOnePoleDifferenceAffineKernel_integral_eq_onePoleContribution_of_verticallyRegular_ownerNormalization
    (f : ZetaAdmissibleFunction)
    (F : ExplicitFormulaVerticallyRegularContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F.toContourFamily) :
    (∫ t : ℝ,
      zetaCompletedExplicitFormulaCorrectionOnePoleDifferenceAffineKernel
        f F.toContourFamily t) =
      -(((2 * (Real.pi : ℂ) * Complex.I) *
        (-zetaCompletedExplicitFormulaPhi f (1 / 2))) * Complex.I) := by
  let B : ℂ :=
    ((2 * (Real.pi : ℂ) * Complex.I) *
      (-zetaCompletedExplicitFormulaPhi f (1 / 2))) * Complex.I
  have hright_int :
      Integrable
        (zetaCompletedExplicitFormulaCorrectionRightOnePoleAffineKernel
          f F.toContourFamily)
        (volume : Measure ℝ) :=
    zetaCompletedExplicitFormulaCorrectionRightOnePoleAffineKernel_integrable_ownerBounds
      f F.toContourFamily h
  have hleft_int :
      Integrable
        (zetaCompletedExplicitFormulaCorrectionLeftOnePoleAffineKernel
          f F.toContourFamily)
        (volume : Measure ℝ) :=
    zetaCompletedExplicitFormulaCorrectionLeftOnePoleAffineKernel_integrable_ownerBounds
      f F.toContourFamily h
  have hsplit :
      (∫ t : ℝ,
        zetaCompletedExplicitFormulaCorrectionOnePoleDifferenceAffineKernel
          f F.toContourFamily t) =
        (∫ t : ℝ,
          zetaCompletedExplicitFormulaCorrectionRightOnePoleAffineKernel
            f F.toContourFamily t) -
          ∫ t : ℝ,
            zetaCompletedExplicitFormulaCorrectionLeftOnePoleAffineKernel
              f F.toContourFamily t :=
    integral_sub hright_int hleft_int
  have hright_value :
      (∫ t : ℝ,
        zetaCompletedExplicitFormulaCorrectionRightOnePoleAffineKernel
          f F.toContourFamily t) =
        0 :=
    zetaCompletedExplicitFormulaCorrectionRightOnePoleAffineKernel_integral_eq_zero_ownerTransport
      f F.toContourFamily h
  have hleft_value :
      (∫ t : ℝ,
        zetaCompletedExplicitFormulaCorrectionLeftOnePoleAffineKernel
          f F.toContourFamily t) =
        B :=
    zetaCompletedExplicitFormulaCorrectionLeftOnePoleAffineKernel_integral_eq_standardResidue_ownerTransport
      f F.toContourFamily h
  calc
    (∫ t : ℝ,
      zetaCompletedExplicitFormulaCorrectionOnePoleDifferenceAffineKernel
        f F.toContourFamily t) =
        (∫ t : ℝ,
          zetaCompletedExplicitFormulaCorrectionRightOnePoleAffineKernel
            f F.toContourFamily t) -
          ∫ t : ℝ,
            zetaCompletedExplicitFormulaCorrectionLeftOnePoleAffineKernel
              f F.toContourFamily t := hsplit
    _ =
        0 -
          ∫ t : ℝ,
            zetaCompletedExplicitFormulaCorrectionLeftOnePoleAffineKernel
              f F.toContourFamily t := by
        exact congrArg
          (fun z : ℂ =>
            z -
              ∫ t : ℝ,
                zetaCompletedExplicitFormulaCorrectionLeftOnePoleAffineKernel
                  f F.toContourFamily t)
          hright_value
    _ = 0 - B := by
        exact congrArg
          (fun z : ℂ => 0 - z)
          hleft_value
    _ = -B := by
        exact zero_sub B
    _ =
        -(((2 * (Real.pi : ℂ) * Complex.I) *
          (-zetaCompletedExplicitFormulaPhi f (1 / 2))) * Complex.I) := by
        rfl

/-- Owner assembly theorem: whole-line value of the elementary correction
right-minus-left affine kernel.

This is the value half of the correction component normalization.  Its proof
combines
`zetaCompletedExplicitFormulaCorrectionRightZeroPoleAffineKernel_integral_eq_value_ownerCauchyInversion`,
the left/right `s = 1` pole residue normalization, and the explicit
standard-contour correction definition. -/
theorem zetaCompletedExplicitFormulaCorrectionDifferenceAffineKernel_integral_eq_correctionContribution_of_verticallyRegular_gammaBinet_ownerNormalization
    (f : ZetaAdmissibleFunction)
    (F : ExplicitFormulaVerticallyRegularContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F.toContourFamily)
    (hcoh : Complex.gammaBinetPrincipalLogCoherence) :
    (∫ t : ℝ,
      zetaCompletedExplicitFormulaCorrectionDifferenceAffineKernel
        f F.toContourFamily t) =
      zetaCompletedExplicitFormulaCorrectionStandardContourContribution f := by
  have hzero_int :
      Integrable
        (zetaCompletedExplicitFormulaCorrectionZeroPoleDifferenceAffineKernel
          f F.toContourFamily)
        (volume : Measure ℝ) :=
    zetaCompletedExplicitFormulaCorrectionZeroPoleDifferenceAffineKernel_integrable_of_verticallyRegular_ownerNormalization
      f F h
  have hone_int :
      Integrable
        (zetaCompletedExplicitFormulaCorrectionOnePoleDifferenceAffineKernel
          f F.toContourFamily)
        (volume : Measure ℝ) :=
    zetaCompletedExplicitFormulaCorrectionOnePoleDifferenceAffineKernel_integrable_of_verticallyRegular_ownerNormalization
      f F h
  have hsplit :
      (∫ t : ℝ,
        zetaCompletedExplicitFormulaCorrectionDifferenceAffineKernel
          f F.toContourFamily t) =
        (∫ t : ℝ,
          zetaCompletedExplicitFormulaCorrectionZeroPoleDifferenceAffineKernel
            f F.toContourFamily t) +
          ∫ t : ℝ,
            zetaCompletedExplicitFormulaCorrectionOnePoleDifferenceAffineKernel
              f F.toContourFamily t :=
    zetaCompletedExplicitFormulaCorrectionDifferenceAffineKernel_integral_eq_zeroPoleIntegral_add_onePoleIntegral
      f F.toContourFamily hzero_int hone_int
  have hzero_value :
      (∫ t : ℝ,
        zetaCompletedExplicitFormulaCorrectionZeroPoleDifferenceAffineKernel
          f F.toContourFamily t) =
        zetaCompletedExplicitFormulaCorrectionRightZeroPoleVerticalInversionValue f :=
    zetaCompletedExplicitFormulaCorrectionZeroPoleDifferenceAffineKernel_integral_eq_zeroPoleContribution_of_verticallyRegular_ownerNormalization
      f F h
  have hzero_unfold :
      zetaCompletedExplicitFormulaCorrectionRightZeroPoleVerticalInversionValue f =
        -(((2 * (Real.pi : ℂ) * Complex.I) *
          (-zetaCompletedExplicitFormulaPhi f (-(1 / 2 : ℂ)))) * Complex.I) :=
    zetaCompletedExplicitFormulaCorrectionRightZeroPoleVerticalInversionValue_eq f
  have hone_value :
      (∫ t : ℝ,
        zetaCompletedExplicitFormulaCorrectionOnePoleDifferenceAffineKernel
          f F.toContourFamily t) =
        -(((2 * (Real.pi : ℂ) * Complex.I) *
          (-zetaCompletedExplicitFormulaPhi f (1 / 2))) * Complex.I) :=
    zetaCompletedExplicitFormulaCorrectionOnePoleDifferenceAffineKernel_integral_eq_onePoleContribution_of_verticallyRegular_ownerNormalization
      f F h
  have hsum :
      (∫ t : ℝ,
        zetaCompletedExplicitFormulaCorrectionZeroPoleDifferenceAffineKernel
          f F.toContourFamily t) +
          ∫ t : ℝ,
            zetaCompletedExplicitFormulaCorrectionOnePoleDifferenceAffineKernel
              f F.toContourFamily t =
        zetaCompletedExplicitFormulaCorrectionStandardContourContribution f := by
    calc
      (∫ t : ℝ,
        zetaCompletedExplicitFormulaCorrectionZeroPoleDifferenceAffineKernel
          f F.toContourFamily t) +
          ∫ t : ℝ,
            zetaCompletedExplicitFormulaCorrectionOnePoleDifferenceAffineKernel
              f F.toContourFamily t =
          zetaCompletedExplicitFormulaCorrectionRightZeroPoleVerticalInversionValue f +
            -(((2 * (Real.pi : ℂ) * Complex.I) *
              (-zetaCompletedExplicitFormulaPhi f (1 / 2))) * Complex.I) := by
        exact congrArg₂ HAdd.hAdd hzero_value hone_value
      _ =
          zetaCompletedExplicitFormulaCorrectionRightZeroPoleVerticalInversionValue f -
            (((2 * (Real.pi : ℂ) * Complex.I) *
              (-zetaCompletedExplicitFormulaPhi f (1 / 2))) * Complex.I) := by
        exact (sub_eq_add_neg
          (zetaCompletedExplicitFormulaCorrectionRightZeroPoleVerticalInversionValue f)
          (((2 * (Real.pi : ℂ) * Complex.I) *
            (-zetaCompletedExplicitFormulaPhi f (1 / 2))) * Complex.I)).symm
      _ =
          -(((2 * (Real.pi : ℂ) * Complex.I) *
            (-zetaCompletedExplicitFormulaPhi f (-(1 / 2 : ℂ)))) * Complex.I) -
            (((2 * (Real.pi : ℂ) * Complex.I) *
              (-zetaCompletedExplicitFormulaPhi f (1 / 2))) * Complex.I) := by
        exact congrArg
          (fun z : ℂ =>
            z -
              (((2 * (Real.pi : ℂ) * Complex.I) *
                (-zetaCompletedExplicitFormulaPhi f (1 / 2))) * Complex.I))
          hzero_unfold
      _ = zetaCompletedExplicitFormulaCorrectionStandardContourContribution f := by
        exact (zetaCompletedExplicitFormulaCorrectionStandardContourContribution_eq f).symm
  exact Eq.trans hsplit hsum

/-- Owner assembly theorem: whole-line value of the elementary correction part of
the right-minus-left inverse-Gamma difference kernel, bundled with the
integrability needed for additive recombination.

The proof assembles the already separated `s = 0` and `s = 1` pole-face
residue values, then
identify their difference with
`zetaCompletedExplicitFormulaCorrectionStandardContourContribution`.  It is
not an analytic remainder estimate and must not depend on the downstream
combined archimedean transport.

Proof chain:
`right zero-pole Cauchy inversion`
`+ left one-pole residue normalization`
`-> elementary correction affine-kernel integrability`
`-> standard-contour correction contribution`. -/
theorem zetaCompletedExplicitFormulaCorrectionDifferenceAffineKernel_integrable_and_integral_eq_correctionContribution_of_verticallyRegular_gammaBinet_ownerNormalization
    (f : ZetaAdmissibleFunction)
    (F : ExplicitFormulaVerticallyRegularContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F.toContourFamily)
    (hcoh : Complex.gammaBinetPrincipalLogCoherence) :
    Integrable
        (zetaCompletedExplicitFormulaCorrectionDifferenceAffineKernel
          f F.toContourFamily)
        (volume : Measure ℝ) ∧
      (∫ t : ℝ,
        zetaCompletedExplicitFormulaCorrectionDifferenceAffineKernel
          f F.toContourFamily t) =
        zetaCompletedExplicitFormulaCorrectionStandardContourContribution f := by
  exact
    And.intro
      (zetaCompletedExplicitFormulaCorrectionDifferenceAffineKernel_integrable_of_verticallyRegular_gammaBinet_ownerNormalization
        f F h hcoh)
      (zetaCompletedExplicitFormulaCorrectionDifferenceAffineKernel_integral_eq_correctionContribution_of_verticallyRegular_gammaBinet_ownerNormalization
        f F h hcoh)

end ZetaAdmissibleFunction

end
end LFunctions
end Boundary
