import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaZeroKreinGram.WeilCriterion.OwnerParts.PolynomialPhysicalBoundaryTransports
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaZeroKreinGram.WeilCriterion.OwnerParts.CompletedAffineScheduledPolynomialLimit
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaExplicitFormulaVerticalChannels.OwnerParts.AutocorrelationPrimeNormalization

/-!
# Boundary identification from scheduled Cauchy path data

This owner part peels the Cauchy-data boundary-identification sink into the
affine-kernel facts that remain to be proved: right integrability, left
integrability, and the completed affine full-line value.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open Filter
open MeasureTheory
open scoped Topology

theorem zetaWeilAutocorrelationBoundaryIdentification_of_canonicalScheduledCauchyPathData_affineKernelIntegrableValue_owner
    (K : ZetaAdmissibleFunction → ℕ)
    (zetaData :
      ∀ f : ZetaAdmissibleFunction,
        ZetaAdmissibleFunction.CanonicalScheduledZetaSideCauchyPathData
          f (K f))
    (gammaData :
      ∀ f : ZetaAdmissibleFunction,
        ZetaAdmissibleFunction.CanonicalScheduledInverseGammaCauchyPathData
          f (K f))
    (rightIntegrable :
      ∀ f : ZetaAdmissibleFunction,
        Integrable
          (ZetaAdmissibleFunction.zetaCompletedRightAffineKernel
            (ZetaAdmissibleFunction.convolutionAutocorrelation f)
            (ZetaAdmissibleFunction.zetaCompletedExplicitFormula_autocorrelation_contourFamily f))
          (volume : Measure ℝ))
    (leftIntegrable :
      ∀ f : ZetaAdmissibleFunction,
        Integrable
          (ZetaAdmissibleFunction.zetaCompletedLeftAffineKernel
            (ZetaAdmissibleFunction.convolutionAutocorrelation f)
            (ZetaAdmissibleFunction.zetaCompletedExplicitFormula_autocorrelation_contourFamily f))
          (volume : Measure ℝ))
    (valueEquality :
      ∀ f : ZetaAdmissibleFunction,
        (∫ t : ℝ,
            ZetaAdmissibleFunction.zetaCompletedRightAffineKernel
              (ZetaAdmissibleFunction.convolutionAutocorrelation f)
              (ZetaAdmissibleFunction.zetaCompletedExplicitFormula_autocorrelation_contourFamily f)
              t) -
          (∫ t : ℝ,
            ZetaAdmissibleFunction.zetaCompletedLeftAffineKernel
              (ZetaAdmissibleFunction.convolutionAutocorrelation f)
              (ZetaAdmissibleFunction.zetaCompletedExplicitFormula_autocorrelation_contourFamily f)
              t) =
            ZetaAdmissibleFunction.explicitFormulaTwoPi *
              zetaCompletedAffinePhysicalBoundaryChannel
                (ZetaAdmissibleFunction.convolutionAutocorrelation f)) :
    ZetaWeilAutocorrelationBoundaryIdentification :=
  let hPolynomial :
      ∀ f : ZetaAdmissibleFunction,
        ZetaAdmissibleFunction.ExplicitFormulaScheduledPolynomialFamilyAnalyticPackage
          (ZetaAdmissibleFunction.convolutionAutocorrelation f)
          (ZetaAdmissibleFunction.zetaCompletedExplicitFormula_autocorrelation_contourFamily f) :=
    fun f =>
      ZetaAdmissibleFunction.zetaCompletedExplicitFormulaAutocorrelationScheduledPolynomialFamilyAnalyticPackage_of_cauchyPathData
        f (K f) (zetaData f) (gammaData f)
  zetaWeilAutocorrelationBoundaryIdentification_of_canonicalScheduledCauchyPathData_affineChannelLimit_owner
    K
    zetaData
    gammaData
    (fun f =>
      ZetaAdmissibleFunction.zetaCompletedAutocorrelationPolynomialScheduledAffineVerticalChannel_tendsto_physical_of_integrable_value
        f
        (hPolynomial f)
        (rightIntegrable f)
        (leftIntegrable f)
        (valueEquality f))

theorem zetaWeilAutocorrelationBoundaryIdentification_of_canonicalScheduledCauchyPathData_componentAffineValue_owner
    (K : ZetaAdmissibleFunction → ℕ)
    (zetaData :
      ∀ f : ZetaAdmissibleFunction,
        ZetaAdmissibleFunction.CanonicalScheduledZetaSideCauchyPathData
          f (K f))
    (gammaData :
      ∀ f : ZetaAdmissibleFunction,
        ZetaAdmissibleFunction.CanonicalScheduledInverseGammaCauchyPathData
          f (K f))
    (rightPrimeIntegrable :
      ∀ f : ZetaAdmissibleFunction,
        Integrable
          (ZetaAdmissibleFunction.zetaCompletedExplicitFormulaPrimeRightVonMangoldtAffineKernel
            (ZetaAdmissibleFunction.convolutionAutocorrelation f)
            (ZetaAdmissibleFunction.zetaCompletedExplicitFormula_autocorrelation_contourFamily f))
          (volume : Measure ℝ))
    (rightInverseGammaIntegrable :
      ∀ f : ZetaAdmissibleFunction,
        Integrable
          (ZetaAdmissibleFunction.zetaCompletedExplicitFormulaInverseGammaRightAffineKernel
            (ZetaAdmissibleFunction.convolutionAutocorrelation f)
            (ZetaAdmissibleFunction.zetaCompletedExplicitFormula_autocorrelation_contourFamily f))
          (volume : Measure ℝ))
    (leftReflectedIntegrable :
      ∀ f : ZetaAdmissibleFunction,
        Integrable
          (ZetaAdmissibleFunction.zetaCompletedExplicitFormulaPrimeLeftReflectedCompletedAffineKernel
            (ZetaAdmissibleFunction.convolutionAutocorrelation f)
            (ZetaAdmissibleFunction.zetaCompletedExplicitFormula_autocorrelation_contourFamily f))
          (volume : Measure ℝ))
    (arithmeticValue archimedeanValue :
      ZetaAdmissibleFunction → ℂ)
    (packetValue :
      ∀ f : ZetaAdmissibleFunction,
        (∫ t : ℝ,
            ZetaAdmissibleFunction.zetaCompletedRightAffineKernel
              (ZetaAdmissibleFunction.convolutionAutocorrelation f)
              (ZetaAdmissibleFunction.zetaCompletedExplicitFormula_autocorrelation_contourFamily f)
              t) -
          (∫ t : ℝ,
            ZetaAdmissibleFunction.zetaCompletedLeftAffineKernel
              (ZetaAdmissibleFunction.convolutionAutocorrelation f)
              (ZetaAdmissibleFunction.zetaCompletedExplicitFormula_autocorrelation_contourFamily f)
              t) =
          arithmeticValue f + archimedeanValue f)
    (arithmeticDivision :
      ∀ f : ZetaAdmissibleFunction,
        arithmeticValue f / ZetaAdmissibleFunction.explicitFormulaTwoPi =
          ZetaAdmissibleFunction.zetaCompletedExplicitFormulaPrimeContribution
            (ZetaAdmissibleFunction.convolutionAutocorrelation f))
    (boundaryEquality :
      ∀ f : ZetaAdmissibleFunction,
        zetaCompletedAffinePhysicalBoundaryChannel
            (ZetaAdmissibleFunction.convolutionAutocorrelation f) =
          ZetaAdmissibleFunction.zetaCompletedExplicitFormulaPrimeContribution
              (ZetaAdmissibleFunction.convolutionAutocorrelation f) +
            archimedeanValue f /
              ZetaAdmissibleFunction.explicitFormulaTwoPi) :
    ZetaWeilAutocorrelationBoundaryIdentification :=
  zetaWeilAutocorrelationBoundaryIdentification_of_canonicalScheduledCauchyPathData_affineKernelIntegrableValue_owner
    K
    zetaData
    gammaData
    (fun f =>
      ZetaAdmissibleFunction.zetaCompletedAutocorrelationRightAffineKernel_integrable_of_component_integrable_owner
        f
        (rightPrimeIntegrable f)
        (rightInverseGammaIntegrable f))
    (fun f =>
      ZetaAdmissibleFunction.zetaCompletedAutocorrelationLeftAffineKernel_integrable_of_reflected_integrable_owner
        f
        (leftReflectedIntegrable f))
    (fun f =>
      ZetaAdmissibleFunction.zetaCompletedAutocorrelationAffineKernel_integral_eq_physical_of_packet_value_owner
        f
        (arithmeticValue f)
        (archimedeanValue f)
        (packetValue f)
        (arithmeticDivision f)
        (boundaryEquality f))

theorem zetaWeilAutocorrelationBoundaryIdentification_of_canonicalScheduledCauchyPathData_componentPacketValue_owner
    (K : ZetaAdmissibleFunction → ℕ)
    (zetaData :
      ∀ f : ZetaAdmissibleFunction,
        ZetaAdmissibleFunction.CanonicalScheduledZetaSideCauchyPathData
          f (K f))
    (gammaData :
      ∀ f : ZetaAdmissibleFunction,
        ZetaAdmissibleFunction.CanonicalScheduledInverseGammaCauchyPathData
          f (K f))
    (rightPrimeIntegrable :
      ∀ f : ZetaAdmissibleFunction,
        Integrable
          (ZetaAdmissibleFunction.zetaCompletedExplicitFormulaPrimeRightVonMangoldtAffineKernel
            (ZetaAdmissibleFunction.convolutionAutocorrelation f)
            (ZetaAdmissibleFunction.zetaCompletedExplicitFormula_autocorrelation_contourFamily f))
          (volume : Measure ℝ))
    (rightInverseGammaIntegrable :
      ∀ f : ZetaAdmissibleFunction,
        Integrable
          (ZetaAdmissibleFunction.zetaCompletedExplicitFormulaInverseGammaRightAffineKernel
            (ZetaAdmissibleFunction.convolutionAutocorrelation f)
            (ZetaAdmissibleFunction.zetaCompletedExplicitFormula_autocorrelation_contourFamily f))
          (volume : Measure ℝ))
    (leftReflectedIntegrable :
      ∀ f : ZetaAdmissibleFunction,
        Integrable
          (ZetaAdmissibleFunction.zetaCompletedExplicitFormulaPrimeLeftReflectedCompletedAffineKernel
            (ZetaAdmissibleFunction.convolutionAutocorrelation f)
            (ZetaAdmissibleFunction.zetaCompletedExplicitFormula_autocorrelation_contourFamily f))
          (volume : Measure ℝ))
    (arithmeticValue :
      ZetaAdmissibleFunction → ℂ)
    (packetDecomposition :
      ∀ f : ZetaAdmissibleFunction,
        (∫ t : ℝ,
            ZetaAdmissibleFunction.zetaCompletedRightAffineKernel
              (ZetaAdmissibleFunction.convolutionAutocorrelation f)
              (ZetaAdmissibleFunction.zetaCompletedExplicitFormula_autocorrelation_contourFamily f)
              t) -
          (∫ t : ℝ,
            ZetaAdmissibleFunction.zetaCompletedLeftAffineKernel
              (ZetaAdmissibleFunction.convolutionAutocorrelation f)
              (ZetaAdmissibleFunction.zetaCompletedExplicitFormula_autocorrelation_contourFamily f)
              t) =
          ((∫ t : ℝ,
              ZetaAdmissibleFunction.zetaCompletedExplicitFormulaPrimeRightVonMangoldtAffineKernel
                (ZetaAdmissibleFunction.convolutionAutocorrelation f)
                (ZetaAdmissibleFunction.zetaCompletedExplicitFormula_autocorrelation_contourFamily f)
                t) -
            ∑' n : ℕ,
              ∫ t : ℝ,
                ZetaAdmissibleFunction.zetaCompletedExplicitFormulaPrimeLeftReflectedTermKernel
                  (ZetaAdmissibleFunction.convolutionAutocorrelation f)
                  (ZetaAdmissibleFunction.zetaCompletedExplicitFormula_autocorrelation_contourFamily f)
                  n t) +
          ((∫ t : ℝ,
              ZetaAdmissibleFunction.zetaCompletedExplicitFormulaInverseGammaRightAffineKernel
                (ZetaAdmissibleFunction.convolutionAutocorrelation f)
                (ZetaAdmissibleFunction.zetaCompletedExplicitFormula_autocorrelation_contourFamily f)
                t) -
            ∫ t : ℝ,
              ZetaAdmissibleFunction.zetaCompletedExplicitFormulaPrimeLeftReflectedInverseGammaKernel
                (ZetaAdmissibleFunction.convolutionAutocorrelation f)
                (ZetaAdmissibleFunction.zetaCompletedExplicitFormula_autocorrelation_contourFamily f)
                t))
    (arithmeticEquality :
      ∀ f : ZetaAdmissibleFunction,
        ((∫ t : ℝ,
            ZetaAdmissibleFunction.zetaCompletedExplicitFormulaPrimeRightVonMangoldtAffineKernel
              (ZetaAdmissibleFunction.convolutionAutocorrelation f)
              (ZetaAdmissibleFunction.zetaCompletedExplicitFormula_autocorrelation_contourFamily f)
              t) -
          ∑' n : ℕ,
            ∫ t : ℝ,
              ZetaAdmissibleFunction.zetaCompletedExplicitFormulaPrimeLeftReflectedTermKernel
                (ZetaAdmissibleFunction.convolutionAutocorrelation f)
                (ZetaAdmissibleFunction.zetaCompletedExplicitFormula_autocorrelation_contourFamily f)
                n t) =
          arithmeticValue f)
    (differenceIntegral :
      ∀ f : ZetaAdmissibleFunction,
        (∫ t : ℝ,
          ZetaAdmissibleFunction.zetaCompletedAffineInverseGammaRightReflectedDifferenceKernel
            (ZetaAdmissibleFunction.convolutionAutocorrelation f)
            (ZetaAdmissibleFunction.zetaCompletedExplicitFormula_autocorrelation_contourFamily f)
            t) =
          (∫ t : ℝ,
            ZetaAdmissibleFunction.zetaCompletedExplicitFormulaInverseGammaRightAffineKernel
              (ZetaAdmissibleFunction.convolutionAutocorrelation f)
              (ZetaAdmissibleFunction.zetaCompletedExplicitFormula_autocorrelation_contourFamily f)
              t) -
            ∫ t : ℝ,
              ZetaAdmissibleFunction.zetaCompletedExplicitFormulaPrimeLeftReflectedInverseGammaKernel
                (ZetaAdmissibleFunction.convolutionAutocorrelation f)
                (ZetaAdmissibleFunction.zetaCompletedExplicitFormula_autocorrelation_contourFamily f)
                t)
    (archimedeanValue :
      ∀ f : ZetaAdmissibleFunction,
        (∫ t : ℝ,
          ZetaAdmissibleFunction.zetaCompletedAffineInverseGammaRightReflectedDifferenceKernel
            (ZetaAdmissibleFunction.convolutionAutocorrelation f)
            (ZetaAdmissibleFunction.zetaCompletedExplicitFormula_autocorrelation_contourFamily f)
            t) =
          ZetaAdmissibleFunction.zetaCompletedExplicitFormulaHermitianArchimedeanContribution
            (ZetaAdmissibleFunction.convolutionAutocorrelation f))
    (arithmeticDivision :
      ∀ f : ZetaAdmissibleFunction,
        arithmeticValue f / ZetaAdmissibleFunction.explicitFormulaTwoPi =
          ZetaAdmissibleFunction.zetaCompletedExplicitFormulaPrimeContribution
            (ZetaAdmissibleFunction.convolutionAutocorrelation f))
    (boundaryEquality :
      ∀ f : ZetaAdmissibleFunction,
        zetaCompletedAffinePhysicalBoundaryChannel
            (ZetaAdmissibleFunction.convolutionAutocorrelation f) =
          ZetaAdmissibleFunction.zetaCompletedExplicitFormulaPrimeContribution
              (ZetaAdmissibleFunction.convolutionAutocorrelation f) +
            ZetaAdmissibleFunction.zetaCompletedExplicitFormulaHermitianArchimedeanContribution
                (ZetaAdmissibleFunction.convolutionAutocorrelation f) /
              ZetaAdmissibleFunction.explicitFormulaTwoPi) :
    ZetaWeilAutocorrelationBoundaryIdentification :=
  zetaWeilAutocorrelationBoundaryIdentification_of_canonicalScheduledCauchyPathData_componentAffineValue_owner
    K
    zetaData
    gammaData
    rightPrimeIntegrable
    rightInverseGammaIntegrable
    leftReflectedIntegrable
    arithmeticValue
    (fun f =>
      ZetaAdmissibleFunction.zetaCompletedExplicitFormulaHermitianArchimedeanContribution
        (ZetaAdmissibleFunction.convolutionAutocorrelation f))
    (fun f =>
      ZetaAdmissibleFunction.zetaCompletedAutocorrelationAffineKernel_packet_value_of_component_values_owner
        f
        (arithmeticValue f)
        (ZetaAdmissibleFunction.zetaCompletedExplicitFormulaHermitianArchimedeanContribution
          (ZetaAdmissibleFunction.convolutionAutocorrelation f))
        (packetDecomposition f)
        (arithmeticEquality f)
        (ZetaAdmissibleFunction.zetaCompletedAutocorrelationInverseGamma_packet_value_of_difference_kernel_value_owner
          f
          (differenceIntegral f)
          (archimedeanValue f)))
    arithmeticDivision
    boundaryEquality

theorem zetaWeilAutocorrelationBoundaryIdentification_of_canonicalScheduledCauchyPathData_canonicalPacketValue_owner
    (K : ZetaAdmissibleFunction → ℕ)
    (zetaData :
      ∀ f : ZetaAdmissibleFunction,
        ZetaAdmissibleFunction.CanonicalScheduledZetaSideCauchyPathData
          f (K f))
    (gammaData :
      ∀ f : ZetaAdmissibleFunction,
        ZetaAdmissibleFunction.CanonicalScheduledInverseGammaCauchyPathData
          f (K f))
    (rightPrimeIntegrable :
      ∀ f : ZetaAdmissibleFunction,
        Integrable
          (ZetaAdmissibleFunction.zetaCompletedExplicitFormulaPrimeRightVonMangoldtAffineKernel
            (ZetaAdmissibleFunction.convolutionAutocorrelation f)
            (ZetaAdmissibleFunction.zetaCompletedExplicitFormula_autocorrelation_contourFamily f))
          (volume : Measure ℝ))
    (rightInverseGammaIntegrable :
      ∀ f : ZetaAdmissibleFunction,
        Integrable
          (ZetaAdmissibleFunction.zetaCompletedExplicitFormulaInverseGammaRightAffineKernel
            (ZetaAdmissibleFunction.convolutionAutocorrelation f)
            (ZetaAdmissibleFunction.zetaCompletedExplicitFormula_autocorrelation_contourFamily f))
          (volume : Measure ℝ))
    (leftReflectedIntegrable :
      ∀ f : ZetaAdmissibleFunction,
        Integrable
          (ZetaAdmissibleFunction.zetaCompletedExplicitFormulaPrimeLeftReflectedCompletedAffineKernel
            (ZetaAdmissibleFunction.convolutionAutocorrelation f)
            (ZetaAdmissibleFunction.zetaCompletedExplicitFormula_autocorrelation_contourFamily f))
          (volume : Measure ℝ))
    (packetDecomposition :
      ∀ f : ZetaAdmissibleFunction,
        (∫ t : ℝ,
            ZetaAdmissibleFunction.zetaCompletedRightAffineKernel
              (ZetaAdmissibleFunction.convolutionAutocorrelation f)
              (ZetaAdmissibleFunction.zetaCompletedExplicitFormula_autocorrelation_contourFamily f)
              t) -
          (∫ t : ℝ,
            ZetaAdmissibleFunction.zetaCompletedLeftAffineKernel
              (ZetaAdmissibleFunction.convolutionAutocorrelation f)
              (ZetaAdmissibleFunction.zetaCompletedExplicitFormula_autocorrelation_contourFamily f)
              t) =
          ((∫ t : ℝ,
              ZetaAdmissibleFunction.zetaCompletedExplicitFormulaPrimeRightVonMangoldtAffineKernel
                (ZetaAdmissibleFunction.convolutionAutocorrelation f)
                (ZetaAdmissibleFunction.zetaCompletedExplicitFormula_autocorrelation_contourFamily f)
                t) -
            ∑' n : ℕ,
              ∫ t : ℝ,
                ZetaAdmissibleFunction.zetaCompletedExplicitFormulaPrimeLeftReflectedTermKernel
                  (ZetaAdmissibleFunction.convolutionAutocorrelation f)
                  (ZetaAdmissibleFunction.zetaCompletedExplicitFormula_autocorrelation_contourFamily f)
                  n t) +
          ((∫ t : ℝ,
              ZetaAdmissibleFunction.zetaCompletedExplicitFormulaInverseGammaRightAffineKernel
                (ZetaAdmissibleFunction.convolutionAutocorrelation f)
                (ZetaAdmissibleFunction.zetaCompletedExplicitFormula_autocorrelation_contourFamily f)
                t) -
            ∫ t : ℝ,
              ZetaAdmissibleFunction.zetaCompletedExplicitFormulaPrimeLeftReflectedInverseGammaKernel
                (ZetaAdmissibleFunction.convolutionAutocorrelation f)
                (ZetaAdmissibleFunction.zetaCompletedExplicitFormula_autocorrelation_contourFamily f)
                t))
    (arithmeticEquality :
      ∀ f : ZetaAdmissibleFunction,
        ((∫ t : ℝ,
            ZetaAdmissibleFunction.zetaCompletedExplicitFormulaPrimeRightVonMangoldtAffineKernel
              (ZetaAdmissibleFunction.convolutionAutocorrelation f)
              (ZetaAdmissibleFunction.zetaCompletedExplicitFormula_autocorrelation_contourFamily f)
              t) -
          ∑' n : ℕ,
            ∫ t : ℝ,
              ZetaAdmissibleFunction.zetaCompletedExplicitFormulaPrimeLeftReflectedTermKernel
                (ZetaAdmissibleFunction.convolutionAutocorrelation f)
                (ZetaAdmissibleFunction.zetaCompletedExplicitFormula_autocorrelation_contourFamily f)
                n t) =
          ZetaAdmissibleFunction.zetaCompletedExplicitFormulaPrimeNaturalTwoFaceBoundaryContribution
            (ZetaAdmissibleFunction.convolutionAutocorrelation f))
    (differenceIntegral :
      ∀ f : ZetaAdmissibleFunction,
        (∫ t : ℝ,
          ZetaAdmissibleFunction.zetaCompletedAffineInverseGammaRightReflectedDifferenceKernel
            (ZetaAdmissibleFunction.convolutionAutocorrelation f)
            (ZetaAdmissibleFunction.zetaCompletedExplicitFormula_autocorrelation_contourFamily f)
            t) =
          (∫ t : ℝ,
            ZetaAdmissibleFunction.zetaCompletedExplicitFormulaInverseGammaRightAffineKernel
              (ZetaAdmissibleFunction.convolutionAutocorrelation f)
              (ZetaAdmissibleFunction.zetaCompletedExplicitFormula_autocorrelation_contourFamily f)
              t) -
            ∫ t : ℝ,
              ZetaAdmissibleFunction.zetaCompletedExplicitFormulaPrimeLeftReflectedInverseGammaKernel
                (ZetaAdmissibleFunction.convolutionAutocorrelation f)
                (ZetaAdmissibleFunction.zetaCompletedExplicitFormula_autocorrelation_contourFamily f)
                t)
    (archimedeanValue :
      ∀ f : ZetaAdmissibleFunction,
        (∫ t : ℝ,
          ZetaAdmissibleFunction.zetaCompletedAffineInverseGammaRightReflectedDifferenceKernel
            (ZetaAdmissibleFunction.convolutionAutocorrelation f)
            (ZetaAdmissibleFunction.zetaCompletedExplicitFormula_autocorrelation_contourFamily f)
            t) =
          ZetaAdmissibleFunction.zetaCompletedExplicitFormulaHermitianArchimedeanContribution
            (ZetaAdmissibleFunction.convolutionAutocorrelation f)) :
    ZetaWeilAutocorrelationBoundaryIdentification :=
  zetaWeilAutocorrelationBoundaryIdentification_of_canonicalScheduledCauchyPathData_componentPacketValue_owner
    K
    zetaData
    gammaData
    rightPrimeIntegrable
    rightInverseGammaIntegrable
    leftReflectedIntegrable
    (fun f =>
      ZetaAdmissibleFunction.zetaCompletedExplicitFormulaPrimeNaturalTwoFaceBoundaryContribution
        (ZetaAdmissibleFunction.convolutionAutocorrelation f))
    packetDecomposition
    arithmeticEquality
    differenceIntegral
    archimedeanValue
    (fun f =>
      ZetaAdmissibleFunction.zetaCompletedExplicitFormulaPrimeNaturalTwoFaceBoundaryContribution_div_twoPi_eq_primeContribution_autocorrelation
        f)
    (fun f =>
      zetaCompletedAffinePhysicalBoundaryChannel_eq
        (ZetaAdmissibleFunction.convolutionAutocorrelation f))

theorem zetaWeilAutocorrelationBoundaryIdentification_of_canonicalScheduledCauchyPathData_packetExchange_owner
    (K : ZetaAdmissibleFunction → ℕ)
    (zetaData :
      ∀ f : ZetaAdmissibleFunction,
        ZetaAdmissibleFunction.CanonicalScheduledZetaSideCauchyPathData
          f (K f))
    (gammaData :
      ∀ f : ZetaAdmissibleFunction,
        ZetaAdmissibleFunction.CanonicalScheduledInverseGammaCauchyPathData
          f (K f))
    (rightPrimeIntegrable :
      ∀ f : ZetaAdmissibleFunction,
        Integrable
          (ZetaAdmissibleFunction.zetaCompletedExplicitFormulaPrimeRightVonMangoldtAffineKernel
            (ZetaAdmissibleFunction.convolutionAutocorrelation f)
            (ZetaAdmissibleFunction.zetaCompletedExplicitFormula_autocorrelation_contourFamily f))
          (volume : Measure ℝ))
    (rightInverseGammaIntegrable :
      ∀ f : ZetaAdmissibleFunction,
        Integrable
          (ZetaAdmissibleFunction.zetaCompletedExplicitFormulaInverseGammaRightAffineKernel
            (ZetaAdmissibleFunction.convolutionAutocorrelation f)
            (ZetaAdmissibleFunction.zetaCompletedExplicitFormula_autocorrelation_contourFamily f))
          (volume : Measure ℝ))
    (leftReflectedIntegrable :
      ∀ f : ZetaAdmissibleFunction,
        Integrable
          (ZetaAdmissibleFunction.zetaCompletedExplicitFormulaPrimeLeftReflectedCompletedAffineKernel
            (ZetaAdmissibleFunction.convolutionAutocorrelation f)
            (ZetaAdmissibleFunction.zetaCompletedExplicitFormula_autocorrelation_contourFamily f))
          (volume : Measure ℝ))
    (leftInverseGammaIntegrable :
      ∀ f : ZetaAdmissibleFunction,
        Integrable
          (ZetaAdmissibleFunction.zetaCompletedExplicitFormulaPrimeLeftReflectedInverseGammaKernel
            (ZetaAdmissibleFunction.convolutionAutocorrelation f)
            (ZetaAdmissibleFunction.zetaCompletedExplicitFormula_autocorrelation_contourFamily f))
          (volume : Measure ℝ))
    (leftArithmeticIntegralExchange :
      ∀ f : ZetaAdmissibleFunction,
        (∫ t : ℝ,
          ∑' n : ℕ,
            ZetaAdmissibleFunction.zetaCompletedExplicitFormulaPrimeLeftReflectedTermKernel
              (ZetaAdmissibleFunction.convolutionAutocorrelation f)
              (ZetaAdmissibleFunction.zetaCompletedExplicitFormula_autocorrelation_contourFamily f)
              n t) =
          ∑' n : ℕ,
            ∫ t : ℝ,
              ZetaAdmissibleFunction.zetaCompletedExplicitFormulaPrimeLeftReflectedTermKernel
                (ZetaAdmissibleFunction.convolutionAutocorrelation f)
                (ZetaAdmissibleFunction.zetaCompletedExplicitFormula_autocorrelation_contourFamily f)
                n t)
    (arithmeticEquality :
      ∀ f : ZetaAdmissibleFunction,
        ((∫ t : ℝ,
            ZetaAdmissibleFunction.zetaCompletedExplicitFormulaPrimeRightVonMangoldtAffineKernel
              (ZetaAdmissibleFunction.convolutionAutocorrelation f)
              (ZetaAdmissibleFunction.zetaCompletedExplicitFormula_autocorrelation_contourFamily f)
              t) -
          ∑' n : ℕ,
            ∫ t : ℝ,
              ZetaAdmissibleFunction.zetaCompletedExplicitFormulaPrimeLeftReflectedTermKernel
                (ZetaAdmissibleFunction.convolutionAutocorrelation f)
                (ZetaAdmissibleFunction.zetaCompletedExplicitFormula_autocorrelation_contourFamily f)
                n t) =
          ZetaAdmissibleFunction.zetaCompletedExplicitFormulaPrimeNaturalTwoFaceBoundaryContribution
            (ZetaAdmissibleFunction.convolutionAutocorrelation f))
    (differenceIntegral :
      ∀ f : ZetaAdmissibleFunction,
        (∫ t : ℝ,
          ZetaAdmissibleFunction.zetaCompletedAffineInverseGammaRightReflectedDifferenceKernel
            (ZetaAdmissibleFunction.convolutionAutocorrelation f)
            (ZetaAdmissibleFunction.zetaCompletedExplicitFormula_autocorrelation_contourFamily f)
            t) =
          (∫ t : ℝ,
            ZetaAdmissibleFunction.zetaCompletedExplicitFormulaInverseGammaRightAffineKernel
              (ZetaAdmissibleFunction.convolutionAutocorrelation f)
              (ZetaAdmissibleFunction.zetaCompletedExplicitFormula_autocorrelation_contourFamily f)
              t) -
            ∫ t : ℝ,
              ZetaAdmissibleFunction.zetaCompletedExplicitFormulaPrimeLeftReflectedInverseGammaKernel
                (ZetaAdmissibleFunction.convolutionAutocorrelation f)
                (ZetaAdmissibleFunction.zetaCompletedExplicitFormula_autocorrelation_contourFamily f)
                t)
    (archimedeanValue :
      ∀ f : ZetaAdmissibleFunction,
        (∫ t : ℝ,
          ZetaAdmissibleFunction.zetaCompletedAffineInverseGammaRightReflectedDifferenceKernel
            (ZetaAdmissibleFunction.convolutionAutocorrelation f)
            (ZetaAdmissibleFunction.zetaCompletedExplicitFormula_autocorrelation_contourFamily f)
            t) =
          ZetaAdmissibleFunction.zetaCompletedExplicitFormulaHermitianArchimedeanContribution
            (ZetaAdmissibleFunction.convolutionAutocorrelation f)) :
    ZetaWeilAutocorrelationBoundaryIdentification :=
  zetaWeilAutocorrelationBoundaryIdentification_of_canonicalScheduledCauchyPathData_canonicalPacketValue_owner
    K
    zetaData
    gammaData
    rightPrimeIntegrable
    rightInverseGammaIntegrable
    leftReflectedIntegrable
    (fun f =>
      ZetaAdmissibleFunction.zetaCompletedAutocorrelationAffineKernel_packet_decomposition_of_component_integrable_exchange_owner
        f
        (rightPrimeIntegrable f)
        (rightInverseGammaIntegrable f)
        (leftReflectedIntegrable f)
        (leftInverseGammaIntegrable f)
        (leftArithmeticIntegralExchange f))
    arithmeticEquality
    differenceIntegral
    archimedeanValue

end
end LFunctions
end Boundary
