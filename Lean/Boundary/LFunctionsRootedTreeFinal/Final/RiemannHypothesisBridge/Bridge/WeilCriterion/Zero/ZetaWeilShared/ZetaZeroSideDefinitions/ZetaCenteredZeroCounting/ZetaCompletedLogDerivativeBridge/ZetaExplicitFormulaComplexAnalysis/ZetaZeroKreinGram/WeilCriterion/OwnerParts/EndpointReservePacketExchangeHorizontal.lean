import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaZeroKreinGram.WeilCriterion.OwnerParts.EndpointReserveHorizontal
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaZeroKreinGram.WeilCriterion.OwnerParts.CauchyPathPacketExchangePositivity

/-!
# Endpoint reserve positivity through packet exchange and package-horizontal transport

This owner part routes packet-exchange affine kernel data through the corrected
polynomial package-horizontal boundary lane.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open MeasureTheory

/-- Canonical scheduled Cauchy path data and packet-exchange affine kernel
inputs give raw Weil positivity through the corrected package-horizontal lane. -/
theorem zetaWeilQuadraticPositivity_of_canonicalScheduledCauchyPathData_packetExchange_packageHorizontal_owner
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
    ZetaWeilQuadraticPositivity :=
  zetaWeilQuadraticPositivity_of_canonicalScheduledCauchyPathData_affineKernelIntegrableValue_packageHorizontal_owner
    K
    zetaData
    gammaData
    (fun f =>
      ZetaAdmissibleFunction.zetaCompletedAutocorrelationRightAffineKernel_integrable_of_packetExchange_owner
        f
        (rightPrimeIntegrable f)
        (rightInverseGammaIntegrable f))
    (fun f =>
      ZetaAdmissibleFunction.zetaCompletedAutocorrelationLeftAffineKernel_integrable_of_packetExchange_owner
        f
        (leftReflectedIntegrable f))
    (fun f =>
      ZetaAdmissibleFunction.zetaCompletedAutocorrelationAffineKernel_integral_eq_physical_of_packetExchange_owner
        f
        (rightPrimeIntegrable f)
        (rightInverseGammaIntegrable f)
        (leftReflectedIntegrable f)
        (leftInverseGammaIntegrable f)
        (leftArithmeticIntegralExchange f)
        (arithmeticEquality f)
        (differenceIntegral f)
        (archimedeanValue f))

/-- Carrier-level Cauchy data and packet-exchange affine kernel inputs give raw
Weil positivity through the corrected package-horizontal lane. -/
theorem zetaWeilQuadraticPositivity_of_canonicalScheduledCarrierCauchyData_packetExchange_packageHorizontal_owner
    (K : ZetaAdmissibleFunction → ℕ)
    (zetaRadius zetaAmplitude zetaValueLower :
      ∀ f : ZetaAdmissibleFunction, ℝ)
    (gammaRadius gammaAmplitude gammaValueLower :
      ∀ f : ZetaAdmissibleFunction, ℝ)
    (zetaRadius_pos :
      ∀ f : ZetaAdmissibleFunction, 0 < zetaRadius f)
    (zetaAmplitude_pos :
      ∀ f : ZetaAdmissibleFunction, 0 < zetaAmplitude f)
    (zetaValueLower_pos :
      ∀ f : ZetaAdmissibleFunction, 0 < zetaValueLower f)
    (gammaRadius_pos :
      ∀ f : ZetaAdmissibleFunction, 0 < gammaRadius f)
    (gammaAmplitude_pos :
      ∀ f : ZetaAdmissibleFunction, 0 < gammaAmplitude f)
    (gammaValueLower_pos :
      ∀ f : ZetaAdmissibleFunction, 0 < gammaValueLower f)
    (zetaDiffCont :
      ∀ (f : ZetaAdmissibleFunction) (z : ℂ),
        z ∈
          (ZetaAdmissibleFunction.zetaCompletedExplicitFormulaAutocorrelationScheduledHorizontalCarrier f)
            .carrier →
        DiffContOnCl ℂ ZetaAdmissibleFunction.zetaSideFactor
          (Metric.ball z (zetaRadius f)))
    (gammaDiffCont :
      ∀ (f : ZetaAdmissibleFunction) (z : ℂ),
        z ∈
          (ZetaAdmissibleFunction.zetaCompletedExplicitFormulaAutocorrelationScheduledHorizontalCarrier f)
            .carrier →
        DiffContOnCl ℂ
          (fun w : ℂ => (Complex.Gammaℝ w)⁻¹)
          (Metric.ball z (gammaRadius f)))
    (zetaSphereBound :
      ∀ (f : ZetaAdmissibleFunction) (z : ℂ),
        z ∈
          (ZetaAdmissibleFunction.zetaCompletedExplicitFormulaAutocorrelationScheduledHorizontalCarrier f)
            .carrier →
        ∀ w : ℂ,
          w ∈ Metric.sphere z (zetaRadius f) →
          ‖ZetaAdmissibleFunction.zetaSideFactor w‖ ≤
            zetaAmplitude f * (1 + ‖z.im‖) ^ K f)
    (gammaSphereBound :
      ∀ (f : ZetaAdmissibleFunction) (z : ℂ),
        z ∈
          (ZetaAdmissibleFunction.zetaCompletedExplicitFormulaAutocorrelationScheduledHorizontalCarrier f)
            .carrier →
        ∀ w : ℂ,
          w ∈ Metric.sphere z (gammaRadius f) →
          ‖(Complex.Gammaℝ w)⁻¹‖ ≤
            gammaAmplitude f * (1 + ‖z.im‖) ^ K f)
    (zetaValueLower_bound :
      ∀ (f : ZetaAdmissibleFunction) (z : ℂ),
        z ∈
          (ZetaAdmissibleFunction.zetaCompletedExplicitFormulaAutocorrelationScheduledHorizontalCarrier f)
            .carrier →
        zetaValueLower f ≤ ‖ZetaAdmissibleFunction.zetaSideFactor z‖)
    (gammaValueLower_bound :
      ∀ (f : ZetaAdmissibleFunction) (z : ℂ),
        z ∈
          (ZetaAdmissibleFunction.zetaCompletedExplicitFormulaAutocorrelationScheduledHorizontalCarrier f)
            .carrier →
        gammaValueLower f ≤ ‖(Complex.Gammaℝ z)⁻¹‖)
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
    ZetaWeilQuadraticPositivity :=
  zetaWeilQuadraticPositivity_of_canonicalScheduledCauchyPathData_packetExchange_packageHorizontal_owner
    K
    (fun f =>
      ZetaAdmissibleFunction.CanonicalScheduledZetaSideCauchyPathData.ofCarrierCauchyData
        f
        (K f)
        (zetaRadius f)
        (zetaAmplitude f)
        (zetaValueLower f)
        (zetaRadius_pos f)
        (zetaAmplitude_pos f)
        (zetaValueLower_pos f)
        (zetaDiffCont f)
        (zetaSphereBound f)
        (zetaValueLower_bound f))
    (fun f =>
      ZetaAdmissibleFunction.CanonicalScheduledInverseGammaCauchyPathData.ofCarrierCauchyData
        f
        (K f)
        (gammaRadius f)
        (gammaAmplitude f)
        (gammaValueLower f)
        (gammaRadius_pos f)
        (gammaAmplitude_pos f)
        (gammaValueLower_pos f)
        (gammaDiffCont f)
        (gammaSphereBound f)
        (gammaValueLower_bound f))
    rightPrimeIntegrable
    rightInverseGammaIntegrable
    leftReflectedIntegrable
    leftInverseGammaIntegrable
    leftArithmeticIntegralExchange
    arithmeticEquality
    differenceIntegral
    archimedeanValue

/-- Carrier-level Cauchy data and autocorrelation log-derivative control give
raw Weil positivity through the corrected package-horizontal lane. -/
theorem zetaWeilQuadraticPositivity_of_canonicalScheduledCarrierCauchyData_packetExchange_logDerivControl_packageHorizontal_owner
    (K : ZetaAdmissibleFunction → ℕ)
    (zetaRadius zetaAmplitude zetaValueLower :
      ∀ f : ZetaAdmissibleFunction, ℝ)
    (gammaRadius gammaAmplitude gammaValueLower :
      ∀ f : ZetaAdmissibleFunction, ℝ)
    (zetaRadius_pos :
      ∀ f : ZetaAdmissibleFunction, 0 < zetaRadius f)
    (zetaAmplitude_pos :
      ∀ f : ZetaAdmissibleFunction, 0 < zetaAmplitude f)
    (zetaValueLower_pos :
      ∀ f : ZetaAdmissibleFunction, 0 < zetaValueLower f)
    (gammaRadius_pos :
      ∀ f : ZetaAdmissibleFunction, 0 < gammaRadius f)
    (gammaAmplitude_pos :
      ∀ f : ZetaAdmissibleFunction, 0 < gammaAmplitude f)
    (gammaValueLower_pos :
      ∀ f : ZetaAdmissibleFunction, 0 < gammaValueLower f)
    (zetaDiffCont :
      ∀ (f : ZetaAdmissibleFunction) (z : ℂ),
        z ∈
          (ZetaAdmissibleFunction.zetaCompletedExplicitFormulaAutocorrelationScheduledHorizontalCarrier f)
            .carrier →
        DiffContOnCl ℂ ZetaAdmissibleFunction.zetaSideFactor
          (Metric.ball z (zetaRadius f)))
    (gammaDiffCont :
      ∀ (f : ZetaAdmissibleFunction) (z : ℂ),
        z ∈
          (ZetaAdmissibleFunction.zetaCompletedExplicitFormulaAutocorrelationScheduledHorizontalCarrier f)
            .carrier →
        DiffContOnCl ℂ
          (fun w : ℂ => (Complex.Gammaℝ w)⁻¹)
          (Metric.ball z (gammaRadius f)))
    (zetaSphereBound :
      ∀ (f : ZetaAdmissibleFunction) (z : ℂ),
        z ∈
          (ZetaAdmissibleFunction.zetaCompletedExplicitFormulaAutocorrelationScheduledHorizontalCarrier f)
            .carrier →
        ∀ w : ℂ,
          w ∈ Metric.sphere z (zetaRadius f) →
          ‖ZetaAdmissibleFunction.zetaSideFactor w‖ ≤
            zetaAmplitude f * (1 + ‖z.im‖) ^ K f)
    (gammaSphereBound :
      ∀ (f : ZetaAdmissibleFunction) (z : ℂ),
        z ∈
          (ZetaAdmissibleFunction.zetaCompletedExplicitFormulaAutocorrelationScheduledHorizontalCarrier f)
            .carrier →
        ∀ w : ℂ,
          w ∈ Metric.sphere z (gammaRadius f) →
          ‖(Complex.Gammaℝ w)⁻¹‖ ≤
            gammaAmplitude f * (1 + ‖z.im‖) ^ K f)
    (zetaValueLower_bound :
      ∀ (f : ZetaAdmissibleFunction) (z : ℂ),
        z ∈
          (ZetaAdmissibleFunction.zetaCompletedExplicitFormulaAutocorrelationScheduledHorizontalCarrier f)
            .carrier →
        zetaValueLower f ≤ ‖ZetaAdmissibleFunction.zetaSideFactor z‖)
    (gammaValueLower_bound :
      ∀ (f : ZetaAdmissibleFunction) (z : ℂ),
        z ∈
          (ZetaAdmissibleFunction.zetaCompletedExplicitFormulaAutocorrelationScheduledHorizontalCarrier f)
            .carrier →
        gammaValueLower f ≤ ‖(Complex.Gammaℝ z)⁻¹‖)
    (hPhi :
      ∀ f : ZetaAdmissibleFunction,
        ZetaAdmissibleFunction.ZetaPhiAnalyticControl
          (ZetaAdmissibleFunction.convolutionAutocorrelation f))
    (hLog :
      ∀ f : ZetaAdmissibleFunction,
        ZetaAdmissibleFunction.CompletedZetaNegLogDerivControl
          (ZetaAdmissibleFunction.convolutionAutocorrelation f)) :
    ZetaWeilQuadraticPositivity :=
  zetaWeilQuadraticPositivity_of_canonicalScheduledCarrierCauchyData_packetExchange_packageHorizontal_owner
    K
    zetaRadius
    zetaAmplitude
    zetaValueLower
    gammaRadius
    gammaAmplitude
    gammaValueLower
    zetaRadius_pos
    zetaAmplitude_pos
    zetaValueLower_pos
    gammaRadius_pos
    gammaAmplitude_pos
    gammaValueLower_pos
    zetaDiffCont
    gammaDiffCont
    zetaSphereBound
    gammaSphereBound
    zetaValueLower_bound
    gammaValueLower_bound
    (fun f =>
      ZetaAdmissibleFunction.zetaCompletedAutocorrelationRightPrimeIntegrable_of_logDerivControl_owner
        f (hPhi f) (hLog f))
    (fun f =>
      ZetaAdmissibleFunction.zetaCompletedAutocorrelationRightInverseGammaIntegrable_of_logDerivControl_owner
        f (hPhi f) (hLog f))
    (fun f =>
      ZetaAdmissibleFunction.zetaCompletedAutocorrelationLeftReflectedIntegrable_of_logDerivControl_owner
        f (hPhi f) (hLog f))
    (fun f =>
      ZetaAdmissibleFunction.zetaCompletedAutocorrelationLeftInverseGammaIntegrable_of_logDerivControl_owner
        f (hPhi f) (hLog f))
    (fun f =>
      ZetaAdmissibleFunction.zetaCompletedAutocorrelationLeftArithmeticIntegralExchange_of_logDerivControl_owner
        f (hPhi f) (hLog f))
    (fun f =>
      ZetaAdmissibleFunction.zetaCompletedAutocorrelationArithmeticEquality_of_logDerivControl_owner
        f (hPhi f) (hLog f))
    (fun f =>
      ZetaAdmissibleFunction.zetaCompletedAutocorrelationInverseGammaDifferenceIntegral_of_logDerivControl_owner
        f (hPhi f) (hLog f))
    (fun f =>
      ZetaAdmissibleFunction.zetaCompletedAutocorrelationArchimedeanValue_of_logDerivControl_owner
        f (hPhi f) (hLog f))

/-- Carrier-level Cauchy data and canonical autocorrelation log-derivative
control give raw Weil positivity through the corrected package-horizontal lane. -/
theorem zetaWeilQuadraticPositivity_of_canonicalScheduledCarrierCauchyData_packetExchange_canonicalPhi_logDerivControl_packageHorizontal_owner
    (K : ZetaAdmissibleFunction → ℕ)
    (zetaRadius zetaAmplitude zetaValueLower :
      ∀ f : ZetaAdmissibleFunction, ℝ)
    (gammaRadius gammaAmplitude gammaValueLower :
      ∀ f : ZetaAdmissibleFunction, ℝ)
    (zetaRadius_pos :
      ∀ f : ZetaAdmissibleFunction, 0 < zetaRadius f)
    (zetaAmplitude_pos :
      ∀ f : ZetaAdmissibleFunction, 0 < zetaAmplitude f)
    (zetaValueLower_pos :
      ∀ f : ZetaAdmissibleFunction, 0 < zetaValueLower f)
    (gammaRadius_pos :
      ∀ f : ZetaAdmissibleFunction, 0 < gammaRadius f)
    (gammaAmplitude_pos :
      ∀ f : ZetaAdmissibleFunction, 0 < gammaAmplitude f)
    (gammaValueLower_pos :
      ∀ f : ZetaAdmissibleFunction, 0 < gammaValueLower f)
    (zetaDiffCont :
      ∀ (f : ZetaAdmissibleFunction) (z : ℂ),
        z ∈
          (ZetaAdmissibleFunction.zetaCompletedExplicitFormulaAutocorrelationScheduledHorizontalCarrier f)
            .carrier →
        DiffContOnCl ℂ ZetaAdmissibleFunction.zetaSideFactor
          (Metric.ball z (zetaRadius f)))
    (gammaDiffCont :
      ∀ (f : ZetaAdmissibleFunction) (z : ℂ),
        z ∈
          (ZetaAdmissibleFunction.zetaCompletedExplicitFormulaAutocorrelationScheduledHorizontalCarrier f)
            .carrier →
        DiffContOnCl ℂ
          (fun w : ℂ => (Complex.Gammaℝ w)⁻¹)
          (Metric.ball z (gammaRadius f)))
    (zetaSphereBound :
      ∀ (f : ZetaAdmissibleFunction) (z : ℂ),
        z ∈
          (ZetaAdmissibleFunction.zetaCompletedExplicitFormulaAutocorrelationScheduledHorizontalCarrier f)
            .carrier →
        ∀ w : ℂ,
          w ∈ Metric.sphere z (zetaRadius f) →
          ‖ZetaAdmissibleFunction.zetaSideFactor w‖ ≤
            zetaAmplitude f * (1 + ‖z.im‖) ^ K f)
    (gammaSphereBound :
      ∀ (f : ZetaAdmissibleFunction) (z : ℂ),
        z ∈
          (ZetaAdmissibleFunction.zetaCompletedExplicitFormulaAutocorrelationScheduledHorizontalCarrier f)
            .carrier →
        ∀ w : ℂ,
          w ∈ Metric.sphere z (gammaRadius f) →
          ‖(Complex.Gammaℝ w)⁻¹‖ ≤
            gammaAmplitude f * (1 + ‖z.im‖) ^ K f)
    (zetaValueLower_bound :
      ∀ (f : ZetaAdmissibleFunction) (z : ℂ),
        z ∈
          (ZetaAdmissibleFunction.zetaCompletedExplicitFormulaAutocorrelationScheduledHorizontalCarrier f)
            .carrier →
        zetaValueLower f ≤ ‖ZetaAdmissibleFunction.zetaSideFactor z‖)
    (gammaValueLower_bound :
      ∀ (f : ZetaAdmissibleFunction) (z : ℂ),
        z ∈
          (ZetaAdmissibleFunction.zetaCompletedExplicitFormulaAutocorrelationScheduledHorizontalCarrier f)
            .carrier →
        gammaValueLower f ≤ ‖(Complex.Gammaℝ z)⁻¹‖)
    (hLog :
      ∀ f : ZetaAdmissibleFunction,
        ZetaAdmissibleFunction.CompletedZetaNegLogDerivControl
          (ZetaAdmissibleFunction.convolutionAutocorrelation f)) :
    ZetaWeilQuadraticPositivity :=
  zetaWeilQuadraticPositivity_of_canonicalScheduledCarrierCauchyData_packetExchange_logDerivControl_packageHorizontal_owner
    K
    zetaRadius
    zetaAmplitude
    zetaValueLower
    gammaRadius
    gammaAmplitude
    gammaValueLower
    zetaRadius_pos
    zetaAmplitude_pos
    zetaValueLower_pos
    gammaRadius_pos
    gammaAmplitude_pos
    gammaValueLower_pos
    zetaDiffCont
    gammaDiffCont
    zetaSphereBound
    gammaSphereBound
    zetaValueLower_bound
    gammaValueLower_bound
    (ZetaAdmissibleFunction.zetaPhiAnalyticControl_autocorrelation_of_concreteControl
      ZetaAdmissibleFunction.zetaPhiAutocorrelationConcreteControl_owner)
    hLog

/-- Carrier-level Cauchy data and split autocorrelation log-derivative controls
give raw Weil positivity through the corrected package-horizontal lane. -/
theorem zetaWeilQuadraticPositivity_of_canonicalScheduledCarrierCauchyData_packetExchange_splitLogDerivControls_packageHorizontal_owner
    (K : ZetaAdmissibleFunction → ℕ)
    (zetaRadius zetaAmplitude zetaValueLower :
      ∀ f : ZetaAdmissibleFunction, ℝ)
    (gammaRadius gammaAmplitude gammaValueLower :
      ∀ f : ZetaAdmissibleFunction, ℝ)
    (zetaRadius_pos :
      ∀ f : ZetaAdmissibleFunction, 0 < zetaRadius f)
    (zetaAmplitude_pos :
      ∀ f : ZetaAdmissibleFunction, 0 < zetaAmplitude f)
    (zetaValueLower_pos :
      ∀ f : ZetaAdmissibleFunction, 0 < zetaValueLower f)
    (gammaRadius_pos :
      ∀ f : ZetaAdmissibleFunction, 0 < gammaRadius f)
    (gammaAmplitude_pos :
      ∀ f : ZetaAdmissibleFunction, 0 < gammaAmplitude f)
    (gammaValueLower_pos :
      ∀ f : ZetaAdmissibleFunction, 0 < gammaValueLower f)
    (zetaDiffCont :
      ∀ (f : ZetaAdmissibleFunction) (z : ℂ),
        z ∈
          (ZetaAdmissibleFunction.zetaCompletedExplicitFormulaAutocorrelationScheduledHorizontalCarrier f)
            .carrier →
        DiffContOnCl ℂ ZetaAdmissibleFunction.zetaSideFactor
          (Metric.ball z (zetaRadius f)))
    (gammaDiffCont :
      ∀ (f : ZetaAdmissibleFunction) (z : ℂ),
        z ∈
          (ZetaAdmissibleFunction.zetaCompletedExplicitFormulaAutocorrelationScheduledHorizontalCarrier f)
            .carrier →
        DiffContOnCl ℂ
          (fun w : ℂ => (Complex.Gammaℝ w)⁻¹)
          (Metric.ball z (gammaRadius f)))
    (zetaSphereBound :
      ∀ (f : ZetaAdmissibleFunction) (z : ℂ),
        z ∈
          (ZetaAdmissibleFunction.zetaCompletedExplicitFormulaAutocorrelationScheduledHorizontalCarrier f)
            .carrier →
        ∀ w : ℂ,
          w ∈ Metric.sphere z (zetaRadius f) →
          ‖ZetaAdmissibleFunction.zetaSideFactor w‖ ≤
            zetaAmplitude f * (1 + ‖z.im‖) ^ K f)
    (gammaSphereBound :
      ∀ (f : ZetaAdmissibleFunction) (z : ℂ),
        z ∈
          (ZetaAdmissibleFunction.zetaCompletedExplicitFormulaAutocorrelationScheduledHorizontalCarrier f)
            .carrier →
        ∀ w : ℂ,
          w ∈ Metric.sphere z (gammaRadius f) →
          ‖(Complex.Gammaℝ w)⁻¹‖ ≤
            gammaAmplitude f * (1 + ‖z.im‖) ^ K f)
    (zetaValueLower_bound :
      ∀ (f : ZetaAdmissibleFunction) (z : ℂ),
        z ∈
          (ZetaAdmissibleFunction.zetaCompletedExplicitFormulaAutocorrelationScheduledHorizontalCarrier f)
            .carrier →
        zetaValueLower f ≤ ‖ZetaAdmissibleFunction.zetaSideFactor z‖)
    (gammaValueLower_bound :
      ∀ (f : ZetaAdmissibleFunction) (z : ℂ),
        z ∈
          (ZetaAdmissibleFunction.zetaCompletedExplicitFormulaAutocorrelationScheduledHorizontalCarrier f)
            .carrier →
        gammaValueLower f ≤ ‖(Complex.Gammaℝ z)⁻¹‖)
    (hZetaSide :
      ZetaAdmissibleFunction.CompletedZetaNegLogDerivAutocorrelationZetaSideControl)
    (hInverseGamma :
      ZetaAdmissibleFunction.CompletedZetaNegLogDerivAutocorrelationInverseGammaControl) :
    ZetaWeilQuadraticPositivity :=
  zetaWeilQuadraticPositivity_of_canonicalScheduledCarrierCauchyData_packetExchange_canonicalPhi_logDerivControl_packageHorizontal_owner
    K
    zetaRadius
    zetaAmplitude
    zetaValueLower
    gammaRadius
    gammaAmplitude
    gammaValueLower
    zetaRadius_pos
    zetaAmplitude_pos
    zetaValueLower_pos
    gammaRadius_pos
    gammaAmplitude_pos
    gammaValueLower_pos
    zetaDiffCont
    gammaDiffCont
    zetaSphereBound
    gammaSphereBound
    zetaValueLower_bound
    gammaValueLower_bound
    (ZetaAdmissibleFunction.completedZetaNegLogDerivControl_autocorrelation_of_concreteControl
      (ZetaAdmissibleFunction.completedZetaNegLogDerivAutocorrelationConcreteControl_of_factorControls
        hZetaSide
        hInverseGamma))

end
end LFunctions
end Boundary
