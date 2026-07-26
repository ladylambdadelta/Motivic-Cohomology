import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaZeroKreinGram.WeilCriterion.OwnerParts.CauchyPathPacketExchangePositivity

/-!
# Carrier Cauchy data packet-exchange positivity

This owner part lifts the packet-exchange positivity lane from scheduled path
data to carrier-level Cauchy data on the canonical scheduled horizontal carrier.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open MeasureTheory

theorem zetaWeilAutocorrelationBoundaryIdentification_of_canonicalScheduledCarrierCauchyData_packetExchange_owner
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
    ZetaWeilAutocorrelationBoundaryIdentification :=
  zetaWeilAutocorrelationBoundaryIdentification_of_canonicalScheduledCauchyPathData_packetExchange_owner
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

theorem zetaWeilQuadraticPositivity_of_canonicalScheduledCarrierCauchyData_packetExchange_owner
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
  zetaWeilQuadraticPositivity_of_boundaryIdentification_owner
    (zetaWeilAutocorrelationBoundaryIdentification_of_canonicalScheduledCarrierCauchyData_packetExchange_owner
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
      rightPrimeIntegrable
      rightInverseGammaIntegrable
      leftReflectedIntegrable
      leftInverseGammaIntegrable
      leftArithmeticIntegralExchange
      arithmeticEquality
      differenceIntegral
      archimedeanValue)

end

end LFunctions
end Boundary
