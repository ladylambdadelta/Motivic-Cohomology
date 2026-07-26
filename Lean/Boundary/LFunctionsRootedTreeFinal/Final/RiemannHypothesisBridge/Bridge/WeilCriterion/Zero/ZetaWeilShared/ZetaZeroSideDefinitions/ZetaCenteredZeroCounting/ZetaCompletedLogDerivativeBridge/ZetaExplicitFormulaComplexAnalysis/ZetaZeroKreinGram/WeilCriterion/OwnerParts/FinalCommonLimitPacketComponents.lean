import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaZeroKreinGram.WeilCriterion.OwnerParts.FinalCommonLimitFromFactorData

/-!
# Final common-limit assembly from affine packet components

This file peels the final common-limit affine packet input into the concrete
component facts used by the completed affine physical boundary lane.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open MeasureTheory

namespace ZetaAdmissibleFunction

/-- Concrete affine packet components assemble into the affine packet data for
the autocorrelation probe. -/
theorem zetaCompletedAutocorrelationAffinePacketData_of_components_final_owner
    (f : ZetaAdmissibleFunction)
    (rightPrimeIntegrable :
      Integrable
        (zetaCompletedExplicitFormulaPrimeRightVonMangoldtAffineKernel
          (convolutionAutocorrelation f)
          (zetaCompletedExplicitFormula_autocorrelation_contourFamily f))
        (volume : Measure ℝ))
    (rightInverseGammaIntegrable :
      Integrable
        (zetaCompletedExplicitFormulaInverseGammaRightAffineKernel
          (convolutionAutocorrelation f)
          (zetaCompletedExplicitFormula_autocorrelation_contourFamily f))
        (volume : Measure ℝ))
    (leftReflectedIntegrable :
      Integrable
        (zetaCompletedExplicitFormulaPrimeLeftReflectedCompletedAffineKernel
          (convolutionAutocorrelation f)
          (zetaCompletedExplicitFormula_autocorrelation_contourFamily f))
        (volume : Measure ℝ))
    (leftInverseGammaIntegrable :
      Integrable
        (zetaCompletedExplicitFormulaPrimeLeftReflectedInverseGammaKernel
          (convolutionAutocorrelation f)
          (zetaCompletedExplicitFormula_autocorrelation_contourFamily f))
        (volume : Measure ℝ))
    (leftArithmeticIntegralExchange :
      (∫ t : ℝ,
        ∑' n : ℕ,
          zetaCompletedExplicitFormulaPrimeLeftReflectedTermKernel
            (convolutionAutocorrelation f)
            (zetaCompletedExplicitFormula_autocorrelation_contourFamily f)
            n t) =
        ∑' n : ℕ,
          ∫ t : ℝ,
            zetaCompletedExplicitFormulaPrimeLeftReflectedTermKernel
              (convolutionAutocorrelation f)
              (zetaCompletedExplicitFormula_autocorrelation_contourFamily f)
              n t)
    (arithmeticEquality :
      ((∫ t : ℝ,
          zetaCompletedExplicitFormulaPrimeRightVonMangoldtAffineKernel
            (convolutionAutocorrelation f)
            (zetaCompletedExplicitFormula_autocorrelation_contourFamily f)
            t) -
        ∑' n : ℕ,
          ∫ t : ℝ,
            zetaCompletedExplicitFormulaPrimeLeftReflectedTermKernel
              (convolutionAutocorrelation f)
              (zetaCompletedExplicitFormula_autocorrelation_contourFamily f)
              n t) =
        zetaCompletedExplicitFormulaPrimeNaturalTwoFaceBoundaryContribution
          (convolutionAutocorrelation f))
    (inverseGammaDifferenceIntegral :
      (∫ t : ℝ,
        zetaCompletedAffineInverseGammaRightReflectedDifferenceKernel
          (convolutionAutocorrelation f)
          (zetaCompletedExplicitFormula_autocorrelation_contourFamily f)
          t) =
        (∫ t : ℝ,
          zetaCompletedExplicitFormulaInverseGammaRightAffineKernel
            (convolutionAutocorrelation f)
            (zetaCompletedExplicitFormula_autocorrelation_contourFamily f)
            t) -
          ∫ t : ℝ,
            zetaCompletedExplicitFormulaPrimeLeftReflectedInverseGammaKernel
              (convolutionAutocorrelation f)
              (zetaCompletedExplicitFormula_autocorrelation_contourFamily f)
              t)
    (archimedeanValue :
      (∫ t : ℝ,
        zetaCompletedAffineInverseGammaRightReflectedDifferenceKernel
          (convolutionAutocorrelation f)
          (zetaCompletedExplicitFormula_autocorrelation_contourFamily f)
          t) =
        zetaCompletedExplicitFormulaHermitianArchimedeanContribution
          (convolutionAutocorrelation f)) :
    ZetaCompletedAutocorrelationAffinePacketData f :=
  zetaCompletedAutocorrelationAffinePacketData_of_componentFacts_owner
    f
    rightPrimeIntegrable
    rightInverseGammaIntegrable
    leftReflectedIntegrable
    leftInverseGammaIntegrable
    leftArithmeticIntegralExchange
    arithmeticEquality
    inverseGammaDifferenceIntegral
    archimedeanValue

end ZetaAdmissibleFunction

/-- Canonical scheduled horizontal bounds and concrete affine packet
components construct the pole-corrected common limit. -/
theorem zetaCompletedAutocorrelationPoleCorrectedCommonLimit_of_canonicalScheduledHorizontalBounds_affinePacketComponents_final_owner
    (horizontalBounds :
      ∀ f : ZetaAdmissibleFunction,
        ZetaAdmissibleFunction.CanonicalScheduledPolynomialHorizontalBounds f)
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
    (inverseGammaDifferenceIntegral :
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
    ZetaCompletedAutocorrelationPoleCorrectedCommonLimit :=
  zetaCompletedAutocorrelationPoleCorrectedCommonLimit_of_canonicalScheduledHorizontalBounds_affinePacketData_final_owner
    horizontalBounds
    (fun f =>
      ZetaAdmissibleFunction.zetaCompletedAutocorrelationAffinePacketData_of_components_final_owner
        f
        (rightPrimeIntegrable f)
        (rightInverseGammaIntegrable f)
        (leftReflectedIntegrable f)
        (leftInverseGammaIntegrable f)
        (leftArithmeticIntegralExchange f)
        (arithmeticEquality f)
        (inverseGammaDifferenceIntegral f)
        (archimedeanValue f))

/-- Canonical scheduled horizontal bounds and explicit full contour analytic
packages construct the pole-corrected common limit through the peeled affine
packet component theorem. -/
theorem zetaCompletedAutocorrelationPoleCorrectedCommonLimit_of_canonicalScheduledHorizontalBounds_analyticPackages_final_owner
    (horizontalBounds :
      ∀ f : ZetaAdmissibleFunction,
        ZetaAdmissibleFunction.CanonicalScheduledPolynomialHorizontalBounds f)
    (analyticPackage :
      ∀ f : ZetaAdmissibleFunction,
        ZetaAdmissibleFunction.ExplicitFormulaFamilyAnalyticPackage
          (ZetaAdmissibleFunction.convolutionAutocorrelation f)
          (ZetaAdmissibleFunction.zetaCompletedExplicitFormula_autocorrelation_contourFamily f))
    (regularAnalyticPackage :
      ∀ f : ZetaAdmissibleFunction,
        ZetaAdmissibleFunction.ExplicitFormulaFamilyAnalyticPackage
          (ZetaAdmissibleFunction.convolutionAutocorrelation f)
          (ZetaAdmissibleFunction.zetaCompletedAutocorrelationRegularFamily f).toContourFamily) :
    ZetaCompletedAutocorrelationPoleCorrectedCommonLimit :=
  zetaCompletedAutocorrelationPoleCorrectedCommonLimit_of_canonicalScheduledHorizontalBounds_affinePacketComponents_final_owner
    horizontalBounds
    (fun f =>
      ZetaAdmissibleFunction.zetaCompletedAutocorrelationRightPrimeIntegrable_of_analyticPackage_owner
        f
        (analyticPackage f))
    (fun f =>
      ZetaAdmissibleFunction.zetaCompletedAutocorrelationRightInverseGammaIntegrable_of_analyticPackage_owner
        f
        (analyticPackage f))
    (fun f =>
      ZetaAdmissibleFunction.zetaCompletedAutocorrelationLeftReflectedIntegrable_of_regularAnalyticPackage_owner
        f
        (regularAnalyticPackage f))
    (fun f =>
      ZetaAdmissibleFunction.zetaCompletedAutocorrelationLeftInverseGammaIntegrable_of_analyticPackage_owner
        f
        (analyticPackage f))
    (fun f =>
      ZetaAdmissibleFunction.zetaCompletedAutocorrelationLeftArithmeticIntegralExchange_of_analyticPackage_owner
        f
        (analyticPackage f))
    (fun f =>
      ZetaAdmissibleFunction.zetaCompletedAutocorrelationArithmeticEquality_of_analyticPackage_owner
        f
        (analyticPackage f))
    (fun f =>
      ZetaAdmissibleFunction.zetaCompletedAutocorrelationInverseGammaDifferenceIntegral_of_analyticPackage_owner
        f
        (analyticPackage f))
    (fun f =>
      ZetaAdmissibleFunction.zetaCompletedAutocorrelationArchimedeanValue_of_inverseGammaTransport_owner
        f
        (ZetaAdmissibleFunction.zetaCompletedAutocorrelationInverseGammaTransport_of_analyticPackage_owner
          f
          (analyticPackage f)))

/-- Canonical scheduled horizontal bounds and the canonical Phi/Gamma affine
packet data construct the pole-corrected common limit. -/
theorem zetaCompletedAutocorrelationPoleCorrectedCommonLimit_of_canonicalScheduledHorizontalBounds_canonicalPhiGammaPacket_final_owner
    (horizontalBounds :
      ∀ f : ZetaAdmissibleFunction,
        ZetaAdmissibleFunction.CanonicalScheduledPolynomialHorizontalBounds f) :
    ZetaCompletedAutocorrelationPoleCorrectedCommonLimit :=
  zetaCompletedAutocorrelationPoleCorrectedCommonLimit_of_canonicalScheduledHorizontalBounds_affinePacketData_final_owner
    horizontalBounds
    (fun f =>
      ZetaAdmissibleFunction.zetaCompletedAutocorrelationAffinePacketData_canonicalPhiGamma_owner
        f)

end
end LFunctions
end Boundary
