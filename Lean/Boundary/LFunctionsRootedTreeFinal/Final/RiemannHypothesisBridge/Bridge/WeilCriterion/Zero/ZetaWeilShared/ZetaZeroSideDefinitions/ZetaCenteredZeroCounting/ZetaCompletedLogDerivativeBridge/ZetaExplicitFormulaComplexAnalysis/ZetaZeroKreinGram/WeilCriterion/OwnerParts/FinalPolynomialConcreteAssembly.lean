import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaZeroKreinGram.WeilCriterion.OwnerParts.FinalBoundaryIdentificationPositivity

/-!
# Final polynomial/concrete assembly

This owner part records the narrow corrected final lane: polynomial scheduled
horizontal control supplies the zero-side limit, while the concrete affine
packet supplies the physical endpoint.
-/

namespace Boundary
namespace LFunctions

noncomputable section

/-- Polynomial scheduled packages and concrete autocorrelation
completed-log-derivative control construct the corrected pole-corrected common
limit through the affine-packet lane. -/
theorem zetaCompletedAutocorrelationPoleCorrectedCommonLimit_of_polynomialScheduledConcreteControl_final_owner
    (hPolynomial :
      ∀ f : ZetaAdmissibleFunction,
        ZetaAdmissibleFunction.ExplicitFormulaScheduledPolynomialFamilyAnalyticPackage
          (zetaAutocorrelationPhysicalProbe f)
          (zetaAutocorrelationPhysicalContourFamily f))
    (hConcrete :
      ZetaAdmissibleFunction.CompletedZetaNegLogDerivAutocorrelationConcreteControl) :
    ZetaCompletedAutocorrelationPoleCorrectedCommonLimit :=
  zetaCompletedAutocorrelationPoleCorrectedCommonLimit_of_polynomialScheduledAffinePacketData_final_owner
    hPolynomial
    (fun f =>
      ZetaAdmissibleFunction.zetaCompletedAutocorrelationAffinePacketData_of_concreteControl_owner
        f
        hConcrete)

/-- Polynomial scheduled packages and split autocorrelation factor controls
construct the corrected pole-corrected common limit. -/
theorem zetaCompletedAutocorrelationPoleCorrectedCommonLimit_of_polynomialScheduledSplitControls_final_owner
    (hPolynomial :
      ∀ f : ZetaAdmissibleFunction,
        ZetaAdmissibleFunction.ExplicitFormulaScheduledPolynomialFamilyAnalyticPackage
          (zetaAutocorrelationPhysicalProbe f)
          (zetaAutocorrelationPhysicalContourFamily f))
    (hZetaSide :
      ZetaAdmissibleFunction.CompletedZetaNegLogDerivAutocorrelationZetaSideControl)
    (hInverseGamma :
      ZetaAdmissibleFunction.CompletedZetaNegLogDerivAutocorrelationInverseGammaControl) :
    ZetaCompletedAutocorrelationPoleCorrectedCommonLimit :=
  zetaCompletedAutocorrelationPoleCorrectedCommonLimit_of_polynomialScheduledConcreteControl_final_owner
    hPolynomial
    (ZetaAdmissibleFunction.completedZetaNegLogDerivAutocorrelationConcreteControl_of_factorControls
      hZetaSide
      hInverseGamma)

/-- Polynomial scheduled packages and global factor controls construct the
corrected pole-corrected common limit. -/
theorem zetaCompletedAutocorrelationPoleCorrectedCommonLimit_of_polynomialScheduledGlobalFactorControls_final_owner
    (hPolynomial :
      ∀ f : ZetaAdmissibleFunction,
        ZetaAdmissibleFunction.ExplicitFormulaScheduledPolynomialFamilyAnalyticPackage
          (zetaAutocorrelationPhysicalProbe f)
          (zetaAutocorrelationPhysicalContourFamily f))
    (hZetaSide :
      ZetaAdmissibleFunction.CompletedZetaNegLogDerivZetaSideControl)
    (hInverseGamma :
      ZetaAdmissibleFunction.CompletedZetaNegLogDerivInverseGammaControl) :
    ZetaCompletedAutocorrelationPoleCorrectedCommonLimit :=
  zetaCompletedAutocorrelationPoleCorrectedCommonLimit_of_polynomialScheduledConcreteControl_final_owner
    hPolynomial
    (ZetaAdmissibleFunction.completedZetaNegLogDerivAutocorrelationConcreteControl_of_globalFactorControls
      hZetaSide
      hInverseGamma)

/-- Polynomial scheduled packages and concrete autocorrelation
completed-log-derivative control give final raw Weil positivity. -/
theorem zetaWeilQuadraticPositivity_of_polynomialScheduledConcreteControl_final_owner
    (hPolynomial :
      ∀ f : ZetaAdmissibleFunction,
        ZetaAdmissibleFunction.ExplicitFormulaScheduledPolynomialFamilyAnalyticPackage
          (zetaAutocorrelationPhysicalProbe f)
          (zetaAutocorrelationPhysicalContourFamily f))
    (hConcrete :
      ZetaAdmissibleFunction.CompletedZetaNegLogDerivAutocorrelationConcreteControl) :
    ZetaWeilQuadraticPositivity :=
  zetaWeilQuadraticPositivity_of_finalCommonLimit_owner
    (zetaCompletedAutocorrelationPoleCorrectedCommonLimit_of_polynomialScheduledConcreteControl_final_owner
      hPolynomial
      hConcrete)

/-- Polynomial scheduled packages and split autocorrelation factor controls give
final raw Weil positivity. -/
theorem zetaWeilQuadraticPositivity_of_polynomialScheduledSplitControls_final_owner
    (hPolynomial :
      ∀ f : ZetaAdmissibleFunction,
        ZetaAdmissibleFunction.ExplicitFormulaScheduledPolynomialFamilyAnalyticPackage
          (zetaAutocorrelationPhysicalProbe f)
          (zetaAutocorrelationPhysicalContourFamily f))
    (hZetaSide :
      ZetaAdmissibleFunction.CompletedZetaNegLogDerivAutocorrelationZetaSideControl)
    (hInverseGamma :
      ZetaAdmissibleFunction.CompletedZetaNegLogDerivAutocorrelationInverseGammaControl) :
    ZetaWeilQuadraticPositivity :=
  zetaWeilQuadraticPositivity_of_finalCommonLimit_owner
    (zetaCompletedAutocorrelationPoleCorrectedCommonLimit_of_polynomialScheduledSplitControls_final_owner
      hPolynomial
      hZetaSide
      hInverseGamma)

/-- Polynomial scheduled packages and global factor controls give final raw
Weil positivity. -/
theorem zetaWeilQuadraticPositivity_of_polynomialScheduledGlobalFactorControls_final_owner
    (hPolynomial :
      ∀ f : ZetaAdmissibleFunction,
        ZetaAdmissibleFunction.ExplicitFormulaScheduledPolynomialFamilyAnalyticPackage
          (zetaAutocorrelationPhysicalProbe f)
          (zetaAutocorrelationPhysicalContourFamily f))
    (hZetaSide :
      ZetaAdmissibleFunction.CompletedZetaNegLogDerivZetaSideControl)
    (hInverseGamma :
      ZetaAdmissibleFunction.CompletedZetaNegLogDerivInverseGammaControl) :
    ZetaWeilQuadraticPositivity :=
  zetaWeilQuadraticPositivity_of_finalCommonLimit_owner
    (zetaCompletedAutocorrelationPoleCorrectedCommonLimit_of_polynomialScheduledGlobalFactorControls_final_owner
      hPolynomial
      hZetaSide
      hInverseGamma)

end

end LFunctions
end Boundary
