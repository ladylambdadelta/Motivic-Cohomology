import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaZeroKreinGram.WeilCriterion.OwnerParts.FinalPolynomialConcreteAssembly

/-!
# Final carrier-Cauchy concrete assembly

This owner part packages the final common-limit lane directly from canonical
scheduled carrier Cauchy data.  The carrier package supplies the horizontal
polynomial bounds; concrete log-derivative control supplies the affine packet.
-/

namespace Boundary
namespace LFunctions

noncomputable section

/-- Canonical scheduled carrier Cauchy data plus concrete autocorrelation
completed-log-derivative control construct the corrected pole-corrected common
limit. -/
theorem zetaCompletedAutocorrelationPoleCorrectedCommonLimit_of_canonicalScheduledCarrierCauchyData_concreteControl_final_owner
    (K : ZetaAdmissibleFunction → ℕ)
    (carrierData : CanonicalScheduledCarrierCauchyData K)
    (hConcrete :
      ZetaAdmissibleFunction.CompletedZetaNegLogDerivAutocorrelationConcreteControl) :
    ZetaCompletedAutocorrelationPoleCorrectedCommonLimit :=
  zetaCompletedAutocorrelationPoleCorrectedCommonLimit_of_canonicalScheduledHorizontalBounds_concreteControl_final_owner
    (fun f => carrierData.horizontalBounds f)
    hConcrete

/-- Canonical scheduled carrier Cauchy data plus split autocorrelation factor
controls construct the corrected pole-corrected common limit. -/
theorem zetaCompletedAutocorrelationPoleCorrectedCommonLimit_of_canonicalScheduledCarrierCauchyData_splitControls_final_owner
    (K : ZetaAdmissibleFunction → ℕ)
    (carrierData : CanonicalScheduledCarrierCauchyData K)
    (hZetaSide :
      ZetaAdmissibleFunction.CompletedZetaNegLogDerivAutocorrelationZetaSideControl)
    (hInverseGamma :
      ZetaAdmissibleFunction.CompletedZetaNegLogDerivAutocorrelationInverseGammaControl) :
    ZetaCompletedAutocorrelationPoleCorrectedCommonLimit :=
  zetaCompletedAutocorrelationPoleCorrectedCommonLimit_of_canonicalScheduledCarrierCauchyData_concreteControl_final_owner
    K
    carrierData
    (ZetaAdmissibleFunction.completedZetaNegLogDerivAutocorrelationConcreteControl_of_factorControls
      hZetaSide
      hInverseGamma)

/-- Canonical scheduled carrier Cauchy data plus global factor controls
construct the corrected pole-corrected common limit. -/
theorem zetaCompletedAutocorrelationPoleCorrectedCommonLimit_of_canonicalScheduledCarrierCauchyData_globalFactorControls_final_owner
    (K : ZetaAdmissibleFunction → ℕ)
    (carrierData : CanonicalScheduledCarrierCauchyData K)
    (hZetaSide :
      ZetaAdmissibleFunction.CompletedZetaNegLogDerivZetaSideControl)
    (hInverseGamma :
      ZetaAdmissibleFunction.CompletedZetaNegLogDerivInverseGammaControl) :
    ZetaCompletedAutocorrelationPoleCorrectedCommonLimit :=
  zetaCompletedAutocorrelationPoleCorrectedCommonLimit_of_canonicalScheduledCarrierCauchyData_splitControls_final_owner
    K
    carrierData
    (ZetaAdmissibleFunction.CompletedZetaNegLogDerivAutocorrelationZetaSideControl.ofZetaSideControl
      hZetaSide)
    (ZetaAdmissibleFunction.CompletedZetaNegLogDerivAutocorrelationInverseGammaControl.ofInverseGammaControl
      hInverseGamma)

/-- Canonical scheduled carrier Cauchy data plus concrete autocorrelation
completed-log-derivative control give final raw Weil positivity. -/
theorem zetaWeilQuadraticPositivity_of_canonicalScheduledCarrierCauchyData_concreteControl_final_owner
    (K : ZetaAdmissibleFunction → ℕ)
    (carrierData : CanonicalScheduledCarrierCauchyData K)
    (hConcrete :
      ZetaAdmissibleFunction.CompletedZetaNegLogDerivAutocorrelationConcreteControl) :
    ZetaWeilQuadraticPositivity :=
  zetaWeilQuadraticPositivity_of_finalCommonLimit_owner
    (zetaCompletedAutocorrelationPoleCorrectedCommonLimit_of_canonicalScheduledCarrierCauchyData_concreteControl_final_owner
      K
      carrierData
      hConcrete)

/-- Canonical scheduled carrier Cauchy data plus split autocorrelation factor
controls give final raw Weil positivity. -/
theorem zetaWeilQuadraticPositivity_of_canonicalScheduledCarrierCauchyData_splitControls_final_owner
    (K : ZetaAdmissibleFunction → ℕ)
    (carrierData : CanonicalScheduledCarrierCauchyData K)
    (hZetaSide :
      ZetaAdmissibleFunction.CompletedZetaNegLogDerivAutocorrelationZetaSideControl)
    (hInverseGamma :
      ZetaAdmissibleFunction.CompletedZetaNegLogDerivAutocorrelationInverseGammaControl) :
    ZetaWeilQuadraticPositivity :=
  zetaWeilQuadraticPositivity_of_finalCommonLimit_owner
    (zetaCompletedAutocorrelationPoleCorrectedCommonLimit_of_canonicalScheduledCarrierCauchyData_splitControls_final_owner
      K
      carrierData
      hZetaSide
      hInverseGamma)

/-- Canonical scheduled carrier Cauchy data plus global factor controls give
final raw Weil positivity. -/
theorem zetaWeilQuadraticPositivity_of_canonicalScheduledCarrierCauchyData_globalFactorControls_final_owner
    (K : ZetaAdmissibleFunction → ℕ)
    (carrierData : CanonicalScheduledCarrierCauchyData K)
    (hZetaSide :
      ZetaAdmissibleFunction.CompletedZetaNegLogDerivZetaSideControl)
    (hInverseGamma :
      ZetaAdmissibleFunction.CompletedZetaNegLogDerivInverseGammaControl) :
    ZetaWeilQuadraticPositivity :=
  zetaWeilQuadraticPositivity_of_finalCommonLimit_owner
    (zetaCompletedAutocorrelationPoleCorrectedCommonLimit_of_canonicalScheduledCarrierCauchyData_globalFactorControls_final_owner
      K
      carrierData
      hZetaSide
      hInverseGamma)

end

end LFunctions
end Boundary
