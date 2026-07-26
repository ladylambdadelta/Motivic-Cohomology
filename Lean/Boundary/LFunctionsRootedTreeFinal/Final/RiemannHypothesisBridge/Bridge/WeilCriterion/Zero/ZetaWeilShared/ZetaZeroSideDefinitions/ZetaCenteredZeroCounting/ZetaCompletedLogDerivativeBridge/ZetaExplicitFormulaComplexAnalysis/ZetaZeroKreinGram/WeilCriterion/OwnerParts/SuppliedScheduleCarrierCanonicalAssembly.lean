import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaZeroKreinGram.WeilCriterion.OwnerParts.CauchyPathCarrierDataPackage
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaZeroKreinGram.WeilCriterion.OwnerParts.SuppliedScheduleCarrierBoundary

/-!
# Canonical carrier assembly through the supplied-schedule route

This owner part connects canonical carrier Cauchy data to the supplied-schedule
positivity route.  The theorem keeps the quantitative carrier construction and
the affine packet construction as separate named inputs.
-/

namespace Boundary
namespace LFunctions

noncomputable section

/-- Canonical carrier Cauchy data, canonical schedule separation, and global
factor controls give raw Weil positivity through the supplied-schedule route. -/
theorem zetaWeilQuadraticPositivity_of_canonicalScheduledCarrierCauchyPackage_suppliedSchedule_globalFactorControls_traceBessel_owner
    (K : ZetaAdmissibleFunction → ℕ)
    (carrierData : CanonicalScheduledCarrierCauchyData K)
    (separated :
      ∀ f : ZetaAdmissibleFunction,
        (ZetaAdmissibleFunction.zetaCompletedExplicitFormulaAutocorrelationScheduledHorizontalCarrier
          f).HasPositiveSingularSeparation)
    (hPhi :
      ∀ f : ZetaAdmissibleFunction,
        ZetaAdmissibleFunction.ZetaPhiAnalyticControl
          (ZetaAdmissibleFunction.convolutionAutocorrelation f))
    (hZetaSide :
      ZetaAdmissibleFunction.CompletedZetaNegLogDerivZetaSideControl)
    (hInverseGamma :
      ZetaAdmissibleFunction.CompletedZetaNegLogDerivInverseGammaControl) :
    ZetaWeilQuadraticPositivity :=
  zetaWeilQuadraticPositivity_of_suppliedCarrierFamily_globalFactorControls_traceBessel_owner
    (carrierData.toSuppliedScheduleFamily separated hPhi)
    hZetaSide
    hInverseGamma

/-- Canonical carrier Cauchy data, canonical schedule separation, and concrete
Phi control give raw Weil positivity through the supplied-schedule route. -/
theorem zetaWeilQuadraticPositivity_of_canonicalScheduledCarrierCauchyPackage_suppliedSchedule_canonicalPhi_globalFactorControls_traceBessel_owner
    (K : ZetaAdmissibleFunction → ℕ)
    (carrierData : CanonicalScheduledCarrierCauchyData K)
    (separated :
      ∀ f : ZetaAdmissibleFunction,
        (ZetaAdmissibleFunction.zetaCompletedExplicitFormulaAutocorrelationScheduledHorizontalCarrier
          f).HasPositiveSingularSeparation)
    (hZetaSide :
      ZetaAdmissibleFunction.CompletedZetaNegLogDerivZetaSideControl)
    (hInverseGamma :
      ZetaAdmissibleFunction.CompletedZetaNegLogDerivInverseGammaControl) :
    ZetaWeilQuadraticPositivity :=
  zetaWeilQuadraticPositivity_of_canonicalScheduledCarrierCauchyPackage_suppliedSchedule_globalFactorControls_traceBessel_owner
    K
    carrierData
    separated
    (ZetaAdmissibleFunction.zetaPhiAnalyticControl_autocorrelation_of_concreteControl
      ZetaAdmissibleFunction.zetaPhiAutocorrelationConcreteControl_owner)
    hZetaSide
    hInverseGamma

end

end LFunctions
end Boundary
