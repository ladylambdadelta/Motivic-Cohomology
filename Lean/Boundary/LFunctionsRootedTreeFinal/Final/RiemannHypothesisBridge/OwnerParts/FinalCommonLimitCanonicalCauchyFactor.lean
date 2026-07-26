import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaZeroKreinGram.WeilCriterion.OwnerParts.FinalCarrierCauchyConcreteAssembly
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaZeroKreinGram.WeilCriterion.OwnerParts.FinalCommonLimitFromFactorData

/-!
# Final common-limit canonical Cauchy-factor route

This file exposes the same canonical scheduled-carrier Cauchy-factor input used
by the packet RH route as a direct source of the final common-limit theorem.
-/

namespace Boundary
namespace LFunctions

noncomputable section

/-- Packaged canonical scheduled-carrier Cauchy data and concrete
autocorrelation log-derivative control give the final common-limit theorem. -/
theorem finalCommonLimit_of_canonicalScheduledCarrierCauchyData_concreteControl_owner
    (K : ZetaAdmissibleFunction → ℕ)
    (carrierData : CanonicalScheduledCarrierCauchyData K)
    (hConcrete :
      ZetaAdmissibleFunction.CompletedZetaNegLogDerivAutocorrelationConcreteControl) :
    ZetaCompletedAutocorrelationPoleCorrectedCommonLimit :=
  zetaCompletedAutocorrelationPoleCorrectedCommonLimit_of_canonicalScheduledCarrierCauchyData_concreteControl_final_owner
    K
    carrierData
    hConcrete

/-- Packaged canonical scheduled-carrier Cauchy data and concrete
autocorrelation log-derivative control give final raw Weil positivity. -/
theorem finalZetaWeilQuadraticPositivity_of_canonicalScheduledCarrierCauchyData_concreteControl_owner
    (K : ZetaAdmissibleFunction → ℕ)
    (carrierData : CanonicalScheduledCarrierCauchyData K)
    (hConcrete :
      ZetaAdmissibleFunction.CompletedZetaNegLogDerivAutocorrelationConcreteControl) :
    ZetaWeilQuadraticPositivity :=
  zetaWeilQuadraticPositivity_of_finalCommonLimit_owner
    (finalCommonLimit_of_canonicalScheduledCarrierCauchyData_concreteControl_owner
      K
      carrierData
      hConcrete)

/-- Canonical scheduled path Cauchy data and concrete autocorrelation
log-derivative control give the final common-limit theorem.

This is the direct centered repair: it uses only the top/bottom scheduled
path estimates and does not ask for positive separation of the whole scheduled
horizontal carrier. -/
theorem finalCommonLimit_of_canonicalScheduledCauchyPathData_concreteControl_owner
    (K : ZetaAdmissibleFunction → ℕ)
    (zetaData :
      ∀ f : ZetaAdmissibleFunction,
        ZetaAdmissibleFunction.CanonicalScheduledZetaSideCauchyPathData
          f (K f))
    (gammaData :
      ∀ f : ZetaAdmissibleFunction,
        ZetaAdmissibleFunction.CanonicalScheduledInverseGammaCauchyPathData
          f (K f))
    (hConcrete :
      ZetaAdmissibleFunction.CompletedZetaNegLogDerivAutocorrelationConcreteControl) :
    ZetaCompletedAutocorrelationPoleCorrectedCommonLimit :=
  zetaCompletedAutocorrelationPoleCorrectedCommonLimit_of_canonicalScheduledCauchyPathData_concreteControl_final_owner
    K
    zetaData
    gammaData
    hConcrete

/-- Canonical scheduled path Cauchy data and concrete autocorrelation
log-derivative control give final raw Weil positivity, without any
whole-carrier separation hypothesis. -/
theorem finalZetaWeilQuadraticPositivity_of_canonicalScheduledCauchyPathData_concreteControl_owner
    (K : ZetaAdmissibleFunction → ℕ)
    (zetaData :
      ∀ f : ZetaAdmissibleFunction,
        ZetaAdmissibleFunction.CanonicalScheduledZetaSideCauchyPathData
          f (K f))
    (gammaData :
      ∀ f : ZetaAdmissibleFunction,
        ZetaAdmissibleFunction.CanonicalScheduledInverseGammaCauchyPathData
          f (K f))
    (hConcrete :
      ZetaAdmissibleFunction.CompletedZetaNegLogDerivAutocorrelationConcreteControl) :
    ZetaWeilQuadraticPositivity :=
  zetaWeilQuadraticPositivity_of_finalCommonLimit_owner
    (finalCommonLimit_of_canonicalScheduledCauchyPathData_concreteControl_owner
      K
      zetaData
      gammaData
      hConcrete)

/-- Canonical scheduled path Cauchy data and global completed-log-derivative
factor controls give the final common-limit theorem. -/
theorem finalCommonLimit_of_canonicalScheduledCauchyPathData_globalFactorControls_owner
    (K : ZetaAdmissibleFunction → ℕ)
    (zetaData :
      ∀ f : ZetaAdmissibleFunction,
        ZetaAdmissibleFunction.CanonicalScheduledZetaSideCauchyPathData
          f (K f))
    (gammaData :
      ∀ f : ZetaAdmissibleFunction,
        ZetaAdmissibleFunction.CanonicalScheduledInverseGammaCauchyPathData
          f (K f))
    (hZetaSide :
      ZetaAdmissibleFunction.CompletedZetaNegLogDerivZetaSideControl)
    (hInverseGamma :
      ZetaAdmissibleFunction.CompletedZetaNegLogDerivInverseGammaControl) :
    ZetaCompletedAutocorrelationPoleCorrectedCommonLimit :=
  zetaCompletedAutocorrelationPoleCorrectedCommonLimit_of_canonicalScheduledCauchyPathData_globalFactorControls_final_owner
    K
    zetaData
    gammaData
    hZetaSide
    hInverseGamma

/-- Canonical scheduled path Cauchy data and global completed-log-derivative
factor controls give final raw Weil positivity. -/
theorem finalZetaWeilQuadraticPositivity_of_canonicalScheduledCauchyPathData_globalFactorControls_owner
    (K : ZetaAdmissibleFunction → ℕ)
    (zetaData :
      ∀ f : ZetaAdmissibleFunction,
        ZetaAdmissibleFunction.CanonicalScheduledZetaSideCauchyPathData
          f (K f))
    (gammaData :
      ∀ f : ZetaAdmissibleFunction,
        ZetaAdmissibleFunction.CanonicalScheduledInverseGammaCauchyPathData
          f (K f))
    (hZetaSide :
      ZetaAdmissibleFunction.CompletedZetaNegLogDerivZetaSideControl)
    (hInverseGamma :
      ZetaAdmissibleFunction.CompletedZetaNegLogDerivInverseGammaControl) :
    ZetaWeilQuadraticPositivity :=
  zetaWeilQuadraticPositivity_of_finalCommonLimit_owner
    (finalCommonLimit_of_canonicalScheduledCauchyPathData_globalFactorControls_owner
      K
      zetaData
      gammaData
      hZetaSide
      hInverseGamma)

/-- Packaged canonical scheduled-carrier Cauchy data and global factor controls
give the final common-limit theorem. -/
theorem finalCommonLimit_of_canonicalScheduledCarrierCauchyData_globalFactorControls_owner
    (K : ZetaAdmissibleFunction → ℕ)
    (carrierData : CanonicalScheduledCarrierCauchyData K)
    (hZetaSide :
      ZetaAdmissibleFunction.CompletedZetaNegLogDerivZetaSideControl)
    (hInverseGamma :
      ZetaAdmissibleFunction.CompletedZetaNegLogDerivInverseGammaControl) :
    ZetaCompletedAutocorrelationPoleCorrectedCommonLimit :=
  zetaCompletedAutocorrelationPoleCorrectedCommonLimit_of_canonicalScheduledCarrierCauchyData_globalFactorControls_final_owner
    K
    carrierData
    hZetaSide
    hInverseGamma

/-- Packaged canonical scheduled-carrier Cauchy data and global factor controls
give final raw Weil positivity. -/
theorem finalZetaWeilQuadraticPositivity_of_canonicalScheduledCarrierCauchyData_globalFactorControls_owner
    (K : ZetaAdmissibleFunction → ℕ)
    (carrierData : CanonicalScheduledCarrierCauchyData K)
    (hZetaSide :
      ZetaAdmissibleFunction.CompletedZetaNegLogDerivZetaSideControl)
    (hInverseGamma :
      ZetaAdmissibleFunction.CompletedZetaNegLogDerivInverseGammaControl) :
    ZetaWeilQuadraticPositivity :=
  zetaWeilQuadraticPositivity_of_finalCommonLimit_owner
    (finalCommonLimit_of_canonicalScheduledCarrierCauchyData_globalFactorControls_owner
      K
      carrierData
      hZetaSide
      hInverseGamma)

end

end LFunctions
end Boundary
