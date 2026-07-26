import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.OwnerParts.FinalCommonLimitCanonicalPathCauchyDataCore
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.OwnerParts.FinalCommonLimitCanonicalCauchyFactor

/-!
# Final common-limit canonical path-Cauchy data

This file owns the narrow final analytic input for the corrected centered RH
lane: Cauchy data only along the canonical scheduled top and bottom horizontal
paths.  It deliberately avoids the stronger separated-carrier hypothesis.
-/

namespace Boundary
namespace LFunctions

noncomputable section

/-- Carrier Cauchy data restricts to the canonical scheduled path-Cauchy
package. -/
def CanonicalScheduledPathCauchyData.ofCarrierCauchyData
    {K : ZetaAdmissibleFunction → ℕ}
    (carrierData : CanonicalScheduledCarrierCauchyData K) :
    CanonicalScheduledPathCauchyData K :=
  carrierData.pathData

/- Canonical path Cauchy data reconstructs the carrier package because the
   canonical carrier is exactly the union of its scheduled top and bottom
   paths. -/
def CanonicalScheduledPathCauchyData.toCarrierCauchyData
    {K : ZetaAdmissibleFunction → ℕ}
    (pathData : CanonicalScheduledPathCauchyData K) :
    CanonicalScheduledCarrierCauchyData K :=
  canonicalScheduledCarrierCauchyData_of_pathData_owner
    pathData.zetaData
    pathData.gammaData

/-- Packaged canonical scheduled path-Cauchy data gives scheduled polynomial
horizontal bounds. -/
def CanonicalScheduledPathCauchyData.horizontalBounds
    {K : ZetaAdmissibleFunction → ℕ}
    (pathData : CanonicalScheduledPathCauchyData K)
    (f : ZetaAdmissibleFunction) :
    ZetaAdmissibleFunction.CanonicalScheduledPolynomialHorizontalBounds f :=
  ZetaAdmissibleFunction.canonicalScheduledPolynomialHorizontalBounds_of_cauchyPathData_owner
    f
    (K f)
    (pathData.zetaData f)
    (pathData.gammaData f)

/-- The canonical path package exports the horizontal-bound family consumed by
the final common-limit owner. -/
def CanonicalScheduledPathCauchyData.horizontalBoundsFamily
    {K : ZetaAdmissibleFunction → ℕ}
    (pathData : CanonicalScheduledPathCauchyData K) :
    ∀ f : ZetaAdmissibleFunction,
      ZetaAdmissibleFunction.CanonicalScheduledPolynomialHorizontalBounds f :=
  fun f => pathData.horizontalBounds f

/-- Packaged canonical scheduled path-Cauchy data and affine packet data give
the final common-limit theorem. -/
theorem finalCommonLimit_of_canonicalScheduledPathCauchyData_packetData_owner
    (K : ZetaAdmissibleFunction → ℕ)
    (pathData : CanonicalScheduledPathCauchyData K)
    (packetData :
      ∀ f : ZetaAdmissibleFunction,
        ZetaAdmissibleFunction.ZetaCompletedAutocorrelationAffinePacketData f) :
    ZetaCompletedAutocorrelationPoleCorrectedCommonLimit :=
  zetaCompletedAutocorrelationPoleCorrectedCommonLimit_of_canonicalScheduledCauchyPathData_affinePacketData_final_owner
    K
    pathData.zetaData
    pathData.gammaData
    packetData

/-- Packaged canonical scheduled path-Cauchy data and affine packet data give
final raw Weil positivity. -/
theorem finalZetaWeilQuadraticPositivity_of_canonicalScheduledPathCauchyData_packetData_owner
    (K : ZetaAdmissibleFunction → ℕ)
    (pathData : CanonicalScheduledPathCauchyData K)
    (packetData :
      ∀ f : ZetaAdmissibleFunction,
        ZetaAdmissibleFunction.ZetaCompletedAutocorrelationAffinePacketData f) :
    ZetaWeilQuadraticPositivity :=
  zetaWeilQuadraticPositivity_of_finalCommonLimit_owner
    (finalCommonLimit_of_canonicalScheduledPathCauchyData_packetData_owner
      K
      pathData
      packetData)

/-- Variable-local canonical scheduled Cauchy data and affine packet data give
the final common-limit theorem. -/
theorem finalCommonLimit_of_canonicalScheduledVariableCauchyPathData_packetData_owner
    (K : ZetaAdmissibleFunction → ℕ)
    (zetaData :
      ∀ f : ZetaAdmissibleFunction,
        ZetaAdmissibleFunction.CanonicalScheduledZetaSideVariableCauchyPathData
          f (K f))
    (gammaData :
      ∀ f : ZetaAdmissibleFunction,
        ZetaAdmissibleFunction.CanonicalScheduledInverseGammaVariableCauchyPathData
          f (K f))
    (packetData :
      ∀ f : ZetaAdmissibleFunction,
        ZetaAdmissibleFunction.ZetaCompletedAutocorrelationAffinePacketData f) :
    ZetaCompletedAutocorrelationPoleCorrectedCommonLimit :=
  zetaCompletedAutocorrelationPoleCorrectedCommonLimit_of_canonicalScheduledVariableCauchyPathData_affinePacketData_final_owner
    K
    zetaData
    gammaData
    packetData

/-- Variable-local canonical scheduled Cauchy data and affine packet data give
final raw Weil positivity through the common-limit bridge. -/
theorem finalZetaWeilQuadraticPositivity_of_canonicalScheduledVariableCauchyPathData_packetData_owner
    (K : ZetaAdmissibleFunction → ℕ)
    (zetaData :
      ∀ f : ZetaAdmissibleFunction,
        ZetaAdmissibleFunction.CanonicalScheduledZetaSideVariableCauchyPathData
          f (K f))
    (gammaData :
      ∀ f : ZetaAdmissibleFunction,
        ZetaAdmissibleFunction.CanonicalScheduledInverseGammaVariableCauchyPathData
          f (K f))
    (packetData :
      ∀ f : ZetaAdmissibleFunction,
        ZetaAdmissibleFunction.ZetaCompletedAutocorrelationAffinePacketData f) :
    ZetaWeilQuadraticPositivity :=
  zetaWeilQuadraticPositivity_of_finalCommonLimit_owner
    (finalCommonLimit_of_canonicalScheduledVariableCauchyPathData_packetData_owner
      K
      zetaData
      gammaData
      packetData)

/-- Packaged canonical scheduled path-Cauchy data and concrete autocorrelation
log-derivative control give the final common-limit theorem. -/
theorem finalCommonLimit_of_canonicalScheduledPathCauchyData_concreteControl_owner
    (K : ZetaAdmissibleFunction → ℕ)
    (pathData : CanonicalScheduledPathCauchyData K)
    (hConcrete :
      ZetaAdmissibleFunction.CompletedZetaNegLogDerivAutocorrelationConcreteControl) :
    ZetaCompletedAutocorrelationPoleCorrectedCommonLimit :=
  finalCommonLimit_of_canonicalScheduledCauchyPathData_concreteControl_owner
    K
    pathData.zetaData
    pathData.gammaData
    hConcrete

/-- Packaged canonical scheduled path-Cauchy data and concrete autocorrelation
log-derivative control give final raw Weil positivity. -/
theorem finalZetaWeilQuadraticPositivity_of_canonicalScheduledPathCauchyData_concreteControl_owner
    (K : ZetaAdmissibleFunction → ℕ)
    (pathData : CanonicalScheduledPathCauchyData K)
    (hConcrete :
      ZetaAdmissibleFunction.CompletedZetaNegLogDerivAutocorrelationConcreteControl) :
    ZetaWeilQuadraticPositivity :=
  finalZetaWeilQuadraticPositivity_of_canonicalScheduledCauchyPathData_concreteControl_owner
    K
    pathData.zetaData
    pathData.gammaData
    hConcrete

/-- Carrier Cauchy data and concrete autocorrelation log-derivative control
give the final common-limit theorem through the path-Cauchy package. -/
theorem finalCommonLimit_of_canonicalScheduledCarrierCauchyData_pathConcreteControl_owner
    (K : ZetaAdmissibleFunction → ℕ)
    (carrierData : CanonicalScheduledCarrierCauchyData K)
    (hConcrete :
      ZetaAdmissibleFunction.CompletedZetaNegLogDerivAutocorrelationConcreteControl) :
    ZetaCompletedAutocorrelationPoleCorrectedCommonLimit :=
  finalCommonLimit_of_canonicalScheduledPathCauchyData_concreteControl_owner
    K
    carrierData.pathData
    hConcrete

/-- Carrier Cauchy data and concrete autocorrelation log-derivative control
give final raw Weil positivity through the path-Cauchy package. -/
theorem finalZetaWeilQuadraticPositivity_of_canonicalScheduledCarrierCauchyData_pathConcreteControl_owner
    (K : ZetaAdmissibleFunction → ℕ)
    (carrierData : CanonicalScheduledCarrierCauchyData K)
    (hConcrete :
      ZetaAdmissibleFunction.CompletedZetaNegLogDerivAutocorrelationConcreteControl) :
    ZetaWeilQuadraticPositivity :=
  finalZetaWeilQuadraticPositivity_of_canonicalScheduledPathCauchyData_concreteControl_owner
    K
    carrierData.pathData
    hConcrete

/-- Packaged canonical scheduled path-Cauchy data and global completed-log-
derivative factor controls give the final common-limit theorem. -/
theorem finalCommonLimit_of_canonicalScheduledPathCauchyData_globalFactorControls_owner
    (K : ZetaAdmissibleFunction → ℕ)
    (pathData : CanonicalScheduledPathCauchyData K)
    (hZetaSide :
      ZetaAdmissibleFunction.CompletedZetaNegLogDerivZetaSideControl)
    (hInverseGamma :
      ZetaAdmissibleFunction.CompletedZetaNegLogDerivInverseGammaControl) :
    ZetaCompletedAutocorrelationPoleCorrectedCommonLimit :=
  finalCommonLimit_of_canonicalScheduledCauchyPathData_globalFactorControls_owner
    K
    pathData.zetaData
    pathData.gammaData
    hZetaSide
    hInverseGamma

/-- Packaged canonical scheduled path-Cauchy data and global completed-log-
derivative factor controls give final raw Weil positivity. -/
theorem finalZetaWeilQuadraticPositivity_of_canonicalScheduledPathCauchyData_globalFactorControls_owner
    (K : ZetaAdmissibleFunction → ℕ)
    (pathData : CanonicalScheduledPathCauchyData K)
    (hZetaSide :
      ZetaAdmissibleFunction.CompletedZetaNegLogDerivZetaSideControl)
    (hInverseGamma :
      ZetaAdmissibleFunction.CompletedZetaNegLogDerivInverseGammaControl) :
    ZetaWeilQuadraticPositivity :=
  finalZetaWeilQuadraticPositivity_of_canonicalScheduledCauchyPathData_globalFactorControls_owner
    K
    pathData.zetaData
    pathData.gammaData
    hZetaSide
    hInverseGamma

/-- Carrier Cauchy data and global completed-log-derivative factor controls
give the final common-limit theorem through the path-Cauchy package. -/
theorem finalCommonLimit_of_canonicalScheduledCarrierCauchyData_pathGlobalFactorControls_owner
    (K : ZetaAdmissibleFunction → ℕ)
    (carrierData : CanonicalScheduledCarrierCauchyData K)
    (hZetaSide :
      ZetaAdmissibleFunction.CompletedZetaNegLogDerivZetaSideControl)
    (hInverseGamma :
      ZetaAdmissibleFunction.CompletedZetaNegLogDerivInverseGammaControl) :
    ZetaCompletedAutocorrelationPoleCorrectedCommonLimit :=
  finalCommonLimit_of_canonicalScheduledPathCauchyData_globalFactorControls_owner
    K
    carrierData.pathData
    hZetaSide
    hInverseGamma

/-- Carrier Cauchy data and global completed-log-derivative factor controls
give final raw Weil positivity through the path-Cauchy package. -/
theorem finalZetaWeilQuadraticPositivity_of_canonicalScheduledCarrierCauchyData_pathGlobalFactorControls_owner
    (K : ZetaAdmissibleFunction → ℕ)
    (carrierData : CanonicalScheduledCarrierCauchyData K)
    (hZetaSide :
      ZetaAdmissibleFunction.CompletedZetaNegLogDerivZetaSideControl)
    (hInverseGamma :
      ZetaAdmissibleFunction.CompletedZetaNegLogDerivInverseGammaControl) :
    ZetaWeilQuadraticPositivity :=
  finalZetaWeilQuadraticPositivity_of_canonicalScheduledPathCauchyData_globalFactorControls_owner
    K
    carrierData.pathData
    hZetaSide
    hInverseGamma

end

end LFunctions
end Boundary
