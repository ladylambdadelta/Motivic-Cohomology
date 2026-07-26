import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaZeroKreinGram.WeilCriterion.OwnerParts.CanonicalScheduledPolynomialPackageParts.FactorPathBounds

/-!
# Final common-limit canonical path-Cauchy data core

This file owns only the package of canonical scheduled path-Cauchy component
data.  It deliberately has no dependency on the final common-limit assembly.
-/

namespace Boundary
namespace LFunctions

noncomputable section

/-- Canonical scheduled path-Cauchy data, split into zeta-side and inverse-Gamma
factors, for each autocorrelation probe. -/
structure CanonicalScheduledPathCauchyData
    (K : ZetaAdmissibleFunction → ℕ) where
  zetaData :
    ∀ f : ZetaAdmissibleFunction,
      ZetaAdmissibleFunction.CanonicalScheduledZetaSideCauchyPathData
        f (K f)
  gammaData :
    ∀ f : ZetaAdmissibleFunction,
      ZetaAdmissibleFunction.CanonicalScheduledInverseGammaCauchyPathData
        f (K f)

/-- Component path-Cauchy data families assemble into the packaged final
path-Cauchy data object. -/
def CanonicalScheduledPathCauchyData.ofComponentData
    (K : ZetaAdmissibleFunction → ℕ)
    (zetaData :
      ∀ f : ZetaAdmissibleFunction,
        ZetaAdmissibleFunction.CanonicalScheduledZetaSideCauchyPathData
          f (K f))
    (gammaData :
      ∀ f : ZetaAdmissibleFunction,
        ZetaAdmissibleFunction.CanonicalScheduledInverseGammaCauchyPathData
          f (K f)) :
    CanonicalScheduledPathCauchyData K :=
  { zetaData := zetaData
    gammaData := gammaData }

/-- Component path-Cauchy data families assemble into the packaged final
path-Cauchy data object. -/
theorem canonicalScheduledPathCauchyData_of_componentData_owner
    (K : ZetaAdmissibleFunction → ℕ)
    (zetaData :
      ∀ f : ZetaAdmissibleFunction,
        ZetaAdmissibleFunction.CanonicalScheduledZetaSideCauchyPathData
          f (K f))
    (gammaData :
      ∀ f : ZetaAdmissibleFunction,
        ZetaAdmissibleFunction.CanonicalScheduledInverseGammaCauchyPathData
          f (K f)) :
    CanonicalScheduledPathCauchyData K :=
  CanonicalScheduledPathCauchyData.ofComponentData
    K
    zetaData
    gammaData

end

end LFunctions
end Boundary
