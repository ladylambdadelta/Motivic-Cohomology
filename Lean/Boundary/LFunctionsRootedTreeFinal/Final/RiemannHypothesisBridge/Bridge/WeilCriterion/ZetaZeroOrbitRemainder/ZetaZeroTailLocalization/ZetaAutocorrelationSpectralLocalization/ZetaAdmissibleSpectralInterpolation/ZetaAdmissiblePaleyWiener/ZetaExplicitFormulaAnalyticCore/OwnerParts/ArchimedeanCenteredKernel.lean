import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaAdmissibleSpectralInterpolation.ZetaAdmissiblePaleyWiener.ZetaExplicitFormulaAnalyticCore.OwnerParts.PrimePowerCoordinates

/-!
# Centered archimedean kernel

This file owns the Gamma-factor distribution on the critical spectral line.
Contour shifts and Binet expansions are representations of this kernel and do
not replace it by a transform value at one point.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open Complex
open MeasureTheory

namespace ZetaAdmissibleFunction

/-- The critical spectral line in centered transform coordinates. -/
noncomputable def zetaCompletedCenteredSpectralLine (t : ℝ) : ℂ :=
  (1 / 2 : ℂ) + t * Complex.I

/-- The logarithmic derivative kernel contributed by the completed real Gamma
factor after removal of the elementary poles at zero and one. -/
noncomputable def zetaCompletedArchimedeanLogDerivativeKernel (s : ℂ) : ℂ :=
  deriv (fun w : ℂ => (Complex.Gammaℝ w)⁻¹) s /
      (Complex.Gammaℝ s)⁻¹ -
    (-1 / s - 1 / (s - 1))

/-- The centered archimedean spectral integrand. -/
noncomputable def zetaCompletedArchimedeanCenteredIntegrand
    (f : ZetaAdmissibleFunction) (t : ℝ) : ℂ :=
  zetaCompletedArchimedeanLogDerivativeKernel
      (zetaCompletedCenteredSpectralLine t) *
    zetaCompletedExplicitFormulaPhi f (t * Complex.I)

/-- The centered integrand unfolds without contour or Binet data. -/
theorem zetaCompletedArchimedeanCenteredIntegrand_eq
    (f : ZetaAdmissibleFunction) (t : ℝ) :
    zetaCompletedArchimedeanCenteredIntegrand f t =
      zetaCompletedArchimedeanLogDerivativeKernel
          ((1 / 2 : ℂ) + t * Complex.I) *
        zetaCompletedExplicitFormulaPhi f (t * Complex.I) := by
  exact Eq.refl (zetaCompletedArchimedeanCenteredIntegrand f t)

end ZetaAdmissibleFunction

end
end LFunctions
end Boundary
