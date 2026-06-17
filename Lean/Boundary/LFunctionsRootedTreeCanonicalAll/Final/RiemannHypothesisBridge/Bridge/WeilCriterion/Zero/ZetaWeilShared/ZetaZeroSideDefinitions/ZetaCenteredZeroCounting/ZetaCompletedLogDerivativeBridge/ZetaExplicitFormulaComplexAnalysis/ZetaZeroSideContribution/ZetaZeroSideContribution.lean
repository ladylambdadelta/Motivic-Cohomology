import Boundary.LFunctionsRootedTreeCanonicalAll.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaZeroSideDefinitions

/-!
# Boundary zero-side contribution

This file packages the single-zero contribution surface and keeps downstream
files attached to the owner definitions.
-/

namespace Boundary
namespace LFunctions

noncomputable section

/-- The zero-side contribution is the signed multiplicity-weighted spectral evaluation. -/
theorem zetaZeroSideContribution_eq
    (ρ : ℂ) (φ : ZetaAdmissibleFunction) :
    zetaZeroSideContribution ρ φ =
      - (zetaZeroMultiplicity ρ : ℂ) * zetaSpectralEval φ (zetaCenteredZero ρ) := by
  rfl

/-- The real-valued zero-side contribution is the real part of the complex one. -/
theorem zetaZeroSideContributionRe_eq
    (ρ : ℂ) (φ : ZetaAdmissibleFunction) :
    zetaZeroSideContributionRe ρ φ =
      Complex.re (zetaZeroSideContribution ρ φ) := by
  rfl

end
end LFunctions
end Boundary
