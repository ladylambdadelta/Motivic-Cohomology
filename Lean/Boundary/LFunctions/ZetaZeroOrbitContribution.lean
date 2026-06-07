import Boundary.LFunctions.ZetaZeroSideContribution

/-!
# Boundary zero-side orbit contribution

This file packages the orbit-level contribution as a consumer of the single
zero-side contribution definitions.
-/

namespace Boundary
namespace LFunctions

noncomputable section

/-- The orbit contribution is the finite sum over the reflection orbit. -/
theorem zetaZeroOrbitContribution_eq
    (ρ : ℂ) (φ : ZetaAdmissibleFunction) :
    zetaZeroOrbitContribution ρ φ =
      Finset.sum (zetaZeroOrbitFinset ρ) (fun η => zetaZeroSideContribution η φ) := by
  rfl

/-- The real-valued orbit contribution is the real part of the complex one. -/
theorem zetaZeroOrbitContributionRe_eq
    (ρ : ℂ) (φ : ZetaAdmissibleFunction) :
    zetaZeroOrbitContributionRe ρ φ =
      Complex.re (zetaZeroOrbitContribution ρ φ) := by
  rfl

end
end LFunctions
end Boundary
