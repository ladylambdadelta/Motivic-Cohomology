import Boundary.LFunctions.ZetaZeroTail
import Boundary.LFunctions.ZetaWeilShared

/-!
# Boundary zero-side orbit remainder

This file packages the orbit remainder as the tail specialized to the orbit of
the chosen zero.
-/

namespace Boundary
namespace LFunctions

noncomputable section

/-- The orbit remainder is the tail after removing the orbit of the chosen zero. -/
theorem zetaZeroOrbitRemainder_eq
    (ρ : ℂ) (φ : ZetaAdmissibleFunction) :
    zetaZeroOrbitRemainder ρ φ =
      zetaZeroTail (zetaZeroOrbitFinset ρ) φ := by
  rfl

/-- The real-valued orbit remainder is the real part of the complex one. -/
theorem zetaZeroOrbitRemainderRe_eq
    (ρ : ℂ) (φ : ZetaAdmissibleFunction) :
    zetaZeroOrbitRemainderRe ρ φ =
      Complex.re (zetaZeroOrbitRemainder ρ φ) := by
  rfl

/-- The completed zero-side real scalar splits into the chosen finite zero orbit and the
complementary orbit remainder.

This is the zero-side owner decomposition: after a finite functional-equation orbit has been
isolated, the completed zero-side `tsum` is the finite orbit contribution plus the tail over
all remaining zeros. -/
theorem zetaCompletedZeroSideRe_eq_orbitContribution_add_orbitRemainderRe
    (ρ : ℂ) (φ : ZetaAdmissibleFunction)
    (hρ : ZetaCompletedZero ρ)
    (horbit : ∀ η : ℂ, η ∈ zetaZeroOrbitFinset ρ → ZetaCompletedZero η) :
    zetaCompletedZeroSideRe φ =
      zetaZeroOrbitContributionRe ρ φ + zetaZeroOrbitRemainderRe ρ φ := by
  sorry

end
end LFunctions
end Boundary
