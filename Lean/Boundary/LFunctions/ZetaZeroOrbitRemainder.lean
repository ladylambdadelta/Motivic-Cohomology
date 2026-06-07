import Boundary.LFunctions.ZetaZeroTail

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

end
end LFunctions
end Boundary
