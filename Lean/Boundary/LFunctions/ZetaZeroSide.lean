import Boundary.LFunctions.ZetaZeroSideDefinitions

/-!
# Boundary zero-side package

This file packages the centered zero locus and its finite reflection orbit as
the current zero-side data surface for the explicit-formula route.
-/

namespace Boundary
namespace LFunctions

noncomputable section

/-- The current zero-side package is the centered zero locus. -/
def zetaZeroSide : Set ℂ := centeredZetaZeros

theorem zetaZeroSide_neg (z : ℂ) :
    z ∈ zetaZeroSide ↔ -z ∈ zetaZeroSide := by
  exact centeredZetaZeros_neg z

/-- The zero-side set is reflection stable. -/
theorem zetaZeroSide_reflect (z : ℂ) : z ∈ zetaZeroSide → -z ∈ zetaZeroSide := by
  intro hz
  exact (zetaZeroSide_neg z).1 hz

/-- The zero-side package is exactly the centered zero locus. -/
theorem zetaZeroSide_eq_centeredZetaZeros : zetaZeroSide = centeredZetaZeros := by
  rfl

/-- The zero-side package is reflection-stable. -/
theorem zetaZeroSide_stable (z : ℂ) : z ∈ zetaZeroSide → -z ∈ zetaZeroSide := by
  exact zetaZeroSide_reflect z

/-- The zero-side package is the centered zero package. -/
theorem zetaZeroSide_centered (z : ℂ) :
    z ∈ zetaZeroSide ↔ centeredCompletedRiemannZeta z = 0 := by
  rfl

end
end LFunctions
end Boundary
