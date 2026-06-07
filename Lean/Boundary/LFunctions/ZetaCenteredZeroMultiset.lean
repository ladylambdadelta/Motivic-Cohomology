import Boundary.LFunctions.ZetaCenteredZeroOrbit

/-!
# Boundary centered zeta zero multiset

This file packages the finite reflection orbit of a centered zeta zero as a
multiset.
-/

namespace Boundary
namespace LFunctions

noncomputable section

namespace CenteredZetaZero

/-- The reflection orbit of a centered zeta zero as a multiset. -/
def orbitMultiset (z : CenteredZetaZero) : Multiset ℂ := {z, -z}

theorem mem_orbitMultiset_left (z : CenteredZetaZero) : (z : ℂ) ∈ orbitMultiset z := by
  decide

theorem mem_orbitMultiset_right (z : CenteredZetaZero) : (-z : ℂ) ∈ orbitMultiset z := by
  decide

/-- The orbit multiset is stable under reflection. -/
theorem orbitMultiset_neg (z : CenteredZetaZero) :
    orbitMultiset z = {(-z : ℂ), (z : ℂ)} := by
  rfl

/-- The orbit multiset is the reflection pair. -/
theorem orbitMultiset_eq (z : CenteredZetaZero) :
    orbitMultiset z = {z, -z} := by
  rfl

end CenteredZetaZero

end
end LFunctions
end Boundary
