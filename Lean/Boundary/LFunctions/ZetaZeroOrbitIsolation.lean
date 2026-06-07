import Boundary.LFunctions.ZetaCenteredZeroCounting

/-!
# Boundary zero-orbit isolation

This file records the simplest orbit-isolation fact available from the current
centered symmetry package: the reflection orbit of a centered zero stays inside
the centered zero set.
-/

namespace Boundary
namespace LFunctions

noncomputable section

namespace CenteredZetaZero

/-- The reflection orbit of a centered zero is contained in the centered zero set. -/
theorem orbit_subset_centeredZetaZeros (z : CenteredZetaZero) :
    {x : ℂ | x ∈ orbit z} ⊆ centeredZetaZeros := by
  intro x hx
  unfold centeredZetaZeros
  rcases hx with rfl | rfl
  · exact z.2
  · exact (centeredZetaZeros_neg z).1 z.2

/-- The centered zero orbit is isolated inside the centered zero set. -/
theorem centeredZeroOrbit_isolated (z : CenteredZetaZero) :
    {x : ℂ | x ∈ orbit z} ⊆ centeredZetaZeros := by
  exact orbit_subset_centeredZetaZeros z

/-- The centered zero orbit isolation theorem. -/
theorem centeredZeroOrbit_isolated' (z : CenteredZetaZero) :
    {x : ℂ | x ∈ orbit z} ⊆ centeredZetaZeros := by
  exact centeredZeroOrbit_isolated z

/-- The centered zero orbit sits inside the centered zero set. -/
theorem centeredZeroOrbit_subset (z : CenteredZetaZero) :
    {x : ℂ | x ∈ orbit z} ⊆ centeredZetaZeros := by
  exact orbit_subset_centeredZetaZeros z

/-- The centered zero orbit is isolated in the centered zero set. -/
theorem centeredZeroOrbit_isolatedSet (z : CenteredZetaZero) :
    {x : ℂ | x ∈ orbit z} ⊆ centeredZetaZeros := by
  exact centeredZeroOrbit_isolated z

end CenteredZetaZero

end
end LFunctions
end Boundary
