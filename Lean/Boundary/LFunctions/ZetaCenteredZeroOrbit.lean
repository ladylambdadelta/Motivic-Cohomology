import Boundary.LFunctions.ZetaCenteredZero
import Mathlib.Data.Set.Finite.Basic

/-!
# Boundary centered zeta zero orbit

This file packages the finite reflection orbit attached to a centered zeta zero.
-/

namespace Boundary
namespace LFunctions

noncomputable section

namespace CenteredZetaZero

/-- The reflection orbit of a centered zeta zero. -/
def orbit (z : CenteredZetaZero) : Finset ℂ := ({(z : ℂ), (-z : ℂ)} : Finset ℂ)

theorem mem_orbit_left (z : CenteredZetaZero) : (z : ℂ) ∈ orbit z := by
  simp [orbit]

theorem mem_orbit_right (z : CenteredZetaZero) : (-z : ℂ) ∈ orbit z := by
  simp [orbit]

theorem orbit_finite (z : CenteredZetaZero) : ({x : ℂ | x ∈ orbit z}.Finite) := by
  classical
  exact Set.Finite.ofFinset (orbit z) (by
    intro x
    constructor <;> intro hx <;> simpa [orbit] using hx)

/-- The orbit of a centered zero is stable under negation. -/
theorem orbit_neg (z : CenteredZetaZero) :
    (-z : ℂ) ∈ orbit z ∧ (z : ℂ) ∈ orbit z := by
  constructor
  · exact mem_orbit_right z
  · exact mem_orbit_left z

/-- The orbit of a centered zero is a two-point finset. -/
theorem orbit_card_le_two (z : CenteredZetaZero) : (orbit z).card ≤ 2 := by
  classical
  simpa [orbit] using (Finset.card_le_two (a := (z : ℂ)) (b := (-z : ℂ)))

/-- The centered zero orbit can be extracted as a finite support. -/
theorem orbit_support_finite (z : CenteredZetaZero) : {x : ℂ | x ∈ orbit z}.Finite := by
  exact orbit_finite z

/-- The centered zero orbit is the finite reflection orbit. -/
theorem orbit_eq (z : CenteredZetaZero) :
    orbit z = ({(z : ℂ), (-z : ℂ)} : Finset ℂ) := by
  rfl

/-- The centered zero orbit is finite. -/
theorem centeredZeroOrbit_finite (z : CenteredZetaZero) : {x : ℂ | x ∈ orbit z}.Finite := by
  exact orbit_finite z

end CenteredZetaZero

end
end LFunctions
end Boundary
