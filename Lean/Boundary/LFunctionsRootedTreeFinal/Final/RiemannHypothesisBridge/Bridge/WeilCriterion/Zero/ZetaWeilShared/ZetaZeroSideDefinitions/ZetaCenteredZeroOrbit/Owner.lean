import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZero.Owner
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

theorem orbit_mem_iff_left (z : CenteredZetaZero) {x : ℂ} :
    x ∈ orbit z → x = (z : ℂ) ∨ x = -z := by
  intro hx
  change x ∈ insert (z : ℂ) ({(-z : ℂ)} : Finset ℂ) at hx
  rcases Finset.mem_insert.mp hx with rfl | hx'
  · exact Or.inl rfl
  · have hx'' : x = -z := by
      change x ∈ ({(-z : ℂ)} : Finset ℂ) at hx'
      exact Finset.mem_singleton.mp hx'
    exact Or.inr hx''

theorem orbit_mem_iff_right (z : CenteredZetaZero) {x : ℂ} :
    x = (z : ℂ) ∨ x = -z → x ∈ orbit z := by
  intro hx
  rcases hx with rfl | rfl
  · exact Finset.mem_insert_self _ _
  · have hmem : (-z : ℂ) ∈ ({(-z : ℂ)} : Finset ℂ) := by
      exact Finset.mem_singleton_self (-z : ℂ)
    exact Finset.mem_insert_of_mem hmem

theorem orbit_mem_iff (z : CenteredZetaZero) {x : ℂ} :
    x ∈ orbit z ↔ x = (z : ℂ) ∨ x = -z := by
  constructor
  · exact orbit_mem_iff_left z
  · exact orbit_mem_iff_right z

theorem mem_orbit_left (z : CenteredZetaZero) : (z : ℂ) ∈ orbit z := by
  exact orbit_mem_iff_right z (Or.inl rfl)

theorem mem_orbit_right (z : CenteredZetaZero) : (-z : ℂ) ∈ orbit z := by
  exact orbit_mem_iff_right z (Or.inr rfl)

theorem orbit_finite (z : CenteredZetaZero) : ({x : ℂ | x ∈ orbit z}.Finite) := by
  exact Set.Finite.ofFinset (orbit z) (by
    intro x
    constructor <;> intro hx <;> exact hx)

/-- The orbit of a centered zero is stable under negation. -/
theorem orbit_neg (z : CenteredZetaZero) :
    (-z : ℂ) ∈ orbit z ∧ (z : ℂ) ∈ orbit z := by
  constructor
  · exact mem_orbit_right z
  · exact mem_orbit_left z

/-- The orbit of a centered zero is a two-point finset. -/
theorem orbit_card_le_two (z : CenteredZetaZero) : (orbit z).card ≤ 2 := by
  exact Finset.card_le_two (a := (z : ℂ)) (b := (-z : ℂ))

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
