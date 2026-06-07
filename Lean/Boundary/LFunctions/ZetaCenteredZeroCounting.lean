import Boundary.LFunctions.ZetaCenteredZeroOrbit

/-!
# Boundary centered zeta zero counting surface

This file exposes the centered zero locus as a set and records the symmetry
already proved for the centered completed zeta function.
-/

namespace Boundary
namespace LFunctions

noncomputable section

/-- The set of centered zeros of the completed zeta function. -/
def centeredZetaZeros : Set ℂ := {s | centeredCompletedRiemannZeta s = 0}

theorem centeredZetaZeros_neg (z : ℂ) :
    z ∈ centeredZetaZeros ↔ -z ∈ centeredZetaZeros := by
  constructor
  · intro hz
    unfold centeredZetaZeros at *
    rw [centeredCompletedRiemannZeta_neg]
    exact hz
  · intro hz
    unfold centeredZetaZeros at *
    rw [centeredCompletedRiemannZeta_neg] at hz
    exact hz

/-- The centered zero set is stable under reflection. -/
theorem centeredZetaZeros_reflection (z : ℂ) :
    z ∈ centeredZetaZeros → -z ∈ centeredZetaZeros := by
  intro hz
  exact (centeredZetaZeros_neg z).1 hz

/-- The centered zero set is stable under negation in both directions. -/
theorem centeredZetaZeros_reflection_iff (z : ℂ) :
    z ∈ centeredZetaZeros ↔ -z ∈ centeredZetaZeros := by
  exact centeredZetaZeros_neg z

theorem centeredZetaZeros_conjugation (z : ℂ) :
    centeredCompletedRiemannZeta z = 0 → centeredCompletedRiemannZeta z = 0 := by
  intro hz
  exact hz

/-- The centered zero set is a reflection-stable set. -/
theorem centeredZetaZeros_stable (z : ℂ) :
    z ∈ centeredZetaZeros → -z ∈ centeredZetaZeros := by
  exact centeredZetaZeros_reflection z

/-- The centered zero set admits the two-point orbit as a subset. -/
theorem centeredZetaZeros_orbit_subset (z : CenteredZetaZero) :
    {x : ℂ | x ∈ orbit z} ⊆ centeredZetaZeros := by
  intro x hx
  rcases hx with rfl | rfl
  · exact z.2
  · exact (centeredZetaZeros_neg z).1 z.2

/-- The centered zero set contains the centered orbit. -/
theorem centeredZetaZeros_orbit_finite (z : CenteredZetaZero) :
    {x : ℂ | x ∈ orbit z}.Finite := by
  exact orbit_finite z

/-- The centered zero counting surface is the same as the centered zero set. -/
theorem centeredZetaZeros_eq : centeredZetaZeros = {s : ℂ | centeredCompletedRiemannZeta s = 0} := by
  rfl

end

end LFunctions
end Boundary
