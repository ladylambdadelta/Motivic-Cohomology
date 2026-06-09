import Boundary.LFunctions.ZetaCenteredZeroOrbit
import Boundary.LFunctions.ZetaCompletedLogDerivativeBridge

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

/-- The centered zero set is countable. -/
theorem centeredZetaZeros_countable :
    centeredZetaZeros.Countable := by
  have hnontriv :
      ({z : ℂ | z ≠ -(1 / 2 : ℂ) ∧ z ≠ (1 / 2 : ℂ) ∧ centeredCompletedRiemannZeta z = 0} :
        Set ℂ).Countable := by
    simpa using centeredZetaZeros_nontrivialZeroSet_countable
  have hpoles : ({z : ℂ | z = -(1 / 2 : ℂ) ∨ z = (1 / 2 : ℂ)} : Set ℂ).Countable := by
    have hneg : ({z : ℂ | z = -(1 / 2 : ℂ)} : Set ℂ).Countable := by
      simpa using (countable_singleton (-(1 / 2 : ℂ)))
    have hpos : ({z : ℂ | z = (1 / 2 : ℂ)} : Set ℂ).Countable := by
      simpa using (countable_singleton (1 / 2 : ℂ))
    simpa [Set.union_eq_or] using hneg.union hpos
  have hsub :
      centeredZetaZeros ⊆
        ({z : ℂ | z = -(1 / 2 : ℂ) ∨ z = (1 / 2 : ℂ)} : Set ℂ) ∪
          {z : ℂ | z ≠ -(1 / 2 : ℂ) ∧ z ≠ (1 / 2 : ℂ) ∧ centeredCompletedRiemannZeta z = 0} := by
    intro z hz
    by_cases hneg : z = -(1 / 2 : ℂ)
    · exact Or.inl (Or.inl hneg)
    · by_cases hpos : z = (1 / 2 : ℂ)
      · exact Or.inl (Or.inr hpos)
      · exact Or.inr ⟨hneg, hpos, hz⟩
  have hcount_union :
      (({z : ℂ | z = -(1 / 2 : ℂ) ∨ z = (1 / 2 : ℂ)} : Set ℂ) ∪
        {z : ℂ | z ≠ -(1 / 2 : ℂ) ∧ z ≠ (1 / 2 : ℂ) ∧ centeredCompletedRiemannZeta z = 0}).Countable := by
    exact hpoles.union hnontriv
  exact Countable.of_subset hcount_union hsub

/-- The centered zero set away from the shifted poles is countable. -/
theorem centeredZetaZeros_nontrivialZeroSet_countable :
    ({z : ℂ | z ≠ -(1 / 2 : ℂ) ∧ z ≠ (1 / 2 : ℂ) ∧ centeredCompletedRiemannZeta z = 0} :
      Set ℂ).Countable := by
  let S : Set ℂ := {z : ℂ | z ≠ -(1 / 2 : ℂ) ∧ z ≠ (1 / 2 : ℂ) ∧ centeredCompletedRiemannZeta z = 0}
  have hdis : DiscreteTopology S := by
    rw [discreteTopology_subtype_iff]
    intro x hx
    rcases hx with ⟨hx0, hx1, hxz⟩
    rw [disjoint_principal_right]
    have hne :
        ∀ᶠ w in 𝓝[≠] (x : ℂ), centeredCompletedRiemannZeta w ≠ 0 :=
      Boundary.LFunctions.centeredCompletedRiemannZeta_eventually_ne_zero_of_zero
        (z := x) hx0 hx1 hxz
    filter_upwards [hne] with w hw
    exact hw
  haveI : DiscreteTopology S := hdis
  haveI : LindelofSpace S := by infer_instance
  have hcount := (countable_of_Lindelof_of_discrete (X := S))
  exact hcount

/-- The centered zero set has the discrete topology. -/
theorem centeredZetaZeros_nontrivialZeroSet_discreteTopology :
    DiscreteTopology
      ({z : ℂ | z ≠ -(1 / 2 : ℂ) ∧ z ≠ (1 / 2 : ℂ) ∧ centeredCompletedRiemannZeta z = 0} : Set ℂ) := by
  rw [discreteTopology_subtype_iff]
  intro x hx
  rcases hx with ⟨hx0, hx1, hxz⟩
  rw [disjoint_principal_right]
  have hne :
      ∀ᶠ w in 𝓝[≠] (x : ℂ), centeredCompletedRiemannZeta w ≠ 0 :=
    Boundary.LFunctions.centeredCompletedRiemannZeta_eventually_ne_zero_of_zero
      (z := x) hx0 hx1 hxz
  filter_upwards [hne] with w hw
  intro hwS
  exact hw hwS.2.2

/-- The centered zero subtype is countable. -/
theorem CenteredZetaZero.countable : Countable CenteredZetaZero := by
  have hcount := centeredZetaZeros_countable
  simpa [CenteredZetaZero] using hcount

/-- The centered zero subtype has a canonical countability instance. -/
instance : Countable CenteredZetaZero := CenteredZetaZero.countable

end

end
end LFunctions
end Boundary
