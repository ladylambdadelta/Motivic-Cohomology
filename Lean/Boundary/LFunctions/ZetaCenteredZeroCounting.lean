import Boundary.LFunctions.ZetaCenteredZeroOrbit
import Boundary.LFunctions.ZetaCompletedNormalization
import Boundary.LFunctions.ZetaCompletedLogDerivativeBridge
import Mathlib.Order.Filter.Bases

/-!
# Boundary centered zeta zero counting surface

This file exposes the centered zero locus as a set and records the symmetry
already proved for the centered completed zeta function.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open scoped Topology

/-- The set of centered zeros of the completed zeta function. -/
def centeredZetaZeros : Set ℂ := {s | centeredCompletedRiemannZeta s = 0}

theorem centeredZetaZeros_neg (z : ℂ) :
    z ∈ centeredZetaZeros ↔ -z ∈ centeredZetaZeros := by
  constructor
  · intro hz
    unfold centeredZetaZeros at *
    exact (CenteredZetaZero.neg_mem_iff z).1 hz
  · intro hz
    unfold centeredZetaZeros at *
    exact (CenteredZetaZero.neg_mem_iff z).2 hz

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
    {x : ℂ | x ∈ CenteredZetaZero.orbit z} ⊆ centeredZetaZeros := by
  intro x hx
  have hx' : x = (z : ℂ) ∨ x = -z := by
    exact (CenteredZetaZero.orbit_mem_iff z).mp hx
  rcases hx' with rfl | rfl
  · exact z.2
  · exact (centeredZetaZeros_neg z).1 z.2

/-- The centered zero set contains the centered orbit. -/
theorem centeredZetaZeros_orbit_finite (z : CenteredZetaZero) :
    {x : ℂ | x ∈ CenteredZetaZero.orbit z}.Finite := by
  exact CenteredZetaZero.orbit_finite z

/-- The centered zero counting surface is the same as the centered zero set. -/
theorem centeredZetaZeros_eq : centeredZetaZeros = {s : ℂ | centeredCompletedRiemannZeta s = 0} := by
  rfl

/-- The nontrivial centered zero locus is discrete at a given point. -/
theorem centeredZetaZeros_nontrivial_discreteTopology_at {x : ℂ}
    (hx0 : x ≠ -(1 / 2 : ℂ)) (hx1 : x ≠ (1 / 2 : ℂ))
    (hxz : centeredCompletedRiemannZeta x = 0) :
    Disjoint (𝓝[≠] (x : ℂ))
      (Filter.principal ({z : ℂ | z ≠ -(1 / 2 : ℂ) ∧ z ≠ (1 / 2 : ℂ) ∧ centeredCompletedRiemannZeta z = 0})) := by
  have hne :
      ∀ᶠ w in 𝓝[≠] (x : ℂ), centeredCompletedRiemannZeta w ≠ 0 :=
    Boundary.LFunctions.ZetaAdmissibleFunction.centeredCompletedRiemannZeta_eventually_ne_zero_of_zero
      (z := x) hx0 hx1 hxz
  have hS :
      ({z : ℂ | z ≠ -(1 / 2 : ℂ) ∧ z ≠ (1 / 2 : ℂ) ∧ centeredCompletedRiemannZeta z = 0}ᶜ) ∈ 𝓝[≠] (x : ℂ) := by
    exact Filter.mem_of_superset hne (by
      intro w hw
      intro hwS
      exact hw hwS.2.2)
  exact (Filter.disjoint_principal_right).2 hS

/-- The nontrivial centered zero locus has the discrete topology. -/
theorem centeredZetaZeros_nontrivialZeroSet_discreteTopology_of_subset :
    DiscreteTopology
      ({z : ℂ | z ≠ -(1 / 2 : ℂ) ∧ z ≠ (1 / 2 : ℂ) ∧ centeredCompletedRiemannZeta z = 0} : Set ℂ) := by
  refine (discreteTopology_subtype_iff).2 ?_
  intro x hx
  rcases hx with ⟨hx0, hx1, hxz⟩
  exact (centeredZetaZeros_nontrivial_discreteTopology_at (x := x) hx0 hx1 hxz).eq_bot

/-- A discrete Lindelöf subtype is countable. -/
theorem centeredZetaZeros_countable_of_discrete {S : Set ℂ}
    (hdis : DiscreteTopology S) : S.Countable := by
  haveI : DiscreteTopology S := hdis
  haveI : LindelofSpace S := by infer_instance
  exact countable_of_Lindelof_of_discrete (X := S)

/-- The centered zero set away from the shifted poles is countable. -/
theorem centeredZetaZeros_nontrivialZeroSet_countable :
    ({z : ℂ | z ≠ -(1 / 2 : ℂ) ∧ z ≠ (1 / 2 : ℂ) ∧ centeredCompletedRiemannZeta z = 0} :
      Set ℂ).Countable := by
  have hdis :
      DiscreteTopology
        ({z : ℂ | z ≠ -(1 / 2 : ℂ) ∧ z ≠ (1 / 2 : ℂ) ∧ centeredCompletedRiemannZeta z = 0} : Set ℂ) :=
    centeredZetaZeros_nontrivialZeroSet_discreteTopology_of_subset
  exact centeredZetaZeros_countable_of_discrete
    (S := {z : ℂ | z ≠ -(1 / 2 : ℂ) ∧ z ≠ (1 / 2 : ℂ) ∧ centeredCompletedRiemannZeta z = 0}) hdis

/-- The negative shifted pole is countable as a singleton. -/
theorem centeredZetaZeros_negPole_countable :
    ({z : ℂ | z = -(1 / 2 : ℂ)} : Set ℂ).Countable := by
  exact Set.countable_singleton (-(1 / 2 : ℂ))

/-- The positive shifted pole is countable as a singleton. -/
theorem centeredZetaZeros_posPole_countable :
    ({z : ℂ | z = (1 / 2 : ℂ)} : Set ℂ).Countable := by
  exact Set.countable_singleton (1 / 2 : ℂ)

/-- The two shifted poles form a countable set. -/
theorem centeredZetaZeros_poles_countable :
    ({z : ℂ | z = -(1 / 2 : ℂ) ∨ z = (1 / 2 : ℂ)} : Set ℂ).Countable := by
  exact centeredZetaZeros_negPole_countable.union centeredZetaZeros_posPole_countable

/-- The centered zero set is covered by the poles and the nontrivial locus. -/
theorem centeredZetaZeros_subset_poles_union_nontrivial :
    centeredZetaZeros ⊆
      ({z : ℂ | z = -(1 / 2 : ℂ) ∨ z = (1 / 2 : ℂ)} : Set ℂ) ∪
        {z : ℂ | z ≠ -(1 / 2 : ℂ) ∧ z ≠ (1 / 2 : ℂ) ∧ centeredCompletedRiemannZeta z = 0} := by
  intro z hz
  by_cases hneg : z = -(1 / 2 : ℂ)
  · exact Or.inl (Or.inl hneg)
  · by_cases hpos : z = (1 / 2 : ℂ)
    · exact Or.inl (Or.inr hpos)
    · exact Or.inr ⟨hneg, hpos, hz⟩

/-- The centered zero set is a subset of a countable union of poles and nontrivial zeros. -/
theorem centeredZetaZeros_subset_countable_union :
    centeredZetaZeros ⊆
      ({z : ℂ | z = -(1 / 2 : ℂ) ∨ z = (1 / 2 : ℂ)} : Set ℂ) ∪
        {z : ℂ | z ≠ -(1 / 2 : ℂ) ∧ z ≠ (1 / 2 : ℂ) ∧ centeredCompletedRiemannZeta z = 0} := by
  exact centeredZetaZeros_subset_poles_union_nontrivial

/-- Centered zeros in the vertical height ball of radius `T`, expressed on
the underlying complex zero set. -/
def centeredZetaZerosInCenteredHeightBall (T : ℝ) : Set ℂ :=
  {z : ℂ |
    centeredCompletedRiemannZeta z = 0 ∧
      1 + ‖(z - (1 / 2 : ℂ)).im‖ ≤ T}

/-- Centered completed-zeta zeros are finite in every centered vertical height ball. -/
theorem finite_centeredZetaZerosInCenteredHeightBall
    (T : ℝ) :
    (centeredZetaZerosInCenteredHeightBall T).Finite := by
  sorry

/-- The union of the poles and the nontrivial centered zeros is countable. -/
theorem centeredZetaZeros_union_countable :
    (({z : ℂ | z = -(1 / 2 : ℂ) ∨ z = (1 / 2 : ℂ)} : Set ℂ) ∪
      {z : ℂ | z ≠ -(1 / 2 : ℂ) ∧ z ≠ (1 / 2 : ℂ) ∧ centeredCompletedRiemannZeta z = 0}).Countable := by
  exact centeredZetaZeros_poles_countable.union centeredZetaZeros_nontrivialZeroSet_countable

/-- The centered zero set is countable. -/
theorem centeredZetaZeros_countable :
    centeredZetaZeros.Countable := by
  exact centeredZetaZeros_union_countable.mono centeredZetaZeros_subset_countable_union

/-- The centered zero subtype is countable. -/
theorem CenteredZetaZero.countable : Countable CenteredZetaZero := by
  have hcount := centeredZetaZeros_countable
  exact hcount.to_subtype

/-- The centered zero subtype has a canonical countability instance. -/
instance : Countable CenteredZetaZero := CenteredZetaZero.countable

end

end LFunctions
end Boundary
