import Boundary.LFunctions.ZetaCenteredZeroOrbit
import Boundary.LFunctions.ZetaExplicitFormulaComplexAnalysis

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
  let t : ℂ → ℂ := fun s => (1 / 2 : ℂ) + s
  let S : Set ℂ := {z : ℂ | z = 0 ∨ z = 1 ∨ (z ≠ 0 ∧ z ≠ 1 ∧ completedRiemannZeta z = 0)}
  have hS : S.Countable := contourIntegrand_singularSet_countable
  let f : centeredZetaZeros → S := fun s =>
    ⟨t s, by
      rcases s.2 with hs
      unfold S
      by_cases h0 : t s = 0
      · exact Or.inl h0
      · by_cases h1 : t s = 1
        · exact Or.inr (Or.inl h1)
        · exact Or.inr (Or.inr ⟨h0, h1, by
          simpa [t, centeredCompletedRiemannZeta] using hs⟩)⟩
  have hf : Function.Injective f := by
    intro x y hxy
    apply Subtype.ext
    simpa [f, t] using congrArg Subtype.val hxy
  haveI : S.Countable := hS
  exact hf.countable

/-- Away from its shifted poles, the centered completed zeta has isolated zeros. -/
theorem centeredCompletedRiemannZeta_eventually_ne_zero_of_zero
    (z : ℂ) (hz0 : z ≠ -(1 / 2 : ℂ)) (hz1 : z ≠ (1 / 2 : ℂ))
    (hz : centeredCompletedRiemannZeta z = 0) :
    ∀ᶠ w in 𝓝[≠] z, centeredCompletedRiemannZeta w ≠ 0 := by
  have hz' : completedRiemannZeta ((1 / 2 : ℂ) + z) = 0 := by
    simpa [centeredCompletedRiemannZeta, add_comm, add_left_comm, add_assoc] using hz
  have hs0 : (1 / 2 : ℂ) + z ≠ 0 := by
    intro h
    apply hz0
    linarith
  have hs1 : (1 / 2 : ℂ) + z ≠ 1 := by
    intro h
    apply hz1
    linarith
  have hzero :=
    completedRiemannZeta_eventually_ne_zero_of_zero ((1 / 2 : ℂ) + z) hs0 hs1 hz'
  have ht :
      Tendsto (fun w : ℂ => (1 / 2 : ℂ) + w) (𝓝[≠] z)
        (𝓝[≠] ((1 / 2 : ℂ) + z)) := by
    simpa using ((Homeomorph.addLeft (1 / 2 : ℂ)).continuous.tendsto)
  have hcomp := hzero.comp ht
  simpa [centeredCompletedRiemannZeta, add_comm, add_left_comm, add_assoc] using hcomp

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
      centeredCompletedRiemannZeta_eventually_ne_zero_of_zero (z := x) hx0 hx1 hxz
    filter_upwards [hne] with w hw
    exact hw
  haveI : DiscreteTopology S := hdis
  haveI : LindelofSpace S := by infer_instance
  simpa [S] using (countable_of_Lindelof_of_discrete (X := S))

/-- The centered nontrivial zero locus has the discrete topology. -/
theorem centeredZetaZeros_nontrivialZeroSet_discreteTopology :
    DiscreteTopology
      ({z : ℂ | z ≠ -(1 / 2 : ℂ) ∧ z ≠ (1 / 2 : ℂ) ∧ centeredCompletedRiemannZeta z = 0} : Set ℂ) := by
  rw [discreteTopology_subtype_iff]
  intro x hx
  rcases hx with ⟨hx0, hx1, hxz⟩
  rw [disjoint_principal_right]
  have hne :
      ∀ᶠ w in 𝓝[≠] (x : ℂ), centeredCompletedRiemannZeta w ≠ 0 :=
    centeredCompletedRiemannZeta_eventually_ne_zero_of_zero (z := x) hx0 hx1 hxz
  filter_upwards [hne] with w hw
  intro hwS
  exact hw hwS.2.2

/-- The centered zero subtype is countable. -/
theorem CenteredZetaZero.countable : Countable CenteredZetaZero := by
  simpa [CenteredZetaZero] using centeredZetaZeros_countable

/-- The centered zero subtype has a canonical countability instance. -/
instance : Countable CenteredZetaZero := CenteredZetaZero.countable

end

end LFunctions
end Boundary
