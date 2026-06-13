import Boundary.LFunctions.ZetaZeroOrbitIsolation

/-!
# Boundary centered zeta zero local finiteness

This file exports the finite orbit fact for the centered zero locus.
-/

namespace Boundary
namespace LFunctions

noncomputable section

/-- The two shifted pole locations, intersected with the centered height ball. -/
def centeredZetaShiftedPolesInCenteredHeightBall (T : ℝ) : Set ℂ :=
  {z : ℂ |
    (z = -(1 / 2 : ℂ) ∨ z = (1 / 2 : ℂ)) ∧
      1 + ‖(z - (1 / 2 : ℂ)).im‖ ≤ T}

/-- The nontrivial centered zero locus, intersected with the centered height ball. -/
def centeredZetaNontrivialZerosInCenteredHeightBall (T : ℝ) : Set ℂ :=
  {z : ℂ |
    z ≠ -(1 / 2 : ℂ) ∧
      z ≠ (1 / 2 : ℂ) ∧
        centeredCompletedRiemannZeta z = 0 ∧
          1 + ‖(z - (1 / 2 : ℂ)).im‖ ≤ T}

/-- The nontrivial centered zero locus in the centered critical strip and height ball. -/
def centeredZetaNontrivialZerosInCenteredCriticalHeightBox (T : ℝ) : Set ℂ :=
  {z : ℂ |
    z ≠ -(1 / 2 : ℂ) ∧
      z ≠ (1 / 2 : ℂ) ∧
        centeredCompletedRiemannZeta z = 0 ∧
          -(1 / 2 : ℝ) ≤ z.re ∧
            z.re ≤ (1 / 2 : ℝ) ∧
              1 + ‖(z - (1 / 2 : ℂ)).im‖ ≤ T}

/-- The ambient centered critical height box. -/
def centeredCriticalHeightBox (T : ℝ) : Set ℂ :=
  {z : ℂ |
    -(1 / 2 : ℝ) ≤ z.re ∧
      z.re ≤ (1 / 2 : ℝ) ∧
        1 + ‖(z - (1 / 2 : ℂ)).im‖ ≤ T}

/-- The nontrivial centered zero set. -/
def centeredZetaNontrivialZeroSet : Set ℂ :=
  {z : ℂ |
    z ≠ -(1 / 2 : ℂ) ∧
      z ≠ (1 / 2 : ℂ) ∧
        centeredCompletedRiemannZeta z = 0}

/-- The critical-height nontrivial zero box is the nontrivial zero set inside
the ambient centered critical height box. -/
theorem centeredZetaNontrivialZerosInCenteredCriticalHeightBox_eq_inter
    (T : ℝ) :
    centeredZetaNontrivialZerosInCenteredCriticalHeightBox T =
      centeredZetaNontrivialZeroSet ∩ centeredCriticalHeightBox T := by
  ext z
  constructor
  · intro hz
    rcases hz with
      ⟨hz_neg, hz_pos, hz_zero, hz_re_left, hz_re_right, hz_height⟩
    exact
      ⟨⟨hz_neg, hz_pos, hz_zero⟩,
        ⟨hz_re_left, hz_re_right, hz_height⟩⟩
  · intro hz
    rcases hz with
      ⟨⟨hz_neg, hz_pos, hz_zero⟩,
        ⟨hz_re_left, hz_re_right, hz_height⟩⟩
    exact
      ⟨hz_neg, hz_pos, hz_zero, hz_re_left, hz_re_right, hz_height⟩

/-- The shifted-pole part of a centered height ball is finite. -/
theorem finite_centeredZetaShiftedPolesInCenteredHeightBall
    (T : ℝ) :
    (centeredZetaShiftedPolesInCenteredHeightBall T).Finite := by
  let s : Finset ℂ := insert (-(1 / 2 : ℂ)) (insert (1 / 2 : ℂ) ∅)
  have hsubset : centeredZetaShiftedPolesInCenteredHeightBall T ⊆
      ({z : ℂ | z ∈ s} : Set ℂ) := by
    intro z hz
    rcases hz with ⟨hz_pole, _hz_height⟩
    rcases hz_pole with hz_neg | hz_pos
    · exact Finset.mem_insert.mpr (Or.inl hz_neg)
    · exact Finset.mem_insert.mpr
        (Or.inr (Finset.mem_insert.mpr (Or.inl hz_pos)))
  have hfinite : ({z : ℂ | z ∈ s} : Set ℂ).Finite :=
    Finset.finite_toSet s
  exact Set.Finite.subset hfinite hsubset

/-- The centered critical height box is compact. -/
theorem isCompact_centeredCriticalHeightBox
    (T : ℝ) :
    IsCompact (centeredCriticalHeightBox T) := by
  sorry

/-- Isolated nontrivial centered zeros have finite intersection with the compact
centered critical height box. -/
theorem finite_centeredZetaNontrivialZeroSet_inter_compactCriticalHeightBox
    (T : ℝ) :
    (centeredZetaNontrivialZeroSet ∩ centeredCriticalHeightBox T).Finite := by
  sorry

/-- Nontrivial centered zeros have finite intersection with each centered
critical height box. -/
theorem finite_centeredZetaNontrivialZeroSet_inter_centeredCriticalHeightBox
    (T : ℝ) :
    (centeredZetaNontrivialZeroSet ∩ centeredCriticalHeightBox T).Finite := by
  exact finite_centeredZetaNontrivialZeroSet_inter_compactCriticalHeightBox T

/-- Nontrivial centered zeros in a height ball lie in the centered critical
height box. -/
theorem centeredZetaNontrivialZerosInCenteredHeightBall_subset_criticalHeightBox
    (T : ℝ) :
    centeredZetaNontrivialZerosInCenteredHeightBall T ⊆
      centeredZetaNontrivialZerosInCenteredCriticalHeightBox T := by
  intro z hz
  rcases hz with ⟨hz_neg, hz_pos, hz_zero, hz_height⟩
  have hstrip :
      -(1 / 2 : ℝ) ≤ z.re ∧ z.re ≤ (1 / 2 : ℝ) :=
    centeredCompletedRiemannZeta_zero_re_mem_centeredCriticalStrip z hz_zero
  exact ⟨hz_neg, hz_pos, hz_zero, hstrip.1, hstrip.2, hz_height⟩

/-- The nontrivial centered zero part in a centered critical height box is finite. -/
theorem finite_centeredZetaNontrivialZerosInCenteredCriticalHeightBox
    (T : ℝ) :
    (centeredZetaNontrivialZerosInCenteredCriticalHeightBox T).Finite := by
  have hfinite :
      (centeredZetaNontrivialZeroSet ∩ centeredCriticalHeightBox T).Finite :=
    finite_centeredZetaNontrivialZeroSet_inter_centeredCriticalHeightBox T
  exact Eq.subst
    (motive := fun S : Set ℂ => S.Finite)
    (centeredZetaNontrivialZerosInCenteredCriticalHeightBox_eq_inter T).symm
    hfinite

/-- The nontrivial centered zero part of a centered height ball is finite. -/
theorem finite_centeredZetaNontrivialZerosInCenteredHeightBall
    (T : ℝ) :
    (centeredZetaNontrivialZerosInCenteredHeightBall T).Finite := by
  have hcritical :
      (centeredZetaNontrivialZerosInCenteredCriticalHeightBox T).Finite :=
    finite_centeredZetaNontrivialZerosInCenteredCriticalHeightBox T
  exact Set.Finite.subset
    hcritical
    (centeredZetaNontrivialZerosInCenteredHeightBall_subset_criticalHeightBox T)

/-- A centered height ball in the zero locus splits into shifted-pole and
nontrivial parts. -/
theorem centeredZetaZerosInCenteredHeightBall_subset_poles_union_nontrivial
    (T : ℝ) :
    centeredZetaZerosInCenteredHeightBall T ⊆
      centeredZetaShiftedPolesInCenteredHeightBall T ∪
        centeredZetaNontrivialZerosInCenteredHeightBall T := by
  intro z hz
  rcases hz with ⟨hz_zero, hz_height⟩
  by_cases hneg : z = -(1 / 2 : ℂ)
  · exact Or.inl ⟨Or.inl hneg, hz_height⟩
  · by_cases hpos : z = (1 / 2 : ℂ)
    · exact Or.inl ⟨Or.inr hpos, hz_height⟩
    · exact Or.inr ⟨hneg, hpos, hz_zero, hz_height⟩

/-- Centered completed-zeta zeros are finite in every centered vertical height ball.

This is the compact-height local-finiteness theorem for the centered completed
zero divisor. The counting file owns the set and discreteness/countability
surface; this local-finiteness file owns the compact-window finiteness input
used by multiplicity counting. -/
theorem finite_centeredZetaZerosInCenteredHeightBall
    (T : ℝ) :
    (centeredZetaZerosInCenteredHeightBall T).Finite := by
  have hpoles : (centeredZetaShiftedPolesInCenteredHeightBall T).Finite :=
    finite_centeredZetaShiftedPolesInCenteredHeightBall T
  have hnontrivial :
      (centeredZetaNontrivialZerosInCenteredHeightBall T).Finite :=
    finite_centeredZetaNontrivialZerosInCenteredHeightBall T
  have hunion :
      (centeredZetaShiftedPolesInCenteredHeightBall T ∪
        centeredZetaNontrivialZerosInCenteredHeightBall T).Finite :=
    Set.Finite.union hpoles hnontrivial
  exact Set.Finite.subset
    hunion
    (centeredZetaZerosInCenteredHeightBall_subset_poles_union_nontrivial T)

namespace CenteredZetaZero

/-- The centered zero orbit is finite inside the centered zero set. -/
theorem centeredZetaZeros_locallyFinite (z : CenteredZetaZero) :
    {x : ℂ | x ∈ orbit z}.Finite := by
  exact orbit_finite z

/-- The centered zero set is locally finite on each reflection orbit. -/
theorem centeredZetaZeros_localFiniteness (z : CenteredZetaZero) :
    {x : ℂ | x ∈ orbit z}.Finite := by
  exact centeredZetaZeros_locallyFinite z

end CenteredZetaZero

end
end LFunctions
end Boundary
