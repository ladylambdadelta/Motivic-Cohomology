import Boundary.LFunctionsRootedTreeCanonicalAll.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroLocalFiniteness.ZetaZeroOrbitIsolation.ZetaZeroOrbitIsolation

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

/-- The named nontrivial zero set is the nontrivial zero locus from the
counting surface. -/
theorem centeredZetaNontrivialZeroSet_eq :
    centeredZetaNontrivialZeroSet =
      ({z : ℂ |
        z ≠ -(1 / 2 : ℂ) ∧
          z ≠ (1 / 2 : ℂ) ∧
            centeredCompletedRiemannZeta z = 0} : Set ℂ) := by
  rfl

/-- The nontrivial centered zero set has the discrete topology. -/
theorem centeredZetaNontrivialZeroSet_discreteTopology :
    DiscreteTopology centeredZetaNontrivialZeroSet := by
  unfold centeredZetaNontrivialZeroSet
  exact centeredZetaZeros_nontrivialZeroSet_discreteTopology_of_subset

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

/-- The centered critical height box is closed. -/
theorem isClosed_centeredCriticalHeightBox
    (T : ℝ) :
    IsClosed (centeredCriticalHeightBox T) := by
  have hleft :
      IsClosed ({z : ℂ | -(1 / 2 : ℝ) ≤ z.re} : Set ℂ) :=
    isClosed_le continuous_const Complex.continuous_re
  have hright :
      IsClosed ({z : ℂ | z.re ≤ (1 / 2 : ℝ)} : Set ℂ) :=
    isClosed_le Complex.continuous_re continuous_const
  have him :
      Continuous
        (fun z : ℂ => 1 + ‖(z - (1 / 2 : ℂ)).im‖) :=
    continuous_const.add
      ((Complex.continuous_im.comp
        (continuous_id.sub continuous_const)).norm)
  have hheight :
      IsClosed
        ({z : ℂ | 1 + ‖(z - (1 / 2 : ℂ)).im‖ ≤ T} : Set ℂ) :=
    isClosed_le him continuous_const
  change
    IsClosed
      (({z : ℂ | -(1 / 2 : ℝ) ≤ z.re} : Set ℂ) ∩
        ({z : ℂ | z.re ≤ (1 / 2 : ℝ)} ∩
          {z : ℂ | 1 + ‖(z - (1 / 2 : ℂ)).im‖ ≤ T}))
  exact hleft.inter (hright.inter hheight)

/-- The real coordinate of a point in the centered critical height box is
bounded by one in absolute value. -/
theorem centeredCriticalHeightBox_abs_re_le_one
    {T : ℝ} {z : ℂ}
    (hz : z ∈ centeredCriticalHeightBox T) :
    |z.re| ≤ (1 : ℝ) := by
  have hnegOne_le_negHalf : (-(1 : ℝ)) ≤ -(1 / 2 : ℝ) := by
    norm_num
  have hhalf_le_one : (1 / 2 : ℝ) ≤ (1 : ℝ) := by
    norm_num
  exact abs_le.mpr
    ⟨hnegOne_le_negHalf.trans hz.1,
      hz.2.1.trans hhalf_le_one⟩

/-- The imaginary coordinate of a point in the centered critical height box is
bounded by the absolute height parameter. -/
theorem centeredCriticalHeightBox_abs_im_le_abs_height
    {T : ℝ} {z : ℂ}
    (hz : z ∈ centeredCriticalHeightBox T) :
    |z.im| ≤ |T| := by
  have hcenter_le_height :
      ‖(z - (1 / 2 : ℂ)).im‖ ≤ T :=
    (le_add_of_nonneg_left zero_le_one).trans hz.2.2
  have hcenter_le_abs_height :
      ‖(z - (1 / 2 : ℂ)).im‖ ≤ |T| :=
    hcenter_le_height.trans (le_abs_self T)
  have him_eq : (z - (1 / 2 : ℂ)).im = z.im := by
    rw [Complex.sub_im, Complex.ofReal_im, sub_zero]
  have him_norm_le_abs_height :
      ‖z.im‖ ≤ |T| :=
    Eq.subst
      (motive := fun x : ℝ => ‖x‖ ≤ |T|)
      him_eq
      hcenter_le_abs_height
  exact Eq.subst
    (motive := fun x : ℝ => x ≤ |T|)
    (Real.norm_eq_abs z.im)
    him_norm_le_abs_height

/-- The norm of a point in the centered critical height box is bounded by an
explicit radius depending only on the height parameter. -/
theorem centeredCriticalHeightBox_norm_le_radius
    {T : ℝ} {z : ℂ}
    (hz : z ∈ centeredCriticalHeightBox T) :
    ‖z‖ ≤ 2 + |T| := by
  have hre : |z.re| ≤ (1 : ℝ) :=
    centeredCriticalHeightBox_abs_re_le_one hz
  have him : |z.im| ≤ |T| :=
    centeredCriticalHeightBox_abs_im_le_abs_height hz
  calc
    ‖z‖ = Complex.abs z := Complex.norm_eq_abs z
    _ ≤ |z.re| + |z.im| := Complex.abs_le_abs_re_add_abs_im z
    _ ≤ 1 + |T| := add_le_add hre him
    _ ≤ 2 + |T| := add_le_add_right one_le_two |T|

/-- The centered critical height box is contained in an explicit closed ball. -/
theorem centeredCriticalHeightBox_subset_closedBall
    (T : ℝ) :
    ∃ R : ℝ,
      centeredCriticalHeightBox T ⊆ Metric.closedBall (0 : ℂ) R := by
  refine ⟨2 + |T|, ?_⟩
  intro z hz
  exact mem_closedBall_zero_iff.mpr
    (centeredCriticalHeightBox_norm_le_radius hz)

/-- A closed subset of a compact closed ball is compact. -/
theorem isCompact_centeredCriticalHeightBox_of_closed_subset_closedBall
    (T R : ℝ)
    (hclosed : IsClosed (centeredCriticalHeightBox T))
    (hsubset : centeredCriticalHeightBox T ⊆ Metric.closedBall (0 : ℂ) R) :
    IsCompact (centeredCriticalHeightBox T) := by
  exact (isCompact_closedBall (0 : ℂ) R).of_isClosed_subset hclosed hsubset

/-- The centered critical height box is compact. -/
theorem isCompact_centeredCriticalHeightBox
    (T : ℝ) :
    IsCompact (centeredCriticalHeightBox T) := by
  rcases centeredCriticalHeightBox_subset_closedBall T with ⟨R, hsubset⟩
  exact isCompact_centeredCriticalHeightBox_of_closed_subset_closedBall
    T
    R
    (isClosed_centeredCriticalHeightBox T)
    hsubset

/-- A compact set has finite intersection with a closed discrete subtype. -/
theorem finite_of_compact_closed_discrete_subtype
    {S K : Set ℂ}
    (hcompact : IsCompact K)
    (hclosed : IsClosed S)
    (hdiscrete : DiscreteTopology S) :
    (S ∩ K).Finite := by
  have hcompact_KS : IsCompact (K ∩ S) :=
    hcompact.inter_right hclosed
  have hdiscrete_KS : DiscreteTopology (K ∩ S) :=
    DiscreteTopology.of_subset hdiscrete Set.inter_subset_right
  have hfinite_KS : (K ∩ S).Finite :=
    IsCompact.finite hcompact_KS hdiscrete_KS
  exact Eq.subst
    (motive := fun U : Set ℂ => U.Finite)
    (Set.inter_comm K S)
    hfinite_KS

/-- Away from the shifted poles and away from a zero value, continuity gives a
neighborhood avoiding the nontrivial centered zero set. -/
theorem eventually_not_mem_centeredZetaNontrivialZeroSet_of_ne_shiftedPoles
    {z : ℂ}
    (hzneg : z ≠ -(1 / 2 : ℂ))
    (hzpos : z ≠ (1 / 2 : ℂ))
    (hzeta : centeredCompletedRiemannZeta z ≠ 0) :
    ∀ᶠ w in 𝓝 z, w ∉ centeredZetaNontrivialZeroSet := by
  have hanalytic :
      AnalyticAt ℂ centeredCompletedRiemannZeta z :=
    centeredCompletedRiemannZeta_analyticAt_of_ne_shiftedPoles
      hzneg
      hzpos
  have hcontinuous :
      ContinuousAt centeredCompletedRiemannZeta z :=
    hanalytic.continuousAt
  have hne :
      ∀ᶠ w in 𝓝 z, centeredCompletedRiemannZeta w ≠ 0 :=
    hcontinuous.eventually_ne hzeta
  exact hne.mono
    (fun w hw hmem => hw hmem.2.2)

/-- The negative shifted pole has a neighborhood avoiding the nontrivial
centered zero set. -/
theorem eventually_not_mem_centeredZetaNontrivialZeroSet_negHalf :
    ∀ᶠ w in 𝓝 (-(1 / 2 : ℂ)), w ∉ centeredZetaNontrivialZeroSet := by
  exact centeredCompletedRiemannZeta_eventually_ne_zero_punctured_negHalf.mono
    (fun w hw hmem =>
      hw hmem.1 hmem.2.2)

/-- The positive shifted pole has a neighborhood avoiding the nontrivial
centered zero set. -/
theorem eventually_not_mem_centeredZetaNontrivialZeroSet_posHalf :
    ∀ᶠ w in 𝓝 ((1 / 2 : ℂ)), w ∉ centeredZetaNontrivialZeroSet := by
  exact centeredCompletedRiemannZeta_eventually_ne_zero_punctured_posHalf.mono
    (fun w hw hmem =>
      hw hmem.2.1 hmem.2.2)

/-- The nontrivial centered zero set has no accumulation at the shifted poles,
and away from the shifted poles it is closed by continuity of the centered
completed zeta function. -/
theorem isClosed_centeredZetaNontrivialZeroSet :
    IsClosed centeredZetaNontrivialZeroSet := by
  rw [← isOpen_compl_iff]
  rw [isOpen_iff_mem_nhds]
  intro z hz
  by_cases hzneg : z = -(1 / 2 : ℂ)
  · exact Eq.subst
      (motive := fun w : ℂ =>
        centeredZetaNontrivialZeroSetᶜ ∈ 𝓝 w)
      hzneg.symm
      eventually_not_mem_centeredZetaNontrivialZeroSet_negHalf
  · by_cases hzpos : z = (1 / 2 : ℂ)
    · exact Eq.subst
        (motive := fun w : ℂ =>
          centeredZetaNontrivialZeroSetᶜ ∈ 𝓝 w)
        hzpos.symm
        eventually_not_mem_centeredZetaNontrivialZeroSet_posHalf
    · have hzeta : centeredCompletedRiemannZeta z ≠ 0 := by
        intro hzeta_zero
        have hmem : z ∈ centeredZetaNontrivialZeroSet :=
          ⟨hzneg, hzpos, hzeta_zero⟩
        exact hz hmem
      exact eventually_not_mem_centeredZetaNontrivialZeroSet_of_ne_shiftedPoles
        hzneg
        hzpos
        hzeta

/-- A discrete nontrivial centered zero set has finite intersection with the
compact centered critical height box. -/
theorem finite_centeredZetaNontrivialZeroSet_inter_compact_of_discrete
    (T : ℝ)
    (hcompact : IsCompact (centeredCriticalHeightBox T))
    (hclosed : IsClosed centeredZetaNontrivialZeroSet)
    (hdiscrete : DiscreteTopology centeredZetaNontrivialZeroSet) :
    (centeredZetaNontrivialZeroSet ∩ centeredCriticalHeightBox T).Finite := by
  exact finite_of_compact_closed_discrete_subtype hcompact hclosed hdiscrete

/-- Isolated nontrivial centered zeros have finite intersection with the compact
centered critical height box. -/
theorem finite_centeredZetaNontrivialZeroSet_inter_compactCriticalHeightBox
    (T : ℝ) :
    (centeredZetaNontrivialZeroSet ∩ centeredCriticalHeightBox T).Finite := by
  have hcompact : IsCompact (centeredCriticalHeightBox T) :=
    isCompact_centeredCriticalHeightBox T
  have hclosed : IsClosed centeredZetaNontrivialZeroSet :=
    isClosed_centeredZetaNontrivialZeroSet
  have hdiscrete : DiscreteTopology centeredZetaNontrivialZeroSet :=
    centeredZetaNontrivialZeroSet_discreteTopology
  exact finite_centeredZetaNontrivialZeroSet_inter_compact_of_discrete
    (T := T)
    hcompact
    hclosed
    hdiscrete

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
