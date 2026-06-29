import Mathlib.Analysis.Complex.PhragmenLindelof
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalization.Core.Owner

/-!
# Right-critical-strip compact normalization package

This file owns the compact-core estimates for the pole-cleared completed
entire part on the right critical strip.
-/

namespace Boundary
namespace LFunctions

noncomputable section

/-- The compact right-critical-strip rectangle for the pole-cleared completed entire part. -/
def completedRiemannZeta₀_rightCriticalStripCompactSet : Set ℂ :=
  {z : ℂ | 0 ≤ z.re ∧ z.re ≤ 2 ∧ ‖z.im‖ ≤ 1}

/-- The right-critical-strip compact rectangle is closed. -/
theorem completedRiemannZeta₀_rightCriticalStripCompactSet_isClosed :
    IsClosed completedRiemannZeta₀_rightCriticalStripCompactSet := by
  have hleft : IsClosed {z : ℂ | 0 ≤ z.re} :=
    isClosed_le continuous_const Complex.continuous_re
  have hright : IsClosed {z : ℂ | z.re ≤ 2} :=
    isClosed_le Complex.continuous_re continuous_const
  have him : IsClosed {z : ℂ | ‖z.im‖ ≤ 1} :=
    isClosed_le (Complex.continuous_im.norm) continuous_const
  have hset :
      completedRiemannZeta₀_rightCriticalStripCompactSet =
        {z : ℂ | 0 ≤ z.re} ∩ {z : ℂ | z.re ≤ 2} ∩ {z : ℂ | ‖z.im‖ ≤ 1} := by
    ext z
    constructor
    · intro hz
      exact ⟨⟨hz.1, hz.2.1⟩, hz.2.2⟩
    · intro hz
      exact ⟨hz.1.1, hz.1.2, hz.2⟩
  exact Eq.subst
    (motive := fun S : Set ℂ => IsClosed S)
    hset.symm
    ((hleft.inter hright).inter him)

/-- The right-critical-strip compact rectangle is bounded. -/
theorem completedRiemannZeta₀_rightCriticalStripCompactSet_isBounded :
    Bornology.IsBounded completedRiemannZeta₀_rightCriticalStripCompactSet := by
  refine isBounded_iff_forall_norm_le.2 ⟨4, ?_⟩
  intro z hz
  have hz_re_abs_le_two : |z.re| ≤ 2 := by
    have hz_re_abs_eq : |z.re| = z.re :=
      abs_of_nonneg hz.1
    exact Eq.subst
      (motive := fun x : ℝ => x ≤ 2)
      hz_re_abs_eq.symm
      hz.2.1
  have hz_abs_le_three : ‖z‖ ≤ 3 := by
    have hcomplex :
        ‖z‖ ≤ |z.re| + |z.im| :=
      Eq.subst
        (motive := fun x : ℝ => x ≤ |z.re| + |z.im|)
        (Complex.norm_eq_abs z).symm
        (Complex.abs_le_abs_re_add_abs_im z)
    have him :
        |z.im| ≤ 1 := by
      exact Eq.subst
        (motive := fun x : ℝ => x ≤ 1)
        (Real.norm_eq_abs z.im)
        hz.2.2
    have hsum : |z.re| + |z.im| ≤ 2 + 1 :=
      add_le_add hz_re_abs_le_two him
    exact le_trans hcomplex (hsum.trans_eq (show (2 : ℝ) + 1 = 3 from rfl))
  have hthree_le_four : (3 : ℝ) ≤ 4 := by
    have hthree_le_three_add_one : (3 : ℝ) ≤ 3 + 1 :=
      le_add_of_nonneg_right (show (0 : ℝ) ≤ 1 from zero_le_one)
    exact Eq.subst
      (motive := fun x : ℝ => (3 : ℝ) ≤ x)
      (show (3 : ℝ) + 1 = 4 from rfl)
      hthree_le_three_add_one
  exact le_trans hz_abs_le_three hthree_le_four

/-- The right-critical-strip rectangle is compact. -/
theorem completedRiemannZeta₀_rightCriticalStripCompactSet_isCompact :
    IsCompact completedRiemannZeta₀_rightCriticalStripCompactSet :=
  Metric.isCompact_of_isClosed_isBounded
    completedRiemannZeta₀_rightCriticalStripCompactSet_isClosed
    completedRiemannZeta₀_rightCriticalStripCompactSet_isBounded

/-- The completed entire part is continuous on the right-critical-strip compact rectangle. -/
theorem completedRiemannZeta₀_continuousOn_rightCriticalStripCompactSet :
    ContinuousOn completedRiemannZeta₀
      completedRiemannZeta₀_rightCriticalStripCompactSet :=
  differentiable_completedZeta₀.continuous.continuousOn

/-- Compact boundedness of the pole-cleared completed-zeta entire part on the right
critical strip rectangle. -/
theorem completedRiemannZeta₀_rightCriticalStrip_compact_norm_bound :
    ∃ C : ℝ,
      0 < C ∧
      ∀ z : ℂ,
        z ∈ completedRiemannZeta₀_rightCriticalStripCompactSet →
        ‖completedRiemannZeta₀ z‖ ≤ C := by
  rcases IsCompact.exists_bound_of_continuousOn
      completedRiemannZeta₀_rightCriticalStripCompactSet_isCompact
      completedRiemannZeta₀_continuousOn_rightCriticalStripCompactSet with
    ⟨C0, hC0⟩
  refine ⟨max C0 0 + 1, ?_, ?_⟩
  · exact add_pos_of_nonneg_of_pos (le_max_right C0 0) zero_lt_one
  intro z hz
  have hraw : ‖completedRiemannZeta₀ z‖ ≤ C0 :=
    hC0 z hz
  exact le_trans hraw (le_trans (le_max_left C0 0) (le_add_of_nonneg_right zero_le_one))

end

end LFunctions
end Boundary
