import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalization.GammaBoundaryPL.DampedFamily.HolomorphyAndBarriers

namespace Boundary
namespace LFunctions

noncomputable section

open Filter
open scoped Filter Topology
local notation "π" => Real.pi

/-- The bounded-height rectangle of a vertical strip, with variable height. -/
def verticalStripBoundedHeightRectangle
    (a b R : ℝ) : Set ℂ :=
  {z : ℂ | a ≤ z.re ∧ z.re ≤ b ∧ ‖z.im‖ ≤ R}

/-- The bounded-height strip rectangle is closed. -/
theorem verticalStripBoundedHeightRectangle_isClosed
    (a b R : ℝ) :
    IsClosed (verticalStripBoundedHeightRectangle a b R) := by
  have hleft : IsClosed {z : ℂ | a ≤ z.re} :=
    isClosed_le continuous_const Complex.continuous_re
  have hright : IsClosed {z : ℂ | z.re ≤ b} :=
    isClosed_le Complex.continuous_re continuous_const
  have him : IsClosed {z : ℂ | ‖z.im‖ ≤ R} :=
    isClosed_le (Complex.continuous_im.norm) continuous_const
  have hset :
      verticalStripBoundedHeightRectangle a b R =
        {z : ℂ | a ≤ z.re} ∩ {z : ℂ | z.re ≤ b} ∩
          {z : ℂ | ‖z.im‖ ≤ R} := by
    ext z
    constructor
    · intro hz
      exact ⟨⟨hz.1, hz.2.1⟩, hz.2.2⟩
    · intro hz
      exact ⟨hz.1.1, hz.1.2, hz.2⟩
  exact
    Eq.subst
      (motive := fun S : Set ℂ => IsClosed S)
      hset.symm
      ((hleft.inter hright).inter him)

/-- The bounded-height strip rectangle is bounded. -/
theorem verticalStripBoundedHeightRectangle_isBounded
    (a b R : ℝ) :
    Bornology.IsBounded (verticalStripBoundedHeightRectangle a b R) := by
  refine isBounded_iff_forall_norm_le.2 ⟨|a| + |b| + |R| + 1, ?_⟩
  intro z hz
  have hre_abs_le : |z.re| ≤ |a| + |b| := by
    have hleft : -(|a| + |b|) ≤ z.re := by
      have hneg_sum : -(|a| + |b|) = -|a| + -|b| :=
        neg_add |a| |b|
      have hneg_sum_le : -|a| + -|b| ≤ -|a| := by
        have hb_nonpos : -|b| ≤ 0 :=
          neg_nonpos.mpr (abs_nonneg b)
        exact
          le_trans
            (add_le_add_left hb_nonpos (-|a|))
            (le_of_eq (add_zero (-|a|)))
      have hneg_abs_a_le_a : -|a| ≤ a :=
        neg_abs_le a
      exact
        le_trans
          (le_of_eq hneg_sum)
          (le_trans hneg_sum_le (le_trans hneg_abs_a_le_a hz.1))
    have hright : z.re ≤ |a| + |b| := by
      have hb_le_abs_b : b ≤ |b| :=
        le_abs_self b
      have habs_b_le_sum : |b| ≤ |a| + |b| :=
        le_add_of_nonneg_left (abs_nonneg a)
      exact le_trans hz.2.1 (le_trans hb_le_abs_b habs_b_le_sum)
    exact abs_le.mpr ⟨hleft, hright⟩
  have him_abs_le : |z.im| ≤ |R| := by
    have him_norm_le : ‖z.im‖ ≤ R :=
      hz.2.2
    have him_abs_norm : |z.im| = ‖z.im‖ :=
      (Real.norm_eq_abs z.im).symm
    exact
      le_trans
        (le_of_eq him_abs_norm)
        (le_trans him_norm_le (le_abs_self R))
  have hnorm_le_sum : ‖z‖ ≤ |z.re| + |z.im| :=
    Eq.subst
      (motive := fun x : ℝ => x ≤ |z.re| + |z.im|)
      (Complex.norm_eq_abs z).symm
      (Complex.abs_le_abs_re_add_abs_im z)
  have hsum_le : |z.re| + |z.im| ≤ (|a| + |b|) + |R| :=
    add_le_add hre_abs_le him_abs_le
  have htarget : (|a| + |b|) + |R| ≤ |a| + |b| + |R| + 1 := by
    exact le_add_of_nonneg_right zero_le_one
  exact le_trans hnorm_le_sum (le_trans hsum_le htarget)

/-- The bounded-height strip rectangle is compact. -/
theorem verticalStripBoundedHeightRectangle_isCompact
    (a b R : ℝ) :
    IsCompact (verticalStripBoundedHeightRectangle a b R) :=
  Metric.isCompact_of_isClosed_isBounded
    (verticalStripBoundedHeightRectangle_isClosed a b R)
    (verticalStripBoundedHeightRectangle_isBounded a b R)

/-- The bounded-height strip rectangle lies in the closed vertical strip. -/
theorem verticalStripBoundedHeightRectangle_subset_closedStrip
    {a b R : ℝ}
    (hab : a < b) :
    verticalStripBoundedHeightRectangle a b R ⊆
      closure (Complex.re ⁻¹' Set.Ioo a b) := by
  intro z hz
  have hz_closed : z ∈ Complex.re ⁻¹' Set.Icc a b :=
    ⟨hz.1, hz.2.1⟩
  have hclosed_eq :
      Complex.re ⁻¹' Set.Icc a b =
        closure (Complex.re ⁻¹' Set.Ioo a b) := by
    calc
      Complex.re ⁻¹' Set.Icc a b =
          Complex.re ⁻¹' closure (Set.Ioo a b) := by
        exact congrArg (fun S : Set ℝ => Complex.re ⁻¹' S) (closure_Ioo hab.ne).symm
      _ = closure (Complex.re ⁻¹' Set.Ioo a b) := by
        exact (Complex.closure_preimage_re (Set.Ioo a b)).symm
  exact
    Eq.subst
      (motive := fun S : Set ℂ => z ∈ S)
      hclosed_eq
      hz_closed

/-- The upper-tail tilted damped family is continuous on each bounded-height
rectangle. -/
theorem verticalStripUpperTailDampedFamily_continuousOn_boundedHeightRectangle
    (f : ℂ → ℂ)
    (a b ε R : ℝ)
    (hab : a < b)
    (hhol : DiffContOnCl ℂ f (Complex.re ⁻¹' Set.Ioo a b)) :
    ContinuousOn (verticalStripUpperTailDampedFamily f a b ε)
      (verticalStripBoundedHeightRectangle a b R) :=
  (verticalStripUpperTailDampedFamily_diffContOnCl
      f a b ε hhol).continuousOn.mono
    (verticalStripBoundedHeightRectangle_subset_closedStrip hab)

/-- Bounded-height rectangle boundedness for the upper-tail tilted damped
family. -/
theorem verticalStripUpperTailDampedFamily_boundedHeightRectangle_bound
    (f : ℂ → ℂ)
    (a b ε R : ℝ)
    (hab : a < b)
    (hhol : DiffContOnCl ℂ f (Complex.re ⁻¹' Set.Ioo a b)) :
    ∃ C : ℝ,
      0 < C ∧
      ∀ z : ℂ,
        z ∈ verticalStripBoundedHeightRectangle a b R →
        ‖verticalStripUpperTailDampedFamily f a b ε z‖ ≤ C := by
  match IsCompact.exists_bound_of_continuousOn
      (verticalStripBoundedHeightRectangle_isCompact a b R)
      (verticalStripUpperTailDampedFamily_continuousOn_boundedHeightRectangle
        f a b ε R hab hhol) with
  | ⟨C0, hC0⟩ =>
      exact
        ⟨max C0 0 + 1,
          add_pos_of_nonneg_of_pos (le_max_right C0 0) zero_lt_one,
          fun z hz =>
            have hraw :
                ‖verticalStripUpperTailDampedFamily f a b ε z‖ ≤ C0 :=
              hC0 z hz
            le_trans hraw
              (le_trans (le_max_left C0 0)
                (le_add_of_nonneg_right zero_le_one))⟩

/-- The subcritical cosine-damped family is continuous on each bounded-height
rectangle. -/
theorem verticalStripSubcriticalCosineDampedFamily_continuousOn_boundedHeightRectangle
    (f : ℂ → ℂ)
    (a b d ε R : ℝ)
    (hab : a < b)
    (hhol : DiffContOnCl ℂ f (Complex.re ⁻¹' Set.Ioo a b)) :
    ContinuousOn (verticalStripSubcriticalCosineDampedFamily f a b d ε)
      (verticalStripBoundedHeightRectangle a b R) :=
  (verticalStripSubcriticalCosineDampedFamily_diffContOnCl
      f a b d ε hhol).continuousOn.mono
    (verticalStripBoundedHeightRectangle_subset_closedStrip hab)

/-- Bounded-height rectangle boundedness for the subcritical cosine-damped
family. -/
theorem verticalStripSubcriticalCosineDampedFamily_boundedHeightRectangle_bound
    (f : ℂ → ℂ)
    (a b d ε R : ℝ)
    (hab : a < b)
    (hhol : DiffContOnCl ℂ f (Complex.re ⁻¹' Set.Ioo a b)) :
    ∃ C : ℝ,
      0 < C ∧
      ∀ z : ℂ,
        z ∈ verticalStripBoundedHeightRectangle a b R →
        ‖verticalStripSubcriticalCosineDampedFamily f a b d ε z‖ ≤ C := by
  match IsCompact.exists_bound_of_continuousOn
      (verticalStripBoundedHeightRectangle_isCompact a b R)
      (verticalStripSubcriticalCosineDampedFamily_continuousOn_boundedHeightRectangle
        f a b d ε R hab hhol) with
  | ⟨C0, hC0⟩ =>
      exact
        ⟨max C0 0 + 1,
          add_pos_of_nonneg_of_pos (le_max_right C0 0) zero_lt_one,
          fun z hz =>
            have hraw :
                ‖verticalStripSubcriticalCosineDampedFamily f a b d ε z‖ ≤ C0 :=
              hC0 z hz
            le_trans hraw
              (le_trans (le_max_left C0 0)
                (le_add_of_nonneg_right zero_le_one))⟩

end
end LFunctions
end Boundary
