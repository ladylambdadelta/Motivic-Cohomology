import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalization.GammaBoundaryPL.DampedFamily.UpperHalfStripGeometry

namespace Boundary
namespace LFunctions

noncomputable section

open Filter
open scoped Filter Topology
local notation "π" => Real.pi

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

/-- The compact-height strip rectangle is closed. -/
theorem verticalStripCompactHeightRectangle_isClosed
    (a b : ℝ) :
    IsClosed (verticalStripCompactHeightRectangle a b) := by
  have hleft : IsClosed {z : ℂ | a ≤ z.re} :=
    isClosed_le continuous_const Complex.continuous_re
  have hright : IsClosed {z : ℂ | z.re ≤ b} :=
    isClosed_le Complex.continuous_re continuous_const
  have him : IsClosed {z : ℂ | ‖z.im‖ ≤ 1} :=
    isClosed_le (Complex.continuous_im.norm) continuous_const
  have hset :
      verticalStripCompactHeightRectangle a b =
        {z : ℂ | a ≤ z.re} ∩ {z : ℂ | z.re ≤ b} ∩
          {z : ℂ | ‖z.im‖ ≤ 1} := by
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

/-- The compact-height strip rectangle is bounded. -/
theorem verticalStripCompactHeightRectangle_isBounded
    (a b : ℝ) :
    Bornology.IsBounded (verticalStripCompactHeightRectangle a b) := by
  refine isBounded_iff_forall_norm_le.2 ⟨|a| + |b| + 2, ?_⟩
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
  have him_abs_le : |z.im| ≤ 1 := by
    exact
      Eq.subst
        (motive := fun x : ℝ => x ≤ 1)
        (Real.norm_eq_abs z.im)
        hz.2.2
  have hnorm_le_sum : ‖z‖ ≤ |z.re| + |z.im| :=
    Eq.subst
      (motive := fun x : ℝ => x ≤ |z.re| + |z.im|)
      (Complex.norm_eq_abs z).symm
      (Complex.abs_le_abs_re_add_abs_im z)
  have hsum_le : |z.re| + |z.im| ≤ (|a| + |b|) + 1 :=
    add_le_add hre_abs_le him_abs_le
  have htarget : (|a| + |b|) + 1 ≤ |a| + |b| + 2 := by
    exact add_le_add_left one_le_two (|a| + |b|)
  exact le_trans hnorm_le_sum (le_trans hsum_le htarget)

/-- The compact-height strip rectangle is compact. -/
theorem verticalStripCompactHeightRectangle_isCompact
    (a b : ℝ) :
    IsCompact (verticalStripCompactHeightRectangle a b) :=
  Metric.isCompact_of_isClosed_isBounded
    (verticalStripCompactHeightRectangle_isClosed a b)
    (verticalStripCompactHeightRectangle_isBounded a b)

/-- The compact-height strip rectangle lies in the closed vertical strip. -/
theorem verticalStripCompactHeightRectangle_subset_closedStrip
    {a b : ℝ}
    (hab : a < b) :
    verticalStripCompactHeightRectangle a b ⊆
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

/-- The cosine-damped family is continuous on the compact-height rectangle. -/
theorem verticalStripCosineDampedFamily_continuousOn_compactHeightRectangle
    (f : ℂ → ℂ)
    (a b ε : ℝ)
    (hab : a < b)
    (hhol : DiffContOnCl ℂ f (Complex.re ⁻¹' Set.Ioo a b)) :
    ContinuousOn (verticalStripCosineDampedFamily f a b ε)
      (verticalStripCompactHeightRectangle a b) :=
  (verticalStripCosineDampedFamily_diffContOnCl f a b ε hab hhol).continuousOn.mono
    (verticalStripCompactHeightRectangle_subset_closedStrip hab)

/-- Compact-height rectangle boundedness for the cosine-damped family. -/
theorem verticalStripCosineDampedFamily_compactHeightRectangle_bound
    (f : ℂ → ℂ)
    (a b ε : ℝ)
    (hab : a < b)
    (hhol : DiffContOnCl ℂ f (Complex.re ⁻¹' Set.Ioo a b)) :
    ∃ C : ℝ,
      0 < C ∧
      ∀ z : ℂ,
        z ∈ verticalStripCompactHeightRectangle a b →
        ‖verticalStripCosineDampedFamily f a b ε z‖ ≤ C := by
  match IsCompact.exists_bound_of_continuousOn
      (verticalStripCompactHeightRectangle_isCompact a b)
      (verticalStripCosineDampedFamily_continuousOn_compactHeightRectangle
        f a b ε hab hhol) with
  | ⟨C0, hC0⟩ =>
      exact
        ⟨max C0 0 + 1,
          add_pos_of_nonneg_of_pos (le_max_right C0 0) zero_lt_one,
          fun z hz =>
            have hraw :
                ‖verticalStripCosineDampedFamily f a b ε z‖ ≤ C0 :=
              hC0 z hz
            le_trans hraw
              (le_trans (le_max_left C0 0)
                (le_add_of_nonneg_right zero_le_one))⟩

/-- The upper-tail tilted damped family is continuous on the compact-height
rectangle. -/
theorem verticalStripUpperTailDampedFamily_continuousOn_compactHeightRectangle
    (f : ℂ → ℂ)
    (a b ε : ℝ)
    (hab : a < b)
    (hhol : DiffContOnCl ℂ f (Complex.re ⁻¹' Set.Ioo a b)) :
    ContinuousOn (verticalStripUpperTailDampedFamily f a b ε)
      (verticalStripCompactHeightRectangle a b) :=
  (verticalStripUpperTailDampedFamily_diffContOnCl
      f a b ε hhol).continuousOn.mono
    (verticalStripCompactHeightRectangle_subset_closedStrip hab)

/-- Compact-height rectangle boundedness for the upper-tail tilted damped
family. -/
theorem verticalStripUpperTailDampedFamily_compactHeightRectangle_bound
    (f : ℂ → ℂ)
    (a b ε : ℝ)
    (hab : a < b)
    (hhol : DiffContOnCl ℂ f (Complex.re ⁻¹' Set.Ioo a b)) :
    ∃ C : ℝ,
      0 < C ∧
      ∀ z : ℂ,
        z ∈ verticalStripCompactHeightRectangle a b →
        ‖verticalStripUpperTailDampedFamily f a b ε z‖ ≤ C := by
  match IsCompact.exists_bound_of_continuousOn
      (verticalStripCompactHeightRectangle_isCompact a b)
      (verticalStripUpperTailDampedFamily_continuousOn_compactHeightRectangle
        f a b ε hab hhol) with
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

/-- Bottom-edge compact control for the shifted upper half-strip. -/
theorem verticalStripUpperTailDampedFamily_upperHalfStrip_bottomEdge_bound
    (f : ℂ → ℂ)
    (a b ε : ℝ)
    (hab : a < b)
    (hhol : DiffContOnCl ℂ f (Complex.re ⁻¹' Set.Ioo a b)) :
    ∃ C : ℝ,
      0 < C ∧
      ∀ z : ℂ,
        z ∈ verticalStripUpperHalfStripBottomEdge a b →
        ‖verticalStripUpperTailDampedFamily f a b ε z‖ ≤ C := by
  match verticalStripUpperTailDampedFamily_compactHeightRectangle_bound
      f a b ε hab hhol with
  | ⟨C, hC_pos, hC_bound⟩ =>
      exact
        ⟨C, hC_pos,
          fun z hz =>
            hC_bound z
              (verticalStripUpperHalfStripBottomEdge_subset_compactHeightRectangle
                hz)⟩

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

/-- Upper-tail eventual boundary control plus bounded-height compactness gives
a uniform upper-tail boundary package for the holomorphic upper-tail damped
family. -/
theorem verticalStripUpperTailDampedFamily_upperTail_boundary_package
    (f : ℂ → ℂ)
    {a b ε A B : ℝ}
    {m : ℕ}
    (hab : a < b)
    (hε_pos : 0 < ε)
    (hA : 0 < A)
    (hB : 0 < B)
    (hhol : DiffContOnCl ℂ f (Complex.re ⁻¹' Set.Ioo a b))
    (hleft :
      ∀ z : ℂ,
        z.re = a →
        1 ≤ ‖z.im‖ →
        ‖f z‖ ≤ A * Real.exp (B * (1 + ‖z.im‖) ^ m))
    (hright :
      ∀ z : ℂ,
        z.re = b →
        1 ≤ ‖z.im‖ →
        ‖f z‖ ≤ A * Real.exp (B * (1 + ‖z.im‖) ^ m)) :
    ∃ C : ℝ,
      0 < C ∧
      (∀ z : ℂ,
        z.re = a →
        1 ≤ z.im →
        ‖verticalStripUpperTailDampedFamily f a b ε z‖ ≤ C) ∧
      (∀ z : ℂ,
        z.re = b →
        1 ≤ z.im →
        ‖verticalStripUpperTailDampedFamily f a b ε z‖ ≤ C) := by
  let hright_upper :=
    verticalStripUpperTailDampedFamily_rightBoundary_eventually_upperTail_bound
      f hab hε_pos hA hB hright
  let hleft_upper :=
    verticalStripUpperTailDampedFamily_leftBoundary_eventually_upperTail_bound
      f hab hε_pos hA hB hleft
  match eventually_atTop.1 hright_upper,
      eventually_atTop.1 hleft_upper with
  | ⟨Rr, hr⟩, ⟨Rl, hl⟩ =>
      let R : ℝ := max 1 (max Rr Rl)
      match verticalStripUpperTailDampedFamily_boundedHeightRectangle_bound
          f a b ε R hab hhol with
      | ⟨M, hM_pos, hM⟩ =>
          let C : ℝ := max 1 M
          have hC_pos : 0 < C :=
            lt_of_lt_of_le zero_lt_one (le_max_left 1 M)
          have hone_le_C : (1 : ℝ) ≤ C :=
            le_max_left 1 M
          have hM_le_C : M ≤ C :=
            le_max_right 1 M
          have hRr : Rr ≤ R :=
            le_trans (le_max_left Rr Rl) (le_max_right 1 (max Rr Rl))
          have hRl : Rl ≤ R :=
            le_trans (le_max_right Rr Rl) (le_max_right 1 (max Rr Rl))
          have hleft_bound :
              ∀ z : ℂ,
                z.re = a →
                1 ≤ z.im →
                ‖verticalStripUpperTailDampedFamily f a b ε z‖ ≤ C :=
            fun z hz_re hz_im =>
              match le_total R z.im with
              | Or.inl hlarge =>
                  have hraw :
                      ‖verticalStripUpperTailDampedFamily f a b ε z‖ ≤ 1 :=
                    hl z.im (le_trans hRl hlarge) z hz_re rfl
                  le_trans hraw hone_le_C
              | Or.inr hmiddle =>
                  have him_nonneg : 0 ≤ z.im :=
                    le_trans zero_le_one hz_im
                  have him_norm : ‖z.im‖ = z.im :=
                    Real.norm_of_nonneg him_nonneg
                  have him_le_R : ‖z.im‖ ≤ R :=
                    Eq.subst
                      (motive := fun x : ℝ => x ≤ R)
                      him_norm.symm
                      hmiddle
                  have hz_mem : z ∈ verticalStripBoundedHeightRectangle a b R :=
                    ⟨le_of_eq hz_re.symm,
                      le_trans (le_of_eq hz_re) (le_of_lt hab),
                      him_le_R⟩
                  le_trans (hM z hz_mem) hM_le_C
          have hright_bound :
              ∀ z : ℂ,
                z.re = b →
                1 ≤ z.im →
                ‖verticalStripUpperTailDampedFamily f a b ε z‖ ≤ C :=
            fun z hz_re hz_im =>
              match le_total R z.im with
              | Or.inl hlarge =>
                  have hraw :
                      ‖verticalStripUpperTailDampedFamily f a b ε z‖ ≤ 1 :=
                    hr z.im (le_trans hRr hlarge) z hz_re rfl
                  le_trans hraw hone_le_C
              | Or.inr hmiddle =>
                  have him_nonneg : 0 ≤ z.im :=
                    le_trans zero_le_one hz_im
                  have him_norm : ‖z.im‖ = z.im :=
                    Real.norm_of_nonneg him_nonneg
                  have him_le_R : ‖z.im‖ ≤ R :=
                    Eq.subst
                      (motive := fun x : ℝ => x ≤ R)
                      him_norm.symm
                      hmiddle
                  have hz_mem : z ∈ verticalStripBoundedHeightRectangle a b R :=
                    ⟨le_trans (le_of_lt hab) (le_of_eq hz_re.symm),
                      le_of_eq hz_re,
                      him_le_R⟩
                  le_trans (hM z hz_mem) hM_le_C
          exact ⟨C, hC_pos, hleft_bound, hright_bound⟩

/-- Analytic, subcritical-growth, and bounded upper-boundary-ray package for
the holomorphic upper-tail damped family. -/
theorem verticalStripUpperTailDampedFamily_upperTail_PL_input_package
    (f : ℂ → ℂ)
    {a b ε A B : ℝ}
    {m : ℕ}
    (hab : a < b)
    (hε_pos : 0 < ε)
    (hA : 0 < A)
    (hB : 0 < B)
    (hhol : DiffContOnCl ℂ f (Complex.re ⁻¹' Set.Ioo a b))
    (hfinite :
      ∃ c : ℝ,
        c < Real.pi / (b - a) ∧
        ∃ D : ℝ,
          f =O[
              Filter.comap (_root_.abs ∘ Complex.im) Filter.atTop ⊓
                𝓟 (Complex.re ⁻¹' Set.Ioo a b)]
            fun z : ℂ => Real.exp (D * Real.exp (c * |z.im|)))
    (hleft :
      ∀ z : ℂ,
        z.re = a →
        1 ≤ ‖z.im‖ →
        ‖f z‖ ≤ A * Real.exp (B * (1 + ‖z.im‖) ^ m))
    (hright :
      ∀ z : ℂ,
        z.re = b →
        1 ≤ ‖z.im‖ →
        ‖f z‖ ≤ A * Real.exp (B * (1 + ‖z.im‖) ^ m)) :
    DiffContOnCl ℂ (verticalStripUpperTailDampedFamily f a b ε)
        (Complex.re ⁻¹' Set.Ioo a b) ∧
      (∃ c : ℝ,
        c < Real.pi / (b - a) ∧
        ∃ D : ℝ,
          verticalStripUpperTailDampedFamily f a b ε =O[
              Filter.comap (_root_.abs ∘ Complex.im) Filter.atTop ⊓
                𝓟 (Complex.re ⁻¹' Set.Ioo a b)]
            fun z : ℂ => Real.exp (D * Real.exp (c * |z.im|))) ∧
      ∃ C : ℝ,
        0 < C ∧
        (∀ z : ℂ,
          z.re = a →
          1 ≤ z.im →
          ‖verticalStripUpperTailDampedFamily f a b ε z‖ ≤ C) ∧
        (∀ z : ℂ,
          z.re = b →
          1 ≤ z.im →
          ‖verticalStripUpperTailDampedFamily f a b ε z‖ ≤ C) := by
  have hanalytic :
      DiffContOnCl ℂ (verticalStripUpperTailDampedFamily f a b ε)
          (Complex.re ⁻¹' Set.Ioo a b) ∧
        ∃ c : ℝ,
          c < Real.pi / (b - a) ∧
          ∃ D : ℝ,
            verticalStripUpperTailDampedFamily f a b ε =O[
                Filter.comap (_root_.abs ∘ Complex.im) Filter.atTop ⊓
                  𝓟 (Complex.re ⁻¹' Set.Ioo a b)]
              fun z : ℂ => Real.exp (D * Real.exp (c * |z.im|)) :=
    verticalStripUpperTailDampedFamily_analytic_growth_package
      f a b ε hhol hfinite (le_of_lt hε_pos)
  have hboundary :
      ∃ C : ℝ,
        0 < C ∧
        (∀ z : ℂ,
          z.re = a →
          1 ≤ z.im →
          ‖verticalStripUpperTailDampedFamily f a b ε z‖ ≤ C) ∧
        (∀ z : ℂ,
          z.re = b →
          1 ≤ z.im →
          ‖verticalStripUpperTailDampedFamily f a b ε z‖ ≤ C) :=
    verticalStripUpperTailDampedFamily_upperTail_boundary_package
      f hab hε_pos hA hB hhol hleft hright
  exact ⟨hanalytic.1, hanalytic.2, hboundary⟩

/-- Full shifted upper half-strip PL input package for the holomorphic
upper-tail damped family: analytic growth, bounded vertical rays, and compact
bottom-edge control. -/
theorem verticalStripUpperTailDampedFamily_upperHalfStrip_PL_boundary_package
    (f : ℂ → ℂ)
    {a b ε A B : ℝ}
    {m : ℕ}
    (hab : a < b)
    (hε_pos : 0 < ε)
    (hA : 0 < A)
    (hB : 0 < B)
    (hhol : DiffContOnCl ℂ f (Complex.re ⁻¹' Set.Ioo a b))
    (hfinite :
      ∃ c : ℝ,
        c < Real.pi / (b - a) ∧
        ∃ D : ℝ,
          f =O[
              Filter.comap (_root_.abs ∘ Complex.im) Filter.atTop ⊓
                𝓟 (Complex.re ⁻¹' Set.Ioo a b)]
            fun z : ℂ => Real.exp (D * Real.exp (c * |z.im|)))
    (hleft :
      ∀ z : ℂ,
        z.re = a →
        1 ≤ ‖z.im‖ →
        ‖f z‖ ≤ A * Real.exp (B * (1 + ‖z.im‖) ^ m))
    (hright :
      ∀ z : ℂ,
        z.re = b →
        1 ≤ ‖z.im‖ →
        ‖f z‖ ≤ A * Real.exp (B * (1 + ‖z.im‖) ^ m)) :
    DiffContOnCl ℂ (verticalStripUpperTailDampedFamily f a b ε)
        (Complex.re ⁻¹' Set.Ioo a b) ∧
      (∃ c : ℝ,
        c < Real.pi / (b - a) ∧
        ∃ D : ℝ,
          verticalStripUpperTailDampedFamily f a b ε =O[
              Filter.comap (_root_.abs ∘ Complex.im) Filter.atTop ⊓
                𝓟 (Complex.re ⁻¹' Set.Ioo a b)]
            fun z : ℂ => Real.exp (D * Real.exp (c * |z.im|))) ∧
      (∃ C : ℝ,
        0 < C ∧
        (∀ z : ℂ,
          z.re = a →
          1 ≤ z.im →
          ‖verticalStripUpperTailDampedFamily f a b ε z‖ ≤ C) ∧
        (∀ z : ℂ,
          z.re = b →
          1 ≤ z.im →
          ‖verticalStripUpperTailDampedFamily f a b ε z‖ ≤ C)) ∧
      ∃ C : ℝ,
        0 < C ∧
        ∀ z : ℂ,
          z ∈ verticalStripUpperHalfStripBottomEdge a b →
          ‖verticalStripUpperTailDampedFamily f a b ε z‖ ≤ C := by
  have hinputs :
      DiffContOnCl ℂ (verticalStripUpperTailDampedFamily f a b ε)
          (Complex.re ⁻¹' Set.Ioo a b) ∧
        (∃ c : ℝ,
          c < Real.pi / (b - a) ∧
          ∃ D : ℝ,
            verticalStripUpperTailDampedFamily f a b ε =O[
                Filter.comap (_root_.abs ∘ Complex.im) Filter.atTop ⊓
                  𝓟 (Complex.re ⁻¹' Set.Ioo a b)]
              fun z : ℂ => Real.exp (D * Real.exp (c * |z.im|))) ∧
        ∃ C : ℝ,
          0 < C ∧
          (∀ z : ℂ,
            z.re = a →
            1 ≤ z.im →
            ‖verticalStripUpperTailDampedFamily f a b ε z‖ ≤ C) ∧
          (∀ z : ℂ,
            z.re = b →
            1 ≤ z.im →
            ‖verticalStripUpperTailDampedFamily f a b ε z‖ ≤ C) :=
    verticalStripUpperTailDampedFamily_upperTail_PL_input_package
      f hab hε_pos hA hB hhol hfinite hleft hright
  have hbottom :
      ∃ C : ℝ,
        0 < C ∧
        ∀ z : ℂ,
          z ∈ verticalStripUpperHalfStripBottomEdge a b →
          ‖verticalStripUpperTailDampedFamily f a b ε z‖ ≤ C :=
    verticalStripUpperTailDampedFamily_upperHalfStrip_bottomEdge_bound
      f a b ε hab hhol
  exact ⟨hinputs.1, hinputs.2.1, hinputs.2.2, hbottom⟩

/-- The subcritical cosine-damped family is continuous on the compact-height
rectangle. -/
theorem verticalStripSubcriticalCosineDampedFamily_continuousOn_compactHeightRectangle
    (f : ℂ → ℂ)
    (a b d ε : ℝ)
    (hab : a < b)
    (hhol : DiffContOnCl ℂ f (Complex.re ⁻¹' Set.Ioo a b)) :
    ContinuousOn (verticalStripSubcriticalCosineDampedFamily f a b d ε)
      (verticalStripCompactHeightRectangle a b) :=
  (verticalStripSubcriticalCosineDampedFamily_diffContOnCl
      f a b d ε hhol).continuousOn.mono
    (verticalStripCompactHeightRectangle_subset_closedStrip hab)

/-- Compact-height rectangle boundedness for the subcritical cosine-damped
family. -/
theorem verticalStripSubcriticalCosineDampedFamily_compactHeightRectangle_bound
    (f : ℂ → ℂ)
    (a b d ε : ℝ)
    (hab : a < b)
    (hhol : DiffContOnCl ℂ f (Complex.re ⁻¹' Set.Ioo a b)) :
    ∃ C : ℝ,
      0 < C ∧
      ∀ z : ℂ,
        z ∈ verticalStripCompactHeightRectangle a b →
        ‖verticalStripSubcriticalCosineDampedFamily f a b d ε z‖ ≤ C := by
  match IsCompact.exists_bound_of_continuousOn
      (verticalStripCompactHeightRectangle_isCompact a b)
      (verticalStripSubcriticalCosineDampedFamily_continuousOn_compactHeightRectangle
        f a b d ε hab hhol) with
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

/-- Bottom-edge compact control for the shifted upper half-strip for the
subcritical cosine-damped family. -/
theorem verticalStripSubcriticalCosineDampedFamily_upperHalfStrip_bottomEdge_bound
    (f : ℂ → ℂ)
    (a b d ε : ℝ)
    (hab : a < b)
    (hhol : DiffContOnCl ℂ f (Complex.re ⁻¹' Set.Ioo a b)) :
    ∃ C : ℝ,
      0 < C ∧
      ∀ z : ℂ,
        z ∈ verticalStripUpperHalfStripBottomEdge a b →
        ‖verticalStripSubcriticalCosineDampedFamily f a b d ε z‖ ≤ C := by
  match verticalStripSubcriticalCosineDampedFamily_compactHeightRectangle_bound
      f a b d ε hab hhol with
  | ⟨C, hC_pos, hC_bound⟩ =>
      exact
        ⟨C, hC_pos,
          fun z hz =>
            hC_bound z
              (verticalStripUpperHalfStripBottomEdge_subset_compactHeightRectangle
                hz)⟩

/-- Fixed-damping bounded upper half-strip control for the subcritical
cosine-damped family.  The resulting bound may depend on the positive damping
parameter; the later undamping step needs a separate uniform-envelope theorem. -/
theorem verticalStripSubcriticalCosineDampedFamily_upperHalfStrip_bound
    (f : ℂ → ℂ)
    {a b c d D ε A B : ℝ}
    {m : ℕ}
    (hab : a < b)
    (hd_pos : 0 < d)
    (hd_threshold : d < π / (b - a))
    (hε_pos : 0 < ε)
    (hcd : c < d)
    (hA : 0 < A)
    (hB : 0 < B)
    (hhol : DiffContOnCl ℂ f (Complex.re ⁻¹' Set.Ioo a b))
    (hD :
      f =O[
          Filter.comap (_root_.abs ∘ Complex.im) Filter.atTop ⊓
            𝓟 (Complex.re ⁻¹' Set.Ioo a b)]
        fun z : ℂ => Real.exp (D * Real.exp (c * |z.im|)))
    (hleft :
      ∀ z : ℂ,
        z.re = a →
        1 ≤ ‖z.im‖ →
        ‖f z‖ ≤ A * Real.exp (B * (1 + ‖z.im‖) ^ m))
    (hright :
      ∀ z : ℂ,
        z.re = b →
        1 ≤ ‖z.im‖ →
        ‖f z‖ ≤ A * Real.exp (B * (1 + ‖z.im‖) ^ m)) :
    ∃ C : ℝ,
      0 < C ∧
      ∀ z : ℂ,
        a ≤ z.re →
        z.re ≤ b →
        1 ≤ z.im →
        ‖verticalStripSubcriticalCosineDampedFamily f a b d ε z‖ ≤ C := by
  match
    verticalStripSubcriticalCosineDampedFamily_eventually_topEdge_bound
      f hab hd_pos hd_threshold hε_pos hcd hA hB hhol hD hleft hright,
    verticalStripSubcriticalCosineDampedFamily_tail_boundary_package
      f hab hd_pos hd_threshold hε_pos hA hB hhol hleft hright,
    verticalStripSubcriticalCosineDampedFamily_upperHalfStrip_bottomEdge_bound
      f a b d ε hab hhol
  with
  | ⟨Ctop, hCtop_pos, htop⟩,
    ⟨Cside, hCside_pos, hleft_side, hright_side⟩,
    ⟨Cbottom, hCbottom_pos, hbottom⟩ =>
      let C : ℝ := max Ctop (max Cside Cbottom)
      have hC_pos : 0 < C :=
        lt_of_lt_of_le hCtop_pos
          (le_max_left Ctop (max Cside Cbottom))
      have hCtop_le : Ctop ≤ C :=
        le_max_left Ctop (max Cside Cbottom)
      have hCside_le : Cside ≤ C :=
        le_trans
          (le_max_left Cside Cbottom)
          (le_max_right Ctop (max Cside Cbottom))
      have hCbottom_le : Cbottom ≤ C :=
        le_trans
          (le_max_right Cside Cbottom)
          (le_max_right Ctop (max Cside Cbottom))
      have hbottom_C :
          ∀ z : ℂ,
            z ∈ verticalStripUpperHalfStripBottomEdge a b →
            ‖verticalStripSubcriticalCosineDampedFamily f a b d ε z‖ ≤ C :=
        fun z hz =>
          le_trans (hbottom z hz) hCbottom_le
      have hleft_C :
          ∀ z : ℂ,
            z.re = a →
            1 ≤ z.im →
            ‖verticalStripSubcriticalCosineDampedFamily f a b d ε z‖ ≤ C :=
        fun z hz_re hz_im =>
          le_trans
            (hleft_side z hz_re (upperTail_im_norm_ge_one z hz_im))
            hCside_le
      have hright_C :
          ∀ z : ℂ,
            z.re = b →
            1 ≤ z.im →
            ‖verticalStripSubcriticalCosineDampedFamily f a b d ε z‖ ≤ C :=
        fun z hz_re hz_im =>
          le_trans
            (hright_side z hz_re (upperTail_im_norm_ge_one z hz_im))
            hCside_le
      have htop_C :
          ∀ᶠ R : ℝ in Filter.atTop,
            ∀ z : ℂ,
              a ≤ z.re →
              z.re ≤ b →
              z.im = R →
              ‖verticalStripSubcriticalCosineDampedFamily f a b d ε z‖ ≤ C :=
        htop.mono
          fun R hR z hza hzb hz_im =>
            le_trans (hR z hza hzb hz_im) hCtop_le
      exact
        ⟨C, hC_pos,
          verticalStripUpperHalfStrip_norm_le_of_eventual_top_boundary
            (verticalStripSubcriticalCosineDampedFamily f a b d ε)
            hab
            (verticalStripSubcriticalCosineDampedFamily_diffContOnCl
              f a b d ε hhol)
            hbottom_C hleft_C hright_C htop_C⟩

/-- Compact-height control for all positive subcritical cosine dampings with
one finite-order envelope independent of the damping parameter. -/
theorem verticalStripSubcriticalCosineDampedFamily_uniform_compactHeight_finiteEnvelope
    (f : ℂ → ℂ)
    {a b d : ℝ}
    (hab : a < b)
    (hd_pos : 0 < d)
    (hd_threshold : d < π / (b - a))
    (hhol : DiffContOnCl ℂ f (Complex.re ⁻¹' Set.Ioo a b)) :
    ∃ A : ℝ, ∃ B : ℝ, ∃ m : ℕ,
      0 < A ∧
      0 < B ∧
      ∀ ε : ℝ,
        0 < ε →
        ∀ z : ℂ,
          z ∈ verticalStripCompactHeightRectangle a b →
          ‖verticalStripSubcriticalCosineDampedFamily f a b d ε z‖ ≤
            A * Real.exp (B * (1 + ‖z‖) ^ m) := by
  match IsCompact.exists_bound_of_continuousOn
      (verticalStripCompactHeightRectangle_isCompact a b)
      (hhol.continuousOn.mono
        (verticalStripCompactHeightRectangle_subset_closedStrip hab)) with
  | ⟨C0, hC0_bound⟩ =>
      let C : ℝ := max C0 0 + 1
      have hC_pos : 0 < C :=
        add_pos_of_nonneg_of_pos (le_max_right C0 0) zero_lt_one
      have hC_bound :
          ∀ z : ℂ,
            z ∈ verticalStripCompactHeightRectangle a b →
            ‖f z‖ ≤ C :=
        fun z hz =>
          le_trans
            (hC0_bound z hz)
            (le_trans (le_max_left C0 0)
              (le_add_of_nonneg_right zero_le_one))
      exact
        ⟨C, 1, 0, hC_pos, zero_lt_one,
          fun ε hε z hz =>
            have hdamped_le :
                ‖verticalStripSubcriticalCosineDampedFamily f a b d ε z‖ ≤
                  ‖f z‖ :=
              verticalStripSubcriticalCosineDampedFamily_norm_le_original_on_closedStrip
                f hab hd_pos hd_threshold (le_of_lt hε) z hz.1 hz.2.1
            have hraw :
                ‖verticalStripSubcriticalCosineDampedFamily f a b d ε z‖ ≤ C :=
              le_trans hdamped_le (hC_bound z hz)
            have hexp_one_le :
                (1 : ℝ) ≤ Real.exp (1 * (1 + ‖z‖) ^ (0 : ℕ)) := by
              have hpow : (1 + ‖z‖) ^ (0 : ℕ) = (1 : ℝ) :=
                pow_zero (1 + ‖z‖)
              have hexponent : 1 * (1 + ‖z‖) ^ (0 : ℕ) = (1 : ℝ) :=
                Eq.trans (congrArg (fun x : ℝ => 1 * x) hpow) (mul_one 1)
              exact
                Eq.subst
                  (motive := fun x : ℝ => (1 : ℝ) ≤ Real.exp x)
                  hexponent.symm
                  (Real.one_le_exp zero_le_one)
            have hC_nonneg : 0 ≤ C :=
              le_of_lt hC_pos
            have hC_le :
                C ≤ C * Real.exp (1 * (1 + ‖z‖) ^ (0 : ℕ)) := by
              calc
                C = C * 1 := (mul_one C).symm
                _ ≤ C * Real.exp (1 * (1 + ‖z‖) ^ (0 : ℕ)) :=
                  mul_le_mul_of_nonneg_left hexp_one_le hC_nonneg
            le_trans hraw hC_le⟩

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

/-- The undamped function is continuous on the compact-height rectangle. -/
theorem verticalStripFunction_continuousOn_compactHeightRectangle
    (f : ℂ → ℂ)
    (a b : ℝ)
    (hab : a < b)
    (hhol : DiffContOnCl ℂ f (Complex.re ⁻¹' Set.Ioo a b)) :
    ContinuousOn f (verticalStripCompactHeightRectangle a b) :=
  hhol.continuousOn.mono
    (verticalStripCompactHeightRectangle_subset_closedStrip hab)

/-- Compact-height rectangle boundedness for the undamped function. -/
theorem verticalStripFunction_compactHeightRectangle_bound
    (f : ℂ → ℂ)
    (a b : ℝ)
    (hab : a < b)
    (hhol : DiffContOnCl ℂ f (Complex.re ⁻¹' Set.Ioo a b)) :
    ∃ C : ℝ,
      0 < C ∧
      ∀ z : ℂ,
        z ∈ verticalStripCompactHeightRectangle a b →
        ‖f z‖ ≤ C := by
  match IsCompact.exists_bound_of_continuousOn
      (verticalStripCompactHeightRectangle_isCompact a b)
      (verticalStripFunction_continuousOn_compactHeightRectangle
        f a b hab hhol) with
  | ⟨C0, hC0⟩ =>
      exact
        ⟨max C0 0 + 1,
          add_pos_of_nonneg_of_pos (le_max_right C0 0) zero_lt_one,
          fun z hz =>
            have hraw : ‖f z‖ ≤ C0 :=
              hC0 z hz
            le_trans hraw
              (le_trans (le_max_left C0 0)
                (le_add_of_nonneg_right zero_le_one))⟩

/-- Compact-height boundary control for the undamped function. -/
theorem verticalStripFunction_compact_boundary_bound
    (f : ℂ → ℂ)
    (a b : ℝ)
    (hab : a < b)
    (hhol : DiffContOnCl ℂ f (Complex.re ⁻¹' Set.Ioo a b)) :
    ∃ C : ℝ,
      0 < C ∧
      (∀ z : ℂ,
        z.re = a →
        ¬ 1 ≤ ‖z.im‖ →
        ‖f z‖ ≤ C) ∧
      (∀ z : ℂ,
        z.re = b →
        ¬ 1 ≤ ‖z.im‖ →
        ‖f z‖ ≤ C) := by
  match verticalStripFunction_compactHeightRectangle_bound
      f a b hab hhol with
  | ⟨C, hC_pos, hC_bound⟩ =>
      exact
        ⟨C, hC_pos,
          fun z hz_re hz_im_not_large =>
            have hz_left : a ≤ z.re :=
              le_of_eq hz_re.symm
            have hz_right : z.re ≤ b :=
              le_trans (le_of_eq hz_re) (le_of_lt hab)
            have hz_im : ‖z.im‖ ≤ 1 :=
              le_of_not_ge hz_im_not_large
            have hz_mem : z ∈ verticalStripCompactHeightRectangle a b :=
              ⟨hz_left, hz_right, hz_im⟩
            hC_bound z hz_mem,
          fun z hz_re hz_im_not_large =>
            have hz_left : a ≤ z.re :=
              le_trans (le_of_lt hab) (le_of_eq hz_re.symm)
            have hz_right : z.re ≤ b :=
              le_of_eq hz_re
            have hz_im : ‖z.im‖ ≤ 1 :=
              le_of_not_ge hz_im_not_large
            have hz_mem : z ∈ verticalStripCompactHeightRectangle a b :=
              ⟨hz_left, hz_right, hz_im⟩
            hC_bound z hz_mem⟩

/-- Compact-height boundary control for the cosine-damped family.

This is the compactness package needed after the tail estimate.  It should be
proved by extracting boundary-line `ContinuousOn` data from `DiffContOnCl` on
the closed strip and applying compactness of the two segments `re z = a`,
`‖im z‖ ≤ 1` and `re z = b`, `‖im z‖ ≤ 1`. -/
theorem verticalStripCosineDampedFamily_compact_boundary_bound_ownerGap
    (f : ℂ → ℂ)
    (a b ε : ℝ)
    (hab : a < b)
    (hε : 0 < ε)
    (hhol : DiffContOnCl ℂ f (Complex.re ⁻¹' Set.Ioo a b)) :
    ∃ C : ℝ,
      0 < C ∧
      (∀ z : ℂ,
        z.re = a →
        ¬ 1 ≤ ‖z.im‖ →
        ‖verticalStripCosineDampedFamily f a b ε z‖ ≤ C) ∧
      (∀ z : ℂ,
        z.re = b →
        ¬ 1 ≤ ‖z.im‖ →
        ‖verticalStripCosineDampedFamily f a b ε z‖ ≤ C) := by
  match verticalStripCosineDampedFamily_compactHeightRectangle_bound
      f a b ε hab hhol with
  | ⟨C, hC_pos, hC_bound⟩ =>
      exact
        ⟨C, hC_pos,
          fun z hz_re hz_im_not_large =>
            have hz_left : a ≤ z.re :=
              le_of_eq hz_re.symm
            have hz_right : z.re ≤ b :=
              le_trans (le_of_eq hz_re) (le_of_lt hab)
            have hz_im : ‖z.im‖ ≤ 1 :=
              le_of_not_ge hz_im_not_large
            have hz_mem : z ∈ verticalStripCompactHeightRectangle a b :=
              ⟨hz_left, hz_right, hz_im⟩
            hC_bound z hz_mem,
          fun z hz_re hz_im_not_large =>
            have hz_left : a ≤ z.re :=
              le_trans (le_of_lt hab) (le_of_eq hz_re.symm)
            have hz_right : z.re ≤ b :=
              le_of_eq hz_re
            have hz_im : ‖z.im‖ ≤ 1 :=
              le_of_not_ge hz_im_not_large
            have hz_mem : z ∈ verticalStripCompactHeightRectangle a b :=
              ⟨hz_left, hz_right, hz_im⟩
            hC_bound z hz_mem⟩

/-- The compact-height pieces of the two vertical boundary lines are uniformly
bounded for the cosine-damped family. -/
theorem verticalStripCosineDampedFamily_compact_boundary_bound
    (f : ℂ → ℂ)
    (a b ε : ℝ)
    (hab : a < b)
    (hε : 0 < ε)
    (hhol : DiffContOnCl ℂ f (Complex.re ⁻¹' Set.Ioo a b)) :
    ∃ C : ℝ,
      0 < C ∧
      (∀ z : ℂ,
        z.re = a →
        ¬ 1 ≤ ‖z.im‖ →
        ‖verticalStripCosineDampedFamily f a b ε z‖ ≤ C) ∧
      (∀ z : ℂ,
        z.re = b →
        ¬ 1 ≤ ‖z.im‖ →
        ‖verticalStripCosineDampedFamily f a b ε z‖ ≤ C) := by
  exact
    verticalStripCosineDampedFamily_compact_boundary_bound_ownerGap
      f a b ε hab hε hhol

/-- Compact-height boundary control for the upper-tail tilted damped family. -/
theorem verticalStripUpperTailDampedFamily_compact_boundary_bound
    (f : ℂ → ℂ)
    (a b ε : ℝ)
    (hab : a < b)
    (hhol : DiffContOnCl ℂ f (Complex.re ⁻¹' Set.Ioo a b)) :
    ∃ C : ℝ,
      0 < C ∧
      (∀ z : ℂ,
        z.re = a →
        ¬ 1 ≤ ‖z.im‖ →
        ‖verticalStripUpperTailDampedFamily f a b ε z‖ ≤ C) ∧
      (∀ z : ℂ,
        z.re = b →
        ¬ 1 ≤ ‖z.im‖ →
        ‖verticalStripUpperTailDampedFamily f a b ε z‖ ≤ C) := by
  match verticalStripUpperTailDampedFamily_compactHeightRectangle_bound
      f a b ε hab hhol with
  | ⟨C, hC_pos, hC_bound⟩ =>
      exact
        ⟨C, hC_pos,
          fun z hz_re hz_im_not_large =>
            have hz_left : a ≤ z.re :=
              le_of_eq hz_re.symm
            have hz_right : z.re ≤ b :=
              le_trans (le_of_eq hz_re) (le_of_lt hab)
            have hz_im : ‖z.im‖ ≤ 1 :=
              le_of_not_ge hz_im_not_large
            have hz_mem : z ∈ verticalStripCompactHeightRectangle a b :=
              ⟨hz_left, hz_right, hz_im⟩
            hC_bound z hz_mem,
          fun z hz_re hz_im_not_large =>
            have hz_left : a ≤ z.re :=
              le_trans (le_of_lt hab) (le_of_eq hz_re.symm)
            have hz_right : z.re ≤ b :=
              le_of_eq hz_re
            have hz_im : ‖z.im‖ ≤ 1 :=
              le_of_not_ge hz_im_not_large
            have hz_mem : z ∈ verticalStripCompactHeightRectangle a b :=
              ⟨hz_left, hz_right, hz_im⟩
            hC_bound z hz_mem⟩

/-- Compact-height boundary control for the subcritical cosine-damped family. -/
theorem verticalStripSubcriticalCosineDampedFamily_compact_boundary_bound
    (f : ℂ → ℂ)
    (a b d ε : ℝ)
    (hab : a < b)
    (hhol : DiffContOnCl ℂ f (Complex.re ⁻¹' Set.Ioo a b)) :
    ∃ C : ℝ,
      0 < C ∧
      (∀ z : ℂ,
        z.re = a →
        ¬ 1 ≤ ‖z.im‖ →
        ‖verticalStripSubcriticalCosineDampedFamily f a b d ε z‖ ≤ C) ∧
      (∀ z : ℂ,
        z.re = b →
        ¬ 1 ≤ ‖z.im‖ →
        ‖verticalStripSubcriticalCosineDampedFamily f a b d ε z‖ ≤ C) := by
  match verticalStripSubcriticalCosineDampedFamily_compactHeightRectangle_bound
      f a b d ε hab hhol with
  | ⟨C, hC_pos, hC_bound⟩ =>
      exact
        ⟨C, hC_pos,
          fun z hz_re hz_im_not_large =>
            have hz_left : a ≤ z.re :=
              le_of_eq hz_re.symm
            have hz_right : z.re ≤ b :=
              le_trans (le_of_eq hz_re) (le_of_lt hab)
            have hz_im : ‖z.im‖ ≤ 1 :=
              le_of_not_ge hz_im_not_large
            have hz_mem : z ∈ verticalStripCompactHeightRectangle a b :=
              ⟨hz_left, hz_right, hz_im⟩
            hC_bound z hz_mem,
          fun z hz_re hz_im_not_large =>
            have hz_left : a ≤ z.re :=
              le_trans (le_of_lt hab) (le_of_eq hz_re.symm)
            have hz_right : z.re ≤ b :=
              le_of_eq hz_re
            have hz_im : ‖z.im‖ ≤ 1 :=
              le_of_not_ge hz_im_not_large
            have hz_mem : z ∈ verticalStripCompactHeightRectangle a b :=
              ⟨hz_left, hz_right, hz_im⟩
            hC_bound z hz_mem⟩

/-- The subcritical cosine-damped family satisfies the finite-order closed-strip
estimate obtained by combining its two-sided tail boundary package, compact
boundary control, and the bounded-boundary strip Phragmen-Lindelöf theorem. -/
theorem verticalStripSubcriticalCosineDampedFamily_finiteOrder_growth_of_boundary_envelope
    (f : ℂ → ℂ)


    {a b d ε A B : ℝ}
    {m : ℕ}
    (hab : a < b)
    (hd_pos : 0 < d)
    (hd_threshold : d < π / (b - a))
    (hε_pos : 0 < ε)
    (hA : 0 < A)
    (hB : 0 < B)
    (hhol : DiffContOnCl ℂ f (Complex.re ⁻¹' Set.Ioo a b))
    (hfinite :
      ∃ c : ℝ,
        c < Real.pi / (b - a) ∧
        ∃ D : ℝ,
          f =O[
              Filter.comap (_root_.abs ∘ Complex.im) Filter.atTop ⊓
                𝓟 (Complex.re ⁻¹' Set.Ioo a b)]
            fun z : ℂ => Real.exp (D * Real.exp (c * |z.im|)))
    (hleft :
      ∀ z : ℂ,
        z.re = a →
        1 ≤ ‖z.im‖ →
        ‖f z‖ ≤ A * Real.exp (B * (1 + ‖z.im‖) ^ m))
    (hright :
      ∀ z : ℂ,
        z.re = b →
        1 ≤ ‖z.im‖ →
        ‖f z‖ ≤ A * Real.exp (B * (1 + ‖z.im‖) ^ m)) :
    ∃ A' : ℝ, ∃ B' : ℝ, ∃ m' : ℕ,
      0 < A' ∧
      0 < B' ∧
      ∀ z : ℂ,
        a ≤ z.re →
        z.re ≤ b →
        1 ≤ ‖z.im‖ →
        ‖verticalStripSubcriticalCosineDampedFamily f a b d ε z‖ ≤
          A' * Real.exp (B' * (1 + ‖z‖) ^ m') := by
  have hpackage :
      DiffContOnCl ℂ (verticalStripSubcriticalCosineDampedFamily f a b d ε)
          (Complex.re ⁻¹' Set.Ioo a b) ∧
        ∃ c : ℝ,
          c < Real.pi / (b - a) ∧
          ∃ D : ℝ,
            verticalStripSubcriticalCosineDampedFamily f a b d ε =O[
                Filter.comap (_root_.abs ∘ Complex.im) Filter.atTop ⊓
                  𝓟 (Complex.re ⁻¹' Set.Ioo a b)]
              fun z : ℂ => Real.exp (D * Real.exp (c * |z.im|)) :=
    verticalStripSubcriticalCosineDampedFamily_analytic_growth_package
      f a b d ε hab hd_pos hd_threshold hε_pos hhol hfinite
  have htail :
      ∃ C : ℝ,
        0 < C ∧
        (∀ z : ℂ,
          z.re = a →
          1 ≤ ‖z.im‖ →
          ‖verticalStripSubcriticalCosineDampedFamily f a b d ε z‖ ≤ C) ∧
        (∀ z : ℂ,
          z.re = b →
          1 ≤ ‖z.im‖ →
          ‖verticalStripSubcriticalCosineDampedFamily f a b d ε z‖ ≤ C) :=
    verticalStripSubcriticalCosineDampedFamily_tail_boundary_package
      f hab hd_pos hd_threshold hε_pos hA hB hhol hleft hright
  have hcompact :
      ∃ C : ℝ,
        0 < C ∧
        (∀ z : ℂ,
          z.re = a →
          ¬ 1 ≤ ‖z.im‖ →
          ‖verticalStripSubcriticalCosineDampedFamily f a b d ε z‖ ≤ C) ∧
        (∀ z : ℂ,
          z.re = b →
          ¬ 1 ≤ ‖z.im‖ →
          ‖verticalStripSubcriticalCosineDampedFamily f a b d ε z‖ ≤ C) :=
    verticalStripSubcriticalCosineDampedFamily_compact_boundary_bound
      f a b d ε hab hhol
  exact
    strip_finite_order_growth_of_tail_compact_boundary_package
      (verticalStripSubcriticalCosineDampedFamily f a b d ε)
      a b hab hpackage.1 hpackage.2 htail hcompact


end
end LFunctions
end Boundary
