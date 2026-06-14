import Mathlib.Analysis.Complex.PhragmenLindelof

/-!
# Punctured vertical strip geometry

This file owns the elementary corridor geometry of the punctured vertical strip
`0 < Re z < 2`, `z ≠ 1`.  Analytic files should consume these owner-level
facts instead of reproving the strip routing inside zeta-specific files.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open scoped Filter Topology Convex

/-- The real inequality `2 < 3`, written without numeric automation. -/
theorem real_two_lt_three :
    (2 : ℝ) < 3 := by
  calc
    (2 : ℝ) = 1 + 1 := by
      exact (one_add_one_eq_two : (1 : ℝ) + 1 = 2).symm
    _ < 1 + 2 := add_lt_add_left one_lt_two 1
    _ = 3 := by
      exact (congrArg (fun x : ℝ => 1 + x) (one_add_one_eq_two : (1 : ℝ) + 1 = 2)).trans
        (show (1 : ℝ) + (1 + 1) = 3 from two_add_one_eq_three)

/-- The real inequality `3 < 4`, written without numeric automation. -/
theorem real_three_lt_four :
    (3 : ℝ) < 4 := by
  calc
    (3 : ℝ) = 1 + 2 := by
      exact
        (show (1 : ℝ) + 2 = 3 by
          calc
            (1 : ℝ) + 2 = 2 + 1 := add_comm 1 2
            _ = 3 := two_add_one_eq_three).symm
    _ < 2 + 2 := add_lt_add_right one_lt_two 2
    _ = 4 := by
      exact two_add_two_eq_four

/-- The punctured vertical strip used by the Euler-Maclaurin identity theorem:
`0 < Re z < 2`, with the point `1` removed. -/
def puncturedVerticalStrip : Set ℂ :=
  {z : ℂ | 0 < z.re ∧ z.re < 2 ∧ z ≠ 1}

/-- A point with nonzero imaginary part is not the deleted point `1`. -/
theorem puncturedVerticalStrip_ne_one_of_im_ne_zero
    {p : ℂ}
    (hp_im : p.im ≠ 0) :
    p ≠ 1 := by
  intro hp
  have hp_im_zero : p.im = 0 := by
    exact (congrArg Complex.im hp).trans (Complex.ofReal_im (1 : ℝ))
  exact hp_im hp_im_zero

/-- A point whose real part is not `1` is not the deleted point `1`. -/
theorem puncturedVerticalStrip_ne_one_of_re_ne_one
    {p : ℂ}
    (hp_re : p.re ≠ 1) :
    p ≠ 1 := by
  intro hp
  have hp_re_one : p.re = 1 := by
    exact (congrArg Complex.re hp).trans (Complex.ofReal_re (1 : ℝ))
  exact hp_re hp_re_one

/-- Horizontal real-coordinate bounds inherited from the endpoints. -/
theorem puncturedVerticalStrip_horizontalSegment_re_bounds
    {z w p : ℂ}
    (hz : z ∈ puncturedVerticalStrip)
    (hw : w ∈ puncturedVerticalStrip)
    (hp_re : p.re ∈ Set.Icc z.re w.re ∨ p.re ∈ Set.Icc w.re z.re) :
    0 < p.re ∧ p.re < 2 := by
  rcases hz with ⟨hz0, hz2, _⟩
  rcases hw with ⟨hw0, hw2, _⟩
  rcases hp_re with hp_re | hp_re
  · exact ⟨lt_of_lt_of_le hz0 hp_re.1, lt_of_le_of_lt hp_re.2 hw2⟩
  · exact ⟨lt_of_lt_of_le hw0 hp_re.1, lt_of_le_of_lt hp_re.2 hz2⟩

/-- Vertical real-coordinate bounds are constant along the vertical segment. -/
theorem puncturedVerticalStrip_verticalSegment_re_bounds
    {z p : ℂ}
    (hz : z ∈ puncturedVerticalStrip)
    (hp_re : p.re = z.re) :
    0 < p.re ∧ p.re < 2 := by
  rcases hz with ⟨hz0, hz2, _⟩
  exact ⟨hp_re ▸ hz0, hp_re ▸ hz2⟩

/-- Horizontal segments at nonzero imaginary height stay inside the punctured
vertical strip once their endpoints lie in the strip. -/
theorem puncturedVerticalStrip_horizontalSegment_mem
    {z w p : ℂ}
    (hz : z ∈ puncturedVerticalStrip)
    (hw : w ∈ puncturedVerticalStrip)
    (hp_re : p.re ∈ Set.Icc z.re w.re ∨ p.re ∈ Set.Icc w.re z.re)
    (hp_im : p.im = z.im)
    (_hzw_im : z.im = w.im)
    (hz_im : z.im ≠ 0) :
    p ∈ puncturedVerticalStrip := by
  have hp_bounds :=
    puncturedVerticalStrip_horizontalSegment_re_bounds hz hw hp_re
  have hp_im_ne : p.im ≠ 0 := by
    intro hp_zero
    exact hz_im (hp_im.symm.trans hp_zero)
  exact ⟨hp_bounds.1, hp_bounds.2, puncturedVerticalStrip_ne_one_of_im_ne_zero hp_im_ne⟩

/-- Vertical segments at real part different from `1` stay inside the
punctured vertical strip once their endpoints lie in the strip. -/
theorem puncturedVerticalStrip_verticalSegment_mem
    {z w p : ℂ}
    (hz : z ∈ puncturedVerticalStrip)
    (_hw : w ∈ puncturedVerticalStrip)
    (hp_re : p.re = z.re)
    (_hp_im : p.im ∈ Set.Icc z.im w.im ∨ p.im ∈ Set.Icc w.im z.im)
    (_hzw_re : z.re = w.re)
    (hz_re : z.re ≠ 1) :
    p ∈ puncturedVerticalStrip := by
  have hp_bounds :=
    puncturedVerticalStrip_verticalSegment_re_bounds hz hp_re
  have hp_re_ne : p.re ≠ 1 := by
    intro hp_one
    exact hz_re (hp_re.symm.trans hp_one)
  exact ⟨hp_bounds.1, hp_bounds.2, puncturedVerticalStrip_ne_one_of_re_ne_one hp_re_ne⟩

/-- The left safe corridor has positive real coordinate. -/
theorem puncturedVerticalStrip_zero_lt_leftCorridor_re :
    (0 : ℝ) < 1 / 2 := by
  exact div_pos zero_lt_one zero_lt_two

/-- The left safe corridor lies left of the deleted vertical line. -/
theorem puncturedVerticalStrip_leftCorridor_re_lt_one :
    (1 / 2 : ℝ) < 1 := by
  exact
    (div_lt_iff₀ zero_lt_two).mpr
      (calc
        (1 : ℝ) < 1 * 2 := by
          rw [one_mul]
          exact one_lt_two)

/-- The left safe corridor lies inside the right strip boundary. -/
theorem puncturedVerticalStrip_leftCorridor_re_lt_two :
    (1 / 2 : ℝ) < 2 := by
  exact lt_trans puncturedVerticalStrip_leftCorridor_re_lt_one one_lt_two

/-- The right safe corridor has positive real coordinate. -/
theorem puncturedVerticalStrip_zero_lt_rightCorridor_re :
    (0 : ℝ) < 3 / 2 := by
  exact div_pos (lt_trans zero_lt_two real_two_lt_three) zero_lt_two

/-- The right safe corridor lies right of the deleted vertical line. -/
theorem puncturedVerticalStrip_one_lt_rightCorridor_re :
    (1 : ℝ) < 3 / 2 := by
  exact
    (lt_div_iff₀ zero_lt_two).mpr
      (calc
        (1 : ℝ) * 2 = 2 := one_mul 2
        _ < 3 := real_two_lt_three)

/-- The right safe corridor lies inside the right strip boundary. -/
theorem puncturedVerticalStrip_rightCorridor_re_lt_two :
    (3 / 2 : ℝ) < 2 := by
  exact
    (div_lt_iff₀ zero_lt_two).mpr
      (calc
        (3 : ℝ) < 4 := real_three_lt_four
        _ = 2 * 2 := by
          exact (two_mul (2 : ℝ)).symm)

/-- The left safe vertical corridor is not the deleted point. -/
theorem puncturedVerticalStrip_leftCorridor_ne_one
    {y : ℝ} :
    Complex.mk (1 / 2) y ≠ (1 : ℂ) := by
  exact
    puncturedVerticalStrip_ne_one_of_re_ne_one
      (ne_of_lt puncturedVerticalStrip_leftCorridor_re_lt_one)

/-- The right safe vertical corridor is not the deleted point. -/
theorem puncturedVerticalStrip_rightCorridor_ne_one
    {y : ℝ} :
    Complex.mk (3 / 2) y ≠ (1 : ℂ) := by
  exact
    puncturedVerticalStrip_ne_one_of_re_ne_one
      (ne_of_gt puncturedVerticalStrip_one_lt_rightCorridor_re)

/-- The left safe vertical corridor lies in the punctured strip. -/
theorem puncturedVerticalStrip_leftCorridor_mem
    {y : ℝ} :
    Complex.mk (1 / 2) y ∈ puncturedVerticalStrip :=
  ⟨puncturedVerticalStrip_zero_lt_leftCorridor_re,
    puncturedVerticalStrip_leftCorridor_re_lt_two,
    puncturedVerticalStrip_leftCorridor_ne_one⟩

/-- The right safe vertical corridor lies in the punctured strip. -/
theorem puncturedVerticalStrip_rightCorridor_mem
    {y : ℝ} :
    Complex.mk (3 / 2) y ∈ puncturedVerticalStrip :=
  ⟨puncturedVerticalStrip_zero_lt_rightCorridor_re,
    puncturedVerticalStrip_rightCorridor_re_lt_two,
    puncturedVerticalStrip_rightCorridor_ne_one⟩

/-- Real coordinate of the real affine line map in `ℂ`. -/
theorem complex_lineMap_re
    (z w : ℂ)
    (t : ℝ) :
    (AffineMap.lineMap z w t).re = (1 - t) * z.re + t * w.re := by
  calc
    (AffineMap.lineMap z w t).re = ((1 - t) • z + t • w).re :=
      congrArg Complex.re (AffineMap.lineMap_apply_module z w t)
    _ = ((1 - t) • z).re + (t • w).re :=
      Complex.add_re ((1 - t) • z) (t • w)
    _ = (1 - t) * z.re + t * w.re := by
      rw [Complex.smul_re, Complex.smul_re]

/-- Imaginary coordinate of the real affine line map in `ℂ`. -/
theorem complex_lineMap_im
    (z w : ℂ)
    (t : ℝ) :
    (AffineMap.lineMap z w t).im = (1 - t) * z.im + t * w.im := by
  calc
    (AffineMap.lineMap z w t).im = ((1 - t) • z + t • w).im :=
      congrArg Complex.im (AffineMap.lineMap_apply_module z w t)
    _ = ((1 - t) • z).im + (t • w).im :=
      Complex.add_im ((1 - t) • z) (t • w)
    _ = (1 - t) * z.im + t * w.im := by
      rw [Complex.smul_im, Complex.smul_im]

/-- Real coordinate of a point on a complex affine segment. -/
theorem complex_segment_re_eq
    {z w p : ℂ}
    (hp : p ∈ [z -[ℝ] w]) :
    ∃ t : ℝ,
      t ∈ Set.Icc (0 : ℝ) 1 ∧
        p.re = (1 - t) * z.re + t * w.re := by
  rw [segment_eq_image ℝ z w] at hp
  rcases hp with ⟨t, ht, rfl⟩
  refine ⟨t, ht, ?_⟩
  exact complex_lineMap_re z w t

/-- Imaginary coordinate of a point on a complex affine segment. -/
theorem complex_segment_im_eq
    {z w p : ℂ}
    (hp : p ∈ [z -[ℝ] w]) :
    ∃ t : ℝ,
      t ∈ Set.Icc (0 : ℝ) 1 ∧
        p.im = (1 - t) * z.im + t * w.im := by
  rw [segment_eq_image ℝ z w] at hp
  rcases hp with ⟨t, ht, rfl⟩
  refine ⟨t, ht, ?_⟩
  exact complex_lineMap_im z w t

/-- Coordinate package for a point on a complex affine segment. -/
theorem complex_segment_coordinates
    {z w p : ℂ}
    (hp : p ∈ [z -[ℝ] w]) :
    ∃ t : ℝ,
      t ∈ Set.Icc (0 : ℝ) 1 ∧
        p.re = (1 - t) * z.re + t * w.re ∧
        p.im = (1 - t) * z.im + t * w.im := by
  rw [segment_eq_image ℝ z w] at hp
  rcases hp with ⟨t, ht, rfl⟩
  refine ⟨t, ht, ?_, ?_⟩
  · exact complex_lineMap_re z w t
  · exact complex_lineMap_im z w t

/-- The affine combination of two equal real endpoints is the endpoint. -/
theorem real_affine_combination_same
    (t x : ℝ) :
    (1 - t) * x + t * x = x := by
  calc
    (1 - t) * x + t * x = (1 * x - t * x) + t * x :=
      congrArg (fun u : ℝ => u + t * x) (sub_mul 1 t x)
    _ = (x - t * x) + t * x :=
      congrArg (fun u : ℝ => (u - t * x) + t * x) (one_mul x)
    _ = x :=
      sub_add_cancel x (t * x)

/-- A real affine combination with parameter in `[0,1]` stays between ordered
endpoints. -/
theorem real_affine_combination_mem_Icc_of_le
    {x y t : ℝ}
    (ht : t ∈ Set.Icc (0 : ℝ) 1)
    (hxy : x ≤ y) :
    (1 - t) * x + t * y ∈ Set.Icc x y := by
  have hx : x ∈ Set.Icc x y := ⟨le_rfl, hxy⟩
  have hy : y ∈ Set.Icc x y := ⟨hxy, le_rfl⟩
  have hline :
      AffineMap.lineMap x y t ∈ Set.Icc x y :=
    (convex_Icc x y).lineMap_mem hx hy ht
  exact Eq.subst
    (motive := fun u : ℝ => u ∈ Set.Icc x y)
    (AffineMap.lineMap_apply_ring x y t)
    hline

/-- If `t ∈ [0,1]`, then `1 - t ∈ [0,1]`. -/
theorem one_sub_mem_Icc_zero_one
    {t : ℝ}
    (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    1 - t ∈ Set.Icc (0 : ℝ) 1 :=
  ⟨sub_nonneg.mpr ht.2, sub_le_self 1 ht.1⟩

/-- Reversing the endpoints of a real affine combination amounts to replacing
`t` by `1 - t`. -/
theorem real_affine_combination_reverse
    (t x y : ℝ) :
    (1 - t) * x + t * y =
      (1 - (1 - t)) * y + (1 - t) * x := by
  calc
    (1 - t) * x + t * y = t * y + (1 - t) * x :=
      add_comm ((1 - t) * x) (t * y)
    _ = (1 - (1 - t)) * y + (1 - t) * x :=
      congrArg (fun u : ℝ => u * y + (1 - t) * x) (sub_sub_cancel 1 t).symm

/-- A real affine combination with parameter in `[0,1]` lies in one of the two
closed intervals determined by its endpoints. -/
theorem real_affine_combination_mem_Icc_or_Icc
    {x y t : ℝ}
    (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    (1 - t) * x + t * y ∈ Set.Icc x y ∨
      (1 - t) * x + t * y ∈ Set.Icc y x := by
  by_cases hxy : x ≤ y
  · exact Or.inl (real_affine_combination_mem_Icc_of_le ht hxy)
  · have hyx : y ≤ x := le_of_not_ge hxy
    have hmem :
        (1 - (1 - t)) * y + (1 - t) * x ∈ Set.Icc y x :=
      real_affine_combination_mem_Icc_of_le
        (one_sub_mem_Icc_zero_one ht)
        hyx
    exact Or.inr ((real_affine_combination_reverse t x y).symm ▸ hmem)

/-- Strict lower bound for a real affine combination whose endpoints both lie
strictly above the lower bound. -/
theorem lower_lt_real_affine_combination
    {a x y t : ℝ}
    (ht : t ∈ Set.Icc (0 : ℝ) 1)
    (hx : a < x)
    (hy : a < y) :
    a < (1 - t) * x + t * y := by
  rcases real_affine_combination_mem_Icc_or_Icc (x := x) (y := y) ht with hmem | hmem
  · exact lt_of_lt_of_le hx hmem.1
  · exact lt_of_lt_of_le hy hmem.1

/-- Strict upper bound for a real affine combination whose endpoints both lie
strictly below the upper bound. -/
theorem real_affine_combination_lt_upper
    {a x y t : ℝ}
    (ht : t ∈ Set.Icc (0 : ℝ) 1)
    (hx : x < a)
    (hy : y < a) :
    (1 - t) * x + t * y < a := by
  rcases real_affine_combination_mem_Icc_or_Icc (x := x) (y := y) ht with hmem | hmem
  · exact lt_of_le_of_lt hmem.2 hy
  · exact lt_of_le_of_lt hmem.2 hx

/-- Horizontal complex segments have constant imaginary coordinate. -/
theorem complex_horizontal_segment_im
    {x₁ x₂ h : ℝ} {p : ℂ}
    (hp : p ∈ [Complex.mk x₁ h -[ℝ] Complex.mk x₂ h]) :
    p.im = h := by
  rcases complex_segment_coordinates hp with ⟨t, ht, _hre, him⟩
  calc
    p.im = (1 - t) * h + t * h := him
    _ = h := real_affine_combination_same t h

/-- Horizontal complex segment real coordinates lie between endpoint real
coordinates. -/
theorem complex_horizontal_segment_re_mem_Icc_or_Icc
    {x₁ x₂ h : ℝ} {p : ℂ}
    (hp : p ∈ [Complex.mk x₁ h -[ℝ] Complex.mk x₂ h]) :
    p.re ∈ Set.Icc x₁ x₂ ∨ p.re ∈ Set.Icc x₂ x₁ := by
  rcases complex_segment_coordinates hp with ⟨t, ht, hre, _him⟩
  by_cases hle : x₁ ≤ x₂
  · left
    exact hre ▸ real_affine_combination_mem_Icc_of_le ht hle
  · right
    have hle' : x₂ ≤ x₁ := le_of_not_ge hle
    have hmem :
        (1 - t) * x₁ + t * x₂ ∈ Set.Icc x₂ x₁ :=
      (real_affine_combination_mem_Icc_or_Icc (x := x₁) (y := x₂) ht).resolve_left
        (fun hmem => hle (hmem.1.trans hmem.2))
    exact hre ▸ hmem

/-- Vertical complex segments have constant real coordinate. -/
theorem complex_vertical_segment_re
    {x y₁ y₂ : ℝ} {p : ℂ}
    (hp : p ∈ [Complex.mk x y₁ -[ℝ] Complex.mk x y₂]) :
    p.re = x := by
  rcases complex_segment_coordinates hp with ⟨t, ht, hre, _him⟩
  calc
    p.re = (1 - t) * x + t * x := hre
    _ = x := real_affine_combination_same t x

/-- Vertical complex segment imaginary coordinates lie between endpoint
imaginary coordinates. -/
theorem complex_vertical_segment_im_mem_Icc_or_Icc
    {x y₁ y₂ : ℝ} {p : ℂ}
    (hp : p ∈ [Complex.mk x y₁ -[ℝ] Complex.mk x y₂]) :
    p.im ∈ Set.Icc y₁ y₂ ∨ p.im ∈ Set.Icc y₂ y₁ := by
  rcases complex_segment_coordinates hp with ⟨t, ht, _hre, him⟩
  by_cases hle : y₁ ≤ y₂
  · left
    exact him ▸ real_affine_combination_mem_Icc_of_le ht hle
  · right
    have hle' : y₂ ≤ y₁ := le_of_not_ge hle
    have hmem :
        (1 - t) * y₁ + t * y₂ ∈ Set.Icc y₂ y₁ :=
      (real_affine_combination_mem_Icc_or_Icc (x := y₁) (y := y₂) ht).resolve_left
        (fun hmem => hle (hmem.1.trans hmem.2))
    exact him ▸ hmem

/-- Explicit horizontal segment containment at nonzero height. -/
theorem puncturedVerticalStrip_horizontal_segment_subset
    {x₁ x₂ h : ℝ}
    (hx₁_left : 0 < x₁)
    (hx₁_right : x₁ < 2)
    (hx₂_left : 0 < x₂)
    (hx₂_right : x₂ < 2)
    (hh : h ≠ 0) :
    [Complex.mk x₁ h -[ℝ] Complex.mk x₂ h] ⊆ puncturedVerticalStrip := by
  intro p hp
  exact
    puncturedVerticalStrip_horizontalSegment_mem
      ⟨hx₁_left, hx₁_right, puncturedVerticalStrip_ne_one_of_im_ne_zero hh⟩
      ⟨hx₂_left, hx₂_right, puncturedVerticalStrip_ne_one_of_im_ne_zero hh⟩
      (complex_horizontal_segment_re_mem_Icc_or_Icc hp)
      (complex_horizontal_segment_im hp)
      rfl
      hh

/-- Explicit vertical segment containment in a safe corridor. -/
theorem puncturedVerticalStrip_vertical_segment_subset
    {x y₁ y₂ : ℝ}
    (hx_left : 0 < x)
    (hx_right : x < 2)
    (hx_ne : x ≠ 1) :
    [Complex.mk x y₁ -[ℝ] Complex.mk x y₂] ⊆ puncturedVerticalStrip := by
  intro p hp
  exact
    puncturedVerticalStrip_verticalSegment_mem
      ⟨hx_left, hx_right, puncturedVerticalStrip_ne_one_of_re_ne_one hx_ne⟩
      ⟨hx_left, hx_right, puncturedVerticalStrip_ne_one_of_re_ne_one hx_ne⟩
      (complex_vertical_segment_re hp)
      (complex_vertical_segment_im_mem_Icc_or_Icc hp)
      rfl
      hx_ne

/-- A segment whose endpoints lie in the left half of the strip stays inside
the punctured strip. -/
theorem puncturedVerticalStrip_leftHalf_segment_subset
    {z w : ℂ}
    (hz : z ∈ puncturedVerticalStrip)
    (hw : w ∈ puncturedVerticalStrip)
    (hz_left : z.re < 1)
    (hw_left : w.re < 1) :
    [z -[ℝ] w] ⊆ puncturedVerticalStrip := by
  intro p hp
  rcases hz with ⟨hz0, _hz2, _hzne⟩
  rcases hw with ⟨hw0, _hw2, _hwne⟩
  rcases complex_segment_coordinates hp with ⟨t, ht, hre, _him⟩
  have hp0 : 0 < p.re := by
    exact hre ▸ lower_lt_real_affine_combination ht hz0 hw0
  have hp1 : p.re < 1 := by
    exact hre ▸ real_affine_combination_lt_upper ht hz_left hw_left
  have hp2 : p.re < 2 := lt_trans hp1 one_lt_two
  have hp_ne : p ≠ 1 :=
    puncturedVerticalStrip_ne_one_of_re_ne_one
      (fun hp_re_one => (lt_irrefl (1 : ℝ)) (hp_re_one ▸ hp1))
  exact ⟨hp0, hp2, hp_ne⟩

/-- A segment whose endpoints lie in the right half of the strip stays inside
the punctured strip. -/
theorem puncturedVerticalStrip_rightHalf_segment_subset
    {z w : ℂ}
    (hz : z ∈ puncturedVerticalStrip)
    (hw : w ∈ puncturedVerticalStrip)
    (hz_right : 1 < z.re)
    (hw_right : 1 < w.re) :
    [z -[ℝ] w] ⊆ puncturedVerticalStrip := by
  intro p hp
  rcases hz with ⟨_hz0, hz2, _hzne⟩
  rcases hw with ⟨_hw0, hw2, _hwne⟩
  rcases complex_segment_coordinates hp with ⟨t, ht, hre, _him⟩
  have hp1 : 1 < p.re := by
    exact hre ▸ lower_lt_real_affine_combination ht hz_right hw_right
  have hp0 : 0 < p.re := lt_trans zero_lt_one hp1
  have hp2 : p.re < 2 := by
    exact hre ▸ real_affine_combination_lt_upper ht hz2 hw2
  have hp_ne : p ≠ 1 :=
    puncturedVerticalStrip_ne_one_of_re_ne_one
      (fun hp_re_one => (lt_irrefl (1 : ℝ)) (hp_re_one ▸ hp1))
  exact ⟨hp0, hp2, hp_ne⟩

/-- Horizontal segments at nonzero height cross safely between any two real
parts in the open strip. -/
theorem puncturedVerticalStrip_nonzeroHeight_horizontalJoined
    {x₁ x₂ h : ℝ}
    (hx₁_left : 0 < x₁)
    (hx₁_right : x₁ < 2)
    (hx₂_left : 0 < x₂)
    (hx₂_right : x₂ < 2)
    (hh : h ≠ 0) :
    JoinedIn
      puncturedVerticalStrip
      (Complex.mk x₁ h)
      (Complex.mk x₂ h) :=
  JoinedIn.of_segment_subset
    (puncturedVerticalStrip_horizontal_segment_subset
      hx₁_left hx₁_right hx₂_left hx₂_right hh)

/-- The left half-column is a safe vertical corridor inside the punctured
strip. -/
theorem puncturedVerticalStrip_leftColumn_verticalJoined
    {y₁ y₂ : ℝ} :
    JoinedIn
      puncturedVerticalStrip
      (Complex.mk (1 / 2) y₁)
      (Complex.mk (1 / 2) y₂) :=
  JoinedIn.of_segment_subset
    (puncturedVerticalStrip_vertical_segment_subset
      puncturedVerticalStrip_zero_lt_leftCorridor_re
      puncturedVerticalStrip_leftCorridor_re_lt_two
      (ne_of_lt puncturedVerticalStrip_leftCorridor_re_lt_one))

/-- The right half-column is a safe vertical corridor inside the punctured
strip. -/
theorem puncturedVerticalStrip_rightColumn_verticalJoined
    {y₁ y₂ : ℝ} :
    JoinedIn
      puncturedVerticalStrip
      (Complex.mk (3 / 2) y₁)
      (Complex.mk (3 / 2) y₂) :=
  JoinedIn.of_segment_subset
    (puncturedVerticalStrip_vertical_segment_subset
      puncturedVerticalStrip_zero_lt_rightCorridor_re
      puncturedVerticalStrip_rightCorridor_re_lt_two
      (ne_of_gt puncturedVerticalStrip_one_lt_rightCorridor_re))

/-- Points in the left component `0 < Re z < 1` of the punctured strip are
joined inside the punctured strip. -/
theorem puncturedVerticalStrip_leftHalf_joined
    {z w : ℂ}
    (hz : z ∈ puncturedVerticalStrip)
    (hw : w ∈ puncturedVerticalStrip)
    (hz_left : z.re < 1)
    (hw_left : w.re < 1) :
    JoinedIn puncturedVerticalStrip z w :=
  JoinedIn.of_segment_subset
    (puncturedVerticalStrip_leftHalf_segment_subset hz hw hz_left hw_left)

/-- Points in the right component `1 < Re z < 2` of the punctured strip are
joined inside the punctured strip. -/
theorem puncturedVerticalStrip_rightHalf_joined
    {z w : ℂ}
    (hz : z ∈ puncturedVerticalStrip)
    (hw : w ∈ puncturedVerticalStrip)
    (hz_right : 1 < z.re)
    (hw_right : 1 < w.re) :
    JoinedIn puncturedVerticalStrip z w :=
  JoinedIn.of_segment_subset
    (puncturedVerticalStrip_rightHalf_segment_subset hz hw hz_right hw_right)

/-- Every point in the punctured strip is joined to one of the two safe
vertical corridors at its own imaginary height. -/
theorem puncturedVerticalStrip_joinedTo_safeCorridor
    {z : ℂ}
    (hz : z ∈ puncturedVerticalStrip) :
    JoinedIn
        puncturedVerticalStrip
        z
        (Complex.mk (1 / 2) z.im) ∨
      JoinedIn
        puncturedVerticalStrip
        z
        (Complex.mk (3 / 2) z.im) := by
  rcases hz with ⟨hz0, hz2, hz_ne⟩
  by_cases hz_im : z.im = 0
  · have hz_re_ne : z.re ≠ 1 := by
      intro hz_re
      have hz_eq_one : z = 1 := by
        ext
        · exact hz_re
        · exact hz_im.trans (Complex.ofReal_im (1 : ℝ)).symm
      exact hz_ne hz_eq_one
    rcases lt_or_gt_of_ne hz_re_ne with hz_left | hz_right
    · left
      exact
        puncturedVerticalStrip_leftHalf_joined
          ⟨hz0, hz2, hz_ne⟩
          puncturedVerticalStrip_leftCorridor_mem
          hz_left
          puncturedVerticalStrip_leftCorridor_re_lt_one
    · right
      exact
        puncturedVerticalStrip_rightHalf_joined
          ⟨hz0, hz2, hz_ne⟩
          puncturedVerticalStrip_rightCorridor_mem
          hz_right
          puncturedVerticalStrip_one_lt_rightCorridor_re
  · left
    have hz_eq : Complex.mk z.re z.im = z := by
      exact Complex.ext rfl rfl
    exact hz_eq ▸
      puncturedVerticalStrip_nonzeroHeight_horizontalJoined
        hz0
        hz2
        puncturedVerticalStrip_zero_lt_leftCorridor_re
        puncturedVerticalStrip_leftCorridor_re_lt_two
        hz_im

/-- The two safe vertical corridors are joined at any nonzero imaginary
height. -/
theorem puncturedVerticalStrip_leftCorridor_joined_rightCorridor
    {h : ℝ}
    (hh : h ≠ 0) :
    JoinedIn
      puncturedVerticalStrip
      (Complex.mk (1 / 2) h)
      (Complex.mk (3 / 2) h) :=
  puncturedVerticalStrip_nonzeroHeight_horizontalJoined
    puncturedVerticalStrip_zero_lt_leftCorridor_re
    puncturedVerticalStrip_leftCorridor_re_lt_two
    puncturedVerticalStrip_zero_lt_rightCorridor_re
    puncturedVerticalStrip_rightCorridor_re_lt_two
    hh

/-- Corridor polygonal-path construction in the punctured vertical strip. -/
theorem puncturedVerticalStrip_joinedIn_via_corridors
    {z w : ℂ}
    (hz : z ∈ puncturedVerticalStrip)
    (hw : w ∈ puncturedVerticalStrip) :
    JoinedIn puncturedVerticalStrip z w := by
  rcases puncturedVerticalStrip_joinedTo_safeCorridor hz with hz_left | hz_right
  · rcases puncturedVerticalStrip_joinedTo_safeCorridor hw with hw_left | hw_right
    · have hz_to_detour :
          JoinedIn
            puncturedVerticalStrip
            (Complex.mk (1 / 2) z.im)
            (Complex.mk (1 / 2) (1 : ℝ)) :=
        puncturedVerticalStrip_leftColumn_verticalJoined
      have hw_to_detour :
          JoinedIn
            puncturedVerticalStrip
            (Complex.mk (1 / 2) w.im)
            (Complex.mk (1 / 2) (1 : ℝ)) :=
        puncturedVerticalStrip_leftColumn_verticalJoined
      exact
        (hz_left.trans hz_to_detour).trans
          (hw_to_detour.symm.trans hw_left.symm)
    · have hz_to_left_detour :
          JoinedIn
            puncturedVerticalStrip
            (Complex.mk (1 / 2) z.im)
            (Complex.mk (1 / 2) (1 : ℝ)) :=
        puncturedVerticalStrip_leftColumn_verticalJoined
      have left_to_right_detour :
          JoinedIn
            puncturedVerticalStrip
            (Complex.mk (1 / 2) (1 : ℝ))
            (Complex.mk (3 / 2) (1 : ℝ)) :=
        puncturedVerticalStrip_leftCorridor_joined_rightCorridor one_ne_zero
      have hw_to_right_detour :
          JoinedIn
            puncturedVerticalStrip
            (Complex.mk (3 / 2) w.im)
            (Complex.mk (3 / 2) (1 : ℝ)) :=
        puncturedVerticalStrip_rightColumn_verticalJoined
      exact
        (((hz_left.trans hz_to_left_detour).trans left_to_right_detour).trans
          hw_to_right_detour.symm).trans
          hw_right.symm
  · rcases puncturedVerticalStrip_joinedTo_safeCorridor hw with hw_left | hw_right
    · have hz_to_right_detour :
          JoinedIn
            puncturedVerticalStrip
            (Complex.mk (3 / 2) z.im)
            (Complex.mk (3 / 2) (1 : ℝ)) :=
        puncturedVerticalStrip_rightColumn_verticalJoined
      have left_to_right_detour :
          JoinedIn
            puncturedVerticalStrip
            (Complex.mk (1 / 2) (1 : ℝ))
            (Complex.mk (3 / 2) (1 : ℝ)) :=
        puncturedVerticalStrip_leftCorridor_joined_rightCorridor one_ne_zero
      have hw_to_left_detour :
          JoinedIn
            puncturedVerticalStrip
            (Complex.mk (1 / 2) w.im)
            (Complex.mk (1 / 2) (1 : ℝ)) :=
        puncturedVerticalStrip_leftColumn_verticalJoined
      exact
        (((hz_right.trans hz_to_right_detour).trans left_to_right_detour.symm).trans
          hw_to_left_detour.symm).trans
          hw_left.symm
    · have hz_to_detour :
          JoinedIn
            puncturedVerticalStrip
            (Complex.mk (3 / 2) z.im)
            (Complex.mk (3 / 2) (1 : ℝ)) :=
        puncturedVerticalStrip_rightColumn_verticalJoined
      have hw_to_detour :
          JoinedIn
            puncturedVerticalStrip
            (Complex.mk (3 / 2) w.im)
            (Complex.mk (3 / 2) (1 : ℝ)) :=
        puncturedVerticalStrip_rightColumn_verticalJoined
      exact
        (hz_right.trans hz_to_detour).trans
          (hw_to_detour.symm.trans hw_right.symm)

/-- The punctured vertical strip is nonempty. -/
theorem puncturedVerticalStrip_nonempty :
    puncturedVerticalStrip.Nonempty :=
  ⟨Complex.mk (1 / 2) 0, puncturedVerticalStrip_leftCorridor_mem⟩

/-- The punctured vertical strip is path-connected. -/
theorem puncturedVerticalStrip_isPathConnected :
    IsPathConnected puncturedVerticalStrip :=
  ⟨puncturedVerticalStrip_nonempty,
    fun _z hz _w hw => puncturedVerticalStrip_joinedIn_via_corridors hz hw⟩

/-- The punctured vertical strip is preconnected. -/
theorem puncturedVerticalStrip_isPreconnected :
    IsPreconnected puncturedVerticalStrip :=
  puncturedVerticalStrip_isPathConnected.isConnected.isPreconnected

end

end LFunctions
end Boundary
