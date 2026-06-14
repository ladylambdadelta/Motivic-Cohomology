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

open scoped Filter Topology

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
    simpa [hp] using (Complex.ofReal_im (1 : ℝ))
  exact hp_im hp_im_zero

/-- A point whose real part is not `1` is not the deleted point `1`. -/
theorem puncturedVerticalStrip_ne_one_of_re_ne_one
    {p : ℂ}
    (hp_re : p.re ≠ 1) :
    p ≠ 1 := by
  intro hp
  have hp_re_one : p.re = 1 := by
    simpa [hp] using (Complex.ofReal_re (1 : ℝ))
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
  exact ⟨by simpa [hp_re] using hz0, by simpa [hp_re] using hz2⟩

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
    exact hz_im (by simpa [hp_im] using hp_zero)
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
    exact hz_re (by simpa [hp_re] using hp_one)
  exact ⟨hp_bounds.1, hp_bounds.2, puncturedVerticalStrip_ne_one_of_re_ne_one hp_re_ne⟩

/-- The left safe corridor has positive real coordinate. -/
theorem puncturedVerticalStrip_zero_lt_leftCorridor_re :
    (0 : ℝ) < 1 / 2 := by
  norm_num

/-- The left safe corridor lies left of the deleted vertical line. -/
theorem puncturedVerticalStrip_leftCorridor_re_lt_one :
    (1 / 2 : ℝ) < 1 := by
  norm_num

/-- The left safe corridor lies inside the right strip boundary. -/
theorem puncturedVerticalStrip_leftCorridor_re_lt_two :
    (1 / 2 : ℝ) < 2 := by
  norm_num

/-- The right safe corridor has positive real coordinate. -/
theorem puncturedVerticalStrip_zero_lt_rightCorridor_re :
    (0 : ℝ) < 3 / 2 := by
  norm_num

/-- The right safe corridor lies right of the deleted vertical line. -/
theorem puncturedVerticalStrip_one_lt_rightCorridor_re :
    (1 : ℝ) < 3 / 2 := by
  norm_num

/-- The right safe corridor lies inside the right strip boundary. -/
theorem puncturedVerticalStrip_rightCorridor_re_lt_two :
    (3 / 2 : ℝ) < 2 := by
  norm_num

/-- The left safe vertical corridor is not the deleted point. -/
theorem puncturedVerticalStrip_leftCorridor_ne_one
    {y : ℝ} :
    Complex.mk (1 / 2) y ≠ (1 : ℂ) := by
  exact
    puncturedVerticalStrip_ne_one_of_re_ne_one
      (by norm_num)

/-- The right safe vertical corridor is not the deleted point. -/
theorem puncturedVerticalStrip_rightCorridor_ne_one
    {y : ℝ} :
    Complex.mk (3 / 2) y ≠ (1 : ℂ) := by
  exact
    puncturedVerticalStrip_ne_one_of_re_ne_one
      (by norm_num)

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
  sorry

/-- Explicit vertical segment containment in a safe corridor. -/
theorem puncturedVerticalStrip_vertical_segment_subset
    {x y₁ y₂ : ℝ}
    (hx_left : 0 < x)
    (hx_right : x < 2)
    (hx_ne : x ≠ 1) :
    [Complex.mk x y₁ -[ℝ] Complex.mk x y₂] ⊆ puncturedVerticalStrip := by
  intro p hp
  sorry

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
      (by norm_num))

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
      (by norm_num))

/-- Points in the left component `0 < Re z < 1` of the punctured strip are
joined inside the punctured strip. -/
theorem puncturedVerticalStrip_leftHalf_joined
    {z w : ℂ}
    (hz : z ∈ puncturedVerticalStrip)
    (hw : w ∈ puncturedVerticalStrip)
    (hz_left : z.re < 1)
    (hw_left : w.re < 1) :
    JoinedIn puncturedVerticalStrip z w := by
  sorry

/-- Points in the right component `1 < Re z < 2` of the punctured strip are
joined inside the punctured strip. -/
theorem puncturedVerticalStrip_rightHalf_joined
    {z w : ℂ}
    (hz : z ∈ puncturedVerticalStrip)
    (hw : w ∈ puncturedVerticalStrip)
    (hz_right : 1 < z.re)
    (hw_right : 1 < w.re) :
    JoinedIn puncturedVerticalStrip z w := by
  sorry

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
  sorry

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
  sorry

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
