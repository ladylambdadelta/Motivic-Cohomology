import Mathlib.Analysis.Complex.PhragmenLindelof

/-!
# Punctured vertical strip geometry

This file owns the elementary path geometry of the punctured vertical strip
`0 < Re z < 2`, `z ≠ 1`.  Analytic files should consume these owner-level
corridor facts instead of reproving the strip routing inside zeta-specific
normalization files.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open scoped Filter Topology

/-- The punctured vertical strip used by the Euler-Maclaurin identity theorem:
`0 < Re z < 2`, with the point `1` removed. -/
def puncturedVerticalStrip : Set ℂ :=
  {z : ℂ | 0 < z.re ∧ z.re < 2 ∧ z ≠ 1}

/-- Horizontal segments at nonzero imaginary height stay inside the punctured
vertical strip once their endpoints lie in the strip. -/
theorem puncturedVerticalStrip_horizontalSegment_mem
    {z w p : ℂ}
    (hz : z ∈ puncturedVerticalStrip)
    (hw : w ∈ puncturedVerticalStrip)
    (hp_re : p.re ∈ Set.Icc z.re w.re ∨ p.re ∈ Set.Icc w.re z.re)
    (hp_im : p.im = z.im)
    (hzw_im : z.im = w.im)
    (hz_im : z.im ≠ 0) :
    p ∈ puncturedVerticalStrip := by
  sorry

/-- Vertical segments at real part different from `1` stay inside the
punctured vertical strip once their endpoints lie in the strip. -/
theorem puncturedVerticalStrip_verticalSegment_mem
    {z w p : ℂ}
    (hz : z ∈ puncturedVerticalStrip)
    (hw : w ∈ puncturedVerticalStrip)
    (hp_re : p.re = z.re)
    (hp_im : p.im ∈ Set.Icc z.im w.im ∨ p.im ∈ Set.Icc w.im z.im)
    (hzw_re : z.re = w.re)
    (hz_re : z.re ≠ 1) :
    p ∈ puncturedVerticalStrip := by
  sorry

/-- The left safe corridor has positive real coordinate. -/
theorem puncturedVerticalStrip_zero_lt_leftCorridor_re :
    (0 : ℝ) < 1 / 2 := by
  exact half_pos zero_lt_one

/-- The left safe corridor lies left of the deleted vertical line. -/
theorem puncturedVerticalStrip_leftCorridor_re_lt_one :
    (1 / 2 : ℝ) < 1 := by
  exact half_lt_self zero_lt_one

/-- The left safe corridor lies inside the right strip boundary. -/
theorem puncturedVerticalStrip_leftCorridor_re_lt_two :
    (1 / 2 : ℝ) < 2 := by
  exact
    lt_trans
      puncturedVerticalStrip_leftCorridor_re_lt_one
      one_lt_two

/-- The right safe corridor has positive real coordinate. -/
theorem puncturedVerticalStrip_zero_lt_rightCorridor_re :
    (0 : ℝ) < 3 / 2 := by
  sorry

/-- The right safe corridor lies right of the deleted vertical line. -/
theorem puncturedVerticalStrip_one_lt_rightCorridor_re :
    (1 : ℝ) < 3 / 2 := by
  sorry

/-- The right safe corridor lies inside the right strip boundary. -/
theorem puncturedVerticalStrip_rightCorridor_re_lt_two :
    (3 / 2 : ℝ) < 2 := by
  sorry

/-- The left safe vertical corridor lies in the punctured strip. -/
theorem puncturedVerticalStrip_leftCorridor_mem
    {y : ℝ} :
    Complex.mk (1 / 2) y ∈ puncturedVerticalStrip := by
  sorry

/-- The right safe vertical corridor lies in the punctured strip. -/
theorem puncturedVerticalStrip_rightCorridor_mem
    {y : ℝ} :
    Complex.mk (3 / 2) y ∈ puncturedVerticalStrip := by
  sorry

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
      (Complex.mk x₂ h) := by
  sorry

/-- The left half-column is a safe vertical corridor inside the punctured
strip. -/
theorem puncturedVerticalStrip_leftColumn_verticalJoined
    {y₁ y₂ : ℝ} :
    JoinedIn
      puncturedVerticalStrip
      (Complex.mk (1 / 2) y₁)
      (Complex.mk (1 / 2) y₂) := by
  sorry

/-- The right half-column is a safe vertical corridor inside the punctured
strip. -/
theorem puncturedVerticalStrip_rightColumn_verticalJoined
    {y₁ y₂ : ℝ} :
    JoinedIn
      puncturedVerticalStrip
      (Complex.mk (3 / 2) y₁)
      (Complex.mk (3 / 2) y₂) := by
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
      (Complex.mk (3 / 2) h) := by
  sorry

/-- Corridor polygonal-path construction in the punctured vertical strip. -/
theorem puncturedVerticalStrip_joinedIn_via_corridors
    {z w : ℂ}
    (hz : z ∈ puncturedVerticalStrip)
    (hw : w ∈ puncturedVerticalStrip) :
    JoinedIn puncturedVerticalStrip z w := by
  sorry

/-- The punctured vertical strip is nonempty. -/
theorem puncturedVerticalStrip_nonempty :
    puncturedVerticalStrip.Nonempty := by
  sorry

/-- The punctured vertical strip is path-connected. -/
theorem puncturedVerticalStrip_isPathConnected :
    IsPathConnected puncturedVerticalStrip := by
  sorry

/-- The punctured vertical strip is preconnected. -/
theorem puncturedVerticalStrip_isPreconnected :
    IsPreconnected puncturedVerticalStrip := by
  exact puncturedVerticalStrip_isPathConnected.isConnected.isPreconnected

end

end LFunctions
end Boundary
