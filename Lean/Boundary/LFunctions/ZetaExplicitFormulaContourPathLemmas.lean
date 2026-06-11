import Boundary.LFunctions.ZetaExplicitFormulaContourPaths
import Boundary.LFunctions.ZetaExplicitFormulaAnalyticCore
import Boundary.LFunctions.ZetaCompletedLogDerivativeCore
import Boundary.LFunctions.ZetaCompletedLogDerivativeControl
import Boundary.LFunctions.ZetaAdmissibleTransformRegularity
import Boundary.LFunctions.ZetaExplicitFormulaPuncturedPlane
import Mathlib.Analysis.Complex.Basic

/-!
# Boundary explicit-formula contour path lemmas

This file owns the explicit path algebra and the basic nonvanishing/strip
lemmas for the contour parametrizations. The main contour file consumes these
as reusable owner-level facts.
-/

namespace Boundary
namespace LFunctions

noncomputable section

namespace ZetaAdmissibleFunction

/-- The right vertical side of the rectangle. -/
def explicitFormulaRightSide (r : ExplicitFormulaRectangle) : Set ℂ :=
  {s : ℂ | s.re = r.c ∧ s.im ≤ r.T ∧ -r.T ≤ s.im}

/-- The left vertical side of the rectangle. -/
def explicitFormulaLeftSide (r : ExplicitFormulaRectangle) : Set ℂ :=
  {s : ℂ | s.re = 1 - r.c ∧ s.im ≤ r.T ∧ -r.T ≤ s.im}

/-- The top horizontal side of the rectangle. -/
def explicitFormulaTopSide (r : ExplicitFormulaRectangle) : Set ℂ :=
  {s : ℂ | r.c ≤ s.re ∧ s.re ≤ 1 - r.c ∧ s.im = r.T}

/-- The bottom horizontal side of the rectangle. -/
def explicitFormulaBottomSide (r : ExplicitFormulaRectangle) : Set ℂ :=
  {s : ℂ | r.c ≤ s.re ∧ s.re ≤ 1 - r.c ∧ s.im = -r.T}

/-- The right path has constant real part `c`. -/
theorem zetaCompletedExplicitFormulaRightPath_re_formula (r : ExplicitFormulaRectangle) (t : ℝ) :
    (zetaCompletedExplicitFormulaRightPath r t).re = r.c := by
  calc
    (zetaCompletedExplicitFormulaRightPath r t).re
        = (r.c : ℂ).re + (t * Complex.I).re := Complex.add_re _ _
    _ = r.c := by
      norm_num [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
        Complex.I_re, Complex.I_im]

/-- The right path has constant real part `c`. -/
theorem zetaCompletedExplicitFormulaRightPath_re (r : ExplicitFormulaRectangle) (t : ℝ) :
    (zetaCompletedExplicitFormulaRightPath r t).re = r.c := by
  exact zetaCompletedExplicitFormulaRightPath_re_formula r t

/-- The right path has positive real part when the rectangle lies to the right of `1/2`. -/
theorem rightPath_re_pos_core (r : ExplicitFormulaRectangle) (t : ℝ)
    (hc : (1 / 2 : ℝ) < r.c) :
    0 < (zetaCompletedExplicitFormulaRightPath r t).re := by
  have hhalf : 0 < (1 / 2 : ℝ) := by norm_num
  have hcpos : 0 < r.c := lt_trans hhalf hc
  exact Eq.symm (zetaCompletedExplicitFormulaRightPath_re r t) ▸ hcpos

/-- The right path has imaginary part `t`. -/
theorem zetaCompletedExplicitFormulaRightPath_im_formula (r : ExplicitFormulaRectangle) (t : ℝ) :
    (zetaCompletedExplicitFormulaRightPath r t).im = t := by
  calc
    (zetaCompletedExplicitFormulaRightPath r t).im
        = (r.c : ℂ).im + (t * Complex.I).im := Complex.add_im _ _
    _ = t := by
      norm_num [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
        Complex.I_re, Complex.I_im]

/-- The right path has imaginary part `t`. -/
theorem zetaCompletedExplicitFormulaRightPath_im (r : ExplicitFormulaRectangle) (t : ℝ) :
    (zetaCompletedExplicitFormulaRightPath r t).im = t := by
  exact zetaCompletedExplicitFormulaRightPath_im_formula r t

/-- The left path has constant real part `1 - c`. -/
theorem zetaCompletedExplicitFormulaLeftPath_re_formula (r : ExplicitFormulaRectangle) (t : ℝ) :
    (zetaCompletedExplicitFormulaLeftPath r t).re = 1 - r.c := by
  calc
    (zetaCompletedExplicitFormulaLeftPath r t).re
        = ((1 - r.c : ℝ) : ℂ).re + (t * Complex.I).re := Complex.add_re _ _
    _ = 1 - r.c := by
      norm_num [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
        Complex.I_re, Complex.I_im]

/-- The left path has constant real part `1 - c`. -/
theorem zetaCompletedExplicitFormulaLeftPath_re (r : ExplicitFormulaRectangle) (t : ℝ) :
    (zetaCompletedExplicitFormulaLeftPath r t).re = 1 - r.c := by
  exact zetaCompletedExplicitFormulaLeftPath_re_formula r t

/-- The left path has positive real part when the rectangle lies to the right of `1/2`. -/
theorem leftPath_re_pos_core (r : ExplicitFormulaRectangle) (t : ℝ)
    (hc : r.c < 1) :
    0 < (zetaCompletedExplicitFormulaLeftPath r t).re := by
  have hpos : 0 < 1 - r.c := sub_pos.mpr hc
  exact Eq.symm (zetaCompletedExplicitFormulaLeftPath_re r t) ▸ hpos

/-- The left path is the reflection of the right path across `s ↦ 1 - s`. -/
theorem zetaCompletedExplicitFormulaLeftPath_eq_one_sub_rightPath
    (r : ExplicitFormulaRectangle) (t : ℝ) :
    zetaCompletedExplicitFormulaLeftPath r t =
      1 - zetaCompletedExplicitFormulaRightPath r (-t) := by
  apply Complex.ext
  · calc
      (zetaCompletedExplicitFormulaLeftPath r t).re = 1 - r.c := by
        exact zetaCompletedExplicitFormulaLeftPath_re r t
      _ = (1 - zetaCompletedExplicitFormulaRightPath r (-t)).re := by
        simp [zetaCompletedExplicitFormulaRightPath_re]
  · calc
      (zetaCompletedExplicitFormulaLeftPath r t).im = t := by
        unfold zetaCompletedExplicitFormulaLeftPath
        norm_num [Complex.add_im, Complex.ofReal_im, Complex.ofReal_re,
          Complex.mul_im, Complex.I_re, Complex.I_im]
      _ = (1 - zetaCompletedExplicitFormulaRightPath r (-t)).im := by
        simp [zetaCompletedExplicitFormulaRightPath_im]

/-- The right path at `t = 0` is the lower-right corner. -/
theorem zetaCompletedExplicitFormulaRightPath_zero_core (r : ExplicitFormulaRectangle) :
    zetaCompletedExplicitFormulaRightPath r 0 = r.c := by
  change r.c + (0 : ℂ) * Complex.I = r.c
  norm_num

theorem zetaCompletedExplicitFormulaRightPath_zero (r : ExplicitFormulaRectangle) :
    zetaCompletedExplicitFormulaRightPath r 0 = r.c := by
  exact zetaCompletedExplicitFormulaRightPath_zero_core r

theorem zetaCompletedExplicitFormulaRightPath_T_core (r : ExplicitFormulaRectangle) :
    zetaCompletedExplicitFormulaRightPath r r.T = r.c + r.T * Complex.I := by
  rfl

theorem zetaCompletedExplicitFormulaRightPath_T (r : ExplicitFormulaRectangle) :
    zetaCompletedExplicitFormulaRightPath r r.T = r.c + r.T * Complex.I := by
  exact zetaCompletedExplicitFormulaRightPath_T_core r

theorem zetaCompletedExplicitFormulaLeftPath_zero_core (r : ExplicitFormulaRectangle) :
    zetaCompletedExplicitFormulaLeftPath r 0 = 1 - r.c := by
  change (1 - r.c : ℂ) + (0 : ℂ) * Complex.I = 1 - r.c
  norm_num

theorem zetaCompletedExplicitFormulaLeftPath_zero (r : ExplicitFormulaRectangle) :
    zetaCompletedExplicitFormulaLeftPath r 0 = 1 - r.c := by
  exact zetaCompletedExplicitFormulaLeftPath_zero_core r

theorem zetaCompletedExplicitFormulaLeftPath_T_core (r : ExplicitFormulaRectangle) :
    zetaCompletedExplicitFormulaLeftPath r r.T = (1 - r.c) + r.T * Complex.I := by
  rfl

theorem zetaCompletedExplicitFormulaLeftPath_T (r : ExplicitFormulaRectangle) :
    zetaCompletedExplicitFormulaLeftPath r r.T = (1 - r.c) + r.T * Complex.I := by
  exact zetaCompletedExplicitFormulaLeftPath_T_core r

theorem zetaCompletedExplicitFormulaTopPath_c_core (r : ExplicitFormulaRectangle) :
    zetaCompletedExplicitFormulaTopPath r r.c = r.c + r.T * Complex.I := by
  rfl

theorem zetaCompletedExplicitFormulaTopPath_c (r : ExplicitFormulaRectangle) :
    zetaCompletedExplicitFormulaTopPath r r.c = r.c + r.T * Complex.I := by
  exact zetaCompletedExplicitFormulaTopPath_c_core r

theorem zetaCompletedExplicitFormulaTopPath_one_sub_core (r : ExplicitFormulaRectangle) :
    zetaCompletedExplicitFormulaTopPath r (1 - r.c) = (1 - r.c) + r.T * Complex.I := by
  unfold zetaCompletedExplicitFormulaTopPath
  norm_num

theorem zetaCompletedExplicitFormulaTopPath_one_sub (r : ExplicitFormulaRectangle) :
    zetaCompletedExplicitFormulaTopPath r (1 - r.c) = (1 - r.c) + r.T * Complex.I := by
  exact zetaCompletedExplicitFormulaTopPath_one_sub_core r

theorem zetaCompletedExplicitFormulaBottomPath_c_core (r : ExplicitFormulaRectangle) :
    zetaCompletedExplicitFormulaBottomPath r r.c = r.c - r.T * Complex.I := by
  rfl

theorem zetaCompletedExplicitFormulaBottomPath_c (r : ExplicitFormulaRectangle) :
    zetaCompletedExplicitFormulaBottomPath r r.c = r.c - r.T * Complex.I := by
  exact zetaCompletedExplicitFormulaBottomPath_c_core r

theorem zetaCompletedExplicitFormulaBottomPath_one_sub (r : ExplicitFormulaRectangle) :
    zetaCompletedExplicitFormulaBottomPath r (1 - r.c) = (1 - r.c) - r.T * Complex.I := by
  unfold zetaCompletedExplicitFormulaBottomPath
  norm_num

theorem zetaCompletedExplicitFormulaLeftPath_im_formula (r : ExplicitFormulaRectangle) (t : ℝ) :
    (zetaCompletedExplicitFormulaLeftPath r t).im = t := by
  unfold zetaCompletedExplicitFormulaLeftPath
  norm_num [Complex.add_im, Complex.ofReal_im, Complex.ofReal_re,
    Complex.mul_im, Complex.I_re, Complex.I_im]

theorem zetaCompletedExplicitFormulaLeftPath_im (r : ExplicitFormulaRectangle) (t : ℝ) :
    (zetaCompletedExplicitFormulaLeftPath r t).im = t := by
  exact zetaCompletedExplicitFormulaLeftPath_im_formula r t

theorem zetaCompletedExplicitFormulaTopPath_re_formula (r : ExplicitFormulaRectangle) (x : ℝ) :
    (zetaCompletedExplicitFormulaTopPath r x).re = x := by
  unfold zetaCompletedExplicitFormulaTopPath
  norm_num [Complex.add_re, Complex.ofReal_re, Complex.ofReal_im,
    Complex.mul_re, Complex.I_re, Complex.I_im]

theorem zetaCompletedExplicitFormulaTopPath_re_eq (r : ExplicitFormulaRectangle) (x : ℝ) :
    (zetaCompletedExplicitFormulaTopPath r x).re = x := by
  exact zetaCompletedExplicitFormulaTopPath_re_formula r x

theorem zetaCompletedExplicitFormulaTopPath_im_formula (r : ExplicitFormulaRectangle) (x : ℝ) :
    (zetaCompletedExplicitFormulaTopPath r x).im = r.T := by
  unfold zetaCompletedExplicitFormulaTopPath
  norm_num [Complex.add_im, Complex.ofReal_im, Complex.ofReal_re,
    Complex.mul_im, Complex.I_re, Complex.I_im]

theorem zetaCompletedExplicitFormulaTopPath_im (r : ExplicitFormulaRectangle) (x : ℝ) :
    (zetaCompletedExplicitFormulaTopPath r x).im = r.T := by
  exact zetaCompletedExplicitFormulaTopPath_im_formula r x

theorem zetaCompletedExplicitFormulaBottomPath_re_formula (r : ExplicitFormulaRectangle) (x : ℝ) :
    (zetaCompletedExplicitFormulaBottomPath r x).re = x := by
  unfold zetaCompletedExplicitFormulaBottomPath
  norm_num [Complex.sub_re, Complex.ofReal_re, Complex.ofReal_im,
    Complex.mul_re, Complex.I_re, Complex.I_im]

theorem zetaCompletedExplicitFormulaBottomPath_re_eq (r : ExplicitFormulaRectangle) (x : ℝ) :
    (zetaCompletedExplicitFormulaBottomPath r x).re = x := by
  exact zetaCompletedExplicitFormulaBottomPath_re_formula r x

theorem zetaCompletedExplicitFormulaBottomPath_im_formula (r : ExplicitFormulaRectangle) (x : ℝ) :
    (zetaCompletedExplicitFormulaBottomPath r x).im = -r.T := by
  unfold zetaCompletedExplicitFormulaBottomPath
  norm_num [Complex.sub_im, Complex.ofReal_im, Complex.ofReal_re,
    Complex.mul_im, Complex.I_re, Complex.I_im]

theorem zetaCompletedExplicitFormulaBottomPath_im (r : ExplicitFormulaRectangle) (x : ℝ) :
    (zetaCompletedExplicitFormulaBottomPath r x).im = -r.T := by
  exact zetaCompletedExplicitFormulaBottomPath_im_formula r x

/-- The bottom horizontal path is the reflection of the top path across `s ↦ 1 - s`. -/
theorem zetaCompletedExplicitFormulaBottomPath_eq_one_sub_topPath
    (r : ExplicitFormulaRectangle) (x : ℝ) :
    zetaCompletedExplicitFormulaBottomPath r x =
      1 - zetaCompletedExplicitFormulaTopPath r (1 - x) := by
  apply Complex.ext
  · calc
      (zetaCompletedExplicitFormulaBottomPath r x).re = x := by
        exact zetaCompletedExplicitFormulaBottomPath_re_eq r x
      _ = (1 - zetaCompletedExplicitFormulaTopPath r (1 - x)).re := by
        simp [zetaCompletedExplicitFormulaTopPath_re_eq]
  · calc
      (zetaCompletedExplicitFormulaBottomPath r x).im = -r.T := by
        exact zetaCompletedExplicitFormulaBottomPath_im r x
      _ = (1 - zetaCompletedExplicitFormulaTopPath r (1 - x)).im := by
        simp [zetaCompletedExplicitFormulaTopPath_im]

/-- `Γℝ` is nonzero on the right contour path when the rectangle lies to the right of `1/2`. -/
theorem Gammaℝ_rightPath_ne_zero (r : ExplicitFormulaRectangle) (t : ℝ)
    (hc : (1 / 2 : ℝ) < r.c) :
    Complex.Gammaℝ (zetaCompletedExplicitFormulaRightPath r t) ≠ 0 := by
  exact Gammaℝ_ne_zero_of_re_pos
    (zetaCompletedExplicitFormulaRightPath r t)
    (rightPath_re_pos_core r t hc)

/-- `Γℝ` is nonzero on the left contour path when the rectangle lies to the right of `1/2`. -/
theorem Gammaℝ_leftPath_ne_zero (r : ExplicitFormulaRectangle) (t : ℝ)
    (hc : r.c < 1) :
    Complex.Gammaℝ (zetaCompletedExplicitFormulaLeftPath r t) ≠ 0 := by
  exact Gammaℝ_ne_zero_of_re_pos
    (zetaCompletedExplicitFormulaLeftPath r t)
    (leftPath_re_pos_core r t hc)

theorem zetaCompletedExplicitFormulaRightPath_mem_re (r : ExplicitFormulaRectangle) (t : ℝ)
    (ht1 : t ≤ r.T) (ht2 : -r.T ≤ t) :
    (zetaCompletedExplicitFormulaRightPath r t).re = r.c := by
  exact zetaCompletedExplicitFormulaRightPath_re r t

theorem zetaCompletedExplicitFormulaRightPath_mem_upper (r : ExplicitFormulaRectangle) (t : ℝ)
    (ht1 : t ≤ r.T) (ht2 : -r.T ≤ t) :
    t ≤ r.T := by
  exact ht1

theorem zetaCompletedExplicitFormulaRightPath_mem_lower (r : ExplicitFormulaRectangle) (t : ℝ)
    (ht1 : t ≤ r.T) (ht2 : -r.T ≤ t) :
    -r.T ≤ t := by
  exact ht2

theorem zetaCompletedExplicitFormulaRightPath_mem_core (r : ExplicitFormulaRectangle) (t : ℝ)
    (ht1 : t ≤ r.T) (ht2 : -r.T ≤ t) :
    zetaCompletedExplicitFormulaRightPath r t ∈ explicitFormulaRightSide r := by
  unfold explicitFormulaRightSide
  constructor
  · exact zetaCompletedExplicitFormulaRightPath_mem_re r t ht1 ht2
  constructor
  · simpa [zetaCompletedExplicitFormulaRightPath_im] using ht1
  · simpa [zetaCompletedExplicitFormulaRightPath_im] using ht2

theorem zetaCompletedExplicitFormulaRightPath_mem (r : ExplicitFormulaRectangle) (t : ℝ)
    (ht1 : t ≤ r.T) (ht2 : -r.T ≤ t) :
    zetaCompletedExplicitFormulaRightPath r t ∈ explicitFormulaRightSide r := by
  exact zetaCompletedExplicitFormulaRightPath_mem_core r t ht1 ht2

theorem zetaCompletedExplicitFormulaLeftPath_mem_re (r : ExplicitFormulaRectangle) (t : ℝ)
    (ht1 : t ≤ r.T) (ht2 : -r.T ≤ t) :
    (zetaCompletedExplicitFormulaLeftPath r t).re = 1 - r.c := by
  exact zetaCompletedExplicitFormulaLeftPath_re r t

theorem zetaCompletedExplicitFormulaLeftPath_mem_upper (r : ExplicitFormulaRectangle) (t : ℝ)
    (ht1 : t ≤ r.T) (ht2 : -r.T ≤ t) :
    t ≤ r.T := by
  exact ht1

theorem zetaCompletedExplicitFormulaLeftPath_mem_lower (r : ExplicitFormulaRectangle) (t : ℝ)
    (ht1 : t ≤ r.T) (ht2 : -r.T ≤ t) :
    -r.T ≤ t := by
  exact ht2

theorem zetaCompletedExplicitFormulaLeftPath_mem_core (r : ExplicitFormulaRectangle) (t : ℝ)
    (ht1 : t ≤ r.T) (ht2 : -r.T ≤ t) :
    zetaCompletedExplicitFormulaLeftPath r t ∈ explicitFormulaLeftSide r := by
  unfold explicitFormulaLeftSide
  constructor
  · exact zetaCompletedExplicitFormulaLeftPath_mem_re r t ht1 ht2
  constructor
  · simpa [zetaCompletedExplicitFormulaLeftPath_im] using ht1
  · simpa [zetaCompletedExplicitFormulaLeftPath_im] using ht2

theorem zetaCompletedExplicitFormulaLeftPath_mem (r : ExplicitFormulaRectangle) (t : ℝ)
    (ht1 : t ≤ r.T) (ht2 : -r.T ≤ t) :
    zetaCompletedExplicitFormulaLeftPath r t ∈ explicitFormulaLeftSide r := by
  exact zetaCompletedExplicitFormulaLeftPath_mem_core r t ht1 ht2

theorem zetaCompletedExplicitFormulaTopPath_mem_lower (r : ExplicitFormulaRectangle) (x : ℝ)
    (hx1 : r.c ≤ x) (hx2 : x ≤ 1 - r.c) :
    r.c ≤ x := by
  exact hx1

theorem zetaCompletedExplicitFormulaTopPath_mem_upper (r : ExplicitFormulaRectangle) (x : ℝ)
    (hx1 : r.c ≤ x) (hx2 : x ≤ 1 - r.c) :
    x ≤ 1 - r.c := by
  exact hx2

theorem zetaCompletedExplicitFormulaTopPath_mem_im (r : ExplicitFormulaRectangle) (x : ℝ)
    (hx1 : r.c ≤ x) (hx2 : x ≤ 1 - r.c) :
    (zetaCompletedExplicitFormulaTopPath r x).im = r.T := by
  exact zetaCompletedExplicitFormulaTopPath_im r x

theorem zetaCompletedExplicitFormulaTopPath_mem_core (r : ExplicitFormulaRectangle) (x : ℝ)
    (hx1 : r.c ≤ x) (hx2 : x ≤ 1 - r.c) :
    zetaCompletedExplicitFormulaTopPath r x ∈ explicitFormulaTopSide r := by
  unfold explicitFormulaTopSide
  constructor
  · simpa [zetaCompletedExplicitFormulaTopPath_re_eq] using hx1
  constructor
  · simpa [zetaCompletedExplicitFormulaTopPath_re_eq] using hx2
  · exact zetaCompletedExplicitFormulaTopPath_mem_im r x hx1 hx2

theorem zetaCompletedExplicitFormulaTopPath_mem (r : ExplicitFormulaRectangle) (x : ℝ)
    (hx1 : r.c ≤ x) (hx2 : x ≤ 1 - r.c) :
    zetaCompletedExplicitFormulaTopPath r x ∈ explicitFormulaTopSide r := by
  exact zetaCompletedExplicitFormulaTopPath_mem_core r x hx1 hx2

theorem zetaCompletedExplicitFormulaTopPath_strip_lower (r : ExplicitFormulaRectangle) (x : ℝ)
    (hx1 : r.c ≤ x) (hx2 : x ≤ 1 - r.c) :
    r.c ≤ (zetaCompletedExplicitFormulaTopPath r x).re := by
  simpa [zetaCompletedExplicitFormulaTopPath_re_eq] using hx1

theorem zetaCompletedExplicitFormulaTopPath_strip_upper (r : ExplicitFormulaRectangle) (x : ℝ)
    (hx1 : r.c ≤ x) (hx2 : x ≤ 1 - r.c) :
    (zetaCompletedExplicitFormulaTopPath r x).re ≤ 1 - r.c := by
  simpa [zetaCompletedExplicitFormulaTopPath_re_eq] using hx2

theorem zetaCompletedExplicitFormulaTopPath_strip_core (r : ExplicitFormulaRectangle) (x : ℝ)
    (hx1 : r.c ≤ x) (hx2 : x ≤ 1 - r.c) :
    r.c ≤ (zetaCompletedExplicitFormulaTopPath r x).re ∧
      (zetaCompletedExplicitFormulaTopPath r x).re ≤ 1 - r.c := by
  constructor
  · exact zetaCompletedExplicitFormulaTopPath_strip_lower r x hx1 hx2
  · exact zetaCompletedExplicitFormulaTopPath_strip_upper r x hx1 hx2

theorem zetaCompletedExplicitFormulaTopPath_strip (r : ExplicitFormulaRectangle) (x : ℝ)
    (hx1 : r.c ≤ x) (hx2 : x ≤ 1 - r.c) :
    r.c ≤ (zetaCompletedExplicitFormulaTopPath r x).re ∧
      (zetaCompletedExplicitFormulaTopPath r x).re ≤ 1 - r.c := by
  exact zetaCompletedExplicitFormulaTopPath_strip_core r x hx1 hx2

theorem zetaCompletedExplicitFormulaBottomPath_mem_lower (r : ExplicitFormulaRectangle) (x : ℝ)
    (hx1 : r.c ≤ x) (hx2 : x ≤ 1 - r.c) :
    r.c ≤ x := by
  exact hx1

theorem zetaCompletedExplicitFormulaBottomPath_mem_upper (r : ExplicitFormulaRectangle) (x : ℝ)
    (hx1 : r.c ≤ x) (hx2 : x ≤ 1 - r.c) :
    x ≤ 1 - r.c := by
  exact hx2

theorem zetaCompletedExplicitFormulaBottomPath_mem_im (r : ExplicitFormulaRectangle) (x : ℝ)
    (hx1 : r.c ≤ x) (hx2 : x ≤ 1 - r.c) :
    (zetaCompletedExplicitFormulaBottomPath r x).im = -r.T := by
  exact zetaCompletedExplicitFormulaBottomPath_im r x

theorem zetaCompletedExplicitFormulaBottomPath_mem_core (r : ExplicitFormulaRectangle) (x : ℝ)
    (hx1 : r.c ≤ x) (hx2 : x ≤ 1 - r.c) :
    zetaCompletedExplicitFormulaBottomPath r x ∈ explicitFormulaBottomSide r := by
  unfold explicitFormulaBottomSide
  constructor
  · simpa [zetaCompletedExplicitFormulaBottomPath_re_eq] using hx1
  constructor
  · simpa [zetaCompletedExplicitFormulaBottomPath_re_eq] using hx2
  · exact zetaCompletedExplicitFormulaBottomPath_mem_im r x hx1 hx2

theorem zetaCompletedExplicitFormulaBottomPath_mem (r : ExplicitFormulaRectangle) (x : ℝ)
    (hx1 : r.c ≤ x) (hx2 : x ≤ 1 - r.c) :
    zetaCompletedExplicitFormulaBottomPath r x ∈ explicitFormulaBottomSide r := by
  exact zetaCompletedExplicitFormulaBottomPath_mem_core r x hx1 hx2

theorem zetaCompletedExplicitFormulaBottomPath_strip_lower (r : ExplicitFormulaRectangle) (x : ℝ)
    (hx1 : r.c ≤ x) (hx2 : x ≤ 1 - r.c) :
    r.c ≤ (zetaCompletedExplicitFormulaBottomPath r x).re := by
  simpa [zetaCompletedExplicitFormulaBottomPath_re_eq] using hx1

theorem zetaCompletedExplicitFormulaBottomPath_strip_upper (r : ExplicitFormulaRectangle) (x : ℝ)
    (hx1 : r.c ≤ x) (hx2 : x ≤ 1 - r.c) :
    (zetaCompletedExplicitFormulaBottomPath r x).re ≤ 1 - r.c := by
  simpa [zetaCompletedExplicitFormulaBottomPath_re_eq] using hx2

theorem zetaCompletedExplicitFormulaBottomPath_strip_core (r : ExplicitFormulaRectangle) (x : ℝ)
    (hx1 : r.c ≤ x) (hx2 : x ≤ 1 - r.c) :
    r.c ≤ (zetaCompletedExplicitFormulaBottomPath r x).re ∧
      (zetaCompletedExplicitFormulaBottomPath r x).re ≤ 1 - r.c := by
  constructor
  · exact zetaCompletedExplicitFormulaBottomPath_strip_lower r x hx1 hx2
  · exact zetaCompletedExplicitFormulaBottomPath_strip_upper r x hx1 hx2

theorem zetaCompletedExplicitFormulaBottomPath_strip (r : ExplicitFormulaRectangle) (x : ℝ)
    (hx1 : r.c ≤ x) (hx2 : x ≤ 1 - r.c) :
    r.c ≤ (zetaCompletedExplicitFormulaBottomPath r x).re ∧
      (zetaCompletedExplicitFormulaBottomPath r x).re ≤ 1 - r.c := by
  exact zetaCompletedExplicitFormulaBottomPath_strip_core r x hx1 hx2

end ZetaAdmissibleFunction

end
end LFunctions
end Boundary
