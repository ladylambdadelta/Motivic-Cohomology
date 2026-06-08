import Boundary.LFunctions.ZetaExplicitFormulaAnalyticCore

/-!
# Boundary explicit-formula contour surface

This file names the contour objects used in the completed Guinand--Weil
argument. The actual residue and decay estimates will be proved against these
definitions.
-/

namespace Boundary
namespace LFunctions

noncomputable section

namespace ZetaAdmissibleFunction

/-- The completed explicit-formula contour integrand, named for the proof. -/
abbrev zetaCompletedExplicitFormulaContourIntegrand
    (f : ZetaAdmissibleFunction) : ℂ → ℂ :=
  zetaCompletedExplicitFormulaPhi f

/-- The right vertical side parametrization of the rectangle. -/
def zetaCompletedExplicitFormulaRightPath
    (r : ExplicitFormulaRectangle) : ℝ → ℂ :=
  fun t => r.c + t * Complex.I

/-- The left vertical side parametrization of the rectangle. -/
def zetaCompletedExplicitFormulaLeftPath
    (r : ExplicitFormulaRectangle) : ℝ → ℂ :=
  fun t => (1 - r.c) + t * Complex.I

/-- The top horizontal side parametrization of the rectangle. -/
def zetaCompletedExplicitFormulaTopPath
    (r : ExplicitFormulaRectangle) : ℝ → ℂ :=
  fun x => x + r.T * Complex.I

/-- The bottom horizontal side parametrization of the rectangle. -/
def zetaCompletedExplicitFormulaBottomPath
    (r : ExplicitFormulaRectangle) : ℝ → ℂ :=
  fun x => x - r.T * Complex.I

/-- The contour integrand along the right vertical side. -/
def zetaCompletedExplicitFormulaRightBoundary
    (f : ZetaAdmissibleFunction) (r : ExplicitFormulaRectangle) (t : ℝ) : ℂ :=
  zetaCompletedExplicitFormulaContourIntegrand f (zetaCompletedExplicitFormulaRightPath r t)

/-- The contour integrand along the left vertical side. -/
def zetaCompletedExplicitFormulaLeftBoundary
    (f : ZetaAdmissibleFunction) (r : ExplicitFormulaRectangle) (t : ℝ) : ℂ :=
  zetaCompletedExplicitFormulaContourIntegrand f (zetaCompletedExplicitFormulaLeftPath r t)

/-- The contour integrand along the top horizontal side. -/
def zetaCompletedExplicitFormulaHorizontalBoundaryTop
    (f : ZetaAdmissibleFunction) (r : ExplicitFormulaRectangle) (x : ℝ) : ℂ :=
  zetaCompletedExplicitFormulaContourIntegrand f (zetaCompletedExplicitFormulaTopPath r x)

/-- The contour integrand along the bottom horizontal side. -/
def zetaCompletedExplicitFormulaHorizontalBoundaryBottom
    (f : ZetaAdmissibleFunction) (r : ExplicitFormulaRectangle) (x : ℝ) : ℂ :=
  zetaCompletedExplicitFormulaContourIntegrand f (zetaCompletedExplicitFormulaBottomPath r x)

/-- The right path has constant real part `c`. -/
theorem zetaCompletedExplicitFormulaRightPath_re (r : ExplicitFormulaRectangle) (t : ℝ) :
    (zetaCompletedExplicitFormulaRightPath r t).re = r.c := by
  unfold zetaCompletedExplicitFormulaRightPath
  rw [Complex.coe_real_add]
  rw [Complex.ofReal_mul_I]
  rw [Complex.re_add_im]
  ring

/-- The left path has constant real part `1 - c`. -/
theorem zetaCompletedExplicitFormulaLeftPath_re (r : ExplicitFormulaRectangle) (t : ℝ) :
    (zetaCompletedExplicitFormulaLeftPath r t).re = 1 - r.c := by
  unfold zetaCompletedExplicitFormulaLeftPath
  rw [Complex.coe_real_add]
  rw [Complex.ofReal_mul_I]
  rw [Complex.re_add_im]
  ring

/-- The left path is the reflection of the right path across `s ↦ 1 - s`. -/
theorem zetaCompletedExplicitFormulaLeftPath_eq_one_sub_rightPath
    (r : ExplicitFormulaRectangle) (t : ℝ) :
    zetaCompletedExplicitFormulaLeftPath r t =
      1 - zetaCompletedExplicitFormulaRightPath r (-t) := by
  unfold zetaCompletedExplicitFormulaLeftPath zetaCompletedExplicitFormulaRightPath
  rw [Complex.coe_real_add, Complex.coe_real_sub, Complex.ofReal_add, Complex.ofReal_sub]
  rw [Complex.ofReal_mul_I]
  ring

/-- The right path reflected in the parameter matches the left path. -/
theorem zetaCompletedExplicitFormulaRightPath_neg_eq_one_sub_leftPath
    (r : ExplicitFormulaRectangle) (t : ℝ) :
    zetaCompletedExplicitFormulaRightPath r (-t) =
      1 - zetaCompletedExplicitFormulaLeftPath r t := by
  rw [zetaCompletedExplicitFormulaLeftPath_eq_one_sub_rightPath]
  ring_nf

/-- The top path has constant imaginary part `T`. -/
theorem zetaCompletedExplicitFormulaTopPath_im (r : ExplicitFormulaRectangle) (x : ℝ) :
    (zetaCompletedExplicitFormulaTopPath r x).im = r.T := by
  unfold zetaCompletedExplicitFormulaTopPath
  rw [Complex.coe_real_add]
  rw [Complex.ofReal_mul_I]
  rw [Complex.im_add_re]
  ring

/-- The top path has real part `x`. -/
theorem zetaCompletedExplicitFormulaTopPath_re (r : ExplicitFormulaRectangle) (x : ℝ) :
    (zetaCompletedExplicitFormulaTopPath r x).re = x := by
  unfold zetaCompletedExplicitFormulaTopPath
  rw [Complex.coe_real_add]
  rw [Complex.ofReal_mul_I]
  rw [Complex.re_add_im]
  ring

/-- The bottom path is the reflection of the top path across `s ↦ 1 - s`. -/
theorem zetaCompletedExplicitFormulaBottomPath_eq_one_sub_topPath
    (r : ExplicitFormulaRectangle) (x : ℝ) :
    zetaCompletedExplicitFormulaBottomPath r x =
      1 - zetaCompletedExplicitFormulaTopPath r x := by
  unfold zetaCompletedExplicitFormulaBottomPath zetaCompletedExplicitFormulaTopPath
  rw [Complex.coe_real_sub, Complex.coe_real_add, Complex.ofReal_sub, Complex.ofReal_add]
  rw [Complex.ofReal_mul_I]
  ring

/-- The bottom path has constant imaginary part `-T`. -/
theorem zetaCompletedExplicitFormulaBottomPath_im (r : ExplicitFormulaRectangle) (x : ℝ) :
    (zetaCompletedExplicitFormulaBottomPath r x).im = -r.T := by
  unfold zetaCompletedExplicitFormulaBottomPath
  rw [Complex.coe_real_sub]
  rw [Complex.ofReal_mul_I]
  rw [Complex.im_sub_re]
  ring

/-- The bottom path has real part `x`. -/
theorem zetaCompletedExplicitFormulaBottomPath_re (r : ExplicitFormulaRectangle) (x : ℝ) :
    (zetaCompletedExplicitFormulaBottomPath r x).re = x := by
  unfold zetaCompletedExplicitFormulaBottomPath
  rw [Complex.coe_real_sub]
  rw [Complex.ofReal_mul_I]
  rw [Complex.re_sub_im]
  ring

/-- The right path starts at the lower-right corner. -/
theorem zetaCompletedExplicitFormulaRightPath_zero (r : ExplicitFormulaRectangle) :
    zetaCompletedExplicitFormulaRightPath r 0 = r.c := by
  unfold zetaCompletedExplicitFormulaRightPath
  rw [zero_mul, add_zero]

/-- The right path at `t = T` is the upper-right corner. -/
theorem zetaCompletedExplicitFormulaRightPath_T (r : ExplicitFormulaRectangle) :
    zetaCompletedExplicitFormulaRightPath r r.T = r.c + r.T * Complex.I := by
  rfl

/-- The left path starts at the lower-left corner. -/
theorem zetaCompletedExplicitFormulaLeftPath_zero (r : ExplicitFormulaRectangle) :
    zetaCompletedExplicitFormulaLeftPath r 0 = 1 - r.c := by
  unfold zetaCompletedExplicitFormulaLeftPath
  rw [zero_mul, add_zero]

/-- The left path at `t = T` is the upper-left corner. -/
theorem zetaCompletedExplicitFormulaLeftPath_T (r : ExplicitFormulaRectangle) :
    zetaCompletedExplicitFormulaLeftPath r r.T = (1 - r.c) + r.T * Complex.I := by
  rfl

/-- The top path at `x = c` is the upper-right corner. -/
theorem zetaCompletedExplicitFormulaTopPath_c (r : ExplicitFormulaRectangle) :
    zetaCompletedExplicitFormulaTopPath r r.c = r.c + r.T * Complex.I := by
  rfl

/-- The top path at `x = 1 - c` is the upper-left corner. -/
theorem zetaCompletedExplicitFormulaTopPath_one_sub (r : ExplicitFormulaRectangle) :
    zetaCompletedExplicitFormulaTopPath r (1 - r.c) = (1 - r.c) + r.T * Complex.I := by
  rfl

/-- The bottom path at `x = c` is the lower-right corner. -/
theorem zetaCompletedExplicitFormulaBottomPath_c (r : ExplicitFormulaRectangle) :
    zetaCompletedExplicitFormulaBottomPath r r.c = r.c - r.T * Complex.I := by
  rfl

/-- The bottom path at `x = 1 - c` is the lower-left corner. -/
theorem zetaCompletedExplicitFormulaBottomPath_one_sub (r : ExplicitFormulaRectangle) :
    zetaCompletedExplicitFormulaBottomPath r (1 - r.c) = (1 - r.c) - r.T * Complex.I := by
  rfl

/-- The right path lands in the right vertical side. -/
theorem zetaCompletedExplicitFormulaRightPath_mem (r : ExplicitFormulaRectangle) (t : ℝ)
    (ht1 : t ≤ r.T) (ht2 : -r.T ≤ t) :
    zetaCompletedExplicitFormulaRightPath r t ∈ explicitFormulaRightSide r := by
  unfold explicitFormulaRightSide
  constructor
  · exact zetaCompletedExplicitFormulaRightPath_re r t
  constructor
  · exact ht1
  · exact ht2

/-- The left path lands in the left vertical side. -/
theorem zetaCompletedExplicitFormulaLeftPath_mem (r : ExplicitFormulaRectangle) (t : ℝ)
    (ht1 : t ≤ r.T) (ht2 : -r.T ≤ t) :
    zetaCompletedExplicitFormulaLeftPath r t ∈ explicitFormulaLeftSide r := by
  unfold explicitFormulaLeftSide
  constructor
  · exact zetaCompletedExplicitFormulaLeftPath_re r t
  constructor
  · exact ht1
  · exact ht2

/-- The top path lands in the top horizontal side. -/
theorem zetaCompletedExplicitFormulaTopPath_mem (r : ExplicitFormulaRectangle) (x : ℝ)
    (hx1 : r.c ≤ x) (hx2 : x ≤ 1 - r.c) :
    zetaCompletedExplicitFormulaTopPath r x ∈ explicitFormulaTopSide r := by
  unfold explicitFormulaTopSide
  constructor
  · exact hx1
  constructor
  · exact hx2
  · exact zetaCompletedExplicitFormulaTopPath_im r x

/-- The top path remains in the horizontal strip. -/
theorem zetaCompletedExplicitFormulaTopPath_strip (r : ExplicitFormulaRectangle) (x : ℝ)
    (hx1 : r.c ≤ x) (hx2 : x ≤ 1 - r.c) :
    r.c ≤ (zetaCompletedExplicitFormulaTopPath r x).re ∧
      (zetaCompletedExplicitFormulaTopPath r x).re ≤ 1 - r.c := by
  constructor
  · rw [zetaCompletedExplicitFormulaTopPath_re]
    exact hx1
  · rw [zetaCompletedExplicitFormulaTopPath_re]
    exact hx2

/-- The bottom path lands in the bottom horizontal side. -/
theorem zetaCompletedExplicitFormulaBottomPath_mem (r : ExplicitFormulaRectangle) (x : ℝ)
    (hx1 : r.c ≤ x) (hx2 : x ≤ 1 - r.c) :
    zetaCompletedExplicitFormulaBottomPath r x ∈ explicitFormulaBottomSide r := by
  unfold explicitFormulaBottomSide
  constructor
  · exact hx1
  constructor
  · exact hx2
  · exact zetaCompletedExplicitFormulaBottomPath_im r x

/-- The bottom path remains in the horizontal strip. -/
theorem zetaCompletedExplicitFormulaBottomPath_strip (r : ExplicitFormulaRectangle) (x : ℝ)
    (hx1 : r.c ≤ x) (hx2 : x ≤ 1 - r.c) :
    r.c ≤ (zetaCompletedExplicitFormulaBottomPath r x).re ∧
      (zetaCompletedExplicitFormulaBottomPath r x).re ≤ 1 - r.c := by
  constructor
  · rw [zetaCompletedExplicitFormulaBottomPath_re]
    exact hx1
  · rw [zetaCompletedExplicitFormulaBottomPath_re]
    exact hx2

end ZetaAdmissibleFunction

end
end LFunctions
end Boundary
