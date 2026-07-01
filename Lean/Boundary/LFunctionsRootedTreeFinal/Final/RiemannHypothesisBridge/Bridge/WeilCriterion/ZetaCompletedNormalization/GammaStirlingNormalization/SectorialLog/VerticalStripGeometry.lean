import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ClassicalAnalysis.GammaBinetStirling.Basic
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalization.GammaStirlingNormalization.SectorialLog.VerticalStripShift
import Mathlib.Analysis.Complex.Basic

/-!
# Sectorial log: shifted vertical-strip geometry

This subowner contains the fixed vertical-line radius and right-shift geometry
used by Gamma recurrence transport.
-/

namespace Boundary
namespace LFunctions

noncomputable section

/-- Fixed vertical points lie in the closed right half-plane exactly when their
fixed real part is nonnegative. -/
theorem Complex.fixedRealPartVerticalPoint_closedRightHalfPlaneSector
    {a b : ℝ}
    (ha : 0 ≤ a) :
    Complex.closedRightHalfPlaneSector
      (Complex.fixedRealPartVerticalPoint a b) := by
  calc
    (0 : ℝ) ≤ a :=
      ha
    _ = (Complex.fixedRealPartVerticalPoint a b).re :=
      (Complex.fixedRealPartVerticalPoint_re a b).symm

/-- The imaginary coordinate gives a lower bound for the fixed vertical-point
norm. -/
theorem Complex.fixedRealPartVerticalPoint_abs_im_le_norm
    (a b : ℝ) :
    ‖b‖ ≤ ‖Complex.fixedRealPartVerticalPoint a b‖ := by
  have him :
    (Complex.fixedRealPartVerticalPoint a b).im = b :=
    Complex.fixedRealPartVerticalPoint_im a b
  have hbasic :
      |(Complex.fixedRealPartVerticalPoint a b).im| ≤
        ‖Complex.fixedRealPartVerticalPoint a b‖ :=
    RCLike.abs_im_le_norm (Complex.fixedRealPartVerticalPoint a b)
  have hnorm_eq_abs : ‖b‖ = |b| :=
    Real.norm_eq_abs b
  have hb_abs_le :
      |b| ≤ ‖Complex.fixedRealPartVerticalPoint a b‖ := by
    calc
      |b| = |(Complex.fixedRealPartVerticalPoint a b).im| :=
        congrArg abs him.symm
      _ ≤ ‖Complex.fixedRealPartVerticalPoint a b‖ :=
        hbasic
  calc
    ‖b‖ = |b| :=
      hnorm_eq_abs
    _ ≤ ‖Complex.fixedRealPartVerticalPoint a b‖ :=
      hb_abs_le

/-- A large imaginary height forces a large complex radius on a fixed vertical
line. -/
theorem Complex.fixedRealPartVerticalPoint_radius_ge_of_height_ge
    {a b H : ℝ}
    (hH : H ≤ ‖b‖) :
    H ≤ ‖Complex.fixedRealPartVerticalPoint a b‖ :=
  le_trans hH (Complex.fixedRealPartVerticalPoint_abs_im_le_norm a b)

/-- If `H` dominates a sectorial radius cutoff, then a height cutoff by `H`
dominates the corresponding complex radius cutoff. -/
theorem Complex.fixedRealPartVerticalPoint_sectorialRadius_ge_of_height_ge
    {a b H R : ℝ}
    (hR_le_H : R ≤ H)
    (hH : H ≤ ‖b‖) :
    R ≤ ‖Complex.fixedRealPartVerticalPoint a b‖ :=
  le_trans hR_le_H
    (Complex.fixedRealPartVerticalPoint_radius_ge_of_height_ge hH)

/-- Shifting a fixed vertical point by a natural number shifts only its real
coordinate. -/
theorem Complex.fixedRealPartVerticalPoint_natShift_re
    (x y : ℝ)
    (N : ℕ) :
    (Complex.fixedRealPartVerticalPoint (x + N) y).re =
      x + (N : ℝ) := by
  exact Complex.fixedRealPartVerticalPoint_re (x + N) y

/-- Shifting a fixed vertical point by a natural number preserves its imaginary
coordinate. -/
theorem Complex.fixedRealPartVerticalPoint_natShift_im
    (x y : ℝ)
    (N : ℕ) :
    (Complex.fixedRealPartVerticalPoint (x + N) y).im = y := by
  exact Complex.fixedRealPartVerticalPoint_im (x + N) y

/-- A natural right shift moves the whole real strip into the closed right
half-plane. -/
theorem Complex.fixedRealPartVerticalPoint_natShift_closedRightHalfPlaneSector
    {A x y : ℝ}
    {N : ℕ}
    (hA : -A ≤ (N : ℝ))
    (hx : A ≤ x) :
    Complex.closedRightHalfPlaneSector
      (Complex.fixedRealPartVerticalPoint (x + N) y) := by
  have hnonneg : 0 ≤ x + (N : ℝ) := by
    have hneg_x_le_N : -x ≤ (N : ℝ) :=
      le_trans (neg_le_neg hx) hA
    calc
      (0 : ℝ) = -x + x :=
        (neg_add_cancel x).symm
      _ ≤ (N : ℝ) + x :=
        add_le_add_right hneg_x_le_N x
      _ = x + (N : ℝ) :=
        add_comm (N : ℝ) x
  exact
    Complex.fixedRealPartVerticalPoint_closedRightHalfPlaneSector hnonneg

/-- The shifted vertical point has radius bounded below by the same height. -/
theorem Complex.fixedRealPartVerticalPoint_natShift_radius_ge_of_height_ge
    {x y H : ℝ}
    {N : ℕ}
    (hH : H ≤ ‖y‖) :
    H ≤ ‖Complex.fixedRealPartVerticalPoint (x + N) y‖ :=
  Complex.fixedRealPartVerticalPoint_radius_ge_of_height_ge hH

/-- Bounded real part in a strip remains bounded after a fixed natural shift. -/
theorem real_natShift_mem_strip_of_mem_strip
    {A B x : ℝ}
    (N : ℕ)
    (hxA : A ≤ x)
    (hxB : x ≤ B) :
    A + (N : ℝ) ≤ x + (N : ℝ) ∧
      x + (N : ℝ) ≤ B + (N : ℝ) :=
  ⟨add_le_add_right hxA (N : ℝ),
    add_le_add_right hxB (N : ℝ)⟩

/-- Shifted strip points have strictly positive real part. -/
theorem Complex.fixedRealPartVerticalPoint_verticalStripRightShift_re_pos
    {A x y : ℝ}
    (hx : A ≤ x) :
    0 <
      (Complex.fixedRealPartVerticalPoint
        (x + Complex.verticalStripRightShift A) y).re :=
  have hone_le : 1 ≤ x + (Complex.verticalStripRightShift A : ℝ) :=
    calc
      1 ≤ A + (Complex.verticalStripRightShift A : ℝ) :=
        Complex.one_le_lower_add_verticalStripRightShift A
      _ ≤ x + (Complex.verticalStripRightShift A : ℝ) :=
        add_le_add_right hx (Complex.verticalStripRightShift A : ℝ)
  have hzero_lt_one : (0 : ℝ) < 1 := zero_lt_one
  have hpos : 0 < x + (Complex.verticalStripRightShift A : ℝ) :=
    lt_of_lt_of_le hzero_lt_one hone_le
  calc
    0 < x + (Complex.verticalStripRightShift A : ℝ) := hpos
    _ =
        (Complex.fixedRealPartVerticalPoint
          (x + Complex.verticalStripRightShift A) y).re :=
      (Complex.fixedRealPartVerticalPoint_re
        (x + Complex.verticalStripRightShift A) y).symm

/-- The deterministic shift moves every point in the strip into the closed
right half-plane. -/
theorem Complex.fixedRealPartVerticalPoint_verticalStripRightShift_closedRightHalfPlaneSector
    {A x y : ℝ}
    (hx : A ≤ x) :
    Complex.closedRightHalfPlaneSector
      (Complex.fixedRealPartVerticalPoint
        (x + Complex.verticalStripRightShift A) y) :=
  Complex.fixedRealPartVerticalPoint_natShift_closedRightHalfPlaneSector
    (Complex.neg_lower_le_verticalStripRightShift A) hx

/-- The deterministic shift preserves the large-height-to-large-radius lower
bound. -/
theorem Complex.fixedRealPartVerticalPoint_verticalStripRightShift_radius_ge_of_height_ge
    {A x y H : ℝ}
    (hH : H ≤ ‖y‖) :
    H ≤
      ‖Complex.fixedRealPartVerticalPoint
        (x + Complex.verticalStripRightShift A) y‖ :=
  Complex.fixedRealPartVerticalPoint_natShift_radius_ge_of_height_ge hH

end

end LFunctions
end Boundary
