import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalization.GammaStirlingNormalization.VerticalRecurrence.Angular.Argument
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalization.GammaStirlingNormalization.SectorialLog.VerticalStripShift

/-!
# Vertical recurrence: angular exponential defect

This subowner contains the shifted vertical angular-defect comparison.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open scoped Filter Topology
local notation "π" => Real.pi

/-- Additive quantitative argument-defect estimate for shifted right-half-plane
vertical strips.

This is the exact arctangent-defect form behind the exponential comparison:
`-arg(w) y` differs from `-(π/2)|y|` by a bounded amount on every shifted
bounded vertical strip. -/
theorem Complex.shiftedVertical_arg_linear_defect_bounded
    (A B : ℝ) :
    ∃ H : ℝ, ∃ D : ℝ,
      0 < H ∧
      0 ≤ D ∧
      ∀ x y : ℝ,
        A ≤ x →
        x ≤ B →
        H ≤ ‖y‖ →
          let w : ℂ :=
            Complex.fixedRealPartVerticalPoint
              (x + Complex.verticalStripTransportShift A) y;
          -(Complex.arg w * y) ≤ D + (-(Real.pi / 2) * ‖y‖) ∧
          (-(Real.pi / 2) * ‖y‖) - D ≤ -(Complex.arg w * y) := by
  let D : ℝ :=
    max |A + Complex.verticalStripTransportShift A|
      |B + Complex.verticalStripTransportShift A|
  have hD_nonneg : 0 ≤ D :=
    le_trans (abs_nonneg (A + Complex.verticalStripTransportShift A))
      (le_max_left
        |A + Complex.verticalStripTransportShift A|
        |B + Complex.verticalStripTransportShift A|)
  exact ⟨1, D, zero_lt_one, hD_nonneg, by
  intro x y hxA hxB _hy
  let u : ℝ := x + Complex.verticalStripTransportShift A
  let w : ℂ :=
    Complex.fixedRealPartVerticalPoint
      (x + Complex.verticalStripTransportShift A) y
  have hu_nonneg : 0 ≤ u := by
    have hshift : -A ≤ (Complex.verticalStripRightShift A : ℝ) :=
      Complex.neg_lower_le_verticalStripRightShift A
    calc
      0 = A + -A := by
        exact (add_neg_cancel A).symm
      _ ≤ x + (Complex.verticalStripRightShift A : ℝ) :=
        add_le_add hxA hshift
  have hu_abs_le_D : |u| ≤ D := by
    exact real_abs_le_max_abs_of_mem_Icc
      (add_le_add_right hxA (Complex.verticalStripTransportShift A))
      (add_le_add_right hxB (Complex.verticalStripTransportShift A))
  have hu_le_D : u ≤ D :=
    le_trans (le_abs_self u) hu_abs_le_D
  have hdef_abs :
      |(Real.pi / 2) * ‖y‖ - Complex.arg w * y| ≤ D := by
    have hray :
        |(Real.pi / 2) * ‖y‖ -
            Complex.arg (Complex.fixedRealPartVerticalPoint u y) * y| ≤ u :=
      Complex.rightHalfPlaneVertical_arg_linear_defect_abs_le_re hu_nonneg
    exact le_trans hray hu_le_D
  have hdef_upper :
      (Real.pi / 2) * ‖y‖ - Complex.arg w * y ≤ D :=
    le_trans (le_abs_self ((Real.pi / 2) * ‖y‖ - Complex.arg w * y))
      hdef_abs
  have hdef_lower :
      -D ≤ (Real.pi / 2) * ‖y‖ - Complex.arg w * y := by
    have hneg_abs :
        -|(Real.pi / 2) * ‖y‖ - Complex.arg w * y| ≤
          (Real.pi / 2) * ‖y‖ - Complex.arg w * y :=
      neg_abs_le ((Real.pi / 2) * ‖y‖ - Complex.arg w * y)
    have hneg_bound :
        -D ≤ -|(Real.pi / 2) * ‖y‖ - Complex.arg w * y| :=
      neg_le_neg hdef_abs
    exact le_trans hneg_bound hneg_abs
  constructor
  · have htarget :
        - (Complex.arg w * y) ≤
          D + (-(Real.pi / 2) * ‖y‖) := by
      calc
        -(Complex.arg w * y) =
            ((Real.pi / 2) * ‖y‖ - Complex.arg w * y) +
              -((Real.pi / 2) * ‖y‖) := by
          calc
            -(Complex.arg w * y) =
                (Real.pi / 2) * ‖y‖ +
                  (-((Real.pi / 2) * ‖y‖) + -(Complex.arg w * y)) :=
              (add_neg_cancel_left ((Real.pi / 2) * ‖y‖)
                (-(Complex.arg w * y))).symm
            _ = (Real.pi / 2) * ‖y‖ +
                  (-(Complex.arg w * y) + -((Real.pi / 2) * ‖y‖)) := by
              exact congrArg
                (fun t : ℝ => (Real.pi / 2) * ‖y‖ + t)
                (add_comm (-((Real.pi / 2) * ‖y‖))
                  (-(Complex.arg w * y)))
            _ = ((Real.pi / 2) * ‖y‖ + -(Complex.arg w * y)) +
                  -((Real.pi / 2) * ‖y‖) :=
              (add_assoc ((Real.pi / 2) * ‖y‖)
                (-(Complex.arg w * y))
                (-((Real.pi / 2) * ‖y‖))).symm
            _ = ((Real.pi / 2) * ‖y‖ - Complex.arg w * y) +
                  -((Real.pi / 2) * ‖y‖) := by
              exact congrArg
                (fun t : ℝ => t + -((Real.pi / 2) * ‖y‖))
                (sub_eq_add_neg ((Real.pi / 2) * ‖y‖)
                  (Complex.arg w * y)).symm
        _ = ((Real.pi / 2) * ‖y‖ - Complex.arg w * y) +
              (-(Real.pi / 2) * ‖y‖) := by
          exact congrArg
            (fun t : ℝ =>
              ((Real.pi / 2) * ‖y‖ - Complex.arg w * y) + t)
            (neg_mul (Real.pi / 2) ‖y‖).symm
        _ ≤ D + (-(Real.pi / 2) * ‖y‖) :=
          add_le_add_right hdef_upper (-(Real.pi / 2) * ‖y‖)
    exact htarget
  · have htarget :
        (-(Real.pi / 2) * ‖y‖) - D ≤
          -(Complex.arg w * y) := by
      calc
        (-(Real.pi / 2) * ‖y‖) - D =
            -D + (-(Real.pi / 2) * ‖y‖) := by
          calc
            (-(Real.pi / 2) * ‖y‖) - D =
                (-(Real.pi / 2) * ‖y‖) + -D :=
              sub_eq_add_neg (-(Real.pi / 2) * ‖y‖) D
            _ = -D + (-(Real.pi / 2) * ‖y‖) :=
              add_comm (-(Real.pi / 2) * ‖y‖) (-D)
        _ ≤ ((Real.pi / 2) * ‖y‖ - Complex.arg w * y) +
              (-(Real.pi / 2) * ‖y‖) :=
          add_le_add_right hdef_lower (-(Real.pi / 2) * ‖y‖)
        _ = -(Complex.arg w * y) := by
          calc
            ((Real.pi / 2) * ‖y‖ - Complex.arg w * y) +
                (-(Real.pi / 2) * ‖y‖) =
              ((Real.pi / 2) * ‖y‖ - Complex.arg w * y) +
                -((Real.pi / 2) * ‖y‖) := by
              exact congrArg
                (fun t : ℝ =>
                  ((Real.pi / 2) * ‖y‖ - Complex.arg w * y) + t)
                (neg_mul (Real.pi / 2) ‖y‖)
            _ = ((Real.pi / 2) * ‖y‖ + -(Complex.arg w * y)) +
                -((Real.pi / 2) * ‖y‖) := by
              exact congrArg
                (fun t : ℝ => t + -((Real.pi / 2) * ‖y‖))
                (sub_eq_add_neg ((Real.pi / 2) * ‖y‖)
                  (Complex.arg w * y))
            _ = (Real.pi / 2) * ‖y‖ +
                (-(Complex.arg w * y) + -((Real.pi / 2) * ‖y‖)) :=
              add_assoc ((Real.pi / 2) * ‖y‖)
                (-(Complex.arg w * y))
                (-((Real.pi / 2) * ‖y‖))
            _ = (Real.pi / 2) * ‖y‖ +
                (-((Real.pi / 2) * ‖y‖) + -(Complex.arg w * y)) := by
              exact congrArg
                (fun t : ℝ => (Real.pi / 2) * ‖y‖ + t)
                (add_comm (-(Complex.arg w * y))
                  (-((Real.pi / 2) * ‖y‖)))
            _ = -(Complex.arg w * y) :=
              add_neg_cancel_left ((Real.pi / 2) * ‖y‖)
                (-(Complex.arg w * y))
    exact htarget⟩

/-- Quantitative arctangent-defect comparison for shifted right-half-plane
vertical strips.

For `w = x + N + i y` with `x` in a fixed bounded strip and `N` the deterministic
right-half-plane shift, the classical estimate
`|arg w - sign(y) · π/2| = O(1 / |y|)` gives a bounded multiplicative loss in
`exp (-arg(w) y)`.  This is the precise geometric input needed by the normalized
Stirling denominator comparison. -/
theorem Complex.shiftedVertical_arg_exponential_defect_comparable_quantitative
    (A B : ℝ) :
    ∃ H : ℝ, ∃ C : ℝ, ∃ c : ℝ,
      0 < H ∧
      0 < C ∧
      0 < c ∧
      ∀ x y : ℝ,
        A ≤ x →
        x ≤ B →
        H ≤ ‖y‖ →
          let w : ℂ :=
            Complex.fixedRealPartVerticalPoint
              (x + Complex.verticalStripTransportShift A) y;
          Real.exp (-(Complex.arg w * y)) ≤
            C * Real.exp (-(Real.pi / 2) * ‖y‖) ∧
          c * Real.exp (-(Real.pi / 2) * ‖y‖) ≤
            Real.exp (-(Complex.arg w * y)) := by
  match Complex.shiftedVertical_arg_linear_defect_bounded A B with
  | ⟨H, D, hH_pos, hD_nonneg, hdefect⟩ =>
  have hC_pos : 0 < Real.exp D :=
    Real.exp_pos D
  have hc_pos : 0 < Real.exp (-D) :=
    Real.exp_pos (-D)
  exact ⟨H, Real.exp D, Real.exp (-D), hH_pos, hC_pos, hc_pos, by
  intro x y hxA hxB hy
  let w : ℂ :=
    Complex.fixedRealPartVerticalPoint
      (x + Complex.verticalStripTransportShift A) y
  let b : ℝ := -(Real.pi / 2) * ‖y‖
  have hdef := hdefect x y hxA hxB hy
  constructor
  · have hexp_le :
        Real.exp (-(Complex.arg w * y)) ≤ Real.exp (D + b) :=
      Real.exp_le_exp.mpr hdef.1
    have hsplit :
        Real.exp (D + b) =
          Real.exp D * Real.exp b :=
      Real.exp_add D b
    exact le_trans hexp_le
      (le_of_eq
        (Eq.trans hsplit
          (by
            rfl)))
  · have hlower_exp :
        Real.exp (b - D) ≤ Real.exp (-(Complex.arg w * y)) :=
      Real.exp_le_exp.mpr hdef.2
    have hsplit :
        Real.exp (b - D) =
          Real.exp (-D) * Real.exp b := by
      calc
        Real.exp (b - D) =
            Real.exp (b + -D) := by
          exact congrArg Real.exp (sub_eq_add_neg b D)
        _ = Real.exp b * Real.exp (-D) :=
          Real.exp_add b (-D)
        _ = Real.exp (-D) * Real.exp b :=
          mul_comm (Real.exp b) (Real.exp (-D))
    exact le_trans (le_of_eq hsplit.symm) hlower_exp⟩

/-- Quantitative vertical argument-defect estimate for shifted right-half-plane
strip points.

This is the real geometric core of the denominator comparison.  In a fixed
right-half-plane vertical strip, the principal argument approaches
`sign(y) * π/2`, and the defect contributes only a bounded exponential factor
to `exp (-arg(w) y)`. -/
theorem Complex.shiftedVertical_arg_exponential_defect_comparable
    (A B : ℝ) :
    ∃ H : ℝ, ∃ C : ℝ, ∃ c : ℝ,
      0 < H ∧
      0 < C ∧
      0 < c ∧
      ∀ x y : ℝ,
        A ≤ x →
        x ≤ B →
        H ≤ ‖y‖ →
          let w : ℂ :=
            Complex.fixedRealPartVerticalPoint
              (x + Complex.verticalStripTransportShift A) y;
          Real.exp (-(Complex.arg w * y)) ≤
            C * Real.exp (-(Real.pi / 2) * ‖y‖) ∧
          c * Real.exp (-(Real.pi / 2) * ‖y‖) ≤
            Real.exp (-(Complex.arg w * y)) := by
  exact
    Complex.shiftedVertical_arg_exponential_defect_comparable_quantitative
      A B

end
end LFunctions
end Boundary
