import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ClassicalAnalysis.OscillatorySums.QuantitativeTransitionSymmetry

/-!
# Total curvature variation of the quantitative transition

This owner converts the half-interval signs of the second derivative into an
exact total-variation identity for the first derivative.  The sign theorem is
proved in the adjacent analytic owner; the calculus and constant arithmetic
live here.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open MeasureTheory

theorem Real.continuous_smoothTransitionDerivative :
    Continuous Real.smoothTransitionDerivative := by
  have hdifferentiable :
      Differentiable ℝ Real.smoothTransitionDerivative :=
    fun x => (Real.hasDerivAt_smoothTransitionDerivative x).differentiableAt
  exact hdifferentiable.continuous

theorem Real.continuous_smoothTransitionSecondDerivative :
    Continuous Real.smoothTransitionSecondDerivative := by
  have hfirstContDiff : ContDiff ℝ ∞ Real.smoothTransitionDerivative := by
    have hraw : ContDiff ℝ ∞ (deriv smoothTransition) :=
      (contDiff_infty_iff_deriv.mp Real.smoothTransition.contDiff).2
    have hfunction :
        deriv smoothTransition = Real.smoothTransitionDerivative := by
      funext x
      exact Real.deriv_smoothTransition_exact x
    exact Eq.subst
      (motive := fun function : ℝ → ℝ => ContDiff ℝ ∞ function)
      hfunction
      hraw
  have hderivativeContinuous :=
    (contDiff_infty_iff_deriv.mp
      hfirstContDiff).2.continuous
  have hfunction :
      deriv Real.smoothTransitionDerivative =
        Real.smoothTransitionSecondDerivative := by
    funext x
    exact Real.deriv_smoothTransitionDerivative x
  exact Eq.subst
    (motive := fun function : ℝ → ℝ => Continuous function)
    hfunction
    hderivativeContinuous

theorem Real.intervalIntegrable_smoothTransitionSecondDerivative
    (left right : ℝ) :
    IntervalIntegrable Real.smoothTransitionSecondDerivative
      volume left right := by
  exact Real.continuous_smoothTransitionSecondDerivative.intervalIntegrable
    left right

theorem Real.intervalIntegrable_abs_smoothTransitionSecondDerivative
    (left right : ℝ) :
    IntervalIntegrable
      (fun x : ℝ => |Real.smoothTransitionSecondDerivative x|)
      volume left right := by
  exact Real.continuous_smoothTransitionSecondDerivative.abs.intervalIntegrable
    left right

theorem Real.integral_smoothTransitionSecondDerivative_eq_derivative_sub
    (left right : ℝ) :
    (∫ x in left..right, Real.smoothTransitionSecondDerivative x) =
      Real.smoothTransitionDerivative right -
        Real.smoothTransitionDerivative left := by
  have hderiv :
      ∀ x ∈ [[left, right]],
        DifferentiableAt ℝ Real.smoothTransitionDerivative x :=
    fun x hx =>
      (Real.hasDerivAt_smoothTransitionDerivative x).differentiableAt
  have hintegrable :
      IntervalIntegrable (deriv Real.smoothTransitionDerivative)
        volume left right := by
    have hfirstContDiff : ContDiff ℝ ∞ Real.smoothTransitionDerivative := by
      have hraw : ContDiff ℝ ∞ (deriv smoothTransition) :=
        (contDiff_infty_iff_deriv.mp Real.smoothTransition.contDiff).2
      have hfunction :
          deriv smoothTransition = Real.smoothTransitionDerivative := by
        funext x
        exact Real.deriv_smoothTransition_exact x
      exact Eq.subst
        (motive := fun function : ℝ → ℝ => ContDiff ℝ ∞ function)
        hfunction
        hraw
    have hcontinuous :=
      (contDiff_infty_iff_deriv.mp
        hfirstContDiff).2.continuous
    exact hcontinuous.intervalIntegrable left right
  have hftc := intervalIntegral.integral_deriv_eq_sub hderiv hintegrable
  have hintegrand := intervalIntegral.integral_congr
    (fun x hx => Real.deriv_smoothTransitionDerivative x)
  exact hintegrand.symm.trans hftc

theorem Real.abs_smoothTransitionSecondDerivative_eq_self_of_nonneg
    {x : ℝ}
    (hx : 0 ≤ Real.smoothTransitionSecondDerivative x) :
    |Real.smoothTransitionSecondDerivative x| =
      Real.smoothTransitionSecondDerivative x := by
  exact abs_of_nonneg hx

theorem Real.abs_smoothTransitionSecondDerivative_eq_neg_of_nonpos
    {x : ℝ}
    (hx : Real.smoothTransitionSecondDerivative x ≤ 0) :
    |Real.smoothTransitionSecondDerivative x| =
      -Real.smoothTransitionSecondDerivative x := by
  exact abs_of_nonpos hx

theorem Real.integral_abs_smoothTransitionSecondDerivative_left_half
    (hleft :
      ∀ x ∈ Set.Icc (0 : ℝ) (1 / 2),
        0 ≤ Real.smoothTransitionSecondDerivative x) :
    (∫ x in (0 : ℝ)..(1 / 2),
      |Real.smoothTransitionSecondDerivative x|) =
      Real.smoothTransitionDerivative (1 / 2) -
        Real.smoothTransitionDerivative 0 := by
  have hintegrand := intervalIntegral.integral_congr
    (fun x hx =>
      Real.abs_smoothTransitionSecondDerivative_eq_self_of_nonneg
        (hleft x hx))
  exact hintegrand.trans
    (Real.integral_smoothTransitionSecondDerivative_eq_derivative_sub
      0 (1 / 2))

theorem Real.integral_abs_smoothTransitionSecondDerivative_right_half
    (hright :
      ∀ x ∈ Set.Icc (1 / 2 : ℝ) 1,
        Real.smoothTransitionSecondDerivative x ≤ 0) :
    (∫ x in (1 / 2 : ℝ)..1,
      |Real.smoothTransitionSecondDerivative x|) =
      Real.smoothTransitionDerivative (1 / 2) -
        Real.smoothTransitionDerivative 1 := by
  have hintegrand := intervalIntegral.integral_congr
    (fun x hx =>
      Real.abs_smoothTransitionSecondDerivative_eq_neg_of_nonpos
        (hright x hx))
  have hnegative := intervalIntegral.integral_neg
    Real.smoothTransitionSecondDerivative
  have hftc :=
    Real.integral_smoothTransitionSecondDerivative_eq_derivative_sub
      (1 / 2) 1
  have hnormalize :
      -(Real.smoothTransitionDerivative 1 -
          Real.smoothTransitionDerivative (1 / 2)) =
        Real.smoothTransitionDerivative (1 / 2) -
          Real.smoothTransitionDerivative 1 := by
    exact neg_sub _ _
  exact hintegrand.trans
    (hnegative.trans
      ((congrArg Neg.neg hftc).trans hnormalize))

theorem Real.smoothTransitionDerivative_zero :
    Real.smoothTransitionDerivative 0 = 0 := by
  exact Eq.trans
    (Real.smoothTransitionDerivative_eq_normalized 0)
    (by
      have hg0 : expNegInvGlue 0 = 0 :=
        expNegInvGlue.zero_of_nonpos (le_refl 0)
      have hd0 : Real.expNegInvGlueDerivative 0 = 0 :=
        Real.expNegInvGlueDerivative_zero
      have hone : (1 : ℝ) - 0 = 1 := sub_zero 1
      have hnumerator :
          Real.smoothTransitionDerivativeNumerator 0 = 0 := by
        unfold Real.smoothTransitionDerivativeNumerator
        exact Eq.trans
          (congrArg₂ (fun first second : ℝ => first + second)
            (congrArg
              (fun value : ℝ => value * expNegInvGlue (1 - 0)) hd0)
            (congrArg
              (fun value : ℝ => value *
                Real.expNegInvGlueDerivative (1 - 0)) hg0))
          (Eq.trans
            (congrArg₂ (fun first second : ℝ => first + second)
              (zero_mul _) (zero_mul _))
            (zero_add 0))
      exact Eq.trans
        (congrArg
          (fun numerator : ℝ => numerator /
            Real.smoothTransitionDerivativeDenominator 0 ^ 2)
          hnumerator)
        (zero_div _))

theorem Real.smoothTransitionDerivative_one :
    Real.smoothTransitionDerivative 1 = 0 := by
  have hreflection := Real.smoothTransitionDerivative_reflection 0
  have hone : (1 : ℝ) - 0 = 1 := sub_zero 1
  exact Eq.trans
    (Eq.subst
      (motive := fun value : ℝ =>
        Real.smoothTransitionDerivative value =
          Real.smoothTransitionDerivative 0)
      hone
      hreflection)
    Real.smoothTransitionDerivative_zero

theorem Real.integral_abs_smoothTransitionSecondDerivative_eq_twice_midpoint
    (hleft :
      ∀ x ∈ Set.Icc (0 : ℝ) (1 / 2),
        0 ≤ Real.smoothTransitionSecondDerivative x)
    (hright :
      ∀ x ∈ Set.Icc (1 / 2 : ℝ) 1,
        Real.smoothTransitionSecondDerivative x ≤ 0) :
    (∫ x in (0 : ℝ)..1,
      |Real.smoothTransitionSecondDerivative x|) =
      2 * Real.smoothTransitionDerivative (1 / 2) := by
  have hsplit := intervalIntegral.integral_add_adjacent_intervals
    (Real.intervalIntegrable_abs_smoothTransitionSecondDerivative 0 (1 / 2))
    (Real.intervalIntegrable_abs_smoothTransitionSecondDerivative (1 / 2) 1)
  have hleftIntegral :=
    Real.integral_abs_smoothTransitionSecondDerivative_left_half hleft
  have hrightIntegral :=
    Real.integral_abs_smoothTransitionSecondDerivative_right_half hright
  have hnormalize :
      (Real.smoothTransitionDerivative (1 / 2) -
          Real.smoothTransitionDerivative 0) +
        (Real.smoothTransitionDerivative (1 / 2) -
          Real.smoothTransitionDerivative 1) =
        2 * Real.smoothTransitionDerivative (1 / 2) := by
    exact Eq.trans
      (congrArg₂ (fun first second : ℝ => first + second)
        (congrArg
          (fun endpoint : ℝ =>
            Real.smoothTransitionDerivative (1 / 2) - endpoint)
          Real.smoothTransitionDerivative_zero)
        (congrArg
          (fun endpoint : ℝ =>
            Real.smoothTransitionDerivative (1 / 2) - endpoint)
          Real.smoothTransitionDerivative_one))
      (Eq.trans
        (congrArg₂ (fun first second : ℝ => first + second)
          (sub_zero _) (sub_zero _))
        (two_mul _).symm)
  exact hsplit.symm.trans
    ((congrArg₂ (fun first second : ℝ => first + second)
      hleftIntegral hrightIntegral).trans hnormalize)

theorem Real.integral_abs_smoothTransitionSecondDerivative_le_eight
    (hleft :
      ∀ x ∈ Set.Icc (0 : ℝ) (1 / 2),
        0 ≤ Real.smoothTransitionSecondDerivative x)
    (hright :
      ∀ x ∈ Set.Icc (1 / 2 : ℝ) 1,
        Real.smoothTransitionSecondDerivative x ≤ 0) :
    (∫ x in (0 : ℝ)..1,
      |Real.smoothTransitionSecondDerivative x|) ≤ 8 := by
  have hidentity :=
    Real.integral_abs_smoothTransitionSecondDerivative_eq_twice_midpoint
      hleft hright
  have hmidpoint := Real.smoothTransitionDerivative_le_four (1 / 2)
  have hdouble := mul_le_mul_of_nonneg_left hmidpoint (Nat.cast_nonneg 2)
  have hnormalize : (2 : ℝ) * 4 = 8 := rfl
  exact Eq.subst
    (motive := fun integralValue : ℝ => integralValue ≤ 8)
    hidentity.symm
    (le_trans hdouble (le_of_eq hnormalize))

end
end LFunctions
end Boundary
