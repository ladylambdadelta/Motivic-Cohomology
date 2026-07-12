import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ClassicalAnalysis.OscillatorySums.QuantitativeCutoffDerivativeSupport

/-!
# Support of quantitative collar second derivatives

Endpoint flatness extends the strict support statements for the transition
second derivative to closed complements.  The affine collar second derivatives
are therefore supported on their exact width-one-third intervals.
-/

namespace Boundary
namespace LFunctions

noncomputable section

theorem Real.smoothTransitionSecondDerivative_zero :
    Real.smoothTransitionSecondDerivative 0 = 0 := by
  unfold Real.smoothTransitionSecondDerivative
  unfold Real.smoothTransitionDerivativeNumeratorDerivative
  unfold Real.smoothTransitionDerivativeDenominator
  unfold Real.smoothTransitionDerivativeNumerator
  unfold Real.smoothTransitionDerivativeDenominatorDerivative
  have hgZero : expNegInvGlue 0 = 0 := expNegInvGlue.zero
  have hdgZero : Real.expNegInvGlueDerivative 0 = 0 :=
    Real.expNegInvGlueDerivative_zero
  have hddgZero : Real.expNegInvGlueGlobalSecondDerivative 0 = 0 :=
    Real.expNegInvGlueGlobalSecondDerivative_zero
  have honeSub : (1 : ℝ) - 0 = 1 := sub_zero 1
  have hdenominatorPos :
      0 < (expNegInvGlue 0 + expNegInvGlue (1 - 0)) ^ 2 :=
    pow_pos (Real.smoothTransitionDenominator_pos 0) 2
  have hnumeratorDerivative :
      Real.expNegInvGlueGlobalSecondDerivative 0 * expNegInvGlue (1 - 0) -
          expNegInvGlue 0 *
            Real.expNegInvGlueGlobalSecondDerivative (1 - 0) = 0 := by
    calc
      Real.expNegInvGlueGlobalSecondDerivative 0 * expNegInvGlue (1 - 0) -
          expNegInvGlue 0 *
            Real.expNegInvGlueGlobalSecondDerivative (1 - 0) =
        0 * expNegInvGlue 1 -
          0 * Real.expNegInvGlueGlobalSecondDerivative 1 := by
        exact congrArg₃
          (fun ddgZero gZero oneSub : ℝ =>
            ddgZero * expNegInvGlue oneSub -
              gZero * Real.expNegInvGlueGlobalSecondDerivative oneSub)
          hddgZero hgZero honeSub
      _ = 0 - 0 := congrArg₂ (fun first second : ℝ => first - second)
        (zero_mul _) (zero_mul _)
      _ = 0 := sub_self 0
  have hnumerator :
      Real.expNegInvGlueDerivative 0 * expNegInvGlue (1 - 0) +
          expNegInvGlue 0 * Real.expNegInvGlueDerivative (1 - 0) = 0 := by
    calc
      Real.expNegInvGlueDerivative 0 * expNegInvGlue (1 - 0) +
          expNegInvGlue 0 * Real.expNegInvGlueDerivative (1 - 0) =
        0 * expNegInvGlue 1 +
          0 * Real.expNegInvGlueDerivative 1 := by
        exact congrArg₃
          (fun dgZero gZero oneSub : ℝ =>
            dgZero * expNegInvGlue oneSub +
              gZero * Real.expNegInvGlueDerivative oneSub)
          hdgZero hgZero honeSub
      _ = 0 + 0 := congrArg₂ (fun first second : ℝ => first + second)
        (zero_mul _) (zero_mul _)
      _ = 0 := zero_add 0
  have htop :
      (Real.expNegInvGlueGlobalSecondDerivative 0 * expNegInvGlue (1 - 0) -
          expNegInvGlue 0 *
            Real.expNegInvGlueGlobalSecondDerivative (1 - 0)) *
          (expNegInvGlue 0 + expNegInvGlue (1 - 0)) ^ 2 -
        (Real.expNegInvGlueDerivative 0 * expNegInvGlue (1 - 0) +
          expNegInvGlue 0 * Real.expNegInvGlueDerivative (1 - 0)) *
          (2 * (expNegInvGlue 0 + expNegInvGlue (1 - 0)) *
            (Real.expNegInvGlueDerivative 0 -
              Real.expNegInvGlueDerivative (1 - 0))) = 0 := by
    exact
      (congrArg₂ (fun first second : ℝ =>
        first * (expNegInvGlue 0 + expNegInvGlue (1 - 0)) ^ 2 -
          second *
            (2 * (expNegInvGlue 0 + expNegInvGlue (1 - 0)) *
              (Real.expNegInvGlueDerivative 0 -
                Real.expNegInvGlueDerivative (1 - 0))))
        hnumeratorDerivative hnumerator).trans
        ((congrArg₂ (fun first second : ℝ => first - second)
          (zero_mul _) (zero_mul _)).trans (sub_self 0))
  exact
    (congrArg
      (fun value : ℝ =>
        value /
          ((expNegInvGlue 0 + expNegInvGlue (1 - 0)) ^ 2) ^ 2)
      htop).trans
      (zero_div _)

theorem Real.smoothTransitionSecondDerivative_one :
    Real.smoothTransitionSecondDerivative 1 = 0 := by
  unfold Real.smoothTransitionSecondDerivative
  unfold Real.smoothTransitionDerivativeNumeratorDerivative
  unfold Real.smoothTransitionDerivativeDenominator
  unfold Real.smoothTransitionDerivativeNumerator
  unfold Real.smoothTransitionDerivativeDenominatorDerivative
  have hgZero : expNegInvGlue 0 = 0 := expNegInvGlue.zero
  have hdgZero : Real.expNegInvGlueDerivative 0 = 0 :=
    Real.expNegInvGlueDerivative_zero
  have hddgZero : Real.expNegInvGlueGlobalSecondDerivative 0 = 0 :=
    Real.expNegInvGlueGlobalSecondDerivative_zero
  have honeSub : (1 : ℝ) - 1 = 0 := sub_self 1
  have hnumeratorDerivative :
      Real.expNegInvGlueGlobalSecondDerivative 1 * expNegInvGlue (1 - 1) -
          expNegInvGlue 1 *
            Real.expNegInvGlueGlobalSecondDerivative (1 - 1) = 0 := by
    calc
      Real.expNegInvGlueGlobalSecondDerivative 1 * expNegInvGlue (1 - 1) -
          expNegInvGlue 1 *
            Real.expNegInvGlueGlobalSecondDerivative (1 - 1) =
        Real.expNegInvGlueGlobalSecondDerivative 1 * 0 -
          expNegInvGlue 1 * 0 := by
        exact congrArg₃
          (fun oneSub gZero ddgZero : ℝ =>
            Real.expNegInvGlueGlobalSecondDerivative 1 * expNegInvGlue oneSub -
              expNegInvGlue 1 *
                Real.expNegInvGlueGlobalSecondDerivative oneSub)
          honeSub hgZero hddgZero
      _ = 0 - 0 := congrArg₂ (fun first second : ℝ => first - second)
        (mul_zero _) (mul_zero _)
      _ = 0 := sub_self 0
  have hnumerator :
      Real.expNegInvGlueDerivative 1 * expNegInvGlue (1 - 1) +
          expNegInvGlue 1 * Real.expNegInvGlueDerivative (1 - 1) = 0 := by
    calc
      Real.expNegInvGlueDerivative 1 * expNegInvGlue (1 - 1) +
          expNegInvGlue 1 * Real.expNegInvGlueDerivative (1 - 1) =
        Real.expNegInvGlueDerivative 1 * 0 + expNegInvGlue 1 * 0 := by
        exact congrArg₃
          (fun oneSub gZero dgZero : ℝ =>
            Real.expNegInvGlueDerivative 1 * expNegInvGlue oneSub +
              expNegInvGlue 1 * Real.expNegInvGlueDerivative oneSub)
          honeSub hgZero hdgZero
      _ = 0 + 0 := congrArg₂ (fun first second : ℝ => first + second)
        (mul_zero _) (mul_zero _)
      _ = 0 := zero_add 0
  have htop :
      (Real.expNegInvGlueGlobalSecondDerivative 1 * expNegInvGlue (1 - 1) -
          expNegInvGlue 1 *
            Real.expNegInvGlueGlobalSecondDerivative (1 - 1)) *
          (expNegInvGlue 1 + expNegInvGlue (1 - 1)) ^ 2 -
        (Real.expNegInvGlueDerivative 1 * expNegInvGlue (1 - 1) +
          expNegInvGlue 1 * Real.expNegInvGlueDerivative (1 - 1)) *
          (2 * (expNegInvGlue 1 + expNegInvGlue (1 - 1)) *
            (Real.expNegInvGlueDerivative 1 -
              Real.expNegInvGlueDerivative (1 - 1))) = 0 := by
    exact
      (congrArg₂ (fun first second : ℝ =>
        first * (expNegInvGlue 1 + expNegInvGlue (1 - 1)) ^ 2 -
          second *
            (2 * (expNegInvGlue 1 + expNegInvGlue (1 - 1)) *
              (Real.expNegInvGlueDerivative 1 -
                Real.expNegInvGlueDerivative (1 - 1))))
        hnumeratorDerivative hnumerator).trans
        ((congrArg₂ (fun first second : ℝ => first - second)
          (zero_mul _) (zero_mul _)).trans (sub_self 0))
  exact
    (congrArg
      (fun value : ℝ =>
        value / ((expNegInvGlue 1 + expNegInvGlue (1 - 1)) ^ 2) ^ 2)
      htop).trans
      (zero_div _)

theorem Real.smoothTransitionSecondDerivative_eq_zero_of_nonpos
    {x : ℝ}
    (hx : x ≤ 0) :
    Real.smoothTransitionSecondDerivative x = 0 := by
  match hx.eq_or_lt with
  | Or.inl hxZero =>
      exact Eq.subst
        (motive := fun value : ℝ =>
          Real.smoothTransitionSecondDerivative value = 0)
        hxZero.symm Real.smoothTransitionSecondDerivative_zero
  | Or.inr hxNeg =>
      exact Real.smoothTransitionSecondDerivative_eq_zero_of_neg hxNeg

theorem Real.smoothTransitionSecondDerivative_eq_zero_of_one_le
    {x : ℝ}
    (hx : 1 ≤ x) :
    Real.smoothTransitionSecondDerivative x = 0 := by
  match hx.eq_or_lt with
  | Or.inl hxOne =>
      exact Eq.subst
        (motive := fun value : ℝ =>
          Real.smoothTransitionSecondDerivative value = 0)
        hxOne Real.smoothTransitionSecondDerivative_one
  | Or.inr hxGt =>
      exact Real.smoothTransitionSecondDerivative_eq_zero_of_one_lt hxGt

theorem Real.quantitativeLogarithmicLeftCutoffSecondDerivative_eq_zero_of_le_supportLeft
    (a : ℤ) {x : ℝ}
    (hx : x ≤ (a : ℝ) - 1 / 3) :
    Real.quantitativeLogarithmicLeftCutoffSecondDerivative a x = 0 := by
  unfold Real.quantitativeLogarithmicLeftCutoffSecondDerivative
  have hargument : 3 * (x - (a : ℝ)) + 1 ≤ 0 := by
    have hsub := sub_le_sub_right hx (a : ℝ)
    have hendpoint : ((a : ℝ) - 1 / 3) - (a : ℝ) = -(1 / 3) :=
      sub_sub_cancel_left (a : ℝ) (1 / 3)
    have hscaled := mul_le_mul_of_nonneg_left
      (Eq.subst (motive := fun value : ℝ => x - (a : ℝ) ≤ value)
        hendpoint hsub) (Nat.cast_nonneg 3)
    exact le_trans (add_le_add_right hscaled 1)
      (le_of_eq Real.three_mul_neg_one_div_three_add_one_eq_zero)
  exact
    (congrArg (fun value : ℝ => 9 * value)
      (Real.smoothTransitionSecondDerivative_eq_zero_of_nonpos hargument)).trans
      (mul_zero 9)

theorem Real.quantitativeLogarithmicLeftCutoffSecondDerivative_eq_zero_of_core_le
    (a : ℤ) {x : ℝ}
    (hx : (a : ℝ) ≤ x) :
    Real.quantitativeLogarithmicLeftCutoffSecondDerivative a x = 0 := by
  unfold Real.quantitativeLogarithmicLeftCutoffSecondDerivative
  have hsub : 0 ≤ x - (a : ℝ) := sub_nonneg.mpr hx
  have hargument : (1 : ℝ) ≤ 3 * (x - (a : ℝ)) + 1 :=
    le_trans (le_of_eq (zero_add 1).symm)
      (add_le_add_right (mul_nonneg (Nat.cast_nonneg 3) hsub) 1)
  exact
    (congrArg (fun value : ℝ => 9 * value)
      (Real.smoothTransitionSecondDerivative_eq_zero_of_one_le hargument)).trans
      (mul_zero 9)

theorem Real.quantitativeLogarithmicRightCutoffSecondDerivative_eq_zero_of_le_core
    (b : ℤ) {x : ℝ}
    (hx : x ≤ (b : ℝ)) :
    Real.quantitativeLogarithmicRightCutoffSecondDerivative b x = 0 := by
  unfold Real.quantitativeLogarithmicRightCutoffSecondDerivative
  have hsub : 0 ≤ (b : ℝ) - x := sub_nonneg.mpr hx
  have hargument : (1 : ℝ) ≤ 3 * ((b : ℝ) - x) + 1 :=
    le_trans (le_of_eq (zero_add 1).symm)
      (add_le_add_right (mul_nonneg (Nat.cast_nonneg 3) hsub) 1)
  exact
    (congrArg (fun value : ℝ => 9 * value)
      (Real.smoothTransitionSecondDerivative_eq_zero_of_one_le hargument)).trans
      (mul_zero 9)

theorem Real.quantitativeLogarithmicRightCutoffSecondDerivative_eq_zero_of_supportRight_le
    (b : ℤ) {x : ℝ}
    (hx : (b : ℝ) + 1 / 3 ≤ x) :
    Real.quantitativeLogarithmicRightCutoffSecondDerivative b x = 0 := by
  unfold Real.quantitativeLogarithmicRightCutoffSecondDerivative
  have hsub := sub_le_sub_left hx (b : ℝ)
  have hendpoint : (b : ℝ) - ((b : ℝ) + 1 / 3) = -(1 / 3) := by
    exact (sub_add_eq_sub_sub (b : ℝ) (b : ℝ) (1 / 3)).trans
      ((congrArg (fun value : ℝ => value - 1 / 3) (sub_self (b : ℝ))).trans
        (zero_sub (1 / 3)))
  have hscaled := mul_le_mul_of_nonneg_left
    (Eq.subst (motive := fun value : ℝ => (b : ℝ) - x ≤ value)
      hendpoint hsub) (Nat.cast_nonneg 3)
  have hargument : 3 * ((b : ℝ) - x) + 1 ≤ 0 :=
    le_trans (add_le_add_right hscaled 1)
      (le_of_eq Real.three_mul_neg_one_div_three_add_one_eq_zero)
  exact
    (congrArg (fun value : ℝ => 9 * value)
      (Real.smoothTransitionSecondDerivative_eq_zero_of_nonpos hargument)).trans
      (mul_zero 9)

end
end LFunctions
end Boundary
