import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ClassicalAnalysis.OscillatorySums.QuantitativeLogarithmicCutoff

/-!
# Differential owner for the explicit smooth transition

This file exposes the exact derivative carried by mathlib's `expNegInvGlue`
construction.  It is the upstream calculus layer for quantitative variation
bounds of the fixed logarithmic cutoff.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open scoped Topology

def Real.expNegInvGlueDerivative
    (x : ℝ) : ℝ :=
  ((Polynomial.X ^ 2 *
      ((1 : ℝ[X]) - Polynomial.derivative (1 : ℝ[X]))).eval x⁻¹) *
    expNegInvGlue x

theorem Real.expNegInvGlue_one_weight_eval
    (x : ℝ) :
    ((1 : ℝ[X]).eval x⁻¹) * expNegInvGlue x = expNegInvGlue x := by
  calc
    ((1 : ℝ[X]).eval x⁻¹) * expNegInvGlue x =
        1 * expNegInvGlue x :=
      congrArg (fun value : ℝ => value * expNegInvGlue x)
        (Polynomial.eval_one)
    _ = expNegInvGlue x := one_mul (expNegInvGlue x)

theorem Real.expNegInvGlue_one_weight_function_eq :
    (fun x : ℝ => ((1 : ℝ[X]).eval x⁻¹) * expNegInvGlue x) =
      expNegInvGlue := by
  funext x
  exact Real.expNegInvGlue_one_weight_eval x

theorem Real.hasDerivAt_expNegInvGlue_exact
    (x : ℝ) :
    HasDerivAt expNegInvGlue (Real.expNegInvGlueDerivative x) x := by
  have hraw :=
    expNegInvGlue.hasDerivAt_polynomial_eval_inv_mul (1 : ℝ[X]) x
  have hfunction := Real.expNegInvGlue_one_weight_function_eq
  exact
    Eq.subst
      (motive := fun function : ℝ → ℝ =>
        HasDerivAt function (Real.expNegInvGlueDerivative x) x)
      hfunction
      hraw

theorem Real.differentiableAt_expNegInvGlue
    (x : ℝ) :
    DifferentiableAt ℝ expNegInvGlue x :=
  (Real.hasDerivAt_expNegInvGlue_exact x).differentiableAt

theorem Real.deriv_expNegInvGlue_exact
    (x : ℝ) :
    deriv expNegInvGlue x = Real.expNegInvGlueDerivative x :=
  (Real.hasDerivAt_expNegInvGlue_exact x).deriv

theorem Real.expNegInvGlueDerivative_polynomial_eq :
    Polynomial.X ^ 2 *
        ((1 : ℝ[X]) - Polynomial.derivative (1 : ℝ[X])) =
      Polynomial.X ^ 2 := by
  calc
    Polynomial.X ^ 2 *
          ((1 : ℝ[X]) - Polynomial.derivative (1 : ℝ[X])) =
        Polynomial.X ^ 2 * ((1 : ℝ[X]) - 0) :=
      congrArg
        (fun polynomial : ℝ[X] => Polynomial.X ^ 2 * ((1 : ℝ[X]) - polynomial))
        Polynomial.derivative_one
    _ = Polynomial.X ^ 2 * 1 :=
      congrArg (fun polynomial : ℝ[X] => Polynomial.X ^ 2 * polynomial)
        (sub_zero (1 : ℝ[X]))
    _ = Polynomial.X ^ 2 := mul_one (Polynomial.X ^ 2)

theorem Real.expNegInvGlueDerivative_eval_eq_inv_sq
    (x : ℝ) :
    ((Polynomial.X ^ 2 *
        ((1 : ℝ[X]) - Polynomial.derivative (1 : ℝ[X]))).eval x⁻¹) =
      x⁻¹ ^ 2 := by
  calc
    ((Polynomial.X ^ 2 *
        ((1 : ℝ[X]) - Polynomial.derivative (1 : ℝ[X]))).eval x⁻¹) =
        (Polynomial.X ^ 2).eval x⁻¹ :=
      congrArg (fun polynomial : ℝ[X] => polynomial.eval x⁻¹)
        Real.expNegInvGlueDerivative_polynomial_eq
    _ = (Polynomial.X.eval x⁻¹) ^ 2 := Polynomial.eval_pow
    _ = x⁻¹ ^ 2 := congrArg (fun value : ℝ => value ^ 2) Polynomial.eval_X

theorem Real.expNegInvGlueDerivative_eq_inv_sq_mul
    (x : ℝ) :
    Real.expNegInvGlueDerivative x = x⁻¹ ^ 2 * expNegInvGlue x := by
  unfold Real.expNegInvGlueDerivative
  exact
    congrArg (fun coefficient : ℝ => coefficient * expNegInvGlue x)
      (Real.expNegInvGlueDerivative_eval_eq_inv_sq x)

def Real.quantitativeTransitionAffine
    (slope intercept : ℝ)
    (x : ℝ) : ℝ :=
  slope * x + intercept

theorem Real.hasDerivAt_quantitativeTransitionAffine
    (slope intercept x : ℝ) :
    HasDerivAt (Real.quantitativeTransitionAffine slope intercept) slope x := by
  unfold Real.quantitativeTransitionAffine
  have hlinear := (hasDerivAt_id x).const_mul slope
  have hsum := hlinear.add (hasDerivAt_const x intercept)
  exact
    Eq.subst
      (motive := fun derivative : ℝ =>
        HasDerivAt (fun y : ℝ => slope * y + intercept) derivative x)
      (add_zero slope).symm
      hsum

theorem Real.hasDerivAt_expNegInvGlue_comp_affine
    (slope intercept x : ℝ) :
    HasDerivAt
      (fun y : ℝ => expNegInvGlue (Real.quantitativeTransitionAffine slope intercept y))
      (Real.expNegInvGlueDerivative
          (Real.quantitativeTransitionAffine slope intercept x) * slope)
      x := by
  have houter :=
    Real.hasDerivAt_expNegInvGlue_exact
      (Real.quantitativeTransitionAffine slope intercept x)
  have hinner := Real.hasDerivAt_quantitativeTransitionAffine slope intercept x
  exact houter.comp x hinner

def Real.smoothTransitionDerivative
    (x : ℝ) : ℝ :=
  (Real.expNegInvGlueDerivative x *
      (expNegInvGlue x + expNegInvGlue (1 - x)) -
    expNegInvGlue x *
      (Real.expNegInvGlueDerivative x -
        Real.expNegInvGlueDerivative (1 - x))) /
    (expNegInvGlue x + expNegInvGlue (1 - x)) ^ 2

theorem Real.hasDerivAt_expNegInvGlue_one_sub
    (x : ℝ) :
    HasDerivAt
      (fun y : ℝ => expNegInvGlue (1 - y))
      (-Real.expNegInvGlueDerivative (1 - x)) x := by
  have houter := Real.hasDerivAt_expNegInvGlue_exact (1 - x)
  have hinner := (hasDerivAt_const x 1).sub (hasDerivAt_id x)
  have hcomposition := houter.comp x hinner
  exact
    Eq.subst
      (motive := fun derivative : ℝ =>
        HasDerivAt
          (fun y : ℝ => expNegInvGlue (1 - y))
          derivative x)
      (mul_neg_one (Real.expNegInvGlueDerivative (1 - x)))
      hcomposition

theorem Real.hasDerivAt_smoothTransition_exact
    (x : ℝ) :
    HasDerivAt smoothTransition (Real.smoothTransitionDerivative x) x := by
  have hleft := Real.hasDerivAt_expNegInvGlue_exact x
  have hright := Real.hasDerivAt_expNegInvGlue_one_sub x
  have hdenominator := hleft.add hright
  have hquotient :=
    hleft.div hdenominator
      (Real.smoothTransition.pos_denom x).ne'
  exact hquotient

theorem Real.deriv_smoothTransition_exact
    (x : ℝ) :
    deriv smoothTransition x = Real.smoothTransitionDerivative x :=
  (Real.hasDerivAt_smoothTransition_exact x).deriv

theorem Real.expNegInvGlueDerivative_zero :
    Real.expNegInvGlueDerivative 0 = 0 := by
  have hinverse : (0 : ℝ)⁻¹ = 0 := inv_zero
  have hglue : expNegInvGlue 0 = 0 := expNegInvGlue.zero
  exact
    (Real.expNegInvGlueDerivative_eq_inv_sq_mul 0).trans <| by
      calc
        (0 : ℝ)⁻¹ ^ 2 * expNegInvGlue 0 = 0 ^ 2 * expNegInvGlue 0 :=
          congrArg (fun value : ℝ => value ^ 2 * expNegInvGlue 0) hinverse
        _ = 0 ^ 2 * 0 :=
          congrArg (fun value : ℝ => 0 ^ 2 * value) hglue
        _ = 0 := mul_zero (0 ^ 2)

theorem Real.smoothTransitionDerivative_zero :
    Real.smoothTransitionDerivative 0 = 0 := by
  unfold Real.smoothTransitionDerivative
  have hglueZero : expNegInvGlue 0 = 0 := expNegInvGlue.zero
  have hderivativeZero : Real.expNegInvGlueDerivative 0 = 0 :=
    Real.expNegInvGlueDerivative_zero
  have honeSub : (1 : ℝ) - 0 = 1 := sub_zero 1
  calc
    (Real.expNegInvGlueDerivative 0 *
          (expNegInvGlue 0 + expNegInvGlue (1 - 0)) -
        expNegInvGlue 0 *
          (Real.expNegInvGlueDerivative 0 -
            Real.expNegInvGlueDerivative (1 - 0))) /
        (expNegInvGlue 0 + expNegInvGlue (1 - 0)) ^ 2 =
      (0 * (0 + expNegInvGlue 1) -
        0 * (0 - Real.expNegInvGlueDerivative 1)) /
          (0 + expNegInvGlue 1) ^ 2 := by
      exact congrArg₃
        (fun derivativeZero glueZero oneSub : ℝ =>
          (derivativeZero *
                (glueZero + expNegInvGlue oneSub) -
              glueZero *
                (derivativeZero - Real.expNegInvGlueDerivative oneSub)) /
            (glueZero + expNegInvGlue oneSub) ^ 2)
        hderivativeZero hglueZero honeSub
    _ = (0 - 0) / (0 + expNegInvGlue 1) ^ 2 := by
      have hfirst : 0 * (0 + expNegInvGlue 1) = 0 := zero_mul _
      have hsecond : 0 * (0 - Real.expNegInvGlueDerivative 1) = 0 := zero_mul _
      exact congrArg
        (fun first second : ℝ =>
          (first - second) / (0 + expNegInvGlue 1) ^ 2)
        hfirst hsecond
    _ = 0 / (0 + expNegInvGlue 1) ^ 2 :=
      congrArg
        (fun value : ℝ => value / (0 + expNegInvGlue 1) ^ 2)
        (sub_self 0)
    _ = 0 := zero_div _

theorem Real.smoothTransitionDerivative_one :
    Real.smoothTransitionDerivative 1 = 0 := by
  unfold Real.smoothTransitionDerivative
  have honeSub : (1 : ℝ) - 1 = 0 := sub_self 1
  have hglueZero : expNegInvGlue 0 = 0 := expNegInvGlue.zero
  have hderivativeZero : Real.expNegInvGlueDerivative 0 = 0 :=
    Real.expNegInvGlueDerivative_zero
  let glueOne : ℝ := expNegInvGlue 1
  let derivativeOne : ℝ := Real.expNegInvGlueDerivative 1
  calc
    (Real.expNegInvGlueDerivative 1 *
          (expNegInvGlue 1 + expNegInvGlue (1 - 1)) -
        expNegInvGlue 1 *
          (Real.expNegInvGlueDerivative 1 -
            Real.expNegInvGlueDerivative (1 - 1))) /
        (expNegInvGlue 1 + expNegInvGlue (1 - 1)) ^ 2 =
      (derivativeOne * (glueOne + 0) -
        glueOne * (derivativeOne - 0)) /
          (glueOne + 0) ^ 2 := by
      exact congrArg₃
        (fun oneSub glueZero derivativeZero : ℝ =>
          (Real.expNegInvGlueDerivative 1 *
                (expNegInvGlue 1 + expNegInvGlue oneSub) -
              expNegInvGlue 1 *
                (Real.expNegInvGlueDerivative 1 -
                  Real.expNegInvGlueDerivative oneSub)) /
            (expNegInvGlue 1 + expNegInvGlue oneSub) ^ 2)
        honeSub hglueZero hderivativeZero
    _ = (derivativeOne * glueOne - glueOne * derivativeOne) /
        glueOne ^ 2 := by
      have hfirst : derivativeOne * (glueOne + 0) =
          derivativeOne * glueOne :=
        congrArg (fun value : ℝ => derivativeOne * value) (add_zero glueOne)
      have hsecond : glueOne * (derivativeOne - 0) =
          glueOne * derivativeOne :=
        congrArg (fun value : ℝ => glueOne * value) (sub_zero derivativeOne)
      have hdenominator : (glueOne + 0) ^ 2 = glueOne ^ 2 :=
        congrArg (fun value : ℝ => value ^ 2) (add_zero glueOne)
      exact congrArg₂ (fun numerator denominator : ℝ => numerator / denominator)
        (congrArg₂ (fun first second : ℝ => first - second) hfirst hsecond)
        hdenominator
    _ = (glueOne * derivativeOne - glueOne * derivativeOne) / glueOne ^ 2 :=
      congrArg
        (fun value : ℝ => (value - glueOne * derivativeOne) / glueOne ^ 2)
        (mul_comm derivativeOne glueOne)
    _ = 0 / glueOne ^ 2 :=
      congrArg (fun value : ℝ => value / glueOne ^ 2)
        (sub_self (glueOne * derivativeOne))
    _ = 0 := zero_div _

theorem Real.deriv_smoothTransition_zero :
    deriv smoothTransition 0 = 0 := by
  exact
    (Real.deriv_smoothTransition_exact 0).trans
      Real.smoothTransitionDerivative_zero

theorem Real.deriv_smoothTransition_one :
    deriv smoothTransition 1 = 0 := by
  exact
    (Real.deriv_smoothTransition_exact 1).trans
      Real.smoothTransitionDerivative_one

def Real.quantitativeLogarithmicLeftCutoffDerivative
    (a : ℤ) (x : ℝ) : ℝ :=
  3 * Real.smoothTransitionDerivative (3 * (x - (a : ℝ)) + 1)

theorem Real.hasDerivAt_quantitativeLogarithmicLeftCutoff
    (a : ℤ) (x : ℝ) :
    HasDerivAt
      (Real.quantitativeLogarithmicLeftCutoff a)
      (Real.quantitativeLogarithmicLeftCutoffDerivative a x) x := by
  have hshift := (hasDerivAt_id x).sub_const (a : ℝ)
  have hscaled := (3 : ℝ).const_mul hshift
  have hscaled_exact :
      HasDerivAt (fun y : ℝ => 3 * (y - (a : ℝ))) 3 x := by
    exact
      Eq.subst
        (motive := fun derivative : ℝ =>
          HasDerivAt (fun y : ℝ => 3 * (y - (a : ℝ))) derivative x)
        (mul_one 3)
        hscaled
  have hinner := hscaled_exact.add_const 1
  have houter :=
    Real.hasDerivAt_smoothTransition_exact (3 * (x - (a : ℝ)) + 1)
  have hcomposition := houter.comp x hinner
  exact hcomposition

theorem Real.deriv_quantitativeLogarithmicLeftCutoff
    (a : ℤ) (x : ℝ) :
    deriv (Real.quantitativeLogarithmicLeftCutoff a) x =
      Real.quantitativeLogarithmicLeftCutoffDerivative a x :=
  (Real.hasDerivAt_quantitativeLogarithmicLeftCutoff a x).deriv

def Real.quantitativeLogarithmicRightCutoffDerivative
    (b : ℤ) (x : ℝ) : ℝ :=
  (-3) * Real.smoothTransitionDerivative (3 * ((b : ℝ) - x) + 1)

theorem Real.three_mul_zero_sub_one_eq_neg_three :
    (3 : ℝ) * (0 - 1) = -3 := by
  calc
    (3 : ℝ) * (0 - 1) = 3 * (-1) :=
      congrArg (fun value : ℝ => 3 * value) (zero_sub 1)
    _ = -(3 * 1) := mul_neg 3 1
    _ = -3 := congrArg Neg.neg (mul_one 3)

theorem Real.hasDerivAt_quantitativeLogarithmicRightCutoff
    (b : ℤ) (x : ℝ) :
    HasDerivAt
      (Real.quantitativeLogarithmicRightCutoff b)
      (Real.quantitativeLogarithmicRightCutoffDerivative b x) x := by
  have hsub := (hasDerivAt_const x (b : ℝ)).sub (hasDerivAt_id x)
  have hscaled := (3 : ℝ).const_mul hsub
  have hscaled_exact :
      HasDerivAt (fun y : ℝ => 3 * ((b : ℝ) - y)) (-3) x := by
    exact
      Eq.subst
        (motive := fun derivative : ℝ =>
          HasDerivAt (fun y : ℝ => 3 * ((b : ℝ) - y)) derivative x)
        Real.three_mul_zero_sub_one_eq_neg_three
        hscaled
  have hinner := hscaled_exact.add_const 1
  have houter :=
    Real.hasDerivAt_smoothTransition_exact (3 * ((b : ℝ) - x) + 1)
  have hcomposition := houter.comp x hinner
  exact hcomposition

theorem Real.deriv_quantitativeLogarithmicRightCutoff
    (b : ℤ) (x : ℝ) :
    deriv (Real.quantitativeLogarithmicRightCutoff b) x =
      Real.quantitativeLogarithmicRightCutoffDerivative b x :=
  (Real.hasDerivAt_quantitativeLogarithmicRightCutoff b x).deriv

def Real.quantitativeLogarithmicBlockCutoffDerivative
    (a b : ℤ) (x : ℝ) : ℝ :=
  Real.quantitativeLogarithmicLeftCutoffDerivative a x *
      Real.quantitativeLogarithmicRightCutoff b x +
    Real.quantitativeLogarithmicLeftCutoff a x *
      Real.quantitativeLogarithmicRightCutoffDerivative b x

theorem Real.hasDerivAt_quantitativeLogarithmicBlockCutoff
    (a b : ℤ) (x : ℝ) :
    HasDerivAt
      (Real.quantitativeLogarithmicBlockCutoff a b)
      (Real.quantitativeLogarithmicBlockCutoffDerivative a b x) x := by
  have hleft := Real.hasDerivAt_quantitativeLogarithmicLeftCutoff a x
  have hright := Real.hasDerivAt_quantitativeLogarithmicRightCutoff b x
  have hproduct := hleft.mul hright
  exact hproduct

theorem Real.deriv_quantitativeLogarithmicBlockCutoff
    (a b : ℤ) (x : ℝ) :
    deriv (Real.quantitativeLogarithmicBlockCutoff a b) x =
      Real.quantitativeLogarithmicBlockCutoffDerivative a b x :=
  (Real.hasDerivAt_quantitativeLogarithmicBlockCutoff a b x).deriv

theorem Real.quantitativeLogarithmicLeftCutoffDerivative_at_supportLeft
    (a : ℤ) :
    Real.quantitativeLogarithmicLeftCutoffDerivative a
        ((a : ℝ) - 1 / 3) = 0 := by
  unfold Real.quantitativeLogarithmicLeftCutoffDerivative
  have hargument :
      3 * (((a : ℝ) - 1 / 3) - (a : ℝ)) + 1 = 0 := by
    calc
      3 * (((a : ℝ) - 1 / 3) - (a : ℝ)) + 1 =
          3 * (-(1 / 3)) + 1 :=
        congrArg (fun value : ℝ => 3 * value + 1)
          (sub_sub_cancel_left (a : ℝ) (1 / 3))
      _ = 0 := Real.three_mul_neg_one_div_three_add_one_eq_zero
  calc
    3 * Real.smoothTransitionDerivative
          (3 * (((a : ℝ) - 1 / 3) - (a : ℝ)) + 1) =
      3 * Real.smoothTransitionDerivative 0 :=
        congrArg (fun value : ℝ => 3 * Real.smoothTransitionDerivative value)
          hargument
    _ = 3 * 0 := congrArg (fun value : ℝ => 3 * value)
      Real.smoothTransitionDerivative_zero
    _ = 0 := mul_zero 3

theorem Real.quantitativeLogarithmicRightCutoffDerivative_at_supportRight
    (b : ℤ) :
    Real.quantitativeLogarithmicRightCutoffDerivative b
        ((b : ℝ) + 1 / 3) = 0 := by
  unfold Real.quantitativeLogarithmicRightCutoffDerivative
  have hargument :
      3 * ((b : ℝ) - ((b : ℝ) + 1 / 3)) + 1 = 0 := by
    have hdifference :
        (b : ℝ) - ((b : ℝ) + 1 / 3) = -(1 / 3) := by
      exact
        (sub_add_eq_sub_sub (b : ℝ) (b : ℝ) (1 / 3)).trans
          ((congrArg (fun value : ℝ => value - 1 / 3)
            (sub_self (b : ℝ))).trans (zero_sub (1 / 3)))
    exact
      (congrArg (fun value : ℝ => 3 * value + 1) hdifference).trans
        Real.three_mul_neg_one_div_three_add_one_eq_zero
  calc
    (-3) * Real.smoothTransitionDerivative
          (3 * ((b : ℝ) - ((b : ℝ) + 1 / 3)) + 1) =
      (-3) * Real.smoothTransitionDerivative 0 :=
        congrArg (fun value : ℝ => (-3) * Real.smoothTransitionDerivative value)
          hargument
    _ = (-3) * 0 := congrArg (fun value : ℝ => (-3) * value)
      Real.smoothTransitionDerivative_zero
    _ = 0 := mul_zero (-3)

theorem Real.quantitativeLogarithmicBlockCutoffDerivative_at_supportLeft
    (a b : ℤ) :
    Real.quantitativeLogarithmicBlockCutoffDerivative a b
        ((a : ℝ) - 1 / 3) = 0 := by
  unfold Real.quantitativeLogarithmicBlockCutoffDerivative
  have hleftDerivative :=
    Real.quantitativeLogarithmicLeftCutoffDerivative_at_supportLeft a
  have hleftCutoff :=
    Real.quantitativeLogarithmicLeftCutoff_eq_zero_of_le
      (le_refl ((a : ℝ) - 1 / 3))
  calc
    Real.quantitativeLogarithmicLeftCutoffDerivative a ((a : ℝ) - 1 / 3) *
          Real.quantitativeLogarithmicRightCutoff b ((a : ℝ) - 1 / 3) +
        Real.quantitativeLogarithmicLeftCutoff a ((a : ℝ) - 1 / 3) *
          Real.quantitativeLogarithmicRightCutoffDerivative b ((a : ℝ) - 1 / 3) =
      0 * Real.quantitativeLogarithmicRightCutoff b ((a : ℝ) - 1 / 3) +
        0 * Real.quantitativeLogarithmicRightCutoffDerivative b ((a : ℝ) - 1 / 3) :=
      congrArg₂ (fun first second : ℝ =>
        first * Real.quantitativeLogarithmicRightCutoff b ((a : ℝ) - 1 / 3) +
          second * Real.quantitativeLogarithmicRightCutoffDerivative b
            ((a : ℝ) - 1 / 3))
        hleftDerivative hleftCutoff
    _ = 0 + 0 := congrArg₂ (fun first second : ℝ => first + second)
      (zero_mul _) (zero_mul _)
    _ = 0 := zero_add 0

theorem Real.quantitativeLogarithmicBlockCutoffDerivative_at_supportRight
    (a b : ℤ) :
    Real.quantitativeLogarithmicBlockCutoffDerivative a b
        ((b : ℝ) + 1 / 3) = 0 := by
  unfold Real.quantitativeLogarithmicBlockCutoffDerivative
  have hrightDerivative :=
    Real.quantitativeLogarithmicRightCutoffDerivative_at_supportRight b
  have hrightCutoff :=
    Real.quantitativeLogarithmicRightCutoff_eq_zero_of_le
      (le_refl ((b : ℝ) + 1 / 3))
  calc
    Real.quantitativeLogarithmicLeftCutoffDerivative a ((b : ℝ) + 1 / 3) *
          Real.quantitativeLogarithmicRightCutoff b ((b : ℝ) + 1 / 3) +
        Real.quantitativeLogarithmicLeftCutoff a ((b : ℝ) + 1 / 3) *
          Real.quantitativeLogarithmicRightCutoffDerivative b ((b : ℝ) + 1 / 3) =
      Real.quantitativeLogarithmicLeftCutoffDerivative a ((b : ℝ) + 1 / 3) * 0 +
        Real.quantitativeLogarithmicLeftCutoff a ((b : ℝ) + 1 / 3) * 0 :=
      congrArg₂ (fun first second : ℝ =>
        Real.quantitativeLogarithmicLeftCutoffDerivative a ((b : ℝ) + 1 / 3) * first +
          Real.quantitativeLogarithmicLeftCutoff a ((b : ℝ) + 1 / 3) * second)
        hrightCutoff hrightDerivative
    _ = 0 + 0 := congrArg₂ (fun first second : ℝ => first + second)
      (mul_zero _) (mul_zero _)
    _ = 0 := zero_add 0

theorem Real.contDiff_quantitativeTransitionAffine
    (slope intercept : ℝ) :
    ContDiff ℝ ∞ (Real.quantitativeTransitionAffine slope intercept) := by
  unfold Real.quantitativeTransitionAffine
  exact (contDiff_const.mul contDiff_id).add contDiff_const

theorem Real.contDiff_expNegInvGlue_comp_affine
    (slope intercept : ℝ) :
    ContDiff ℝ ∞
      (fun x : ℝ => expNegInvGlue
        (Real.quantitativeTransitionAffine slope intercept x)) := by
  exact expNegInvGlue.contDiff.comp
    (Real.contDiff_quantitativeTransitionAffine slope intercept)

end
end LFunctions
end Boundary
