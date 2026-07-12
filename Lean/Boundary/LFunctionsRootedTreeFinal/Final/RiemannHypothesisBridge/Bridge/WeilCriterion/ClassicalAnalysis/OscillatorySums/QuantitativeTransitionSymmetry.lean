import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ClassicalAnalysis.OscillatorySums.QuantitativeTransitionSecondDerivative

/-!
# Reflection symmetry of the quantitative transition

The normalized flat transition satisfies `S(1-x)=1-S(x)`.  Its first
derivative is therefore reflection-invariant and its second derivative is
reflection-anti-invariant.  These identities are the structural input for the
sharp curvature-variation estimate.
-/

namespace Boundary
namespace LFunctions

noncomputable section

theorem Real.smoothTransitionDenominator_reflection
    (x : ℝ) :
    expNegInvGlue (1 - x) + expNegInvGlue (1 - (1 - x)) =
      expNegInvGlue x + expNegInvGlue (1 - x) := by
  have hinner : 1 - (1 - x) = x := by
    calc
      1 - (1 - x) = 1 + -(1 - x) := sub_eq_add_neg _ _
      _ = 1 + (-1 + x) := by
        exact congrArg (fun value : ℝ => 1 + value)
          ((neg_sub 1 x).trans
            (congrArg₂ (fun first second : ℝ => first + second)
              rfl (neg_neg x)))
      _ = (1 + -1) + x := (add_assoc 1 (-1) x).symm
      _ = 0 + x :=
        congrArg (fun value : ℝ => value + x) (add_neg_cancel 1)
      _ = x := zero_add _
  exact Eq.trans
    (congrArg
      (fun value : ℝ => expNegInvGlue (1 - x) + expNegInvGlue value)
      hinner)
    (add_comm _ _)

theorem Real.smoothTransition_reflection_add
    (x : ℝ) :
    smoothTransition (1 - x) + smoothTransition x = 1 := by
  unfold smoothTransition
  have hinner : 1 - (1 - x) = x := by
    exact sub_sub_cancel_left 1 x
  have hdenominator := Real.smoothTransitionDenominator_reflection x
  let gx := expNegInvGlue x
  let gy := expNegInvGlue (1 - x)
  have hdenominatorNe : gx + gy ≠ 0 :=
    ne_of_gt (Real.smoothTransitionDenominator_pos x)
  have hreflected :
      expNegInvGlue (1 - x) /
          (expNegInvGlue (1 - x) + expNegInvGlue (1 - (1 - x))) =
        gy / (gx + gy) := by
    exact congrArg (fun denominator : ℝ => gy / denominator) hdenominator
  have hsum : gy / (gx + gy) + gx / (gx + gy) = 1 := by
    calc
      gy / (gx + gy) + gx / (gx + gy) =
          (gy + gx) / (gx + gy) :=
        (add_div gy gx (gx + gy)).symm
      _ = (gx + gy) / (gx + gy) :=
        congrArg (fun numerator : ℝ => numerator / (gx + gy))
          (add_comm gy gx)
      _ = 1 := div_self hdenominatorNe
  exact Eq.trans
    (congrArg₂ (fun first second : ℝ => first + second)
      hreflected rfl)
    hsum

theorem Real.smoothTransition_reflection
    (x : ℝ) :
    smoothTransition (1 - x) = 1 - smoothTransition x := by
  have hsum := Real.smoothTransition_reflection_add x
  exact eq_sub_of_add_eq hsum

theorem Real.smoothTransition_half_eq_half :
    smoothTransition (1 / 2) = 1 / 2 := by
  have hreflection := Real.smoothTransition_reflection (1 / 2)
  have hhalfReflection : (1 : ℝ) - 1 / 2 = 1 / 2 := by
    have htwoNe : (2 : ℝ) ≠ 0 := two_ne_zero
    have honeEq : (1 : ℝ) = 2 / 2 :=
      (div_self htwoNe).symm
    calc
      (1 : ℝ) - 1 / 2 = 2 / 2 - 1 / 2 :=
        congrArg (fun value : ℝ => value - 1 / 2) honeEq
      _ = (2 - 1) / 2 := (sub_div 2 1 2).symm
      _ = 1 / 2 :=
        congrArg (fun numerator : ℝ => numerator / 2)
          (show (2 : ℝ) - 1 = 1 from sub_self_add_one 1)
  have hequation :
      smoothTransition (1 / 2) = 1 - smoothTransition (1 / 2) :=
    Eq.subst
      (motive := fun reflected : ℝ =>
        smoothTransition reflected = 1 - smoothTransition (1 / 2))
      hhalfReflection
      hreflection
  have hdouble :
      smoothTransition (1 / 2) + smoothTransition (1 / 2) = 1 := by
    exact add_eq_of_eq_sub hequation
  have htwoMul :
      2 * smoothTransition (1 / 2) = 1 := by
    exact Eq.trans
      (two_mul (smoothTransition (1 / 2)))
      hdouble
  exact (eq_div_iff two_ne_zero).2 htwoMul

theorem Real.smoothTransitionDerivativeNumerator_reflection
    (x : ℝ) :
    Real.smoothTransitionDerivativeNumerator (1 - x) =
      Real.smoothTransitionDerivativeNumerator x := by
  unfold Real.smoothTransitionDerivativeNumerator
  have hinner : 1 - (1 - x) = x := sub_sub_cancel_left 1 x
  calc
    Real.expNegInvGlueDerivative (1 - x) *
          expNegInvGlue (1 - (1 - x)) +
        expNegInvGlue (1 - x) *
          Real.expNegInvGlueDerivative (1 - (1 - x)) =
      Real.expNegInvGlueDerivative (1 - x) * expNegInvGlue x +
        expNegInvGlue (1 - x) * Real.expNegInvGlueDerivative x :=
      congrArg₂ (fun first second : ℝ => first + second)
        (congrArg
          (fun value : ℝ =>
            Real.expNegInvGlueDerivative (1 - x) * expNegInvGlue value)
          hinner)
        (congrArg
          (fun value : ℝ =>
            expNegInvGlue (1 - x) * Real.expNegInvGlueDerivative value)
          hinner)
    _ = expNegInvGlue x * Real.expNegInvGlueDerivative (1 - x) +
        Real.expNegInvGlueDerivative x * expNegInvGlue (1 - x) :=
      congrArg₂ (fun first second : ℝ => first + second)
        (mul_comm _ _) (mul_comm _ _)
    _ = Real.expNegInvGlueDerivative x * expNegInvGlue (1 - x) +
        expNegInvGlue x * Real.expNegInvGlueDerivative (1 - x) :=
      add_comm _ _

theorem Real.smoothTransitionDerivativeDenominator_reflection
    (x : ℝ) :
    Real.smoothTransitionDerivativeDenominator (1 - x) =
      Real.smoothTransitionDerivativeDenominator x := by
  unfold Real.smoothTransitionDerivativeDenominator
  exact Real.smoothTransitionDenominator_reflection x

theorem Real.smoothTransitionDerivative_reflection
    (x : ℝ) :
    Real.smoothTransitionDerivative (1 - x) =
      Real.smoothTransitionDerivative x := by
  have hleft := Real.smoothTransitionDerivative_eq_normalized (1 - x)
  have hright := Real.smoothTransitionDerivative_eq_normalized x
  have hnumerator := Real.smoothTransitionDerivativeNumerator_reflection x
  have hdenominator :=
    Real.smoothTransitionDerivativeDenominator_reflection x
  exact Eq.trans hleft
    (Eq.trans
      (congrArg₂ (fun numerator denominator : ℝ => numerator / denominator ^ 2)
        hnumerator hdenominator)
      hright.symm)

theorem Real.deriv_smoothTransition_reflection
    (x : ℝ) :
    deriv smoothTransition (1 - x) = deriv smoothTransition x := by
  exact Eq.trans
    (Real.deriv_smoothTransition_exact (1 - x))
    (Eq.trans
      (Real.smoothTransitionDerivative_reflection x)
      (Real.deriv_smoothTransition_exact x).symm)

theorem Real.smoothTransitionSecondDerivative_reflection_neg
    (x : ℝ) :
    Real.smoothTransitionSecondDerivative (1 - x) =
      -Real.smoothTransitionSecondDerivative x := by
  have hfunction :
      (fun y : ℝ => Real.smoothTransitionDerivative (1 - y)) =
        Real.smoothTransitionDerivative := by
    funext y
    exact Real.smoothTransitionDerivative_reflection y
  have hleftOuter := Real.hasDerivAt_smoothTransitionDerivative (1 - x)
  have hinner := (hasDerivAt_const x 1).sub (hasDerivAt_id x)
  have hcomposition := hleftOuter.comp x hinner
  have hleftDerivative :
      HasDerivAt
        (fun y : ℝ => Real.smoothTransitionDerivative (1 - y))
        (-Real.smoothTransitionSecondDerivative (1 - x)) x := by
    exact Eq.subst
      (motive := fun value : ℝ =>
        HasDerivAt
          (fun y : ℝ => Real.smoothTransitionDerivative (1 - y))
          value x)
      (mul_neg_one (Real.smoothTransitionSecondDerivative (1 - x)))
      hcomposition
  have htransported :
      HasDerivAt Real.smoothTransitionDerivative
        (-Real.smoothTransitionSecondDerivative (1 - x)) x :=
    Eq.subst
      (motive := fun function : ℝ → ℝ =>
        HasDerivAt function
          (-Real.smoothTransitionSecondDerivative (1 - x)) x)
      hfunction
      hleftDerivative
  have hunique := htransported.unique
    (Real.hasDerivAt_smoothTransitionDerivative x)
  have hnegEquality :
      -Real.smoothTransitionSecondDerivative (1 - x) =
        Real.smoothTransitionSecondDerivative x :=
    hunique
  exact neg_eq_iff_eq_neg.mpr hnegEquality

theorem Real.smoothTransitionSecondDerivative_half_eq_zero :
    Real.smoothTransitionSecondDerivative (1 / 2) = 0 := by
  have hreflection :=
    Real.smoothTransitionSecondDerivative_reflection_neg (1 / 2)
  have hhalfReflection : (1 : ℝ) - 1 / 2 = 1 / 2 := by
    have htwoNe : (2 : ℝ) ≠ 0 := two_ne_zero
    calc
      (1 : ℝ) - 1 / 2 = 2 / 2 - 1 / 2 :=
        congrArg (fun value : ℝ => value - 1 / 2) (div_self htwoNe).symm
      _ = (2 - 1) / 2 := (sub_div 2 1 2).symm
      _ = 1 / 2 :=
        congrArg (fun numerator : ℝ => numerator / 2)
          (show (2 : ℝ) - 1 = 1 from sub_self_add_one 1)
  have hselfNeg :
      Real.smoothTransitionSecondDerivative (1 / 2) =
        -Real.smoothTransitionSecondDerivative (1 / 2) :=
    Eq.subst
      (motive := fun reflected : ℝ =>
        Real.smoothTransitionSecondDerivative reflected =
          -Real.smoothTransitionSecondDerivative (1 / 2))
      hhalfReflection
      hreflection
  exact (CharZero.eq_neg_self_iff).mp hselfNeg

theorem Real.abs_smoothTransitionSecondDerivative_reflection
    (x : ℝ) :
    |Real.smoothTransitionSecondDerivative (1 - x)| =
      |Real.smoothTransitionSecondDerivative x| := by
  exact Eq.trans
    (congrArg abs
      (Real.smoothTransitionSecondDerivative_reflection_neg x))
    (abs_neg _)

end
end LFunctions
end Boundary
