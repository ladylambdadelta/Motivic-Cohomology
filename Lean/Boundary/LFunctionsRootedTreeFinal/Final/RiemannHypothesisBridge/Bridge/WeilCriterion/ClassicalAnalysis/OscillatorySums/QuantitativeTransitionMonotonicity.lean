import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ClassicalAnalysis.OscillatorySums.QuantitativeTransitionVariation

/-!
# Monotonicity and variation of the quantitative transition

The smooth transition is monotone because its quotient-rule numerator is a
sum of two nonnegative glue products.  This owner records that sign explicitly
and transports it to the increasing and decreasing logarithmic collars.
-/

namespace Boundary
namespace LFunctions

noncomputable section

theorem Real.expNegInvGlueDerivative_nonneg
    (x : ℝ) :
    0 ≤ Real.expNegInvGlueDerivative x := by
  exact Eq.subst
    (motive := fun value : ℝ => 0 ≤ value)
    (Real.expNegInvGlueDerivative_eq_inv_sq_mul x).symm
    (mul_nonneg (sq_nonneg x⁻¹) (expNegInvGlue.nonneg x))

theorem Real.smoothTransitionDerivative_numerator_eq
    (x : ℝ) :
    Real.expNegInvGlueDerivative x *
          (expNegInvGlue x + expNegInvGlue (1 - x)) -
        expNegInvGlue x *
          (Real.expNegInvGlueDerivative x -
            Real.expNegInvGlueDerivative (1 - x)) =
      Real.expNegInvGlueDerivative x * expNegInvGlue (1 - x) +
        expNegInvGlue x * Real.expNegInvGlueDerivative (1 - x) := by
  let dx := Real.expNegInvGlueDerivative x
  let dy := Real.expNegInvGlueDerivative (1 - x)
  let gx := expNegInvGlue x
  let gy := expNegInvGlue (1 - x)
  calc
    dx * (gx + gy) - gx * (dx - dy) =
        (dx * gx + dx * gy) - gx * (dx - dy) :=
      congrArg (fun value : ℝ => value - gx * (dx - dy))
        (mul_add dx gx gy)
    _ = (dx * gx + dx * gy) - (gx * dx - gx * dy) :=
      congrArg
        (fun value : ℝ => (dx * gx + dx * gy) - value)
        (mul_sub gx dx dy)
    _ = (dx * gx + dx * gy) + (-(gx * dx - gx * dy)) :=
      sub_eq_add_neg _ _
    _ = (dx * gx + dx * gy) + (-gx * dx + gx * dy) := by
      have hnegative : -(gx * dx - gx * dy) = -gx * dx + gx * dy := by
        exact
          (neg_sub (gx * dx) (gx * dy)).trans
            (congrArg₂ (fun first second : ℝ => first + second)
              (neg_mul gx dx) rfl)
      exact congrArg (fun value : ℝ => (dx * gx + dx * gy) + value)
        hnegative
    _ = ((dx * gx) + (-gx * dx)) + (dx * gy + gx * dy) := by
      exact
        (add_assoc (dx * gx) (dx * gy) (-gx * dx + gx * dy)).trans
          ((congrArg
            (fun value : ℝ => dx * gx + value)
            ((add_assoc (dx * gy) (-gx * dx) (gx * dy)).symm.trans
              (congrArg
                (fun value : ℝ => value + gx * dy)
                (add_comm (dx * gy) (-gx * dx))))).trans
            ((add_assoc (dx * gx) (-gx * dx) (dx * gy + gx * dy)).symm))
    _ = 0 + (dx * gy + gx * dy) :=
      congrArg (fun value : ℝ => value + (dx * gy + gx * dy))
        ((congrArg (fun value : ℝ => dx * gx + value)
          (congrArg Neg.neg (mul_comm gx dx))).trans
          (add_neg_cancel (dx * gx)))
    _ = dx * gy + gx * dy := zero_add _

theorem Real.smoothTransitionDerivative_nonneg
    (x : ℝ) :
    0 ≤ Real.smoothTransitionDerivative x := by
  unfold Real.smoothTransitionDerivative
  have hnumeratorEq := Real.smoothTransitionDerivative_numerator_eq x
  have hfirst : 0 ≤
      Real.expNegInvGlueDerivative x * expNegInvGlue (1 - x) :=
    mul_nonneg
      (Real.expNegInvGlueDerivative_nonneg x)
      (expNegInvGlue.nonneg (1 - x))
  have hsecond : 0 ≤
      expNegInvGlue x * Real.expNegInvGlueDerivative (1 - x) :=
    mul_nonneg
      (expNegInvGlue.nonneg x)
      (Real.expNegInvGlueDerivative_nonneg (1 - x))
  have hnumerator : 0 ≤
      Real.expNegInvGlueDerivative x *
          (expNegInvGlue x + expNegInvGlue (1 - x)) -
        expNegInvGlue x *
          (Real.expNegInvGlueDerivative x -
            Real.expNegInvGlueDerivative (1 - x)) :=
    Eq.subst
      (motive := fun value : ℝ => 0 ≤ value)
      hnumeratorEq.symm
      (add_nonneg hfirst hsecond)
  exact div_nonneg hnumerator (sq_nonneg _)

theorem Real.deriv_smoothTransition_nonneg
    (x : ℝ) :
    0 ≤ deriv smoothTransition x := by
  exact Eq.subst
    (motive := fun value : ℝ => 0 ≤ value)
    (Real.deriv_smoothTransition_exact x).symm
    (Real.smoothTransitionDerivative_nonneg x)

theorem Real.monotone_smoothTransition :
    Monotone smoothTransition := by
  exact monotone_of_deriv_nonneg
    (fun x => (Real.hasDerivAt_smoothTransition_exact x).differentiableAt)
    Real.deriv_smoothTransition_nonneg

theorem Real.quantitativeLogarithmicLeftCutoffDerivative_nonneg
    (a : ℤ) (x : ℝ) :
    0 ≤ Real.quantitativeLogarithmicLeftCutoffDerivative a x := by
  unfold Real.quantitativeLogarithmicLeftCutoffDerivative
  exact mul_nonneg
    (Nat.cast_nonneg 3)
    (Real.smoothTransitionDerivative_nonneg _)

theorem Real.quantitativeLogarithmicRightCutoffDerivative_nonpos
    (b : ℤ) (x : ℝ) :
    Real.quantitativeLogarithmicRightCutoffDerivative b x ≤ 0 := by
  unfold Real.quantitativeLogarithmicRightCutoffDerivative
  have hnegative : (-3 : ℝ) ≤ 0 := neg_nonpos.mpr (Nat.cast_nonneg 3)
  exact mul_nonpos_of_nonpos_of_nonneg hnegative
    (Real.smoothTransitionDerivative_nonneg _)

theorem Real.abs_quantitativeLogarithmicLeftCutoffDerivative
    (a : ℤ) (x : ℝ) :
    |Real.quantitativeLogarithmicLeftCutoffDerivative a x| =
      Real.quantitativeLogarithmicLeftCutoffDerivative a x := by
  exact abs_of_nonneg
    (Real.quantitativeLogarithmicLeftCutoffDerivative_nonneg a x)

theorem Real.abs_quantitativeLogarithmicRightCutoffDerivative
    (b : ℤ) (x : ℝ) :
    |Real.quantitativeLogarithmicRightCutoffDerivative b x| =
      -Real.quantitativeLogarithmicRightCutoffDerivative b x := by
  exact abs_of_nonpos
    (Real.quantitativeLogarithmicRightCutoffDerivative_nonpos b x)

theorem Real.quantitativeLogarithmicLeftCutoff_monotone
    (a : ℤ) :
    Monotone (Real.quantitativeLogarithmicLeftCutoff a) := by
  exact monotone_of_deriv_nonneg
    (fun x =>
      (Real.hasDerivAt_quantitativeLogarithmicLeftCutoff a x).differentiableAt)
    (fun x =>
      Eq.subst
        (motive := fun value : ℝ => 0 ≤ value)
        (Real.deriv_quantitativeLogarithmicLeftCutoff a x).symm
        (Real.quantitativeLogarithmicLeftCutoffDerivative_nonneg a x))

theorem Real.quantitativeLogarithmicRightCutoff_antitone
    (b : ℤ) :
    Antitone (Real.quantitativeLogarithmicRightCutoff b) := by
  exact antitone_of_deriv_nonpos
    (fun x =>
      (Real.hasDerivAt_quantitativeLogarithmicRightCutoff b x).differentiableAt)
    (fun x =>
      Eq.subst
        (motive := fun value : ℝ => value ≤ 0)
        (Real.deriv_quantitativeLogarithmicRightCutoff b x).symm
        (Real.quantitativeLogarithmicRightCutoffDerivative_nonpos b x))

theorem Real.quantitativeLogarithmicLeftCutoff_at_supportLeft
    (a : ℤ) :
    Real.quantitativeLogarithmicLeftCutoff a ((a : ℝ) - 1 / 3) = 0 := by
  exact Real.quantitativeLogarithmicLeftCutoff_eq_zero_of_le
    (le_refl ((a : ℝ) - 1 / 3))

theorem Real.quantitativeLogarithmicLeftCutoff_at_core
    (a : ℤ) :
    Real.quantitativeLogarithmicLeftCutoff a (a : ℝ) = 1 := by
  exact Real.quantitativeLogarithmicLeftCutoff_eq_one_of_le (le_refl (a : ℝ))

theorem Real.quantitativeLogarithmicRightCutoff_at_core
    (b : ℤ) :
    Real.quantitativeLogarithmicRightCutoff b (b : ℝ) = 1 := by
  exact Real.quantitativeLogarithmicRightCutoff_eq_one_of_le (le_refl (b : ℝ))

theorem Real.quantitativeLogarithmicRightCutoff_at_supportRight
    (b : ℤ) :
    Real.quantitativeLogarithmicRightCutoff b ((b : ℝ) + 1 / 3) = 0 := by
  exact Real.quantitativeLogarithmicRightCutoff_eq_zero_of_le
    (le_refl ((b : ℝ) + 1 / 3))

end
end LFunctions
end Boundary
