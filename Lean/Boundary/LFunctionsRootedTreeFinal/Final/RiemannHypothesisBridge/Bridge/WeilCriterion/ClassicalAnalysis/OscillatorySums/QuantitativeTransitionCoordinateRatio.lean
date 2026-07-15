import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ClassicalAnalysis.OscillatorySums.QuantitativeTransitionScalarRatio
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ClassicalAnalysis.OscillatorySums.QuantitativeTransitionSymmetry

/-!
# Coordinate specialization of the transition ratio

This owner specializes the scalar sum-gap comparison to `p=x⁻¹` and
`q=(1-x)⁻¹`, then identifies the exponential odd ratio of `p-q` with the
normalized difference of the two flat glues.
-/

namespace Boundary
namespace LFunctions

noncomputable section

theorem Real.transitionReciprocalGap_sq_eq_sum_mul_shift
    {x : ℝ}
    (hx0 : 0 < x)
    (hx1 : x < 1) :
    Real.transitionReciprocalGap x ^ 2 =
      Real.transitionReciprocalSum x *
        (Real.transitionReciprocalSum x - 4) := by
  let p := Real.transitionLeftReciprocal x
  let q := Real.transitionRightReciprocal x
  let s := Real.transitionReciprocalSum x
  have hpq : p * q = s :=
    Real.transitionReciprocal_product_eq_sum hx0 hx1
  unfold Real.transitionReciprocalGap
  change (p - q) ^ 2 = s * (s - 4)
  have hleft : (p - q) ^ 2 = p ^ 2 + q ^ 2 - 2 * (p * q) := by
    calc
      (p - q) ^ 2 = p ^ 2 - 2 * p * q + q ^ 2 := sub_sq p q
      _ = p ^ 2 - 2 * (p * q) + q ^ 2 :=
        congrArg (fun value : ℝ => p ^ 2 - value + q ^ 2)
          (mul_assoc 2 p q)
      _ = p ^ 2 + q ^ 2 - 2 * (p * q) :=
        sub_add_eq_add_sub (p ^ 2) (2 * (p * q)) (q ^ 2)
  have henergy :=
    Real.transitionReciprocalEnergy_eq_sum_sq_sub_two_sum hx0 hx1
  have hleftNormalized : p ^ 2 + q ^ 2 - 2 * (p * q) =
      s ^ 2 - 4 * s := by
    change p ^ 2 + q ^ 2 = s ^ 2 - 2 * s at henergy
    have hpqTwice : 2 * (p * q) = 2 * s :=
      congrArg (fun value : ℝ => 2 * value) hpq
    have htwoAddTwo : (2 : ℝ) + 2 = 4 :=
      Real.transition_nat_cast_add 2 2 4 rfl
    have htwiceAdd : 2 * s + 2 * s = 4 * s :=
      Eq.trans
        (add_mul 2 2 s).symm
        (congrArg (fun coefficient : ℝ => coefficient * s) htwoAddTwo)
    calc
      p ^ 2 + q ^ 2 - 2 * (p * q) =
          (s ^ 2 - 2 * s) - 2 * s :=
        congrArg₂ (fun first second : ℝ => first - second)
          henergy hpqTwice
      _ = s ^ 2 - (2 * s + 2 * s) :=
        sub_sub (s ^ 2) (2 * s) (2 * s)
      _ = s ^ 2 - 4 * s :=
        congrArg (fun value : ℝ => s ^ 2 - value) htwiceAdd
  have hright : s * (s - 4) = s ^ 2 - 4 * s := by
    exact (mul_sub s s 4).trans
      (congrArg₂ (fun first second : ℝ => first - second)
        (pow_two s).symm (mul_comm s 4))
  exact Eq.trans hleft
    (Eq.trans hleftNormalized hright.symm)

theorem Real.transitionCoordinateCurvatureRatio_le_exponential
    {x : ℝ}
    (hx0 : 0 < x)
    (hxHalf : x ≤ 1 / 2) :
    Real.transitionScalarCurvatureRatio
        (Real.transitionReciprocalSum x)
        (Real.transitionReciprocalGap x) ≤
      Real.exponentialOddRatio (Real.transitionReciprocalGap x) := by
  have hxOne : x < 1 := by
    have hhalfLtOne : (1 / 2 : ℝ) < 1 := by
      exact (div_lt_one zero_lt_two).mpr one_lt_two
    exact lt_of_le_of_lt hxHalf hhalfLtOne
  have hsum := Real.four_le_transitionReciprocalSum hx0 hxOne
  have hgap := Real.transitionReciprocalGap_nonneg hx0 hxHalf
  have hgapSquare :=
    Real.transitionReciprocalGap_sq_eq_sum_mul_shift hx0 hxOne
  exact Real.transitionScalarCurvatureRatio_le_exponentialOddRatio
    hsum hgap hgapSquare

theorem Real.exp_transitionReciprocalGap_eq_glue_ratio
    {x : ℝ}
    (hx0 : 0 < x)
    (hx1 : x < 1) :
    Real.exp (Real.transitionReciprocalGap x) =
      expNegInvGlue (1 - x) / expNegInvGlue x := by
  have hxComp : 0 < 1 - x := sub_pos.mpr hx1
  have hgLeft := Real.expNegInvGlue_eq_exp_neg_inv_of_pos hx0
  have hgRight := Real.expNegInvGlue_eq_exp_neg_inv_of_pos hxComp
  unfold Real.transitionReciprocalGap
  unfold Real.transitionLeftReciprocal
  unfold Real.transitionRightReciprocal
  have hdiff : x⁻¹ - (1 - x)⁻¹ =
      (-(1 - x)⁻¹) - (-x⁻¹) := by
    calc
      x⁻¹ - (1 - x)⁻¹ = x⁻¹ + (-(1 - x)⁻¹) := sub_eq_add_neg _ _
      _ = (-(1 - x)⁻¹) + x⁻¹ := add_comm _ _
      _ = (-(1 - x)⁻¹) + (-(-x⁻¹)) :=
        congrArg (fun value : ℝ => (-(1 - x)⁻¹) + value)
          (neg_neg x⁻¹).symm
      _ = (-(1 - x)⁻¹) - (-x⁻¹) :=
        (sub_eq_add_neg (-(1 - x)⁻¹) (-x⁻¹)).symm
  have hexp := Real.exp_sub (-(1 - x)⁻¹) (-x⁻¹)
  exact Eq.trans
    (congrArg Real.exp hdiff)
    (Eq.trans hexp
      (congrArg₂ (fun numerator denominator : ℝ => numerator / denominator)
        hgRight.symm hgLeft.symm))

theorem Real.exponentialOddRatio_transitionGap_eq_glue_difference
    {x : ℝ}
    (hx0 : 0 < x)
    (hx1 : x < 1) :
    Real.exponentialOddRatio (Real.transitionReciprocalGap x) =
      (expNegInvGlue (1 - x) - expNegInvGlue x) /
        (expNegInvGlue (1 - x) + expNegInvGlue x) := by
  let A := expNegInvGlue x
  let B := expNegInvGlue (1 - x)
  have hA : 0 < A := expNegInvGlue.pos_of_pos hx0
  have hANe : A ≠ 0 := ne_of_gt hA
  have hratio := Real.exp_transitionReciprocalGap_eq_glue_ratio hx0 hx1
  unfold Real.exponentialOddRatio
  change (Real.exp (Real.transitionReciprocalGap x) - 1) /
      (Real.exp (Real.transitionReciprocalGap x) + 1) =
    (B - A) / (B + A)
  calc
    (Real.exp (Real.transitionReciprocalGap x) - 1) /
        (Real.exp (Real.transitionReciprocalGap x) + 1) =
      (B / A - 1) / (B / A + 1) :=
        congrArg₂ (fun numerator denominator : ℝ =>
          (numerator - 1) / (denominator + 1)) hratio hratio
    _ = ((B - A) / A) / ((B + A) / A) := by
      have hminus : B / A - 1 = (B - A) / A := by
        exact Eq.trans
          (congrArg (fun value : ℝ => B / A - value)
            (div_self hANe).symm)
          (sub_div B A A).symm
      have hplus : B / A + 1 = (B + A) / A := by
        exact Eq.trans
          (congrArg (fun value : ℝ => B / A + value)
            (div_self hANe).symm)
          (add_div B A A).symm
      exact congrArg₂ (fun numerator denominator : ℝ => numerator / denominator)
        hminus hplus
    _ = (B - A) / (B + A) := by
      exact div_div_div_cancel_right₀ hANe (B - A) (B + A)

theorem Real.monotone_expNegInvGlue :
    Monotone expNegInvGlue := by
  exact monotone_of_deriv_nonneg
    Real.differentiableAt_expNegInvGlue
    (fun x =>
      Eq.subst
        (motive := fun value : ℝ => 0 ≤ value)
        (Real.deriv_expNegInvGlue_exact x).symm
        (Real.expNegInvGlueDerivative_nonneg x))

theorem Real.glue_difference_nonneg_on_left_half
    {x : ℝ}
    (hx0 : 0 < x)
    (hxHalf : x ≤ 1 / 2) :
    0 ≤ expNegInvGlue (1 - x) - expNegInvGlue x := by
  have hxComplement := Real.transition_left_le_right_complement hxHalf
  have hmono := Real.monotone_expNegInvGlue hxComplement
  exact sub_nonneg.mpr hmono

end
end LFunctions
end Boundary
