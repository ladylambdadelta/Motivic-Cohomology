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
    have hbound := Real.twice_reciprocal_product_le_energy p q
    have hsquare : 0 ≤ (p - q) ^ 2 := sq_nonneg (p - q)
    calc
      (p - q) ^ 2 = (p - q) * (p - q) := pow_two (p - q)
      _ = p * p - p * q - (q * p - q * q) := by
        exact (mul_sub (p - q) p q).trans
          (congrArg₂ (fun first second : ℝ => first - second)
            (sub_mul p q p) (sub_mul p q q))
      _ = p ^ 2 + q ^ 2 - 2 * (p * q) := by
        have hpp : p * p = p ^ 2 := (pow_two p).symm
        have hqq : q * q = q ^ 2 := (pow_two q).symm
        have hqp : q * p = p * q := mul_comm q p
        exact Eq.trans
          (congrArg₂ (fun first second : ℝ => first - second)
            (congrArg₂ (fun first second : ℝ => first - second) hpp rfl)
            (congrArg₂ (fun first second : ℝ => first - second) hqp hqq))
          (sub_sub_sub_cancel_right (p ^ 2 - p * q) (p * q) (q ^ 2)).trans
          (congrArg (fun value : ℝ => p ^ 2 + q ^ 2 - value)
            (two_mul (p * q)).symm)
  have henergy :=
    Real.transitionReciprocalEnergy_eq_sum_sq_sub_two_sum hx0 hx1
  have hleftNormalized : p ^ 2 + q ^ 2 - 2 * (p * q) =
      s ^ 2 - 4 * s := by
    have hpqTwice : 2 * (p * q) = 2 * s :=
      congrArg (fun value : ℝ => 2 * value) hpq
    exact Eq.trans
      (congrArg₂ (fun first second : ℝ => first - second)
        henergy hpqTwice)
      (Eq.trans
        (sub_sub (s ^ 2) (2 * s) (2 * s)).symm
        (congrArg (fun value : ℝ => s ^ 2 - value)
          ((add_mul 2 2 s).symm.trans
            (congrArg (fun coefficient : ℝ => coefficient * s)
              (show (2 : ℝ) + 2 = 4 from rfl)))))
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
      exact (div_lt_one₀ zero_lt_two).mpr one_lt_two
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
      _ = (-(1 - x)⁻¹) - (-x⁻¹) :=
        (sub_eq_add_neg (-(1 - x)⁻¹) (-x⁻¹)).symm.trans
          (congrArg (fun value : ℝ => (-(1 - x)⁻¹) + value)
            (neg_neg x⁻¹))
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
  have hA : 0 < A := expNegInvGlue.pos hx0
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
      exact div_div_div_cancel_right₀ (B - A) (B + A) hANe

theorem Real.glue_difference_nonneg_on_left_half
    {x : ℝ}
    (hx0 : 0 < x)
    (hxHalf : x ≤ 1 / 2) :
    0 ≤ expNegInvGlue (1 - x) - expNegInvGlue x := by
  have hxComplement := Real.transition_left_le_right_complement hxHalf
  have hmono := expNegInvGlue.monotone hxComplement
  exact sub_nonneg.mpr hmono

end
end LFunctions
end Boundary
