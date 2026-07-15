import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ClassicalAnalysis.OscillatorySums.QuantitativeGlueSecondDerivative

/-!
# Uniform denominator separation for the smooth transition

On the unit interval, one of `x` and `1 - x` is at least one half.  The
corresponding glue term is at least `exp (-2)`, so the transition denominator
is uniformly separated from zero.
-/

namespace Boundary
namespace LFunctions

noncomputable section

theorem Real.one_le_two_mul_of_half_le
    {x : ℝ}
    (hx : (1 / 2 : ℝ) ≤ x) :
    1 ≤ 2 * x := by
  have htwoPos : (0 : ℝ) < 2 :=
    Nat.cast_pos.mpr (Nat.succ_pos 1)
  have hmul := mul_le_mul_of_nonneg_left hx htwoPos.le
  have hleft : (2 : ℝ) * (1 / 2) = 1 := by
    have htwoNe : (2 : ℝ) ≠ 0 := ne_of_gt htwoPos
    exact
      (congrArg (fun value : ℝ => 2 * value) (one_div 2)).trans
        (mul_inv_cancel₀ htwoNe)
  exact le_trans (le_of_eq hleft.symm) hmul

theorem Real.inv_le_two_of_half_le
    {x : ℝ}
    (hx : (1 / 2 : ℝ) ≤ x) :
    x⁻¹ ≤ 2 := by
  have hhalfPos : (0 : ℝ) < 1 / 2 := by
    exact div_pos zero_lt_one
      (Nat.cast_pos.mpr (Nat.succ_pos 1))
  have hinverse : x⁻¹ ≤ ((1 / 2 : ℝ))⁻¹ :=
    inv_anti₀ hhalfPos hx
  have hhalfInverse : ((1 / 2 : ℝ))⁻¹ = 2 := by
    have honeDiv : (1 / 2 : ℝ) = (2 : ℝ)⁻¹ := one_div 2
    exact Eq.trans (congrArg Inv.inv honeDiv) (inv_inv 2)
  exact le_trans hinverse (le_of_eq hhalfInverse)

theorem Real.exp_neg_two_le_exp_neg_inv_of_half_le
    {x : ℝ}
    (hx : (1 / 2 : ℝ) ≤ x) :
    Real.exp (-2) ≤ Real.exp (-x⁻¹) := by
  have hinverse := Real.inv_le_two_of_half_le hx
  exact Real.exp_le_exp.mpr (neg_le_neg hinverse)

theorem Real.expNegInvGlue_eq_exp_neg_inv_of_pos
    {x : ℝ}
    (hx : 0 < x) :
    expNegInvGlue x = Real.exp (-x⁻¹) := by
  unfold expNegInvGlue
  exact if_neg (not_le.mpr hx)

theorem Real.exp_neg_two_le_expNegInvGlue_of_half_le
    {x : ℝ}
    (hx : (1 / 2 : ℝ) ≤ x) :
    Real.exp (-2) ≤ expNegInvGlue x := by
  have hhalfPos : (0 : ℝ) < 1 / 2 := by
    exact div_pos zero_lt_one
      (Nat.cast_pos.mpr (Nat.succ_pos 1))
  have hxPos : 0 < x := lt_of_lt_of_le hhalfPos hx
  exact le_trans
    (Real.exp_neg_two_le_exp_neg_inv_of_half_le hx)
    (le_of_eq (Real.expNegInvGlue_eq_exp_neg_inv_of_pos hxPos).symm)

theorem Real.half_le_one_sub_of_le_half
    {x : ℝ}
    (hx : x ≤ (1 / 2 : ℝ)) :
    (1 / 2 : ℝ) ≤ 1 - x := by
  have hhalfSum : (1 / 2 : ℝ) + 1 / 2 = 1 := by
    calc
      (1 / 2 : ℝ) + 1 / 2 = (1 + 1) / 2 := (add_div 1 1 2).symm
      _ = 2 / 2 := congrArg (fun value : ℝ => value / 2) one_add_one_eq_two
      _ = 1 := by
        have htwoNe : (2 : ℝ) ≠ 0 :=
          ne_of_gt (Nat.cast_pos.mpr (Nat.succ_pos 1))
        exact div_self htwoNe
  exact (le_sub_iff_add_le).mpr
    (le_trans
      (add_le_add_left hx (1 / 2 : ℝ))
      (le_of_eq hhalfSum))

theorem Real.half_le_x_or_half_le_one_sub
    (x : ℝ) :
    (1 / 2 : ℝ) ≤ x ∨ (1 / 2 : ℝ) ≤ 1 - x := by
  match le_total (1 / 2 : ℝ) x with
  | Or.inl hx => exact Or.inl hx
  | Or.inr hx => exact Or.inr (Real.half_le_one_sub_of_le_half hx)

theorem Real.exp_neg_two_le_smoothTransitionDenominator
    (x : ℝ) :
    Real.exp (-2) ≤
      expNegInvGlue x + expNegInvGlue (1 - x) := by
  match Real.half_le_x_or_half_le_one_sub x with
  | Or.inl hx =>
      have hleft := Real.exp_neg_two_le_expNegInvGlue_of_half_le hx
      exact le_trans hleft
        (le_add_of_nonneg_right (expNegInvGlue.nonneg (1 - x)))
  | Or.inr hx =>
      have hright := Real.exp_neg_two_le_expNegInvGlue_of_half_le hx
      exact le_trans hright
        (le_add_of_nonneg_left (expNegInvGlue.nonneg x))

theorem Real.smoothTransitionDenominator_pos
    (x : ℝ) :
    0 < expNegInvGlue x + expNegInvGlue (1 - x) := by
  exact lt_of_lt_of_le (Real.exp_pos (-2))
    (Real.exp_neg_two_le_smoothTransitionDenominator x)

theorem Real.inv_smoothTransitionDenominator_le_exp_two
    (x : ℝ) :
    (expNegInvGlue x + expNegInvGlue (1 - x))⁻¹ ≤ Real.exp 2 := by
  have hlowerPos : 0 < Real.exp (-2) := Real.exp_pos (-2)
  have hlower := Real.exp_neg_two_le_smoothTransitionDenominator x
  have hinverse :
      (expNegInvGlue x + expNegInvGlue (1 - x))⁻¹ ≤
        (Real.exp (-2))⁻¹ :=
    inv_anti₀ hlowerPos hlower
  have hnormalize : (Real.exp (-2))⁻¹ = Real.exp 2 := by
    have hnegExp : Real.exp (-2) = (Real.exp 2)⁻¹ := Real.exp_neg 2
    exact Eq.trans
      (congrArg Inv.inv hnegExp)
      (inv_inv (Real.exp 2))
  exact le_trans hinverse (le_of_eq hnormalize)

theorem Real.inv_sq_smoothTransitionDenominator_le_exp_two_sq
    (x : ℝ) :
    (expNegInvGlue x + expNegInvGlue (1 - x))⁻¹ ^ 2 ≤
      (Real.exp 2) ^ 2 := by
  have hinverseNonneg : 0 ≤
      (expNegInvGlue x + expNegInvGlue (1 - x))⁻¹ :=
    inv_nonneg.mpr (Real.smoothTransitionDenominator_pos x).le
  have hproducts :
      (expNegInvGlue x + expNegInvGlue (1 - x))⁻¹ *
          (expNegInvGlue x + expNegInvGlue (1 - x))⁻¹ ≤
        Real.exp 2 * Real.exp 2 :=
    mul_self_le_mul_self hinverseNonneg
      (Real.inv_smoothTransitionDenominator_le_exp_two x)
  have hleftSquare :
      (expNegInvGlue x + expNegInvGlue (1 - x))⁻¹ ^ 2 =
        (expNegInvGlue x + expNegInvGlue (1 - x))⁻¹ *
          (expNegInvGlue x + expNegInvGlue (1 - x))⁻¹ :=
    pow_two _
  have hrightSquare :
      (Real.exp 2) ^ 2 = Real.exp 2 * Real.exp 2 :=
    pow_two _
  exact le_trans (le_of_eq hleftSquare)
    (le_trans hproducts (le_of_eq hrightSquare.symm))

theorem Real.inv_pow_four_smoothTransitionDenominator_le_exp_two_pow_four
    (x : ℝ) :
    (expNegInvGlue x + expNegInvGlue (1 - x))⁻¹ ^ 4 ≤
      (Real.exp 2) ^ 4 := by
  have hsquare :=
    Real.inv_sq_smoothTransitionDenominator_le_exp_two_sq x
  have hleftNonneg : 0 ≤
      (expNegInvGlue x + expNegInvGlue (1 - x))⁻¹ ^ 2 := sq_nonneg _
  have hrightNonneg : 0 ≤ (Real.exp 2) ^ 2 := sq_nonneg _
  have hmulProducts :
      (expNegInvGlue x + expNegInvGlue (1 - x))⁻¹ ^ 2 *
          (expNegInvGlue x + expNegInvGlue (1 - x))⁻¹ ^ 2 ≤
        (Real.exp 2) ^ 2 * (Real.exp 2) ^ 2 :=
    mul_self_le_mul_self hleftNonneg hsquare
  have hleftOuterSquare :
      ((expNegInvGlue x + expNegInvGlue (1 - x))⁻¹ ^ 2) ^ 2 =
        (expNegInvGlue x + expNegInvGlue (1 - x))⁻¹ ^ 2 *
          (expNegInvGlue x + expNegInvGlue (1 - x))⁻¹ ^ 2 :=
    pow_two _
  have hrightOuterSquare :
      ((Real.exp 2) ^ 2) ^ 2 =
        (Real.exp 2) ^ 2 * (Real.exp 2) ^ 2 :=
    pow_two _
  have hmulPowers :
      ((expNegInvGlue x + expNegInvGlue (1 - x))⁻¹ ^ 2) ^ 2 ≤
        ((Real.exp 2) ^ 2) ^ 2 :=
    le_trans (le_of_eq hleftOuterSquare)
      (le_trans hmulProducts (le_of_eq hrightOuterSquare.symm))
  have hleftPower :
      ((expNegInvGlue x + expNegInvGlue (1 - x))⁻¹ ^ 2) ^ 2 =
        (expNegInvGlue x + expNegInvGlue (1 - x))⁻¹ ^ 4 :=
    Eq.trans (pow_mul _ 2 2).symm rfl
  have hrightPower : ((Real.exp 2) ^ 2) ^ 2 = (Real.exp 2) ^ 4 :=
    Eq.trans (pow_mul _ 2 2).symm rfl
  exact le_trans (le_of_eq hleftPower.symm)
    (le_trans hmulPowers (le_of_eq hrightPower))

end
end LFunctions
end Boundary
