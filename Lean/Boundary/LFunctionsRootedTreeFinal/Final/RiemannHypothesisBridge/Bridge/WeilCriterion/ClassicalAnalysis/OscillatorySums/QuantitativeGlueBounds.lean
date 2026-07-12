import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ClassicalAnalysis.OscillatorySums.QuantitativeTransitionMonotonicity

/-!
# Explicit weighted exponential bounds for the transition glue

The derivatives of `expNegInvGlue` are inverse powers multiplied by
`exp (-x⁻¹)`.  This file supplies elementary global bounds for those weighted
exponentials, starting from `y + 1 ≤ exp y`.
-/

namespace Boundary
namespace LFunctions

noncomputable section

theorem Real.nonneg_le_exp
    {y : ℝ}
    (hy : 0 ≤ y) :
    y ≤ Real.exp y := by
  have hyAdd : y ≤ y + 1 := le_add_of_nonneg_right zero_le_one
  exact le_trans hyAdd (Real.add_one_le_exp y)

theorem Real.exp_mul_exp_neg_eq_one
    (y : ℝ) :
    Real.exp y * Real.exp (-y) = 1 := by
  exact
    (Real.exp_add y (-y)).symm.trans
      ((congrArg Real.exp (add_neg_cancel y)).trans Real.exp_zero)

theorem Real.mul_exp_neg_le_one
    {y : ℝ}
    (hy : 0 ≤ y) :
    y * Real.exp (-y) ≤ 1 := by
  have hbase := Real.nonneg_le_exp hy
  have hexpNonneg : 0 ≤ Real.exp (-y) := (Real.exp_pos (-y)).le
  have hmul := mul_le_mul_of_nonneg_right hbase hexpNonneg
  exact le_trans hmul
    (le_of_eq (Real.exp_mul_exp_neg_eq_one y))

theorem Real.mul_exp_neg_nonneg
    {y : ℝ}
    (hy : 0 ≤ y) :
    0 ≤ y * Real.exp (-y) := by
  exact mul_nonneg hy (Real.exp_pos (-y)).le

theorem Real.half_nonneg
    {y : ℝ}
    (hy : 0 ≤ y) :
    0 ≤ y / 2 := by
  exact div_nonneg hy (Nat.cast_nonneg 2)

theorem Real.half_mul_exp_neg_half_le_one
    {y : ℝ}
    (hy : 0 ≤ y) :
    (y / 2) * Real.exp (-(y / 2)) ≤ 1 := by
  exact Real.mul_exp_neg_le_one (Real.half_nonneg hy)

theorem Real.sq_half_mul_exp_neg_half_le_one
    {y : ℝ}
    (hy : 0 ≤ y) :
    ((y / 2) * Real.exp (-(y / 2))) ^ 2 ≤ 1 := by
  have hnonneg := Real.mul_exp_neg_nonneg (Real.half_nonneg hy)
  have honeNonneg : (0 : ℝ) ≤ 1 := zero_le_one
  have hbase := Real.half_mul_exp_neg_half_le_one hy
  have hsquare := mul_self_le_mul_self hnonneg hbase
  exact le_trans
    (le_of_eq (pow_two ((y / 2) * Real.exp (-(y / 2)))).symm)
    (le_trans hsquare (le_of_eq (one_mul 1)))

theorem Real.neg_half_add_neg_half_eq_neg
    (y : ℝ) :
    -(y / 2) + -(y / 2) = -y := by
  have hhalf : y / 2 + y / 2 = y := by
    calc
      y / 2 + y / 2 = (y + y) / 2 := (add_div y y 2).symm
      _ = (2 * y) / 2 :=
        congrArg (fun value : ℝ => value / 2) (two_mul y).symm
      _ = y := by
        have htwo : (2 : ℝ) ≠ 0 :=
          ne_of_gt (Nat.cast_pos.mpr (Nat.succ_pos 1))
        exact mul_div_cancel_left₀ y htwo
  exact
    (neg_add (y / 2) (y / 2)).symm.trans
      (congrArg Neg.neg hhalf)

theorem Real.exp_neg_half_sq_eq_exp_neg
    (y : ℝ) :
    Real.exp (-(y / 2)) ^ 2 = Real.exp (-y) := by
  exact
    (pow_two (Real.exp (-(y / 2)))).trans
      ((Real.exp_add (-(y / 2)) (-(y / 2))).trans
        (congrArg Real.exp (Real.neg_half_add_neg_half_eq_neg y)))

theorem Real.half_sq_eq_quarter_mul_sq
    (y : ℝ) :
    (y / 2) ^ 2 = (1 / 4 : ℝ) * y ^ 2 := by
  have hdivPow : (y / 2) ^ 2 = y ^ 2 / 2 ^ 2 := div_pow y 2 2
  have htwoSq : (2 : ℝ) ^ 2 = 4 := by
    exact (pow_two (2 : ℝ)).trans
      (show (2 : ℝ) * 2 = 4 from rfl)
  have hdivision : y ^ 2 / 4 = (1 / 4 : ℝ) * y ^ 2 := by
    exact
      (div_eq_mul_inv (y ^ 2) 4).trans
        (mul_comm (y ^ 2) 4⁻¹).trans
        (congrArg (fun value : ℝ => value * y ^ 2) (one_div 4).symm)
  exact hdivPow.trans
    ((congrArg (fun value : ℝ => y ^ 2 / value) htwoSq).trans hdivision)

theorem Real.sq_mul_exp_neg_le_four
    {y : ℝ}
    (hy : 0 ≤ y) :
    y ^ 2 * Real.exp (-y) ≤ 4 := by
  have hsquare := Real.sq_half_mul_exp_neg_half_le_one hy
  have hproductSquare :
      ((y / 2) * Real.exp (-(y / 2))) ^ 2 =
        (y / 2) ^ 2 * Real.exp (-(y / 2)) ^ 2 :=
    mul_pow (y / 2) (Real.exp (-(y / 2))) 2
  have hnormalized :
      ((y / 2) * Real.exp (-(y / 2))) ^ 2 =
        (1 / 4 : ℝ) * (y ^ 2 * Real.exp (-y)) := by
    exact hproductSquare.trans
      ((congrArg₂ (fun first second : ℝ => first * second)
        (Real.half_sq_eq_quarter_mul_sq y)
        (Real.exp_neg_half_sq_eq_exp_neg y)).trans
        (mul_assoc (1 / 4 : ℝ) (y ^ 2) (Real.exp (-y))))
  have hquarter :
      (1 / 4 : ℝ) * (y ^ 2 * Real.exp (-y)) ≤ 1 :=
    le_trans (le_of_eq hnormalized.symm) hsquare
  have hfourPos : (0 : ℝ) < 4 :=
    Nat.cast_pos.mpr (Nat.succ_pos 3)
  have hscaled := mul_le_mul_of_nonneg_left hquarter hfourPos.le
  have hleft :
      4 * ((1 / 4 : ℝ) * (y ^ 2 * Real.exp (-y))) =
        y ^ 2 * Real.exp (-y) := by
    have hfourNe : (4 : ℝ) ≠ 0 := ne_of_gt hfourPos
    have hcancel : (4 : ℝ) * (1 / 4) = 1 := by
      exact
        (congrArg (fun value : ℝ => 4 * value) (one_div 4)).trans
          (mul_inv_cancel₀ hfourNe)
    exact
      (mul_assoc (4 : ℝ) (1 / 4) (y ^ 2 * Real.exp (-y))).symm.trans
        ((congrArg
          (fun value : ℝ => value * (y ^ 2 * Real.exp (-y))) hcancel).trans
          (one_mul _))
  have hright : (4 : ℝ) * 1 = 4 := mul_one 4
  exact le_trans (le_of_eq hleft.symm)
    (le_trans hscaled (le_of_eq hright))

theorem Real.inv_sq_mul_exp_neg_inv_le_four
    {x : ℝ}
    (hx : 0 < x) :
    x⁻¹ ^ 2 * Real.exp (-x⁻¹) ≤ 4 := by
  exact Real.sq_mul_exp_neg_le_four (inv_nonneg.mpr hx.le)

theorem Real.expNegInvGlueDerivative_le_four
    {x : ℝ}
    (hx : 0 < x) :
    Real.expNegInvGlueDerivative x ≤ 4 := by
  have hglue : expNegInvGlue x = Real.exp (-x⁻¹) := by
    unfold expNegInvGlue
    exact if_neg (not_le.mpr hx)
  exact
    Eq.subst
      (motive := fun value : ℝ =>
        Real.expNegInvGlueDerivative x ≤ value)
      rfl
      (le_trans
        (le_of_eq
          ((Real.expNegInvGlueDerivative_eq_inv_sq_mul x).trans
            (congrArg (fun value : ℝ => x⁻¹ ^ 2 * value) hglue)))
        (Real.inv_sq_mul_exp_neg_inv_le_four hx))

theorem Real.quarter_nonneg
    {y : ℝ}
    (hy : 0 ≤ y) :
    0 ≤ y / 4 := by
  exact div_nonneg hy (Nat.cast_nonneg 4)

theorem Real.quarter_sq_mul_exp_neg_quarter_le_four
    {y : ℝ}
    (hy : 0 ≤ y) :
    (y / 4) ^ 2 * Real.exp (-(y / 4)) ≤ 4 := by
  exact Real.sq_mul_exp_neg_le_four (Real.quarter_nonneg hy)

theorem Real.quarter_sq_mul_exp_neg_quarter_nonneg
    {y : ℝ}
    (hy : 0 ≤ y) :
    0 ≤ (y / 4) ^ 2 * Real.exp (-(y / 4)) := by
  exact mul_nonneg (sq_nonneg _) (Real.exp_pos _).le

theorem Real.quarter_sq_exp_square_le_sixteen
    {y : ℝ}
    (hy : 0 ≤ y) :
    ((y / 4) ^ 2 * Real.exp (-(y / 4))) ^ 2 ≤ 16 := by
  have hnonneg := Real.quarter_sq_mul_exp_neg_quarter_nonneg hy
  have hbound := Real.quarter_sq_mul_exp_neg_quarter_le_four hy
  have hsquare := mul_self_le_mul_self hnonneg hbound
  have hleft :
      ((y / 4) ^ 2 * Real.exp (-(y / 4))) ^ 2 =
        ((y / 4) ^ 2 * Real.exp (-(y / 4))) *
          ((y / 4) ^ 2 * Real.exp (-(y / 4))) :=
    pow_two _
  have hright : (4 : ℝ) * 4 = 16 := rfl
  exact le_trans (le_of_eq hleft) (le_trans hsquare (le_of_eq hright))

theorem Real.neg_quarter_add_neg_quarter_eq_neg_half
    (y : ℝ) :
    -(y / 4) + -(y / 4) = -(y / 2) := by
  have hquarter : y / 4 + y / 4 = y / 2 := by
    calc
      y / 4 + y / 4 = (y + y) / 4 := (add_div y y 4).symm
      _ = (2 * y) / 4 :=
        congrArg (fun value : ℝ => value / 4) (two_mul y).symm
      _ = y / 2 := by
        have htwoNe : (2 : ℝ) ≠ 0 :=
          ne_of_gt (Nat.cast_pos.mpr (Nat.succ_pos 1))
        have hfour : (4 : ℝ) = 2 * 2 := rfl
        calc
          (2 * y) / 4 = (2 * y) / (2 * 2) :=
            congrArg (fun value : ℝ => (2 * y) / value) hfour.symm
          _ = y / 2 := div_mul_div_cancel_left₀ y 2 htwoNe
  exact
    (neg_add (y / 4) (y / 4)).symm.trans
      (congrArg Neg.neg hquarter)

theorem Real.exp_neg_quarter_sq_eq_exp_neg_half
    (y : ℝ) :
    Real.exp (-(y / 4)) ^ 2 = Real.exp (-(y / 2)) := by
  exact
    (pow_two (Real.exp (-(y / 4)))).trans
      ((Real.exp_add (-(y / 4)) (-(y / 4))).trans
        (congrArg Real.exp
          (Real.neg_quarter_add_neg_quarter_eq_neg_half y)))

theorem Real.quarter_pow_four_eq_inv_256_mul_pow_four
    (y : ℝ) :
    (y / 4) ^ 4 = (1 / 256 : ℝ) * y ^ 4 := by
  have hdivPow : (y / 4) ^ 4 = y ^ 4 / 4 ^ 4 := div_pow y 4 4
  have hfourPow : (4 : ℝ) ^ 4 = 256 := by
    calc
      (4 : ℝ) ^ 4 = 4 * 4 * 4 * 4 := rfl
      _ = 256 := rfl
  have hdivision : y ^ 4 / 256 = (1 / 256 : ℝ) * y ^ 4 := by
    exact
      (div_eq_mul_inv (y ^ 4) 256).trans
        ((mul_comm (y ^ 4) 256⁻¹).trans
          (congrArg (fun value : ℝ => value * y ^ 4) (one_div 256).symm))
  exact hdivPow.trans
    ((congrArg (fun value : ℝ => y ^ 4 / value) hfourPow).trans hdivision)

theorem Real.pow_four_mul_exp_neg_le_two_fifty_six
    {y : ℝ}
    (hy : 0 ≤ y) :
    y ^ 4 * Real.exp (-y) ≤ 256 := by
  have hbase := Real.sq_mul_exp_neg_le_four (Real.half_nonneg hy)
  have hbaseNonneg :
      0 ≤ (y / 2) ^ 2 * Real.exp (-(y / 2)) :=
    mul_nonneg (sq_nonneg _) (Real.exp_pos _).le
  have hsquare := mul_self_le_mul_self hbaseNonneg hbase
  have hright : (4 : ℝ) * 4 = 16 := rfl
  have hsquareBound :
      ((y / 2) ^ 2 * Real.exp (-(y / 2))) ^ 2 ≤ 16 :=
    le_trans
      (le_of_eq (pow_two ((y / 2) ^ 2 * Real.exp (-(y / 2)))))
      (le_trans hsquare (le_of_eq hright))
  have hhalfPowFour :
      (y / 2) ^ 4 = (1 / 16 : ℝ) * y ^ 4 := by
    have hdivPow : (y / 2) ^ 4 = y ^ 4 / 2 ^ 4 := div_pow y 2 4
    have htwoPow : (2 : ℝ) ^ 4 = 16 := rfl
    exact hdivPow.trans
      ((congrArg (fun value : ℝ => y ^ 4 / value) htwoPow).trans
        ((div_eq_mul_inv (y ^ 4) 16).trans
          ((mul_comm (y ^ 4) 16⁻¹).trans
            (congrArg (fun value : ℝ => value * y ^ 4) (one_div 16).symm))))
  have hnormalized :
      ((y / 2) ^ 2 * Real.exp (-(y / 2))) ^ 2 =
        (1 / 16 : ℝ) * (y ^ 4 * Real.exp (-y)) := by
    have hmulPow := mul_pow
      ((y / 2) ^ 2) (Real.exp (-(y / 2))) 2
    have hpowPower : ((y / 2) ^ 2) ^ 2 = (y / 2) ^ 4 :=
      (pow_mul (y / 2) 2 2).trans rfl
    exact hmulPow.trans
      ((congrArg₂ (fun first second : ℝ => first * second)
        hpowPower (Real.exp_neg_half_sq_eq_exp_neg y)).trans
        ((congrArg
          (fun value : ℝ => value * Real.exp (-y)) hhalfPowFour).trans
          (mul_assoc (1 / 16 : ℝ) (y ^ 4) (Real.exp (-y))))
  have hquarter :
      (1 / 16 : ℝ) * (y ^ 4 * Real.exp (-y)) ≤ 16 :=
    le_trans (le_of_eq hnormalized.symm) hsquareBound
  have hsixteenPos : (0 : ℝ) < 16 :=
    Nat.cast_pos.mpr (Nat.succ_pos 15)
  have hscaled := mul_le_mul_of_nonneg_left hquarter hsixteenPos.le
  have hcancel :
      16 * ((1 / 16 : ℝ) * (y ^ 4 * Real.exp (-y))) =
        y ^ 4 * Real.exp (-y) := by
    have hsixteenNe : (16 : ℝ) ≠ 0 := ne_of_gt hsixteenPos
    have hunit : (16 : ℝ) * (1 / 16) = 1 :=
      (congrArg (fun value : ℝ => 16 * value) (one_div 16)).trans
        (mul_inv_cancel₀ hsixteenNe)
    exact
      (mul_assoc (16 : ℝ) (1 / 16) (y ^ 4 * Real.exp (-y))).symm.trans
        ((congrArg
          (fun value : ℝ => value * (y ^ 4 * Real.exp (-y))) hunit).trans
          (one_mul _))
  have hrightScaled : (16 : ℝ) * 16 = 256 := rfl
  exact le_trans (le_of_eq hcancel.symm)
    (le_trans hscaled (le_of_eq hrightScaled))

end
end LFunctions
end Boundary
