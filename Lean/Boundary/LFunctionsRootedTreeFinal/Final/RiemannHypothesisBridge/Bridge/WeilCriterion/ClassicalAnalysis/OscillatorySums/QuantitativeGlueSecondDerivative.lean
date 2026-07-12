import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ClassicalAnalysis.OscillatorySums.QuantitativeGlueBounds

/-!
# Second derivative bound for the transition glue

On the positive half-line the glue is `exp (-x⁻¹)`.  Its second derivative is
`(x⁻⁴ - 2x⁻³) exp (-x⁻¹)`.  Weighted exponential bounds give a uniform
absolute estimate.
-/

namespace Boundary
namespace LFunctions

noncomputable section

def Real.expNegInvGlueSecondDerivative
    (x : ℝ) : ℝ :=
  (x⁻¹ ^ 4 - 2 * x⁻¹ ^ 3) * expNegInvGlue x

theorem Real.hasDerivAt_inv_sq
    {x : ℝ}
    (hx : 0 < x) :
    HasDerivAt (fun y : ℝ => y⁻¹ ^ 2) (-2 * x⁻¹ ^ 3) x := by
  have hinverse := (hasDerivAt_id x).inv hx.ne'
  have hsquare := hinverse.pow 2
  have hraw :
      (2 : ℕ) * x⁻¹ ^ (2 - 1) * (-x⁻¹ ^ 2) =
        -2 * x⁻¹ ^ 3 := by
    have hindex : (2 - 1 : ℕ) = 1 := rfl
    calc
      (2 : ℕ) * x⁻¹ ^ (2 - 1) * (-x⁻¹ ^ 2) =
        (2 : ℝ) * x⁻¹ ^ 1 * (-x⁻¹ ^ 2) := rfl
      _ = 2 * x⁻¹ * (-x⁻¹ ^ 2) :=
        congrArg (fun value : ℝ => 2 * value * (-x⁻¹ ^ 2))
          (pow_one x⁻¹)
      _ = -(2 * x⁻¹ * x⁻¹ ^ 2) :=
        mul_neg (2 * x⁻¹) (x⁻¹ ^ 2)
      _ = -(2 * (x⁻¹ * x⁻¹ ^ 2)) :=
        congrArg Neg.neg (mul_assoc 2 x⁻¹ (x⁻¹ ^ 2))
      _ = -(2 * x⁻¹ ^ 3) := by
        have hpower : x⁻¹ * x⁻¹ ^ 2 = x⁻¹ ^ 3 := by
          exact (pow_succ x⁻¹ 2).symm.trans
            (congrArg (fun value : ℝ => value * x⁻¹) (pow_two x⁻¹)).trans
            (mul_assoc x⁻¹ x⁻¹ x⁻¹).symm.trans
            (pow_succ x⁻¹ 2)
        exact congrArg (fun value : ℝ => -(2 * value)) hpower
      _ = -2 * x⁻¹ ^ 3 := neg_mul 2 (x⁻¹ ^ 3)
  exact Eq.subst
    (motive := fun value : ℝ =>
      HasDerivAt (fun y : ℝ => y⁻¹ ^ 2) value x)
    hraw hsquare

theorem Real.hasDerivAt_expNegInvGlueDerivative_positive
    {x : ℝ}
    (hx : 0 < x) :
    HasDerivAt
      Real.expNegInvGlueDerivative
      (Real.expNegInvGlueSecondDerivative x)
      x := by
  have hcoefficient := Real.hasDerivAt_inv_sq hx
  have hglue := Real.hasDerivAt_expNegInvGlue_exact x
  have hproduct := hcoefficient.mul hglue
  have hfunction :
      (fun y : ℝ => y⁻¹ ^ 2 * expNegInvGlue y) =
        Real.expNegInvGlueDerivative := by
    funext y
    exact (Real.expNegInvGlueDerivative_eq_inv_sq_mul y).symm
  have hvalue :
      (-2 * x⁻¹ ^ 3) * expNegInvGlue x +
          x⁻¹ ^ 2 * Real.expNegInvGlueDerivative x =
        Real.expNegInvGlueSecondDerivative x := by
    unfold Real.expNegInvGlueSecondDerivative
    have hderivative := Real.expNegInvGlueDerivative_eq_inv_sq_mul x
    calc
      (-2 * x⁻¹ ^ 3) * expNegInvGlue x +
          x⁻¹ ^ 2 * Real.expNegInvGlueDerivative x =
        (-2 * x⁻¹ ^ 3) * expNegInvGlue x +
          x⁻¹ ^ 2 * (x⁻¹ ^ 2 * expNegInvGlue x) :=
        congrArg
          (fun value : ℝ =>
            (-2 * x⁻¹ ^ 3) * expNegInvGlue x + x⁻¹ ^ 2 * value)
          hderivative
      _ = (-2 * x⁻¹ ^ 3) * expNegInvGlue x +
          (x⁻¹ ^ 2 * x⁻¹ ^ 2) * expNegInvGlue x :=
        congrArg
          (fun value : ℝ =>
            (-2 * x⁻¹ ^ 3) * expNegInvGlue x + value)
          (mul_assoc (x⁻¹ ^ 2) (x⁻¹ ^ 2) (expNegInvGlue x)).symm
      _ = (-2 * x⁻¹ ^ 3) * expNegInvGlue x +
          x⁻¹ ^ 4 * expNegInvGlue x := by
        exact congrArg
          (fun value : ℝ =>
            (-2 * x⁻¹ ^ 3) * expNegInvGlue x + value * expNegInvGlue x)
          (Eq.trans (mul_pow x⁻¹ x⁻¹ 2).symm rfl)
      _ = x⁻¹ ^ 4 * expNegInvGlue x +
          (-2 * x⁻¹ ^ 3) * expNegInvGlue x := add_comm _ _
      _ = (x⁻¹ ^ 4 + (-2 * x⁻¹ ^ 3)) * expNegInvGlue x :=
        (add_mul (x⁻¹ ^ 4) (-2 * x⁻¹ ^ 3) (expNegInvGlue x)).symm
      _ = (x⁻¹ ^ 4 - 2 * x⁻¹ ^ 3) * expNegInvGlue x :=
        congrArg (fun value : ℝ => value * expNegInvGlue x)
          (sub_eq_add_neg (x⁻¹ ^ 4) (2 * x⁻¹ ^ 3)).symm
  exact Eq.subst
    (motive := fun function : ℝ → ℝ =>
      HasDerivAt function (Real.expNegInvGlueSecondDerivative x) x)
    hfunction
    (Eq.subst
      (motive := fun value : ℝ =>
        HasDerivAt
          (fun y : ℝ => y⁻¹ ^ 2 * expNegInvGlue y) value x)
      hvalue hproduct)

theorem Real.cube_mul_exp_neg_le_two_fifty_six
    {y : ℝ}
    (hy : 0 ≤ y) :
    y ^ 3 * Real.exp (-y) ≤ 256 := by
  match le_total y 1 with
  | Or.inl hyOne =>
      have hcubeSquare : y ^ 3 ≤ y ^ 2 := by
        have hySquare : 0 ≤ y ^ 2 := sq_nonneg y
        have hmul := mul_le_mul_of_nonneg_left hyOne hySquare
        have hleft : y ^ 2 * y = y ^ 3 := (pow_succ y 2).symm
        have hright : y ^ 2 * 1 = y ^ 2 := mul_one _
        exact le_trans (le_of_eq hleft.symm)
          (le_trans hmul (le_of_eq hright))
      have hexpNonneg : 0 ≤ Real.exp (-y) := (Real.exp_pos (-y)).le
      have hweighted := mul_le_mul_of_nonneg_right hcubeSquare hexpNonneg
      exact le_trans hweighted
        (le_trans (Real.sq_mul_exp_neg_le_four hy)
          (by exact_mod_cast (show (4 : ℕ) ≤ 256 by decide)))
  | Or.inr honeY =>
      have hcubeFourth : y ^ 3 ≤ y ^ 4 := by
        have hcubeNonneg : 0 ≤ y ^ 3 := pow_nonneg hy 3
        have hmul := mul_le_mul_of_nonneg_left honeY hcubeNonneg
        have hleft : y ^ 3 * 1 = y ^ 3 := mul_one _
        have hright : y ^ 3 * y = y ^ 4 := (pow_succ y 3).symm
        exact le_trans (le_of_eq hleft.symm)
          (le_trans hmul (le_of_eq hright))
      have hexpNonneg : 0 ≤ Real.exp (-y) := (Real.exp_pos (-y)).le
      exact le_trans
        (mul_le_mul_of_nonneg_right hcubeFourth hexpNonneg)
        (Real.pow_four_mul_exp_neg_le_two_fifty_six hy)

theorem Real.abs_expNegInvGlueSecondDerivative_le_seven_sixty_eight
    {x : ℝ}
    (hx : 0 < x) :
    |Real.expNegInvGlueSecondDerivative x| ≤ 768 := by
  unfold Real.expNegInvGlueSecondDerivative
  have hglue : expNegInvGlue x = Real.exp (-x⁻¹) := by
    unfold expNegInvGlue
    exact if_neg (not_le.mpr hx)
  have hy : 0 ≤ x⁻¹ := inv_nonneg.mpr hx.le
  have htriangle :
      |(x⁻¹ ^ 4 - 2 * x⁻¹ ^ 3) * expNegInvGlue x| ≤
        x⁻¹ ^ 4 * Real.exp (-x⁻¹) +
          2 * (x⁻¹ ^ 3 * Real.exp (-x⁻¹)) := by
    have hproduct := abs_mul
      (x⁻¹ ^ 4 - 2 * x⁻¹ ^ 3) (expNegInvGlue x)
    have hglueAbs : |expNegInvGlue x| = Real.exp (-x⁻¹) :=
      (congrArg abs hglue).trans
        (abs_of_pos (Real.exp_pos (-x⁻¹)))
    have hdifference := abs_sub (x⁻¹ ^ 4) (2 * x⁻¹ ^ 3)
    have hfirstAbs : |x⁻¹ ^ 4| = x⁻¹ ^ 4 :=
      abs_of_nonneg (pow_nonneg hy 4)
    have hsecondAbs : |2 * x⁻¹ ^ 3| = 2 * x⁻¹ ^ 3 :=
      abs_of_nonneg (mul_nonneg (Nat.cast_nonneg 2) (pow_nonneg hy 3))
    have hfactorNonneg : 0 ≤ Real.exp (-x⁻¹) := (Real.exp_pos _).le
    have hmul := mul_le_mul_of_nonneg_right
      (le_trans hdifference
        (le_of_eq (congrArg₂ (fun first second : ℝ => first + second)
          hfirstAbs hsecondAbs)))
      hfactorNonneg
    exact le_trans (le_of_eq
      (hproduct.trans
        (congrArg₂ (fun first second : ℝ => first * second) rfl hglueAbs)))
      (le_trans hmul
        (le_of_eq
          ((add_mul (x⁻¹ ^ 4) (2 * x⁻¹ ^ 3) (Real.exp (-x⁻¹))).trans
            (congrArg
              (fun value : ℝ =>
                x⁻¹ ^ 4 * Real.exp (-x⁻¹) + value)
              (mul_assoc 2 (x⁻¹ ^ 3) (Real.exp (-x⁻¹))))))))
  have hfourth := Real.pow_four_mul_exp_neg_le_two_fifty_six hy
  have hthird := Real.cube_mul_exp_neg_le_two_fifty_six hy
  have htwice := mul_le_mul_of_nonneg_left hthird (Nat.cast_nonneg 2)
  have hsum := add_le_add hfourth htwice
  have hvalue : (256 : ℝ) + 2 * 256 = 768 := rfl
  exact le_trans htriangle (le_trans hsum (le_of_eq hvalue))

end
end LFunctions
end Boundary
