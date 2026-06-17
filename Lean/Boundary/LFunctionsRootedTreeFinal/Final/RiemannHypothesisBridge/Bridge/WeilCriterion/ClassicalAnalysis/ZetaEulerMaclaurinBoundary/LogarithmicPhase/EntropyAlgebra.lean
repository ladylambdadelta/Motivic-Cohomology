import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ClassicalAnalysis.ZetaEulerMaclaurinBoundary.LogarithmicPhase.CriticalAlgebra

/-!
# Entropy and scalar support algebra for logarithmic phase estimates

This file owns four-thirds entropy algebra, critical-expression expansion, and
small order lemmas used before the analytic logarithmic phase definitions.
-/

namespace Boundary
namespace LFunctions

noncomputable section

theorem real_rat_four_thirds_cast_for_logarithmicPhase :
    (((4 / 3 : ℚ) : ℝ)) = (4 / 3 : ℝ) := by
  calc
    (((4 / 3 : ℚ) : ℝ)) = ((4 : ℚ) : ℝ) / ((3 : ℚ) : ℝ) :=
      Rat.cast_div 4 3
    _ = (4 : ℝ) / ((3 : ℚ) : ℝ) := by
      exact congrArg (fun x : ℝ => x / ((3 : ℚ) : ℝ)) (Rat.cast_ofNat 4)
    _ = (4 : ℝ) / 3 := by
      exact congrArg (fun x : ℝ => (4 : ℝ) / x) (Rat.cast_ofNat 3)

theorem real_four_thirds_mul_two_eq_eight_thirds_for_logarithmicPhase :
    (4 / 3 : ℝ) * 2 = 8 / 3 := by
  have hq : (4 / 3 : ℚ) * 2 = 8 / 3 := by
    native_decide
  calc
    (4 / 3 : ℝ) * 2 =
        ((4 / 3 : ℚ) : ℝ) * ((2 : ℚ) : ℝ) := by
      exact congrArg₂ Mul.mul
        real_rat_four_thirds_cast_for_logarithmicPhase.symm
        (Rat.cast_ofNat 2).symm
    _ = (((4 / 3 : ℚ) * 2 : ℚ) : ℝ) :=
      (Rat.cast_mul (4 / 3 : ℚ) 2).symm
    _ = ((8 / 3 : ℚ) : ℝ) := by
      exact congrArg (fun q : ℚ => (q : ℝ)) hq
    _ = 8 / 3 :=
      real_rat_eight_thirds_cast_for_logarithmicPhase

theorem real_four_thirds_mul_two_for_logarithmicPhase
    (A : ℝ) :
    (4 / 3 : ℝ) * (2 * A) = (8 / 3 : ℝ) * A := by
  have hcoeff : (4 / 3 : ℝ) * 2 = 8 / 3 := by
    exact real_four_thirds_mul_two_eq_eight_thirds_for_logarithmicPhase
  calc
    (4 / 3 : ℝ) * (2 * A) = ((4 / 3 : ℝ) * 2) * A :=
      (mul_assoc (4 / 3 : ℝ) 2 A).symm
    _ = (8 / 3 : ℝ) * A := by
      exact congrArg (fun c : ℝ => c * A) hcoeff

theorem real_four_thirds_entropy_log_three_terms_for_logarithmicPhase
    (B : ℝ) :
    -((4 / 3 : ℝ) * B) - ((4 / 3 : ℝ) - 1) * (-B) = -B := by
  have hthird : ((4 / 3 : ℝ) - 1) = 1 / 3 :=
    real_four_div_three_sub_one_eq_one_div_three_for_logarithmicPhase
  have hcoeff :
      (4 / 3 : ℝ) - (1 / 3 : ℝ) = 1 := by
    calc
      (4 / 3 : ℝ) - (1 / 3 : ℝ) =
          (4 / 3 : ℝ) - ((4 / 3 : ℝ) - 1) := by
        exact congrArg (fun x : ℝ => (4 / 3 : ℝ) - x) hthird.symm
      _ = 1 :=
        sub_sub_self (4 / 3 : ℝ) 1
  calc
    -((4 / 3 : ℝ) * B) - ((4 / 3 : ℝ) - 1) * (-B) =
        -((4 / 3 : ℝ) * B) - (1 / 3 : ℝ) * (-B) := by
      exact congrArg
        (fun c : ℝ => -((4 / 3 : ℝ) * B) - c * (-B))
        hthird
    _ = -((4 / 3 : ℝ) * B) - -((1 / 3 : ℝ) * B) := by
      exact congrArg
        (fun z : ℝ => -((4 / 3 : ℝ) * B) - z)
        (mul_neg (1 / 3 : ℝ) B)
    _ = -((4 / 3 : ℝ) * B) + -(-((1 / 3 : ℝ) * B)) := by
      exact sub_eq_add_neg (-((4 / 3 : ℝ) * B)) (-((1 / 3 : ℝ) * B))
    _ = -((4 / 3 : ℝ) * B) + ((1 / 3 : ℝ) * B) := by
      exact congrArg
        (fun z : ℝ => -((4 / 3 : ℝ) * B) + z)
        (neg_neg ((1 / 3 : ℝ) * B))
    _ = ((1 / 3 : ℝ) * B) - ((4 / 3 : ℝ) * B) := by
      calc
        -((4 / 3 : ℝ) * B) + ((1 / 3 : ℝ) * B) =
            ((1 / 3 : ℝ) * B) + -((4 / 3 : ℝ) * B) := by
          exact add_comm (-((4 / 3 : ℝ) * B)) ((1 / 3 : ℝ) * B)
        _ = ((1 / 3 : ℝ) * B) - ((4 / 3 : ℝ) * B) := by
          exact (sub_eq_add_neg ((1 / 3 : ℝ) * B) ((4 / 3 : ℝ) * B)).symm
    _ = -(((4 / 3 : ℝ) * B) - ((1 / 3 : ℝ) * B)) := by
      exact (neg_sub ((4 / 3 : ℝ) * B) ((1 / 3 : ℝ) * B)).symm
    _ = -(((4 / 3 : ℝ) - (1 / 3 : ℝ)) * B) := by
      exact congrArg Neg.neg (sub_mul (4 / 3 : ℝ) (1 / 3 : ℝ) B).symm
    _ = -(1 * B) := by
      exact congrArg (fun c : ℝ => -(c * B)) hcoeff
    _ = -B := by
      exact congrArg Neg.neg (one_mul B)

theorem real_four_thirds_entropy_value_algebra_for_logarithmicPhase
    (A B : ℝ) :
    (4 / 3 : ℝ) * (2 * A - B) - ((4 / 3 : ℝ) - 1) * (-B) =
      (8 / 3 : ℝ) * A - B := by
  calc
    (4 / 3 : ℝ) * (2 * A - B) - ((4 / 3 : ℝ) - 1) * (-B) =
        ((4 / 3 : ℝ) * (2 * A) - (4 / 3 : ℝ) * B) -
          ((4 / 3 : ℝ) - 1) * (-B) := by
      exact congrArg
        (fun z : ℝ => z - ((4 / 3 : ℝ) - 1) * (-B))
        (mul_sub (4 / 3 : ℝ) (2 * A) B)
    _ = ((8 / 3 : ℝ) * A - (4 / 3 : ℝ) * B) -
          ((4 / 3 : ℝ) - 1) * (-B) := by
      exact congrArg
        (fun z : ℝ => (z - (4 / 3 : ℝ) * B) - ((4 / 3 : ℝ) - 1) * (-B))
        (real_four_thirds_mul_two_for_logarithmicPhase A)
    _ = (8 / 3 : ℝ) * A +
          (-((4 / 3 : ℝ) * B) - ((4 / 3 : ℝ) - 1) * (-B)) := by
      calc
        ((8 / 3 : ℝ) * A - (4 / 3 : ℝ) * B) -
            ((4 / 3 : ℝ) - 1) * (-B) =
            ((8 / 3 : ℝ) * A + -((4 / 3 : ℝ) * B)) -
              ((4 / 3 : ℝ) - 1) * (-B) := by
          exact congrArg
            (fun z : ℝ => z - ((4 / 3 : ℝ) - 1) * (-B))
            (sub_eq_add_neg ((8 / 3 : ℝ) * A) ((4 / 3 : ℝ) * B))
        _ = ((8 / 3 : ℝ) * A + -((4 / 3 : ℝ) * B)) +
              -(((4 / 3 : ℝ) - 1) * (-B)) := by
          exact sub_eq_add_neg
            ((8 / 3 : ℝ) * A + -((4 / 3 : ℝ) * B))
            (((4 / 3 : ℝ) - 1) * (-B))
        _ = (8 / 3 : ℝ) * A +
              (-((4 / 3 : ℝ) * B) + -(((4 / 3 : ℝ) - 1) * (-B))) := by
          exact add_assoc ((8 / 3 : ℝ) * A) (-((4 / 3 : ℝ) * B))
            (-(((4 / 3 : ℝ) - 1) * (-B)))
        _ = (8 / 3 : ℝ) * A +
              (-((4 / 3 : ℝ) * B) - ((4 / 3 : ℝ) - 1) * (-B)) := by
          exact congrArg
            (fun z : ℝ => (8 / 3 : ℝ) * A + z)
            (sub_eq_add_neg (-((4 / 3 : ℝ) * B)) (((4 / 3 : ℝ) - 1) * (-B))).symm
    _ = (8 / 3 : ℝ) * A + -B := by
      exact congrArg
        (fun z : ℝ => (8 / 3 : ℝ) * A + z)
        (real_four_thirds_entropy_log_three_terms_for_logarithmicPhase B)
    _ = (8 / 3 : ℝ) * A - B :=
      (sub_eq_add_neg ((8 / 3 : ℝ) * A) B).symm

theorem real_two_mul_sub_mul_reassociate_for_logarithmicPhase
    (A B L : ℝ) :
    (2 * (A - B)) * L = (2 * L) * A - (2 * L) * B := by
  calc
    (2 * (A - B)) * L = (2 * L) * (A - B) := by
      calc
        (2 * (A - B)) * L = 2 * ((A - B) * L) :=
          mul_assoc 2 (A - B) L
        _ = 2 * (L * (A - B)) := by
          exact congrArg (fun z : ℝ => 2 * z) (mul_comm (A - B) L)
        _ = (2 * L) * (A - B) := by
          exact (mul_assoc 2 L (A - B)).symm
    _ = (2 * L) * A - (2 * L) * B :=
      mul_sub (2 * L) A B

theorem real_critical_expression_expand_for_logarithmicPhase
    (A B L : ℝ) :
    (2 * (A - B)) * L - (L - B) =
      (2 * L) * A - ((2 * L) - 1) * B - L := by
  calc
    (2 * (A - B)) * L - (L - B) =
        ((2 * L) * A - (2 * L) * B) - (L - B) := by
      exact congrArg
        (fun z : ℝ => z - (L - B))
        (real_two_mul_sub_mul_reassociate_for_logarithmicPhase A B L)
    _ = ((2 * L) * A - (2 * L) * B) - L + B := by
      calc
        ((2 * L) * A - (2 * L) * B) - (L - B) =
            ((2 * L) * A - (2 * L) * B) - (L + -B) := by
          exact congrArg
            (fun z : ℝ => ((2 * L) * A - (2 * L) * B) - z)
            (sub_eq_add_neg L B)
        _ = ((2 * L) * A - (2 * L) * B) - L - -B := by
          exact sub_add_eq_sub_sub ((2 * L) * A - (2 * L) * B) L (-B)
        _ = ((2 * L) * A - (2 * L) * B) - L + -(-B) := by
          exact sub_eq_add_neg (((2 * L) * A - (2 * L) * B) - L) (-B)
        _ = ((2 * L) * A - (2 * L) * B) - L + B := by
          exact congrArg
            (fun z : ℝ => ((2 * L) * A - (2 * L) * B) - L + z)
            (neg_neg B)
    _ = ((2 * L) * A - L) - ((2 * L) * B - B) := by
      calc
        ((2 * L) * A - (2 * L) * B) - L + B =
            ((2 * L) * A - (2 * L) * B - L) + B := rfl
        _ = ((2 * L) * A - L - (2 * L) * B) + B := by
          exact congrArg (fun z : ℝ => z + B)
            (sub_right_comm ((2 * L) * A) ((2 * L) * B) L)
        _ = ((2 * L) * A - L) - (2 * L) * B + B := rfl
        _ = ((2 * L) * A - L) - ((2 * L) * B - B) := by
          calc
            ((2 * L) * A - L) - (2 * L) * B + B =
                ((2 * L) * A - L) - (2 * L) * B + -(-B) := by
              exact congrArg
                (fun z : ℝ => ((2 * L) * A - L) - (2 * L) * B + z)
                (neg_neg B).symm
            _ = ((2 * L) * A - L) - (2 * L) * B - -B := by
              exact (sub_eq_add_neg (((2 * L) * A - L) - (2 * L) * B) (-B)).symm
            _ = ((2 * L) * A - L) - ((2 * L) * B + -B) := by
              exact (sub_add_eq_sub_sub ((2 * L) * A - L) ((2 * L) * B) (-B)).symm
            _ = ((2 * L) * A - L) - ((2 * L) * B - B) := by
              exact congrArg
                (fun z : ℝ => ((2 * L) * A - L) - z)
                (sub_eq_add_neg ((2 * L) * B) B).symm
    _ = ((2 * L) * A - L) - ((2 * L - 1) * B) := by
      exact congrArg
        (fun z : ℝ => ((2 * L) * A - L) - z)
        (calc
          (2 * L) * B - B = (2 * L) * B - 1 * B := by
            exact congrArg (fun z : ℝ => (2 * L) * B - z) (one_mul B).symm
          _ = (2 * L - 1) * B := by
            exact (sub_mul (2 * L) 1 B).symm)
    _ = (2 * L) * A - ((2 * L) - 1) * B - L := by
      exact sub_right_comm ((2 * L) * A) L (((2 * L) - 1) * B)

theorem real_zero_lt_add_one_of_nonneg_for_logarithmicPhase {x : ℝ}
    (hx : 0 ≤ x) :
    0 < x + 1 := by
  have hone_le : (1 : ℝ) ≤ 1 + x :=
    le_add_of_nonneg_right hx
  have hone_le_commuted : (1 : ℝ) ≤ x + 1 :=
    Eq.subst
      (motive := fun y : ℝ => (1 : ℝ) ≤ y)
      (add_comm 1 x)
      hone_le
  exact lt_of_lt_of_le zero_lt_one hone_le_commuted

theorem real_zero_lt_add_two_of_nonneg_for_logarithmicPhase {x : ℝ}
    (hx : 0 ≤ x) :
    0 < x + 2 := by
  have htwo_le : (2 : ℝ) ≤ 2 + x :=
    le_add_of_nonneg_right hx
  have htwo_le_commuted : (2 : ℝ) ≤ x + 2 :=
    Eq.subst
      (motive := fun y : ℝ => (2 : ℝ) ≤ y)
      (add_comm 2 x)
      htwo_le
  exact lt_of_lt_of_le zero_lt_two htwo_le_commuted

theorem real_two_mul_inv_mul_two_inv_reassociate_for_logarithmicPhase
    (u : ℝ) :
    (2 : ℝ) * (u⁻¹ * (2 : ℝ)⁻¹) = ((2 : ℝ) * (2 : ℝ)⁻¹) * u⁻¹ := by
  calc
    (2 : ℝ) * (u⁻¹ * (2 : ℝ)⁻¹) =
        ((2 : ℝ) * u⁻¹) * (2 : ℝ)⁻¹ := by
      exact (mul_assoc (2 : ℝ) u⁻¹ (2 : ℝ)⁻¹).symm
    _ = (u⁻¹ * (2 : ℝ)) * (2 : ℝ)⁻¹ := by
      exact congrArg (fun y : ℝ => y * (2 : ℝ)⁻¹) (mul_comm (2 : ℝ) u⁻¹)
    _ = u⁻¹ * ((2 : ℝ) * (2 : ℝ)⁻¹) := by
      exact mul_assoc u⁻¹ (2 : ℝ) (2 : ℝ)⁻¹
    _ = ((2 : ℝ) * (2 : ℝ)⁻¹) * u⁻¹ := by
      exact mul_comm u⁻¹ ((2 : ℝ) * (2 : ℝ)⁻¹)

theorem real_sub_one_le_self_for_logarithmicPhase (y : ℝ) :
    y - 1 ≤ y :=
  sub_le_self y zero_le_one

theorem real_zero_le_one_div_two_for_logarithmicPhase : (0 : ℝ) ≤ 1 / 2 :=
  le_of_lt one_half_pos

theorem real_one_lt_four_div_three_for_logarithmicPhase : (1 : ℝ) < 4 / 3 := by
  exact (lt_div_iff₀' zero_lt_three).mpr
    (by
      calc
        (3 : ℝ) * 1 = 3 := mul_one 3
        _ < 3 + 1 := lt_add_of_pos_right 3 zero_lt_one
        _ = 4 := three_add_one_eq_four)

theorem real_sum_le_two_mul_self_of_nonneg_for_logarithmicPhase {x : ℝ}
    (hx : 0 ≤ x) :
    x ≤ 2 * x :=
  Eq.subst
    (motive := fun y : ℝ => y ≤ 2 * x)
    (one_mul x)
    (mul_le_mul_of_nonneg_right one_le_two hx)

end

end LFunctions
end Boundary
