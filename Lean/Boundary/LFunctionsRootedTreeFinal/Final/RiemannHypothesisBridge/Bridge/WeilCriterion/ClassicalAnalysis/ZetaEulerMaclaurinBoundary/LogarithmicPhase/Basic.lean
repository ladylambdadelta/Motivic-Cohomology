import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ClassicalAnalysis.ZetaEulerMaclaurinBoundary.BoundaryLine
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Angle
import Mathlib.Data.Complex.ExponentialBounds
import Mathlib.Data.Rat.Cast.Order

/-!
# Elementary support for logarithmic phase estimates

This file owns the low-level arithmetic and cast lemmas used by the
logarithmic phase estimates.
-/

namespace Boundary
namespace LFunctions

noncomputable section

theorem real_zero_le_four_for_logarithmicPhase : (0 : ℝ) ≤ 4 :=
  le_of_lt zero_lt_four

theorem real_two_le_four_for_logarithmicPhase : (2 : ℝ) ≤ 4 :=
  calc
    (2 : ℝ) = 2 + 0 := (add_zero 2).symm
    _ ≤ 2 + 2 := add_le_add_left zero_le_two 2
    _ = 4 := two_add_two_eq_four

theorem real_one_le_four_mul_one_for_logarithmicPhase : (1 : ℝ) ≤ 4 * 1 := by
  calc
    (1 : ℝ) ≤ 4 := le_trans one_le_two real_two_le_four_for_logarithmicPhase
    _ = 4 * 1 := (mul_one 4).symm

theorem real_div_two_pos_of_pos_for_logarithmicPhase {lam : ℝ}
    (hlam_pos : 0 < lam) :
    0 < lam / 2 :=
  div_pos hlam_pos zero_lt_two

theorem real_div_two_le_of_le_mul_two_for_logarithmicPhase {lam x : ℝ}
    (_hlam_pos : 0 < lam)
    (hden : lam ≤ x * 2) :
    lam / 2 ≤ x :=
  (div_le_iff₀' zero_lt_two).mpr
    (Eq.subst (motive := fun r : ℝ => lam ≤ r) (mul_comm x 2) hden)

theorem real_inv_div_two_eq_two_mul_inv_for_logarithmicPhase {lam : ℝ} :
    (lam / 2)⁻¹ = 2 * lam⁻¹ := by
  calc
    (lam / 2)⁻¹ = 2 / lam := inv_div lam 2
    _ = 2 * lam⁻¹ := div_eq_mul_inv 2 lam

theorem real_pi_div_two_le_two_for_logarithmicPhase : Real.pi / 2 ≤ (2 : ℝ) := by
  exact (div_le_iff₀' zero_lt_two).mpr
    (by
      calc
        Real.pi ≤ (4 : ℝ) :=
          Real.pi_le_four
        _ = 2 * 2 := by
          exact ((two_mul (2 : ℝ)).trans two_add_two_eq_four).symm)

theorem real_four_eq_two_sq_for_logarithmicPhase : (4 : ℝ) = (2 : ℝ) ^ 2 := by
  calc
    (4 : ℝ) = 2 * 2 := ((two_mul (2 : ℝ)).trans two_add_two_eq_four).symm
    _ = (2 : ℝ) ^ 2 := (pow_two (2 : ℝ)).symm

theorem real_exp_two_eq_exp_nat_two_mul_one_for_logarithmicPhase :
    Real.exp (2 : ℝ) = Real.exp ((2 : ℕ) * (1 : ℝ)) :=
  congrArg Real.exp (mul_one (2 : ℝ)).symm

theorem real_decimal_exp_upper_lt_four_for_logarithmicPhase :
    (2.7182818286 : ℝ) < 4 := by
  have hq : (OfScientific.ofScientific 27182818286 true 10 : ℚ) < (4 : ℚ) := by
    native_decide
  exact Eq.subst
    (motive := fun x : ℝ => x < 4)
    (Rat.cast_ofScientific (K := ℝ) 27182818286 true 10)
    (Rat.cast_lt.mpr hq)

theorem real_two_lt_decimal_exp_lower_for_logarithmicPhase :
    (2 : ℝ) < 2.7182818283 := by
  have hq : (2 : ℚ) < (OfScientific.ofScientific 27182818283 true 10 : ℚ) := by
    native_decide
  exact Eq.subst
    (motive := fun x : ℝ => (2 : ℝ) < x)
    (Rat.cast_ofScientific (K := ℝ) 27182818283 true 10)
    (Rat.cast_lt.mpr hq)

theorem real_decimal_exp_upper_sq_lt_eight_for_logarithmicPhase :
    (2.7182818286 : ℝ) ^ 2 < 8 := by
  let q : ℚ := OfScientific.ofScientific 27182818286 true 10
  have hq : q ^ 2 < (8 : ℚ) := by
    native_decide
  have hcast : (OfScientific.ofScientific 27182818286 true 10 : ℝ) = (q : ℝ) := by
    exact (Rat.cast_ofScientific (K := ℝ) 27182818286 true 10).symm
  have hsq_cast : (2.7182818286 : ℝ) ^ 2 = ((q ^ 2 : ℚ) : ℝ) := by
    calc
      (2.7182818286 : ℝ) ^ 2 =
          (OfScientific.ofScientific 27182818286 true 10 : ℝ) ^ 2 := by
        rfl
      _ = (q : ℝ) ^ 2 := by
        exact congrArg (fun x : ℝ => x ^ 2) hcast
      _ = (q : ℝ) * (q : ℝ) := pow_two (q : ℝ)
      _ = ((q * q : ℚ) : ℝ) := (Rat.cast_mul q q).symm
      _ = ((q ^ 2 : ℚ) : ℝ) := by
        exact congrArg (fun r : ℚ => (r : ℝ)) (pow_two q).symm
  exact Eq.subst
    (motive := fun x : ℝ => x < 8)
    hsq_cast.symm
    (Rat.cast_lt.mpr hq)

theorem real_zero_lt_eight_for_logarithmicPhase : (0 : ℝ) < 8 := by
  exact lt_trans zero_lt_four
    (by
      calc
        (4 : ℝ) = 4 + 0 := (add_zero 4).symm
        _ < 4 + 4 := add_lt_add_left zero_lt_four 4
        _ = 8 := by
          exact (Nat.cast_add 4 4).symm.trans
            (congrArg (fun n : ℕ => (n : ℝ))
              (show (4 : ℕ) + 4 = 8 by native_decide)))

theorem real_eight_eq_two_pow_three_for_logarithmicPhase :
    (8 : ℝ) = (2 : ℝ) ^ 3 := by
  calc
    (8 : ℝ) = (((8 : ℕ) : ℝ)) := rfl
    _ = (((2 : ℕ) ^ 3 : ℕ) : ℝ) := by
      exact congrArg (fun n : ℕ => (n : ℝ))
        (show (8 : ℕ) = 2 ^ 3 by native_decide)
    _ = (2 : ℝ) ^ 3 :=
      Nat.cast_pow (α := ℝ) 2 3

theorem real_zero_lt_twenty_seven_for_logarithmicPhase : (0 : ℝ) < 27 := by
  exact Nat.cast_pos.mpr (show (0 : ℕ) < 27 by native_decide)

theorem real_twenty_seven_le_thirty_two_for_logarithmicPhase : (27 : ℝ) ≤ 32 := by
  exact Nat.cast_le.mpr (show (27 : ℕ) ≤ 32 by native_decide)

theorem real_twenty_seven_eq_three_pow_three_for_logarithmicPhase :
    (27 : ℝ) = (3 : ℝ) ^ 3 := by
  calc
    (27 : ℝ) = (((27 : ℕ) : ℝ)) := rfl
    _ = (((3 : ℕ) ^ 3 : ℕ) : ℝ) := by
      exact congrArg (fun n : ℕ => (n : ℝ))
        (show (27 : ℕ) = 3 ^ 3 by native_decide)
    _ = (3 : ℝ) ^ 3 :=
      Nat.cast_pow (α := ℝ) 3 3

theorem real_thirty_two_eq_two_pow_five_for_logarithmicPhase :
    (32 : ℝ) = (2 : ℝ) ^ 5 := by
  calc
    (32 : ℝ) = (((32 : ℕ) : ℝ)) := rfl
    _ = (((2 : ℕ) ^ 5 : ℕ) : ℝ) := by
      exact congrArg (fun n : ℕ => (n : ℝ))
        (show (32 : ℕ) = 2 ^ 5 by native_decide)
    _ = (2 : ℝ) ^ 5 :=
      Nat.cast_pow (α := ℝ) 2 5

theorem real_four_div_three_pos_for_logarithmicPhase : (0 : ℝ) < 4 / 3 :=
  div_pos zero_lt_four zero_lt_three

theorem real_four_div_three_ne_zero_for_logarithmicPhase :
    (4 / 3 : ℝ) ≠ 0 :=
  ne_of_gt real_four_div_three_pos_for_logarithmicPhase

theorem real_four_div_three_sub_one_eq_one_div_three_for_logarithmicPhase :
    (4 / 3 : ℝ) - 1 = 1 / 3 := by
  calc
    (4 / 3 : ℝ) - 1 = (4 - 3 : ℝ) / 3 := by
      exact div_sub_one (show (3 : ℝ) ≠ 0 from ne_of_gt zero_lt_three)
    _ = 1 / 3 := by
      have hnat : ((4 - 3 : ℕ) : ℝ) = 1 := by
        calc
          ((4 - 3 : ℕ) : ℝ) = ((1 : ℕ) : ℝ) := by
            exact congrArg (fun n : ℕ => (n : ℝ))
              (show (4 : ℕ) - 3 = 1 by native_decide)
          _ = 1 :=
            Nat.cast_one
      have hreal : (4 - 3 : ℝ) = 1 := by
        exact Eq.subst
          (motive := fun x : ℝ => x = 1)
          (Nat.cast_sub (show (3 : ℕ) ≤ 4 by native_decide))
          hnat
      exact congrArg (fun x : ℝ => x / 3) hreal

theorem real_four_div_three_sub_one_ne_zero_for_logarithmicPhase :
    ((4 / 3 : ℝ) - 1) ≠ 0 := by
  exact Eq.subst
    (motive := fun x : ℝ => x ≠ 0)
    real_four_div_three_sub_one_eq_one_div_three_for_logarithmicPhase.symm
    (ne_of_gt (one_div_pos.mpr zero_lt_three))

theorem real_rat_half_cast_for_logarithmicPhase :
    (((1 / 2 : ℚ) : ℝ)) = (1 / 2 : ℝ) := by
  calc
    (((1 / 2 : ℚ) : ℝ)) = ((1 : ℚ) : ℝ) / ((2 : ℚ) : ℝ) :=
      Rat.cast_div 1 2
    _ = (1 : ℝ) / ((2 : ℚ) : ℝ) := by
      exact congrArg (fun x : ℝ => x / ((2 : ℚ) : ℝ)) Rat.cast_one
    _ = (1 : ℝ) / 2 := by
      exact congrArg (fun x : ℝ => (1 : ℝ) / x) (Rat.cast_ofNat 2)

theorem real_rat_five_thirds_cast_for_logarithmicPhase :
    (((5 / 3 : ℚ) : ℝ)) = (5 / 3 : ℝ) := by
  calc
    (((5 / 3 : ℚ) : ℝ)) = ((5 : ℚ) : ℝ) / ((3 : ℚ) : ℝ) :=
      Rat.cast_div 5 3
    _ = (5 : ℝ) / ((3 : ℚ) : ℝ) := by
      exact congrArg (fun x : ℝ => x / ((3 : ℚ) : ℝ)) (Rat.cast_ofNat 5)
    _ = (5 : ℝ) / 3 := by
      exact congrArg (fun x : ℝ => (5 : ℝ) / x) (Rat.cast_ofNat 3)

theorem real_rat_eight_thirds_cast_for_logarithmicPhase :
    (((8 / 3 : ℚ) : ℝ)) = (8 / 3 : ℝ) := by
  calc
    (((8 / 3 : ℚ) : ℝ)) = ((8 : ℚ) : ℝ) / ((3 : ℚ) : ℝ) :=
      Rat.cast_div 8 3
    _ = (8 : ℝ) / ((3 : ℚ) : ℝ) := by
      exact congrArg (fun x : ℝ => x / ((3 : ℚ) : ℝ)) (Rat.cast_ofNat 8)
    _ = (8 : ℝ) / 3 := by
      exact congrArg (fun x : ℝ => (8 : ℝ) / x) (Rat.cast_ofNat 3)

theorem real_eight_eq_sixteen_mul_half_for_logarithmicPhase :
    (8 : ℝ) = 16 * (1 / 2 : ℝ) := by
  have hq : (8 : ℚ) = 16 * (1 / 2 : ℚ) := by
    native_decide
  calc
    (8 : ℝ) = ((8 : ℚ) : ℝ) := rfl
    _ = ((16 * (1 / 2 : ℚ) : ℚ) : ℝ) := by
      exact congrArg (fun q : ℚ => (q : ℝ)) hq
    _ = (16 : ℝ) * ((1 / 2 : ℚ) : ℝ) :=
      Rat.cast_mul 16 (1 / 2 : ℚ)
    _ = (16 : ℝ) * (1 / 2 : ℝ) := by
      exact congrArg (fun x : ℝ => (16 : ℝ) * x)
        real_rat_half_cast_for_logarithmicPhase

theorem real_eight_mul_two_eq_sixteen_for_logarithmicPhase :
    (8 : ℝ) * 2 = 16 := by
  have hq : (8 : ℚ) * 2 = 16 := by
    native_decide
  calc
    (8 : ℝ) * 2 = ((8 : ℚ) : ℝ) * ((2 : ℚ) : ℝ) := by
      exact congrArg₂ Mul.mul rfl (Rat.cast_ofNat 2).symm
    _ = (((8 : ℚ) * 2 : ℚ) : ℝ) :=
      (Rat.cast_mul 8 2).symm
    _ = 16 := by
      exact congrArg (fun q : ℚ => (q : ℝ)) hq

theorem real_one_add_five_thirds_eq_eight_thirds_for_logarithmicPhase :
    (1 : ℝ) + 5 / 3 = 8 / 3 := by
  have hq : (1 : ℚ) + 5 / 3 = 8 / 3 := by
    native_decide
  calc
    (1 : ℝ) + 5 / 3 = ((1 : ℚ) : ℝ) + ((5 / 3 : ℚ) : ℝ) := by
      exact congrArg₂ Add.add Rat.cast_one.symm
        real_rat_five_thirds_cast_for_logarithmicPhase.symm
    _ = (((1 : ℚ) + 5 / 3 : ℚ) : ℝ) :=
      (Rat.cast_add 1 (5 / 3 : ℚ)).symm
    _ = ((8 / 3 : ℚ) : ℝ) := by
      exact congrArg (fun q : ℚ => (q : ℝ)) hq
    _ = 8 / 3 :=
      real_rat_eight_thirds_cast_for_logarithmicPhase

end

end LFunctions
end Boundary
