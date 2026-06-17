import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ClassicalAnalysis.ZetaEulerMaclaurinBoundary.LogarithmicPhase.Basic

/-!
# Algebraic support for logarithmic phase estimates

This file owns the small real and complex algebra rearrangements used by the
analytic logarithmic phase estimates.
-/

namespace Boundary
namespace LFunctions

noncomputable section

theorem real_log_one_sub_log_eq_neg_log_for_logarithmicPhase (x : ℝ) :
    Real.log (1 : ℝ) - Real.log x = -Real.log x := by
  calc
    Real.log (1 : ℝ) - Real.log x = 0 - Real.log x := by
      exact congrArg (fun y : ℝ => y - Real.log x) Real.log_one
    _ = -Real.log x := zero_sub (Real.log x)

theorem real_log_endpoint_factor_for_logarithmicPhase (L : ℝ) :
    (2 * L) * L - L = L * (2 * L - 1) := by
  calc
    (2 * L) * L - L = L * (2 * L) - L := by
      exact congrArg (fun y : ℝ => y - L) (mul_comm (2 * L) L)
    _ = L * (2 * L) - L * 1 := by
      exact congrArg (fun y : ℝ => L * (2 * L) - y) (mul_one L).symm
    _ = L * (2 * L - 1) := by
      exact (mul_sub L (2 * L) 1).symm

theorem real_two_one_div_mul_eq_two_mul_div_for_logarithmicPhase
    (L u : ℝ) :
    (2 * (1 / u)) * L = 2 * L / u := by
  calc
    (2 * (1 / u)) * L = (2 * u⁻¹) * L := by
      exact congrArg (fun y : ℝ => (2 * y) * L) (one_div u)
    _ = 2 * (u⁻¹ * L) := by
      exact mul_assoc 2 u⁻¹ L
    _ = 2 * (L * u⁻¹) := by
      exact congrArg (fun y : ℝ => 2 * y) (mul_comm u⁻¹ L)
    _ = (2 * L) * u⁻¹ := by
      exact (mul_assoc 2 L u⁻¹).symm
    _ = 2 * L / u := by
      exact (div_eq_mul_inv (2 * L) u).symm

theorem real_zero_add_two_eq_two_for_logarithmicPhase : (0 : ℝ) + 2 = 2 :=
  zero_add 2

theorem real_two_mul_zero_add_one_eq_two_for_logarithmicPhase :
    (2 : ℝ) * (0 + 1) = 2 := by
  calc
    (2 : ℝ) * (0 + 1) = 2 * 1 := by
      exact congrArg (fun x : ℝ => (2 : ℝ) * x) (zero_add 1)
    _ = 2 := mul_one 2

theorem real_nat_succ_mul_two_cast_eq_for_logarithmicPhase
    (N : ℕ) :
    ((((N + 1) * 2 : ℕ) : ℝ)) = 2 * (((N : ℝ) + 1)) := by
  calc
    ((((N + 1) * 2 : ℕ) : ℝ)) = ((N + 1 : ℕ) : ℝ) * (2 : ℝ) := by
      exact Nat.cast_mul (N + 1) 2
    _ = (((N : ℝ) + 1) * 2) := by
      exact congrArg (fun x : ℝ => x * 2)
        ((Nat.cast_add N 1).trans
          (congrArg (fun x : ℝ => (N : ℝ) + x) Nat.cast_one))
    _ = 2 * (((N : ℝ) + 1)) := by
      exact mul_comm ((N : ℝ) + 1) 2

theorem real_nat_add_two_comm_for_logarithmicPhase
    (N : ℕ) :
    ((N : ℝ) + 2) = 2 + N :=
  add_comm (N : ℝ) 2

theorem real_eight_mul_eq_sixteen_mul_half_for_logarithmicPhase
    (q : ℝ) :
    8 * q = 16 * q * (1 / 2 : ℝ) := by
  calc
    8 * q = (16 * (1 / 2 : ℝ)) * q := by
      exact congrArg (fun c : ℝ => c * q)
        real_eight_eq_sixteen_mul_half_for_logarithmicPhase
    _ = (16 * q) * (1 / 2 : ℝ) := by
      calc
        (16 * (1 / 2 : ℝ)) * q = 16 * ((1 / 2 : ℝ) * q) := by
          exact mul_assoc 16 (1 / 2 : ℝ) q
        _ = 16 * (q * (1 / 2 : ℝ)) := by
          exact congrArg (fun y : ℝ => 16 * y) (mul_comm (1 / 2 : ℝ) q)
        _ = (16 * q) * (1 / 2 : ℝ) := by
          exact (mul_assoc 16 q (1 / 2 : ℝ)).symm

theorem real_eight_two_mul_log_scale_for_logarithmicPhase
    (s L : ℝ) :
    8 * (2 * s * L) = 16 * s * L := by
  calc
    8 * (2 * s * L) = 8 * ((2 * s) * L) := rfl
    _ = (8 * (2 * s)) * L := by
      exact (mul_assoc 8 (2 * s) L).symm
    _ = ((8 * 2) * s) * L := by
      exact congrArg (fun y : ℝ => y * L) (mul_assoc 8 2 s).symm
    _ = (16 * s) * L := by
      exact congrArg (fun y : ℝ => (y * s) * L)
        real_eight_mul_two_eq_sixteen_for_logarithmicPhase
    _ = 16 * s * L := rfl

theorem real_eight_mul_three_term_split_for_logarithmicPhase
    (q l : ℝ) :
    8 * (q + l + 1) = 8 * q + 8 * (l + 1) := by
  calc
    8 * (q + l + 1) = 8 * (q + (l + 1)) := by
      exact congrArg (fun x : ℝ => 8 * x) (add_assoc q l 1)
    _ = 8 * q + 8 * (l + 1) := by
      exact mul_add 8 q (l + 1)

theorem real_sixteen_mul_sum_log_factor_for_logarithmicPhase
    (q s L : ℝ) :
    16 * q * L + 16 * s * L = 16 * (q + s) * L := by
  calc
    16 * q * L + 16 * s * L = (16 * q + 16 * s) * L := by
      exact (add_mul (16 * q) (16 * s) L).symm
    _ = (16 * (q + s)) * L := by
      exact congrArg (fun x : ℝ => x * L) (mul_add 16 q s).symm
    _ = 16 * (q + s) * L := rfl

theorem real_add_one_sub_add_one_eq_sub_for_logarithmicPhase
    (A B : ℝ) :
    (A + 1) - (B + 1) = A - B := by
  calc
    (A + 1) - (B + 1) = (A + 1) - (1 + B) := by
      exact congrArg (fun y : ℝ => (A + 1) - y) (add_comm B 1)
    _ = A - B := by
      calc
        (A + 1) - (1 + B) = (A + 1) - 1 - B :=
          sub_add_eq_sub_sub (A + 1) 1 B
        _ = A - B := by
          exact congrArg (fun z : ℝ => z - B) (add_sub_cancel_right A 1)

theorem real_one_add_five_thirds_mul_eq_eight_thirds_mul_for_logarithmicPhase
    (A : ℝ) :
    A + (5 / 3 : ℝ) * A = (8 / 3 : ℝ) * A := by
  calc
    A + (5 / 3 : ℝ) * A = 1 * A + (5 / 3 : ℝ) * A := by
      exact congrArg (fun y : ℝ => y + (5 / 3 : ℝ) * A) (one_mul A).symm
    _ = (1 + (5 / 3 : ℝ)) * A := by
      exact (add_mul 1 (5 / 3 : ℝ) A).symm
    _ = (8 / 3 : ℝ) * A := by
      exact congrArg (fun c : ℝ => c * A)
        real_one_add_five_thirds_eq_eight_thirds_for_logarithmicPhase

end

end LFunctions
end Boundary
