import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ClassicalAnalysis.ZetaEulerMaclaurinBoundary.LogarithmicPhase.InverseChordAlgebra

/-!
# Critical-point algebra for logarithmic phase estimates

This file owns scalar algebra around the critical point of the dyadic
logarithmic comparison defect.
-/

namespace Boundary
namespace LFunctions

noncomputable section

theorem real_critical_num_add_den_eq_one_for_logarithmicPhase
    (L : ℝ) :
    (2 - 2 * L) + (2 * L - 1) = 1 := by
  calc
    (2 - 2 * L) + (2 * L - 1) = (2 : ℝ) - 1 :=
      sub_add_sub_cancel 2 (2 * L) 1
    _ = 1 := by
      calc
        (2 : ℝ) - 1 = (1 + 1 : ℝ) - 1 := by
          exact congrArg (fun x : ℝ => x - 1) (one_add_one_eq_two.symm)
        _ = 1 := by
          exact add_sub_cancel_right 1 1

theorem real_one_add_critical_den_eq_two_log_for_logarithmicPhase
    (L : ℝ) :
    (1 : ℝ) + (2 * L - 1) = 2 * L := by
  calc
    (1 : ℝ) + (2 * L - 1) = (2 * L - 1) + 1 := add_comm 1 (2 * L - 1)
    _ = 2 * L := sub_add_cancel (2 * L) 1

theorem real_critical_num_add_two_den_eq_two_log_for_logarithmicPhase
    (L : ℝ) :
    (2 - 2 * L) + 2 * (2 * L - 1) = 2 * L := by
  calc
    (2 - 2 * L) + 2 * (2 * L - 1) =
        (2 - 2 * L) + ((2 * L - 1) + (2 * L - 1)) := by
      exact congrArg (fun y : ℝ => (2 - 2 * L) + y) (two_mul (2 * L - 1))
    _ = ((2 - 2 * L) + (2 * L - 1)) + (2 * L - 1) := by
      exact (add_assoc (2 - 2 * L) (2 * L - 1) (2 * L - 1)).symm
    _ = 1 + (2 * L - 1) := by
      exact congrArg (fun y : ℝ => y + (2 * L - 1))
        (real_critical_num_add_den_eq_one_for_logarithmicPhase L)
    _ = 2 * L :=
      real_one_add_critical_den_eq_two_log_for_logarithmicPhase L

theorem real_critical_fraction_add_one_for_logarithmicPhase
    (L : ℝ)
    (hden_ne : 2 * L - 1 ≠ 0) :
    (2 - 2 * L) / (2 * L - 1) + 1 = 1 / (2 * L - 1) := by
  calc
    (2 - 2 * L) / (2 * L - 1) + 1 =
        (2 - 2 * L) / (2 * L - 1) + (2 * L - 1) / (2 * L - 1) := by
      exact congrArg
        (fun y : ℝ => (2 - 2 * L) / (2 * L - 1) + y)
        (div_self hden_ne).symm
    _ = ((2 - 2 * L) + (2 * L - 1)) / (2 * L - 1) := by
      exact (add_div (2 - 2 * L) (2 * L - 1) (2 * L - 1)).symm
    _ = 1 / (2 * L - 1) := by
      exact congrArg (fun y : ℝ => y / (2 * L - 1))
        (real_critical_num_add_den_eq_one_for_logarithmicPhase L)

theorem real_critical_fraction_add_two_for_logarithmicPhase
    (L : ℝ)
    (hden_ne : 2 * L - 1 ≠ 0) :
    (2 - 2 * L) / (2 * L - 1) + 2 =
      (2 * L) / (2 * L - 1) := by
  calc
    (2 - 2 * L) / (2 * L - 1) + 2 =
        (2 - 2 * L) / (2 * L - 1) +
          (2 * (2 * L - 1)) / (2 * L - 1) := by
      exact congrArg
        (fun y : ℝ => (2 - 2 * L) / (2 * L - 1) + y)
        (mul_div_cancel_right₀ 2 hden_ne).symm
    _ = ((2 - 2 * L) + 2 * (2 * L - 1)) / (2 * L - 1) := by
      exact (add_div (2 - 2 * L) (2 * (2 * L - 1)) (2 * L - 1)).symm
    _ = (2 * L) / (2 * L - 1) := by
      exact congrArg (fun y : ℝ => y / (2 * L - 1))
        (real_critical_num_add_two_den_eq_two_log_for_logarithmicPhase L)

theorem real_dyadic_deriv_left_common_denominator_for_logarithmicPhase
    (L x : ℝ)
    (hx_two_ne : x + 2 ≠ 0)
    (hx_one_ne : x + 1 ≠ 0) :
    2 * L / (x + 2) - 1 / (x + 1) =
      ((2 * L) * (x + 1) - 1 * (x + 2)) / ((x + 2) * (x + 1)) :=
  calc
    2 * L / (x + 2) - 1 / (x + 1) =
        ((2 * L) * (x + 1) - (x + 2) * 1) / ((x + 2) * (x + 1)) :=
      div_sub_div (2 * L) 1 hx_two_ne hx_one_ne
    _ = ((2 * L) * (x + 1) - 1 * (x + 2)) / ((x + 2) * (x + 1)) := by
      exact congrArg
        (fun y : ℝ => ((2 * L) * (x + 1) - y) / ((x + 2) * (x + 1)))
        (mul_comm (x + 2) 1)

theorem real_dyadic_deriv_numerator_factor_for_logarithmicPhase
    (L x : ℝ)
    (hden_ne : 2 * L - 1 ≠ 0) :
    (2 * L) * (x + 1) - 1 * (x + 2) =
      (2 * L - 1) * (x - (2 - 2 * L) / (2 * L - 1)) := by
  have hcancel :
      (2 * L - 1) * ((2 - 2 * L) / (2 * L - 1)) =
        2 - 2 * L := by
    exact mul_div_cancel₀ (2 - 2 * L) hden_ne
  calc
    (2 * L) * (x + 1) - 1 * (x + 2) =
        (2 * L * x + 2 * L * 1) - (1 * x + 1 * 2) := by
      exact congrArg₂ Sub.sub
        (mul_add (2 * L) x 1)
        (mul_add 1 x 2)
    _ = (2 * L * x + 2 * L) - (x + 2) := by
      exact congrArg₂ Sub.sub
        (congrArg (fun y : ℝ => 2 * L * x + y) (mul_one (2 * L)))
        (congrArg₂ Add.add (one_mul x) (one_mul 2))
    _ = (2 * L * x - x) + (2 * L - 2) := by
      calc
        (2 * L * x + 2 * L) - (x + 2) =
            (2 * L * x + 2 * L) - x - 2 := by
          exact sub_add_eq_sub_sub (2 * L * x + 2 * L) x 2
        _ = (2 * L * x - x) + 2 * L - 2 := by
          exact congrArg (fun y : ℝ => y - 2) (add_sub_right_comm (2 * L * x) (2 * L) x)
        _ = (2 * L * x - x) + (2 * L - 2) := by
          exact add_sub_assoc (2 * L * x - x) (2 * L) 2
    _ = (2 * L - 1) * x + (2 * L - 2) := by
      have hx_factor : 2 * L * x - x = (2 * L - 1) * x := by
        calc
          2 * L * x - x = 2 * L * x - 1 * x := by
            exact congrArg (fun y : ℝ => 2 * L * x - y) (one_mul x).symm
          _ = (2 * L - 1) * x := by
            exact (sub_mul (2 * L) 1 x).symm
      exact congrArg (fun y : ℝ => y + (2 * L - 2)) hx_factor
    _ = (2 * L - 1) * x - (2 - 2 * L) := by
      calc
        (2 * L - 1) * x + (2 * L - 2) =
            (2 * L - 1) * x + -(2 - 2 * L) := by
          exact congrArg
            (fun y : ℝ => (2 * L - 1) * x + y)
            (neg_sub 2 (2 * L)).symm
        _ = (2 * L - 1) * x - (2 - 2 * L) := by
          exact (sub_eq_add_neg ((2 * L - 1) * x) (2 - 2 * L)).symm
    _ = (2 * L - 1) * x -
          (2 * L - 1) * ((2 - 2 * L) / (2 * L - 1)) := by
      exact congrArg
        (fun y : ℝ => (2 * L - 1) * x - y)
        hcancel.symm
    _ = (2 * L - 1) *
          (x - (2 - 2 * L) / (2 * L - 1)) := by
      exact (mul_sub (2 * L - 1) x ((2 - 2 * L) / (2 * L - 1))).symm

end

end LFunctions
end Boundary
