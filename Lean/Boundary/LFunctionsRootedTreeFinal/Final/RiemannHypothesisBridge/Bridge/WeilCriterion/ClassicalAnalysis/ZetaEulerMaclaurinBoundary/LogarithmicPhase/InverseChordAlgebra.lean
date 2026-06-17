import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ClassicalAnalysis.ZetaEulerMaclaurinBoundary.LogarithmicPhase.Algebra

/-!
# Inverse-chord algebra for logarithmic phase estimates

This file owns the unit-circle algebra identities used to normalize inverse
geometric chord denominators.
-/

namespace Boundary
namespace LFunctions

noncomputable section

theorem real_inverse_chord_normsq_algebra_for_logarithmicPhase
    {s c : ℝ}
    (hunit : s ^ 2 + c ^ 2 = 1) :
    (1 - c) * (1 - c) + (-s) * (-s) = 2 * (1 - c) := by
  have hneg : (-s) * (-s) = s * s :=
    neg_mul_neg s s
  have hsq_sub : (1 - c) * (1 - c) = (1 - c) ^ 2 :=
    (pow_two (1 - c)).symm
  have hsub_sq :
      (1 - c) ^ 2 = 1 ^ 2 - 2 * 1 * c + c ^ 2 :=
    sub_sq 1 c
  have hone_sq : (1 : ℝ) ^ 2 = 1 := by
    calc
      (1 : ℝ) ^ 2 = (1 : ℝ) * 1 := pow_two 1
      _ = 1 := one_mul 1
  have htwo_one : (2 : ℝ) * 1 * c = 2 * c := by
    exact congrArg (fun x : ℝ => x * c) (mul_one 2)
  have hs_sq : s * s = s ^ 2 :=
    (pow_two s).symm
  have hunit_comm : c ^ 2 + s ^ 2 = 1 :=
    Eq.subst (motive := fun x : ℝ => x = 1) (add_comm (s ^ 2) (c ^ 2)) hunit
  calc
    (1 - c) * (1 - c) + (-s) * (-s) =
        (1 - c) ^ 2 + s * s := by
      exact congrArg₂ Add.add hsq_sub hneg
    _ = (1 ^ 2 - 2 * 1 * c + c ^ 2) + s * s := by
      exact congrArg (fun x : ℝ => x + s * s) hsub_sq
    _ = (1 - 2 * c + c ^ 2) + s ^ 2 := by
      exact congrArg₂ Add.add
        (congrArg₂ Add.add
          (congrArg₂ Sub.sub hone_sq htwo_one)
          rfl)
        hs_sq
    _ = 1 - 2 * c + (c ^ 2 + s ^ 2) := by
      calc
        (1 - 2 * c + c ^ 2) + s ^ 2 =
            (1 - 2 * c) + c ^ 2 + s ^ 2 := rfl
        _ = (1 - 2 * c) + (c ^ 2 + s ^ 2) := by
          exact add_assoc (1 - 2 * c) (c ^ 2) (s ^ 2)
    _ = 1 - 2 * c + 1 := by
      exact congrArg (fun x : ℝ => 1 - 2 * c + x) hunit_comm
    _ = 2 * (1 - c) := by
      calc
        1 - 2 * c + 1 = (1 + 1) - 2 * c := by
          exact sub_add_eq_add_sub 1 (2 * c) 1
        _ = 2 - 2 * c := by
          exact congrArg (fun x : ℝ => x - 2 * c) one_add_one_eq_two
        _ = 2 * 1 - 2 * c := by
          exact congrArg (fun x : ℝ => x - 2 * c) (mul_one 2).symm
        _ = 2 * (1 - c) := by
          exact (mul_sub 2 1 c).symm

theorem real_inverse_chord_derivative_numerator_algebra_for_logarithmicPhase
    {s c : ℝ}
    (hunit : s ^ 2 + c ^ 2 = 1) :
    c * (2 * (1 - c)) - s * (2 * s) =
      -2 * (1 - c) := by
  have hs_sq : s * s = s ^ 2 :=
    (pow_two s).symm
  have hc_sq : c * c = c ^ 2 :=
    (pow_two c).symm
  have hunit_comm : c ^ 2 + s ^ 2 = 1 :=
    Eq.subst (motive := fun x : ℝ => x = 1) (add_comm (s ^ 2) (c ^ 2)) hunit
  calc
    c * (2 * (1 - c)) - s * (2 * s) =
        (2 * c * (1 - c)) - (2 * (s * s)) := by
      have hleft : c * (2 * (1 - c)) = 2 * c * (1 - c) := by
        calc
          c * (2 * (1 - c)) = (c * 2) * (1 - c) := by
            exact (mul_assoc c 2 (1 - c)).symm
          _ = (2 * c) * (1 - c) := by
            exact congrArg (fun x : ℝ => x * (1 - c)) (mul_comm c 2)
          _ = 2 * c * (1 - c) := rfl
      have hright : s * (2 * s) = 2 * (s * s) := by
        calc
          s * (2 * s) = (s * 2) * s := by
            exact (mul_assoc s 2 s).symm
          _ = (2 * s) * s := by
            exact congrArg (fun x : ℝ => x * s) (mul_comm s 2)
          _ = 2 * (s * s) := by
            exact mul_assoc 2 s s
      exact congrArg₂ Sub.sub hleft hright
    _ = (2 * c * 1 - 2 * c * c) - 2 * (s * s) := by
      exact congrArg (fun x : ℝ => x - 2 * (s * s)) (mul_sub (2 * c) 1 c)
    _ = (2 * c - 2 * c ^ 2) - 2 * s ^ 2 := by
      have hc_square_scaled :
          2 * c * c = 2 * c ^ 2 := by
        calc
          2 * c * c = 2 * (c * c) := by
            exact mul_assoc 2 c c
          _ = 2 * c ^ 2 := by
            exact congrArg (fun x : ℝ => 2 * x) hc_sq
      exact congrArg₂ Sub.sub
        (congrArg₂ Sub.sub
          (mul_one (2 * c))
          hc_square_scaled)
        (congrArg (fun x : ℝ => 2 * x) hs_sq)
    _ = 2 * c - 2 * (c ^ 2 + s ^ 2) := by
      calc
        (2 * c - 2 * c ^ 2) - 2 * s ^ 2 =
            2 * c - (2 * c ^ 2 + 2 * s ^ 2) := by
          exact sub_sub (2 * c) (2 * c ^ 2) (2 * s ^ 2)
        _ = 2 * c - 2 * (c ^ 2 + s ^ 2) := by
          exact congrArg (fun x : ℝ => 2 * c - x) (mul_add 2 (c ^ 2) (s ^ 2)).symm
    _ = 2 * c - 2 * 1 := by
      exact congrArg (fun x : ℝ => 2 * c - 2 * x) hunit_comm
    _ = -(2 * 1 - 2 * c) := by
      exact (neg_sub (2 * 1) (2 * c)).symm
    _ = -2 * (1 - c) := by
      calc
        -(2 * 1 - 2 * c) = -(2 * (1 - c)) := by
          exact congrArg Neg.neg (mul_sub 2 1 c).symm
        _ = -2 * (1 - c) := by
          exact (neg_mul 2 (1 - c)).symm

end

end LFunctions
end Boundary
