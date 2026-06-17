import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ClassicalAnalysis.ZetaEulerMaclaurinBoundary.LogarithmicPhase.EntropyAlgebra

/-!
# Complex support algebra for logarithmic phase estimates

This file owns elementary complex rearrangements and finite-Abel algebraic
steps used by the logarithmic phase estimates.
-/

namespace Boundary
namespace LFunctions

noncomputable section

theorem complex_sub_one_eq_neg_one_sub_for_logarithmicPhase (z : ℂ) :
    z - 1 = -(1 - z) :=
  (neg_sub 1 z).symm

theorem real_neg_pi_add_two_pi_eq_pi_for_logarithmicPhase :
    -Real.pi + 2 * Real.pi = Real.pi := by
  calc
    -Real.pi + 2 * Real.pi = -Real.pi + (Real.pi + Real.pi) := by
      exact congrArg (fun x : ℝ => -Real.pi + x) (two_mul Real.pi)
    _ = (-Real.pi + Real.pi) + Real.pi := by
      exact (add_assoc (-Real.pi) Real.pi Real.pi).symm
    _ = 0 + Real.pi := by
      exact congrArg (fun x : ℝ => x + Real.pi) (neg_add_cancel Real.pi)
    _ = Real.pi := zero_add Real.pi

theorem real_mem_Ioc_pi_to_periodic_upper_for_logarithmicPhase
    {x : ℝ}
    (hx : x ∈ Set.Ioc (-Real.pi) Real.pi) :
    x ∈ Set.Ioc (-Real.pi) (-Real.pi + 2 * Real.pi) :=
  Eq.subst
    (motive := fun upper : ℝ => x ∈ Set.Ioc (-Real.pi) upper)
    real_neg_pi_add_two_pi_eq_pi_for_logarithmicPhase.symm
    hx

theorem real_toIocMod_mem_Ioc_pi_for_logarithmicPhase
    (θ : ℝ) :
    toIocMod Real.two_pi_pos (-Real.pi) θ ∈ Set.Ioc (-Real.pi) Real.pi :=
  Eq.subst
    (motive := fun upper : ℝ =>
      toIocMod Real.two_pi_pos (-Real.pi) θ ∈ Set.Ioc (-Real.pi) upper)
    real_neg_pi_add_two_pi_eq_pi_for_logarithmicPhase
    (toIocMod_mem_Ioc Real.two_pi_pos (-Real.pi) θ)

theorem complex_I_mul_eq_I_mul_add_I_mul_sub_for_logarithmicPhase
    (a b : ℂ) :
    Complex.I * b = Complex.I * a + Complex.I * (b - a) := by
  have hadd : a + (b - a) = b := by
    calc
      a + (b - a) = (b - a) + a := add_comm a (b - a)
      _ = b := sub_add_cancel b a
  calc
    Complex.I * b = Complex.I * (a + (b - a)) := by
      exact congrArg (fun z : ℂ => Complex.I * z) hadd.symm
    _ = Complex.I * a + Complex.I * (b - a) := by
      exact mul_add Complex.I a (b - a)

theorem complex_sub_mul_self_eq_mul_one_sub_for_logarithmicPhase
    (u r : ℂ) :
    u - u * r = u * (1 - r) := by
  calc
    u - u * r = u * 1 - u * r := by
      exact congrArg (fun z : ℂ => z - u * r) (mul_one u).symm
    _ = u * (1 - r) := by
      exact (mul_sub u 1 r).symm

theorem complex_inv_mul_mul_right_cancel_for_logarithmicPhase
    {d u : ℂ}
    (hd : d ≠ 0) :
    d⁻¹ * (u * d) = u := by
  calc
    d⁻¹ * (u * d) = d⁻¹ * (d * u) := by
      exact congrArg (fun z : ℂ => d⁻¹ * z) (mul_comm u d)
    _ = (d⁻¹ * d) * u := by
      exact (mul_assoc d⁻¹ d u).symm
    _ = 1 * u := by
      exact congrArg (fun z : ℂ => z * u) (inv_mul_cancel₀ hd)
    _ = u := one_mul u

theorem complex_finiteAbel_singleton_step_for_logarithmicPhase
    (A u : ℕ → ℂ)
    (m : ℕ) :
    A m * (u m - u (m + 1)) =
      A m * u m - A ((m + 1) - 1) * u (m + 1) := by
  have hpred : (m + 1) - 1 = m :=
    Nat.add_sub_cancel m 1
  calc
    A m * (u m - u (m + 1)) =
        A m * u m - A m * u (m + 1) := by
      exact mul_sub (A m) (u m) (u (m + 1))
    _ = A m * u m - A ((m + 1) - 1) * u (m + 1) := by
      exact congrArg
        (fun z : ℂ => A m * u m - z * u (m + 1))
        (congrArg A hpred.symm)

theorem complex_prefixAbel_boundary_rearrange_for_logarithmicPhase
    (X D U V : ℂ) :
    (X - D * U + V) + U = (X + (1 - D) * U) + V := by
  have hinner : -D * U + U = (1 - D) * U := by
    calc
      -D * U + U = U + -D * U := add_comm (-D * U) U
      _ = 1 * U + -D * U := by
        exact congrArg (fun z : ℂ => z + -D * U) (one_mul U).symm
      _ = 1 * U + (-D) * U := rfl
      _ = (1 + -D) * U := by
        exact (add_mul 1 (-D) U).symm
      _ = (1 - D) * U := by
        exact congrArg (fun z : ℂ => z * U) (sub_eq_add_neg 1 D).symm
  calc
    (X - D * U + V) + U = (X - D * U) + (V + U) := by
      exact add_assoc (X - D * U) V U
    _ = (X - D * U) + (U + V) := by
      exact congrArg (fun z : ℂ => (X - D * U) + z) (add_comm V U)
    _ = ((X - D * U) + U) + V := by
      exact (add_assoc (X - D * U) U V).symm
    _ = (X + (-(D * U)) + U) + V := by
      exact congrArg (fun z : ℂ => (z + U) + V) (sub_eq_add_neg X (D * U))
    _ = (X + (-D * U) + U) + V := by
      exact congrArg
        (fun z : ℂ => (X + z + U) + V)
        (neg_mul D U).symm
    _ = (X + ((-D * U) + U)) + V := by
      exact congrArg (fun z : ℂ => z + V) (add_assoc X (-D * U) U)
    _ = (X + (1 - D) * U) + V := by
      exact congrArg (fun z : ℂ => (X + z) + V) hinner

theorem real_two_add_two_eq_four_for_logarithmicPhase :
    (2 : ℝ) + 2 = 4 := by
  have hnat : (2 : ℕ) + 2 = 4 := by
    rfl
  have hcast :
      (((2 : ℕ) + 2 : ℕ) : ℝ) = ((4 : ℕ) : ℝ) :=
    congrArg (fun n : ℕ => (n : ℝ)) hnat
  have hleft :
      (((2 : ℕ) + 2 : ℕ) : ℝ) = (2 : ℝ) + 2 :=
    Nat.cast_add 2 2
  have hright : ((4 : ℕ) : ℝ) = 4 :=
    rfl
  exact Eq.trans hleft.symm (Eq.trans hcast hright)

theorem real_two_mul_add_two_mul_eq_four_mul_for_logarithmicPhase
    (x : ℝ) :
    2 * x + 2 * x = 4 * x := by
  calc
    2 * x + 2 * x = ((2 : ℝ) + 2) * x :=
      (add_mul (2 : ℝ) 2 x).symm
    _ = 4 * x := by
      exact congrArg (fun r : ℝ => r * x)
        real_two_add_two_eq_four_for_logarithmicPhase

theorem complex_finiteAbel_successor_reassociate_for_logarithmicPhase
    (p q r s S : ℂ) :
    (r - s) + (p - q + S) = p - s + (r - q) + S := by
  calc
    (r - s) + (p - q + S) =
        (r + -s) + ((p + -q) + S) := by
      exact congrArg₂ Add.add (sub_eq_add_neg r s) (congrArg (fun z : ℂ => z + S) (sub_eq_add_neg p q))
    _ = r + -s + (p + -q) + S := by
      exact (add_assoc (r + -s) (p + -q) S).symm
    _ = (r + -s + (p + -q)) + S := rfl
    _ = (p + -s + (r + -q)) + S := by
      have hcore :
          r + -s + (p + -q) = p + -s + (r + -q) := by
        calc
          r + -s + (p + -q) = (r + -s) + (p + -q) := rfl
          _ = r + (-s + (p + -q)) := by
            exact add_assoc r (-s) (p + -q)
          _ = r + ((-s + p) + -q) := by
            exact congrArg (fun z : ℂ => r + z) (add_assoc (-s) p (-q)).symm
          _ = r + ((p + -s) + -q) := by
            exact congrArg (fun z : ℂ => r + (z + -q)) (add_comm (-s) p)
          _ = (r + (p + -s)) + -q := by
            exact (add_assoc r (p + -s) (-q)).symm
          _ = ((p + -s) + r) + -q := by
            exact congrArg (fun z : ℂ => z + -q) (add_comm r (p + -s))
          _ = (p + -s) + (r + -q) := by
            exact add_assoc (p + -s) r (-q)
      exact congrArg (fun z : ℂ => z + S) hcore
    _ = (p - s + (r - q)) + S := by
      exact congrArg
        (fun z : ℂ => (z + (r + -q)) + S)
        (sub_eq_add_neg p s).symm
    _ = p - s + (r - q) + S := by
      exact congrArg (fun z : ℂ => (p - s + z) + S) (sub_eq_add_neg r q).symm

end

end LFunctions
end Boundary
