import Mathlib.Order.Filter.AtTopBot
import Mathlib.Topology.Algebra.InfiniteSum.Basic

/-!
# Polynomial tail summability

This file owns one-dimensional polynomial tail summability lemmas shared by the
prime-window and completed-zero counting surfaces.
-/

namespace Boundary
namespace LFunctions

noncomputable section

/-- The natural height base is positive. -/
theorem one_add_nat_norm_pos
    (m : ℕ) :
    0 < 1 + ‖((m : ℕ) : ℝ)‖ := by
  exact lt_of_lt_of_le zero_lt_one
    (le_add_of_nonneg_right (norm_nonneg ((m : ℕ) : ℝ)))

/-- The natural height base is at least one. -/
theorem one_le_one_add_nat_norm
    (m : ℕ) :
    1 ≤ 1 + ‖((m : ℕ) : ℝ)‖ := by
  exact le_add_of_nonneg_right (norm_nonneg ((m : ℕ) : ℝ))

/-- The reciprocal-square tail over positive natural denominators is summable. -/
theorem summable_nat_succ_inverse_square :
    Summable
      (fun m : ℕ =>
        ((m + 1 : ℕ) : ℝ)⁻¹ ^ (2 : ℕ)) := by
  sorry

/-- The height-base reciprocal-square tail is the usual reciprocal-square tail. -/
theorem one_add_nat_norm_negative_two_eq_nat_succ_inverse_square
    (m : ℕ) :
    (1 + ‖((m : ℕ) : ℝ)‖) ^ (-(2 : ℤ)) =
      ((m + 1 : ℕ) : ℝ)⁻¹ ^ (2 : ℕ) := by
  sorry

/-- The reciprocal-square natural tail is summable. -/
theorem summable_one_add_nat_norm_negative_two :
    Summable
      (fun m : ℕ =>
        (1 + ‖((m : ℕ) : ℝ)‖) ^ (-(2 : ℤ))) := by
  have hfun :
      (fun m : ℕ =>
        (1 + ‖((m : ℕ) : ℝ)‖) ^ (-(2 : ℤ))) =
        (fun m : ℕ =>
          ((m + 1 : ℕ) : ℝ)⁻¹ ^ (2 : ℕ)) := by
    funext m
    exact one_add_nat_norm_negative_two_eq_nat_succ_inverse_square m
  exact Eq.subst
    (motive := fun u : ℕ → ℝ => Summable u)
    hfun.symm
    summable_nat_succ_inverse_square

/-- Higher negative powers of the natural height base are dominated by the
reciprocal-square tail. -/
theorem one_add_nat_norm_negative_zpow_succ_le_negative_two
    (k m : ℕ) :
    (1 + ‖((m : ℕ) : ℝ)‖) ^ (-(k + 2 : ℤ)) ≤
      (1 + ‖((m : ℕ) : ℝ)‖) ^ (-(2 : ℤ)) := by
  have hbase : 1 ≤ 1 + ‖((m : ℕ) : ℝ)‖ :=
    one_le_one_add_nat_norm m
  have hexp : (-(k + 2 : ℤ)) ≤ -(2 : ℤ) := by
    omega
  exact zpow_le_zpow_right₀ hbase hexp

/-- The one-dimensional polynomial tail is pointwise nonnegative. -/
theorem one_add_nat_norm_negative_zpow_succ_nonnegative
    (k m : ℕ) :
    0 ≤ (1 + ‖((m : ℕ) : ℝ)‖) ^ (-(k + 2 : ℤ)) := by
  exact zpow_nonneg
    (le_trans zero_le_one (one_le_one_add_nat_norm m))
    (-(k + 2 : ℤ))

/-- The one-dimensional polynomial tail with one spare power is summable. -/
theorem summable_one_add_nat_norm_negative_zpow_succ
    (k : ℕ) :
    Summable
      (fun m : ℕ =>
        (1 + ‖((m : ℕ) : ℝ)‖) ^ (-(k + 2 : ℤ))) := by
  exact Summable.of_norm_bounded
    (fun m : ℕ =>
      (1 + ‖((m : ℕ) : ℝ)‖) ^ (-(2 : ℤ)))
    summable_one_add_nat_norm_negative_two
    (fun m : ℕ => by
      have hleft_nonneg :
          0 ≤ (1 + ‖((m : ℕ) : ℝ)‖) ^ (-(k + 2 : ℤ)) :=
        one_add_nat_norm_negative_zpow_succ_nonnegative k m
      have hright_nonneg :
          0 ≤ (1 + ‖((m : ℕ) : ℝ)‖) ^ (-(2 : ℤ)) :=
        zpow_nonneg
          (le_trans zero_le_one (one_le_one_add_nat_norm m))
          (-(2 : ℤ))
      have hleft_norm :
          ‖(1 + ‖((m : ℕ) : ℝ)‖) ^ (-(k + 2 : ℤ))‖ =
            (1 + ‖((m : ℕ) : ℝ)‖) ^ (-(k + 2 : ℤ)) :=
        Real.norm_of_nonneg hleft_nonneg
      have hright_norm :
          ‖(1 + ‖((m : ℕ) : ℝ)‖) ^ (-(2 : ℤ))‖ =
            (1 + ‖((m : ℕ) : ℝ)‖) ^ (-(2 : ℤ)) :=
        Real.norm_of_nonneg hright_nonneg
      exact Eq.subst
        (motive := fun lhs : ℝ =>
          lhs ≤ ‖(1 + ‖((m : ℕ) : ℝ)‖) ^ (-(2 : ℤ))‖)
        hleft_norm.symm
        (Eq.subst
          (motive := fun rhs : ℝ =>
            (1 + ‖((m : ℕ) : ℝ)‖) ^ (-(k + 2 : ℤ)) ≤ rhs)
          hright_norm.symm
          (one_add_nat_norm_negative_zpow_succ_le_negative_two k m)))

end

end LFunctions
end Boundary
