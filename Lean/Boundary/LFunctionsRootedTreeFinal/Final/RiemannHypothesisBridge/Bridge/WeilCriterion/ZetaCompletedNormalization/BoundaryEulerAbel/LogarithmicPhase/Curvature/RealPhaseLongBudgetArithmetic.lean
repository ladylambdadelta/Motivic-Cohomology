import Mathlib.Data.Real.Basic

/-!
# Real-phase long-budget arithmetic

This file owns the elementary target arithmetic used when assembling the
stationary and endpoint packet budgets in the logarithmic long branch.
-/

namespace Boundary
namespace LFunctions

noncomputable section

/-- Arithmetic for three endpoint-tail twentieth-budget estimates. -/
theorem Real.logarithmicPhase_three_twenty_targets_le_sixty
    (E : ℝ) :
    20 * E + (20 * E + 20 * E) ≤ 60 * E := by
  have hthree_sum :
      20 * E + (20 * E + 20 * E) = 60 * E := by
    have htwenty_twenty : (20 + 20 : ℝ) = 40 := by
      have hnat : (20 + 20 : ℕ) = 40 :=
        rfl
      exact Eq.trans (Nat.cast_add 20 20).symm
        (Eq.trans (congrArg (fun n : ℕ => (n : ℝ)) hnat) Nat.cast_ofNat)
    have hforty_twenty : (40 + 20 : ℝ) = 60 := by
      have hnat : (40 + 20 : ℕ) = 60 :=
        rfl
      exact Eq.trans (Nat.cast_add 40 20).symm
        (Eq.trans (congrArg (fun n : ℕ => (n : ℝ)) hnat) Nat.cast_ofNat)
    calc
      20 * E + (20 * E + 20 * E) =
          (20 * E + 20 * E) + 20 * E :=
        (add_assoc (20 * E) (20 * E) (20 * E)).symm
      _ = (20 + 20 : ℝ) * E + 20 * E := by
        exact congrArg (fun z : ℝ => z + 20 * E)
          ((add_mul 20 20 E).symm)
      _ = 40 * E + 20 * E := by
        exact congrArg (fun z : ℝ => z * E + 20 * E) htwenty_twenty
      _ = (40 + 20 : ℝ) * E :=
        (add_mul 40 20 E).symm
      _ = 60 * E := by
        exact congrArg (fun z : ℝ => z * E) hforty_twenty
  exact le_of_eq hthree_sum

/-- Three target units are bounded by ten target units for a nonnegative
target. -/
theorem Real.logarithmicPhase_three_target_le_ten
    {E : ℝ}
    (hE : 0 ≤ E) :
    3 * E ≤ 10 * E := by
  have hthree_le_ten : (3 : ℝ) ≤ 10 := by
    have hseven_nonneg : 0 ≤ (7 : ℝ) :=
      Nat.cast_nonneg 7
    calc
      (3 : ℝ) ≤ 3 + 7 :=
        le_add_of_nonneg_right hseven_nonneg
      _ = 10 := by
        have hnat : (3 + 7 : ℕ) = 10 :=
          rfl
        exact Eq.trans
          (Nat.cast_add 3 7).symm
          (Eq.trans
            (congrArg (fun n : ℕ => (n : ℝ)) hnat)
            Nat.cast_ofNat)
  exact mul_le_mul_of_nonneg_right hthree_le_ten hE

/-- Ten target units are bounded by twenty target units for a nonnegative
target. -/
theorem Real.logarithmicPhase_ten_target_le_twenty
    {E : ℝ}
    (hE : 0 ≤ E) :
    10 * E ≤ 20 * E := by
  have hten_le_twenty : (10 : ℝ) ≤ 20 := by
    have hten_nonneg : 0 ≤ (10 : ℝ) :=
      Nat.cast_nonneg 10
    calc
      (10 : ℝ) ≤ 10 + 10 :=
        le_add_of_nonneg_right hten_nonneg
      _ = 20 := by
        have hnat : (10 + 10 : ℕ) = 20 :=
          rfl
        exact Eq.trans
          (Nat.cast_add 10 10).symm
          (Eq.trans
            (congrArg (fun n : ℕ => (n : ℝ)) hnat)
            Nat.cast_ofNat)
  exact mul_le_mul_of_nonneg_right hten_le_twenty hE

/-- The stationary and endpoint packet budgets assemble into the widened long
target. -/
theorem Real.logarithmicPhase_twenty_sixty_targets_le_eighty
    (E : ℝ) :
    20 * E + 60 * E ≤ 80 * E := by
  have hleft :
      20 * E + 60 * E = (20 + 60) * E :=
    (add_mul 20 60 E).symm
  have hconst : (20 + 60 : ℝ) = 80 := by
    have hnat : (20 + 60 : ℕ) = 80 :=
      rfl
    exact Eq.trans (Nat.cast_add 20 60).symm
      (Eq.trans (congrArg (fun n : ℕ => (n : ℝ)) hnat) Nat.cast_ofNat)
  have hright :
      (20 + 60 : ℝ) * E = 80 * E :=
    congrArg (fun r : ℝ => r * E) hconst
  exact le_of_eq (Eq.trans hleft hright)

end

end LFunctions
end Boundary
