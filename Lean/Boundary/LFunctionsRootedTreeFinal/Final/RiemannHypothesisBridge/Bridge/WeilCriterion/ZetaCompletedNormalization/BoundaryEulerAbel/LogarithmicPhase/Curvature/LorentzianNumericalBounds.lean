import Mathlib.Data.Real.Basic

/-!
# Lorentzian numerical bounds — arithmetic lemmas

Support theorems for the dyadic decomposition arithmetic.
-/

namespace Boundary
namespace LFunctions

noncomputable section

namespace Real

/-- Floor of 2η is at most 2η. -/
theorem floor_two_eta_le (η : ℝ) (hη_pos : 0 < η) :
    (⌊2 * η⌋₊ : ℝ) ≤ 2 * η :=
  Nat.floor_le hη_pos.le

/-- ⌊2η⌋ + 3 ≤ 2η + 3. -/
theorem floor_two_eta_plus_three_le (η : ℝ) (hη_pos : 0 < η) :
    ((⌊2 * η⌋₊ + 3 : ℕ) : ℝ) ≤ 2 * η + 3 := by
  have h := floor_two_eta_le η hη_pos
  have h_cast : ((⌊2 * η⌋₊ : ℕ) : ℝ) + (3 : ℝ) ≤ 2 * η + 3 := add_le_add h (le_refl 3)
  have h_unfold : ((⌊2 * η⌋₊ + 3 : ℕ) : ℝ) = ((⌊2 * η⌋₊ : ℕ) : ℝ) + (3 : ℝ) := by
    rw [Nat.cast_add]
  rw [h_unfold]
  exact h_cast

/-- For η > 0, we have 2η + 3 ≤ 8(η + 1). -/
theorem two_eta_plus_three_le_eight_eta_plus_one
    (η : ℝ) (hη_pos : 0 < η) :
    2 * η + 3 ≤ 8 * (η + 1) := by
  sorry

/-- Chaining: ⌊2η⌋ + 3 ≤ 8(η + 1). -/
theorem floor_two_eta_plus_three_le_eight_eta_plus_one
    (η : ℝ) (hη_pos : 0 < η) :
    ((⌊2 * η⌋₊ + 3 : ℕ) : ℝ) ≤ 8 * (η + 1) :=
  le_trans (floor_two_eta_plus_three_le η hη_pos) (two_eta_plus_three_le_eight_eta_plus_one η hη_pos)

end Real

end LFunctions
end Boundary
