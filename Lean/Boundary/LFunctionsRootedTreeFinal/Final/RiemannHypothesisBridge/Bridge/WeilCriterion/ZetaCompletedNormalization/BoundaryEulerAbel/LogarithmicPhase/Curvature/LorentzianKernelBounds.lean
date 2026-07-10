import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Data.Real.Basic

/-!
# Lorentzian kernel bounds — support theorems

Standalone, sorry-free proofs for kernel bound properties.
-/

namespace Boundary
namespace LFunctions
namespace Real

/-- The Lorentzian kernel: η² / ((m - x)² + η²) -/
noncomputable def lorentzianKernel (η x m : ℝ) : ℝ :=
  η ^ 2 / (((m : ℝ) - x) ^ 2 + η ^ 2)

/-- Core shell: on the interval |m - x| ≤ η, the Lorentzian kernel is ≤ 1. -/
theorem lorentzianKernel_le_one_on_core
    (η : ℝ) (hη_pos : 0 < η) (m x : ℝ) :
    lorentzianKernel η x m ≤ 1 := by
  unfold lorentzianKernel
  -- Goal: η² / ((m - x)² + η²) ≤ 1
  -- Equivalent to: η² ≤ (m - x)² + η²
  rw [div_le_one]
  · -- Prove: η² ≤ (m - x)² + η²
    -- This is obvious: 0 ≤ (m - x)²
    have h_sq_nonneg : 0 ≤ (m - x) ^ 2 := sq_nonneg _
    exact le_add_of_nonneg_left h_sq_nonneg
  · -- Prove: 0 < (m - x)² + η²
    -- Since η² > 0 and (m - x)² ≥ 0, the sum is positive
    have h_η_sq_pos : 0 < η ^ 2 := sq_pos_of_pos hη_pos
    have h_sq_nonneg : 0 ≤ (m - x) ^ 2 := sq_nonneg _
    exact add_pos_of_nonneg_of_pos h_sq_nonneg h_η_sq_pos

end Real
end LFunctions
end Boundary
