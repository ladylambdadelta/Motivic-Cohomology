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

/-- The one-dimensional polynomial tail with one spare power is summable. -/
theorem summable_one_add_nat_norm_negative_zpow_succ
    (k : ℕ) :
    Summable
      (fun m : ℕ =>
        (1 + ‖((m : ℕ) : ℝ)‖) ^ (-(k + 2 : ℤ))) := by
  sorry

end

end LFunctions
end Boundary
