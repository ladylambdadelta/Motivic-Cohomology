import Boundary.LFunctions.ZetaZeroSideDefinitions

/-!
# Jensen counting for completed zeta zeros

This file owns the finite-order/Jensen analytic counting input for the centered
completed zeta divisor, counted with analytic multiplicity.
-/

namespace Boundary
namespace LFunctions

noncomputable section

/-- Finite-order/Jensen zero counting for the centered completed zeta divisor,
with analytic multiplicities and centered vertical height. -/
theorem centeredCompletedRiemannZeta_finiteOrder_zeroMultiplicityCounting_height_bound :
    ∃ C : ℝ, ∃ d : ℕ,
      0 < C ∧
      ∀ T : ℝ,
        1 ≤ T →
        completedZeroMultiplicityCountingInCenteredHeightBall T ≤ C * T ^ d := by
  sorry

/-- Coarse polynomial counting of completed zeros with multiplicity in centered
height. -/
theorem exists_completedZeroMultiplicityCounting_height_bound :
    ∃ C : ℝ, ∃ d : ℕ,
      0 < C ∧
      ∀ T : ℝ,
        1 ≤ T →
        completedZeroMultiplicityCountingInCenteredHeightBall T ≤ C * T ^ d := by
  exact centeredCompletedRiemannZeta_finiteOrder_zeroMultiplicityCounting_height_bound

end

end LFunctions
end Boundary
