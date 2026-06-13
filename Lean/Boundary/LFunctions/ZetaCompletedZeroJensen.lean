import Boundary.LFunctions.ZetaZeroSideDefinitions

/-!
# Jensen counting for completed zeta zeros

This file owns the finite-order/Jensen analytic counting input for the centered
completed zeta divisor, counted with analytic multiplicity.
-/

namespace Boundary
namespace LFunctions

noncomputable section

/-- Finite-order growth for the centered completed zeta function.

This is the entire-function input: the completed zeta normalization is an entire
function of finite order in the centered coordinate. -/
theorem centeredCompletedRiemannZeta_finiteOrder_growth_bound :
    ∃ A : ℝ, ∃ m : ℕ,
      0 < A ∧
      ∀ z : ℂ,
        ‖centeredCompletedRiemannZeta z‖ ≤
          A * (1 + ‖z‖) ^ m := by
  sorry

/-- Jensen transport from finite-order growth to multiplicity-aware centered-height
zero counting. -/
theorem centeredCompletedRiemannZeta_zeroMultiplicityCounting_height_bound_of_finiteOrder
    (hfinite :
      ∃ A : ℝ, ∃ m : ℕ,
        0 < A ∧
        ∀ z : ℂ,
          ‖centeredCompletedRiemannZeta z‖ ≤
            A * (1 + ‖z‖) ^ m) :
    ∃ C : ℝ, ∃ d : ℕ,
      0 < C ∧
      ∀ T : ℝ,
        1 ≤ T →
        completedZeroMultiplicityCountingInCenteredHeightBall T ≤ C * T ^ d := by
  sorry

/-- Finite-order/Jensen zero counting for the centered completed zeta divisor,
with analytic multiplicities and centered vertical height. -/
theorem centeredCompletedRiemannZeta_finiteOrder_zeroMultiplicityCounting_height_bound :
    ∃ C : ℝ, ∃ d : ℕ,
      0 < C ∧
      ∀ T : ℝ,
        1 ≤ T →
        completedZeroMultiplicityCountingInCenteredHeightBall T ≤ C * T ^ d := by
  exact
    centeredCompletedRiemannZeta_zeroMultiplicityCounting_height_bound_of_finiteOrder
      centeredCompletedRiemannZeta_finiteOrder_growth_bound

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
