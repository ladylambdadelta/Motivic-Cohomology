import Boundary.LFunctions.ZetaZeroMultiplicityCounting

/-!
# Completed zero multiplicity summability

This file owns the passage from multiplicity-aware height counting to summability
of negative centered-height powers over completed zeros.
-/

namespace Boundary
namespace LFunctions

noncomputable section

/-- The degree-aware shell masses are summable under the polynomial
multiplicity-counting bound. -/
theorem summable_completedZeroCenteredHeightShellDecayMass_of_counting_bound
    (C : ℝ) (d k : ℕ)
    (hCpos : 0 < C)
    (hcount :
      ∀ T : ℝ,
        1 ≤ T →
        completedZeroMultiplicityCountingInCenteredHeightBall T ≤ C * T ^ d) :
    Summable
      (fun m : ℕ =>
        completedZeroCenteredHeightShellDecayMass d k m) := by
  sorry

/-- Polynomial negative-height envelopes are summable over completed zeros once
the decay exponent is chosen beyond the counting degree.

This is the p-series consequence of multiplicity-aware polynomial zero counting. -/
theorem summable_completedZero_centeredHeight_negativePower_of_counting_bound
    (C : ℝ) (d k : ℕ)
    (hCpos : 0 < C)
    (hcount :
      ∀ T : ℝ,
        1 ≤ T →
        completedZeroMultiplicityCountingInCenteredHeightBall T ≤ C * T ^ d) :
    Summable
      (fun ρ : {ρ : ℂ // ZetaCompletedZero ρ} =>
        zetaCompletedZeroCenteredHeight ρ ^ (-(d + k + 3 : ℤ))) := by
  exact summable_completedZero_centeredHeight_negativePower_of_shellMass
    d
    k
    (summable_completedZeroCenteredHeightShellDecayMass_of_counting_bound
      C d k hCpos hcount)

/-- The completed-zero counting theorem supplies a counting degree after which
all further polynomial negative-height envelopes are summable. -/
theorem exists_summable_completedZero_centeredHeight_negativePower_with_countingMargin :
    ∃ d : ℕ,
      ∀ k : ℕ,
        Summable
          (fun ρ : {ρ : ℂ // ZetaCompletedZero ρ} =>
            zetaCompletedZeroCenteredHeight ρ ^ (-(d + k + 3 : ℤ))) := by
  rcases exists_completedZeroMultiplicityCounting_height_bound with
    ⟨C, d, hCpos, hcount⟩
  refine ⟨d, ?_⟩
  intro k
  exact summable_completedZero_centeredHeight_negativePower_of_counting_bound
    C d k hCpos hcount

end

end LFunctions
end Boundary
