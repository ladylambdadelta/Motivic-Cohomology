import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaZeroTail.ZetaZeroMultiplicitySummability.OwnerParts.Part05_TailEnvelope

namespace Boundary
namespace LFunctions

noncomputable section

theorem exists_norm_completedZeroCenteredHeightShellDecayMass_le_polynomialTail_of_counting_bound
    (C : ℝ) (d k : ℕ)
    (hCpos : 0 < C)
    (hcount :
      ∀ T : ℝ,
        1 ≤ T →
        completedZeroMultiplicityCountingInCenteredHeightBall T ≤ C * T ^ d) :
    ∃ A : ℝ,
      0 < A ∧
      ∀ m : ℕ,
        ‖completedZeroCenteredHeightShellDecayMass d k m‖ ≤
          A * (1 + ‖((m : ℕ) : ℝ)‖) ^ (-(k + 2 : ℤ)) := by
  exact match exists_completedZeroCenteredHeightShellCountingEnvelope_le_polynomialTail
      C d k hCpos with
  | ⟨A, hApos, hA⟩ =>
      Exists.intro A
        (And.intro hApos
          (fun m =>
            le_trans
              (norm_completedZeroCenteredHeightShellDecayMass_le_countingEnvelope
                C d k m hcount)
              (hA m)))

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
  exact match exists_norm_completedZeroCenteredHeightShellDecayMass_le_polynomialTail_of_counting_bound
      C d k hCpos hcount with
  | ⟨A, hAdata⟩ =>
      have htail :
          Summable
            (fun m : ℕ =>
              A * (1 + ‖((m : ℕ) : ℝ)‖) ^ (-(k + 2 : ℤ))) :=
        (summable_one_add_nat_norm_negative_zpow_succ k).mul_left A
      Summable.of_norm_bounded
        (fun m : ℕ =>
          A * (1 + ‖((m : ℕ) : ℝ)‖) ^ (-(k + 2 : ℤ)))
        htail
        hAdata.2


end

end LFunctions
end Boundary
