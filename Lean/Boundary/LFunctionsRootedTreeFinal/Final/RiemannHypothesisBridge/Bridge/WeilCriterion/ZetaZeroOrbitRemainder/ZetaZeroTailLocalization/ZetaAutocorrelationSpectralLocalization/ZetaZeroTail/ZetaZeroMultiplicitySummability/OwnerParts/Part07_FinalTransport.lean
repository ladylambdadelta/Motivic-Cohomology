import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaZeroTail.ZetaZeroMultiplicitySummability.OwnerParts.Part06_ShellMassSummability

namespace Boundary
namespace LFunctions

noncomputable section

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
theorem exists_summable_completedZero_centeredHeight_negativePower_with_countingMargin
    (hbranch : Complex.BinetSecondFormulaBranchUniformTailAbsorption)
    (hpartialOneTwo : BoundaryLineOneAbelPartialMajorant)
    (hcompactOneTwo : PoleClearedOneTwoStripCompactBoundaryBound)
    (hfinite : PoleClearedRightCriticalStripAdmissibleGrowth)
    (hpartialLeft : ReflectedBoundaryAbelPartialMajorant)
    (hcompactBoundary : PoleClearedRightCriticalStripCompactBoundaryBound) :
    ∃ d : ℕ,
      ∀ k : ℕ,
        Summable
          (fun ρ : {ρ : ℂ // ZetaCompletedZero ρ} =>
            zetaCompletedZeroCenteredHeight ρ ^ (-(d + k + 3 : ℤ))) := by
  exact match exists_completedZeroMultiplicityCounting_height_bound
      hbranch
      hpartialOneTwo hcompactOneTwo
      hfinite
      hpartialLeft hcompactBoundary with
  | ⟨C, d, hCpos, hcount⟩ =>
      Exists.intro d
        (fun k =>
          summable_completedZero_centeredHeight_negativePower_of_counting_bound
            C d k hCpos hcount)

end

end LFunctions
end Boundary
