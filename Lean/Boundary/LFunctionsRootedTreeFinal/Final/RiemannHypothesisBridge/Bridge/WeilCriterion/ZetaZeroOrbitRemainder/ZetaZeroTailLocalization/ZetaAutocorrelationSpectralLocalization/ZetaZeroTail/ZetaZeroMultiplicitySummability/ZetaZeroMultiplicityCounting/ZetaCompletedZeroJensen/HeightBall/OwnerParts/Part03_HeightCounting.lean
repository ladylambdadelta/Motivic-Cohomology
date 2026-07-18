import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaZeroTail.ZetaZeroMultiplicitySummability.ZetaZeroMultiplicityCounting.ZetaCompletedZeroJensen.HeightBall.OwnerParts.Part02_SummandComparison

namespace Boundary
namespace LFunctions

noncomputable section

open Filter
open scoped Topology

/-- Height-ball summands vanish off the centered height ball. -/
theorem completedZeroMultiplicityHeightBallSummand_eq_zero_of_not_mem_for_jensen
    (T : ℝ) (ρ : {ρ : ℂ // ZetaCompletedZero ρ})
    (hρ : ρ ∉ completedZerosInCenteredHeightBall T) :
    completedZeroMultiplicityHeightBallSummand T ρ = 0 := by
  exact if_neg hρ

/-- Finite centered-height balls give the height-ball summand needed for Jensen transport. -/
theorem summable_completedZeroMultiplicityHeightBallSummand_for_jensen
    (T : ℝ) :
    Summable
      (fun ρ : {ρ : ℂ // ZetaCompletedZero ρ} =>
        completedZeroMultiplicityHeightBallSummand T ρ) := by
  exact summable_of_finite_support_real
    (fun ρ : {ρ : ℂ // ZetaCompletedZero ρ} =>
      completedZeroMultiplicityHeightBallSummand T ρ)
    (completedZerosInCenteredHeightBall T)
    (finite_completedZerosInCenteredHeightBall T)
    (completedZeroMultiplicityHeightBallSummand_eq_zero_of_not_mem_for_jensen T)

/-- Centered-height multiplicity counting is bounded by closed-disk multiplicity counting
at the controlled enlarged radius. -/
theorem completedZeroMultiplicityCounting_heightBall_le_closedDiskCounting
    (T : ℝ) (hT : 1 ≤ T) :
    completedZeroMultiplicityCountingInCenteredHeightBall T ≤
      completedZeroMultiplicityCountingInCenteredClosedDisk (T + 2) := by
    exact tsum_le_tsum
      (fun ρ : {ρ : ℂ // ZetaCompletedZero ρ} =>
        completedZeroMultiplicityHeightBallSummand_le_closedDiskSummand T hT ρ)
      (summable_completedZeroMultiplicityHeightBallSummand_for_jensen T)
      (summable_completedZeroMultiplicityClosedDiskSummand (T + 2))
end

end LFunctions
end Boundary
