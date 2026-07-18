import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaZeroTail.ZetaZeroMultiplicitySummability.ZetaZeroMultiplicityCounting.ZetaCompletedZeroJensen.ClosedDisk.OwnerParts.Part02_Geometry

namespace Boundary
namespace LFunctions

noncomputable section

/-- Finite closed disks make the closed-disk multiplicity summand summable. -/
theorem summable_completedZeroMultiplicityClosedDiskSummand_of_finite_closedDisk
    (R : ℝ)
    (hfinite : (completedZerosInCenteredClosedDisk R).Finite) :
    Summable
      (fun ρ : {ρ : ℂ // ZetaCompletedZero ρ} =>
        completedZeroMultiplicityClosedDiskSummand R ρ) := by
  exact summable_of_finite_support_real
    (fun ρ : {ρ : ℂ // ZetaCompletedZero ρ} =>
      completedZeroMultiplicityClosedDiskSummand R ρ)
    (completedZerosInCenteredClosedDisk R)
    hfinite
    (completedZeroMultiplicityClosedDiskSummand_eq_zero_of_not_mem R)

/-- Closed-disk multiplicity summands are summable. -/
theorem summable_completedZeroMultiplicityClosedDiskSummand
    (R : ℝ) :
    Summable
      (fun ρ : {ρ : ℂ // ZetaCompletedZero ρ} =>
        completedZeroMultiplicityClosedDiskSummand R ρ) := by
  exact summable_completedZeroMultiplicityClosedDiskSummand_of_finite_closedDisk
    R
    (finite_completedZerosInCenteredClosedDisk R)

end

end LFunctions
end Boundary

