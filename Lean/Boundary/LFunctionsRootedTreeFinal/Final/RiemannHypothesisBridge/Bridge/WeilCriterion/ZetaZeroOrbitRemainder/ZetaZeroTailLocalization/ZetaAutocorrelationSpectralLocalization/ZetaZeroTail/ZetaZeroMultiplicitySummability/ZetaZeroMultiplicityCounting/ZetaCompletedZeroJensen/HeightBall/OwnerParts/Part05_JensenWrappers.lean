import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaZeroTail.ZetaZeroMultiplicitySummability.ZetaZeroMultiplicityCounting.ZetaCompletedZeroJensen.HeightBall.OwnerParts.Part04_PolynomialTransport

namespace Boundary
namespace LFunctions

noncomputable section

open Filter
open scoped Topology

/-- Closed-disk zero counting bounds height-ball counting after polynomial enlargement. -/
theorem completedZeroMultiplicityCounting_heightBall_bound_of_closedDisk_bound
    (hclosed :
      ∃ C : ℝ, ∃ d : ℕ,
        0 < C ∧
        ∀ R : ℝ,
          1 ≤ R →
          completedZeroMultiplicityCountingInCenteredClosedDisk R ≤ C * R ^ d) :
    ∃ C : ℝ, ∃ d : ℕ,
      0 < C ∧
      ∀ T : ℝ,
        1 ≤ T →
        completedZeroMultiplicityCountingInCenteredHeightBall T ≤ C * T ^ d := by
  exact
    match hclosed with
    | ⟨C, d, hC, hbound⟩ =>
        match completedZeroMultiplicityCounting_heightBall_polynomial_bound_of_closedDisk_bound
            C d hC hbound with
        | ⟨C', hC', hbound'⟩ =>
            ⟨C', d, hC', hbound'⟩

/-- Jensen transport from finite-order growth of the entire zero-carrier to
multiplicity-aware centered-height completed-zero counting. -/
theorem centeredCompletedRiemannZeta_zeroMultiplicityCounting_height_bound_of_zeroCarrierFiniteOrder
    (hfinite :
      ∃ A : ℝ, ∃ B : ℝ, ∃ m : ℕ,
        0 < A ∧
        0 < B ∧
        ∀ z : ℂ,
          ‖centeredCompletedRiemannZetaZeroCarrier z‖ ≤
            A * Real.exp (B * (1 + ‖z‖) ^ m)) :
    ∃ C : ℝ, ∃ d : ℕ,
      0 < C ∧
      ∀ T : ℝ,
        1 ≤ T →
        completedZeroMultiplicityCountingInCenteredHeightBall T ≤ C * T ^ d := by
  exact completedZeroMultiplicityCounting_heightBall_bound_of_closedDisk_bound
    (centeredCompletedRiemannZeta_closedDiskMultiplicityCounting_bound_of_zeroCarrierFiniteOrder
      hfinite)

/-- Jensen transport from finite-order growth of the uncentered entire completed-zeta part
to multiplicity-aware centered-height completed-zero counting. -/
theorem centeredCompletedRiemannZeta_zeroMultiplicityCounting_height_bound_of_uncenteredFiniteOrder
    (huncentered :
      ∃ A : ℝ, ∃ B : ℝ, ∃ m : ℕ,
        0 < A ∧
        0 < B ∧
        ∀ z : ℂ,
          ‖completedRiemannZeta₀ z‖ ≤
            A * Real.exp (B * (1 + ‖z‖) ^ m)) :
    ∃ C : ℝ, ∃ d : ℕ,
      0 < C ∧
      ∀ T : ℝ,
        1 ≤ T →
        completedZeroMultiplicityCountingInCenteredHeightBall T ≤ C * T ^ d := by
  exact centeredCompletedRiemannZeta_zeroMultiplicityCounting_height_bound_of_zeroCarrierFiniteOrder
    (centeredCompletedRiemannZetaZeroCarrier_finiteOrder_growth_bound_of_uncentered huncentered)

/-- Finite-order/Jensen zero counting for the centered completed zeta divisor,
with analytic multiplicities and centered vertical height. -/
theorem centeredCompletedRiemannZeta_finiteOrder_zeroMultiplicityCounting_height_bound
    (hbranch : Complex.BinetSecondFormulaBranchUniformTailAbsorption)
    (hpartialOneTwo : BoundaryLineOneAbelPartialMajorant)
    (hcompactOneTwo : PoleClearedOneTwoStripCompactBoundaryBound)
    (hfinite : PoleClearedRightCriticalStripAdmissibleGrowth)
    (hpartialLeft : ReflectedBoundaryAbelPartialMajorant)
    (hcompactBoundary : PoleClearedRightCriticalStripCompactBoundaryBound) :
    ∃ C : ℝ, ∃ d : ℕ,
      0 < C ∧
      ∀ T : ℝ,
        1 ≤ T →
        completedZeroMultiplicityCountingInCenteredHeightBall T ≤ C * T ^ d := by
  exact
    centeredCompletedRiemannZeta_zeroMultiplicityCounting_height_bound_of_uncenteredFiniteOrder
      (completedRiemannZeta₀_finiteOrder_growth_bound
        hbranch
        hpartialOneTwo hcompactOneTwo
        hfinite
        hpartialLeft hcompactBoundary)

/-- Coarse polynomial counting of completed zeros with multiplicity in centered
height. -/
theorem exists_completedZeroMultiplicityCounting_height_bound
    (hbranch : Complex.BinetSecondFormulaBranchUniformTailAbsorption)
    (hpartialOneTwo : BoundaryLineOneAbelPartialMajorant)
    (hcompactOneTwo : PoleClearedOneTwoStripCompactBoundaryBound)
    (hfinite : PoleClearedRightCriticalStripAdmissibleGrowth)
    (hpartialLeft : ReflectedBoundaryAbelPartialMajorant)
    (hcompactBoundary : PoleClearedRightCriticalStripCompactBoundaryBound) :
    ∃ C : ℝ, ∃ d : ℕ,
      0 < C ∧
      ∀ T : ℝ,
        1 ≤ T →
        completedZeroMultiplicityCountingInCenteredHeightBall T ≤ C * T ^ d := by
  exact centeredCompletedRiemannZeta_finiteOrder_zeroMultiplicityCounting_height_bound
    hbranch
    hpartialOneTwo hcompactOneTwo
    hfinite
    hpartialLeft hcompactBoundary



end

end LFunctions
end Boundary
