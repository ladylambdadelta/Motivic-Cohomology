import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaZeroTail.ZetaZeroMultiplicitySummability.ZetaZeroMultiplicityCounting.ZetaCompletedZeroJensen.CarrierTransport.Owner

/-!
# Jensen closed-disk zero counting

This owner layer applies Jensen counting to the centered zero-carrier closed-disk divisor.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open Filter
open scoped Topology

/-- Jensen counting for the centered entire zero-carrier divisor in ordinary closed disks.

The nontriviality hypothesis is essential: finite-order growth alone does not control the
zero divisor of an identically zero entire function. The zeta-specific wrapper supplies
this hypothesis from the explicit value at the shifted pole face. -/
theorem centeredCompletedZetaZeroCarrierMultiplicityCounting_closedDisk_bound_by_jensen
    (hnontrivial :
      ∃ z : ℂ, centeredCompletedRiemannZetaZeroCarrier z ≠ 0)
    (hfinite :
      ∃ A : ℝ, ∃ B : ℝ, ∃ m : ℕ,
        0 < A ∧
        0 < B ∧
        ∀ z : ℂ,
          ‖centeredCompletedRiemannZetaZeroCarrier z‖ ≤
            A * Real.exp (B * (1 + ‖z‖) ^ m)) :
    ∃ C : ℝ, ∃ d : ℕ,
      0 < C ∧
      ∀ R : ℝ,
        1 ≤ R →
        centeredCompletedZetaZeroCarrierMultiplicityCountingInClosedDisk R ≤ C * R ^ d := by
  exact
    match entireFunctionZeroMultiplicityCounting_closedDisk_bound_by_jensen
        centeredCompletedRiemannZetaZeroCarrier
        centeredCompletedRiemannZetaZeroCarrier_analyticAt
        hnontrivial
        hfinite with
    | ⟨C, d, hC, hbound⟩ =>
        ⟨C, d, hC,
          fun R hR =>
            Eq.subst
              (motive := fun x : ℝ => x ≤ C * R ^ d)
              (centeredCompletedZetaZeroCarrierMultiplicityCountingInClosedDisk_eq_entire R).symm
              (hbound R hR)⟩

/-- Finite-order growth of the centered entire zero-carrier gives polynomial closed-disk
counting for its zero divisor.

This theorem is a thin wrapper over the Jensen owner theorem above; downstream completed-zero
transport should consume this wrapper rather than restating Jensen. -/
theorem centeredCompletedZetaZeroCarrierMultiplicityCounting_closedDisk_bound_of_finiteOrder
    (hfinite :
      ∃ A : ℝ, ∃ B : ℝ, ∃ m : ℕ,
        0 < A ∧
        0 < B ∧
        ∀ z : ℂ,
          ‖centeredCompletedRiemannZetaZeroCarrier z‖ ≤
            A * Real.exp (B * (1 + ‖z‖) ^ m)) :
    ∃ C : ℝ, ∃ d : ℕ,
      0 < C ∧
      ∀ R : ℝ,
        1 ≤ R →
        centeredCompletedZetaZeroCarrierMultiplicityCountingInClosedDisk R ≤ C * R ^ d := by
  exact centeredCompletedZetaZeroCarrierMultiplicityCounting_closedDisk_bound_by_jensen
    centeredCompletedRiemannZetaZeroCarrier_nontrivial
    hfinite

/-- Completed-zero closed-disk counting is dominated by the cleared-carrier divisor count.

This is the local divisor-transport step: clearing the shifted pole denominators does not
decrease the order of a non-pole zero. -/
theorem completedZeroMultiplicityCounting_closedDisk_le_carrierCounting
    (R : ℝ) :
    completedZeroMultiplicityCountingInCenteredClosedDisk R ≤
      centeredCompletedZetaZeroCarrierMultiplicityCountingInClosedDisk R := by
  exact completedZeroMultiplicityCounting_closedDisk_le_carrierCounting_of_summable
    R
    (summable_centeredCompletedZetaZeroCarrierMultiplicityClosedDiskSummand R)

/-- Jensen transport from finite-order growth of the entire zero-carrier to
multiplicity-aware centered closed-disk completed-zero counting. -/
theorem centeredCompletedRiemannZeta_closedDiskMultiplicityCounting_bound_of_zeroCarrierFiniteOrder
    (hfinite :
      ∃ A : ℝ, ∃ B : ℝ, ∃ m : ℕ,
        0 < A ∧
        0 < B ∧
        ∀ z : ℂ,
          ‖centeredCompletedRiemannZetaZeroCarrier z‖ ≤
            A * Real.exp (B * (1 + ‖z‖) ^ m)) :
    ∃ C : ℝ, ∃ d : ℕ,
      0 < C ∧
      ∀ R : ℝ,
        1 ≤ R →
        completedZeroMultiplicityCountingInCenteredClosedDisk R ≤ C * R ^ d := by
  exact
    match centeredCompletedZetaZeroCarrierMultiplicityCounting_closedDisk_bound_of_finiteOrder
        hfinite with
    | ⟨C, d, hC, hcarrier⟩ =>
        ⟨C, d, hC,
          fun R hR =>
            le_trans
              (completedZeroMultiplicityCounting_closedDisk_le_carrierCounting R)
              (hcarrier R hR)⟩


end

end LFunctions
end Boundary
