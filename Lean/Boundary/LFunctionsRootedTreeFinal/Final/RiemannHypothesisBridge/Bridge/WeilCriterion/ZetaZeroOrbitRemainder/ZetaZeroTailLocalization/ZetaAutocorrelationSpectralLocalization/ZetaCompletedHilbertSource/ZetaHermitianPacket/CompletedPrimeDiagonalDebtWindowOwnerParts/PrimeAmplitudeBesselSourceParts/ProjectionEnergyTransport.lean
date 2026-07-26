import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaCompletedHilbertSource.EndpointTraceBessel
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaCompletedHilbertSource.ZetaHermitianPacket.CompletedPrimeDiagonalDebtWindowOwnerParts.PrimeAmplitudeBesselSourceParts.ProjectionEnergyCore

/-!
# Completed weighted prime sampling projection-energy transport

This file owns the order-theoretic transport from endpoint domination of all
finite completed prime projections to a finite-projection Bessel upper bound.
-/

namespace Boundary
namespace LFunctions

noncomputable section

namespace ZetaAdmissibleFunction

/-- Endpoint domination of every finite completed weighted prime-center
projection. -/
def CompletedWeightedPrimeSamplingFiniteProjectionEndpointDomination
    (f : ZetaAdmissibleFunction) : Prop :=
  ∀ s : Finset ZetaPrimePowerIndex,
    completedWeightedPrimeSamplingProjectionEnergy_hilbertFrame s f ≤
      completedBoundaryHilbertSourceEndpointProjectionEnergy
        (completedBoundaryHilbertSource f)

/-- Endpoint domination gives a concrete upper-bound package for finite
completed weighted prime-center projection energies. -/
theorem completedWeightedPrimeSamplingProjectionEnergy_hasUpperBound_of_endpointDomination
    (f : ZetaAdmissibleFunction)
    (hdomination :
      CompletedWeightedPrimeSamplingFiniteProjectionEndpointDomination f) :
    ∃ C : ℝ,
      ∀ s : Finset ZetaPrimePowerIndex,
        completedWeightedPrimeSamplingProjectionEnergy_hilbertFrame s f ≤ C :=
  ⟨completedBoundaryHilbertSourceEndpointProjectionEnergy
      (completedBoundaryHilbertSource f),
    hdomination⟩

/-- A finite-projection upper bound bounds every member of the projection-energy
range. -/
theorem completedWeightedPrimeSamplingProjectionEnergy_range_le_of_upperBound
    (f : ZetaAdmissibleFunction)
    (C : ℝ)
    (hC :
      ∀ s : Finset ZetaPrimePowerIndex,
        completedWeightedPrimeSamplingProjectionEnergy_hilbertFrame s f ≤ C) :
    ∀ value : ℝ,
      value ∈
        Set.range
          (fun s : Finset ZetaPrimePowerIndex =>
            completedWeightedPrimeSamplingProjectionEnergy_hilbertFrame s f) →
      value ≤ C :=
  fun value hvalue =>
    match hvalue with
    | ⟨s, hvalue_eq⟩ =>
        Eq.subst
          (motive := fun projectionValue : ℝ => projectionValue ≤ C)
          hvalue_eq
          (hC s)

/-- A finite-projection upper bound gives boundedness above of the projection
energy range. -/
theorem completedWeightedPrimeSamplingProjectionEnergy_bddAbove_of_upperBound
    (f : ZetaAdmissibleFunction)
    (C : ℝ)
    (hC :
      ∀ s : Finset ZetaPrimePowerIndex,
        completedWeightedPrimeSamplingProjectionEnergy_hilbertFrame s f ≤ C) :
    BddAbove
      (Set.range
        (fun s : Finset ZetaPrimePowerIndex =>
          completedWeightedPrimeSamplingProjectionEnergy_hilbertFrame s f)) :=
  ⟨C,
    completedWeightedPrimeSamplingProjectionEnergy_range_le_of_upperBound
      f C hC⟩

/-- Endpoint domination gives boundedness above of the finite completed
weighted prime-center projection-energy range. -/
theorem completedWeightedPrimeSamplingProjectionEnergy_bddAbove_of_endpointDomination
    (f : ZetaAdmissibleFunction)
    (hdomination :
      CompletedWeightedPrimeSamplingFiniteProjectionEndpointDomination f) :
    BddAbove
      (Set.range
        (fun s : Finset ZetaPrimePowerIndex =>
          completedWeightedPrimeSamplingProjectionEnergy_hilbertFrame s f)) :=
  match
    completedWeightedPrimeSamplingProjectionEnergy_hasUpperBound_of_endpointDomination
      f hdomination with
  | ⟨C, hC⟩ =>
      completedWeightedPrimeSamplingProjectionEnergy_bddAbove_of_upperBound
        f C hC

end ZetaAdmissibleFunction

end
end LFunctions
end Boundary
