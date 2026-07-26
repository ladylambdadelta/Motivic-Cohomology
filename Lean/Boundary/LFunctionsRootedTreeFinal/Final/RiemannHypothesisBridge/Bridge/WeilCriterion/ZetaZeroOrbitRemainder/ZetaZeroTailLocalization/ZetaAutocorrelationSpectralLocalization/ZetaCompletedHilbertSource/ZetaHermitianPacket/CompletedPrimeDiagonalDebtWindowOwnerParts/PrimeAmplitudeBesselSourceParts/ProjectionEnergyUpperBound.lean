import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaCompletedHilbertSource.ZetaHermitianPacket.CompletedPrimeDiagonalDebtWindowOwnerParts.PrimeAmplitudeBesselSourceParts.HilbertFrameBesselBound
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaCompletedHilbertSource.ZetaHermitianPacket.CompletedPrimeDiagonalDebtWindowOwnerParts.PrimeAmplitudeBesselSourceParts.ProjectionEnergyTransport
import Mathlib.Topology.Basic

/-!
# Completed weighted prime sampling projection-energy upper bound

This file owns the finite-projection Bessel upper-bound package for the
completed weighted prime-center sampling stream.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open scoped BigOperators

namespace ZetaAdmissibleFunction

/-- The finite projection-energy range is nonempty. -/
theorem completedWeightedPrimeSamplingProjectionEnergy_range_nonempty_hilbertFrame
    (f : ZetaAdmissibleFunction) :
    (Set.range
      (fun s : Finset ZetaPrimePowerIndex =>
        completedWeightedPrimeSamplingProjectionEnergy_hilbertFrame
          s f)).Nonempty :=
  Set.range_nonempty
    (fun s : Finset ZetaPrimePowerIndex =>
      completedWeightedPrimeSamplingProjectionEnergy_hilbertFrame s f)

/-- Source upper-bound package for finite completed weighted prime-center
projection energies. -/
theorem completedWeightedPrimeSamplingProjectionEnergy_hasUpperBound_hilbertFrame_source_primitive
    (f : ZetaAdmissibleFunction) :
    ∃ C : ℝ,
      CompletedWeightedPrimeSamplingProjectionEnergyUpperBound_hilbertFrame
        f C :=
  completedWeightedPrimeSamplingHilbertFrameBesselBound_source f

theorem completedWeightedPrimeSamplingProjectionEnergy_hasUpperBound_of_spectralPolynomialBounds_hilbertFrame_source
    (f : ZetaAdmissibleFunction) (Cpos Cneg : ℝ) (kpos kneg : ℕ)
    (hpos : PrimeCenterSpectralPolynomialBound f Cpos kpos)
    (hneg : PrimeCenterSpectralPolynomialBound
      (ZetaAdmissibleFunction.reflect f) Cneg kneg) :
    ∃ C : ℝ,
      CompletedWeightedPrimeSamplingProjectionEnergyUpperBound_hilbertFrame
        f C :=
  completedWeightedPrimeSamplingHilbertFrameBesselBound_of_spectralPolynomialBounds_source
    f Cpos Cneg kpos kneg hpos hneg

/-- A concrete upper-bound package gives boundedness above of the finite
projection-energy range. -/
theorem completedWeightedPrimeSamplingProjectionEnergy_bddAbove_of_hasUpperBound_hilbertFrame
    (f : ZetaAdmissibleFunction)
    (hupper :
      ∃ C : ℝ,
        CompletedWeightedPrimeSamplingProjectionEnergyUpperBound_hilbertFrame
          f C) :
    BddAbove
      (Set.range
        (fun s : Finset ZetaPrimePowerIndex =>
          completedWeightedPrimeSamplingProjectionEnergy_hilbertFrame
            s f)) :=
  match hupper with
  | ⟨C, hC⟩ =>
      completedWeightedPrimeSamplingProjectionEnergy_bddAbove_of_upperBound
        f C hC

/-- Source boundedness above of the finite completed weighted prime-center
projection energies. -/
theorem completedWeightedPrimeSamplingProjectionEnergy_bddAbove_hilbertFrame_source
    (f : ZetaAdmissibleFunction) :
    BddAbove
      (Set.range
        (fun s : Finset ZetaPrimePowerIndex =>
          completedWeightedPrimeSamplingProjectionEnergy_hilbertFrame
            s f)) :=
  completedWeightedPrimeSamplingProjectionEnergy_bddAbove_of_hasUpperBound_hilbertFrame
    f
    (completedWeightedPrimeSamplingProjectionEnergy_hasUpperBound_hilbertFrame_source_primitive
      f)

end ZetaAdmissibleFunction

end
end LFunctions
end Boundary
