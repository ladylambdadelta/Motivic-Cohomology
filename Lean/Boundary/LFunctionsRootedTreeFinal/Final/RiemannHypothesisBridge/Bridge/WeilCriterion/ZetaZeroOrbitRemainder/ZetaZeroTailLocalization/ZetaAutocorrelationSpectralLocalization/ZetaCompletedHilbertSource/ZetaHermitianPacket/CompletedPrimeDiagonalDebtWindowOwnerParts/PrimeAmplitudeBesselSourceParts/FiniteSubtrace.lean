import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaCompletedHilbertSource.ZetaHermitianPacket.PrimeCenterSamplingDecayParts.TraceBesselParts.PrimeWeightedSamplingTraceEnergy
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaCompletedHilbertSource.ZetaHermitianPacket.CompletedPrimeDiagonalDebtWindowOwnerParts.PrimeAmplitudeBesselSourceParts.ProjectionEnergyCore
import Mathlib.Topology.Algebra.InfiniteSum.Order

/-!
# Completed prime weighted finite-subtrace source

This file owns the Hilbert-frame finite-subtrace Bessel estimate for the
completed weighted prime-center sampling stream.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open scoped BigOperators

namespace ZetaAdmissibleFunction

/-- A scalar is a Hilbert-frame Bessel bound for finite completed weighted
prime-center sampling subtraces. -/
def CompletedWeightedPrimeSamplingHilbertFrameBesselBound
    (f : ZetaAdmissibleFunction) (C : ℝ) : Prop :=
  ∀ s : Finset ZetaPrimePowerIndex,
    ∑ index in s,
      completedAutocorrelationSpectralTransform_weightedPrimeSampling
        index f ≤ C

/-- Hilbert-frame source summability for completed weighted prime-center
sampling. -/
theorem completedWeightedPrimeSampling_summable_hilbertFrame_source
    (f : ZetaAdmissibleFunction) :
    Summable
      (fun index : ZetaPrimePowerIndex =>
        completedAutocorrelationSpectralTransform_weightedPrimeSampling
          index f) :=
  completedAutocorrelationSpectralTransform_weightedPrimeSampling_summable_traceEnergy_source
    f

/-- Hilbert-frame source summability has the corresponding `tsum` as its sum. -/
theorem completedWeightedPrimeSampling_hasSum_tsum_hilbertFrame_source
    (f : ZetaAdmissibleFunction) :
    HasSum
      (fun index : ZetaPrimePowerIndex =>
        completedAutocorrelationSpectralTransform_weightedPrimeSampling
          index f)
      (∑' index : ZetaPrimePowerIndex,
        completedAutocorrelationSpectralTransform_weightedPrimeSampling
          index f) :=
  (completedWeightedPrimeSampling_summable_hilbertFrame_source f).hasSum

/-- The completed weighted prime sampling stream is pointwise nonnegative in
the finite-subtrace owner. -/
theorem completedWeightedPrimeSampling_nonnegative_finiteSubtrace
    (f : ZetaAdmissibleFunction) :
    ∀ index : ZetaPrimePowerIndex,
      0 ≤
        completedAutocorrelationSpectralTransform_weightedPrimeSampling
          index f :=
  fun index : ZetaPrimePowerIndex =>
    completedAutocorrelationSpectralTransform_weightedPrimeSampling_nonnegative
      index f

/-- A completed weighted prime sampling `HasSum` bounds every finite subtrace. -/
theorem completedWeightedPrimeSampling_finiteSubtrace_le_of_hasSum_hilbertFrame
    (f : ZetaAdmissibleFunction)
    (total : ℝ)
    (hhasSum :
      HasSum
        (fun index : ZetaPrimePowerIndex =>
          completedAutocorrelationSpectralTransform_weightedPrimeSampling
            index f)
        total) :
    ∀ s : Finset ZetaPrimePowerIndex,
      ∑ index in s,
        completedAutocorrelationSpectralTransform_weightedPrimeSampling
          index f ≤ total :=
  fun s : Finset ZetaPrimePowerIndex =>
    sum_le_hasSum
      s
      (fun index membership =>
        completedWeightedPrimeSampling_nonnegative_finiteSubtrace
          f index)
      hhasSum

/-- The `tsum` of the completed weighted prime-center sampling stream is a
Hilbert-frame Bessel bound for all finite subtraces. -/
theorem completedWeightedPrimeSampling_tsum_besselBound_of_summable_hilbertFrame
    (f : ZetaAdmissibleFunction) :
    CompletedWeightedPrimeSamplingHilbertFrameBesselBound
      f
      (∑' index : ZetaPrimePowerIndex,
        completedAutocorrelationSpectralTransform_weightedPrimeSampling
          index f) :=
  let hhasSum :
      HasSum
        (fun index : ZetaPrimePowerIndex =>
          completedAutocorrelationSpectralTransform_weightedPrimeSampling
            index f)
        (∑' index : ZetaPrimePowerIndex,
          completedAutocorrelationSpectralTransform_weightedPrimeSampling
            index f) :=
    completedWeightedPrimeSampling_hasSum_tsum_hilbertFrame_source f
  completedWeightedPrimeSampling_finiteSubtrace_le_of_hasSum_hilbertFrame
    f
    (∑' index : ZetaPrimePowerIndex,
      completedAutocorrelationSpectralTransform_weightedPrimeSampling
        index f)
    hhasSum

/-- Hilbert-frame source existence of a Bessel bound for completed weighted
prime-center sampling. -/
theorem completedWeightedPrimeSamplingHilbertFrameBesselBound_source
    (f : ZetaAdmissibleFunction) :
    ∃ C : ℝ,
      CompletedWeightedPrimeSamplingHilbertFrameBesselBound f C :=
  ⟨∑' index : ZetaPrimePowerIndex,
      completedAutocorrelationSpectralTransform_weightedPrimeSampling
        index f,
    completedWeightedPrimeSampling_tsum_besselBound_of_summable_hilbertFrame
      f⟩

/-- Hilbert-frame source finite-subtrace Bessel domination for completed
weighted prime-center sampling. -/
theorem completedAutocorrelationSpectralTransform_weightedPrimeSampling_finiteSubtrace_hilbertFrame_source
    (f : ZetaAdmissibleFunction) :
    ∃ C : ℝ,
      ∀ s : Finset ZetaPrimePowerIndex,
        ∑ index in s,
          completedAutocorrelationSpectralTransform_weightedPrimeSampling
            index f ≤ C :=
  completedWeightedPrimeSamplingHilbertFrameBesselBound_source
    f

theorem completedWeightedPrimeSamplingProjectionEnergy_bddAbove_hilbertFrame_source
    (f : ZetaAdmissibleFunction) :
    BddAbove
      (Set.range
        (fun s : Finset ZetaPrimePowerIndex =>
          completedWeightedPrimeSamplingProjectionEnergy_hilbertFrame s f)) :=
  match completedWeightedPrimeSamplingHilbertFrameBesselBound_source f with
  | ⟨C, hC⟩ =>
      ⟨C, fun value hvalue =>
        match hvalue with
        | ⟨s, hs⟩ =>
            Eq.subst
              (motive := fun projection : ℝ => projection ≤ C)
              (completedWeightedPrimeSamplingProjectionEnergy_eq_sum_hilbertFrame
                s f).symm
              (hC s)⟩

end ZetaAdmissibleFunction

end
end LFunctions
end Boundary
