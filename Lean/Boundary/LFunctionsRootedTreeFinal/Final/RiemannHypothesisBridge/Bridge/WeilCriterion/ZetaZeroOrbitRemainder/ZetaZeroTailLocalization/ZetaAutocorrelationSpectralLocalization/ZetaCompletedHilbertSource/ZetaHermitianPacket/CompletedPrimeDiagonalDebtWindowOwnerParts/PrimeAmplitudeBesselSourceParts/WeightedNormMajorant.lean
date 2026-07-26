import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaCompletedHilbertSource.ZetaHermitianPacket.CompletedPrimeDiagonalDebtWindowOwnerParts.PrimeAmplitudeBesselSourceParts.FiniteWeightedSamplingBesselSource
import Mathlib.Topology.Algebra.InfiniteSum.Order

/-!
# Completed prime weighted norm majorant

This file turns the finite-subtrace Bessel source for completed weighted
prime-center sampling into a summable norm majorant.
-/

namespace Boundary
namespace LFunctions

noncomputable section

namespace ZetaAdmissibleFunction

/-- A nonnegative summable majorant for the completed weighted prime-center
sampling norm stream. -/
def CompletedWeightedPrimeSamplingNormMajorant
    (f : ZetaAdmissibleFunction) (u : ZetaPrimePowerIndex → ℝ) : Prop :=
  Summable u ∧
    (∀ index : ZetaPrimePowerIndex, 0 ≤ u index) ∧
      ∀ index : ZetaPrimePowerIndex,
        ‖completedAutocorrelationSpectralTransform_weightedPrimeSampling
          index f‖ ≤ u index

/-- The completed weighted prime sampling stream is pointwise nonnegative. -/
theorem completedWeightedPrimeSampling_nonnegative_hilbertFrame
    (f : ZetaAdmissibleFunction) :
    ∀ index : ZetaPrimePowerIndex,
      0 ≤ completedAutocorrelationSpectralTransform_weightedPrimeSampling
        index f :=
  fun index : ZetaPrimePowerIndex =>
    completedAutocorrelationSpectralTransform_weightedPrimeSampling_nonnegative
      index f

/-- A finite-subtrace Bessel bound makes the completed weighted prime sampling
stream summable. -/
theorem completedWeightedPrimeSampling_summable_of_finiteSubtraceBound_hilbertFrame
    (f : ZetaAdmissibleFunction)
    (hbound :
      ∃ C : ℝ,
        ∀ s : Finset ZetaPrimePowerIndex,
          ∑ index in s,
            completedAutocorrelationSpectralTransform_weightedPrimeSampling
              index f ≤ C) :
    Summable
      (fun index : ZetaPrimePowerIndex =>
        completedAutocorrelationSpectralTransform_weightedPrimeSampling
          index f) :=
  match hbound with
  | ⟨C, hC⟩ =>
      summable_of_sum_le
        (completedWeightedPrimeSampling_nonnegative_hilbertFrame f)
        hC

/-- The completed weighted prime sampling stream majorizes its own norm,
because it is nonnegative. -/
theorem completedWeightedPrimeSampling_norm_le_self_hilbertFrame
    (f : ZetaAdmissibleFunction) :
    ∀ index : ZetaPrimePowerIndex,
      ‖completedAutocorrelationSpectralTransform_weightedPrimeSampling
        index f‖ ≤
        completedAutocorrelationSpectralTransform_weightedPrimeSampling
          index f :=
  fun index : ZetaPrimePowerIndex =>
    le_of_eq
    (Real.norm_of_nonneg
      (completedAutocorrelationSpectralTransform_weightedPrimeSampling_nonnegative
        index f))

/-- The completed weighted prime sampling stream is a nonnegative summable
majorant for its own norm. -/
theorem completedWeightedPrimeSamplingNormMajorant_of_finiteSubtraceBound_hilbertFrame
    (f : ZetaAdmissibleFunction)
    (hbound :
      ∃ C : ℝ,
        ∀ s : Finset ZetaPrimePowerIndex,
          ∑ index in s,
            completedAutocorrelationSpectralTransform_weightedPrimeSampling
              index f ≤ C) :
    ∃ u : ZetaPrimePowerIndex → ℝ,
      CompletedWeightedPrimeSamplingNormMajorant f u :=
  let u : ZetaPrimePowerIndex → ℝ :=
    fun index : ZetaPrimePowerIndex =>
      completedAutocorrelationSpectralTransform_weightedPrimeSampling
        index f
  let hsummable : Summable u :=
    completedWeightedPrimeSampling_summable_of_finiteSubtraceBound_hilbertFrame
      f hbound
  let hnonnegative :
      ∀ index : ZetaPrimePowerIndex, 0 ≤ u index :=
    completedWeightedPrimeSampling_nonnegative_hilbertFrame f
  let hmajorizes :
      ∀ index : ZetaPrimePowerIndex,
        ‖completedAutocorrelationSpectralTransform_weightedPrimeSampling
          index f‖ ≤ u index :=
    completedWeightedPrimeSampling_norm_le_self_hilbertFrame f
  ⟨u, hsummable, hnonnegative, hmajorizes⟩

/-- Hilbert-frame source construction of a summable majorant for the completed
weighted prime-center sampling norm stream. -/
theorem completedWeightedPrimeSamplingNormMajorant_source
    (f : ZetaAdmissibleFunction) :
    ∃ u : ZetaPrimePowerIndex → ℝ,
      CompletedWeightedPrimeSamplingNormMajorant f u :=
  completedWeightedPrimeSamplingNormMajorant_of_finiteSubtraceBound_hilbertFrame
    f
    (completedWeightedPrimeSamplingFiniteSubtraceBound_hilbertFrame_source_primitive
      f)

end ZetaAdmissibleFunction

end
end LFunctions
end Boundary
