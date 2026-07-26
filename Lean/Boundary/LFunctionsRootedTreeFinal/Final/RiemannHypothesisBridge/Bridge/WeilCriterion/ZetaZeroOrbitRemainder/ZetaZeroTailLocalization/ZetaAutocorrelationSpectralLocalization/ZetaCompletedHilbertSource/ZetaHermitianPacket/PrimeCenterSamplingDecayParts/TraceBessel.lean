import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaCompletedHilbertSource.ZetaHermitianPacket.CompletedPrimePowerSampling
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaCompletedHilbertSource.ZetaHermitianPacket.PrimeCenterSamplingDecayParts.TraceBesselParts.HasSum
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaCompletedHilbertSource.ZetaHermitianPacket.PrimeCenterSamplingDecayParts.TraceBesselParts.PrimeAmplitudeFrameSummability
import Mathlib.Topology.Algebra.InfiniteSum.Order

/-!
# Prime-center trace Bessel source

This file owns the finite-subtrace Bessel input for the weighted completed
prime-center sampling stream.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open scoped BigOperators

namespace ZetaAdmissibleFunction

/-- Source trace-energy `HasSum` reconstruction for the weighted completed
prime-center sampling stream. -/
theorem completedAutocorrelationSpectralTransform_weightedPrimeSampling_hasSum_traceEnergy_source_owner
    (f : ZetaAdmissibleFunction) (C₀ : ℝ) (k : ℕ)
    (hbound : PrimeCenterSpectralPolynomialBound f C₀ k) :
    HasSum
      (fun index : ZetaPrimePowerIndex =>
        completedAutocorrelationSpectralTransform_weightedPrimeSampling
          index f)
      (completedAutocorrelationSpectralTransform_weightedPrimeSamplingTraceEnergy
        f) := by
  exact
    completedAutocorrelationSpectralTransform_weightedPrimeSampling_hasSum_traceEnergy_source_primitive
      f
      C₀ k hbound

/-- Source rectangular-window Bessel domination by one reconstructed
trace-energy scalar. -/
theorem completedAutocorrelationSpectralTransform_weightedPrimeSampling_boxSubtrace_le_traceEnergyScalar_source_owner
    (f : ZetaAdmissibleFunction) (C₀ : ℝ) (k : ℕ)
    (hbound : PrimeCenterSpectralPolynomialBound f C₀ k) :
    ∀ N : ℕ,
      ∑ index in ZetaPrimePowerIndex.box N,
        completedAutocorrelationSpectralTransform_weightedPrimeSampling
          index f ≤
        completedAutocorrelationSpectralTransform_weightedPrimeSamplingTraceEnergy
          f := by
  intro N
  have hnonnegative :
      ∀ index : ZetaPrimePowerIndex,
        0 ≤
          completedAutocorrelationSpectralTransform_weightedPrimeSampling
            index f := by
    intro index
    exact
      completedAutocorrelationSpectralTransform_weightedPrimeSampling_nonnegative
        index f
  exact
    sum_le_hasSum
      (ZetaPrimePowerIndex.box N)
      (fun index hindex => hnonnegative index)
      (completedAutocorrelationSpectralTransform_weightedPrimeSampling_hasSum_traceEnergy_source_owner
        f C₀ k hbound)

/-- Source rectangular-window Bessel domination for the weighted completed
prime-center sampling stream. -/
theorem completedAutocorrelationSpectralTransform_weightedPrimeSampling_boxSubtrace_bounded_traceKernel_source_owner
    (f : ZetaAdmissibleFunction) (C₀ : ℝ) (k : ℕ)
    (hbound : PrimeCenterSpectralPolynomialBound f C₀ k) :
    ∃ C : ℝ,
      ∀ N : ℕ,
        ∑ index in ZetaPrimePowerIndex.box N,
          completedAutocorrelationSpectralTransform_weightedPrimeSampling
            index f ≤ C := by
  exact
    ⟨completedAutocorrelationSpectralTransform_weightedPrimeSamplingTraceEnergy f,
      completedAutocorrelationSpectralTransform_weightedPrimeSampling_boxSubtrace_le_traceEnergyScalar_source_owner
        f C₀ k hbound⟩

/-- Source finite-subtrace Bessel domination for the weighted completed
prime-center sampling stream. -/
theorem completedAutocorrelationSpectralTransform_weightedPrimeSampling_finiteSubtrace_bounded_traceKernel_source_owner
    (f : ZetaAdmissibleFunction) (C₀ : ℝ) (k : ℕ)
    (hbound : PrimeCenterSpectralPolynomialBound f C₀ k) :
    ∃ C : ℝ,
      ∀ s : Finset ZetaPrimePowerIndex,
        ∑ index in s,
          completedAutocorrelationSpectralTransform_weightedPrimeSampling
            index f ≤ C := by
  exact
    completedAutocorrelationSpectralTransform_weightedPrimeSampling_finiteSubtrace_bessel_source_primitive
      f C₀ k hbound

theorem zetaCompletedPrimeVerticalSpectralAmplitudeIndex_normSq_finiteProjectionEnergy_bddAbove_traceBessel_source_owner
    (f : ZetaAdmissibleFunction) (D : ℝ) (k : ℕ)
    (hbound : VerticalPrimeCenterWeightedSpectralPolynomialBound f D k) :
    BddAbove
      (Set.range
        (fun s : Finset ZetaPrimePowerIndex =>
          zetaCompletedPrimeVerticalSpectralAmplitudeIndex_normSq_finiteProjectionEnergy
            s f)) :=
  zetaCompletedPrimeVerticalSpectralAmplitudeIndex_normSq_finiteProjectionEnergy_bddAbove_frame_source
    f D k hbound

theorem zetaCompletedPrimeVerticalOppositeSpectralAmplitudeIndex_normSq_finiteProjectionEnergy_bddAbove_traceBessel_source_owner
    (f : ZetaAdmissibleFunction) (D : ℝ) (k : ℕ)
    (hbound : VerticalPrimeCenterWeightedSpectralPolynomialBound
      (ZetaAdmissibleFunction.reflect f) D k) :
    BddAbove
      (Set.range
        (fun s : Finset ZetaPrimePowerIndex =>
          zetaCompletedPrimeVerticalOppositeSpectralAmplitudeIndex_normSq_finiteProjectionEnergy
            s f)) :=
  zetaCompletedPrimeVerticalOppositeSpectralAmplitudeIndex_normSq_finiteProjectionEnergy_bddAbove_frame_source
    f D k hbound

theorem zetaCompletedPrimeVerticalSpectralAmplitudeIndex_normSq_hasSum_traceBessel_source_owner
    (f : ZetaAdmissibleFunction) (D : ℝ) (k : ℕ)
    (hbound : VerticalPrimeCenterWeightedSpectralPolynomialBound f D k) :
    HasSum
      (fun index : ZetaPrimePowerIndex =>
        ‖zetaCompletedPrimeVerticalSpectralAmplitudeIndex index f‖ ^ 2)
      (∑' index : ZetaPrimePowerIndex,
        ‖zetaCompletedPrimeVerticalSpectralAmplitudeIndex index f‖ ^ 2) :=
  zetaCompletedPrimeVerticalSpectralAmplitudeIndex_normSq_hasSum_tsum_frame_source
    f D k hbound

theorem zetaCompletedPrimeVerticalOppositeSpectralAmplitudeIndex_normSq_hasSum_traceBessel_source_owner
    (f : ZetaAdmissibleFunction) (D : ℝ) (k : ℕ)
    (hbound : VerticalPrimeCenterWeightedSpectralPolynomialBound
      (ZetaAdmissibleFunction.reflect f) D k) :
    HasSum
      (fun index : ZetaPrimePowerIndex =>
        ‖zetaCompletedPrimeVerticalOppositeSpectralAmplitudeIndex index f‖ ^ 2)
      (∑' index : ZetaPrimePowerIndex,
        ‖zetaCompletedPrimeVerticalOppositeSpectralAmplitudeIndex index f‖ ^ 2) :=
  zetaCompletedPrimeVerticalOppositeSpectralAmplitudeIndex_normSq_hasSum_tsum_frame_source
    f D k hbound

end ZetaAdmissibleFunction

end
end LFunctions
end Boundary
