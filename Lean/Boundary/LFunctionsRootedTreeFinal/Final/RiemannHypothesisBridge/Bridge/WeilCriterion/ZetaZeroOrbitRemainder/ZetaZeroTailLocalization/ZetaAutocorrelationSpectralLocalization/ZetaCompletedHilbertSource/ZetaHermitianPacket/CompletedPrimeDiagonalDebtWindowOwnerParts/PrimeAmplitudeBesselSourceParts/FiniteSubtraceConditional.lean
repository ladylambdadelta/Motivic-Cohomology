import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaCompletedHilbertSource.ZetaHermitianPacket.CompletedPrimeDiagonalDebtWindowOwnerParts.PrimeAmplitudeBesselSourceParts.FiniteSubtrace
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaCompletedHilbertSource.ZetaHermitianPacket.PrimeCenterSamplingDecayParts.TraceBesselParts.PrimeWeightedSamplingDiagonalDebtBessel
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaCompletedHilbertSource.ZetaHermitianPacket.PrimeCenterSamplingSpectralOwner

/-!
# Conditional completed prime weighted finite-subtrace source

This file owns the finite-subtrace Bessel consequences that follow directly
from a completed diagonal-debt real-coordinate `HasSum`.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open scoped BigOperators

namespace ZetaAdmissibleFunction

/-- A diagonal-debt real-coordinate `HasSum` gives finite-subtrace Bessel
domination for completed weighted prime-center sampling. -/
theorem completedAutocorrelationSpectralTransform_weightedPrimeSampling_finiteSubtrace_hilbertFrame_of_diagonalDebtCoordinate_re_hasSum_source
    (f : ZetaAdmissibleFunction) (C : ℝ)
    (hhasSum :
      HasSum
        (fun index : ZetaPrimePowerIndex =>
          Complex.re
            (zetaCompletedPrimeDefectKernelDiagonalDebtCoordinate index f))
        C) :
    ∃ B : ℝ,
      ∀ s : Finset ZetaPrimePowerIndex,
        ∑ index in s,
          completedAutocorrelationSpectralTransform_weightedPrimeSampling
            index f ≤ B :=
  completedAutocorrelationSpectralTransform_weightedPrimeSampling_finiteSubtrace_bessel_exists_of_diagonalDebtCoordinate_re_hasSum_traceEnergy_source
    f C hhasSum

theorem completedAutocorrelationSpectralTransform_weightedPrimeSampling_finiteSubtrace_hilbertFrame_of_spectralPolynomialBound_source
    (f : ZetaAdmissibleFunction) (C : ℝ) (k : ℕ)
    (hbound : PrimeCenterSpectralPolynomialBound f C k) :
    ∃ B : ℝ,
      ∀ s : Finset ZetaPrimePowerIndex,
        ∑ index in s,
          completedAutocorrelationSpectralTransform_weightedPrimeSampling
            index f ≤ B :=
  completedAutocorrelationSpectralTransform_weightedPrimeSampling_finiteSubtrace_upperBound_of_spectralPolynomialBound_owner
    f C k hbound

theorem completedWeightedPrimeSampling_summable_hilbertFrame_of_spectralPolynomialBound_source
    (f : ZetaAdmissibleFunction) (C : ℝ) (k : ℕ)
    (hbound : PrimeCenterSpectralPolynomialBound f C k) :
    Summable
      (fun index : ZetaPrimePowerIndex =>
        completedAutocorrelationSpectralTransform_weightedPrimeSampling
          index f) :=
  match
    completedAutocorrelationSpectralTransform_weightedPrimeSampling_finiteSubtrace_upperBound_of_spectralPolynomialBound_owner
      f C k hbound with
  | ⟨B, hB⟩ =>
      let hnonnegative :
          0 ≤
            fun index : ZetaPrimePowerIndex =>
              completedAutocorrelationSpectralTransform_weightedPrimeSampling
                index f :=
        fun index : ZetaPrimePowerIndex =>
          completedAutocorrelationSpectralTransform_weightedPrimeSampling_nonnegative
            index f
      summable_of_sum_le hnonnegative hB

theorem completedAutocorrelationSpectralTransform_weightedPrimeSampling_windowSubtrace_upperBound_of_spectralPolynomialBound_source
    (f : ZetaAdmissibleFunction) (C : ℝ) (k : ℕ)
    (hbound : PrimeCenterSpectralPolynomialBound f C k) :
    ∃ B : ℝ, ∀ N : ℕ,
      completedAutocorrelationSpectralTransform_weightedPrimeSamplingWindow
        N f ≤ B :=
  completedAutocorrelationSpectralTransform_weightedPrimeSampling_windowSubtrace_upperBound_of_spectralPolynomialBound_owner
    f C k hbound

theorem completedAutocorrelationSpectralTransform_weightedPrimeSampling_boxSubtrace_upperBound_of_spectralPolynomialBound_source
    (f : ZetaAdmissibleFunction) (C : ℝ) (k : ℕ)
    (hbound : PrimeCenterSpectralPolynomialBound f C k) :
    ∃ B : ℝ, ∀ N : ℕ,
      (∑ index in ZetaPrimePowerIndex.box N,
        completedAutocorrelationSpectralTransform_weightedPrimeSampling
          index f) ≤ B :=
  completedAutocorrelationSpectralTransform_weightedPrimeSampling_boxSubtrace_upperBound_of_spectralPolynomialBound_owner
    f C k hbound

/-- A diagonal-debt real-coordinate `HasSum` gives Hilbert-frame finite
Bessel domination in the local finite-subtrace package. -/
theorem completedWeightedPrimeSamplingHilbertFrameBesselBound_of_diagonalDebtCoordinate_re_hasSum_source
    (f : ZetaAdmissibleFunction) (C : ℝ)
    (hhasSum :
      HasSum
        (fun index : ZetaPrimePowerIndex =>
          Complex.re
            (zetaCompletedPrimeDefectKernelDiagonalDebtCoordinate index f))
        C) :
    ∃ B : ℝ,
      CompletedWeightedPrimeSamplingHilbertFrameBesselBound f B :=
  match
    completedAutocorrelationSpectralTransform_weightedPrimeSampling_finiteSubtrace_hilbertFrame_of_diagonalDebtCoordinate_re_hasSum_source
      f C hhasSum with
  | ⟨B, hB⟩ =>
      ⟨B, hB⟩

/-- A diagonal-debt real-coordinate `HasSum` gives summability of the completed
weighted prime-center sampling stream through finite-subtrace Bessel
domination. -/
theorem completedWeightedPrimeSampling_summable_hilbertFrame_of_diagonalDebtCoordinate_re_hasSum_source
    (f : ZetaAdmissibleFunction) (C : ℝ)
    (hhasSum :
      HasSum
        (fun index : ZetaPrimePowerIndex =>
          Complex.re
            (zetaCompletedPrimeDefectKernelDiagonalDebtCoordinate index f))
        C) :
    Summable
      (fun index : ZetaPrimePowerIndex =>
        completedAutocorrelationSpectralTransform_weightedPrimeSampling
          index f) :=
  match
    completedWeightedPrimeSamplingHilbertFrameBesselBound_of_diagonalDebtCoordinate_re_hasSum_source
      f C hhasSum with
  | ⟨B, hB⟩ =>
      let hnonnegative :
          0 ≤
            fun index : ZetaPrimePowerIndex =>
              completedAutocorrelationSpectralTransform_weightedPrimeSampling
                index f :=
        fun index : ZetaPrimePowerIndex =>
          completedAutocorrelationSpectralTransform_weightedPrimeSampling_nonnegative
            index f
      summable_of_sum_le hnonnegative hB

/-- A diagonal-debt real-coordinate `HasSum` reconstructs the completed
weighted prime-center sampling stream at its raw `tsum`. -/
theorem completedWeightedPrimeSampling_hasSum_tsum_hilbertFrame_of_diagonalDebtCoordinate_re_hasSum_source
    (f : ZetaAdmissibleFunction) (C : ℝ)
    (hhasSum :
      HasSum
        (fun index : ZetaPrimePowerIndex =>
          Complex.re
            (zetaCompletedPrimeDefectKernelDiagonalDebtCoordinate index f))
        C) :
    HasSum
      (fun index : ZetaPrimePowerIndex =>
        completedAutocorrelationSpectralTransform_weightedPrimeSampling
          index f)
      (∑' index : ZetaPrimePowerIndex,
        completedAutocorrelationSpectralTransform_weightedPrimeSampling
          index f) :=
  (completedWeightedPrimeSampling_summable_hilbertFrame_of_diagonalDebtCoordinate_re_hasSum_source
    f C hhasSum).hasSum

end ZetaAdmissibleFunction

end
end LFunctions
end Boundary
