import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaCompletedHilbertSource.ZetaHermitianPacket.CompletedPrimePowerSampling

/-!
# Prime-amplitude finite-subtrace transport

This file owns the acyclic finite-subtrace transport from completed weighted
prime-center sampling to positive completed prime spectral-amplitude squares.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open scoped BigOperators

namespace ZetaAdmissibleFunction

/-- Pointwise transport from positive completed prime spectral-amplitude
norm-square to completed weighted prime-center sampling. -/
theorem zetaCompletedPrimeSpectralAmplitudeIndex_normSq_eq_weightedPrimeSampling_finiteSubtraceTransport
    (index : ZetaPrimePowerIndex) (f : ZetaAdmissibleFunction) :
    ‖zetaCompletedPrimeSpectralAmplitudeIndex index f‖ ^ 2 =
      completedAutocorrelationSpectralTransform_weightedPrimeSampling
        index f :=
  (zetaCompletedPrimeSpectralAmplitudeIndex_norm_sq_eq_weightedSampleNormSq
    index f).trans
    (zetaCompletedPrimePositiveWeightedSampleNormSq_eq_weightedPrimeSampling
      index f)

/-- Finite sums of positive completed prime spectral-amplitude norm-squares
transport to finite completed weighted prime-center sampling sums. -/
theorem zetaCompletedPrimeSpectralAmplitudeIndex_normSq_finiteSubtrace_eq_weightedPrimeSampling_finiteSubtraceTransport
    (s : Finset ZetaPrimePowerIndex) (f : ZetaAdmissibleFunction) :
    (∑ index in s,
      ‖zetaCompletedPrimeSpectralAmplitudeIndex index f‖ ^ 2) =
      ∑ index in s,
        completedAutocorrelationSpectralTransform_weightedPrimeSampling
          index f :=
  Finset.sum_congr
    (Eq.refl s)
    (fun index membership =>
      zetaCompletedPrimeSpectralAmplitudeIndex_normSq_eq_weightedPrimeSampling_finiteSubtraceTransport
        index f)

/-- A finite-subtrace Bessel bound for completed weighted prime-center
sampling gives the corresponding finite-subtrace Bessel bound for positive
completed prime spectral-amplitude squares. -/
theorem zetaCompletedPrimeSpectralAmplitudeIndex_normSq_finiteSubtrace_bessel_of_weightedPrimeSampling_finiteSubtrace_bessel
    (f : ZetaAdmissibleFunction) (C : ℝ)
    (hC :
      ∀ s : Finset ZetaPrimePowerIndex,
        ∑ index in s,
          completedAutocorrelationSpectralTransform_weightedPrimeSampling
            index f ≤ C) :
    ∀ s : Finset ZetaPrimePowerIndex,
      ∑ index in s,
        ‖zetaCompletedPrimeSpectralAmplitudeIndex index f‖ ^ 2 ≤ C :=
  fun s =>
  Eq.subst
    (motive := fun value : ℝ => value ≤ C)
    (zetaCompletedPrimeSpectralAmplitudeIndex_normSq_finiteSubtrace_eq_weightedPrimeSampling_finiteSubtraceTransport
      s f).symm
    (hC s)

/-- Existential finite-subtrace Bessel transport from completed weighted
prime-center sampling to positive completed prime spectral-amplitude squares. -/
theorem zetaCompletedPrimeSpectralAmplitudeIndex_normSq_finiteSubtrace_bessel_exists_of_weightedPrimeSampling_finiteSubtrace_bessel_exists
    (f : ZetaAdmissibleFunction)
    (hweighted :
      ∃ C : ℝ,
        ∀ s : Finset ZetaPrimePowerIndex,
          ∑ index in s,
            completedAutocorrelationSpectralTransform_weightedPrimeSampling
              index f ≤ C) :
    ∃ C : ℝ,
      ∀ s : Finset ZetaPrimePowerIndex,
        ∑ index in s,
          ‖zetaCompletedPrimeSpectralAmplitudeIndex index f‖ ^ 2 ≤ C :=
  match hweighted with
  | ⟨C, hC⟩ =>
      Exists.intro C
        (zetaCompletedPrimeSpectralAmplitudeIndex_normSq_finiteSubtrace_bessel_of_weightedPrimeSampling_finiteSubtrace_bessel
          f C hC)

end ZetaAdmissibleFunction

end
end LFunctions
end Boundary
