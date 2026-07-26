import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaCompletedHilbertSource.ZetaHermitianPacket.PrimeCenterSamplingDecayParts.TraceBesselParts.PrimeAmplitudeFrameBessel

/-!
# Prime-center Hilbert sampling Bessel source

This file owns the Hilbert-source Bessel estimate for genuine prime-center
sampling windows.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open scoped BigOperators

namespace ZetaAdmissibleFunction

/-- Hilbert-source Bessel domination for the completed prime spectral amplitude
evaluation windows. -/
theorem zetaCompletedPrimeSpectralAmplitudeIndex_normSq_window_bessel_hilbertSampling_source
    (f : ZetaAdmissibleFunction) :
    ∃ C : ℝ,
      ∀ N : ℕ,
        ∑ index in ZetaPrimePowerIndex.window N,
          ‖zetaCompletedPrimeSpectralAmplitudeIndex index f‖ ^ 2 ≤ C :=
  zetaCompletedPrimeSpectralAmplitudeIndex_normSq_window_bessel_frame_source f

theorem zetaCompletedPrimePositiveWeightedSampleNormSq_window_eq_amplitudeNormSq_window
    (f : ZetaAdmissibleFunction) (N : ℕ) :
    (∑ index in ZetaPrimePowerIndex.window N,
      zetaCompletedPrimePositiveWeightedSampleNormSq index f) =
      ∑ index in ZetaPrimePowerIndex.window N,
        ‖zetaCompletedPrimeSpectralAmplitudeIndex index f‖ ^ 2 :=
  Finset.sum_congr
    (Eq.refl (ZetaPrimePowerIndex.window N))
    (fun index membership =>
      (zetaCompletedPrimeSpectralAmplitudeIndex_norm_sq_eq_weightedSampleNormSq
        index f).symm)

theorem zetaCompletedPrimePositiveWeightedSampleNormSq_window_bound_of_amplitudeNormSq_window_bound
    (f : ZetaAdmissibleFunction) (C : ℝ)
    (hC :
      ∀ N : ℕ,
        ∑ index in ZetaPrimePowerIndex.window N,
          ‖zetaCompletedPrimeSpectralAmplitudeIndex index f‖ ^ 2 ≤ C) :
    ∀ N : ℕ,
      ∑ index in ZetaPrimePowerIndex.window N,
        zetaCompletedPrimePositiveWeightedSampleNormSq index f ≤ C :=
  fun N =>
    Eq.subst
      (motive := fun value : ℝ => value ≤ C)
      (zetaCompletedPrimePositiveWeightedSampleNormSq_window_eq_amplitudeNormSq_window
        f N).symm
      (hC N)

/-- Hilbert-source Bessel domination for the positive completed weighted prime
sample-square windows. -/
theorem zetaCompletedPrimePositiveWeightedSampleNormSq_window_bessel_hilbertSampling_source
    (f : ZetaAdmissibleFunction) :
    ∃ C : ℝ,
      ∀ N : ℕ,
        ∑ index in ZetaPrimePowerIndex.window N,
          zetaCompletedPrimePositiveWeightedSampleNormSq index f ≤ C :=
  match
    zetaCompletedPrimeSpectralAmplitudeIndex_normSq_window_bessel_hilbertSampling_source
      f with
  | ⟨C, hC⟩ =>
      Exists.intro C
        (zetaCompletedPrimePositiveWeightedSampleNormSq_window_bound_of_amplitudeNormSq_window_bound
          f C hC)

end ZetaAdmissibleFunction

end
end LFunctions
end Boundary
