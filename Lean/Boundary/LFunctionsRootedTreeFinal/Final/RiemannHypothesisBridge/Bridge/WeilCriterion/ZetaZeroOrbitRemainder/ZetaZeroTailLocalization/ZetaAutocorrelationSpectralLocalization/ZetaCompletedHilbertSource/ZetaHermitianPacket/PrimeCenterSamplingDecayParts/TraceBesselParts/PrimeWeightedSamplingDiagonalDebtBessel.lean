import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaCompletedHilbertSource.ZetaHermitianPacket.PrimeCenterSamplingDecayParts.TraceBesselParts.PrimeWeightedSamplingBesselCore

/-!
# Prime weighted sampling diagonal-debt domination

This file owns only the pointwise and genuine-window domination of the
positive completed prime face by the completed diagonal-debt real window.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open scoped BigOperators

namespace ZetaAdmissibleFunction

/-- A positive completed prime face coordinate is bounded by its completed
diagonal-debt coordinate real scalar. -/
theorem zetaCompletedPrimeSpectralAmplitudeIndex_normSq_le_diagonalDebtCoordinate_re_traceEnergy_source
    (index : ZetaPrimePowerIndex) (f : ZetaAdmissibleFunction) :
    ‖zetaCompletedPrimeSpectralAmplitudeIndex index f‖ ^ 2 ≤
      Complex.re
        (zetaCompletedPrimeDefectKernelDiagonalDebtCoordinate index f) :=
  zetaCompletedPrimeSpectralAmplitudeIndex_normSq_le_diagonalDebtCoordinate_re_traceBessel
    index f

/-- A positive completed prime face window is bounded by the completed
diagonal-debt real window. -/
theorem zetaCompletedPrimeSpectralAmplitudeIndex_normSq_windowSubtrace_le_diagonalDebtRealWindow_traceEnergy_source
    (N : ℕ) (f : ZetaAdmissibleFunction) :
    (∑ index in ZetaPrimePowerIndex.window N,
      ‖zetaCompletedPrimeSpectralAmplitudeIndex index f‖ ^ 2) ≤
      zetaCompletedPrimeDefectKernelDiagonalDebtRealWindow N f :=
  zetaCompletedPrimeSpectralAmplitudeIndex_normSq_windowSubtrace_le_diagonalDebtRealWindow_traceBessel
    N f

/-- A reconstructed nonnegative diagonal-debt real-coordinate sum uniformly
dominates the positive completed prime spectral-amplitude windows. -/
theorem zetaCompletedPrimeSpectralAmplitudeIndex_normSq_windowSubtrace_bessel_of_diagonalDebtCoordinate_re_hasSum_traceEnergy_source
    (f : ZetaAdmissibleFunction) (C : ℝ)
    (hhasSum :
      HasSum
        (fun index : ZetaPrimePowerIndex =>
          Complex.re
            (zetaCompletedPrimeDefectKernelDiagonalDebtCoordinate index f))
        C) :
    ∀ N : ℕ,
      (∑ index in ZetaPrimePowerIndex.window N,
        ‖zetaCompletedPrimeSpectralAmplitudeIndex index f‖ ^ 2) ≤ C :=
  fun N =>
  let hdiagonal_nonnegative :
      ∀ index : ZetaPrimePowerIndex,
        0 ≤
          Complex.re
            (zetaCompletedPrimeDefectKernelDiagonalDebtCoordinate index f) :=
    fun index =>
      zetaCompletedPrimeDefectKernelDiagonalDebtCoordinate_re_nonnegative
        index f
  let hrealWindow_le :
      zetaCompletedPrimeDefectKernelDiagonalDebtRealWindow N f ≤ C :=
    let hsum :
        (∑ index in ZetaPrimePowerIndex.window N,
          Complex.re
            (zetaCompletedPrimeDefectKernelDiagonalDebtCoordinate index f)) ≤
          C :=
      sum_le_hasSum
        (ZetaPrimePowerIndex.window N)
        (fun index membership => hdiagonal_nonnegative index)
        hhasSum
    let hrealWindow :
        zetaCompletedPrimeDefectKernelDiagonalDebtRealWindow N f =
          ∑ index in ZetaPrimePowerIndex.window N,
            Complex.re
              (zetaCompletedPrimeDefectKernelDiagonalDebtCoordinate index f) :=
      zetaCompletedPrimeDefectKernelDiagonalDebtRealWindow_eq_sum_re_traceBessel
        N f
    Eq.subst
      (motive := fun value : ℝ => value ≤ C)
      hrealWindow.symm
      hsum
  le_trans
    (zetaCompletedPrimeSpectralAmplitudeIndex_normSq_windowSubtrace_le_diagonalDebtRealWindow_traceEnergy_source
      N f)
    hrealWindow_le

/-- A reconstructed nonnegative diagonal-debt real-coordinate sum uniformly
dominates the rectangular-box positive completed prime spectral-amplitude
subtraces. -/
theorem zetaCompletedPrimeSpectralAmplitudeIndex_normSq_boxSubtrace_bessel_of_diagonalDebtCoordinate_re_hasSum_traceEnergy_source
    (f : ZetaAdmissibleFunction) (C : ℝ)
    (hhasSum :
      HasSum
        (fun index : ZetaPrimePowerIndex =>
          Complex.re
            (zetaCompletedPrimeDefectKernelDiagonalDebtCoordinate index f))
        C) :
    ∀ N : ℕ,
      (∑ index in ZetaPrimePowerIndex.box N,
        ‖zetaCompletedPrimeSpectralAmplitudeIndex index f‖ ^ 2) ≤ C :=
  fun N =>
  let hboxWindow :
      (∑ index in ZetaPrimePowerIndex.box N,
        ‖zetaCompletedPrimeSpectralAmplitudeIndex index f‖ ^ 2) =
        ∑ index in ZetaPrimePowerIndex.window N,
          ‖zetaCompletedPrimeSpectralAmplitudeIndex index f‖ ^ 2 :=
    ZetaPrimePowerIndex.sum_box_eq_sum_window_of_zero_not_isGenuine
      (fun index : ZetaPrimePowerIndex =>
        ‖zetaCompletedPrimeSpectralAmplitudeIndex index f‖ ^ 2)
      (fun index hindex =>
        zetaCompletedPrimeSpectralAmplitudeIndex_normSq_eq_zero_of_not_isGenuine_traceBessel
          index f hindex)
      N
  let hwindow :
      (∑ index in ZetaPrimePowerIndex.window N,
        ‖zetaCompletedPrimeSpectralAmplitudeIndex index f‖ ^ 2) ≤ C :=
    zetaCompletedPrimeSpectralAmplitudeIndex_normSq_windowSubtrace_bessel_of_diagonalDebtCoordinate_re_hasSum_traceEnergy_source
      f C hhasSum N
  Eq.subst
    (motive := fun value : ℝ => value ≤ C)
    hboxWindow.symm
    hwindow

/-- A reconstructed nonnegative diagonal-debt real-coordinate sum uniformly
dominates all finite positive completed prime spectral-amplitude subtraces. -/
theorem zetaCompletedPrimeSpectralAmplitudeIndex_normSq_finiteSubtrace_bessel_of_diagonalDebtCoordinate_re_hasSum_traceEnergy_source
    (f : ZetaAdmissibleFunction) (C : ℝ)
    (hhasSum :
      HasSum
        (fun index : ZetaPrimePowerIndex =>
          Complex.re
            (zetaCompletedPrimeDefectKernelDiagonalDebtCoordinate index f))
        C) :
    ∀ s : Finset ZetaPrimePowerIndex,
      (∑ index in s,
        ‖zetaCompletedPrimeSpectralAmplitudeIndex index f‖ ^ 2) ≤ C :=
  fun s =>
  let hcontainsEventually :
      ∀ᶠ N in Filter.atTop,
        s ≤ ZetaPrimePowerIndex.box N :=
    ZetaPrimePowerIndex.box_tendsto_atTop.eventually
      (Filter.eventually_ge_atTop s)
  match hcontainsEventually.exists with
  | ⟨N, hfiniteBox⟩ =>
      let hsubset :
          s ⊆ ZetaPrimePowerIndex.box N :=
        hfiniteBox
      let hfinite_le_box :
          (∑ index in s,
            ‖zetaCompletedPrimeSpectralAmplitudeIndex index f‖ ^ 2) ≤
            ∑ index in ZetaPrimePowerIndex.box N,
              ‖zetaCompletedPrimeSpectralAmplitudeIndex index f‖ ^ 2 :=
        Finset.sum_le_sum_of_subset_of_nonneg
          hsubset
          (fun index boxMembership outsideMembership =>
            sq_nonneg ‖zetaCompletedPrimeSpectralAmplitudeIndex index f‖)
      le_trans hfinite_le_box
        (zetaCompletedPrimeSpectralAmplitudeIndex_normSq_boxSubtrace_bessel_of_diagonalDebtCoordinate_re_hasSum_traceEnergy_source
          f C hhasSum N)

/-- A reconstructed nonnegative diagonal-debt real-coordinate sum uniformly
dominates all finite completed weighted prime-center sampling subtraces. -/
theorem completedAutocorrelationSpectralTransform_weightedPrimeSampling_finiteSubtrace_bessel_of_diagonalDebtCoordinate_re_hasSum_traceEnergy_source
    (f : ZetaAdmissibleFunction) (C : ℝ)
    (hhasSum :
      HasSum
        (fun index : ZetaPrimePowerIndex =>
          Complex.re
            (zetaCompletedPrimeDefectKernelDiagonalDebtCoordinate index f))
        C) :
    ∀ s : Finset ZetaPrimePowerIndex,
      (∑ index in s,
        completedAutocorrelationSpectralTransform_weightedPrimeSampling
          index f) ≤ C :=
  fun s =>
  let hamplitude :
      (∑ index in s,
        ‖zetaCompletedPrimeSpectralAmplitudeIndex index f‖ ^ 2) ≤ C :=
    zetaCompletedPrimeSpectralAmplitudeIndex_normSq_finiteSubtrace_bessel_of_diagonalDebtCoordinate_re_hasSum_traceEnergy_source
      f C hhasSum s
  let hcoordinate :
      (∑ index in s,
        completedAutocorrelationSpectralTransform_weightedPrimeSampling
          index f) =
        ∑ index in s,
          ‖zetaCompletedPrimeSpectralAmplitudeIndex index f‖ ^ 2 :=
    Finset.sum_congr
      (Eq.refl s)
      (fun index membership =>
        (Eq.trans
          (zetaCompletedPrimeSpectralAmplitudeIndex_norm_sq_eq_weightedSampleNormSq
            index f)
          (zetaCompletedPrimePositiveWeightedSampleNormSq_eq_weightedPrimeSampling
            index f)).symm)
  Eq.subst
    (motive := fun value : ℝ => value ≤ C)
    hcoordinate.symm
    hamplitude

/-- A reconstructed nonnegative diagonal-debt real-coordinate sum gives a
finite-subtrace Bessel package for completed weighted prime-center sampling. -/
theorem completedAutocorrelationSpectralTransform_weightedPrimeSampling_finiteSubtrace_bessel_exists_of_diagonalDebtCoordinate_re_hasSum_traceEnergy_source
    (f : ZetaAdmissibleFunction) (C : ℝ)
    (hhasSum :
      HasSum
        (fun index : ZetaPrimePowerIndex =>
          Complex.re
            (zetaCompletedPrimeDefectKernelDiagonalDebtCoordinate index f))
        C) :
    ∃ B : ℝ,
      ∀ s : Finset ZetaPrimePowerIndex,
        (∑ index in s,
          completedAutocorrelationSpectralTransform_weightedPrimeSampling
            index f) ≤ B :=
  Exists.intro C
    (completedAutocorrelationSpectralTransform_weightedPrimeSampling_finiteSubtrace_bessel_of_diagonalDebtCoordinate_re_hasSum_traceEnergy_source
      f C hhasSum)

end ZetaAdmissibleFunction

end
end LFunctions
end Boundary
