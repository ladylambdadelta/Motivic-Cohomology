import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaCompletedHilbertSource.ZetaHermitianPacket.CompletedPrimeDiagonalDebtWindowOwnerParts.PrimeAmplitudeBesselSourceParts.FiniteSubtrace
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaCompletedHilbertSource.ZetaHermitianPacket.PrimeCenterSamplingDecayParts.TraceBesselParts.PrimeAmplitudeFiniteSubtraceTransport

/-!
# Completed prime amplitude Bessel source

This file owns the forward finite-subtrace Bessel estimate for the completed
prime spectral amplitude sample stream.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open scoped BigOperators

namespace ZetaAdmissibleFunction

/-- The finite projection energy of completed weighted prime sampling over a
finite prime-power coordinate family. -/
noncomputable def completedAutocorrelationSpectralTransform_weightedPrimeSamplingProjectionEnergy_besselSource
    (s : Finset ZetaPrimePowerIndex) (f : ZetaAdmissibleFunction) : ℝ :=
  ∑ index in s,
    completedAutocorrelationSpectralTransform_weightedPrimeSampling
      index f

/-- The finite projection energy unfolds to the finite weighted sampling
subtrace. -/
theorem completedAutocorrelationSpectralTransform_weightedPrimeSamplingProjectionEnergy_eq_sum_besselSource
    (s : Finset ZetaPrimePowerIndex) (f : ZetaAdmissibleFunction) :
    completedAutocorrelationSpectralTransform_weightedPrimeSamplingProjectionEnergy_besselSource
        s f =
      ∑ index in s,
        completedAutocorrelationSpectralTransform_weightedPrimeSampling
          index f :=
  Eq.refl
    (completedAutocorrelationSpectralTransform_weightedPrimeSamplingProjectionEnergy_besselSource
      s f)

/-- A scalar upper bound for all finite completed weighted prime-sampling
projection energies. -/
def CompletedAutocorrelationSpectralTransformWeightedPrimeSamplingProjectionEnergyUpperBound_besselSource
    (f : ZetaAdmissibleFunction) (C : ℝ) : Prop :=
  ∀ s : Finset ZetaPrimePowerIndex,
    completedAutocorrelationSpectralTransform_weightedPrimeSamplingProjectionEnergy_besselSource
      s f ≤ C

/-- Analytic source finite-subtrace Bessel domination for completed weighted
prime sampling. -/
theorem completedAutocorrelationSpectralTransform_weightedPrimeSampling_finiteSubtrace_bessel_source_analytic
    (f : ZetaAdmissibleFunction) :
    ∃ C : ℝ,
      ∀ s : Finset ZetaPrimePowerIndex,
        ∑ index in s,
          completedAutocorrelationSpectralTransform_weightedPrimeSampling
            index f ≤ C :=
  completedAutocorrelationSpectralTransform_weightedPrimeSampling_finiteSubtrace_hilbertFrame_source
    f

/-- Analytic source Bessel domination for finite completed weighted
prime-sampling projection energies. -/
theorem completedAutocorrelationSpectralTransform_weightedPrimeSamplingProjectionEnergy_upperBound_besselSource_analytic
    (f : ZetaAdmissibleFunction) :
    ∃ C : ℝ,
      CompletedAutocorrelationSpectralTransformWeightedPrimeSamplingProjectionEnergyUpperBound_besselSource
        f C :=
  match
    completedAutocorrelationSpectralTransform_weightedPrimeSampling_finiteSubtrace_bessel_source_analytic
      f with
  | ⟨C, hC⟩ =>
      let hprojection :
          CompletedAutocorrelationSpectralTransformWeightedPrimeSamplingProjectionEnergyUpperBound_besselSource
            f C :=
        fun s : Finset ZetaPrimePowerIndex =>
          Eq.subst
          (motive := fun value : ℝ => value ≤ C)
          (completedAutocorrelationSpectralTransform_weightedPrimeSamplingProjectionEnergy_eq_sum_besselSource
            s f).symm
          (hC s)
      ⟨C, hprojection⟩

/-- Public finite-subtrace Bessel source for completed weighted prime
sampling. -/
theorem completedAutocorrelationSpectralTransform_weightedPrimeSampling_finiteSubtrace_bessel_source
    (f : ZetaAdmissibleFunction) :
    ∃ C : ℝ,
      ∀ s : Finset ZetaPrimePowerIndex,
        ∑ index in s,
          completedAutocorrelationSpectralTransform_weightedPrimeSampling
            index f ≤ C :=
  completedAutocorrelationSpectralTransform_weightedPrimeSampling_finiteSubtrace_bessel_source_analytic
    f

/-- A diagonal-debt real-coordinate `HasSum` gives public finite-subtrace
Bessel domination for completed weighted prime sampling. -/
theorem completedAutocorrelationSpectralTransform_weightedPrimeSampling_finiteSubtrace_bessel_of_diagonalDebtCoordinate_re_hasSum_source
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
  completedAutocorrelationSpectralTransform_weightedPrimeSampling_finiteSubtrace_bessel_source
    f

/-- Analytic finite-subtrace Bessel source for completed prime spectral
amplitude samples. -/
theorem zetaCompletedPrimeSpectralAmplitudeIndex_normSq_finiteSubtrace_bessel_source
    (f : ZetaAdmissibleFunction) :
    ∃ C : ℝ,
      ∀ s : Finset ZetaPrimePowerIndex,
        ∑ index in s,
          ‖zetaCompletedPrimeSpectralAmplitudeIndex index f‖ ^ 2 ≤ C :=
  zetaCompletedPrimeSpectralAmplitudeIndex_normSq_finiteSubtrace_bessel_exists_of_weightedPrimeSampling_finiteSubtrace_bessel_exists
    f
    (completedAutocorrelationSpectralTransform_weightedPrimeSampling_finiteSubtrace_bessel_source
      f)

/-- A diagonal-debt real-coordinate `HasSum` gives public finite-subtrace
Bessel domination for completed prime spectral-amplitude norm squares. -/
theorem zetaCompletedPrimeSpectralAmplitudeIndex_normSq_finiteSubtrace_bessel_of_diagonalDebtCoordinate_re_hasSum_source
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
          ‖zetaCompletedPrimeSpectralAmplitudeIndex index f‖ ^ 2 ≤ B :=
  zetaCompletedPrimeSpectralAmplitudeIndex_normSq_finiteSubtrace_bessel_exists_of_weightedPrimeSampling_finiteSubtrace_bessel_exists
    f
    (completedAutocorrelationSpectralTransform_weightedPrimeSampling_finiteSubtrace_bessel_of_diagonalDebtCoordinate_re_hasSum_source
      f C hhasSum)

end ZetaAdmissibleFunction

end
end LFunctions
end Boundary
