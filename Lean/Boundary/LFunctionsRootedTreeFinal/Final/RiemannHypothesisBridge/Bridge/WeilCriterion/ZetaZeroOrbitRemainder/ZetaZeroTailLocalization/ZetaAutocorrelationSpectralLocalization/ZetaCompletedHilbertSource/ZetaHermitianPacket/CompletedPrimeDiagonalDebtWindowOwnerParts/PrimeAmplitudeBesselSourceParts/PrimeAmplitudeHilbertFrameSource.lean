import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaCompletedHilbertSource.ZetaHermitianPacket.CompletedPrimeDiagonalDebtWindowOwnerParts.PrimeAmplitudeBesselSourceParts.HilbertFrameBesselBound

/-!
# Completed prime amplitude Hilbert-frame source

This file owns the narrow Hilbert-frame summability wrappers for the completed
positive prime spectral amplitude coordinate family.
-/

namespace Boundary
namespace LFunctions

noncomputable section

namespace ZetaAdmissibleFunction

/-- Rectangular-box Bessel domination for the completed weighted prime
sampling stream. -/
def CompletedWeightedPrimeSamplingBoxBesselBound_hilbertTrace_source
    (f : ZetaAdmissibleFunction) : Prop :=
  ∃ C : ℝ,
    ∀ N : ℕ,
      ∑ index in ZetaPrimePowerIndex.box N,
        completedAutocorrelationSpectralTransform_weightedPrimeSampling
          index f ≤ C

/-- Finite-subtrace Bessel domination for the completed weighted prime
sampling stream. -/
def CompletedWeightedPrimeSamplingFiniteSubtraceBesselBound_hilbertTrace_source
    (f : ZetaAdmissibleFunction) : Prop :=
  ∃ C : ℝ,
    ∀ s : Finset ZetaPrimePowerIndex,
      ∑ index in s,
        completedAutocorrelationSpectralTransform_weightedPrimeSampling
          index f ≤ C

/-- A projection-energy upper bound gives the corresponding finite-sum upper
bound. -/
theorem completedWeightedPrimeSampling_finiteSum_le_of_projectionEnergy_le_hilbertTrace_source
    (f : ZetaAdmissibleFunction) (C : ℝ)
    (hC :
      ∀ s : Finset ZetaPrimePowerIndex,
        completedWeightedPrimeSamplingProjectionEnergy_hilbertFrame s f ≤ C) :
    ∀ s : Finset ZetaPrimePowerIndex,
      ∑ index in s,
        completedAutocorrelationSpectralTransform_weightedPrimeSampling
          index f ≤ C :=
  fun s : Finset ZetaPrimePowerIndex =>
    Eq.subst
      (motive := fun value : ℝ => value ≤ C)
      (completedWeightedPrimeSamplingProjectionEnergy_eq_sum_hilbertFrame
        s f)
      (hC s)

/-- A projection-energy upper bound gives the corresponding rectangular-box
finite-sum upper bound. -/
theorem completedWeightedPrimeSampling_boxSum_le_of_projectionEnergy_le_hilbertTrace_source
    (f : ZetaAdmissibleFunction) (C : ℝ)
    (hC :
      ∀ s : Finset ZetaPrimePowerIndex,
        completedWeightedPrimeSamplingProjectionEnergy_hilbertFrame s f ≤ C) :
    ∀ N : ℕ,
      ∑ index in ZetaPrimePowerIndex.box N,
        completedAutocorrelationSpectralTransform_weightedPrimeSampling
          index f ≤ C :=
  fun N : ℕ =>
    completedWeightedPrimeSampling_finiteSum_le_of_projectionEnergy_le_hilbertTrace_source
      f C hC (ZetaPrimePowerIndex.box N)

/-- Hilbert-frame rectangular-box source for the completed weighted prime
sampling stream. -/
theorem completedWeightedPrimeSampling_boxBesselBound_hilbertTrace_source
    (f : ZetaAdmissibleFunction) :
    CompletedWeightedPrimeSamplingBoxBesselBound_hilbertTrace_source
      f :=
  match completedWeightedPrimeSamplingHilbertFrameBesselBound_source f with
  | ⟨C, hC⟩ =>
      ⟨C,
        completedWeightedPrimeSampling_boxSum_le_of_projectionEnergy_le_hilbertTrace_source
          f C hC⟩

theorem completedWeightedPrimeSampling_boxBesselBound_of_spectralPolynomialBounds_hilbertTrace_source
    (f : ZetaAdmissibleFunction) (Cpos Cneg : ℝ) (kpos kneg : ℕ)
    (hpos : PrimeCenterSpectralPolynomialBound f Cpos kpos)
    (hneg : PrimeCenterSpectralPolynomialBound
      (ZetaAdmissibleFunction.reflect f) Cneg kneg) :
    CompletedWeightedPrimeSamplingBoxBesselBound_hilbertTrace_source f :=
  match completedWeightedPrimeSamplingHilbertFrameBesselBound_of_spectralPolynomialBounds_source
      f Cpos Cneg kpos kneg hpos hneg with
  | ⟨C, hC⟩ =>
      ⟨C,
        completedWeightedPrimeSampling_boxSum_le_of_projectionEnergy_le_hilbertTrace_source
          f C hC⟩

/-- Hilbert-frame finite-subtrace source for the completed weighted prime
sampling stream. -/
theorem completedWeightedPrimeSampling_finiteSubtraceBesselBound_hilbertTrace_source
    (f : ZetaAdmissibleFunction) :
    CompletedWeightedPrimeSamplingFiniteSubtraceBesselBound_hilbertTrace_source
      f :=
  match completedWeightedPrimeSamplingHilbertFrameBesselBound_source f with
  | ⟨C, hC⟩ =>
      ⟨C,
        completedWeightedPrimeSampling_finiteSum_le_of_projectionEnergy_le_hilbertTrace_source
          f C hC⟩

theorem completedWeightedPrimeSampling_finiteSubtraceBesselBound_of_spectralPolynomialBounds_hilbertTrace_source
    (f : ZetaAdmissibleFunction) (Cpos Cneg : ℝ) (kpos kneg : ℕ)
    (hpos : PrimeCenterSpectralPolynomialBound f Cpos kpos)
    (hneg : PrimeCenterSpectralPolynomialBound
      (ZetaAdmissibleFunction.reflect f) Cneg kneg) :
    CompletedWeightedPrimeSamplingFiniteSubtraceBesselBound_hilbertTrace_source
      f :=
  match completedWeightedPrimeSamplingHilbertFrameBesselBound_of_spectralPolynomialBounds_source
      f Cpos Cneg kpos kneg hpos hneg with
  | ⟨B, hB⟩ =>
      ⟨B,
        completedWeightedPrimeSampling_finiteSum_le_of_projectionEnergy_le_hilbertTrace_source
          f B hB⟩

/-- A finite-subtrace Bessel bound gives summability for the completed weighted
prime sampling stream. -/
theorem completedWeightedPrimeSampling_summable_of_finiteSubtraceBesselBound_hilbertTrace_source
    (f : ZetaAdmissibleFunction)
    (hbound :
      CompletedWeightedPrimeSamplingFiniteSubtraceBesselBound_hilbertTrace_source
        f) :
    Summable
      (fun index : ZetaPrimePowerIndex =>
        completedAutocorrelationSpectralTransform_weightedPrimeSampling
          index f) :=
  let hnonnegative :
      0 ≤
        fun index : ZetaPrimePowerIndex =>
          completedAutocorrelationSpectralTransform_weightedPrimeSampling
            index f :=
    fun index : ZetaPrimePowerIndex =>
      completedAutocorrelationSpectralTransform_weightedPrimeSampling_nonnegative
        index f
  match hbound with
  | ⟨C, hC⟩ =>
      summable_of_sum_le hnonnegative hC

/-- Hilbert-frame summability for the completed weighted prime sampling
stream.  This is a trace-positive Bessel theorem, not pointwise decay of the
Laplace transform on the positive real prime-center axis. -/
theorem completedWeightedPrimeSampling_summable_hilbertTrace_source
    (f : ZetaAdmissibleFunction) :
    Summable
      (fun index : ZetaPrimePowerIndex =>
        completedAutocorrelationSpectralTransform_weightedPrimeSampling
          index f) :=
  completedWeightedPrimeSampling_summable_of_finiteSubtraceBesselBound_hilbertTrace_source
    f
    (completedWeightedPrimeSampling_finiteSubtraceBesselBound_hilbertTrace_source
      f)

/-- Weighted prime sampling equals the norm-square of the positive completed
prime spectral amplitude coordinate. -/
theorem completedWeightedPrimeSampling_eq_amplitudeNormSq_hilbertTrace_source
    (index : ZetaPrimePowerIndex) (f : ZetaAdmissibleFunction) :
    completedAutocorrelationSpectralTransform_weightedPrimeSampling index f =
      ‖zetaCompletedPrimeSpectralAmplitudeIndex index f‖ ^ 2 :=
  (Eq.trans
    (zetaCompletedPrimeSpectralAmplitudeIndex_norm_sq_eq_weightedSampleNormSq
      index f)
    (zetaCompletedPrimePositiveWeightedSampleNormSq_eq_weightedPrimeSampling
      index f)).symm

/-- Hilbert-frame square-summability for the completed positive prime spectral
amplitude coordinate family. -/
theorem zetaCompletedPrimeSpectralAmplitudeIndex_normSq_summable_hilbertFrame_source
    (f : ZetaAdmissibleFunction) :
    Summable
      (fun index : ZetaPrimePowerIndex =>
        ‖zetaCompletedPrimeSpectralAmplitudeIndex index f‖ ^ 2) :=
  (completedWeightedPrimeSampling_summable_hilbertTrace_source
    f).congr
    (fun index : ZetaPrimePowerIndex =>
      completedWeightedPrimeSampling_eq_amplitudeNormSq_hilbertTrace_source
        index f)

theorem zetaCompletedPrimeSpectralAmplitudeIndex_normSq_summable_of_spectralPolynomialBound_hilbertFrame_source
    (f : ZetaAdmissibleFunction) (C : ℝ) (k : ℕ)
    (hbound : PrimeCenterSpectralPolynomialBound f C k) :
    Summable
      (fun index : ZetaPrimePowerIndex =>
        ‖zetaCompletedPrimeSpectralAmplitudeIndex index f‖ ^ 2) :=
  (completedWeightedPrimeSampling_summable_hilbertFrame_of_spectralPolynomialBound_source
    f C k hbound).congr
    (fun index : ZetaPrimePowerIndex =>
      completedWeightedPrimeSampling_eq_amplitudeNormSq_hilbertTrace_source
        index f)

end ZetaAdmissibleFunction

end
end LFunctions
end Boundary
