import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaCompletedHilbertSource.ZetaHermitianPacket.PrimeCenterSamplingDecayParts.TraceBesselParts.PrimeWeightedSamplingDiagonalDebtBessel
import Mathlib.Topology.Algebra.InfiniteSum.Order

/-!
# Prime weighted sampling diagonal-debt majorants

This file owns the summability consequences that follow directly from
completed diagonal-debt real-coordinate `HasSum` inputs.
-/

namespace Boundary
namespace LFunctions

noncomputable section

namespace ZetaAdmissibleFunction

/-- A diagonal-debt real-coordinate `HasSum` gives summability of the
positive completed prime spectral-amplitude square stream. -/
theorem zetaCompletedPrimeSpectralAmplitudeIndex_normSq_summable_of_diagonalDebtCoordinate_re_hasSum_traceEnergy_free_source
    (f : ZetaAdmissibleFunction) (C : ℝ)
    (hhasSum :
      HasSum
        (fun index : ZetaPrimePowerIndex =>
          Complex.re
            (zetaCompletedPrimeDefectKernelDiagonalDebtCoordinate index f))
        C) :
    Summable
      (fun index : ZetaPrimePowerIndex =>
        ‖zetaCompletedPrimeSpectralAmplitudeIndex index f‖ ^ 2) :=
  let hnonnegative :
      0 ≤
        fun index : ZetaPrimePowerIndex =>
          ‖zetaCompletedPrimeSpectralAmplitudeIndex index f‖ ^ 2 :=
    fun index =>
      sq_nonneg
        ‖zetaCompletedPrimeSpectralAmplitudeIndex index f‖
  let hfinite :
      ∀ s : Finset ZetaPrimePowerIndex,
        (∑ index in s,
          ‖zetaCompletedPrimeSpectralAmplitudeIndex index f‖ ^ 2) ≤ C :=
    zetaCompletedPrimeSpectralAmplitudeIndex_normSq_finiteSubtrace_bessel_of_diagonalDebtCoordinate_re_hasSum_traceEnergy_source
      f C hhasSum
  summable_of_sum_le hnonnegative hfinite

theorem zetaCompletedPrimeSpectralAmplitudeIndex_reflect_normSq_eq_opposite_normSq_traceEnergy_free_source
    (f : ZetaAdmissibleFunction) (index : ZetaPrimePowerIndex) :
    ‖zetaCompletedPrimeSpectralAmplitudeIndex index
        (ZetaAdmissibleFunction.reflect f)‖ ^ 2 =
      ‖zetaCompletedPrimeOppositeSpectralAmplitudeIndex index f‖ ^ 2 :=
  let hpositiveNorm :
      ‖zetaCompletedPrimeSpectralAmplitudeIndex index
          (ZetaAdmissibleFunction.reflect f)‖ ^ 2 =
        zetaCompletedPrimePositiveWeightedSampleNormSq index
          (ZetaAdmissibleFunction.reflect f) :=
    zetaCompletedPrimeSpectralAmplitudeIndex_norm_sq_eq_weightedSampleNormSq
      index (ZetaAdmissibleFunction.reflect f)
  let hreflect :
      zetaCompletedPrimePositiveWeightedSampleNormSq index
          (ZetaAdmissibleFunction.reflect f) =
        zetaCompletedPrimeOppositeWeightedSampleNormSq index f :=
    (zetaCompletedPrimeOppositeWeightedSampleNormSq_eq_positive_reflect
      index f).symm
  let hoppositeNorm :
      zetaCompletedPrimeOppositeWeightedSampleNormSq index f =
        ‖zetaCompletedPrimeOppositeSpectralAmplitudeIndex index f‖ ^ 2 :=
    (zetaCompletedPrimeOppositeSpectralAmplitudeIndex_norm_sq_eq_weightedSampleNormSq
      index f).symm
  hpositiveNorm.trans (hreflect.trans hoppositeNorm)

/-- A reflected diagonal-debt real-coordinate `HasSum` gives summability of
the opposite completed prime spectral-amplitude square stream. -/
theorem zetaCompletedPrimeOppositeSpectralAmplitudeIndex_normSq_summable_of_reflect_diagonalDebtCoordinate_re_hasSum_traceEnergy_free_source
    (f : ZetaAdmissibleFunction) (C : ℝ)
    (hhasSum :
      HasSum
        (fun index : ZetaPrimePowerIndex =>
          Complex.re
            (zetaCompletedPrimeDefectKernelDiagonalDebtCoordinate
              index (ZetaAdmissibleFunction.reflect f)))
        C) :
    Summable
      (fun index : ZetaPrimePowerIndex =>
        ‖zetaCompletedPrimeOppositeSpectralAmplitudeIndex index f‖ ^ 2) :=
  let hpositiveReflect :
      Summable
        (fun index : ZetaPrimePowerIndex =>
          ‖zetaCompletedPrimeSpectralAmplitudeIndex index
              (ZetaAdmissibleFunction.reflect f)‖ ^ 2) :=
    zetaCompletedPrimeSpectralAmplitudeIndex_normSq_summable_of_diagonalDebtCoordinate_re_hasSum_traceEnergy_free_source
      (ZetaAdmissibleFunction.reflect f) C hhasSum
  hpositiveReflect.congr
    (fun index : ZetaPrimePowerIndex =>
      zetaCompletedPrimeSpectralAmplitudeIndex_reflect_normSq_eq_opposite_normSq_traceEnergy_free_source
        f index)

theorem zetaCompletedPrimeSpectralCoordinateMajorant_eq_normSq_add_normSq_traceEnergy_free_source
    (f : ZetaAdmissibleFunction) (index : ZetaPrimePowerIndex) :
    ‖zetaCompletedPrimeSpectralAmplitudeIndex index f‖ ^ 2 +
        ‖zetaCompletedPrimeOppositeSpectralAmplitudeIndex index f‖ ^ 2 =
      zetaCompletedPrimeSpectralCoordinateMajorant index f :=
  Eq.refl
    (zetaCompletedPrimeSpectralCoordinateMajorant index f)

/-- Diagonal-debt real-coordinate `HasSum` inputs for a probe and its
reflected probe give summability of the completed prime spectral-coordinate
majorant. -/
theorem zetaCompletedPrimeSpectralCoordinateMajorant_summable_of_diagonalDebtCoordinate_re_hasSum_traceEnergy_free_source
    (f : ZetaAdmissibleFunction) (C Creflect : ℝ)
    (hhasSum :
      HasSum
        (fun index : ZetaPrimePowerIndex =>
          Complex.re
            (zetaCompletedPrimeDefectKernelDiagonalDebtCoordinate index f))
        C)
    (hhasSumReflect :
      HasSum
        (fun index : ZetaPrimePowerIndex =>
          Complex.re
            (zetaCompletedPrimeDefectKernelDiagonalDebtCoordinate
              index (ZetaAdmissibleFunction.reflect f)))
        Creflect) :
    Summable
      (fun index : ZetaPrimePowerIndex =>
        zetaCompletedPrimeSpectralCoordinateMajorant index f) :=
  let hpositive :
      Summable
        (fun index : ZetaPrimePowerIndex =>
          ‖zetaCompletedPrimeSpectralAmplitudeIndex index f‖ ^ 2) :=
    zetaCompletedPrimeSpectralAmplitudeIndex_normSq_summable_of_diagonalDebtCoordinate_re_hasSum_traceEnergy_free_source
      f C hhasSum
  let hopposite :
      Summable
        (fun index : ZetaPrimePowerIndex =>
          ‖zetaCompletedPrimeOppositeSpectralAmplitudeIndex index f‖ ^ 2) :=
    zetaCompletedPrimeOppositeSpectralAmplitudeIndex_normSq_summable_of_reflect_diagonalDebtCoordinate_re_hasSum_traceEnergy_free_source
      f Creflect hhasSumReflect
  (hpositive.add hopposite).congr
    (fun index : ZetaPrimePowerIndex =>
      zetaCompletedPrimeSpectralCoordinateMajorant_eq_normSq_add_normSq_traceEnergy_free_source
        f index)

end ZetaAdmissibleFunction

end
end LFunctions
end Boundary
