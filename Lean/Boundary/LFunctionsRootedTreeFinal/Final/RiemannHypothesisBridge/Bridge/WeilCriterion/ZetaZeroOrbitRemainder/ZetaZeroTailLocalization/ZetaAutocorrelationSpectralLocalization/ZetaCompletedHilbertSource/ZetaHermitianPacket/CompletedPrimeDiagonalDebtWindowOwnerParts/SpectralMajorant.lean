import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaCompletedHilbertSource.ZetaHermitianPacket.CompletedPrimePowerPackets
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaCompletedHilbertSource.ZetaHermitianPacket.CompletedPrimePowerSampling
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaCompletedHilbertSource.ZetaHermitianPacket.PrimeCenterSamplingDecayParts.TraceBesselParts.PrimeWeightedSamplingDiagonalDebtMajorant
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaCompletedHilbertSource.ZetaHermitianPacket.PrimeCenterSamplingDecayParts.TraceBesselParts.PrimeWeightedSamplingTraceEnergy
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaCompletedHilbertSource.ZetaHermitianPacket.PrimeSpectralMajorantSummability

/-!
# Spectral majorant source for completed prime diagonal debt

This file owns the face-square summability inputs used by the completed prime
diagonal-debt coordinate presentation.
-/

namespace Boundary
namespace LFunctions

noncomputable section

namespace ZetaAdmissibleFunction

/-- The completed prime spectral majorant unfolds to the sum of the two
face-amplitude square streams. -/
theorem zetaCompletedPrimeSpectralCoordinateMajorant_eq_normSq_add_normSq_diagonalDebt
    (index : ZetaPrimePowerIndex) (f : ZetaAdmissibleFunction) :
    zetaCompletedPrimeSpectralCoordinateMajorant index f =
      ‖zetaCompletedPrimeSpectralAmplitudeIndex index f‖ ^ 2 +
        ‖zetaCompletedPrimeOppositeSpectralAmplitudeIndex index f‖ ^ 2 :=
  Eq.refl (zetaCompletedPrimeSpectralCoordinateMajorant index f)

/-- Owner-level summability of the positive completed prime face-amplitude
square stream. -/
theorem zetaCompletedPrimeSpectralAmplitudeIndex_normSq_summable_diagonalDebt_owner
    (f : ZetaAdmissibleFunction) (C : ℝ) (k : ℕ)
    (hbound : PrimeCenterSpectralPolynomialBound f C k) :
    Summable
      (fun index : ZetaPrimePowerIndex =>
        ‖zetaCompletedPrimeSpectralAmplitudeIndex index f‖ ^ 2) :=
  zetaCompletedPrimeSpectralAmplitudeIndex_normSq_summable_traceEnergy_source
    f C k hbound

theorem zetaCompletedPrimeSpectralAmplitudeIndex_normSq_summable_of_spectralPolynomialBound_diagonalDebt_owner
    (f : ZetaAdmissibleFunction) (C : ℝ) (k : ℕ)
    (hbound : PrimeCenterSpectralPolynomialBound f C k) :
    Summable
      (fun index : ZetaPrimePowerIndex =>
        ‖zetaCompletedPrimeSpectralAmplitudeIndex index f‖ ^ 2) :=
  zetaCompletedPrimeSpectralAmplitudeIndex_normSq_summable_of_spectralPolynomialBound
    f C k hbound

theorem zetaCompletedPrimeOppositeSpectralAmplitudeIndex_normSq_summable_of_reflect_spectralPolynomialBound_diagonalDebt_owner
    (f : ZetaAdmissibleFunction) (C : ℝ) (k : ℕ)
    (hbound : PrimeCenterSpectralPolynomialBound
      (ZetaAdmissibleFunction.reflect f) C k) :
    Summable
      (fun index : ZetaPrimePowerIndex =>
        ‖zetaCompletedPrimeOppositeSpectralAmplitudeIndex index f‖ ^ 2) :=
  zetaCompletedPrimeOppositeSpectralAmplitudeIndex_normSq_summable_of_reflect_spectralPolynomialBound
    f C k hbound

theorem zetaCompletedPrimeSpectralCoordinateMajorant_summable_of_spectralPolynomialBounds_diagonalDebt_owner
    (f : ZetaAdmissibleFunction) (Cpos Cneg : ℝ) (kpos kneg : ℕ)
    (hpos : PrimeCenterSpectralPolynomialBound f Cpos kpos)
    (hneg : PrimeCenterSpectralPolynomialBound
      (ZetaAdmissibleFunction.reflect f) Cneg kneg) :
    Summable
      (fun index : ZetaPrimePowerIndex =>
        zetaCompletedPrimeSpectralCoordinateMajorant index f) :=
  zetaCompletedPrimeSpectralCoordinateMajorant_summable_of_spectralPolynomialBounds
    f Cpos kpos Cneg kneg hpos hneg

/-- Reflection identifies the positive face-square stream with the opposite
face-square stream pointwise. -/
theorem zetaCompletedPrimeSpectralAmplitudeIndex_reflect_normSq_eq_opposite_normSq
    (index : ZetaPrimePowerIndex) (f : ZetaAdmissibleFunction) :
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

/-- Owner-level summability of the opposite completed prime face-amplitude
square stream. -/
theorem zetaCompletedPrimeOppositeSpectralAmplitudeIndex_normSq_summable_diagonalDebt_owner
    (f : ZetaAdmissibleFunction) (C : ℝ) (k : ℕ)
    (hbound : PrimeCenterSpectralPolynomialBound
      (ZetaAdmissibleFunction.reflect f) C k) :
    Summable
      (fun index : ZetaPrimePowerIndex =>
        ‖zetaCompletedPrimeOppositeSpectralAmplitudeIndex index f‖ ^ 2) :=
  let hpositiveReflect :
      Summable
        (fun index : ZetaPrimePowerIndex =>
          ‖zetaCompletedPrimeSpectralAmplitudeIndex index
              (ZetaAdmissibleFunction.reflect f)‖ ^ 2) :=
    zetaCompletedPrimeSpectralAmplitudeIndex_normSq_summable_diagonalDebt_owner
      (ZetaAdmissibleFunction.reflect f) C k hbound
  hpositiveReflect.congr
    (fun index : ZetaPrimePowerIndex =>
      zetaCompletedPrimeSpectralAmplitudeIndex_reflect_normSq_eq_opposite_normSq
        index f)

/-- A reflected diagonal-debt real-coordinate `HasSum` gives owner-level
summability of the opposite completed prime face-amplitude square stream. -/
theorem zetaCompletedPrimeOppositeSpectralAmplitudeIndex_normSq_summable_of_reflect_diagonalDebtCoordinate_re_hasSum_diagonalDebt_owner
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
    zetaCompletedPrimeOppositeSpectralAmplitudeIndex_normSq_summable_of_reflect_diagonalDebtCoordinate_re_hasSum_traceEnergy_free_source
      f C hhasSum

/-- Diagonal-debt real-coordinate `HasSum` inputs for a probe and its reflected
probe give summability of the completed prime spectral coordinate majorant. -/
theorem zetaCompletedPrimeSpectralCoordinateMajorant_summable_of_diagonalDebtCoordinate_re_hasSum_diagonalDebt_owner
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
  zetaCompletedPrimeSpectralCoordinateMajorant_summable_of_diagonalDebtCoordinate_re_hasSum_traceEnergy_free_source
    f C Creflect hhasSum hhasSumReflect

/-- Owner-level summability of the completed prime spectral coordinate
majorant used to control the completed diagonal-debt coordinate presentation. -/
theorem zetaCompletedPrimeSpectralCoordinateMajorant_summable_diagonalDebt_owner
    (f : ZetaAdmissibleFunction) (Cpos : ℝ) (kpos : ℕ)
    (hpos : PrimeCenterSpectralPolynomialBound f Cpos kpos)
    (Cneg : ℝ) (kneg : ℕ)
    (hneg : PrimeCenterSpectralPolynomialBound
      (ZetaAdmissibleFunction.reflect f) Cneg kneg) :
    Summable
      (fun index : ZetaPrimePowerIndex =>
        zetaCompletedPrimeSpectralCoordinateMajorant index f) :=
  let hpositive :
      Summable
        (fun index : ZetaPrimePowerIndex =>
          ‖zetaCompletedPrimeSpectralAmplitudeIndex index f‖ ^ 2) :=
    zetaCompletedPrimeSpectralAmplitudeIndex_normSq_summable_diagonalDebt_owner
      f Cpos kpos hpos
  let hopposite :
      Summable
        (fun index : ZetaPrimePowerIndex =>
          ‖zetaCompletedPrimeOppositeSpectralAmplitudeIndex index f‖ ^ 2) :=
    zetaCompletedPrimeOppositeSpectralAmplitudeIndex_normSq_summable_diagonalDebt_owner
      f Cneg kneg hneg
  (hpositive.add hopposite).congr
    (fun index : ZetaPrimePowerIndex =>
      (zetaCompletedPrimeSpectralCoordinateMajorant_eq_normSq_add_normSq_diagonalDebt
        index f).symm)

end ZetaAdmissibleFunction

end
end LFunctions
end Boundary
