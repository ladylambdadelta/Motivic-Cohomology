import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaCompletedHilbertSource.ZetaHermitianPacket.CompletedPrimeDiagonalDebtWindowOwnerParts.DiagonalTransportParts.CoordinateAssembly
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaCompletedHilbertSource.ZetaHermitianPacket.CompletedPrimeDiagonalDebtWindowOwnerParts.DiagonalTransportParts.PositiveRealWindowLimit
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaCompletedHilbertSource.ZetaHermitianPacket.CompletedPrimeDiagonalDebtWindowOwnerParts.PositiveWeightedSampleSummabilitySource

/-!
# Completed prime diagonal coordinate owner source

This file owns the narrow transport statement identifying the raw completed
diagonal-debt coordinate presentation with the owner completed diagonal debt.
-/

namespace Boundary
namespace LFunctions

noncomputable section

namespace ZetaAdmissibleFunction

/-- The opposite completed prime weighted sample norm-square stream is
summable. -/
theorem zetaCompletedPrimeOppositeWeightedSampleNormSq_summable_windowSource
    (f : ZetaAdmissibleFunction) :
    Summable
      (fun index : ZetaPrimePowerIndex =>
        zetaCompletedPrimeOppositeWeightedSampleNormSq index f) :=
  (zetaCompletedPrimePositiveWeightedSampleNormSq_summable_windowSource
    (ZetaAdmissibleFunction.reflect f)).congr
    (fun index : ZetaPrimePowerIndex =>
      (zetaCompletedPrimeOppositeWeightedSampleNormSq_eq_positive_reflect
        index f).symm)

/-- The positive completed prime spectral-amplitude square stream is
summable. -/
theorem zetaCompletedPrimeSpectralAmplitudeIndex_normSq_summable_windowSource
    (f : ZetaAdmissibleFunction) :
    Summable
      (fun index : ZetaPrimePowerIndex =>
        ‖zetaCompletedPrimeSpectralAmplitudeIndex index f‖ ^ 2) :=
  (zetaCompletedPrimePositiveWeightedSampleNormSq_summable_windowSource
    f).congr
    (fun index : ZetaPrimePowerIndex =>
      (zetaCompletedPrimeSpectralAmplitudeIndex_norm_sq_eq_weightedSampleNormSq
        index f).symm)

/-- The opposite completed prime spectral-amplitude square stream is
summable. -/
theorem zetaCompletedPrimeOppositeSpectralAmplitudeIndex_normSq_summable_windowSource
    (f : ZetaAdmissibleFunction) :
    Summable
      (fun index : ZetaPrimePowerIndex =>
        ‖zetaCompletedPrimeOppositeSpectralAmplitudeIndex index f‖ ^ 2) :=
  (zetaCompletedPrimeOppositeWeightedSampleNormSq_summable_windowSource
    f).congr
    (fun index : ZetaPrimePowerIndex =>
      (zetaCompletedPrimeOppositeSpectralAmplitudeIndex_norm_sq_eq_weightedSampleNormSq
        index f).symm)

/-- The completed spectral-coordinate majorant is the pointwise sum of the two
completed prime face-amplitude square streams. -/
theorem zetaCompletedPrimeSpectralCoordinateMajorant_eq_normSq_add_normSq_windowSource
    (f : ZetaAdmissibleFunction) :
    (fun index : ZetaPrimePowerIndex =>
      zetaCompletedPrimeSpectralCoordinateMajorant index f) =
      fun index : ZetaPrimePowerIndex =>
        ‖zetaCompletedPrimeSpectralAmplitudeIndex index f‖ ^ 2 +
          ‖zetaCompletedPrimeOppositeSpectralAmplitudeIndex index f‖ ^ 2 :=
  funext
    (fun index : ZetaPrimePowerIndex =>
      Eq.refl (zetaCompletedPrimeSpectralCoordinateMajorant index f))

/-- The completed spectral-coordinate majorant is summable. -/
theorem zetaCompletedPrimeSpectralCoordinateMajorant_summable_windowSource
    (f : ZetaAdmissibleFunction) :
    Summable
      (fun index : ZetaPrimePowerIndex =>
        zetaCompletedPrimeSpectralCoordinateMajorant index f) :=
  let hpositive :
      Summable
        (fun index : ZetaPrimePowerIndex =>
          ‖zetaCompletedPrimeSpectralAmplitudeIndex index f‖ ^ 2) :=
    zetaCompletedPrimeSpectralAmplitudeIndex_normSq_summable_windowSource
      f
  let hopposite :
      Summable
        (fun index : ZetaPrimePowerIndex =>
          ‖zetaCompletedPrimeOppositeSpectralAmplitudeIndex index f‖ ^ 2) :=
    zetaCompletedPrimeOppositeSpectralAmplitudeIndex_normSq_summable_windowSource
      f
  (hpositive.add hopposite).congr
    (fun index : ZetaPrimePowerIndex =>
      congrFun
        (zetaCompletedPrimeSpectralCoordinateMajorant_eq_normSq_add_normSq_windowSource
          f)
        index).symm

/-- The raw completed diagonal-debt coordinate presentation has the owner
completed diagonal-debt real scalar. -/
theorem zetaCompletedPrimeDefectKernelDiagonalDebtCoordinateTsum_re_eq_owner_re_windowSourcePrimitive
    (f : ZetaAdmissibleFunction)
    (hcoordinateZero :
      Complex.re (zetaCompletedPrimeDefectKernelDiagonalDebtCoordinateTsum f) =
        0) :
    Complex.re (zetaCompletedPrimeDefectKernelDiagonalDebtCoordinateTsum f) =
      Complex.re (zetaCompletedPrimeDefectKernelDiagonalDebt f) :=
  let hmajorant :
      Summable
        (fun index : ZetaPrimePowerIndex =>
          zetaCompletedPrimeSpectralCoordinateMajorant index f) :=
    zetaCompletedPrimeSpectralCoordinateMajorant_summable_windowSource f
  let hcoordinate :
      Filter.Tendsto
        (fun N : ℕ =>
          zetaCompletedPrimeDefectKernelDiagonalDebtRealWindow N f)
        Filter.atTop
        (𝓝
          (Complex.re
            (zetaCompletedPrimeDefectKernelDiagonalDebtCoordinateTsum f))) :=
    zetaCompletedPrimeDefectKernelDiagonalDebtRealWindow_tendsto_coordinateTsum_re_of_spectralMajorant
      f hmajorant
  let howner :
      Filter.Tendsto
        (fun N : ℕ =>
          zetaCompletedPrimeDefectKernelDiagonalDebtRealWindow N f)
        Filter.atTop
        (𝓝 (Complex.re (zetaCompletedPrimeDefectKernelDiagonalDebt f))) :=
    zetaCompletedPrimeDefectKernelDiagonalDebtRealWindow_tendsto_ownerRe_of_spectralCoordinateMajorant_summable_positiveRealWindowLimit
      f hmajorant hcoordinateZero
  tendsto_nhds_unique hcoordinate howner

/-- The raw completed positive coordinate presentation has the owner positive
channel as its real scalar. -/
theorem zetaCompletedPrimeDefectKernelPositiveCoordinateTsumRe_eq_ownerPositiveChannel_windowSource
    (f : ZetaAdmissibleFunction)
    (hmajorant :
      Summable
        (fun index : ZetaPrimePowerIndex =>
          zetaCompletedPrimeSpectralCoordinateMajorant index f))
    (hcoordinateZero :
      Complex.re (zetaCompletedPrimeDefectKernelDiagonalDebtCoordinateTsum f) =
        0) :
    zetaCompletedPrimeDefectKernelPositiveCoordinateTsumRe f =
      completedPrimeDefectKernelPositiveChannel f :=
  zetaCompletedPrimeDefectKernelPositiveCoordinateTsumRe_eq_completedPrimeDefectKernelPositiveChannel_of_diagonalDebtCoordinateTsum_re
    f
    hmajorant
    (zetaCompletedPrimeDefectKernelDiagonalDebtCoordinateTsum_re_eq_owner_re_windowSourcePrimitive
      f hcoordinateZero)

end ZetaAdmissibleFunction

end
end LFunctions
end Boundary
