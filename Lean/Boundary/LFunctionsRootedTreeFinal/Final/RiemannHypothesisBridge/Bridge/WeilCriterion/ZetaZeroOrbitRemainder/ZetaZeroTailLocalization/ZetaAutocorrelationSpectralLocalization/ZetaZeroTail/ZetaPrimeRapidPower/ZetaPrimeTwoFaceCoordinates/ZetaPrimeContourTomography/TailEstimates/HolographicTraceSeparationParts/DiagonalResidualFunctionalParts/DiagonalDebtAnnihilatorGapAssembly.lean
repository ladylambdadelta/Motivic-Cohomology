import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaZeroTail.ZetaPrimeRapidPower.ZetaPrimeTwoFaceCoordinates.ZetaPrimeContourTomography.TailEstimates.HolographicTraceSeparationParts.DiagonalResidualFunctionalParts.DiagonalDebtAnnihilatorSource
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaCompletedHilbertSource.ZetaHermitianPacket.CompletedPrimeDiagonalDebtWindowOwner
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaZeroTail.ZetaPrimeRapidPower.ZetaPrimeTwoFaceCoordinates.ZetaPrimeContourTomography.TailEstimates.ResidualCoordinateSource

/-!
# Diagonal-debt annihilator gap assembly

This file owns the final gap-zero assembly that turns the raw source algebra
into trace-residual identities for the diagonal-debt coordinate residual.
-/

namespace Boundary
namespace LFunctions

noncomputable section

namespace ZetaAdmissibleFunction

/-- The owner ledger and oriented-coordinate summability give the completed/raw
two-face real comparison at the diagonal-debt gap layer. -/
theorem completedPrimeTwoFaceGNSMatrixCoefficient_re_eq_raw_source
    (f : ZetaAdmissibleFunction) :
    Complex.re (zetaCompletedPrimeTwoFaceGNSMatrixCoefficient f) =
      Complex.re (zetaPrimeTwoFaceGNSMatrixCoefficient f) :=
  let hledger :
      ZetaCompletedPrimePowerAutocorrelationLedgerCancellation f :=
    zetaCompletedPrimePowerAutocorrelationLedgerCancellation_owner f
  let horiented :
      Summable
        (fun index : ZetaPrimePowerIndex =>
          zetaCompletedPrimePowerAutocorrelationOrientedCrossCoordinate
            index f) :=
    zetaCompletedPrimePowerAutocorrelationOrientedCrossCoordinate_summable_owner
      f
  completedPrimeTwoFaceGNSMatrixCoefficient_re_eq_finite_boundaryCancellation
    f hledger horiented

/-- The finite lower-weight normalization kills the raw two-face real scalar
used in the diagonal-debt gap comparison. -/
theorem zetaPrimeTwoFaceGNSMatrixCoefficient_re_eq_zero_source
    (f : ZetaAdmissibleFunction) :
    Complex.re (zetaPrimeTwoFaceGNSMatrixCoefficient f) = 0 :=
  zetaPrimeTwoFaceGNSMatrixCoefficient_re_eq_zero_of_completedLowerWeightNormalization
    f

/-- Boundary cancellation and lower-weight normalization kill the completed
two-face real scalar. -/
theorem zetaCompletedPrimeTwoFaceGNSMatrixCoefficient_re_eq_zero_source
    (f : ZetaAdmissibleFunction) :
    Complex.re (zetaCompletedPrimeTwoFaceGNSMatrixCoefficient f) = 0 :=
  let hmatrix :
      Complex.re (zetaCompletedPrimeTwoFaceGNSMatrixCoefficient f) =
        Complex.re (zetaPrimeTwoFaceGNSMatrixCoefficient f) :=
    completedPrimeTwoFaceGNSMatrixCoefficient_re_eq_raw_source f
  let hrawTwoFace :
      Complex.re (zetaPrimeTwoFaceGNSMatrixCoefficient f) = 0 :=
    zetaPrimeTwoFaceGNSMatrixCoefficient_re_eq_zero_source f
  hmatrix.trans hrawTwoFace

/-- Completed two-face real vanishing identifies the completed off-diagonal
channel with the owner positive channel. -/
theorem completedPrimeOffDiagonalChannel_eq_ownerPositiveChannel_of_twoFace_re_eq_zero_source
    (f : ZetaAdmissibleFunction)
    (D : CompletedFiniteWindowPrimeDistributionReconstruction f)
    (htwoFace :
      Complex.re (zetaCompletedPrimeTwoFaceGNSMatrixCoefficient f) = 0) :
    completedPrimeOffDiagonalChannel f =
      completedPrimeDefectKernelPositiveChannel f :=
  (completedPrimeOffDiagonalChannel_eq_positiveChannel_iff_completedPrimeTwoFaceGNSMatrixCoefficient_re_eq_zero
    f D).mpr
    htwoFace

/-- Source bridge from the completed off-diagonal channel to the owner
positive channel. -/
theorem completedPrimeOffDiagonalChannel_eq_ownerPositiveChannel_twoFaceZero_source
    (f : ZetaAdmissibleFunction)
    (D : CompletedFiniteWindowPrimeDistributionReconstruction f) :
    completedPrimeOffDiagonalChannel f =
      completedPrimeDefectKernelPositiveChannel f :=
  completedPrimeOffDiagonalChannel_eq_ownerPositiveChannel_of_twoFace_re_eq_zero_source
    f D
    (zetaCompletedPrimeTwoFaceGNSMatrixCoefficient_re_eq_zero_source f)

/-- After source two-face cancellation, diagonal-coordinate annihilation is
equivalent to raw positive-coordinate annihilation. -/
theorem diagonalDebtCoordinateTsum_re_eq_zero_iff_positiveCoordinate_zero_source
    (f : ZetaAdmissibleFunction)
    (hmajorant :
      Summable
        (fun index : ZetaPrimePowerIndex =>
          zetaCompletedPrimeSpectralCoordinateMajorant index f)) :
    Complex.re (zetaCompletedPrimeDefectKernelDiagonalDebtCoordinateTsum f) =
        0 ↔
      zetaCompletedPrimeDefectKernelPositiveCoordinateTsumRe f = 0 :=
  zetaCompletedPrimeDefectKernelDiagonalDebtCoordinateTsum_re_eq_zero_iff_positiveCoordinate_zero_of_twoFace_zero_source
    f
    hmajorant
    (zetaCompletedPrimeTwoFaceGNSMatrixCoefficient_re_eq_zero_source f)

/-- Source vanishing of the named positive/off-diagonal mismatch scalar. -/
theorem completedPrimePositiveOffDiagonalGap_eq_zero_of_coordinateOwner_source
    (f : ZetaAdmissibleFunction)
    (D : CompletedFiniteWindowPrimeDistributionReconstruction f) :
    Summable
        (fun index : ZetaPrimePowerIndex =>
          zetaCompletedPrimeSpectralCoordinateMajorant index f) →
    Complex.re (zetaCompletedPrimeDefectKernelDiagonalDebtCoordinateTsum f) =
      Complex.re (zetaCompletedPrimeDefectKernelDiagonalDebt f) →
    completedPrimePositiveOffDiagonalGap f = 0 :=
  fun hmajorant =>
  fun hcoordinateOwner =>
  let howner :
      completedPrimeOffDiagonalChannel f =
        completedPrimeDefectKernelPositiveChannel f :=
    completedPrimeOffDiagonalChannel_eq_ownerPositiveChannel_twoFaceZero_source
      f D
  let hcoordinate :
      zetaCompletedPrimeDefectKernelPositiveCoordinateTsumRe f =
        completedPrimeDefectKernelPositiveChannel f :=
    zetaCompletedPrimeDefectKernelPositiveCoordinateTsumRe_eq_ownerPositiveChannel_of_coordinateOwner_source
      f hmajorant hcoordinateOwner
  let hoffPositive :
      completedPrimeOffDiagonalChannel f =
        zetaCompletedPrimeDefectKernelPositiveCoordinateTsumRe f :=
    completedPrimeOffDiagonalChannel_eq_positiveCoordinateTsumRe_of_ownerPositiveChannel_source
      f howner hcoordinate
  completedPrimePositiveOffDiagonalGap_eq_zero_of_offDiagonal_eq_positiveCoordinate_source
    f hoffPositive

/-- Source vanishing of the named positive/off-diagonal mismatch scalar. -/
theorem completedPrimePositiveOffDiagonalGap_eq_zero_source
    (f : ZetaAdmissibleFunction)
    (D : CompletedFiniteWindowPrimeDistributionReconstruction f)
    (hmajorant :
      Summable
        (fun index : ZetaPrimePowerIndex =>
          zetaCompletedPrimeSpectralCoordinateMajorant index f))
    (hcoordinateZero :
      Complex.re (zetaCompletedPrimeDefectKernelDiagonalDebtCoordinateTsum f) =
        0) :
    completedPrimePositiveOffDiagonalGap f = 0 :=
  let hpositive :
      zetaCompletedPrimeDefectKernelPositiveCoordinateTsumRe f = 0 :=
    (diagonalDebtCoordinateTsum_re_eq_zero_iff_positiveCoordinate_zero_source
      f hmajorant).mp hcoordinateZero
  let hoffOwner :
      completedPrimeOffDiagonalChannel f =
        completedPrimeDefectKernelPositiveChannel f :=
    completedPrimeOffDiagonalChannel_eq_ownerPositiveChannel_twoFaceZero_source
      f D
  let hoffDiagonal :
      completedPrimeOffDiagonalChannel f = 0 :=
    hoffOwner.trans
      (completedPrimeDefectKernelPositiveChannel_eq_zero_of_completedLowerWeightNormalization
        f)
  completedPrimePositiveOffDiagonalGap_eq_zero_of_positive_zero_and_offDiagonal_zero_source
    f
    hpositive
    hoffDiagonal

/-- At the gap assembly layer, the coordinate positive presentation
reconstructs the owner completed positive channel. -/
theorem zetaCompletedPrimeDefectKernelPositiveCoordinateTsumRe_eq_ownerPositiveChannel_source
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
  let hpositive :
      zetaCompletedPrimeDefectKernelPositiveCoordinateTsumRe f = 0 :=
    (diagonalDebtCoordinateTsum_re_eq_zero_iff_positiveCoordinate_zero_source
      f hmajorant).mp hcoordinateZero
  hpositive.trans
    (completedPrimeDefectKernelPositiveChannel_eq_zero_of_completedLowerWeightNormalization
      f).symm

/-- Positive trace-faithfulness identifies the coordinate positive
presentation with the owner positive channel. -/
theorem zetaCompletedPrimeDefectKernelPositiveCoordinateTsumRe_eq_completedPrimeDefectKernelPositiveChannel_traceFaithfulness_source
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
  zetaCompletedPrimeDefectKernelPositiveCoordinateTsumRe_eq_ownerPositiveChannel_source
    f hmajorant hcoordinateZero

/-- If the off-diagonal trace channel is the raw positive coordinate total,
then the completed diagonal-debt coordinate residual is the completed prime
trace functional gap. -/
theorem diagonalDebtCoordinateResidual_re_eq_completedPrimeTraceFunctionalGap_of_offDiagonal_eq_positiveCoordinate_source
    (f : ZetaAdmissibleFunction)
    (hmajorant :
      Summable
        (fun index : ZetaPrimePowerIndex =>
          zetaCompletedPrimeSpectralCoordinateMajorant index f))
    (hoffPositive :
      completedPrimeOffDiagonalChannel f =
        zetaCompletedPrimeDefectKernelPositiveCoordinateTsumRe f) :
    Complex.re
        (zetaCompletedPrimeDefectKernelDiagonalDebtCoordinateTsum f) =
      completedPrimeTraceFunctionalGap f :=
  diagonalDebtCoordinateResidual_re_eq_completedPrimeTraceFunctionalGap_of_positiveOffDiagonalGap_eq_zero_source
    f
    hmajorant
    (completedPrimePositiveOffDiagonalGap_eq_zero_of_offDiagonal_eq_positiveCoordinate_source
      f hoffPositive)

/-- Source scalar identification of the completed diagonal-debt coordinate
residual with the named completed prime trace functional gap. -/
theorem diagonalDebtCoordinateResidual_re_eq_completedPrimeTraceFunctionalGap_source
    (f : ZetaAdmissibleFunction)
    (D : CompletedFiniteWindowPrimeDistributionReconstruction f)
    (hmajorant :
      Summable
        (fun index : ZetaPrimePowerIndex =>
          zetaCompletedPrimeSpectralCoordinateMajorant index f))
    (hcoordinateZero :
      Complex.re (zetaCompletedPrimeDefectKernelDiagonalDebtCoordinateTsum f) =
        0) :
    Complex.re
        (zetaCompletedPrimeDefectKernelDiagonalDebtCoordinateTsum f) =
      completedPrimeTraceFunctionalGap f :=
  diagonalDebtCoordinateResidual_re_eq_completedPrimeTraceFunctionalGap_of_positiveOffDiagonalGap_eq_zero_source
    f
    hmajorant
    (completedPrimePositiveOffDiagonalGap_eq_zero_source f D hmajorant hcoordinateZero)

/-- Source real scalar identification of the completed diagonal-debt
coordinate residual with the completed prime trace gap. -/
theorem diagonalDebtCoordinateResidual_re_eq_completedPrimeTraceGap_source
    (f : ZetaAdmissibleFunction)
    (D : CompletedFiniteWindowPrimeDistributionReconstruction f)
    (hmajorant :
      Summable
        (fun index : ZetaPrimePowerIndex =>
          zetaCompletedPrimeSpectralCoordinateMajorant index f))
    (hcoordinateZero :
      Complex.re (zetaCompletedPrimeDefectKernelDiagonalDebtCoordinateTsum f) =
        0) :
    Complex.re
        (zetaCompletedPrimeDefectKernelDiagonalDebtCoordinateTsum f) =
      completedPrimeTraceTimeScalar f -
        completedPrimeTraceSpectralScalar f :=
  (diagonalDebtCoordinateResidual_re_eq_completedPrimeTraceFunctionalGap_source
    f D hmajorant hcoordinateZero).trans
    (completedPrimeTraceFunctionalGap_eq f)

/-- If the off-diagonal trace channel is the raw positive coordinate total,
then the completed diagonal-debt coordinate residual is the completed prime
trace gap. -/
theorem diagonalDebtCoordinateResidual_re_eq_completedPrimeTraceGap_of_offDiagonal_eq_positiveCoordinate_source
    (f : ZetaAdmissibleFunction)
    (hmajorant :
      Summable
        (fun index : ZetaPrimePowerIndex =>
          zetaCompletedPrimeSpectralCoordinateMajorant index f))
    (hoffPositive :
      completedPrimeOffDiagonalChannel f =
        zetaCompletedPrimeDefectKernelPositiveCoordinateTsumRe f) :
    Complex.re
        (zetaCompletedPrimeDefectKernelDiagonalDebtCoordinateTsum f) =
      completedPrimeTraceTimeScalar f -
        completedPrimeTraceSpectralScalar f :=
  (diagonalDebtCoordinateResidual_re_eq_completedPrimeTraceFunctionalGap_of_offDiagonal_eq_positiveCoordinate_source
    f hmajorant hoffPositive).trans
    (completedPrimeTraceFunctionalGap_eq f)

/-- Real trace-gap identification transports the diagonal-debt real coordinate
to the completed prime trace residual complex scalar. -/
theorem diagonalDebtCoordinateResidual_eq_completedPrimeTraceResidual_of_re_eq_traceGap_source
    (f : ZetaAdmissibleFunction)
    (hreal :
      Complex.re
          (zetaCompletedPrimeDefectKernelDiagonalDebtCoordinateTsum f) =
        completedPrimeTraceTimeScalar f -
          completedPrimeTraceSpectralScalar f) :
    ((Complex.re
        (zetaCompletedPrimeDefectKernelDiagonalDebtCoordinateTsum f) : ℝ) :
      ℂ) =
      completedPrimeTraceResidualComplexScalar f :=
  let hcoerce :
      ((Complex.re
          (zetaCompletedPrimeDefectKernelDiagonalDebtCoordinateTsum f) : ℝ) :
        ℂ) =
        ((completedPrimeTraceTimeScalar f -
          completedPrimeTraceSpectralScalar f : ℝ) : ℂ) :=
    congrArg (fun value : ℝ => (value : ℂ)) hreal
  Eq.trans hcoerce (completedPrimeTraceResidualComplexScalar_eq f).symm

/-- Source scalar identification of the completed diagonal-debt coordinate
residual with the completed prime trace residual. -/
theorem diagonalDebtCoordinateResidual_eq_completedPrimeTraceResidual_source
    (f : ZetaAdmissibleFunction)
    (D : CompletedFiniteWindowPrimeDistributionReconstruction f)
    (hmajorant :
      Summable
        (fun index : ZetaPrimePowerIndex =>
          zetaCompletedPrimeSpectralCoordinateMajorant index f))
    (hcoordinateZero :
      Complex.re (zetaCompletedPrimeDefectKernelDiagonalDebtCoordinateTsum f) =
        0) :
    ((Complex.re
        (zetaCompletedPrimeDefectKernelDiagonalDebtCoordinateTsum f) : ℝ) :
      ℂ) =
      completedPrimeTraceResidualComplexScalar f :=
  let hreal :
      Complex.re
          (zetaCompletedPrimeDefectKernelDiagonalDebtCoordinateTsum f) =
        completedPrimeTraceTimeScalar f -
          completedPrimeTraceSpectralScalar f :=
    diagonalDebtCoordinateResidual_re_eq_completedPrimeTraceGap_source f
      D hmajorant hcoordinateZero
  diagonalDebtCoordinateResidual_eq_completedPrimeTraceResidual_of_re_eq_traceGap_source
    f hreal

/-- If the off-diagonal trace channel is the raw positive coordinate total,
then the completed diagonal-debt coordinate residual is the completed prime
trace residual. -/
theorem diagonalDebtCoordinateResidual_eq_completedPrimeTraceResidual_of_offDiagonal_eq_positiveCoordinate_source
    (f : ZetaAdmissibleFunction)
    (hmajorant :
      Summable
        (fun index : ZetaPrimePowerIndex =>
          zetaCompletedPrimeSpectralCoordinateMajorant index f))
    (hoffPositive :
      completedPrimeOffDiagonalChannel f =
        zetaCompletedPrimeDefectKernelPositiveCoordinateTsumRe f) :
    ((Complex.re
        (zetaCompletedPrimeDefectKernelDiagonalDebtCoordinateTsum f) : ℝ) :
      ℂ) =
      completedPrimeTraceResidualComplexScalar f :=
  let hreal :
      Complex.re
          (zetaCompletedPrimeDefectKernelDiagonalDebtCoordinateTsum f) =
        completedPrimeTraceTimeScalar f -
          completedPrimeTraceSpectralScalar f :=
    diagonalDebtCoordinateResidual_re_eq_completedPrimeTraceGap_of_offDiagonal_eq_positiveCoordinate_source
      f hmajorant hoffPositive
  diagonalDebtCoordinateResidual_eq_completedPrimeTraceResidual_of_re_eq_traceGap_source
    f hreal

end ZetaAdmissibleFunction

end
end LFunctions
end Boundary
