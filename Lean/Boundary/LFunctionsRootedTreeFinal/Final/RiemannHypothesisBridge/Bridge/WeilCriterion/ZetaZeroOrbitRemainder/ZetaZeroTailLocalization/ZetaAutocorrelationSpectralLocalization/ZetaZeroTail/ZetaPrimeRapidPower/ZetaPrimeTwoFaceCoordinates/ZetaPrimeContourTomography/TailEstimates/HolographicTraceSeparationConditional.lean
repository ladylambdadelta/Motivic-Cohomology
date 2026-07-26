import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaZeroTail.ZetaPrimeRapidPower.ZetaPrimeTwoFaceCoordinates.ZetaPrimeContourTomography.TailEstimates.HolographicTraceSeparation
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaZeroTail.ZetaPrimeRapidPower.ZetaPrimeTwoFaceCoordinates.ZetaPrimeContourTomography.TailEstimates.HolographicTraceSeparationParts.DiagonalResidualFunctionalParts.DiagonalCoordinateTransportConditionalSource
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaCompletedHilbertSource.ZetaHermitianPacket.CompletedPrimeDiagonalDebtWindowOwnerParts.DiagonalTransportParts.PositiveRealWindowLimitConditional

/-!
# Conditional holographic trace separation

This file exposes the holographic trace-separation conclusions from explicit
completed diagonal-debt real-coordinate `HasSum` inputs.
-/

namespace Boundary
namespace LFunctions

noncomputable section

namespace ZetaAdmissibleFunction

/-- Explicit diagonal-debt real-coordinate `HasSum` inputs identify the
completed off-diagonal trace scalar with the raw positive coordinate once
diagonal debt vanishes. -/
theorem completedPrimeOffDiagonalChannel_eq_zetaCompletedPrimeDefectKernelPositiveCoordinateTsumRe_of_diagonalDebtCoordinateTsum_re_eq_zero_of_diagonalDebtCoordinate_re_hasSum_ownerHolographicTraceSeparation
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
        Creflect)
    (hdiagonal :
      Complex.re (zetaCompletedPrimeDefectKernelDiagonalDebtCoordinateTsum f) =
        0) :
    completedPrimeOffDiagonalChannel f =
      zetaCompletedPrimeDefectKernelPositiveCoordinateTsumRe f :=
  let hbase :
      completedPrimeOffDiagonalChannel f =
        zetaCompletedPrimeDefectKernelPositiveCoordinateTsumRe f :=
    completedPrimeOffDiagonalChannel_eq_positiveCoordinateTsumRe_of_ownerPositiveChannel_source
      f
      (completedPrimeOffDiagonalChannel_eq_ownerPositiveChannel_twoFaceZero_source f)
      (zetaCompletedPrimeDefectKernelPositiveCoordinateTsumRe_eq_ownerPositiveChannel_of_coordinateOwner_of_diagonalDebtCoordinate_re_hasSum_source
        f C Creflect hhasSum hhasSumReflect
        (zetaCompletedPrimeDefectKernelDiagonalDebtCoordinateTsum_re_eq_ownerDiagonalDebt_re_of_diagonalDebtCoordinate_re_hasSum_source_primitive
          f C Creflect hhasSum hhasSumReflect))
  Eq.ndrec
    (motive := fun value : ℝ =>
      completedPrimeOffDiagonalChannel f =
        zetaCompletedPrimeDefectKernelPositiveCoordinateTsumRe f)
    hbase
    hdiagonal

/-- Explicit diagonal-debt real-coordinate `HasSum` inputs and positive trace
faithfulness force the two-face real scalar to vanish. -/
theorem zetaCompletedPrimeTwoFaceGNSMatrixCoefficient_re_eq_zero_of_positiveTraceFaithfulness_of_diagonalDebtCoordinate_re_hasSum_ownerHolographicTraceSeparation
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
        Creflect)
    (hdiagonal :
      Complex.re (zetaCompletedPrimeDefectKernelDiagonalDebtCoordinateTsum f) =
        0)
    (hfaithful :
      zetaCompletedPrimeDefectKernelPositiveCoordinateTsumRe f =
        completedPrimeDefectKernelPositiveChannel f) :
    Complex.re (zetaCompletedPrimeTwoFaceGNSMatrixCoefficient f) = 0 :=
  let hmajorant :
      Summable
        (fun index : ZetaPrimePowerIndex =>
          zetaCompletedPrimeSpectralCoordinateMajorant index f) :=
    zetaCompletedPrimeSpectralCoordinateMajorant_summable_of_diagonalDebtCoordinate_re_hasSum_positiveRealWindowLimit
      f C Creflect hhasSum hhasSumReflect
  zetaCompletedPrimeTwoFaceGNSMatrixCoefficient_re_eq_zero_of_diagonalCoordinate_zero_and_positiveChannel
    f
    hmajorant
    hdiagonal
    hfaithful

end ZetaAdmissibleFunction

end
end LFunctions
end Boundary
