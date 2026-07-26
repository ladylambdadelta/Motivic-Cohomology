import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaCompletedHilbertSource.ZetaHermitianPacket.CompletedPrimeDiagonalDebtWindowOwnerParts.DiagonalTransportParts.CoordinateAssembly
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaCompletedHilbertSource.ZetaHermitianPacket.CompletedPrimeDiagonalDebtWindowOwnerParts.DiagonalTransportParts.PositiveRealWindowLimit

namespace Boundary
namespace LFunctions

noncomputable section

namespace ZetaAdmissibleFunction

theorem zetaCompletedPrimeDefectKernelPositiveCoordinateTsumRe_eq_positiveChannel_coordinateAssembly
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
    (hcoordinateZero :
      Complex.re (zetaCompletedPrimeDefectKernelDiagonalDebtCoordinateTsum f) =
        0) :
    zetaCompletedPrimeDefectKernelPositiveCoordinateTsumRe f =
      completedPrimeDefectKernelPositiveChannel f :=
  let hmajorant :
      Summable
        (fun index : ZetaPrimePowerIndex =>
          zetaCompletedPrimeSpectralCoordinateMajorant index f) :=
    zetaCompletedPrimeSpectralCoordinateMajorant_summable_of_diagonalDebtCoordinate_re_hasSum_diagonalDebt_owner
      f C Creflect hhasSum hhasSumReflect
  zetaCompletedPrimeDefectKernelPositiveCoordinateTsumRe_eq_positiveChannel_positiveRealWindowLimit
    f hmajorant hcoordinateZero

theorem zetaCompletedPrimeDefectKernelPositiveCoordinateTsumRe_eq_positiveChannel_of_diagonalDebtCoordinate_re_hasSum_coordinateAssembly
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
    (hcoordinateZero :
      Complex.re (zetaCompletedPrimeDefectKernelDiagonalDebtCoordinateTsum f) =
        0) :
    zetaCompletedPrimeDefectKernelPositiveCoordinateTsumRe f =
      completedPrimeDefectKernelPositiveChannel f :=
  zetaCompletedPrimeDefectKernelPositiveCoordinateTsumRe_eq_positiveChannel_coordinateAssembly
    f C Creflect hhasSum hhasSumReflect hcoordinateZero

theorem zetaCompletedPrimeDefectKernelPositiveCoordinateTsum_re_eq_owner_re_coordinateAssembly
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
    (hcoordinateZero :
      Complex.re (zetaCompletedPrimeDefectKernelDiagonalDebtCoordinateTsum f) =
        0) :
    Complex.re (zetaCompletedPrimeDefectKernelPositiveCoordinateTsum f) =
      Complex.re (zetaCompletedPrimeDefectKernelPositiveForm f) :=
  (zetaCompletedPrimeDefectKernelPositiveCoordinateTsum_re_eq_coordinateTsumRe_coordinateAssembly f).trans
    ((zetaCompletedPrimeDefectKernelPositiveCoordinateTsumRe_eq_positiveChannel_coordinateAssembly
      f C Creflect hhasSum hhasSumReflect hcoordinateZero).trans
      (zetaCompletedPrimeDefectKernelPositiveForm_re_eq_positiveChannel_coordinateAssembly f).symm)

theorem zetaCompletedPrimeDefectKernelPositiveCoordinateTsum_re_eq_owner_re_of_diagonalDebtCoordinate_re_hasSum_coordinateAssembly
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
    (hcoordinateZero :
      Complex.re (zetaCompletedPrimeDefectKernelDiagonalDebtCoordinateTsum f) =
        0) :
    Complex.re (zetaCompletedPrimeDefectKernelPositiveCoordinateTsum f) =
      Complex.re (zetaCompletedPrimeDefectKernelPositiveForm f) :=
  (zetaCompletedPrimeDefectKernelPositiveCoordinateTsum_re_eq_coordinateTsumRe_coordinateAssembly
    f).trans
    ((zetaCompletedPrimeDefectKernelPositiveCoordinateTsumRe_eq_positiveChannel_coordinateAssembly
      f C Creflect hhasSum hhasSumReflect hcoordinateZero).trans
      (zetaCompletedPrimeDefectKernelPositiveForm_re_eq_positiveChannel_coordinateAssembly
        f).symm)

theorem zetaCompletedPrimeDefectKernelPositiveCoordinateTsum_im_eq_owner_im_coordinateAssembly
    (f : ZetaAdmissibleFunction) :
    Complex.im (zetaCompletedPrimeDefectKernelPositiveCoordinateTsum f) =
      Complex.im (zetaCompletedPrimeDefectKernelPositiveForm f) :=
  (zetaCompletedPrimeDefectKernelPositiveCoordinateTsum_im_eq_zero_coordinateAssembly f).trans
    (zetaCompletedPrimeDefectKernelPositiveForm_im_eq_zero_coordinateAssembly f).symm

theorem zetaCompletedPrimeDefectKernelPositiveCoordinateTsum_eq_owner_coordinateAssembly
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
    (hcoordinateZero :
      Complex.re (zetaCompletedPrimeDefectKernelDiagonalDebtCoordinateTsum f) =
        0) :
    zetaCompletedPrimeDefectKernelPositiveCoordinateTsum f =
      zetaCompletedPrimeDefectKernelPositiveForm f :=
  Complex.ext
    (zetaCompletedPrimeDefectKernelPositiveCoordinateTsum_re_eq_owner_re_coordinateAssembly
      f C Creflect hhasSum hhasSumReflect hcoordinateZero)
    (zetaCompletedPrimeDefectKernelPositiveCoordinateTsum_im_eq_owner_im_coordinateAssembly f)

theorem zetaCompletedPrimeDefectKernelPositiveCoordinateTsum_eq_owner_of_diagonalDebtCoordinate_re_hasSum_coordinateAssembly
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
    (hcoordinateZero :
      Complex.re (zetaCompletedPrimeDefectKernelDiagonalDebtCoordinateTsum f) =
        0) :
    zetaCompletedPrimeDefectKernelPositiveCoordinateTsum f =
      zetaCompletedPrimeDefectKernelPositiveForm f :=
  Complex.ext
    (zetaCompletedPrimeDefectKernelPositiveCoordinateTsum_re_eq_owner_re_coordinateAssembly
      f C Creflect hhasSum hhasSumReflect hcoordinateZero)
    (zetaCompletedPrimeDefectKernelPositiveCoordinateTsum_im_eq_owner_im_coordinateAssembly
      f)

/-- Majorant summability transports the completed diagonal-debt coordinate
presentation to the owner completed diagonal debt once the positive channel has
already been identified. -/
theorem zetaCompletedPrimeDefectKernelDiagonalDebtCoordinateTsum_eq_owner_of_spectralCoordinateMajorant_summable_coordinateAssembly
    (f : ZetaAdmissibleFunction)
    (hmajorant :
      Summable
        (fun index : ZetaPrimePowerIndex =>
          zetaCompletedPrimeSpectralCoordinateMajorant index f))
    (hcoordinateZero :
      Complex.re (zetaCompletedPrimeDefectKernelDiagonalDebtCoordinateTsum f) =
        0) :
    zetaCompletedPrimeDefectKernelDiagonalDebtCoordinateTsum f =
      zetaCompletedPrimeDefectKernelDiagonalDebt f :=
  let hcoordinate :
      zetaCompletedPrimeDefectKernelDiagonalDebtCoordinateTsum f =
        zetaCompletedPrimeDefectKernelPositiveCoordinateTsum f +
          zetaCompletedPrimeTwoFaceGNSMatrixCoefficient f :=
    zetaCompletedPrimeDefectKernelDiagonalDebtCoordinateTsum_eq_positive_add_twoFace_of_spectralCoordinateMajorant_summable_coordinateAssembly
      f hmajorant
  let hpositive :
      zetaCompletedPrimeDefectKernelPositiveCoordinateTsum f =
        zetaCompletedPrimeDefectKernelPositiveForm f :=
    Complex.ext
      ((zetaCompletedPrimeDefectKernelPositiveCoordinateTsum_re_eq_coordinateTsumRe_coordinateAssembly
        f).trans
        ((zetaCompletedPrimeDefectKernelPositiveCoordinateTsumRe_eq_positiveChannel_positiveRealWindowLimit
          f hmajorant hcoordinateZero).trans
          (zetaCompletedPrimeDefectKernelPositiveForm_re_eq_positiveChannel_coordinateAssembly
            f).symm))
      (zetaCompletedPrimeDefectKernelPositiveCoordinateTsum_im_eq_owner_im_coordinateAssembly
        f)
  let howner :
      zetaCompletedPrimeDefectKernelPositiveForm f +
          zetaCompletedPrimeTwoFaceGNSMatrixCoefficient f =
        zetaCompletedPrimeDefectKernelDiagonalDebt f :=
    (zetaCompletedPrimeDefectKernelDiagonalDebt_eq_positive_add_twoFace_coordinateAssembly
      f).symm
  hcoordinate.trans
    ((congrArg
      (fun value : ℂ =>
        value + zetaCompletedPrimeTwoFaceGNSMatrixCoefficient f)
      hpositive).trans
      howner)

theorem zetaCompletedPrimeDefectKernelDiagonalDebtCoordinateTsum_eq_owner_coordinateAssembly
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
    (hcoordinateZero :
      Complex.re (zetaCompletedPrimeDefectKernelDiagonalDebtCoordinateTsum f) =
        0) :
    zetaCompletedPrimeDefectKernelDiagonalDebtCoordinateTsum f =
      zetaCompletedPrimeDefectKernelDiagonalDebt f :=
  let hmajorant :
      Summable
        (fun index : ZetaPrimePowerIndex =>
          zetaCompletedPrimeSpectralCoordinateMajorant index f) :=
    zetaCompletedPrimeSpectralCoordinateMajorant_summable_of_diagonalDebtCoordinate_re_hasSum_diagonalDebt_owner
      f C Creflect hhasSum hhasSumReflect
  zetaCompletedPrimeDefectKernelDiagonalDebtCoordinateTsum_eq_owner_of_spectralCoordinateMajorant_summable_coordinateAssembly
    f hmajorant hcoordinateZero

theorem zetaCompletedPrimeDefectKernelDiagonalDebtCoordinateTsum_eq_owner_of_diagonalDebtCoordinate_re_hasSum_coordinateAssembly
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
    (hcoordinateZero :
      Complex.re (zetaCompletedPrimeDefectKernelDiagonalDebtCoordinateTsum f) =
        0) :
    zetaCompletedPrimeDefectKernelDiagonalDebtCoordinateTsum f =
      zetaCompletedPrimeDefectKernelDiagonalDebt f :=
  let hcoordinate :
      zetaCompletedPrimeDefectKernelDiagonalDebtCoordinateTsum f =
        zetaCompletedPrimeDefectKernelPositiveCoordinateTsum f +
          zetaCompletedPrimeTwoFaceGNSMatrixCoefficient f :=
    zetaCompletedPrimeDefectKernelDiagonalDebtCoordinateTsum_eq_positive_add_twoFace_of_spectralCoordinateMajorant_summable_coordinateAssembly
      f
      (zetaCompletedPrimeSpectralCoordinateMajorant_summable_of_diagonalDebtCoordinate_re_hasSum_diagonalDebt_owner
        f C Creflect hhasSum hhasSumReflect)
  let hpositive :
      zetaCompletedPrimeDefectKernelPositiveCoordinateTsum f =
        zetaCompletedPrimeDefectKernelPositiveForm f :=
    zetaCompletedPrimeDefectKernelPositiveCoordinateTsum_eq_owner_coordinateAssembly
      f C Creflect hhasSum hhasSumReflect hcoordinateZero
  let howner :
      zetaCompletedPrimeDefectKernelPositiveForm f +
          zetaCompletedPrimeTwoFaceGNSMatrixCoefficient f =
        zetaCompletedPrimeDefectKernelDiagonalDebt f :=
    (zetaCompletedPrimeDefectKernelDiagonalDebt_eq_positive_add_twoFace_coordinateAssembly
      f).symm
  hcoordinate.trans
    ((congrArg
      (fun value : ℂ =>
        value + zetaCompletedPrimeTwoFaceGNSMatrixCoefficient f)
      hpositive).trans
      howner)

end ZetaAdmissibleFunction

end
end LFunctions
end Boundary
