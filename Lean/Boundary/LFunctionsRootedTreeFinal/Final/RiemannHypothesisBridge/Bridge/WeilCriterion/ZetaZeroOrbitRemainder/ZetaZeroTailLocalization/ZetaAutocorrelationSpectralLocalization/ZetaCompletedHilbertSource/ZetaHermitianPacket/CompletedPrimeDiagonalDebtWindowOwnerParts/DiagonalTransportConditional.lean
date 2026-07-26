import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaCompletedHilbertSource.ZetaHermitianPacket.CompletedPrimeDiagonalDebtWindowOwnerParts.DiagonalTransport

/-!
# Conditional diagonal-debt coordinate transport

This file exposes diagonal-debt transport from explicit completed
diagonal-debt real-coordinate `HasSum` inputs.
-/

namespace Boundary
namespace LFunctions

noncomputable section

namespace ZetaAdmissibleFunction

/-- Diagonal-debt real-coordinate `HasSum` inputs give the spectral majorant
used by diagonal-debt transport. -/
theorem zetaCompletedPrimeSpectralCoordinateMajorant_summable_of_diagonalDebtCoordinate_re_hasSum_transport_owner
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
  zetaCompletedPrimeSpectralCoordinateMajorant_summable_of_diagonalDebtCoordinate_re_hasSum_diagonalDebt_owner
    f C Creflect hhasSum hhasSumReflect

/-- Diagonal-debt real-coordinate `HasSum` inputs give summability of the
completed positive defect-square coordinate stream. -/
theorem zetaCompletedPrimeDefectKernelPositiveCoordinate_summable_of_diagonalDebtCoordinate_re_hasSum_transport_owner
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
        zetaCompletedPrimeDefectKernelPositiveCoordinate index f) :=
  let hmajorant :
      Summable
        (fun index : ZetaPrimePowerIndex =>
          zetaCompletedPrimeSpectralCoordinateMajorant index f) :=
    zetaCompletedPrimeSpectralCoordinateMajorant_summable_of_diagonalDebtCoordinate_re_hasSum_transport_owner
      f C Creflect hhasSum hhasSumReflect
  zetaCompletedPrimeDefectKernelPositiveCoordinate_summable_of_spectralCoordinateMajorant_summable_transport_owner
    f hmajorant

/-- Diagonal-debt real-coordinate `HasSum` inputs give the completed positive
defect-square coordinate stream with its raw coordinate-presentation sum. -/
theorem zetaCompletedPrimeDefectKernelPositiveCoordinate_hasSum_coordinateTsum_of_diagonalDebtCoordinate_re_hasSum_transport_owner
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
    HasSum
      (fun index : ZetaPrimePowerIndex =>
        zetaCompletedPrimeDefectKernelPositiveCoordinate index f)
      (zetaCompletedPrimeDefectKernelPositiveCoordinateTsum f) :=
  let hmajorant :
      Summable
        (fun index : ZetaPrimePowerIndex =>
          zetaCompletedPrimeSpectralCoordinateMajorant index f) :=
    zetaCompletedPrimeSpectralCoordinateMajorant_summable_of_diagonalDebtCoordinate_re_hasSum_transport_owner
      f C Creflect hhasSum hhasSumReflect
  zetaCompletedPrimeDefectKernelPositiveCoordinate_hasSum_coordinateTsum_of_spectralCoordinateMajorant_summable_transport_owner
    f hmajorant

/-- Diagonal-debt real-coordinate `HasSum` inputs give the completed positive
coordinate stream with the owner positive defect-square form as its sum. -/
theorem zetaCompletedPrimeDefectKernelPositiveCoordinate_hasSum_of_diagonalDebtCoordinate_re_hasSum_transport_owner
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
    HasSum
      (fun index : ZetaPrimePowerIndex =>
        zetaCompletedPrimeDefectKernelPositiveCoordinate index f)
      (zetaCompletedPrimeDefectKernelPositiveForm f) :=
  Eq.subst
    (motive := fun value : ℂ =>
      HasSum
        (fun index : ZetaPrimePowerIndex =>
          zetaCompletedPrimeDefectKernelPositiveCoordinate index f)
        value)
    (zetaCompletedPrimeDefectKernelPositiveCoordinateTsum_eq_owner_of_diagonalDebtCoordinate_re_hasSum_coordinateAssembly
      f C Creflect hhasSum hhasSumReflect hcoordinateZero)
    (zetaCompletedPrimeDefectKernelPositiveCoordinate_hasSum_coordinateTsum_of_diagonalDebtCoordinate_re_hasSum_transport_owner
      f C Creflect hhasSum hhasSumReflect)

/-- Diagonal-debt real-coordinate `HasSum` inputs give summability of the
signed completed symmetrized two-face coordinate stream. -/
theorem zetaCompletedPrimeTwoFaceGNSSymmetrizedCoordinate_neg_summable_of_diagonalDebtCoordinate_re_hasSum_transport_owner
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
        -zetaCompletedPrimeTwoFaceGNSSymmetrizedCoordinate index f) :=
  let hmajorant :
      Summable
        (fun index : ZetaPrimePowerIndex =>
          zetaCompletedPrimeSpectralCoordinateMajorant index f) :=
    zetaCompletedPrimeSpectralCoordinateMajorant_summable_of_diagonalDebtCoordinate_re_hasSum_transport_owner
      f C Creflect hhasSum hhasSumReflect
  zetaCompletedPrimeTwoFaceGNSSymmetrizedCoordinate_neg_summable_of_spectralCoordinateMajorant_summable_transport_owner
    f hmajorant

/-- Diagonal-debt real-coordinate `HasSum` inputs give the signed completed
symmetrized two-face coordinate stream with owner boundary-coefficient sum. -/
theorem zetaCompletedPrimeTwoFaceGNSSymmetrizedCoordinate_neg_hasSum_boundary_of_diagonalDebtCoordinate_re_hasSum_transport_owner
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
    HasSum
      (fun index : ZetaPrimePowerIndex =>
        -zetaCompletedPrimeTwoFaceGNSSymmetrizedCoordinate index f)
      (zetaCompletedPrimeTwoFaceGNSBoundaryCoefficient f) :=
  let hmajorant :
      Summable
        (fun index : ZetaPrimePowerIndex =>
          zetaCompletedPrimeSpectralCoordinateMajorant index f) :=
    zetaCompletedPrimeSpectralCoordinateMajorant_summable_of_diagonalDebtCoordinate_re_hasSum_transport_owner
      f C Creflect hhasSum hhasSumReflect
  zetaCompletedPrimeTwoFaceGNSSymmetrizedCoordinate_neg_hasSum_boundary_of_spectralCoordinateMajorant_summable_transport_owner
    f hmajorant

/-- Diagonal-debt real-coordinate `HasSum` inputs give the completed
symmetrized two-face coordinate stream with owner matrix-coefficient sum. -/
theorem zetaCompletedPrimeTwoFaceGNSSymmetrizedCoordinate_hasSum_of_diagonalDebtCoordinate_re_hasSum_transport_owner
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
    HasSum
      (fun index : ZetaPrimePowerIndex =>
        zetaCompletedPrimeTwoFaceGNSSymmetrizedCoordinate index f)
      (zetaCompletedPrimeTwoFaceGNSMatrixCoefficient f) :=
  zetaCompletedPrimeTwoFaceGNSSymmetrizedCoordinate_hasSum_transport_owner_of_neg_boundary
    f
    (zetaCompletedPrimeTwoFaceGNSSymmetrizedCoordinate_neg_hasSum_boundary_of_diagonalDebtCoordinate_re_hasSum_transport_owner
      f C Creflect hhasSum hhasSumReflect)

/-- Diagonal-debt real-coordinate `HasSum` inputs give the completed
diagonal-debt coordinate stream with the owner completed diagonal-debt form as
its sum. -/
theorem zetaCompletedPrimeDefectKernelDiagonalDebtCoordinate_hasSum_of_diagonalDebtCoordinate_re_hasSum_transport_owner
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
    HasSum
      (fun index : ZetaPrimePowerIndex =>
        zetaCompletedPrimeDefectKernelDiagonalDebtCoordinate index f)
      (zetaCompletedPrimeDefectKernelDiagonalDebt f) :=
  Eq.subst
    (motive := fun value : ℂ =>
      HasSum
        (fun index : ZetaPrimePowerIndex =>
          zetaCompletedPrimeDefectKernelDiagonalDebtCoordinate index f)
        value)
    (zetaCompletedPrimeDefectKernelDiagonalDebtCoordinateTsum_eq_owner_of_diagonalDebtCoordinate_re_hasSum_coordinateAssembly
      f C Creflect hhasSum hhasSumReflect hcoordinateZero)
    (zetaCompletedPrimeDefectKernelDiagonalDebtCoordinate_hasSum_coordinateTsum_of_diagonalDebtCoordinate_re_hasSum_windowLimit_owner
      f C Creflect hhasSum hhasSumReflect)

/-- Diagonal-debt real-coordinate `HasSum` inputs identify the raw completed
diagonal-debt coordinate presentation with the owner completed diagonal-debt
form. -/
theorem zetaCompletedPrimeDefectKernelDiagonalDebtCoordinateTsum_eq_owner_of_diagonalDebtCoordinate_re_hasSum
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
  zetaCompletedPrimeDefectKernelDiagonalDebtCoordinateTsum_eq_owner_of_diagonalDebtCoordinate_re_hasSum_coordinateAssembly
    f C Creflect hhasSum hhasSumReflect hcoordinateZero

/-- Diagonal-debt real-coordinate `HasSum` inputs identify the real parts of
the raw completed diagonal-debt coordinate presentation and the owner completed
diagonal-debt form. -/
theorem zetaCompletedPrimeDefectKernelDiagonalDebtCoordinateTsum_re_eq_owner_re_of_diagonalDebtCoordinate_re_hasSum
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
    Complex.re (zetaCompletedPrimeDefectKernelDiagonalDebtCoordinateTsum f) =
      Complex.re (zetaCompletedPrimeDefectKernelDiagonalDebt f) :=
  congrArg Complex.re
    (zetaCompletedPrimeDefectKernelDiagonalDebtCoordinateTsum_eq_owner_of_diagonalDebtCoordinate_re_hasSum
      f C Creflect hhasSum hhasSumReflect hcoordinateZero)

end ZetaAdmissibleFunction

end
end LFunctions
end Boundary
