import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaCompletedHilbertSource.ZetaHermitianPacket.CompletedPrimeDiagonalDebtWindowOwnerParts.DiagonalTransportParts.PositiveRealWindowLimit

/-!
# Conditional positive real-window limit wrappers

This file exposes the positive real-window limit consequences from explicit
completed diagonal-debt real-coordinate `HasSum` inputs.
-/

namespace Boundary
namespace LFunctions

noncomputable section

namespace ZetaAdmissibleFunction

/-- Diagonal-debt real-coordinate `HasSum` inputs give the spectral majorant
summability used by positive real-window transport. -/
theorem zetaCompletedPrimeSpectralCoordinateMajorant_summable_of_diagonalDebtCoordinate_re_hasSum_positiveRealWindowLimit
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

/-- Diagonal-debt real-coordinate `HasSum` inputs give the completed
symmetrized two-face coordinate stream with the completed matrix coefficient
as its sum. -/
theorem zetaCompletedPrimeTwoFaceGNSSymmetrizedCoordinate_hasSum_matrixCoefficient_of_diagonalDebtCoordinate_re_hasSum_positiveRealWindowLimit
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
  let hmajorant :
      Summable
        (fun index : ZetaPrimePowerIndex =>
          zetaCompletedPrimeSpectralCoordinateMajorant index f) :=
    zetaCompletedPrimeSpectralCoordinateMajorant_summable_of_diagonalDebtCoordinate_re_hasSum_positiveRealWindowLimit
      f C Creflect hhasSum hhasSumReflect
  zetaCompletedPrimeTwoFaceGNSSymmetrizedCoordinate_hasSum_matrixCoefficient_of_spectralCoordinateMajorant_summable_positiveRealWindowLimit
    f hmajorant

/-- Diagonal-debt real-coordinate `HasSum` inputs give convergence of completed
two-face matrix-coefficient windows to the owner completed matrix
coefficient. -/
theorem zetaCompletedPrimeTwoFaceGNSMatrixCoefficientWindow_tendsto_matrixCoefficient_of_diagonalDebtCoordinate_re_hasSum_positiveRealWindowLimit
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
    Tendsto
      (fun N : ℕ => zetaCompletedPrimeTwoFaceGNSMatrixCoefficientWindow N f)
      atTop
      (𝓝 (zetaCompletedPrimeTwoFaceGNSMatrixCoefficient f)) :=
  let hmajorant :
      Summable
        (fun index : ZetaPrimePowerIndex =>
          zetaCompletedPrimeSpectralCoordinateMajorant index f) :=
    zetaCompletedPrimeSpectralCoordinateMajorant_summable_of_diagonalDebtCoordinate_re_hasSum_positiveRealWindowLimit
      f C Creflect hhasSum hhasSumReflect
  zetaCompletedPrimeTwoFaceGNSMatrixCoefficientWindow_tendsto_matrixCoefficient_of_spectralCoordinateMajorant_summable_positiveRealWindowLimit
    f hmajorant

/-- Diagonal-debt real-coordinate `HasSum` inputs identify the completed and
raw two-face real coefficients. -/
theorem zetaCompletedPrimeTwoFaceGNSMatrixCoefficient_re_eq_rawTwoFace_re_of_diagonalDebtCoordinate_re_hasSum_positiveRealWindowLimit
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
    Complex.re (zetaCompletedPrimeTwoFaceGNSMatrixCoefficient f) =
      Complex.re (zetaPrimeTwoFaceGNSMatrixCoefficient f) :=
  let hmajorant :
      Summable
        (fun index : ZetaPrimePowerIndex =>
          zetaCompletedPrimeSpectralCoordinateMajorant index f) :=
    zetaCompletedPrimeSpectralCoordinateMajorant_summable_of_diagonalDebtCoordinate_re_hasSum_positiveRealWindowLimit
      f C Creflect hhasSum hhasSumReflect
  zetaCompletedPrimeTwoFaceGNSMatrixCoefficient_re_eq_rawTwoFace_re_of_spectralCoordinateMajorant_summable_positiveRealWindowLimit
    f hmajorant

/-- Diagonal-debt real-coordinate `HasSum` inputs give vanishing of the real
owner completed diagonal-debt scalar. -/
theorem zetaCompletedPrimeDefectKernelDiagonalDebt_re_eq_zero_of_diagonalDebtCoordinate_re_hasSum_positiveRealWindowLimit
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
    Complex.re (zetaCompletedPrimeDefectKernelDiagonalDebt f) = 0 :=
  let hmajorant :
      Summable
        (fun index : ZetaPrimePowerIndex =>
          zetaCompletedPrimeSpectralCoordinateMajorant index f) :=
    zetaCompletedPrimeSpectralCoordinateMajorant_summable_of_diagonalDebtCoordinate_re_hasSum_positiveRealWindowLimit
      f C Creflect hhasSum hhasSumReflect
  zetaCompletedPrimeDefectKernelDiagonalDebt_re_eq_zero_of_spectralCoordinateMajorant_summable_positiveRealWindowLimit
    f hmajorant

/-- Diagonal-debt real-coordinate `HasSum` inputs and coordinate
annihilation identify the raw completed diagonal-debt coordinate presentation
with the owner real scalar. -/
theorem zetaCompletedPrimeDefectKernelDiagonalDebtCoordinateTsum_re_eq_ownerRe_of_diagonalDebtCoordinate_re_hasSum_positiveRealWindowLimit
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
  let hmajorant :
      Summable
        (fun index : ZetaPrimePowerIndex =>
          zetaCompletedPrimeSpectralCoordinateMajorant index f) :=
    zetaCompletedPrimeSpectralCoordinateMajorant_summable_of_diagonalDebtCoordinate_re_hasSum_positiveRealWindowLimit
      f C Creflect hhasSum hhasSumReflect
  zetaCompletedPrimeDefectKernelDiagonalDebtCoordinateTsum_re_eq_ownerRe_of_spectralCoordinateMajorant_summable_positiveRealWindowLimit
    f hmajorant hcoordinateZero

/-- Diagonal-debt real-coordinate `HasSum` inputs and coordinate
annihilation give convergence of completed diagonal-debt real windows to the
real owner completed diagonal debt. -/
theorem zetaCompletedPrimeDefectKernelDiagonalDebtRealWindow_tendsto_ownerRe_of_diagonalDebtCoordinate_re_hasSum_positiveRealWindowLimit
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
    Tendsto
      (fun N : ℕ => zetaCompletedPrimeDefectKernelDiagonalDebtRealWindow N f)
      atTop
      (𝓝 (Complex.re (zetaCompletedPrimeDefectKernelDiagonalDebt f))) :=
  let hmajorant :
      Summable
        (fun index : ZetaPrimePowerIndex =>
          zetaCompletedPrimeSpectralCoordinateMajorant index f) :=
    zetaCompletedPrimeSpectralCoordinateMajorant_summable_of_diagonalDebtCoordinate_re_hasSum_positiveRealWindowLimit
      f C Creflect hhasSum hhasSumReflect
  zetaCompletedPrimeDefectKernelDiagonalDebtRealWindow_tendsto_ownerRe_of_spectralCoordinateMajorant_summable_positiveRealWindowLimit
    f hmajorant hcoordinateZero

/-- Diagonal-debt real-coordinate `HasSum` inputs and coordinate
annihilation give convergence of completed positive real windows to the owner
positive channel. -/
theorem zetaCompletedPrimeDefectKernelPositiveRealWindow_tendsto_positiveChannel_of_diagonalDebtCoordinate_re_hasSum_positiveRealWindowLimit
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
    Tendsto
      (fun N : ℕ => zetaCompletedPrimeDefectKernelPositiveRealWindow N f)
      atTop
      (𝓝 (completedPrimeDefectKernelPositiveChannel f)) :=
  let hmajorant :
      Summable
        (fun index : ZetaPrimePowerIndex =>
          zetaCompletedPrimeSpectralCoordinateMajorant index f) :=
    zetaCompletedPrimeSpectralCoordinateMajorant_summable_of_diagonalDebtCoordinate_re_hasSum_positiveRealWindowLimit
      f C Creflect hhasSum hhasSumReflect
  zetaCompletedPrimeDefectKernelPositiveRealWindow_tendsto_positiveChannel_of_spectralCoordinateMajorant_summable_positiveRealWindowLimit
    f hmajorant hcoordinateZero

/-- Diagonal-debt real-coordinate `HasSum` inputs and coordinate
annihilation identify the raw completed positive coordinate real scalar with
the owner positive channel. -/
theorem zetaCompletedPrimeDefectKernelPositiveCoordinateTsumRe_eq_positiveChannel_of_diagonalDebtCoordinate_re_hasSum_positiveRealWindowLimit
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
    zetaCompletedPrimeSpectralCoordinateMajorant_summable_of_diagonalDebtCoordinate_re_hasSum_positiveRealWindowLimit
      f C Creflect hhasSum hhasSumReflect
  zetaCompletedPrimeDefectKernelPositiveCoordinateTsumRe_eq_positiveChannel_of_spectralCoordinateMajorant_summable_positiveRealWindowLimit
    f hmajorant hcoordinateZero

end ZetaAdmissibleFunction

end
end LFunctions
end Boundary
