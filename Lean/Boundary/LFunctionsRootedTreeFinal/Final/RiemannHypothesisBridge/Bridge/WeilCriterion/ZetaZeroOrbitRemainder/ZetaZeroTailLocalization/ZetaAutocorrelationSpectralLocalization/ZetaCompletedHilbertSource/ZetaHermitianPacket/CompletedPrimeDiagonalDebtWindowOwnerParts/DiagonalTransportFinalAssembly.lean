import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaCompletedHilbertSource.ZetaHermitianPacket.CompletedPrimeDiagonalDebtWindowOwnerParts.DiagonalTransport

/-!
# Completed diagonal-debt final HasSum assembly

This file owns the final compatibility assembly of the completed diagonal-debt
coordinate `HasSum` from the positive and two-face coordinate streams.
-/

namespace Boundary
namespace LFunctions

noncomputable section

namespace ZetaAdmissibleFunction

/-- Majorant summability identifies the raw completed positive coordinate
presentation with the owner completed positive defect-square form. -/
theorem zetaCompletedPrimeDefectKernelPositiveCoordinateTsum_eq_owner_of_spectralCoordinateMajorant_summable_finalAssembly
    (f : ZetaAdmissibleFunction)
    (hmajorant :
      Summable
        (fun index : ZetaPrimePowerIndex =>
          zetaCompletedPrimeSpectralCoordinateMajorant index f))
    (hcoordinateZero :
      Complex.re (zetaCompletedPrimeDefectKernelDiagonalDebtCoordinateTsum f) =
        0) :
    zetaCompletedPrimeDefectKernelPositiveCoordinateTsum f =
      zetaCompletedPrimeDefectKernelPositiveForm f :=
  let hre :
      Complex.re (zetaCompletedPrimeDefectKernelPositiveCoordinateTsum f) =
        Complex.re (zetaCompletedPrimeDefectKernelPositiveForm f) :=
    (zetaCompletedPrimeDefectKernelPositiveCoordinateTsum_re_eq_coordinateTsumRe_transport_owner
      f).trans
      ((zetaCompletedPrimeDefectKernelPositiveCoordinateTsumRe_eq_positiveChannel_of_spectralCoordinateMajorant_summable_positiveRealWindowLimit
        f hmajorant hcoordinateZero).trans
        (zetaCompletedPrimeDefectKernelPositiveForm_re_eq_positiveChannel_transport_owner
          f).symm)
  let him :
      Complex.im (zetaCompletedPrimeDefectKernelPositiveCoordinateTsum f) =
        Complex.im (zetaCompletedPrimeDefectKernelPositiveForm f) :=
    zetaCompletedPrimeDefectKernelPositiveCoordinateTsum_im_eq_owner_im_transport_owner
      f
  Complex.ext hre him

/-- Majorant summability gives the completed positive coordinate stream with
the owner positive defect-square form as its sum. -/
theorem zetaCompletedPrimeDefectKernelPositiveCoordinate_hasSum_of_spectralCoordinateMajorant_summable_finalAssembly
    (f : ZetaAdmissibleFunction)
    (hmajorant :
      Summable
        (fun index : ZetaPrimePowerIndex =>
          zetaCompletedPrimeSpectralCoordinateMajorant index f))
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
    (zetaCompletedPrimeDefectKernelPositiveCoordinateTsum_eq_owner_of_spectralCoordinateMajorant_summable_finalAssembly
      f hmajorant hcoordinateZero)
    (zetaCompletedPrimeDefectKernelPositiveCoordinate_hasSum_coordinateTsum_of_spectralCoordinateMajorant_summable_transport_owner
      f hmajorant)

/-- Majorant summability gives the completed symmetrized two-face coordinate
stream with owner matrix-coefficient sum. -/
theorem zetaCompletedPrimeTwoFaceGNSSymmetrizedCoordinate_hasSum_of_spectralCoordinateMajorant_summable_finalAssembly
    (f : ZetaAdmissibleFunction)
    (hmajorant :
      Summable
        (fun index : ZetaPrimePowerIndex =>
          zetaCompletedPrimeSpectralCoordinateMajorant index f)) :
    HasSum
      (fun index : ZetaPrimePowerIndex =>
        zetaCompletedPrimeTwoFaceGNSSymmetrizedCoordinate index f)
      (zetaCompletedPrimeTwoFaceGNSMatrixCoefficient f) :=
  zetaCompletedPrimeTwoFaceGNSSymmetrizedCoordinate_hasSum_transport_owner_of_neg_boundary
    f
    (zetaCompletedPrimeTwoFaceGNSSymmetrizedCoordinate_neg_hasSum_boundary_of_spectralCoordinateMajorant_summable_transport_owner
      f hmajorant)

/-- Majorant summability gives the completed diagonal-debt coordinate stream
with the owner completed diagonal-debt form as its sum. -/
theorem zetaCompletedPrimeDefectKernelDiagonalDebtCoordinate_hasSum_of_spectralCoordinateMajorant_summable_finalAssembly
    (f : ZetaAdmissibleFunction)
    (hmajorant :
      Summable
        (fun index : ZetaPrimePowerIndex =>
          zetaCompletedPrimeSpectralCoordinateMajorant index f))
    (hcoordinateZero :
      Complex.re (zetaCompletedPrimeDefectKernelDiagonalDebtCoordinateTsum f) =
        0) :
    HasSum
      (fun index : ZetaPrimePowerIndex =>
        zetaCompletedPrimeDefectKernelDiagonalDebtCoordinate index f)
      (zetaCompletedPrimeDefectKernelDiagonalDebt f) :=
  let positiveSeries : ZetaPrimePowerIndex → ℂ :=
    fun index : ZetaPrimePowerIndex =>
      zetaCompletedPrimeDefectKernelPositiveCoordinate index f
  let twoFaceSeries : ZetaPrimePowerIndex → ℂ :=
    fun index : ZetaPrimePowerIndex =>
      zetaCompletedPrimeTwoFaceGNSSymmetrizedCoordinate index f
  let diagonalSeries : ZetaPrimePowerIndex → ℂ :=
    fun index : ZetaPrimePowerIndex =>
      zetaCompletedPrimeDefectKernelDiagonalDebtCoordinate index f
  let positiveOwner : ℂ := zetaCompletedPrimeDefectKernelPositiveForm f
  let twoFaceOwner : ℂ := zetaCompletedPrimeTwoFaceGNSMatrixCoefficient f
  let diagonalOwner : ℂ := zetaCompletedPrimeDefectKernelDiagonalDebt f
  let hpositive :
      HasSum positiveSeries positiveOwner :=
    zetaCompletedPrimeDefectKernelPositiveCoordinate_hasSum_of_spectralCoordinateMajorant_summable_finalAssembly
      f hmajorant hcoordinateZero
  let htwoFace :
      HasSum twoFaceSeries twoFaceOwner :=
    zetaCompletedPrimeTwoFaceGNSSymmetrizedCoordinate_hasSum_of_spectralCoordinateMajorant_summable_finalAssembly
      f hmajorant
  let hadd :
      HasSum
        (fun index : ZetaPrimePowerIndex =>
          positiveSeries index + twoFaceSeries index)
        (positiveOwner + twoFaceOwner) :=
    hpositive.add htwoFace
  let hseries :
      diagonalSeries =
        (fun index : ZetaPrimePowerIndex =>
          positiveSeries index + twoFaceSeries index) :=
    zetaCompletedPrimeDefectKernelDiagonalDebtCoordinate_eq_positive_add_twoFace_transport_owner
      f
  let howner :
      diagonalOwner = positiveOwner + twoFaceOwner :=
    zetaCompletedPrimeDefectKernelDiagonalDebt_eq_positive_add_twoFace_transport_owner
      f
  let htarget :
      HasSum
        (fun index : ZetaPrimePowerIndex =>
          positiveSeries index + twoFaceSeries index)
        diagonalOwner :=
    Eq.subst
      (motive := fun value : ℂ =>
        HasSum
          (fun index : ZetaPrimePowerIndex =>
            positiveSeries index + twoFaceSeries index)
          value)
      howner.symm
      hadd
  let hdiagonal :
      HasSum diagonalSeries diagonalOwner :=
    Eq.subst
      (motive := fun series : ZetaPrimePowerIndex → ℂ =>
        HasSum series diagonalOwner)
      hseries.symm
      htarget
  hdiagonal

/-- Diagonal-debt real-coordinate `HasSum` inputs give the completed
diagonal-debt coordinate stream with the owner completed diagonal-debt form as
its sum at the final assembly level. -/
theorem zetaCompletedPrimeDefectKernelDiagonalDebtCoordinate_hasSum_of_diagonalDebtCoordinate_re_hasSum_finalAssembly
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
  let htransport :
      HasSum
        (fun index : ZetaPrimePowerIndex =>
          zetaCompletedPrimeDefectKernelDiagonalDebtCoordinate index f)
        (zetaCompletedPrimeDefectKernelDiagonalDebt f) :=
    let hmajorant :
        Summable
          (fun index : ZetaPrimePowerIndex =>
            zetaCompletedPrimeSpectralCoordinateMajorant index f) :=
      zetaCompletedPrimeSpectralCoordinateMajorant_summable_of_diagonalDebtCoordinate_re_hasSum_diagonalDebt_owner
        f C Creflect hhasSum hhasSumReflect
    zetaCompletedPrimeDefectKernelDiagonalDebtCoordinate_hasSum_of_spectralCoordinateMajorant_summable_finalAssembly
      f
      hmajorant
      hcoordinateZero
  let hleft : hhasSum = hhasSum :=
    Eq.refl hhasSum
  let hright : hhasSumReflect = hhasSumReflect :=
    Eq.refl hhasSumReflect
  Eq.ndrec
    (motive := fun proof =>
      HasSum
        (fun index : ZetaPrimePowerIndex =>
          zetaCompletedPrimeDefectKernelDiagonalDebtCoordinate index f)
        (zetaCompletedPrimeDefectKernelDiagonalDebt f))
    (Eq.ndrec
      (motive := fun proof =>
        HasSum
          (fun index : ZetaPrimePowerIndex =>
            zetaCompletedPrimeDefectKernelDiagonalDebtCoordinate index f)
          (zetaCompletedPrimeDefectKernelDiagonalDebt f))
      htransport
      hright)
    hleft

end ZetaAdmissibleFunction

end
end LFunctions
end Boundary
