import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaCompletedHilbertSource.ZetaHermitianPacket.CompletedPrimePowerPackets
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaCompletedHilbertSource.ZetaHermitianPacket.CompletedPrimeDiagonalDebtWindowOwnerParts.SpectralMajorant
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaCompletedHilbertSource.ZetaHermitianPacket.CompletedPrimeDiagonalDebtWindowOwnerParts.DiagonalTransportParts.WindowLimit

/-!
# Diagonal-debt coordinate transport

This file owns the transport from the completed diagonal-debt coordinate
presentation to the completed diagonal-debt owner form.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open Filter
open scoped Topology

namespace ZetaAdmissibleFunction

/-- Majorant summability gives summability of the completed positive
defect-square coordinate stream. -/
theorem zetaCompletedPrimeDefectKernelPositiveCoordinate_summable_of_spectralCoordinateMajorant_summable_transport_owner
    (f : ZetaAdmissibleFunction)
    (hmajorant :
      Summable
        (fun index : ZetaPrimePowerIndex =>
          zetaCompletedPrimeSpectralCoordinateMajorant index f)) :
    Summable
      (fun index : ZetaPrimePowerIndex =>
        zetaCompletedPrimeDefectKernelPositiveCoordinate index f) :=
  summable_zetaCompletedPrimeDefectKernelPositiveCoordinate_of_spectralMajorant
    f
    hmajorant

/-- Majorant summability gives the completed positive defect-square coordinate
stream with its raw coordinate-presentation sum. -/
theorem zetaCompletedPrimeDefectKernelPositiveCoordinate_hasSum_coordinateTsum_of_spectralCoordinateMajorant_summable_transport_owner
    (f : ZetaAdmissibleFunction)
    (hmajorant :
      Summable
        (fun index : ZetaPrimePowerIndex =>
          zetaCompletedPrimeSpectralCoordinateMajorant index f)) :
    HasSum
      (fun index : ZetaPrimePowerIndex =>
        zetaCompletedPrimeDefectKernelPositiveCoordinate index f)
      (zetaCompletedPrimeDefectKernelPositiveCoordinateTsum f) :=
  (zetaCompletedPrimeDefectKernelPositiveCoordinate_summable_of_spectralCoordinateMajorant_summable_transport_owner
    f hmajorant).hasSum

/-- The real part of the raw positive coordinate presentation is its named
coordinate-presentation scalar. -/
theorem zetaCompletedPrimeDefectKernelPositiveCoordinateTsum_re_eq_coordinateTsumRe_transport_owner
    (f : ZetaAdmissibleFunction) :
    Complex.re (zetaCompletedPrimeDefectKernelPositiveCoordinateTsum f) =
      zetaCompletedPrimeDefectKernelPositiveCoordinateTsumRe f :=
  zetaCompletedPrimeDefectKernelPositiveCoordinateTsum_re_eq_coordinateTsumRe_coordinateAssembly
    f

/-- The real scalar of the owner completed positive defect-square form is its
named positive channel. -/
theorem zetaCompletedPrimeDefectKernelPositiveForm_re_eq_positiveChannel_transport_owner
    (f : ZetaAdmissibleFunction) :
    Complex.re (zetaCompletedPrimeDefectKernelPositiveForm f) =
      completedPrimeDefectKernelPositiveChannel f :=
  zetaCompletedPrimeDefectKernelPositiveForm_re_eq_positiveChannel_coordinateAssembly
    f

/-- Diagonal-debt real-window convergence identifies the raw positive
coordinate scalar with the owner positive channel. -/
theorem zetaCompletedPrimeDefectKernelPositiveCoordinateTsumRe_eq_positiveChannel_of_diagonalRealWindow_tendsto_transport_owner
    (f : ZetaAdmissibleFunction)
    (hmajorant :
      Summable
        (fun index : ZetaPrimePowerIndex =>
          zetaCompletedPrimeSpectralCoordinateMajorant index f))
    (hdiagonal :
      Tendsto
        (fun N : ℕ => zetaCompletedPrimeDefectKernelDiagonalDebtRealWindow N f)
        atTop
        (𝓝 (Complex.re (zetaCompletedPrimeDefectKernelDiagonalDebt f)))) :
    zetaCompletedPrimeDefectKernelPositiveCoordinateTsumRe f =
      completedPrimeDefectKernelPositiveChannel f :=
  zetaCompletedPrimeDefectKernelPositiveCoordinateTsumRe_eq_completedPrimeDefectKernelPositiveChannel_of_diagonalDebtRealWindow_tendsto
    f
    hmajorant
    hdiagonal

/-- One completed positive defect-square coordinate is real-valued. -/
theorem zetaCompletedPrimeDefectKernelPositiveCoordinate_im_eq_zero_transport_owner
    (index : ZetaPrimePowerIndex) (f : ZetaAdmissibleFunction) :
    Complex.im
      (zetaCompletedPrimeDefectKernelPositiveCoordinate index f) = 0 :=
  zetaCompletedPrimeDefectKernelPositiveCoordinate_im_eq_zero_coordinateAssembly
    index f

/-- The raw completed positive defect-square coordinate presentation is
real-valued. -/
theorem zetaCompletedPrimeDefectKernelPositiveCoordinateTsum_im_eq_zero_transport_owner
    (f : ZetaAdmissibleFunction) :
    Complex.im (zetaCompletedPrimeDefectKernelPositiveCoordinateTsum f) = 0 :=
  zetaCompletedPrimeDefectKernelPositiveCoordinateTsum_im_eq_zero_coordinateAssembly
    f

/-- One finite prime diagonal-debt coordinate is real-valued. -/
theorem zetaPrimeDefectKernelDiagonalDebtCoordinate_im_eq_zero_transport_owner
    (p n : ℕ) (f : ZetaAdmissibleFunction) :
    Complex.im (zetaPrimeDefectKernelDiagonalDebtCoordinate p n f) = 0 :=
  zetaPrimeDefectKernelDiagonalDebtCoordinate_im_eq_zero_coordinateAssembly
    p n f

/-- The finite prime diagonal-debt form is real-valued. -/
theorem zetaPrimeDefectKernelDiagonalDebt_im_eq_zero_transport_owner
    (f : ZetaAdmissibleFunction) :
    Complex.im (zetaPrimeDefectKernelDiagonalDebt f) = 0 :=
  zetaPrimeDefectKernelDiagonalDebt_im_eq_zero_coordinateAssembly f

/-- The owner completed diagonal-debt form is real-valued. -/
theorem zetaCompletedPrimeDefectKernelDiagonalDebt_im_eq_zero_transport_owner
    (f : ZetaAdmissibleFunction) :
    Complex.im (zetaCompletedPrimeDefectKernelDiagonalDebt f) = 0 :=
  zetaCompletedPrimeDefectKernelDiagonalDebt_im_eq_zero_coordinateAssembly f

/-- The owner completed positive defect-square form is real-valued. -/
theorem zetaCompletedPrimeDefectKernelPositiveForm_im_eq_zero_transport_owner
    (f : ZetaAdmissibleFunction) :
    Complex.im (zetaCompletedPrimeDefectKernelPositiveForm f) = 0 :=
  zetaCompletedPrimeDefectKernelPositiveForm_im_eq_zero_coordinateAssembly f

/-- The raw completed positive coordinate presentation has the same imaginary
part as the owner completed positive defect-square form. -/
theorem zetaCompletedPrimeDefectKernelPositiveCoordinateTsum_im_eq_owner_im_transport_owner
    (f : ZetaAdmissibleFunction) :
    Complex.im (zetaCompletedPrimeDefectKernelPositiveCoordinateTsum f) =
      Complex.im (zetaCompletedPrimeDefectKernelPositiveForm f) :=
  zetaCompletedPrimeDefectKernelPositiveCoordinateTsum_im_eq_owner_im_coordinateAssembly
    f

/-- Majorant summability gives summability of the signed completed symmetrized
two-face coordinate stream. -/
theorem zetaCompletedPrimeTwoFaceGNSSymmetrizedCoordinate_neg_summable_of_spectralCoordinateMajorant_summable_transport_owner
    (f : ZetaAdmissibleFunction)
    (hmajorant :
      Summable
        (fun index : ZetaPrimePowerIndex =>
          zetaCompletedPrimeSpectralCoordinateMajorant index f)) :
    Summable
      (fun index : ZetaPrimePowerIndex =>
        -zetaCompletedPrimeTwoFaceGNSSymmetrizedCoordinate index f) :=
  (summable_zetaCompletedPrimeTwoFaceGNSSymmetrizedCoordinate_of_spectralMajorant
    f
    hmajorant).neg

/-- Majorant summability gives the signed completed symmetrized two-face
coordinate stream with owner boundary-coefficient sum. -/
theorem zetaCompletedPrimeTwoFaceGNSSymmetrizedCoordinate_neg_hasSum_boundary_of_spectralCoordinateMajorant_summable_transport_owner
    (f : ZetaAdmissibleFunction)
    (hmajorant :
      Summable
        (fun index : ZetaPrimePowerIndex =>
          zetaCompletedPrimeSpectralCoordinateMajorant index f)) :
    HasSum
      (fun index : ZetaPrimePowerIndex =>
        -zetaCompletedPrimeTwoFaceGNSSymmetrizedCoordinate index f)
      (zetaCompletedPrimeTwoFaceGNSBoundaryCoefficient f) :=
  let hsummable :
      Summable
        (fun index : ZetaPrimePowerIndex =>
          -zetaCompletedPrimeTwoFaceGNSSymmetrizedCoordinate index f) :=
    zetaCompletedPrimeTwoFaceGNSSymmetrizedCoordinate_neg_summable_of_spectralCoordinateMajorant_summable_transport_owner
      f hmajorant
  let hhasSum :
      HasSum
        (fun index : ZetaPrimePowerIndex =>
          -zetaCompletedPrimeTwoFaceGNSSymmetrizedCoordinate index f)
        (∑' index : ZetaPrimePowerIndex,
          -zetaCompletedPrimeTwoFaceGNSSymmetrizedCoordinate index f) :=
    hsummable.hasSum
  let hboundary :
      (∑' index : ZetaPrimePowerIndex,
        -zetaCompletedPrimeTwoFaceGNSSymmetrizedCoordinate index f) =
        zetaCompletedPrimeTwoFaceGNSBoundaryCoefficient f :=
    zetaCompletedPrimeTwoFaceGNSBoundaryCoordinate_tsum_eq_boundaryCoefficient
      f
  Eq.subst
    (motive := fun value : ℂ =>
      HasSum
        (fun index : ZetaPrimePowerIndex =>
          -zetaCompletedPrimeTwoFaceGNSSymmetrizedCoordinate index f)
        value)
    hboundary
    hhasSum

/-- Negating the completed two-face boundary-coordinate sum gives the owner
matrix-coefficient sum. -/
theorem zetaCompletedPrimeTwoFaceGNSSymmetrizedCoordinate_hasSum_transport_owner_of_neg_boundary
    (f : ZetaAdmissibleFunction)
    (hboundary :
      HasSum
        (fun index : ZetaPrimePowerIndex =>
          -zetaCompletedPrimeTwoFaceGNSSymmetrizedCoordinate index f)
        (zetaCompletedPrimeTwoFaceGNSBoundaryCoefficient f)) :
    HasSum
      (fun index : ZetaPrimePowerIndex =>
        zetaCompletedPrimeTwoFaceGNSSymmetrizedCoordinate index f)
      (zetaCompletedPrimeTwoFaceGNSMatrixCoefficient f) :=
  let hneg :
      HasSum
        (fun index : ZetaPrimePowerIndex =>
          -(-zetaCompletedPrimeTwoFaceGNSSymmetrizedCoordinate index f))
        (-zetaCompletedPrimeTwoFaceGNSBoundaryCoefficient f) :=
    hboundary.neg
  let hseries :
      (fun index : ZetaPrimePowerIndex =>
        -(-zetaCompletedPrimeTwoFaceGNSSymmetrizedCoordinate index f)) =
        (fun index : ZetaPrimePowerIndex =>
          zetaCompletedPrimeTwoFaceGNSSymmetrizedCoordinate index f) :=
    funext
      (fun index : ZetaPrimePowerIndex =>
        neg_neg
          (zetaCompletedPrimeTwoFaceGNSSymmetrizedCoordinate index f))
  let hboundaryEq :
      zetaCompletedPrimeTwoFaceGNSBoundaryCoefficient f =
        -zetaCompletedPrimeTwoFaceGNSMatrixCoefficient f :=
    zetaCompletedPrimeTwoFaceGNSBoundaryCoefficient_eq_neg_matrixCoefficient
      f
  let howner :
      -zetaCompletedPrimeTwoFaceGNSBoundaryCoefficient f =
        zetaCompletedPrimeTwoFaceGNSMatrixCoefficient f :=
    Eq.trans
      (congrArg Neg.neg hboundaryEq)
      (neg_neg (zetaCompletedPrimeTwoFaceGNSMatrixCoefficient f))
  Eq.subst
    (motive := fun series : ZetaPrimePowerIndex → ℂ =>
      HasSum series (zetaCompletedPrimeTwoFaceGNSMatrixCoefficient f))
    hseries
    (Eq.subst
      (motive := fun value : ℂ =>
        HasSum
          (fun index : ZetaPrimePowerIndex =>
            -(-zetaCompletedPrimeTwoFaceGNSSymmetrizedCoordinate index f))
          value)
      howner
      hneg)

/-- The completed diagonal-debt coordinate stream is the pointwise sum of the
positive defect-square stream and the symmetrized two-face stream. -/
theorem zetaCompletedPrimeDefectKernelDiagonalDebtCoordinate_eq_positive_add_twoFace_transport_owner
    (f : ZetaAdmissibleFunction) :
    (fun index : ZetaPrimePowerIndex =>
      zetaCompletedPrimeDefectKernelDiagonalDebtCoordinate index f) =
      (fun index : ZetaPrimePowerIndex =>
        zetaCompletedPrimeDefectKernelPositiveCoordinate index f +
          zetaCompletedPrimeTwoFaceGNSSymmetrizedCoordinate index f) :=
  funext
    (fun index : ZetaPrimePowerIndex =>
      (zetaCompletedPrimeDefectKernelPositiveCoordinate_add_twoFace_eq_diagonalDebtCoordinate
        index f).symm)

/-- The owner completed diagonal-debt form is the sum of the owner positive
defect-square form and the owner symmetrized two-face coefficient. -/
theorem zetaCompletedPrimeDefectKernelDiagonalDebt_eq_positive_add_twoFace_transport_owner
    (f : ZetaAdmissibleFunction) :
    zetaCompletedPrimeDefectKernelDiagonalDebt f =
      zetaCompletedPrimeDefectKernelPositiveForm f +
        zetaCompletedPrimeTwoFaceGNSMatrixCoefficient f :=
  (zetaCompletedPrimeDefectKernelPositiveWindow_expansion_passes_to_completedForms
    f).symm

end ZetaAdmissibleFunction

end
end LFunctions
end Boundary
