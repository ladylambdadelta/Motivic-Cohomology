
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaCompletedHilbertSource.ZetaHermitianPacket.CompletedPrimePowerPackets
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaCompletedHilbertSource.ZetaHermitianPacket.HermitianBoundaryDefect
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaCompletedHilbertSource.ZetaHermitianPacket.CompletedPrimeDiagonalDebtWindowOwnerParts.SpectralMajorant

/-!
# Completed diagonal-debt coordinate assembly

This file owns the coordinate-to-owner transport for the completed diagonal
debt.  Window convergence and downstream real scalar arguments consume this
assembly theorem rather than restating it.
-/

namespace Boundary
namespace LFunctions

noncomputable section

namespace ZetaAdmissibleFunction

/-- The real part of the raw completed positive coordinate presentation is its
named coordinate-presentation scalar. -/
theorem zetaCompletedPrimeDefectKernelPositiveCoordinateTsum_re_eq_coordinateTsumRe_coordinateAssembly
    (f : ZetaAdmissibleFunction) :
    Complex.re (zetaCompletedPrimeDefectKernelPositiveCoordinateTsum f) =
      zetaCompletedPrimeDefectKernelPositiveCoordinateTsumRe f :=
  Eq.refl (Complex.re (zetaCompletedPrimeDefectKernelPositiveCoordinateTsum f))

/-- The real scalar of the owner completed positive defect-square form is its
named positive channel. -/
theorem zetaCompletedPrimeDefectKernelPositiveForm_re_eq_positiveChannel_coordinateAssembly
    (f : ZetaAdmissibleFunction) :
    Complex.re (zetaCompletedPrimeDefectKernelPositiveForm f) =
      completedPrimeDefectKernelPositiveChannel f :=
  Eq.refl (Complex.re (zetaCompletedPrimeDefectKernelPositiveForm f))

/-- One completed positive defect-square coordinate is real-valued. -/
theorem zetaCompletedPrimeDefectKernelPositiveCoordinate_im_eq_zero_coordinateAssembly
    (index : ZetaPrimePowerIndex) (f : ZetaAdmissibleFunction) :
    Complex.im
      (zetaCompletedPrimeDefectKernelPositiveCoordinate index f) = 0 :=
  let difference : ℂ :=
    zetaCompletedPrimeSpectralAmplitudeIndex index f -
      zetaCompletedPrimeOppositeSpectralAmplitudeIndex index f
  let hcoordinate :
      zetaCompletedPrimeDefectKernelPositiveCoordinate index f =
        difference * star difference :=
    Eq.refl (zetaCompletedPrimeDefectKernelPositiveCoordinate index f)
  let hmul :
      difference * star difference =
        (Complex.normSq difference : ℂ) :=
    Complex.mul_conj difference
  Eq.trans
    (congrArg Complex.im hcoordinate)
    ((congrArg Complex.im hmul).trans
      (Complex.ofReal_im (Complex.normSq difference)))

/-- The raw completed positive defect-square coordinate presentation is
real-valued. -/
theorem zetaCompletedPrimeDefectKernelPositiveCoordinateTsum_im_eq_zero_coordinateAssembly
    (f : ZetaAdmissibleFunction) :
    Complex.im (zetaCompletedPrimeDefectKernelPositiveCoordinateTsum f) = 0 :=
  complex_im_tsum_eq_zero_of_forall_im_eq_zero
    (fun index : ZetaPrimePowerIndex =>
      zetaCompletedPrimeDefectKernelPositiveCoordinate index f)
    (fun index : ZetaPrimePowerIndex =>
      zetaCompletedPrimeDefectKernelPositiveCoordinate_im_eq_zero_coordinateAssembly
        index f)

/-- One finite prime diagonal-debt coordinate is real-valued. -/
theorem zetaPrimeDefectKernelDiagonalDebtCoordinate_im_eq_zero_coordinateAssembly
    (p n : ℕ) (f : ZetaAdmissibleFunction) :
    Complex.im (zetaPrimeDefectKernelDiagonalDebtCoordinate p n f) = 0 :=
  let positiveValue : ℂ :=
    zetaCompletedExplicitFormulaPrimeSpectralAmplitude p n f
  let negativeValue : ℂ :=
    zetaCompletedExplicitFormulaPrimeOppositeSpectralAmplitude p n f
  let hcoordinate :
      zetaPrimeDefectKernelDiagonalDebtCoordinate p n f =
        positiveValue * star positiveValue +
          negativeValue * star negativeValue :=
    Eq.refl (zetaPrimeDefectKernelDiagonalDebtCoordinate p n f)
  let hpositive :
      positiveValue * star positiveValue =
        (Complex.normSq positiveValue : ℂ) :=
    Complex.mul_conj positiveValue
  let hnegative :
      negativeValue * star negativeValue =
        (Complex.normSq negativeValue : ℂ) :=
    Complex.mul_conj negativeValue
  let hrewritePositive :
      Complex.im
          (positiveValue * star positiveValue +
            negativeValue * star negativeValue) =
        Complex.im
          ((Complex.normSq positiveValue : ℂ) +
            negativeValue * star negativeValue) :=
    congrArg
      (fun value : ℂ =>
        Complex.im (value + negativeValue * star negativeValue))
      hpositive
  let hrewriteNegative :
      Complex.im
          ((Complex.normSq positiveValue : ℂ) +
            negativeValue * star negativeValue) =
        Complex.im
          ((Complex.normSq positiveValue : ℂ) +
            (Complex.normSq negativeValue : ℂ)) :=
    congrArg
      (fun value : ℂ =>
        Complex.im ((Complex.normSq positiveValue : ℂ) + value))
      hnegative
  let hadd :
      ((Complex.normSq positiveValue : ℂ) +
          (Complex.normSq negativeValue : ℂ)) =
        ((Complex.normSq positiveValue +
          Complex.normSq negativeValue : ℝ) : ℂ) :=
    (Complex.ofReal_add
      (Complex.normSq positiveValue)
      (Complex.normSq negativeValue)).symm
  let hofReal :
      Complex.im
          ((Complex.normSq positiveValue : ℂ) +
            (Complex.normSq negativeValue : ℂ)) = 0 :=
    Eq.trans
      (congrArg Complex.im hadd)
      (Complex.ofReal_im
        (Complex.normSq positiveValue + Complex.normSq negativeValue))
  let hsum :
      Complex.im
          (positiveValue * star positiveValue +
            negativeValue * star negativeValue) = 0 :=
    hrewritePositive.trans (hrewriteNegative.trans hofReal)
  Eq.trans
    (congrArg Complex.im hcoordinate)
    hsum

/-- The finite prime diagonal-debt form is real-valued. -/
theorem zetaPrimeDefectKernelDiagonalDebt_im_eq_zero_coordinateAssembly
    (f : ZetaAdmissibleFunction) :
    Complex.im (zetaPrimeDefectKernelDiagonalDebt f) = 0 :=
  let hsum :
      Complex.im
          (∑ label in zetaCompletedExplicitFormulaPrimeSupport,
            zetaPrimeDefectKernelDiagonalDebtCoordinate label.1 label.2 f) =
        ∑ label in zetaCompletedExplicitFormulaPrimeSupport,
          Complex.im
            (zetaPrimeDefectKernelDiagonalDebtCoordinate label.1 label.2 f) :=
    Complex.im_sum
      zetaCompletedExplicitFormulaPrimeSupport
      (fun label : ℕ × ℕ =>
        zetaPrimeDefectKernelDiagonalDebtCoordinate label.1 label.2 f)
  let hzero :
      (∑ label in zetaCompletedExplicitFormulaPrimeSupport,
        Complex.im
          (zetaPrimeDefectKernelDiagonalDebtCoordinate label.1 label.2 f)) =
        0 :=
    Finset.sum_eq_zero
      (fun label supportMembership =>
        zetaPrimeDefectKernelDiagonalDebtCoordinate_im_eq_zero_coordinateAssembly
          label.1 label.2 f)
  hsum.trans hzero

/-- The owner completed diagonal-debt form is real-valued. -/
theorem zetaCompletedPrimeDefectKernelDiagonalDebt_im_eq_zero_coordinateAssembly
    (f : ZetaAdmissibleFunction) :
    Complex.im (zetaCompletedPrimeDefectKernelDiagonalDebt f) = 0 :=
  let finiteDiagonal : ℂ := zetaPrimeDefectKernelDiagonalDebt f
  let finiteTwoFace : ℂ := zetaPrimeTwoFaceGNSMatrixCoefficient f
  let completedTwoFace : ℂ := zetaCompletedPrimeTwoFaceGNSMatrixCoefficient f
  let hdefinition :
      zetaCompletedPrimeDefectKernelDiagonalDebt f =
        finiteDiagonal - finiteTwoFace + completedTwoFace :=
    Eq.refl (zetaCompletedPrimeDefectKernelDiagonalDebt f)
  let hfiniteDiagonal :
      Complex.im finiteDiagonal = 0 :=
    zetaPrimeDefectKernelDiagonalDebt_im_eq_zero_coordinateAssembly f
  let hfiniteTwoFace :
      Complex.im finiteTwoFace = 0 :=
    zetaPrimeTwoFaceGNSMatrixCoefficient_im_eq_zero f
  let hcompletedTwoFace :
      Complex.im completedTwoFace = 0 :=
    zetaCompletedPrimeTwoFaceGNSMatrixCoefficient_im_eq_zero f
  let hsub :
      Complex.im (finiteDiagonal - finiteTwoFace) =
        Complex.im finiteDiagonal - Complex.im finiteTwoFace :=
    Complex.sub_im finiteDiagonal finiteTwoFace
  let hadd :
      Complex.im (finiteDiagonal - finiteTwoFace + completedTwoFace) =
        Complex.im (finiteDiagonal - finiteTwoFace) +
          Complex.im completedTwoFace :=
    Complex.add_im (finiteDiagonal - finiteTwoFace) completedTwoFace
  let hleft :
      Complex.im finiteDiagonal - Complex.im finiteTwoFace =
        0 - Complex.im finiteTwoFace :=
    congrArg
      (fun value : ℝ => value - Complex.im finiteTwoFace)
      hfiniteDiagonal
  let hright :
      0 - Complex.im finiteTwoFace = 0 - 0 :=
    congrArg
      (fun value : ℝ => 0 - value)
      hfiniteTwoFace
  let hfinal :
      (0 : ℝ) - 0 = 0 :=
    sub_self 0
  let hzeroSub :
      Complex.im finiteDiagonal - Complex.im finiteTwoFace = 0 :=
    hleft.trans (hright.trans hfinal)
  let hfirst :
      Complex.im (finiteDiagonal - finiteTwoFace + completedTwoFace) =
        (Complex.im finiteDiagonal - Complex.im finiteTwoFace) +
          Complex.im completedTwoFace :=
    hadd.trans
      (congrArg
        (fun value : ℝ => value + Complex.im completedTwoFace)
        hsub)
  let hsecond :
      (Complex.im finiteDiagonal - Complex.im finiteTwoFace) +
            Complex.im completedTwoFace =
        0 + Complex.im completedTwoFace :=
    congrArg
      (fun value : ℝ => value + Complex.im completedTwoFace)
      hzeroSub
  let hthird :
      0 + Complex.im completedTwoFace = 0 + 0 :=
    congrArg
      (fun value : ℝ => 0 + value)
      hcompletedTwoFace
  let hfourth :
      (0 : ℝ) + 0 = 0 :=
    zero_add 0
  let hzeroTotal :
      Complex.im (finiteDiagonal - finiteTwoFace + completedTwoFace) = 0 :=
    hfirst.trans (hsecond.trans (hthird.trans hfourth))
  Eq.trans
    (congrArg Complex.im hdefinition)
    hzeroTotal

/-- The owner completed positive defect-square form is real-valued. -/
theorem zetaCompletedPrimeDefectKernelPositiveForm_im_eq_zero_coordinateAssembly
    (f : ZetaAdmissibleFunction) :
    Complex.im (zetaCompletedPrimeDefectKernelPositiveForm f) = 0 :=
  let diagonalDebt : ℂ := zetaCompletedPrimeDefectKernelDiagonalDebt f
  let boundaryCoefficient : ℂ :=
    zetaCompletedPrimeTwoFaceGNSBoundaryCoefficient f
  let hform :
      zetaCompletedPrimeDefectKernelPositiveForm f =
        diagonalDebt + boundaryCoefficient :=
    zetaCompletedPrimeDefectKernelPositiveForm_eq_diagonalDebt_add_boundaryCoefficient
      f
  let hdiagonal :
      Complex.im diagonalDebt = 0 :=
    zetaCompletedPrimeDefectKernelDiagonalDebt_im_eq_zero_coordinateAssembly f
  let hboundary :
      Complex.im boundaryCoefficient = 0 :=
    zetaCompletedPrimeTwoFaceGNSBoundaryCoefficient_im_eq_zero f
  let hadd :
      Complex.im (diagonalDebt + boundaryCoefficient) =
        Complex.im diagonalDebt + Complex.im boundaryCoefficient :=
    Complex.add_im diagonalDebt boundaryCoefficient
  let hzeroLeft :
      Complex.im diagonalDebt + Complex.im boundaryCoefficient =
        0 + Complex.im boundaryCoefficient :=
    congrArg
      (fun value : ℝ => value + Complex.im boundaryCoefficient)
      hdiagonal
  let hzeroRight :
      0 + Complex.im boundaryCoefficient = 0 + 0 :=
    congrArg
      (fun value : ℝ => 0 + value)
      hboundary
  let hzeroSum :
      (0 : ℝ) + 0 = 0 :=
    zero_add 0
  let hsum :
      Complex.im (diagonalDebt + boundaryCoefficient) = 0 :=
    hadd.trans (hzeroLeft.trans (hzeroRight.trans hzeroSum))
  Eq.trans
    (congrArg Complex.im hform)
    hsum

/-- Majorant summability gives the completed coordinate presentation
decomposition into positive coordinate plus completed two-face coefficient. -/
theorem zetaCompletedPrimeDefectKernelDiagonalDebtCoordinateTsum_eq_positive_add_twoFace_of_spectralCoordinateMajorant_summable_coordinateAssembly
    (f : ZetaAdmissibleFunction)
    (hmajorant :
      Summable
        (fun index : ZetaPrimePowerIndex =>
          zetaCompletedPrimeSpectralCoordinateMajorant index f)) :
    zetaCompletedPrimeDefectKernelDiagonalDebtCoordinateTsum f =
      zetaCompletedPrimeDefectKernelPositiveCoordinateTsum f +
        zetaCompletedPrimeTwoFaceGNSMatrixCoefficient f :=
  (zetaCompletedPrimeDefectKernelPositiveCoordinateTsum_add_twoFace_eq_diagonalDebtCoordinateTsum
    f
    hmajorant).symm

/-- The completed coordinate presentation decomposes as positive coordinate
plus completed two-face coefficient. -/
theorem zetaCompletedPrimeDefectKernelDiagonalDebtCoordinateTsum_eq_positive_add_twoFace_coordinateAssembly
    (f : ZetaAdmissibleFunction) (Cpos Cneg : ℝ) (kpos kneg : ℕ)
    (hpos : PrimeCenterSpectralPolynomialBound f Cpos kpos)
    (hneg : PrimeCenterSpectralPolynomialBound
      (ZetaAdmissibleFunction.reflect f) Cneg kneg) :
    zetaCompletedPrimeDefectKernelDiagonalDebtCoordinateTsum f =
      zetaCompletedPrimeDefectKernelPositiveCoordinateTsum f +
        zetaCompletedPrimeTwoFaceGNSMatrixCoefficient f :=
  zetaCompletedPrimeDefectKernelDiagonalDebtCoordinateTsum_eq_positive_add_twoFace_of_spectralCoordinateMajorant_summable_coordinateAssembly
    f
    (zetaCompletedPrimeSpectralCoordinateMajorant_summable_diagonalDebt_owner
      f Cpos kpos hpos Cneg kneg hneg)

/-- The owner completed diagonal-debt form decomposes as owner positive form
plus completed two-face coefficient. -/
theorem zetaCompletedPrimeDefectKernelDiagonalDebt_eq_positive_add_twoFace_coordinateAssembly
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
