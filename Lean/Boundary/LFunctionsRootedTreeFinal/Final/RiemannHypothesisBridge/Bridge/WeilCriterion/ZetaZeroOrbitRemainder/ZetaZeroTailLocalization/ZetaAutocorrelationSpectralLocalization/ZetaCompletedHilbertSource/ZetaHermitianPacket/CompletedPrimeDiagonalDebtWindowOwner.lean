import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaCompletedHilbertSource.ZetaHermitianPacket.CompletedPrimePowerPackets
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaCompletedHilbertSource.ZetaHermitianPacket.CompletedPrimeDiagonalDebtWindowOwnerParts.SpectralMajorant
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaCompletedHilbertSource.ZetaHermitianPacket.CompletedPrimeDiagonalDebtWindowOwnerParts.DiagonalTransportFinalAssembly
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaCompletedHilbertSource.ZetaHermitianPacket.CompletedPrimeDiagonalDebtWindowOwnerParts.DiagonalDebtWindowFiniteSumBound
import Mathlib.Topology.Algebra.InfiniteSum.Module
import Mathlib.Topology.Algebra.InfiniteSum.Order

/-!
# Completed prime diagonal-debt finite-window ownership

This file owns the finite-window domination statement for the completed prime
diagonal-debt coordinate presentation.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open scoped BigOperators

namespace ZetaAdmissibleFunction

/-- The real part of the raw positive coordinate presentation is its named
real coordinate-presentation scalar. -/
theorem zetaCompletedPrimeDefectKernelPositiveCoordinateTsum_re_eq_coordinateTsumRe_owner
    (f : ZetaAdmissibleFunction) :
    Complex.re (zetaCompletedPrimeDefectKernelPositiveCoordinateTsum f) =
      zetaCompletedPrimeDefectKernelPositiveCoordinateTsumRe f :=
  Eq.refl (Complex.re (zetaCompletedPrimeDefectKernelPositiveCoordinateTsum f))

/-- The real scalar of the owner completed positive defect-square form is its
named positive channel. -/
theorem zetaCompletedPrimeDefectKernelPositiveForm_re_eq_positiveChannel_owner
    (f : ZetaAdmissibleFunction) :
    Complex.re (zetaCompletedPrimeDefectKernelPositiveForm f) =
      completedPrimeDefectKernelPositiveChannel f :=
  Eq.refl (Complex.re (zetaCompletedPrimeDefectKernelPositiveForm f))

/-- The raw completed positive coordinate real presentation equals the owner
completed positive defect-square channel. -/
theorem zetaCompletedPrimeDefectKernelPositiveCoordinateTsumRe_eq_positiveChannel_owner
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
    f
    hmajorant
      hcoordinateZero

/-- One completed positive defect-square coordinate is real-valued. -/
theorem zetaCompletedPrimeDefectKernelPositiveCoordinate_im_eq_zero_owner
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
theorem zetaCompletedPrimeDefectKernelPositiveCoordinateTsum_im_eq_zero_owner
    (f : ZetaAdmissibleFunction) :
    Complex.im (zetaCompletedPrimeDefectKernelPositiveCoordinateTsum f) = 0 :=
  complex_im_tsum_eq_zero_of_forall_im_eq_zero
    (fun index : ZetaPrimePowerIndex =>
      zetaCompletedPrimeDefectKernelPositiveCoordinate index f)
    (fun index : ZetaPrimePowerIndex =>
      zetaCompletedPrimeDefectKernelPositiveCoordinate_im_eq_zero_owner
        index f)

/-- One finite prime diagonal-debt coordinate is real-valued. -/
theorem zetaPrimeDefectKernelDiagonalDebtCoordinate_im_eq_zero_owner
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
  let hsum :
      Complex.im
          (positiveValue * star positiveValue +
            negativeValue * star negativeValue) = 0 :=
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
    let hofReal :
        Complex.im
            ((Complex.normSq positiveValue : ℂ) +
              (Complex.normSq negativeValue : ℂ)) = 0 :=
      let hadd :
          ((Complex.normSq positiveValue : ℂ) +
              (Complex.normSq negativeValue : ℂ)) =
            ((Complex.normSq positiveValue +
              Complex.normSq negativeValue : ℝ) : ℂ) :=
        (Complex.ofReal_add
          (Complex.normSq positiveValue)
          (Complex.normSq negativeValue)).symm
      Eq.trans
        (congrArg Complex.im hadd)
        (Complex.ofReal_im
          (Complex.normSq positiveValue + Complex.normSq negativeValue))
    hrewritePositive.trans (hrewriteNegative.trans hofReal)
  Eq.trans
    (congrArg Complex.im hcoordinate)
    hsum

/-- The finite prime diagonal-debt form is real-valued. -/
theorem zetaPrimeDefectKernelDiagonalDebt_im_eq_zero_owner
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
        zetaPrimeDefectKernelDiagonalDebtCoordinate_im_eq_zero_owner
          label.1 label.2 f)
  hsum.trans hzero

/-- The owner completed diagonal-debt form is real-valued. -/
theorem zetaCompletedPrimeDefectKernelDiagonalDebt_im_eq_zero_owner
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
    zetaPrimeDefectKernelDiagonalDebt_im_eq_zero_owner f
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
  let hzeroSub :
      Complex.im finiteDiagonal - Complex.im finiteTwoFace = 0 :=
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
      sub_self (0 : ℝ)
    hleft.trans (hright.trans hfinal)
  let hzeroTotal :
      Complex.im (finiteDiagonal - finiteTwoFace + completedTwoFace) = 0 :=
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
      zero_add (0 : ℝ)
    hfirst.trans (hsecond.trans (hthird.trans hfourth))
  Eq.trans
    (congrArg Complex.im hdefinition)
    hzeroTotal

/-- The owner completed positive defect-square form is real-valued. -/
theorem zetaCompletedPrimeDefectKernelPositiveForm_im_eq_zero_owner
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
    zetaCompletedPrimeDefectKernelDiagonalDebt_im_eq_zero_owner f
  let hboundary :
      Complex.im boundaryCoefficient = 0 :=
    zetaCompletedPrimeTwoFaceGNSBoundaryCoefficient_im_eq_zero f
  let hsum :
      Complex.im (diagonalDebt + boundaryCoefficient) = 0 :=
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
      zero_add (0 : ℝ)
    hadd.trans (hzeroLeft.trans (hzeroRight.trans hzeroSum))
  Eq.trans
    (congrArg Complex.im hform)
    hsum

/-- The raw completed positive defect-square coordinate presentation has the
same imaginary part as the owner completed positive defect-square form. -/
theorem zetaCompletedPrimeDefectKernelPositiveCoordinateTsum_im_eq_owner_im
    (f : ZetaAdmissibleFunction) :
    Complex.im (zetaCompletedPrimeDefectKernelPositiveCoordinateTsum f) =
      Complex.im (zetaCompletedPrimeDefectKernelPositiveForm f) :=
  (zetaCompletedPrimeDefectKernelPositiveCoordinateTsum_im_eq_zero_owner
    f).trans
    (zetaCompletedPrimeDefectKernelPositiveForm_im_eq_zero_owner f).symm

/-- The completed diagonal-debt coordinate stream is the pointwise sum of the
positive defect-square stream and the symmetrized two-face stream. -/
theorem zetaCompletedPrimeDefectKernelDiagonalDebtCoordinate_eq_positive_add_twoFace
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

/-- The owner completed diagonal-debt scalar is the sum of the owner positive
defect-square form and the owner symmetrized two-face matrix coefficient. -/
theorem zetaCompletedPrimeDefectKernelDiagonalDebt_eq_positive_add_twoFace_owner
    (f : ZetaAdmissibleFunction) :
    zetaCompletedPrimeDefectKernelDiagonalDebt f =
      zetaCompletedPrimeDefectKernelPositiveForm f +
        zetaCompletedPrimeTwoFaceGNSMatrixCoefficient f :=
  (zetaCompletedPrimeDefectKernelPositiveWindow_expansion_passes_to_completedForms
    f).symm

/-- The completed prime diagonal-debt coordinate stream has owner sum. -/
theorem zetaCompletedPrimeDefectKernelDiagonalDebtCoordinate_hasSum_owner
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
  zetaCompletedPrimeDefectKernelDiagonalDebtCoordinate_hasSum_of_diagonalDebtCoordinate_re_hasSum_finalAssembly
    f C Creflect hhasSum hhasSumReflect hcoordinateZero

/-- Explicit diagonal-debt real-coordinate `HasSum` inputs give the completed
prime diagonal-debt coordinate stream with owner sum. -/
theorem zetaCompletedPrimeDefectKernelDiagonalDebtCoordinate_hasSum_owner_of_diagonalDebtCoordinate_re_hasSum
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
  zetaCompletedPrimeDefectKernelDiagonalDebtCoordinate_hasSum_of_diagonalDebtCoordinate_re_hasSum_finalAssembly
    f C Creflect hhasSum hhasSumReflect hcoordinateZero

/-- The real completed prime diagonal-debt coordinate stream has owner scalar
sum. -/
theorem zetaCompletedPrimeDefectKernelDiagonalDebtCoordinate_re_hasSum_ownerScalar
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
        Complex.re
          (zetaCompletedPrimeDefectKernelDiagonalDebtCoordinate index f))
      (Complex.re (zetaCompletedPrimeDefectKernelDiagonalDebt f)) :=
  (RCLike.reCLM : ℂ →L[ℝ] ℝ).hasSum
    (zetaCompletedPrimeDefectKernelDiagonalDebtCoordinate_hasSum_owner
      f C Creflect hhasSum hhasSumReflect hcoordinateZero)

/-- Explicit diagonal-debt real-coordinate `HasSum` inputs give the real
completed prime diagonal-debt coordinate stream with owner scalar sum. -/
theorem zetaCompletedPrimeDefectKernelDiagonalDebtCoordinate_re_hasSum_ownerScalar_of_diagonalDebtCoordinate_re_hasSum
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
        Complex.re
          (zetaCompletedPrimeDefectKernelDiagonalDebtCoordinate index f))
      (Complex.re (zetaCompletedPrimeDefectKernelDiagonalDebt f)) :=
  (RCLike.reCLM : ℂ →L[ℝ] ℝ).hasSum
    (zetaCompletedPrimeDefectKernelDiagonalDebtCoordinate_hasSum_owner_of_diagonalDebtCoordinate_re_hasSum
      f C Creflect hhasSum hhasSumReflect hcoordinateZero)

/-- A finite completed prime diagonal-debt real window is the finite sum of
real diagonal-debt coordinates over that window. -/
theorem zetaCompletedPrimeDefectKernelDiagonalDebtRealWindow_eq_sum_re
    (N : ℕ) (f : ZetaAdmissibleFunction) :
    zetaCompletedPrimeDefectKernelDiagonalDebtRealWindow N f =
      ∑ index in ZetaPrimePowerIndex.window N,
        Complex.re
          (zetaCompletedPrimeDefectKernelDiagonalDebtCoordinate index f) :=
  Complex.re_sum
    (ZetaPrimePowerIndex.window N)
    (fun index : ZetaPrimePowerIndex =>
      zetaCompletedPrimeDefectKernelDiagonalDebtCoordinate index f)

/-- The finite completed prime diagonal-debt real window is dominated by the
owner completed prime diagonal-debt scalar. -/
theorem zetaCompletedPrimeDefectKernelDiagonalDebtRealWindow_le_ownerScalar
    (N : ℕ) (f : ZetaAdmissibleFunction) (C Creflect : ℝ)
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
    zetaCompletedPrimeDefectKernelDiagonalDebtRealWindow N f ≤
      Complex.re (zetaCompletedPrimeDefectKernelDiagonalDebt f) :=
  let hhasSum :
      HasSum
        (fun index : ZetaPrimePowerIndex =>
          Complex.re
            (zetaCompletedPrimeDefectKernelDiagonalDebtCoordinate index f))
        (Complex.re (zetaCompletedPrimeDefectKernelDiagonalDebt f)) :=
    zetaCompletedPrimeDefectKernelDiagonalDebtCoordinate_re_hasSum_ownerScalar
      f C Creflect hhasSum hhasSumReflect hcoordinateZero
  let hnonnegative :
      ∀ index : ZetaPrimePowerIndex,
        0 ≤
          Complex.re
            (zetaCompletedPrimeDefectKernelDiagonalDebtCoordinate index f) :=
    fun index : ZetaPrimePowerIndex =>
      zetaCompletedPrimeDefectKernelDiagonalDebtCoordinate_re_nonnegative
        index f
  let hsum :
      (∑ index in ZetaPrimePowerIndex.window N,
        Complex.re
          (zetaCompletedPrimeDefectKernelDiagonalDebtCoordinate index f)) ≤
        Complex.re (zetaCompletedPrimeDefectKernelDiagonalDebt f) :=
    finite_window_sum_le_hasSum_of_nonnegative
      (ZetaPrimePowerIndex.window N)
      (fun index : ZetaPrimePowerIndex =>
        Complex.re
          (zetaCompletedPrimeDefectKernelDiagonalDebtCoordinate index f))
      hnonnegative
      hhasSum
  Eq.subst
    (motive := fun value : ℝ =>
      value ≤ Complex.re (zetaCompletedPrimeDefectKernelDiagonalDebt f))
    (zetaCompletedPrimeDefectKernelDiagonalDebtRealWindow_eq_sum_re N f).symm
    hsum

/-- Explicit diagonal-debt real-coordinate `HasSum` inputs make a finite
completed prime diagonal-debt real window dominated by the owner scalar. -/
theorem zetaCompletedPrimeDefectKernelDiagonalDebtRealWindow_le_ownerScalar_of_diagonalDebtCoordinate_re_hasSum
    (N : ℕ) (f : ZetaAdmissibleFunction) (C Creflect : ℝ)
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
    zetaCompletedPrimeDefectKernelDiagonalDebtRealWindow N f ≤
      Complex.re (zetaCompletedPrimeDefectKernelDiagonalDebt f) :=
  let hhasSumOwner :
      HasSum
        (fun index : ZetaPrimePowerIndex =>
          Complex.re
            (zetaCompletedPrimeDefectKernelDiagonalDebtCoordinate index f))
        (Complex.re (zetaCompletedPrimeDefectKernelDiagonalDebt f)) :=
    zetaCompletedPrimeDefectKernelDiagonalDebtCoordinate_re_hasSum_ownerScalar_of_diagonalDebtCoordinate_re_hasSum
      f C Creflect hhasSum hhasSumReflect hcoordinateZero
  let hnonnegative :
      ∀ index : ZetaPrimePowerIndex,
        0 ≤
          Complex.re
            (zetaCompletedPrimeDefectKernelDiagonalDebtCoordinate index f) :=
    fun index : ZetaPrimePowerIndex =>
      zetaCompletedPrimeDefectKernelDiagonalDebtCoordinate_re_nonnegative
        index f
  let hsum :
      (∑ index in ZetaPrimePowerIndex.window N,
        Complex.re
          (zetaCompletedPrimeDefectKernelDiagonalDebtCoordinate index f)) ≤
        Complex.re (zetaCompletedPrimeDefectKernelDiagonalDebt f) :=
    finite_window_sum_le_hasSum_of_nonnegative
      (ZetaPrimePowerIndex.window N)
      (fun index : ZetaPrimePowerIndex =>
        Complex.re
          (zetaCompletedPrimeDefectKernelDiagonalDebtCoordinate index f))
      hnonnegative
      hhasSumOwner
  Eq.subst
    (motive := fun value : ℝ =>
      value ≤ Complex.re (zetaCompletedPrimeDefectKernelDiagonalDebt f))
    (zetaCompletedPrimeDefectKernelDiagonalDebtRealWindow_eq_sum_re N f).symm
    hsum

/-- The finite completed prime diagonal-debt real-window complement inside the
owner completed prime diagonal-debt scalar is nonnegative. -/
theorem zetaCompletedPrimeDefectKernelDiagonalDebtRealWindow_ownerComplement_nonnegative
    (N : ℕ) (f : ZetaAdmissibleFunction) (C Creflect : ℝ)
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
    0 ≤
      Complex.re (zetaCompletedPrimeDefectKernelDiagonalDebt f) -
        zetaCompletedPrimeDefectKernelDiagonalDebtRealWindow N f :=
  sub_nonneg.mpr
    (zetaCompletedPrimeDefectKernelDiagonalDebtRealWindow_le_ownerScalar
      N f C Creflect hhasSum hhasSumReflect hcoordinateZero)

/-- Explicit diagonal-debt real-coordinate `HasSum` inputs make the finite
completed prime diagonal-debt real-window complement nonnegative. -/
theorem zetaCompletedPrimeDefectKernelDiagonalDebtRealWindow_ownerComplement_nonnegative_of_diagonalDebtCoordinate_re_hasSum
    (N : ℕ) (f : ZetaAdmissibleFunction) (C Creflect : ℝ)
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
    0 ≤
      Complex.re (zetaCompletedPrimeDefectKernelDiagonalDebt f) -
        zetaCompletedPrimeDefectKernelDiagonalDebtRealWindow N f :=
  sub_nonneg.mpr
    (zetaCompletedPrimeDefectKernelDiagonalDebtRealWindow_le_ownerScalar_of_diagonalDebtCoordinate_re_hasSum
      N f C Creflect hhasSum hhasSumReflect hcoordinateZero)

end ZetaAdmissibleFunction

end
end LFunctions
end Boundary
