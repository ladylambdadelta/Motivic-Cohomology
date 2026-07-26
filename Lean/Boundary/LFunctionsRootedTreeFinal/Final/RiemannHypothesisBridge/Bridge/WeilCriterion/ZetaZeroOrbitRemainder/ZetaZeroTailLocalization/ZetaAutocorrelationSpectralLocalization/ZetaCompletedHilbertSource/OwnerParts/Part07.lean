import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaCompletedHilbertSource.OwnerParts.Part06

namespace Boundary
namespace LFunctions

noncomputable section

open Filter
open LSeries ArithmeticFunction
open scoped ArithmeticFunction
open scoped Topology

namespace ZetaAdmissibleFunction

/-- The raw positive/off-diagonal mismatch scalar. -/
noncomputable def completedPrimePositiveOffDiagonalGap
    (f : ZetaAdmissibleFunction) : ℝ :=
  zetaCompletedPrimeDefectKernelPositiveCoordinateTsumRe f -
    completedPrimeOffDiagonalChannel f

/-- The raw positive/off-diagonal mismatch unfolds to the difference of the
raw positive coordinate total and the physical off-diagonal channel. -/
theorem completedPrimePositiveOffDiagonalGap_eq
    (f : ZetaAdmissibleFunction) :
    completedPrimePositiveOffDiagonalGap f =
      zetaCompletedPrimeDefectKernelPositiveCoordinateTsumRe f -
        completedPrimeOffDiagonalChannel f :=
  Eq.refl (completedPrimePositiveOffDiagonalGap f)

/-- With the existing summed contour/time transport, the off-diagonal/positive-coordinate
comparison is exactly the real completed diagonal-debt coordinate presentation. -/
theorem zetaCompletedPrimeDefectKernelDiagonalDebtCoordinateTsum_re_eq_positiveCoordinate_sub_offDiagonal_summedTransport
    (f : ZetaAdmissibleFunction)
    (D : CompletedSummedPrimeContourTimeTransport f)
    (hmajorant :
      Summable
        (fun ι : ZetaPrimePowerIndex =>
          zetaCompletedPrimeSpectralCoordinateMajorant ι f)) :
    Complex.re (zetaCompletedPrimeDefectKernelDiagonalDebtCoordinateTsum f) =
      zetaCompletedPrimeDefectKernelPositiveCoordinateTsumRe f -
        completedPrimeOffDiagonalChannel f :=
  let P : ℝ := zetaCompletedPrimeDefectKernelPositiveCoordinateTsumRe f
  let O : ℝ := completedPrimeOffDiagonalChannel f
  let T : ℝ := Complex.re (zetaCompletedPrimeTwoFaceGNSMatrixCoefficient f)
  let R : ℝ :=
    Complex.re (zetaCompletedPrimeDefectKernelDiagonalDebtCoordinateTsum f)
  let hexpansionComplex :
      zetaCompletedPrimeDefectKernelPositiveCoordinateTsum f +
          zetaCompletedPrimeTwoFaceGNSMatrixCoefficient f =
        zetaCompletedPrimeDefectKernelDiagonalDebtCoordinateTsum f :=
    zetaCompletedPrimeDefectKernelPositiveCoordinateTsum_add_twoFace_eq_diagonalDebtCoordinateTsum
      f hmajorant
  let hexpansionReStart :
      R =
        Complex.re
          (zetaCompletedPrimeDefectKernelPositiveCoordinateTsum f +
            zetaCompletedPrimeTwoFaceGNSMatrixCoefficient f) :=
    congrArg Complex.re hexpansionComplex.symm
  let hexpansionReAdd :
      Complex.re
          (zetaCompletedPrimeDefectKernelPositiveCoordinateTsum f +
            zetaCompletedPrimeTwoFaceGNSMatrixCoefficient f) =
        P + T :=
    Complex.add_re
      (zetaCompletedPrimeDefectKernelPositiveCoordinateTsum f)
      (zetaCompletedPrimeTwoFaceGNSMatrixCoefficient f)
  let htwoFace :
      T = -O :=
    zetaCompletedPrimeTwoFaceGNSMatrixCoefficient_re_eq_neg_completedPrimeOffDiagonalChannel_ownerSummedDistributionTransport
      f D
  let htwoFaceTransport :
      P + T = P + -O :=
    congrArg (fun value : ℝ => P + value) htwoFace
  let hsub :
      P + -O = P - O :=
    (sub_eq_add_neg P O).symm
  let htarget :
      P - O =
        zetaCompletedPrimeDefectKernelPositiveCoordinateTsumRe f -
          completedPrimeOffDiagonalChannel f :=
    Eq.refl (P - O)
  hexpansionReStart.trans
    (hexpansionReAdd.trans
      (htwoFaceTransport.trans
        (hsub.trans htarget)))

theorem completedPrimeOffDiagonalChannel_eq_positiveCoordinateTsumRe_iff_diagonalDebtCoordinateTsum_re_eq_zero_summedTransport
    (f : ZetaAdmissibleFunction)
    (D : CompletedSummedPrimeContourTimeTransport f)
    (hmajorant :
      Summable
        (fun ι : ZetaPrimePowerIndex =>
          zetaCompletedPrimeSpectralCoordinateMajorant ι f)) :
    completedPrimeOffDiagonalChannel f =
        zetaCompletedPrimeDefectKernelPositiveCoordinateTsumRe f ↔
      Complex.re (zetaCompletedPrimeDefectKernelDiagonalDebtCoordinateTsum f) =
        0 :=
  let P : ℝ := zetaCompletedPrimeDefectKernelPositiveCoordinateTsumRe f
  let O : ℝ := completedPrimeOffDiagonalChannel f
  let R : ℝ :=
    Complex.re (zetaCompletedPrimeDefectKernelDiagonalDebtCoordinateTsum f)
  let hR :
      R = P - O :=
    zetaCompletedPrimeDefectKernelDiagonalDebtCoordinateTsum_re_eq_positiveCoordinate_sub_offDiagonal_summedTransport
      f D hmajorant
  let htarget :
      (R = 0) =
        (Complex.re
            (zetaCompletedPrimeDefectKernelDiagonalDebtCoordinateTsum f) =
          0) :=
    Eq.refl (R = 0)
  Iff.intro
    (fun hoffPositive =>
      let hpositiveOff :
          P = O :=
        hoffPositive.symm
      let hsubZero :
          P - O = 0 :=
        sub_eq_zero.mpr hpositiveOff
      Eq.mp htarget (hR.trans hsubZero))
    (fun hdiagonalZero =>
      let hRZero : R = 0 :=
        Eq.mp htarget.symm hdiagonalZero
      let hsubZero : P - O = 0 :=
        hR.symm.trans hRZero
      (sub_eq_zero.mp hsubZero).symm)

/-- The positive/off-diagonal gap is the same scalar as the completed diagonal-debt
coordinate residual under summed contour/time transport. -/
theorem completedPrimePositiveOffDiagonalGap_eq_diagonalDebtCoordinateTsum_re_summedTransport
    (f : ZetaAdmissibleFunction)
    (D : CompletedSummedPrimeContourTimeTransport f)
    (hmajorant :
      Summable
        (fun ι : ZetaPrimePowerIndex =>
          zetaCompletedPrimeSpectralCoordinateMajorant ι f)) :
    completedPrimePositiveOffDiagonalGap f =
      Complex.re (zetaCompletedPrimeDefectKernelDiagonalDebtCoordinateTsum f) :=
  let hgap :
      completedPrimePositiveOffDiagonalGap f =
        zetaCompletedPrimeDefectKernelPositiveCoordinateTsumRe f -
          completedPrimeOffDiagonalChannel f :=
    completedPrimePositiveOffDiagonalGap_eq f
  let hresidual :
      Complex.re (zetaCompletedPrimeDefectKernelDiagonalDebtCoordinateTsum f) =
        zetaCompletedPrimeDefectKernelPositiveCoordinateTsumRe f -
          completedPrimeOffDiagonalChannel f :=
    zetaCompletedPrimeDefectKernelDiagonalDebtCoordinateTsum_re_eq_positiveCoordinate_sub_offDiagonal_summedTransport
      f D hmajorant
  hgap.trans hresidual.symm

end ZetaAdmissibleFunction

end
end LFunctions
end Boundary
