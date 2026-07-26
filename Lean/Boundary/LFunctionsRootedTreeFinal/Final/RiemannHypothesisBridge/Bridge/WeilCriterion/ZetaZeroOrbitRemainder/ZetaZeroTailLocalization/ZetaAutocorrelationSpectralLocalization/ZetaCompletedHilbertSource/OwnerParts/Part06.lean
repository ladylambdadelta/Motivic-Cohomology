import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaCompletedHilbertSource.OwnerParts.Part05

namespace Boundary
namespace LFunctions

noncomputable section

open Filter
open LSeries ArithmeticFunction
open scoped ArithmeticFunction
open scoped Topology
local notation "π" => Real.pi

namespace ZetaAdmissibleFunction

theorem completedPrimeOffDiagonalChannel_eq_positiveCoordinateTsumRe_iff_diagonalDebtCoordinateTsum_re_eq_zero_of_summedTransport
    (f : ZetaAdmissibleFunction)
    (D : CompletedSummedPrimeContourTimeTransport f)
    (hmajorant :
      Summable
        (fun ι : ZetaPrimePowerIndex =>
          zetaCompletedPrimeSpectralCoordinateMajorant ι f)) :
    completedPrimeOffDiagonalChannel f =
        zetaCompletedPrimeDefectKernelPositiveCoordinateTsumRe f ↔
      Complex.re (zetaCompletedPrimeDefectKernelDiagonalDebtCoordinateTsum f) = 0 := by
  constructor
  · intro hoffCoordinate
    let O : ℝ := completedPrimeOffDiagonalChannel f
    let P : ℝ := zetaCompletedPrimeDefectKernelPositiveCoordinateTsumRe f
    let T : ℝ := Complex.re (zetaCompletedPrimeTwoFaceGNSMatrixCoefficient f)
    let Dcoord : ℝ :=
      Complex.re (zetaCompletedPrimeDefectKernelDiagonalDebtCoordinateTsum f)
    have htwoFace : T = -O := by
      unfold T
      unfold O
      exact
        zetaCompletedPrimeTwoFaceGNSMatrixCoefficient_re_eq_neg_completedPrimeOffDiagonalChannel_ownerSummedDistributionTransport
          f D
    have hexpansion : P + T = Dcoord := by
      unfold P
      unfold T
      unfold Dcoord
      calc
        zetaCompletedPrimeDefectKernelPositiveCoordinateTsumRe f +
            Complex.re (zetaCompletedPrimeTwoFaceGNSMatrixCoefficient f) =
            Complex.re
              (zetaCompletedPrimeDefectKernelPositiveCoordinateTsum f) +
              Complex.re (zetaCompletedPrimeTwoFaceGNSMatrixCoefficient f) := by
          rfl
        _ =
            Complex.re
              (zetaCompletedPrimeDefectKernelPositiveCoordinateTsum f +
                zetaCompletedPrimeTwoFaceGNSMatrixCoefficient f) := by
          exact (Complex.add_re
            (zetaCompletedPrimeDefectKernelPositiveCoordinateTsum f)
            (zetaCompletedPrimeTwoFaceGNSMatrixCoefficient f)).symm
        _ =
            Complex.re
              (zetaCompletedPrimeDefectKernelDiagonalDebtCoordinateTsum f) := by
          exact congrArg Complex.re
            (zetaCompletedPrimeDefectKernelPositiveCoordinateTsum_add_twoFace_eq_diagonalDebtCoordinateTsum
              f hmajorant)
    have hP : P = O := hoffCoordinate.symm
    calc
      Complex.re (zetaCompletedPrimeDefectKernelDiagonalDebtCoordinateTsum f) =
          Dcoord := by
        rfl
      _ = P + T := by
        exact hexpansion.symm
      _ = O + T := by
        exact congrArg (fun x : ℝ => x + T) hP
      _ = O + -O := by
        exact congrArg (fun x : ℝ => O + x) htwoFace
      _ = 0 := by
        exact add_neg_cancel O
  · intro hdiagonalZero
    let O : ℝ := completedPrimeOffDiagonalChannel f
    let P : ℝ := zetaCompletedPrimeDefectKernelPositiveCoordinateTsumRe f
    let T : ℝ := Complex.re (zetaCompletedPrimeTwoFaceGNSMatrixCoefficient f)
    let Dcoord : ℝ :=
      Complex.re (zetaCompletedPrimeDefectKernelDiagonalDebtCoordinateTsum f)
    have htwoFace : T = -O := by
      unfold T
      unfold O
      exact
        zetaCompletedPrimeTwoFaceGNSMatrixCoefficient_re_eq_neg_completedPrimeOffDiagonalChannel_ownerSummedDistributionTransport
          f D
    have hexpansion : P + T = Dcoord := by
      unfold P
      unfold T
      unfold Dcoord
      calc
        zetaCompletedPrimeDefectKernelPositiveCoordinateTsumRe f +
            Complex.re (zetaCompletedPrimeTwoFaceGNSMatrixCoefficient f) =
            Complex.re
              (zetaCompletedPrimeDefectKernelPositiveCoordinateTsum f) +
              Complex.re (zetaCompletedPrimeTwoFaceGNSMatrixCoefficient f) := by
          rfl
        _ =
            Complex.re
              (zetaCompletedPrimeDefectKernelPositiveCoordinateTsum f +
                zetaCompletedPrimeTwoFaceGNSMatrixCoefficient f) := by
          exact (Complex.add_re
            (zetaCompletedPrimeDefectKernelPositiveCoordinateTsum f)
            (zetaCompletedPrimeTwoFaceGNSMatrixCoefficient f)).symm
        _ =
            Complex.re
              (zetaCompletedPrimeDefectKernelDiagonalDebtCoordinateTsum f) := by
          exact congrArg Complex.re
            (zetaCompletedPrimeDefectKernelPositiveCoordinateTsum_add_twoFace_eq_diagonalDebtCoordinateTsum
              f hmajorant)
    have hsum : P + -O = 0 := by
      calc
        P + -O = P + T := by
          exact congrArg (fun x : ℝ => P + x) htwoFace.symm
        _ = Dcoord := by
          exact hexpansion
        _ = Complex.re (zetaCompletedPrimeDefectKernelDiagonalDebtCoordinateTsum f) := by
          rfl
        _ = 0 := by
          exact hdiagonalZero
    have hcancel :
        (P + -O) + O = 0 + O := by
      exact congrArg (fun x : ℝ => x + O) hsum
    have hleft : (P + -O) + O = P := by
      calc
        (P + -O) + O = P + (-O + O) := by
          exact add_assoc P (-O) O
        _ = P + 0 := by
          exact congrArg (fun x : ℝ => P + x) (neg_add_cancel O)
        _ = P := by
          exact add_zero P
    have hright : 0 + O = O := by
      exact zero_add O
    calc
      completedPrimeOffDiagonalChannel f = O := by
        rfl
      _ = 0 + O := by
        exact hright.symm
      _ = (P + -O) + O := by
        exact hcancel.symm
      _ = P := by
        exact hleft
      _ = zetaCompletedPrimeDefectKernelPositiveCoordinateTsumRe f := by
        rfl

/-- The completed off-diagonal channel equals the raw positive coordinate real channel once
the completed diagonal-debt coordinate presentation has zero real scalar. -/
theorem completedPrimeOffDiagonalChannel_eq_positiveCoordinateTsumRe_of_diagonalDebtCoordinateTsum_re_eq_zero
    (f : ZetaAdmissibleFunction)
    (D : CompletedSummedPrimeContourTimeTransport f)
    (hmajorant :
      Summable
        (fun ι : ZetaPrimePowerIndex =>
          zetaCompletedPrimeSpectralCoordinateMajorant ι f))
    (hdiagonalZero :
      Complex.re (zetaCompletedPrimeDefectKernelDiagonalDebtCoordinateTsum f) = 0) :
    completedPrimeOffDiagonalChannel f =
      zetaCompletedPrimeDefectKernelPositiveCoordinateTsumRe f := by
  exact
    (completedPrimeOffDiagonalChannel_eq_positiveCoordinateTsumRe_iff_diagonalDebtCoordinateTsum_re_eq_zero_of_summedTransport
      f D hmajorant).mpr
      hdiagonalZero

/-- The completed off-diagonal/positive-coordinate comparison forces the completed
diagonal-debt coordinate presentation to have zero real scalar. -/
theorem diagonalDebtCoordinateTsum_re_eq_zero_of_completedPrimeOffDiagonalChannel_eq_positiveCoordinateTsumRe
    (f : ZetaAdmissibleFunction)
    (D : CompletedSummedPrimeContourTimeTransport f)
    (hmajorant :
      Summable
        (fun ι : ZetaPrimePowerIndex =>
          zetaCompletedPrimeSpectralCoordinateMajorant ι f))
    (hoffCoordinate :
      completedPrimeOffDiagonalChannel f =
        zetaCompletedPrimeDefectKernelPositiveCoordinateTsumRe f) :
    Complex.re (zetaCompletedPrimeDefectKernelDiagonalDebtCoordinateTsum f) = 0 := by
  exact
    (completedPrimeOffDiagonalChannel_eq_positiveCoordinateTsumRe_iff_diagonalDebtCoordinateTsum_re_eq_zero_of_summedTransport
      f D hmajorant).mp
      hoffCoordinate

/-- The completed diagonal-debt owner scalar vanishes when the completed/raw two-face real
coefficients agree. -/
theorem zetaCompletedPrimeDefectKernelDiagonalDebt_re_eq_zero_of_matrixCoefficient_re_eq
    (f : ZetaAdmissibleFunction)
    (hmatrix :
      Complex.re (zetaCompletedPrimeTwoFaceGNSMatrixCoefficient f) =
        Complex.re (zetaPrimeTwoFaceGNSMatrixCoefficient f)) :
    Complex.re (zetaCompletedPrimeDefectKernelDiagonalDebt f) = 0 := by
  exact
    zetaCompletedPrimeDefectKernelDiagonalDebt_re_eq_zero_of_twoFace_re_eq
      f hmatrix

/-- Vanishing of the raw diagonal-debt coordinate presentation identifies the raw positive
coordinate presentation with the owner positive channel, once the completed/raw two-face real
coefficients agree. -/
theorem zetaCompletedPrimeDefectKernelPositiveCoordinateTsumRe_eq_completedPrimeDefectKernelPositiveChannel_of_diagonalDebtCoordinateTsum_re_eq_zero_and_matrixCoefficient_re_eq
    (f : ZetaAdmissibleFunction)
    (hmajorant :
      Summable
        (fun ι : ZetaPrimePowerIndex =>
          zetaCompletedPrimeSpectralCoordinateMajorant ι f))
    (hdiagonalCoordinateZero :
      Complex.re (zetaCompletedPrimeDefectKernelDiagonalDebtCoordinateTsum f) = 0)
    (hmatrix :
      Complex.re (zetaCompletedPrimeTwoFaceGNSMatrixCoefficient f) =
        Complex.re (zetaPrimeTwoFaceGNSMatrixCoefficient f)) :
    zetaCompletedPrimeDefectKernelPositiveCoordinateTsumRe f =
      completedPrimeDefectKernelPositiveChannel f := by
  have hownerZero :
      Complex.re (zetaCompletedPrimeDefectKernelDiagonalDebt f) = 0 :=
    zetaCompletedPrimeDefectKernelDiagonalDebt_re_eq_zero_of_matrixCoefficient_re_eq
      f hmatrix
  have hdiagonal :
      Complex.re (zetaCompletedPrimeDefectKernelDiagonalDebtCoordinateTsum f) =
        Complex.re (zetaCompletedPrimeDefectKernelDiagonalDebt f) :=
    hdiagonalCoordinateZero.trans hownerZero.symm
  exact
    zetaCompletedPrimeDefectKernelPositiveCoordinateTsumRe_eq_completedPrimeDefectKernelPositiveChannel_of_diagonalDebtCoordinateTsum_re
      f hmajorant hdiagonal

/-- The diagonal-coordinate vanishing condition plus completed/raw two-face real comparison
gives the completed off-diagonal/positive-channel comparison. -/
theorem completedPrimeOffDiagonalChannel_eq_completedPrimeDefectKernelPositiveChannel_of_diagonalDebtCoordinateTsum_re_eq_zero_and_matrixCoefficient_re_eq
    (f : ZetaAdmissibleFunction)
    (D : CompletedSummedPrimeContourTimeTransport f)
    (hmajorant :
      Summable
        (fun ι : ZetaPrimePowerIndex =>
          zetaCompletedPrimeSpectralCoordinateMajorant ι f))
    (hdiagonalCoordinateZero :
      Complex.re (zetaCompletedPrimeDefectKernelDiagonalDebtCoordinateTsum f) = 0)
    (hmatrix :
      Complex.re (zetaCompletedPrimeTwoFaceGNSMatrixCoefficient f) =
        Complex.re (zetaPrimeTwoFaceGNSMatrixCoefficient f)) :
    completedPrimeOffDiagonalChannel f =
      completedPrimeDefectKernelPositiveChannel f := by
  have hoffCoordinate :
      completedPrimeOffDiagonalChannel f =
        zetaCompletedPrimeDefectKernelPositiveCoordinateTsumRe f :=
    completedPrimeOffDiagonalChannel_eq_positiveCoordinateTsumRe_of_diagonalDebtCoordinateTsum_re_eq_zero
      f D hmajorant hdiagonalCoordinateZero
  have hpositiveCoordinate :
      zetaCompletedPrimeDefectKernelPositiveCoordinateTsumRe f =
        completedPrimeDefectKernelPositiveChannel f :=
    zetaCompletedPrimeDefectKernelPositiveCoordinateTsumRe_eq_completedPrimeDefectKernelPositiveChannel_of_diagonalDebtCoordinateTsum_re_eq_zero_and_matrixCoefficient_re_eq
      f hmajorant hdiagonalCoordinateZero hmatrix
  exact hoffCoordinate.trans hpositiveCoordinate

/-- The diagonal-coordinate vanishing condition plus completed/raw two-face real comparison
gives the completed off-diagonal reconstruction bridge. -/
theorem completedPrimeOffDiagonalChannel_eq_neg_primeConvolutionContribution_re_of_diagonalDebtCoordinateTsum_re_eq_zero_and_matrixCoefficient_re_eq
    (f : ZetaAdmissibleFunction)
    (D : CompletedSummedPrimeContourTimeTransport f)
    (hmajorant :
      Summable
        (fun ι : ZetaPrimePowerIndex =>
          zetaCompletedPrimeSpectralCoordinateMajorant ι f))
    (hdiagonalCoordinateZero :
      Complex.re (zetaCompletedPrimeDefectKernelDiagonalDebtCoordinateTsum f) = 0)
    (hmatrix :
      Complex.re (zetaCompletedPrimeTwoFaceGNSMatrixCoefficient f) =
        Complex.re (zetaPrimeTwoFaceGNSMatrixCoefficient f)) :
    completedPrimeOffDiagonalChannel f =
      -Complex.re (zetaCompletedExplicitFormulaPrimeConvolutionContribution f) := by
  have hpositive :
      completedPrimeOffDiagonalChannel f =
        completedPrimeDefectKernelPositiveChannel f :=
    completedPrimeOffDiagonalChannel_eq_completedPrimeDefectKernelPositiveChannel_of_diagonalDebtCoordinateTsum_re_eq_zero_and_matrixCoefficient_re_eq
      f D hmajorant hdiagonalCoordinateZero hmatrix
  exact
    completedPrimeOffDiagonalChannel_eq_neg_primeConvolutionContribution_re_of_positiveChannel
      f hpositive

/-- The diagonal-debt coordinate transport facts imply the completed off-diagonal
reconstruction bridge. -/
theorem completedPrimeOffDiagonalChannel_eq_neg_primeConvolutionContribution_re_of_diagonalDebtCoordinateTsum
    (f : ZetaAdmissibleFunction)
    (D : CompletedSummedPrimeContourTimeTransport f)
    (hmajorant :
      Summable
        (fun ι : ZetaPrimePowerIndex =>
          zetaCompletedPrimeSpectralCoordinateMajorant ι f))
    (hdiagonalZero :
      Complex.re (zetaCompletedPrimeDefectKernelDiagonalDebtCoordinateTsum f) = 0)
    (hdiagonalOwner :
      Complex.re (zetaCompletedPrimeDefectKernelDiagonalDebtCoordinateTsum f) =
        Complex.re (zetaCompletedPrimeDefectKernelDiagonalDebt f)) :
    completedPrimeOffDiagonalChannel f =
      -Complex.re (zetaCompletedExplicitFormulaPrimeConvolutionContribution f) := by
  have hoffCoordinate :
      completedPrimeOffDiagonalChannel f =
        zetaCompletedPrimeDefectKernelPositiveCoordinateTsumRe f :=
    (completedPrimeOffDiagonalChannel_eq_positiveCoordinateTsumRe_iff_diagonalDebtCoordinateTsum_re_eq_zero_of_summedTransport
      f D hmajorant).mpr
      hdiagonalZero
  have hpositiveCoordinate :
      zetaCompletedPrimeDefectKernelPositiveCoordinateTsumRe f =
        completedPrimeDefectKernelPositiveChannel f :=
    zetaCompletedPrimeDefectKernelPositiveCoordinateTsumRe_eq_completedPrimeDefectKernelPositiveChannel_of_diagonalDebtCoordinateTsum_re
      f hmajorant hdiagonalOwner
  exact
    completedPrimeOffDiagonalChannel_eq_neg_primeConvolutionContribution_re_of_coordinateTsumRe_comparisons
      f hoffCoordinate hpositiveCoordinate

/-- The requested completed off-diagonal reconstruction bridge is equivalent to the absorbed
finite prime defect-square windows converging to the completed Hermitian positive prime
channel. -/
theorem completedPrimeOffDiagonalChannel_eq_neg_primeConvolutionContribution_re_iff_absorbedPrimeDefectSquare_tendsto
    (f : ZetaAdmissibleFunction) :
    completedPrimeOffDiagonalChannel f =
        -Complex.re (zetaCompletedExplicitFormulaPrimeConvolutionContribution f) ↔
      Tendsto
        (fun N : ℕ =>
          zetaPrimeTranslationDefectEnergy N f +
            finitePartDebtAbsorptionWindow N f)
        atTop
        (𝓝 (completedPrimeDefectKernelPositiveChannel f)) := by
  exact
    (completedPrimeOffDiagonalChannel_eq_neg_primeConvolutionContribution_re_iff_positiveChannel
      f).trans
      (completedPrimeOffDiagonalChannel_eq_positiveChannel_iff_absorbedPrimeDefectSquare_tendsto
        f)

/-- The finite prime diagonal debt is the positive prime-defect channel plus the signed
two-face channel. -/
theorem zetaPrimeDefectKernelDiagonalDebt_re_eq_positiveChannel_add_twoFace
    (f : ZetaAdmissibleFunction) :
    Complex.re (zetaPrimeDefectKernelDiagonalDebt f) =
      completedPrimeDefectKernelPositiveChannel f +
        Complex.re (zetaPrimeTwoFaceGNSMatrixCoefficient f) := by
  let P : ℂ := zetaPrimeDefectKernelPositiveForm f
  let T : ℂ := zetaPrimeTwoFaceGNSMatrixCoefficient f
  let D : ℂ := zetaPrimeDefectKernelDiagonalDebt f
  have hpositive :
      completedPrimeDefectKernelPositiveChannel f = Complex.re P :=
    completedPrimeDefectKernelPositiveChannel_eq_finitePositiveForm_re f
  have hexpansion :
      P + T = D :=
    zetaPrimeDefectKernelPositiveForm_add_twoFace_eq_diagonalDebt f
  calc
    Complex.re D = Complex.re (P + T) := by
      exact congrArg Complex.re hexpansion.symm
    _ = Complex.re P + Complex.re T := by
      exact Complex.add_re P T
    _ =
        completedPrimeDefectKernelPositiveChannel f +
          Complex.re (zetaPrimeTwoFaceGNSMatrixCoefficient f) := by
      exact congrArg
        (fun x : ℝ => x + Complex.re (zetaPrimeTwoFaceGNSMatrixCoefficient f))
        hpositive.symm

/-- The prime boundary channel of an autocorrelation is the positive prime-defect kernel
channel once the time-distribution reconstruction and whole-channel two-face normalization
are supplied. -/
theorem primeBoundaryChannel_convolutionAutocorrelation_re_eq_positiveChannel_of_matrixComparison
    (f : ZetaAdmissibleFunction)
    (D : CompletedFiniteWindowPrimeDistributionReconstruction f)
    (hmatrix :
      Complex.re (zetaCompletedPrimeTwoFaceGNSMatrixCoefficient f) =
        Complex.re (zetaPrimeTwoFaceGNSMatrixCoefficient f)) :
    Complex.re (primeBoundaryChannel (convolutionAutocorrelation f)) =
      completedPrimeDefectKernelPositiveChannel f := by
  have hsigned :
      Complex.re (primeBoundaryChannel (convolutionAutocorrelation f)) =
        -Complex.re (zetaCompletedExplicitFormulaPrimeConvolutionContribution f) :=
    primeBoundaryChannel_convolutionAutocorrelation_re_eq_neg_primeConvolutionContribution
      f D hmatrix
  have hnormalization :
      Complex.re (zetaCompletedExplicitFormulaPrimeConvolutionContribution f) =
        -completedPrimeDefectKernelPositiveChannel f :=
    zetaCompletedExplicitFormulaPrimeConvolutionContribution_re_eq_neg_positiveChannel_of_lowerWeightNormalization
      f
  calc
    Complex.re (primeBoundaryChannel (convolutionAutocorrelation f)) =
        -Complex.re (zetaCompletedExplicitFormulaPrimeConvolutionContribution f) := by
      exact hsigned
    _ = -(-completedPrimeDefectKernelPositiveChannel f) := by
      exact congrArg Neg.neg hnormalization
    _ = completedPrimeDefectKernelPositiveChannel f := by
      exact neg_neg (completedPrimeDefectKernelPositiveChannel f)

/-- The prime boundary channel of an autocorrelation is the positive prime-defect kernel
channel using the explicit summed contour/time transport provider. -/
theorem primeBoundaryChannel_convolutionAutocorrelation_re_eq_positiveChannel_of_summedTransport
    (f : ZetaAdmissibleFunction)
    (D : CompletedSummedPrimeContourTimeTransport f)
    (hmatrix :
      Complex.re (zetaCompletedPrimeTwoFaceGNSMatrixCoefficient f) =
        Complex.re (zetaPrimeTwoFaceGNSMatrixCoefficient f)) :
    Complex.re (primeBoundaryChannel (convolutionAutocorrelation f)) =
      completedPrimeDefectKernelPositiveChannel f := by
  have hsigned :
      Complex.re (primeBoundaryChannel (convolutionAutocorrelation f)) =
        -Complex.re (zetaCompletedExplicitFormulaPrimeConvolutionContribution f) :=
    primeBoundaryChannel_convolutionAutocorrelation_re_eq_neg_primeConvolutionContribution_of_summedTransport
      f D hmatrix
  have hnormalization :
      Complex.re (zetaCompletedExplicitFormulaPrimeConvolutionContribution f) =
        -completedPrimeDefectKernelPositiveChannel f :=
    zetaCompletedExplicitFormulaPrimeConvolutionContribution_re_eq_neg_positiveChannel_of_lowerWeightNormalization
      f
  calc
    Complex.re (primeBoundaryChannel (convolutionAutocorrelation f)) =
        -Complex.re (zetaCompletedExplicitFormulaPrimeConvolutionContribution f) := by
      exact hsigned
    _ = -(-completedPrimeDefectKernelPositiveChannel f) := by
      exact congrArg Neg.neg hnormalization
    _ = completedPrimeDefectKernelPositiveChannel f := by
      exact neg_neg (completedPrimeDefectKernelPositiveChannel f)

/-- The canonical completed Hilbert-source correction coordinate is normalized by the
centered-pole Hermitian correction packet. -/
theorem completedBoundaryHilbertSourcePacket_source_correction_sq_eq_hermitianCorrectionPacketGram
    (f : ZetaAdmissibleFunction) :
    (completedBoundaryHilbertSource f).correctionCoordinate *
        (completedBoundaryHilbertSource f).correctionCoordinate =
      ZetaHermitianPacketEnsemble.correctionPacketGram
        (zetaCompletedHermitianBoundaryDefect f) := by
  exact completedBoundaryHilbertSource_correctionCoordinate_sq f

/-- The ordered-heart GNS scalar of a canonical source is the completed Hermitian
positive-presentation scalar. -/
theorem completedBoundaryHermitianGNSScalar_source_eq_positivePresentationScalar_compat
    (f : ZetaAdmissibleFunction) :
    completedBoundaryHermitianGNSScalar (completedBoundaryHilbertSource f) =
      zetaCompletedGNSPositiveBoundaryPresentationScalar f := by
  exact completedBoundaryHermitianGNSScalar_source_eq_positivePresentationScalar f

end ZetaAdmissibleFunction

end
end LFunctions
end Boundary
