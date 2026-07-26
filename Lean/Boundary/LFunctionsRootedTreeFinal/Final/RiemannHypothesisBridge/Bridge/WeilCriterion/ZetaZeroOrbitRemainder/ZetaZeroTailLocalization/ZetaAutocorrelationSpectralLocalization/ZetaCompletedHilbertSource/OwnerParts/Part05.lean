import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaCompletedHilbertSource.OwnerParts.Part04

namespace Boundary
namespace LFunctions

noncomputable section

open Filter
open LSeries ArithmeticFunction
open scoped ArithmeticFunction
open scoped Topology
local notation "π" => Real.pi

namespace ZetaAdmissibleFunction

theorem completedPrimeOffDiagonalChannel_eq_positiveChannel_iff_completedPrimeOffDiagonalChannel_eq_zero
    (f : ZetaAdmissibleFunction) :
    completedPrimeOffDiagonalChannel f =
        completedPrimeDefectKernelPositiveChannel f ↔
      completedPrimeOffDiagonalChannel f = 0 := by
  constructor
  · intro hpositive
    calc
      completedPrimeOffDiagonalChannel f =
          completedPrimeDefectKernelPositiveChannel f := by
        exact hpositive
      _ = 0 := by
        exact completedPrimeDefectKernelPositiveChannel_eq_zero_of_completedLowerWeightNormalization
          f
  · intro hoffZero
    calc
      completedPrimeOffDiagonalChannel f = 0 := by
        exact hoffZero
      _ = completedPrimeDefectKernelPositiveChannel f := by
        exact
          (completedPrimeDefectKernelPositiveChannel_eq_zero_of_completedLowerWeightNormalization
            f).symm

/-- Under summed transport, vanishing of the completed two-face real scalar is equivalent to
vanishing of the completed off-diagonal channel. -/
theorem completedPrimeTwoFaceGNSMatrixCoefficient_re_eq_zero_iff_completedPrimeOffDiagonalChannel_eq_zero_of_summedTransport
    (f : ZetaAdmissibleFunction)
    (D : CompletedSummedPrimeContourTimeTransport f) :
    Complex.re (zetaCompletedPrimeTwoFaceGNSMatrixCoefficient f) = 0 ↔
      completedPrimeOffDiagonalChannel f = 0 := by
  have htwoFace :
      Complex.re (zetaCompletedPrimeTwoFaceGNSMatrixCoefficient f) =
        -completedPrimeOffDiagonalChannel f :=
    zetaCompletedPrimeTwoFaceGNSMatrixCoefficient_re_eq_neg_completedPrimeOffDiagonalChannel_ownerSummedDistributionTransport
      f D
  constructor
  · intro hzero
    have hneg_zero : -completedPrimeOffDiagonalChannel f = 0 :=
      htwoFace.symm.trans hzero
    calc
      completedPrimeOffDiagonalChannel f =
          -(-completedPrimeOffDiagonalChannel f) := by
        exact (neg_neg (completedPrimeOffDiagonalChannel f)).symm
      _ = -0 := by
        exact congrArg Neg.neg hneg_zero
      _ = 0 := by
        exact neg_zero
  · intro hoffZero
    calc
      Complex.re (zetaCompletedPrimeTwoFaceGNSMatrixCoefficient f) =
          -completedPrimeOffDiagonalChannel f := by
        exact htwoFace
      _ = -0 := by
        exact congrArg Neg.neg hoffZero
      _ = 0 := by
        exact neg_zero

/-- Under summed transport and the current finite-display lower-weight normalization, the
completed-vs-finite matrix comparison is equivalent to vanishing of the completed
off-diagonal channel. -/
theorem matrixComparison_iff_completedPrimeOffDiagonalChannel_eq_zero_of_summedTransport
    (f : ZetaAdmissibleFunction)
    (D : CompletedSummedPrimeContourTimeTransport f) :
    (Complex.re (zetaCompletedPrimeTwoFaceGNSMatrixCoefficient f) =
        Complex.re (zetaPrimeTwoFaceGNSMatrixCoefficient f)) ↔
      completedPrimeOffDiagonalChannel f = 0 := by
  exact
    (matrixComparison_iff_completedPrimeTwoFaceGNSMatrixCoefficient_re_eq_zero
      f).trans
      (completedPrimeTwoFaceGNSMatrixCoefficient_re_eq_zero_iff_completedPrimeOffDiagonalChannel_eq_zero_of_summedTransport
        f D)

/-- Under summed transport and lower-weight normalization, the completed off-diagonal
reconstruction bridge is exactly vanishing of the completed off-diagonal channel. -/
theorem completedPrimeOffDiagonalChannel_eq_neg_primeConvolutionContribution_re_iff_completedPrimeOffDiagonalChannel_eq_zero_summedTransport
    (f : ZetaAdmissibleFunction)
    (D : CompletedSummedPrimeContourTimeTransport f) :
    completedPrimeOffDiagonalChannel f =
        -Complex.re (zetaCompletedExplicitFormulaPrimeConvolutionContribution f) ↔
      completedPrimeOffDiagonalChannel f = 0 := by
  exact
    (completedPrimeOffDiagonalChannel_eq_neg_primeConvolutionContribution_re_iff_matrixComparison_of_summedTransport
      f D).trans
      (matrixComparison_iff_completedPrimeOffDiagonalChannel_eq_zero_of_summedTransport
        f D)

/-- Summed transport turns vanishing of the completed off-diagonal channel into the
completed off-diagonal reconstruction bridge. -/
theorem completedPrimeOffDiagonalChannel_eq_neg_primeConvolutionContribution_re_of_completedPrimeOffDiagonalChannel_eq_zero_summedTransport
    (f : ZetaAdmissibleFunction)
    (D : CompletedSummedPrimeContourTimeTransport f)
    (hoffZero : completedPrimeOffDiagonalChannel f = 0) :
    completedPrimeOffDiagonalChannel f =
      -Complex.re (zetaCompletedExplicitFormulaPrimeConvolutionContribution f) := by
  exact
    (completedPrimeOffDiagonalChannel_eq_neg_primeConvolutionContribution_re_iff_completedPrimeOffDiagonalChannel_eq_zero_summedTransport
      f D).mpr
      hoffZero

/-- The completed off-diagonal/positive-channel comparison is exactly the assertion that the
absorbed finite prime defect-square windows converge to the completed Hermitian positive
prime channel.

The square-ledger owner already proves that the same absorbed finite windows converge to the
completed off-diagonal channel.  This theorem is therefore pure uniqueness of the completed
finite-window limit, not a new reconstruction provider. -/
theorem completedPrimeOffDiagonalChannel_eq_positiveChannel_iff_absorbedPrimeDefectSquare_tendsto
    (f : ZetaAdmissibleFunction) :
    completedPrimeOffDiagonalChannel f =
        completedPrimeDefectKernelPositiveChannel f ↔
      Tendsto
        (fun N : ℕ =>
          zetaPrimeTranslationDefectEnergy N f +
            finitePartDebtAbsorptionWindow N f)
        atTop
        (𝓝 (completedPrimeDefectKernelPositiveChannel f)) := by
  constructor
  · intro hpositive
    have hoff :
        Tendsto
          (fun N : ℕ =>
            zetaPrimeTranslationDefectEnergy N f +
              finitePartDebtAbsorptionWindow N f)
          atTop
          (𝓝 (completedPrimeOffDiagonalChannel f)) :=
      zetaPrimeTranslationDefectEnergy_add_debtAbsorption_tendsto_completedPrimeOffDiagonalChannel
        f
    exact Eq.subst
      (motive := fun x : ℝ =>
        Tendsto
          (fun N : ℕ =>
            zetaPrimeTranslationDefectEnergy N f +
              finitePartDebtAbsorptionWindow N f)
          atTop
          (𝓝 x))
      hpositive
      hoff
  · intro hpositiveLimit
    have hoff :
        Tendsto
          (fun N : ℕ =>
            zetaPrimeTranslationDefectEnergy N f +
              finitePartDebtAbsorptionWindow N f)
          atTop
          (𝓝 (completedPrimeOffDiagonalChannel f)) :=
      zetaPrimeTranslationDefectEnergy_add_debtAbsorption_tendsto_completedPrimeOffDiagonalChannel
        f
    exact tendsto_nhds_unique hoff hpositiveLimit

/-- The completed-vs-finite two-face GNS real-coefficient comparison supplies the positive
owner limit for the absorbed finite prime defect-square stream. -/
theorem absorbedPrimeDefectSquare_tendsto_positiveChannel_of_matrixComparison
    (f : ZetaAdmissibleFunction)
    (D : CompletedFiniteWindowPrimeDistributionReconstruction f)
    (hmatrix :
      Complex.re (zetaCompletedPrimeTwoFaceGNSMatrixCoefficient f) =
        Complex.re (zetaPrimeTwoFaceGNSMatrixCoefficient f)) :
    Tendsto
      (fun N : ℕ =>
        zetaPrimeTranslationDefectEnergy N f +
          finitePartDebtAbsorptionWindow N f)
      atTop
      (𝓝 (completedPrimeDefectKernelPositiveChannel f)) := by
  have hpositive :
      completedPrimeOffDiagonalChannel f =
        completedPrimeDefectKernelPositiveChannel f :=
    completedPrimeOffDiagonalChannel_eq_positiveChannel_of_matrixComparison
      f D hmatrix
  exact
    (completedPrimeOffDiagonalChannel_eq_positiveChannel_iff_absorbedPrimeDefectSquare_tendsto
      f).mp
      hpositive

/-- The summed-transport version of the positive owner limit for the absorbed finite prime
defect-square stream from the completed-vs-finite two-face GNS real comparison. -/
theorem absorbedPrimeDefectSquare_tendsto_positiveChannel_of_matrixComparison_summedTransport
    (f : ZetaAdmissibleFunction)
    (D : CompletedSummedPrimeContourTimeTransport f)
    (hmatrix :
      Complex.re (zetaCompletedPrimeTwoFaceGNSMatrixCoefficient f) =
        Complex.re (zetaPrimeTwoFaceGNSMatrixCoefficient f)) :
    Tendsto
      (fun N : ℕ =>
        zetaPrimeTranslationDefectEnergy N f +
          finitePartDebtAbsorptionWindow N f)
      atTop
      (𝓝 (completedPrimeDefectKernelPositiveChannel f)) := by
  have hpositive :
      completedPrimeOffDiagonalChannel f =
        completedPrimeDefectKernelPositiveChannel f :=
    completedPrimeOffDiagonalChannel_eq_positiveChannel_of_matrixComparison_summedTransport
      f D hmatrix
  exact
    (completedPrimeOffDiagonalChannel_eq_positiveChannel_iff_absorbedPrimeDefectSquare_tendsto
      f).mp
      hpositive

/-- Vanishing of the completed two-face real coefficient supplies the positive owner limit
for the absorbed finite prime defect-square stream. -/
theorem absorbedPrimeDefectSquare_tendsto_positiveChannel_of_completedPrimeTwoFaceGNSMatrixCoefficient_re_eq_zero
    (f : ZetaAdmissibleFunction)
    (D : CompletedFiniteWindowPrimeDistributionReconstruction f)
    (htwoFaceZero :
      Complex.re (zetaCompletedPrimeTwoFaceGNSMatrixCoefficient f) = 0) :
    Tendsto
      (fun N : ℕ =>
        zetaPrimeTranslationDefectEnergy N f +
          finitePartDebtAbsorptionWindow N f)
      atTop
      (𝓝 (completedPrimeDefectKernelPositiveChannel f)) := by
  have hmatrix :
      Complex.re (zetaCompletedPrimeTwoFaceGNSMatrixCoefficient f) =
        Complex.re (zetaPrimeTwoFaceGNSMatrixCoefficient f) :=
    (matrixComparison_iff_completedPrimeTwoFaceGNSMatrixCoefficient_re_eq_zero
      f).mpr
      htwoFaceZero
  exact absorbedPrimeDefectSquare_tendsto_positiveChannel_of_matrixComparison
    f D hmatrix

/-- Summed-transport version: vanishing of the completed two-face real coefficient supplies
the positive owner limit for the absorbed finite prime defect-square stream. -/
theorem absorbedPrimeDefectSquare_tendsto_positiveChannel_of_completedPrimeTwoFaceGNSMatrixCoefficient_re_eq_zero_summedTransport
    (f : ZetaAdmissibleFunction)
    (D : CompletedSummedPrimeContourTimeTransport f)
    (htwoFaceZero :
      Complex.re (zetaCompletedPrimeTwoFaceGNSMatrixCoefficient f) = 0) :
    Tendsto
      (fun N : ℕ =>
        zetaPrimeTranslationDefectEnergy N f +
          finitePartDebtAbsorptionWindow N f)
      atTop
      (𝓝 (completedPrimeDefectKernelPositiveChannel f)) := by
  have hmatrix :
      Complex.re (zetaCompletedPrimeTwoFaceGNSMatrixCoefficient f) =
        Complex.re (zetaPrimeTwoFaceGNSMatrixCoefficient f) :=
    (matrixComparison_iff_completedPrimeTwoFaceGNSMatrixCoefficient_re_eq_zero
      f).mpr
      htwoFaceZero
  exact absorbedPrimeDefectSquare_tendsto_positiveChannel_of_matrixComparison_summedTransport
    f D hmatrix

/-- Vanishing of the completed off-diagonal channel supplies the positive owner limit for the
absorbed finite prime defect-square stream under the current lower-weight normalization. -/
theorem absorbedPrimeDefectSquare_tendsto_positiveChannel_of_completedPrimeOffDiagonalChannel_eq_zero
    (f : ZetaAdmissibleFunction)
    (hoffZero : completedPrimeOffDiagonalChannel f = 0) :
    Tendsto
      (fun N : ℕ =>
        zetaPrimeTranslationDefectEnergy N f +
          finitePartDebtAbsorptionWindow N f)
      atTop
      (𝓝 (completedPrimeDefectKernelPositiveChannel f)) := by
  have hpositive :
      completedPrimeOffDiagonalChannel f =
        completedPrimeDefectKernelPositiveChannel f :=
    (completedPrimeOffDiagonalChannel_eq_positiveChannel_iff_completedPrimeOffDiagonalChannel_eq_zero
      f).mpr
      hoffZero
  exact
    (completedPrimeOffDiagonalChannel_eq_positiveChannel_iff_absorbedPrimeDefectSquare_tendsto
      f).mp
      hpositive

/-- Under the current finite-display lower-weight normalization, the positive owner limit for
the absorbed finite prime defect-square stream is equivalent to vanishing of the completed
off-diagonal channel. -/
theorem absorbedPrimeDefectSquare_tendsto_positiveChannel_iff_completedPrimeOffDiagonalChannel_eq_zero
    (f : ZetaAdmissibleFunction) :
    Tendsto
        (fun N : ℕ =>
          zetaPrimeTranslationDefectEnergy N f +
            finitePartDebtAbsorptionWindow N f)
        atTop
        (𝓝 (completedPrimeDefectKernelPositiveChannel f)) ↔
      completedPrimeOffDiagonalChannel f = 0 := by
  exact
    (completedPrimeOffDiagonalChannel_eq_positiveChannel_iff_absorbedPrimeDefectSquare_tendsto
      f).symm.trans
      (completedPrimeOffDiagonalChannel_eq_positiveChannel_iff_completedPrimeOffDiagonalChannel_eq_zero
        f)

/-- With summed transport, the positive owner limit for the absorbed finite prime
defect-square stream is equivalent to vanishing of the completed two-face real coefficient. -/
theorem absorbedPrimeDefectSquare_tendsto_positiveChannel_iff_completedPrimeTwoFaceGNSMatrixCoefficient_re_eq_zero_summedTransport
    (f : ZetaAdmissibleFunction)
    (D : CompletedSummedPrimeContourTimeTransport f) :
    Tendsto
        (fun N : ℕ =>
          zetaPrimeTranslationDefectEnergy N f +
            finitePartDebtAbsorptionWindow N f)
        atTop
        (𝓝 (completedPrimeDefectKernelPositiveChannel f)) ↔
      Complex.re (zetaCompletedPrimeTwoFaceGNSMatrixCoefficient f) = 0 := by
  exact
    (absorbedPrimeDefectSquare_tendsto_positiveChannel_iff_completedPrimeOffDiagonalChannel_eq_zero
      f).trans
      (completedPrimeTwoFaceGNSMatrixCoefficient_re_eq_zero_iff_completedPrimeOffDiagonalChannel_eq_zero_of_summedTransport
        f D).symm

/-- With summed transport, the positive owner limit for the absorbed finite prime
defect-square stream is equivalent to the completed off-diagonal reconstruction bridge. -/
theorem absorbedPrimeDefectSquare_tendsto_positiveChannel_iff_completedPrimeOffDiagonalBridge_summedTransport
    (f : ZetaAdmissibleFunction)
    (D : CompletedSummedPrimeContourTimeTransport f) :
    Tendsto
        (fun N : ℕ =>
          zetaPrimeTranslationDefectEnergy N f +
            finitePartDebtAbsorptionWindow N f)
        atTop
        (𝓝 (completedPrimeDefectKernelPositiveChannel f)) ↔
      completedPrimeOffDiagonalChannel f =
        -Complex.re (zetaCompletedExplicitFormulaPrimeConvolutionContribution f) := by
  exact
    (absorbedPrimeDefectSquare_tendsto_positiveChannel_iff_completedPrimeOffDiagonalChannel_eq_zero
      f).trans
      (completedPrimeOffDiagonalChannel_eq_neg_primeConvolutionContribution_re_iff_completedPrimeOffDiagonalChannel_eq_zero_summedTransport
        f D).symm

/-- The same square-ledger uniqueness statement with the raw completed positive
prime-power coordinate presentation as target. -/
theorem completedPrimeOffDiagonalChannel_eq_positiveCoordinateTsumRe_iff_absorbedPrimeDefectSquare_tendsto
    (f : ZetaAdmissibleFunction) :
    completedPrimeOffDiagonalChannel f =
        zetaCompletedPrimeDefectKernelPositiveCoordinateTsumRe f ↔
      Tendsto
        (fun N : ℕ =>
          zetaPrimeTranslationDefectEnergy N f +
            finitePartDebtAbsorptionWindow N f)
        atTop
        (𝓝 (zetaCompletedPrimeDefectKernelPositiveCoordinateTsumRe f)) := by
  constructor
  · intro hcoordinate
    have hoff :
        Tendsto
          (fun N : ℕ =>
            zetaPrimeTranslationDefectEnergy N f +
              finitePartDebtAbsorptionWindow N f)
          atTop
          (𝓝 (completedPrimeOffDiagonalChannel f)) :=
      zetaPrimeTranslationDefectEnergy_add_debtAbsorption_tendsto_completedPrimeOffDiagonalChannel
        f
    exact Eq.subst
      (motive := fun x : ℝ =>
        Tendsto
          (fun N : ℕ =>
            zetaPrimeTranslationDefectEnergy N f +
              finitePartDebtAbsorptionWindow N f)
          atTop
          (𝓝 x))
      hcoordinate
      hoff
  · intro hcoordinateLimit
    have hoff :
        Tendsto
          (fun N : ℕ =>
            zetaPrimeTranslationDefectEnergy N f +
              finitePartDebtAbsorptionWindow N f)
        atTop
        (𝓝 (completedPrimeOffDiagonalChannel f)) :=
      zetaPrimeTranslationDefectEnergy_add_debtAbsorption_tendsto_completedPrimeOffDiagonalChannel
        f
    exact tendsto_nhds_unique hoff hcoordinateLimit

/-- If the absorbed finite prime defect-square stream converges to the raw positive
coordinate presentation, then the completed off-diagonal channel is that presentation. -/
theorem completedPrimeOffDiagonalChannel_eq_positiveCoordinateTsumRe_of_absorbedPrimeDefectSquare_tendsto
    (f : ZetaAdmissibleFunction)
    (hcoordinateLimit :
      Tendsto
        (fun N : ℕ =>
          zetaPrimeTranslationDefectEnergy N f +
            finitePartDebtAbsorptionWindow N f)
        atTop
        (𝓝 (zetaCompletedPrimeDefectKernelPositiveCoordinateTsumRe f))) :
    completedPrimeOffDiagonalChannel f =
      zetaCompletedPrimeDefectKernelPositiveCoordinateTsumRe f := by
  exact
    (completedPrimeOffDiagonalChannel_eq_positiveCoordinateTsumRe_iff_absorbedPrimeDefectSquare_tendsto
      f).mpr
      hcoordinateLimit

/-- Positive completed prime-power windows identify the raw positive coordinate presentation
with the owner positive channel by uniqueness of finite-window limits. -/
theorem zetaCompletedPrimeDefectKernelPositiveCoordinateTsumRe_eq_completedPrimeDefectKernelPositiveChannel_of_positiveRealWindow_tendsto
    (f : ZetaAdmissibleFunction)
    (hmajorant :
      Summable
        (fun ι : ZetaPrimePowerIndex =>
          zetaCompletedPrimeSpectralCoordinateMajorant ι f))
    (hpositiveLimit :
      Tendsto
        (fun N : ℕ => zetaCompletedPrimeDefectKernelPositiveRealWindow N f)
        atTop
        (𝓝 (completedPrimeDefectKernelPositiveChannel f))) :
    zetaCompletedPrimeDefectKernelPositiveCoordinateTsumRe f =
      completedPrimeDefectKernelPositiveChannel f := by
  have hcoordinateLimit :
      Tendsto
        (fun N : ℕ => zetaCompletedPrimeDefectKernelPositiveRealWindow N f)
        atTop
        (𝓝 (zetaCompletedPrimeDefectKernelPositiveCoordinateTsumRe f)) :=
    zetaCompletedPrimeDefectKernelPositiveRealWindow_tendsto_coordinateTsum_re_of_spectralMajorant
      f hmajorant
  exact tendsto_nhds_unique hcoordinateLimit hpositiveLimit

/-- The absorbed finite prime defect-square stream identifies the off-diagonal channel with
the owner positive channel once it has the owner positive-channel limit. -/
theorem completedPrimeOffDiagonalChannel_eq_completedPrimeDefectKernelPositiveChannel_of_absorbedPrimeDefectSquare_tendsto
    (f : ZetaAdmissibleFunction)
    (hpositiveLimit :
      Tendsto
        (fun N : ℕ =>
          zetaPrimeTranslationDefectEnergy N f +
            finitePartDebtAbsorptionWindow N f)
        atTop
        (𝓝 (completedPrimeDefectKernelPositiveChannel f))) :
    completedPrimeOffDiagonalChannel f =
      completedPrimeDefectKernelPositiveChannel f := by
  exact
    (completedPrimeOffDiagonalChannel_eq_positiveChannel_iff_absorbedPrimeDefectSquare_tendsto
      f).mpr
      hpositiveLimit

/-- If the absorbed finite prime defect-square stream has the raw positive-coordinate limit
and positive windows have the owner positive-channel limit, then the completed off-diagonal
and owner positive channels agree. -/
theorem completedPrimeOffDiagonalChannel_eq_completedPrimeDefectKernelPositiveChannel_of_coordinate_and_positive_window_limits
    (f : ZetaAdmissibleFunction)
    (hmajorant :
      Summable
        (fun ι : ZetaPrimePowerIndex =>
          zetaCompletedPrimeSpectralCoordinateMajorant ι f))
    (habsorbedCoordinateLimit :
      Tendsto
        (fun N : ℕ =>
          zetaPrimeTranslationDefectEnergy N f +
            finitePartDebtAbsorptionWindow N f)
        atTop
        (𝓝 (zetaCompletedPrimeDefectKernelPositiveCoordinateTsumRe f)))
    (hpositiveLimit :
      Tendsto
        (fun N : ℕ => zetaCompletedPrimeDefectKernelPositiveRealWindow N f)
        atTop
        (𝓝 (completedPrimeDefectKernelPositiveChannel f))) :
    completedPrimeOffDiagonalChannel f =
      completedPrimeDefectKernelPositiveChannel f := by
  have hoffCoordinate :
      completedPrimeOffDiagonalChannel f =
        zetaCompletedPrimeDefectKernelPositiveCoordinateTsumRe f :=
    completedPrimeOffDiagonalChannel_eq_positiveCoordinateTsumRe_of_absorbedPrimeDefectSquare_tendsto
      f habsorbedCoordinateLimit
  have hpositiveCoordinate :
      zetaCompletedPrimeDefectKernelPositiveCoordinateTsumRe f =
        completedPrimeDefectKernelPositiveChannel f :=
    zetaCompletedPrimeDefectKernelPositiveCoordinateTsumRe_eq_completedPrimeDefectKernelPositiveChannel_of_positiveRealWindow_tendsto
      f hmajorant hpositiveLimit
  exact hoffCoordinate.trans hpositiveCoordinate

/-- Coordinate and positive-window limits give the completed off-diagonal reconstruction
bridge through the owner positive prime channel. -/
theorem completedPrimeOffDiagonalChannel_eq_neg_primeConvolutionContribution_re_of_coordinate_and_positive_window_limits
    (f : ZetaAdmissibleFunction)
    (hmajorant :
      Summable
        (fun ι : ZetaPrimePowerIndex =>
          zetaCompletedPrimeSpectralCoordinateMajorant ι f))
    (habsorbedCoordinateLimit :
      Tendsto
        (fun N : ℕ =>
          zetaPrimeTranslationDefectEnergy N f +
            finitePartDebtAbsorptionWindow N f)
        atTop
        (𝓝 (zetaCompletedPrimeDefectKernelPositiveCoordinateTsumRe f)))
    (hpositiveLimit :
      Tendsto
        (fun N : ℕ => zetaCompletedPrimeDefectKernelPositiveRealWindow N f)
        atTop
        (𝓝 (completedPrimeDefectKernelPositiveChannel f))) :
    completedPrimeOffDiagonalChannel f =
      -Complex.re (zetaCompletedExplicitFormulaPrimeConvolutionContribution f) := by
  have hpositive :
      completedPrimeOffDiagonalChannel f =
        completedPrimeDefectKernelPositiveChannel f :=
    completedPrimeOffDiagonalChannel_eq_completedPrimeDefectKernelPositiveChannel_of_coordinate_and_positive_window_limits
      f hmajorant habsorbedCoordinateLimit hpositiveLimit
  exact
    completedPrimeOffDiagonalChannel_eq_neg_primeConvolutionContribution_re_of_positiveChannel
      f hpositive

/-- The absorbed coordinate limit and diagonal-debt owner limit identify the completed
off-diagonal channel with the owner positive prime channel. -/
theorem completedPrimeOffDiagonalChannel_eq_completedPrimeDefectKernelPositiveChannel_of_absorbedCoordinate_and_diagonalDebt_limits
    (f : ZetaAdmissibleFunction)
    (hmajorant :
      Summable
        (fun ι : ZetaPrimePowerIndex =>
          zetaCompletedPrimeSpectralCoordinateMajorant ι f))
    (habsorbedCoordinateLimit :
      Tendsto
        (fun N : ℕ =>
          zetaPrimeTranslationDefectEnergy N f +
            finitePartDebtAbsorptionWindow N f)
        atTop
        (𝓝 (zetaCompletedPrimeDefectKernelPositiveCoordinateTsumRe f)))
    (hdiagonalOwnerLimit :
      Tendsto
        (fun N : ℕ => zetaCompletedPrimeDefectKernelDiagonalDebtRealWindow N f)
        atTop
        (𝓝 (Complex.re (zetaCompletedPrimeDefectKernelDiagonalDebt f)))) :
    completedPrimeOffDiagonalChannel f =
      completedPrimeDefectKernelPositiveChannel f := by
  have hoffCoordinate :
      completedPrimeOffDiagonalChannel f =
        zetaCompletedPrimeDefectKernelPositiveCoordinateTsumRe f :=
    completedPrimeOffDiagonalChannel_eq_positiveCoordinateTsumRe_of_absorbedPrimeDefectSquare_tendsto
      f habsorbedCoordinateLimit
  have hpositiveCoordinate :
      zetaCompletedPrimeDefectKernelPositiveCoordinateTsumRe f =
        completedPrimeDefectKernelPositiveChannel f :=
    zetaCompletedPrimeDefectKernelPositiveCoordinateTsumRe_eq_completedPrimeDefectKernelPositiveChannel_of_diagonalDebtRealWindow_tendsto
      f hmajorant hdiagonalOwnerLimit
  exact hoffCoordinate.trans hpositiveCoordinate

/-- The absorbed coordinate limit and diagonal-debt owner limit give the completed
off-diagonal reconstruction bridge. -/
theorem completedPrimeOffDiagonalChannel_eq_neg_primeConvolutionContribution_re_of_absorbedCoordinate_and_diagonalDebt_limits
    (f : ZetaAdmissibleFunction)
    (hmajorant :
      Summable
        (fun ι : ZetaPrimePowerIndex =>
          zetaCompletedPrimeSpectralCoordinateMajorant ι f))
    (habsorbedCoordinateLimit :
      Tendsto
        (fun N : ℕ =>
          zetaPrimeTranslationDefectEnergy N f +
            finitePartDebtAbsorptionWindow N f)
        atTop
        (𝓝 (zetaCompletedPrimeDefectKernelPositiveCoordinateTsumRe f)))
    (hdiagonalOwnerLimit :
      Tendsto
        (fun N : ℕ => zetaCompletedPrimeDefectKernelDiagonalDebtRealWindow N f)
        atTop
        (𝓝 (Complex.re (zetaCompletedPrimeDefectKernelDiagonalDebt f)))) :
    completedPrimeOffDiagonalChannel f =
      -Complex.re (zetaCompletedExplicitFormulaPrimeConvolutionContribution f) := by
  have hpositive :
      completedPrimeOffDiagonalChannel f =
        completedPrimeDefectKernelPositiveChannel f :=
    completedPrimeOffDiagonalChannel_eq_completedPrimeDefectKernelPositiveChannel_of_absorbedCoordinate_and_diagonalDebt_limits
      f hmajorant habsorbedCoordinateLimit hdiagonalOwnerLimit
  exact
    completedPrimeOffDiagonalChannel_eq_neg_primeConvolutionContribution_re_of_positiveChannel
      f hpositive

/-- The coordinate-presentation comparison and the off-diagonal/coordinate comparison
supply the remaining positive-channel convergence for the absorbed prime defect-square
stream. -/
theorem absorbedPrimeDefectSquare_tendsto_positiveChannel_of_coordinateTsumRe_comparisons
    (f : ZetaAdmissibleFunction)
    (hoffCoordinate :
      completedPrimeOffDiagonalChannel f =
        zetaCompletedPrimeDefectKernelPositiveCoordinateTsumRe f)
    (hpositiveCoordinate :
      zetaCompletedPrimeDefectKernelPositiveCoordinateTsumRe f =
        completedPrimeDefectKernelPositiveChannel f) :
    Tendsto
      (fun N : ℕ =>
        zetaPrimeTranslationDefectEnergy N f +
          finitePartDebtAbsorptionWindow N f)
      atTop
      (𝓝 (completedPrimeDefectKernelPositiveChannel f)) := by
  have hcoordinateLimit :
      Tendsto
        (fun N : ℕ =>
          zetaPrimeTranslationDefectEnergy N f +
            finitePartDebtAbsorptionWindow N f)
        atTop
        (𝓝 (zetaCompletedPrimeDefectKernelPositiveCoordinateTsumRe f)) :=
    (completedPrimeOffDiagonalChannel_eq_positiveCoordinateTsumRe_iff_absorbedPrimeDefectSquare_tendsto
      f).mp
      hoffCoordinate
  exact Eq.subst
    (motive := fun x : ℝ =>
      Tendsto
        (fun N : ℕ =>
          zetaPrimeTranslationDefectEnergy N f +
            finitePartDebtAbsorptionWindow N f)
        atTop
        (𝓝 x))
    hpositiveCoordinate
    hcoordinateLimit

/-- The absorbed finite prime defect-square stream converges to the owner positive prime
channel once its positive-coordinate limit and the diagonal-debt owner limit are known. -/
theorem absorbedPrimeDefectSquare_tendsto_positiveChannel_of_absorbedCoordinate_and_diagonalDebt_limits
    (f : ZetaAdmissibleFunction)
    (hmajorant :
      Summable
        (fun ι : ZetaPrimePowerIndex =>
          zetaCompletedPrimeSpectralCoordinateMajorant ι f))
    (habsorbedCoordinateLimit :
      Tendsto
        (fun N : ℕ =>
          zetaPrimeTranslationDefectEnergy N f +
            finitePartDebtAbsorptionWindow N f)
        atTop
        (𝓝 (zetaCompletedPrimeDefectKernelPositiveCoordinateTsumRe f)))
    (hdiagonalOwnerLimit :
      Tendsto
        (fun N : ℕ => zetaCompletedPrimeDefectKernelDiagonalDebtRealWindow N f)
        atTop
        (𝓝 (Complex.re (zetaCompletedPrimeDefectKernelDiagonalDebt f)))) :
    Tendsto
      (fun N : ℕ =>
        zetaPrimeTranslationDefectEnergy N f +
          finitePartDebtAbsorptionWindow N f)
      atTop
      (𝓝 (completedPrimeDefectKernelPositiveChannel f)) := by
  have hoffCoordinate :
      completedPrimeOffDiagonalChannel f =
        zetaCompletedPrimeDefectKernelPositiveCoordinateTsumRe f :=
    completedPrimeOffDiagonalChannel_eq_positiveCoordinateTsumRe_of_absorbedPrimeDefectSquare_tendsto
      f habsorbedCoordinateLimit
  have hpositiveCoordinate :
      zetaCompletedPrimeDefectKernelPositiveCoordinateTsumRe f =
        completedPrimeDefectKernelPositiveChannel f :=
    zetaCompletedPrimeDefectKernelPositiveCoordinateTsumRe_eq_completedPrimeDefectKernelPositiveChannel_of_diagonalDebtRealWindow_tendsto
      f hmajorant hdiagonalOwnerLimit
  exact
    absorbedPrimeDefectSquare_tendsto_positiveChannel_of_coordinateTsumRe_comparisons
      f hoffCoordinate hpositiveCoordinate

/-- The coordinate-presentation comparisons imply the completed off-diagonal reconstruction
bridge. -/
theorem completedPrimeOffDiagonalChannel_eq_neg_primeConvolutionContribution_re_of_coordinateTsumRe_comparisons
    (f : ZetaAdmissibleFunction)
    (hoffCoordinate :
      completedPrimeOffDiagonalChannel f =
        zetaCompletedPrimeDefectKernelPositiveCoordinateTsumRe f)
    (hpositiveCoordinate :
      zetaCompletedPrimeDefectKernelPositiveCoordinateTsumRe f =
        completedPrimeDefectKernelPositiveChannel f) :
    completedPrimeOffDiagonalChannel f =
      -Complex.re (zetaCompletedExplicitFormulaPrimeConvolutionContribution f) := by
  have hpositive :
      completedPrimeOffDiagonalChannel f =
        completedPrimeDefectKernelPositiveChannel f :=
    hoffCoordinate.trans hpositiveCoordinate
  exact
    completedPrimeOffDiagonalChannel_eq_neg_primeConvolutionContribution_re_of_positiveChannel
      f hpositive

end ZetaAdmissibleFunction

end
end LFunctions
end Boundary
