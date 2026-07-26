import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaCompletedHilbertSource.OwnerParts.Part03

namespace Boundary
namespace LFunctions

noncomputable section

open Filter
open LSeries ArithmeticFunction
open scoped ArithmeticFunction
open scoped Topology
local notation "π" => Real.pi

namespace ZetaAdmissibleFunction

theorem finitePrimeTimeDistributionWindow_add_coordinateRemainderWindow_coordinateRemainderTransport
    (N : ℕ) (f : ZetaAdmissibleFunction) :
    finitePrimeTimeDistributionWindow N (convolutionAutocorrelation f) +
        finitePrimeContourTransportCoordinateRemainderWindow N f =
      finitePrimeContourRealizedTimeDistributionWindow N
        (convolutionAutocorrelation f) := by
  exact
    finitePrimeTimeDistributionWindow_add_coordinateRemainderWindow_ownerPrimeTransport
      N f

/-- The completed two-face boundary coefficient has the opposite real scalar from the finite
reconstructed prime convolution contribution.

This is the signed finite/completed normalization for the prime two-face packet.  The
boundary coefficient is the explicit-formula signed coefficient, while the reconstructed
prime convolution contribution is the GNS two-face matrix coefficient. -/
theorem zetaCompletedPrimeTwoFaceGNSBoundaryCoefficient_re_eq_neg_primeConvolutionContribution_re
    (f : ZetaAdmissibleFunction)
    (hmatrix :
      Complex.re (zetaCompletedPrimeTwoFaceGNSMatrixCoefficient f) =
        Complex.re (zetaPrimeTwoFaceGNSMatrixCoefficient f)) :
    Complex.re (zetaCompletedPrimeTwoFaceGNSBoundaryCoefficient f) =
      -Complex.re (zetaCompletedExplicitFormulaPrimeConvolutionContribution f) := by
  let Tc : ℂ := zetaCompletedPrimeTwoFaceGNSMatrixCoefficient f
  let Tf : ℂ := zetaPrimeTwoFaceGNSMatrixCoefficient f
  have hboundary :
      zetaCompletedPrimeTwoFaceGNSBoundaryCoefficient f = -Tc := by
    unfold Tc
    exact zetaCompletedPrimeTwoFaceGNSBoundaryCoefficient_eq_neg_matrixCoefficient f
  have hcontribution :
      zetaCompletedExplicitFormulaPrimeConvolutionContribution f = Tf := by
    unfold Tf
    exact zetaCompletedExplicitFormulaPrimeConvolutionContribution_eq_twoFaceMatrixCoefficient
      f
  calc
    Complex.re (zetaCompletedPrimeTwoFaceGNSBoundaryCoefficient f) =
        Complex.re (-Tc) := by
      exact congrArg Complex.re hboundary
    _ = -Complex.re Tc := by
      exact Complex.neg_re Tc
    _ = -Complex.re Tf := by
      exact congrArg Neg.neg hmatrix
    _ = -Complex.re (zetaCompletedExplicitFormulaPrimeConvolutionContribution f) := by
      exact congrArg Neg.neg (congrArg Complex.re hcontribution.symm)

/-- Explicit owner gap: the completed time-side prime off-diagonal channel agrees with the
signed reconstructed prime convolution contribution after the summed completed explicit-formula
transport has replaced the legacy finite physical/spectral window equality. -/
theorem completedPrimeOffDiagonalChannel_eq_neg_primeConvolutionContribution_re
    (f : ZetaAdmissibleFunction)
    (D : CompletedFiniteWindowPrimeDistributionReconstruction f)
    (hmatrix :
      Complex.re (zetaCompletedPrimeTwoFaceGNSMatrixCoefficient f) =
        Complex.re (zetaPrimeTwoFaceGNSMatrixCoefficient f)) :
    completedPrimeOffDiagonalChannel f =
      -Complex.re (zetaCompletedExplicitFormulaPrimeConvolutionContribution f) := by
  have htransport :
      completedPrimeOffDiagonalChannel f =
        Complex.re (zetaCompletedPrimeTwoFaceGNSBoundaryCoefficient f) :=
    completedPrimeOffDiagonalChannel_eq_completedTwoFaceGNSBoundaryCoefficient_re_ownerDistributionTransport
      f D
  have hsigned :
      Complex.re (zetaCompletedPrimeTwoFaceGNSBoundaryCoefficient f) =
        -Complex.re (zetaCompletedExplicitFormulaPrimeConvolutionContribution f) :=
    zetaCompletedPrimeTwoFaceGNSBoundaryCoefficient_re_eq_neg_primeConvolutionContribution_re
      f hmatrix
  exact htransport.trans hsigned

/-- The completed time-side prime off-diagonal channel agrees with the signed reconstructed
prime convolution contribution using the explicit summed contour/time transport provider. -/
theorem completedPrimeOffDiagonalChannel_eq_neg_primeConvolutionContribution_re_of_summedTransport
    (f : ZetaAdmissibleFunction)
    (D : CompletedSummedPrimeContourTimeTransport f)
    (hmatrix :
      Complex.re (zetaCompletedPrimeTwoFaceGNSMatrixCoefficient f) =
        Complex.re (zetaPrimeTwoFaceGNSMatrixCoefficient f)) :
    completedPrimeOffDiagonalChannel f =
      -Complex.re (zetaCompletedExplicitFormulaPrimeConvolutionContribution f) := by
  have htransport :
      completedPrimeOffDiagonalChannel f =
        Complex.re (zetaCompletedPrimeTwoFaceGNSBoundaryCoefficient f) :=
    completedPrimeOffDiagonalChannel_eq_completedTwoFaceGNSBoundaryCoefficient_re_ownerSummedDistributionTransport
      f D
  have hsigned :
      Complex.re (zetaCompletedPrimeTwoFaceGNSBoundaryCoefficient f) =
        -Complex.re (zetaCompletedExplicitFormulaPrimeConvolutionContribution f) :=
    zetaCompletedPrimeTwoFaceGNSBoundaryCoefficient_re_eq_neg_primeConvolutionContribution_re
      f hmatrix
  exact htransport.trans hsigned

/-- A completed off-diagonal reconstruction bridge gives the completed-vs-finite GNS
real-coefficient comparison.

This is the forward implication in the genuine completed-to-finite prime bridge: the completed
two-face coefficient is first transported to the completed off-diagonal channel, and the
finite side is then identified with the reconstructed prime convolution packet. -/
theorem zetaCompletedPrimeTwoFaceGNSMatrixCoefficient_re_eq_finite_of_completedPrimeOffDiagonalBridge
    (f : ZetaAdmissibleFunction)
    (D : CompletedFiniteWindowPrimeDistributionReconstruction f)
    (hbridge :
      completedPrimeOffDiagonalChannel f =
        -Complex.re (zetaCompletedExplicitFormulaPrimeConvolutionContribution f)) :
    Complex.re (zetaCompletedPrimeTwoFaceGNSMatrixCoefficient f) =
      Complex.re (zetaPrimeTwoFaceGNSMatrixCoefficient f) := by
  have hcompleted :
      Complex.re (zetaCompletedPrimeTwoFaceGNSMatrixCoefficient f) =
        -completedPrimeOffDiagonalChannel f :=
    zetaCompletedPrimeTwoFaceGNSMatrixCoefficient_re_eq_neg_completedPrimeOffDiagonalChannel_ownerDistributionTransport
      f D
  have hfinite :
      Complex.re (zetaCompletedExplicitFormulaPrimeConvolutionContribution f) =
        Complex.re (zetaPrimeTwoFaceGNSMatrixCoefficient f) :=
    zetaCompletedExplicitFormulaPrimeConvolutionContribution_re_eq_twoFaceMatrixCoefficient
      f
  calc
    Complex.re (zetaCompletedPrimeTwoFaceGNSMatrixCoefficient f) =
        -completedPrimeOffDiagonalChannel f := by
      exact hcompleted
    _ = -(-Complex.re (zetaCompletedExplicitFormulaPrimeConvolutionContribution f)) := by
      exact congrArg Neg.neg hbridge
    _ = Complex.re (zetaCompletedExplicitFormulaPrimeConvolutionContribution f) := by
      exact neg_neg
        (Complex.re (zetaCompletedExplicitFormulaPrimeConvolutionContribution f))
    _ = Complex.re (zetaPrimeTwoFaceGNSMatrixCoefficient f) := by
      exact hfinite

/-- The visible-remainder summed transport version of the completed off-diagonal bridge
to the completed-vs-finite GNS real-coefficient comparison. -/
theorem zetaCompletedPrimeTwoFaceGNSMatrixCoefficient_re_eq_finite_of_completedPrimeOffDiagonalBridge_summedTransport
    (f : ZetaAdmissibleFunction)
    (D : CompletedSummedPrimeContourTimeTransport f)
    (hbridge :
      completedPrimeOffDiagonalChannel f =
        -Complex.re (zetaCompletedExplicitFormulaPrimeConvolutionContribution f)) :
    Complex.re (zetaCompletedPrimeTwoFaceGNSMatrixCoefficient f) =
      Complex.re (zetaPrimeTwoFaceGNSMatrixCoefficient f) := by
  have hcompleted :
      Complex.re (zetaCompletedPrimeTwoFaceGNSMatrixCoefficient f) =
        -completedPrimeOffDiagonalChannel f :=
    zetaCompletedPrimeTwoFaceGNSMatrixCoefficient_re_eq_neg_completedPrimeOffDiagonalChannel_ownerSummedDistributionTransport
      f D
  have hfinite :
      Complex.re (zetaCompletedExplicitFormulaPrimeConvolutionContribution f) =
        Complex.re (zetaPrimeTwoFaceGNSMatrixCoefficient f) :=
    zetaCompletedExplicitFormulaPrimeConvolutionContribution_re_eq_twoFaceMatrixCoefficient
      f
  calc
    Complex.re (zetaCompletedPrimeTwoFaceGNSMatrixCoefficient f) =
        -completedPrimeOffDiagonalChannel f := by
      exact hcompleted
    _ = -(-Complex.re (zetaCompletedExplicitFormulaPrimeConvolutionContribution f)) := by
      exact congrArg Neg.neg hbridge
    _ = Complex.re (zetaCompletedExplicitFormulaPrimeConvolutionContribution f) := by
      exact neg_neg
        (Complex.re (zetaCompletedExplicitFormulaPrimeConvolutionContribution f))
    _ = Complex.re (zetaPrimeTwoFaceGNSMatrixCoefficient f) := by
      exact hfinite

/-- The completed off-diagonal bridge to the finite reconstructed prime two-face packet is
equivalent to the completed-vs-finite GNS real-coefficient comparison.

The forward direction recovers the coefficient comparison from the transported completed
two-face sign and the finite convolution reconstruction.  The reverse direction is the
previous signed normalization. -/
theorem completedPrimeOffDiagonalChannel_eq_neg_primeConvolutionContribution_re_iff_matrixComparison
    (f : ZetaAdmissibleFunction)
    (D : CompletedFiniteWindowPrimeDistributionReconstruction f) :
    completedPrimeOffDiagonalChannel f =
        -Complex.re (zetaCompletedExplicitFormulaPrimeConvolutionContribution f) ↔
      Complex.re (zetaCompletedPrimeTwoFaceGNSMatrixCoefficient f) =
        Complex.re (zetaPrimeTwoFaceGNSMatrixCoefficient f) := by
  constructor
  · intro hbridge
    exact
      zetaCompletedPrimeTwoFaceGNSMatrixCoefficient_re_eq_finite_of_completedPrimeOffDiagonalBridge
        f D hbridge
  · intro hmatrix
    exact completedPrimeOffDiagonalChannel_eq_neg_primeConvolutionContribution_re
      f D hmatrix

/-- The visible-remainder summed transport version of the completed off-diagonal bridge
equivalence. -/
theorem completedPrimeOffDiagonalChannel_eq_neg_primeConvolutionContribution_re_iff_matrixComparison_of_summedTransport
    (f : ZetaAdmissibleFunction)
    (D : CompletedSummedPrimeContourTimeTransport f) :
    completedPrimeOffDiagonalChannel f =
        -Complex.re (zetaCompletedExplicitFormulaPrimeConvolutionContribution f) ↔
      Complex.re (zetaCompletedPrimeTwoFaceGNSMatrixCoefficient f) =
        Complex.re (zetaPrimeTwoFaceGNSMatrixCoefficient f) := by
  constructor
  · intro hbridge
    exact
      zetaCompletedPrimeTwoFaceGNSMatrixCoefficient_re_eq_finite_of_completedPrimeOffDiagonalBridge_summedTransport
        f D hbridge
  · intro hmatrix
    exact completedPrimeOffDiagonalChannel_eq_neg_primeConvolutionContribution_re_of_summedTransport
      f D hmatrix

/-- The prime boundary channel agrees with the signed reconstructed prime convolution
contribution once the completed time-distribution normalization is supplied. -/
theorem primeBoundaryChannel_convolutionAutocorrelation_re_eq_neg_primeConvolutionContribution
    (f : ZetaAdmissibleFunction)
    (D : CompletedFiniteWindowPrimeDistributionReconstruction f)
    (hmatrix :
      Complex.re (zetaCompletedPrimeTwoFaceGNSMatrixCoefficient f) =
        Complex.re (zetaPrimeTwoFaceGNSMatrixCoefficient f)) :
    Complex.re (primeBoundaryChannel (convolutionAutocorrelation f)) =
      -Complex.re (zetaCompletedExplicitFormulaPrimeConvolutionContribution f) := by
  have hboundary :
      completedPrimeOffDiagonalChannel f =
        Complex.re (primeBoundaryChannel (convolutionAutocorrelation f)) :=
    completedPrimeOffDiagonalChannel_eq_primeBoundaryChannel f
  have hnormalization :
      completedPrimeOffDiagonalChannel f =
      -Complex.re (zetaCompletedExplicitFormulaPrimeConvolutionContribution f) :=
    completedPrimeOffDiagonalChannel_eq_neg_primeConvolutionContribution_re f D hmatrix
  exact hboundary.symm.trans hnormalization

/-- The prime boundary channel agrees with the signed reconstructed prime convolution
contribution from the explicit summed contour/time transport provider. -/
theorem primeBoundaryChannel_convolutionAutocorrelation_re_eq_neg_primeConvolutionContribution_of_summedTransport
    (f : ZetaAdmissibleFunction)
    (D : CompletedSummedPrimeContourTimeTransport f)
    (hmatrix :
      Complex.re (zetaCompletedPrimeTwoFaceGNSMatrixCoefficient f) =
        Complex.re (zetaPrimeTwoFaceGNSMatrixCoefficient f)) :
    Complex.re (primeBoundaryChannel (convolutionAutocorrelation f)) =
      -Complex.re (zetaCompletedExplicitFormulaPrimeConvolutionContribution f) := by
  have hboundary :
      completedPrimeOffDiagonalChannel f =
        Complex.re (primeBoundaryChannel (convolutionAutocorrelation f)) :=
    completedPrimeOffDiagonalChannel_eq_primeBoundaryChannel f
  have hnormalization :
      completedPrimeOffDiagonalChannel f =
      -Complex.re (zetaCompletedExplicitFormulaPrimeConvolutionContribution f) :=
    completedPrimeOffDiagonalChannel_eq_neg_primeConvolutionContribution_re_of_summedTransport
      f D hmatrix
  exact hboundary.symm.trans hnormalization

/-- The finite prime diagonal-debt real scalar cancels in the completed two-face
normalization. -/
theorem zetaPrimeDefectKernelDiagonalDebt_re_eq_zero_of_lowerWeightNormalization
    (f : ZetaAdmissibleFunction) :
    Complex.re (zetaPrimeDefectKernelDiagonalDebt f) = 0 := by
  exact
    zetaPrimeDefectKernelDiagonalDebt_re_eq_zero_of_completedLowerWeightNormalization
      f

/-- The reconstructed prime two-face channel has the opposite real scalar from the positive
prime-defect channel under lower-weight normalization. -/
theorem zetaPrimeTwoFaceGNSMatrixCoefficient_re_eq_neg_positiveChannel_of_lowerWeightNormalization
    (f : ZetaAdmissibleFunction) :
    Complex.re (zetaPrimeTwoFaceGNSMatrixCoefficient f) =
      -completedPrimeDefectKernelPositiveChannel f := by
  let P : ℝ := completedPrimeDefectKernelPositiveChannel f
  let T : ℝ := Complex.re (zetaPrimeTwoFaceGNSMatrixCoefficient f)
  have hpositive :
      P = Complex.re (zetaPrimeDefectKernelPositiveForm f) := by
    unfold P
    exact completedPrimeDefectKernelPositiveChannel_eq_finitePositiveForm_re f
  have hexpansion :
      Complex.re (zetaPrimeDefectKernelPositiveForm f) +
          Complex.re (zetaPrimeTwoFaceGNSMatrixCoefficient f) =
        Complex.re (zetaPrimeDefectKernelDiagonalDebt f) :=
    zetaPrimeDefectKernelPositiveForm_re_add_twoFace_re_eq_diagonalDebt_re f
  have hdebt :
      Complex.re (zetaPrimeDefectKernelDiagonalDebt f) = 0 :=
    zetaPrimeDefectKernelDiagonalDebt_re_eq_zero_of_lowerWeightNormalization f
  have hsum :
      P + T = 0 := by
    calc
      P + T =
          Complex.re (zetaPrimeDefectKernelPositiveForm f) +
            Complex.re (zetaPrimeTwoFaceGNSMatrixCoefficient f) := by
        exact congrArg
          (fun x : ℝ =>
            x + Complex.re (zetaPrimeTwoFaceGNSMatrixCoefficient f))
          hpositive
      _ = Complex.re (zetaPrimeDefectKernelDiagonalDebt f) := by
        exact hexpansion
      _ = 0 := by
        exact hdebt
  have hsum_comm : T + P = 0 := by
    exact (add_comm T P).trans hsum
  have hsigned : T = -P :=
    eq_neg_of_add_eq_zero_left hsum_comm
  exact hsigned

/-- The explicit prime convolution contribution inherits the signed two-face normalization. -/
theorem zetaCompletedExplicitFormulaPrimeConvolutionContribution_re_eq_neg_positiveChannel_of_lowerWeightNormalization
    (f : ZetaAdmissibleFunction) :
    Complex.re (zetaCompletedExplicitFormulaPrimeConvolutionContribution f) =
      -completedPrimeDefectKernelPositiveChannel f := by
  have htwoFace :
      Complex.re (zetaCompletedExplicitFormulaPrimeConvolutionContribution f) =
        Complex.re (zetaPrimeTwoFaceGNSMatrixCoefficient f) :=
    zetaCompletedExplicitFormulaPrimeConvolutionContribution_re_eq_twoFaceMatrixCoefficient
      f
  have hsigned :
      Complex.re (zetaPrimeTwoFaceGNSMatrixCoefficient f) =
        -completedPrimeDefectKernelPositiveChannel f :=
    zetaPrimeTwoFaceGNSMatrixCoefficient_re_eq_neg_positiveChannel_of_lowerWeightNormalization
      f
  exact htwoFace.trans hsigned

/-- The actual completed off-diagonal reconstruction bridge is equivalent to identifying the
completed off-diagonal prime channel with the positive prime-defect channel.

This isolates the remaining prime-only limit theorem: the finite reconstructed convolution
packet has real scalar `-completedPrimeDefectKernelPositiveChannel`, so the completed bridge
is exactly the assertion that the completed off-diagonal limit is the same positive channel. -/
theorem completedPrimeOffDiagonalChannel_eq_neg_primeConvolutionContribution_re_iff_positiveChannel
    (f : ZetaAdmissibleFunction) :
    completedPrimeOffDiagonalChannel f =
        -Complex.re (zetaCompletedExplicitFormulaPrimeConvolutionContribution f) ↔
      completedPrimeOffDiagonalChannel f =
        completedPrimeDefectKernelPositiveChannel f := by
  constructor
  · intro hbridge
    have hfinite :
        Complex.re (zetaCompletedExplicitFormulaPrimeConvolutionContribution f) =
          -completedPrimeDefectKernelPositiveChannel f :=
      zetaCompletedExplicitFormulaPrimeConvolutionContribution_re_eq_neg_positiveChannel_of_lowerWeightNormalization
        f
    calc
      completedPrimeOffDiagonalChannel f =
          -Complex.re (zetaCompletedExplicitFormulaPrimeConvolutionContribution f) := by
        exact hbridge
      _ = -(-completedPrimeDefectKernelPositiveChannel f) := by
        exact congrArg Neg.neg hfinite
      _ = completedPrimeDefectKernelPositiveChannel f := by
        exact neg_neg (completedPrimeDefectKernelPositiveChannel f)
  · intro hpositive
    have hfinite :
        Complex.re (zetaCompletedExplicitFormulaPrimeConvolutionContribution f) =
          -completedPrimeDefectKernelPositiveChannel f :=
      zetaCompletedExplicitFormulaPrimeConvolutionContribution_re_eq_neg_positiveChannel_of_lowerWeightNormalization
        f
    calc
      completedPrimeOffDiagonalChannel f =
          completedPrimeDefectKernelPositiveChannel f := by
        exact hpositive
      _ = -(-completedPrimeDefectKernelPositiveChannel f) := by
        exact (neg_neg (completedPrimeDefectKernelPositiveChannel f)).symm
      _ = -Complex.re (zetaCompletedExplicitFormulaPrimeConvolutionContribution f) := by
        exact congrArg Neg.neg hfinite.symm

/-- The remaining prime-only completed limit theorem implies the completed off-diagonal
reconstruction bridge. -/
theorem completedPrimeOffDiagonalChannel_eq_neg_primeConvolutionContribution_re_of_positiveChannel
    (f : ZetaAdmissibleFunction)
    (hpositive :
      completedPrimeOffDiagonalChannel f =
        completedPrimeDefectKernelPositiveChannel f) :
    completedPrimeOffDiagonalChannel f =
      -Complex.re (zetaCompletedExplicitFormulaPrimeConvolutionContribution f) := by
  exact
    (completedPrimeOffDiagonalChannel_eq_neg_primeConvolutionContribution_re_iff_positiveChannel
      f).mpr hpositive

/-- The completed off-diagonal/positive-channel comparison is equivalent to the
completed-vs-finite two-face GNS real-coefficient comparison. -/
theorem completedPrimeOffDiagonalChannel_eq_positiveChannel_iff_matrixComparison
    (f : ZetaAdmissibleFunction)
    (D : CompletedFiniteWindowPrimeDistributionReconstruction f) :
    completedPrimeOffDiagonalChannel f =
        completedPrimeDefectKernelPositiveChannel f ↔
      Complex.re (zetaCompletedPrimeTwoFaceGNSMatrixCoefficient f) =
        Complex.re (zetaPrimeTwoFaceGNSMatrixCoefficient f) := by
  exact
    (completedPrimeOffDiagonalChannel_eq_neg_primeConvolutionContribution_re_iff_positiveChannel
      f).symm.trans
      (completedPrimeOffDiagonalChannel_eq_neg_primeConvolutionContribution_re_iff_matrixComparison
        f D)

/-- The summed-transport version of the completed off-diagonal/positive-channel comparison
equivalence with the completed-vs-finite two-face GNS real-coefficient comparison. -/
theorem completedPrimeOffDiagonalChannel_eq_positiveChannel_iff_matrixComparison_of_summedTransport
    (f : ZetaAdmissibleFunction)
    (D : CompletedSummedPrimeContourTimeTransport f) :
    completedPrimeOffDiagonalChannel f =
        completedPrimeDefectKernelPositiveChannel f ↔
      Complex.re (zetaCompletedPrimeTwoFaceGNSMatrixCoefficient f) =
        Complex.re (zetaPrimeTwoFaceGNSMatrixCoefficient f) := by
  exact
    (completedPrimeOffDiagonalChannel_eq_neg_primeConvolutionContribution_re_iff_positiveChannel
      f).symm.trans
      (completedPrimeOffDiagonalChannel_eq_neg_primeConvolutionContribution_re_iff_matrixComparison_of_summedTransport
        f D)

/-- The completed-vs-finite two-face GNS real-coefficient comparison gives the
completed off-diagonal/positive-channel comparison. -/
theorem completedPrimeOffDiagonalChannel_eq_positiveChannel_of_matrixComparison
    (f : ZetaAdmissibleFunction)
    (D : CompletedFiniteWindowPrimeDistributionReconstruction f)
    (hmatrix :
      Complex.re (zetaCompletedPrimeTwoFaceGNSMatrixCoefficient f) =
        Complex.re (zetaPrimeTwoFaceGNSMatrixCoefficient f)) :
    completedPrimeOffDiagonalChannel f =
      completedPrimeDefectKernelPositiveChannel f := by
  exact
    (completedPrimeOffDiagonalChannel_eq_positiveChannel_iff_matrixComparison
      f D).mpr
      hmatrix

/-- The summed-transport version: the completed-vs-finite two-face GNS real-coefficient
comparison gives the completed off-diagonal/positive-channel comparison. -/
theorem completedPrimeOffDiagonalChannel_eq_positiveChannel_of_matrixComparison_summedTransport
    (f : ZetaAdmissibleFunction)
    (D : CompletedSummedPrimeContourTimeTransport f)
    (hmatrix :
      Complex.re (zetaCompletedPrimeTwoFaceGNSMatrixCoefficient f) =
        Complex.re (zetaPrimeTwoFaceGNSMatrixCoefficient f)) :
    completedPrimeOffDiagonalChannel f =
      completedPrimeDefectKernelPositiveChannel f := by
  exact
    (completedPrimeOffDiagonalChannel_eq_positiveChannel_iff_matrixComparison_of_summedTransport
      f D).mpr
      hmatrix

/-- Under the current finite-display lower-weight normalization, the completed-vs-finite
two-face GNS real-coefficient comparison is exactly vanishing of the completed two-face real
coefficient. -/
theorem matrixComparison_iff_completedPrimeTwoFaceGNSMatrixCoefficient_re_eq_zero
    (f : ZetaAdmissibleFunction) :
    (Complex.re (zetaCompletedPrimeTwoFaceGNSMatrixCoefficient f) =
        Complex.re (zetaPrimeTwoFaceGNSMatrixCoefficient f)) ↔
      Complex.re (zetaCompletedPrimeTwoFaceGNSMatrixCoefficient f) = 0 := by
  constructor
  · intro hmatrix
    calc
      Complex.re (zetaCompletedPrimeTwoFaceGNSMatrixCoefficient f) =
          Complex.re (zetaPrimeTwoFaceGNSMatrixCoefficient f) := by
        exact hmatrix
      _ = 0 := by
        exact zetaPrimeTwoFaceGNSMatrixCoefficient_re_eq_zero_of_completedLowerWeightNormalization
          f
  · intro hzero
    calc
      Complex.re (zetaCompletedPrimeTwoFaceGNSMatrixCoefficient f) = 0 := by
        exact hzero
      _ = Complex.re (zetaPrimeTwoFaceGNSMatrixCoefficient f) := by
        exact
          (zetaPrimeTwoFaceGNSMatrixCoefficient_re_eq_zero_of_completedLowerWeightNormalization
            f).symm

/-- The completed two-face GNS real coefficient is definitionally the real
part of the negated completed prime-power spectral sample on the
autocorrelation probe. -/
theorem completedPrimeTwoFaceGNSMatrixCoefficient_re_eq_neg_spectralSample
    (f : ZetaAdmissibleFunction) :
    Complex.re (zetaCompletedPrimeTwoFaceGNSMatrixCoefficient f) =
      Complex.re
        (-(zetaCompletedExplicitFormulaPrimePowerSpectralSampleContribution
            (convolutionAutocorrelation f))) := by
  rfl

/-- A zero completed prime-power spectral sample kills the completed two-face
GNS real coefficient. -/
theorem completedPrimeTwoFaceGNSMatrixCoefficient_re_eq_zero_of_spectralSample_eq_zero
    (f : ZetaAdmissibleFunction)
    (hsample :
      zetaCompletedExplicitFormulaPrimePowerSpectralSampleContribution
          (convolutionAutocorrelation f) = 0) :
    Complex.re (zetaCompletedPrimeTwoFaceGNSMatrixCoefficient f) = 0 := by
  have hnegSample :
      Complex.re
          (-(zetaCompletedExplicitFormulaPrimePowerSpectralSampleContribution
              (convolutionAutocorrelation f))) =
        Complex.re (-0 : ℂ) := by
    exact congrArg (fun z : ℂ => Complex.re (-z)) hsample
  have hnegZeroRe :
      Complex.re (-0 : ℂ) = Complex.re (0 : ℂ) := by
    exact congrArg Complex.re (neg_zero : -(0 : ℂ) = 0)
  have hzeroRe :
      Complex.re (0 : ℂ) = 0 := by
    exact Complex.zero_re
  exact
    Eq.trans
      (completedPrimeTwoFaceGNSMatrixCoefficient_re_eq_neg_spectralSample f)
      (Eq.trans hnegSample (Eq.trans hnegZeroRe hzeroRe))

/-- Completed autocorrelation prime two-face boundary cancellation.

This is the upstream scalar sink for diagonal-debt removal: the completed spectral
two-face/GNS matrix coefficient has zero real scalar on autocorrelation probes. -/
theorem completedPrimeTwoFaceGNSMatrixCoefficient_re_eq_zero_boundaryCancellation
    (f : ZetaAdmissibleFunction)
    (hledger : ZetaCompletedPrimePowerAutocorrelationLedgerCancellation f)
    (horiented :
      Summable
        (fun ι : ZetaPrimePowerIndex =>
          zetaCompletedPrimePowerAutocorrelationOrientedCrossCoordinate ι f)) :
    Complex.re (zetaCompletedPrimeTwoFaceGNSMatrixCoefficient f) = 0 := by
  have hsample :
      zetaCompletedExplicitFormulaPrimePowerSpectralSampleContribution
          (convolutionAutocorrelation f) = 0 :=
    zetaCompletedExplicitFormulaPrimePowerSpectralSampleContribution_convolutionAutocorrelation_eq_zero_contourTomography
      f hledger horiented
  exact
    completedPrimeTwoFaceGNSMatrixCoefficient_re_eq_zero_of_spectralSample_eq_zero
      f hsample

/-- Boundary cancellation gives the completed/raw two-face real-coefficient comparison. -/
theorem completedPrimeTwoFaceGNSMatrixCoefficient_re_eq_finite_boundaryCancellation
    (f : ZetaAdmissibleFunction)
    (hledger : ZetaCompletedPrimePowerAutocorrelationLedgerCancellation f)
    (horiented :
      Summable
        (fun ι : ZetaPrimePowerIndex =>
          zetaCompletedPrimePowerAutocorrelationOrientedCrossCoordinate ι f)) :
    Complex.re (zetaCompletedPrimeTwoFaceGNSMatrixCoefficient f) =
      Complex.re (zetaPrimeTwoFaceGNSMatrixCoefficient f) := by
  calc
    Complex.re (zetaCompletedPrimeTwoFaceGNSMatrixCoefficient f) = 0 := by
      exact completedPrimeTwoFaceGNSMatrixCoefficient_re_eq_zero_boundaryCancellation
        f hledger horiented
    _ = Complex.re (zetaPrimeTwoFaceGNSMatrixCoefficient f) := by
      exact
        (zetaPrimeTwoFaceGNSMatrixCoefficient_re_eq_zero_of_completedLowerWeightNormalization
          f).symm

/-- The completed diagonal prime-debt real scalar vanishes by upstream two-face boundary
cancellation. -/
theorem zetaCompletedPrimeDefectKernelDiagonalDebt_re_eq_zero_boundaryCancellation
    (f : ZetaAdmissibleFunction)
    (hledger : ZetaCompletedPrimePowerAutocorrelationLedgerCancellation f)
    (horiented :
      Summable
        (fun ι : ZetaPrimePowerIndex =>
          zetaCompletedPrimePowerAutocorrelationOrientedCrossCoordinate ι f)) :
    Complex.re (zetaCompletedPrimeDefectKernelDiagonalDebt f) = 0 := by
  exact
    zetaCompletedPrimeDefectKernelDiagonalDebt_re_eq_zero_of_twoFace_re_eq
      f
      (completedPrimeTwoFaceGNSMatrixCoefficient_re_eq_finite_boundaryCancellation
        f hledger horiented)

/-- Under the current finite-display lower-weight normalization, the completed
off-diagonal/positive-channel comparison is equivalent to vanishing of the completed two-face
real coefficient. -/
theorem completedPrimeOffDiagonalChannel_eq_positiveChannel_iff_completedPrimeTwoFaceGNSMatrixCoefficient_re_eq_zero
    (f : ZetaAdmissibleFunction)
    (D : CompletedFiniteWindowPrimeDistributionReconstruction f) :
    completedPrimeOffDiagonalChannel f =
        completedPrimeDefectKernelPositiveChannel f ↔
      Complex.re (zetaCompletedPrimeTwoFaceGNSMatrixCoefficient f) = 0 := by
  exact
    (completedPrimeOffDiagonalChannel_eq_positiveChannel_iff_matrixComparison
      f D).trans
      (matrixComparison_iff_completedPrimeTwoFaceGNSMatrixCoefficient_re_eq_zero f)

/-- Summed-transport version of the lower-weight normalized two-face vanishing criterion for
the completed off-diagonal/positive-channel comparison. -/
theorem completedPrimeOffDiagonalChannel_eq_positiveChannel_iff_completedPrimeTwoFaceGNSMatrixCoefficient_re_eq_zero_summedTransport
    (f : ZetaAdmissibleFunction)
    (D : CompletedSummedPrimeContourTimeTransport f) :
    completedPrimeOffDiagonalChannel f =
        completedPrimeDefectKernelPositiveChannel f ↔
      Complex.re (zetaCompletedPrimeTwoFaceGNSMatrixCoefficient f) = 0 := by
  exact
    (completedPrimeOffDiagonalChannel_eq_positiveChannel_iff_matrixComparison_of_summedTransport
      f D).trans
      (matrixComparison_iff_completedPrimeTwoFaceGNSMatrixCoefficient_re_eq_zero f)

end ZetaAdmissibleFunction

end
end LFunctions
end Boundary
