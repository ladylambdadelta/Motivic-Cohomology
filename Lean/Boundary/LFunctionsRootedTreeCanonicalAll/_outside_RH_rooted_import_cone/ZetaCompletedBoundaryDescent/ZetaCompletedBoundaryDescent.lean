import Boundary.LFunctionsRootedTreeCanonicalAll.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaCompletedHilbertSource.ZetaCompletedWeightStream.ZetaCompletedFinitePart.ZetaCompletedSquareLedger.ZetaCompletedSquareLedger
import Boundary.LFunctionsRootedTreeCanonicalAll.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaCompletedHilbertSource.ZetaCompletedWeightStream.ZetaCompletedFinitePart.ZetaCompletedFinitePart
import Boundary.LFunctionsRootedTreeCanonicalAll.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaCompletedHilbertSource.ZetaCompletedWeightStream.ZetaCompletedWeightStream
import Boundary.LFunctionsRootedTreeCanonicalAll.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaCompletedHilbertSource.ZetaCompletedHilbertSource
import Boundary.LFunctionsRootedTreeCanonicalAll.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaZeroTail.ZetaPrimeRapidPower.ZetaPrimeTwoFaceCoordinates.ZetaCompletedPositiveBoundary.ZetaCompletedLowerWeight.ZetaCompletedLowerWeight
import Boundary.LFunctionsRootedTreeCanonicalAll.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaZeroTail.ZetaPrimeRapidPower.ZetaPrimeTwoFaceCoordinates.ZetaCompletedPositiveBoundary.ZetaCompletedPositiveBoundary
import Boundary.LFunctionsRootedTreeCanonicalAll._outside_RH_rooted_import_cone.Completion.ZetaCompletedBoundaryDescent.ZetaPrimeTwoFaceTomography.ZetaPrimeTwoFaceTomography
import Boundary.LFunctionsRootedTreeCanonicalAll.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaTransformCalculus.ZetaTransformCalculusBase.ZetaTransformCalculusBase
import Boundary.LFunctionsRootedTreeCanonicalAll.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaAdmissibleSpectralInterpolation.ZetaAdmissiblePaleyWiener.ZetaTransformCalculusWeighted.ZetaTransformCalculusWeighted
import Boundary.LFunctionsRootedTreeCanonicalAll.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaCompletedHilbertSource.ZetaPacketComparison.ZetaPacketComparison
import Boundary.LFunctionsRootedTreeCanonicalAll.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaCompletedHilbertSource.ZetaHermitianPacket.ZetaHermitianPacket
import Boundary.LFunctionsRootedTreeCanonicalAll.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaExplicitFormulaComplexAnalysis
import Boundary.LFunctionsRootedTreeCanonicalAll.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaCompletedHilbertSource.ZetaCompletedWeightStream.ZetaCompletedFinitePart.ZetaPrimeDistributionTransport.ZetaPrimeDistributionTransport
import Boundary.LFunctionsRootedTreeCanonicalAll.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaZeroTail.ZetaPrimeRapidPower.ZetaPrimeTwoFaceCoordinates.ZetaPrimeContourTomography.ZetaPrimeContourTomography

/-!
# Boundary completed-channel descent

This file owns the concrete descent and compatibility statements for the
completed explicit-formula boundary channel.  It deliberately uses named
channel definitions and named theorems rather than an abstract prerequisite
record.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open Filter
open scoped Topology

namespace ZetaAdmissibleFunction

/-- Prime-channel tomography for the canonical positive boundary source.

The reduced time-side prime coordinate reconstructs the two-face/GNS cross term.  It is not
the positive defect square before lower-weight diagonal-debt transport. -/
theorem completedPositiveBoundary_primeTimeChannel_re_eq_twoFaceMatrixCoefficient
    (f : ZetaAdmissibleFunction) :
    Complex.re (primeBoundaryChannel (convolutionPair f f)) =
      Complex.re (zetaCompletedPrimeTwoFaceGNSBoundaryCoefficient f) := by
  have hchannel :
      Complex.re (primeBoundaryChannel (convolutionPair f f)) =
        completedPrimeTimeDistributionPairing (convolutionAutocorrelation f) :=
    primeBoundaryChannel_convolutionPair_re_eq_timeDistributionPairing f
  have hcontour :
      completedPrimeTimeDistributionPairing (convolutionAutocorrelation f) =
        Complex.re (zetaCompletedPrimeTwoFaceGNSBoundaryCoefficient f) :=
    completedPrimeTimeDistributionPairing_convolutionAutocorrelation_eq_completedTwoFace_re
      f
  exact hchannel.trans hcontour

/-- Archimedean-channel tomography for the canonical positive boundary source. -/
theorem completedPositiveBoundary_archimedeanTimeChannel_re_eq_packetGram
    (f : ZetaAdmissibleFunction) :
    Complex.re (archimedeanBoundaryChannel (convolutionPair f f)) =
      ZetaHermitianPacketEnsemble.archimedeanPacketGram
        (zetaCompletedHermitianBoundaryDefect f) := by
  have hpair :
      convolutionPair f f = convolutionAutocorrelation f :=
    convolutionPair_self f
  have hchannel :
      archimedeanBoundaryChannel (convolutionAutocorrelation f) =
        zetaCompletedExplicitFormulaArchimedeanConvolutionContribution f :=
    archimedeanBoundaryChannel_convolutionAutocorrelation_eq_archimedeanConvolutionContribution
      f
  have hgram :
      Complex.re
          (zetaCompletedExplicitFormulaArchimedeanConvolutionContribution f) =
        ZetaHermitianPacketEnsemble.archimedeanPacketGram
          (zetaCompletedHermitianBoundaryDefect f) :=
    zetaCompletedExplicitFormulaArchimedeanConvolutionContribution_re_eq_archimedeanPacketGram
      f
  exact
    (congrArg
      (fun g : ZetaAdmissibleFunction =>
        Complex.re (archimedeanBoundaryChannel g))
      hpair).trans
      ((congrArg Complex.re hchannel).trans hgram)

/-- The residual completion channel vanishes on the canonical positive boundary source. -/
theorem completedPositiveBoundary_completionTimeChannel_re_eq_zero
    (f : ZetaAdmissibleFunction) :
    Complex.re (completionBoundaryChannel (convolutionPair f f)) = 0 := by
  unfold completionBoundaryChannel
  exact Complex.zero_re

/-- The correction coordinate in the time-side Hilbert pairing is the correction packet Gram
of the completed Hermitian boundary defect. -/
theorem completedPositiveBoundary_correctionCoordinate_sq_eq_packetGram
    (f : ZetaAdmissibleFunction) :
    zetaCompletionCorrectionPacketCoordinate *
        zetaCompletionCorrectionPacketCoordinate =
      ZetaHermitianPacketEnsemble.correctionPacketGram
        (zetaCompletedHermitianBoundaryDefect f) := by
  exact
    (zetaCompletedHermitianBoundaryDefect_correctionPacketGram_eq_coordinate_sq
      f).symm

/-- Channel reconstruction for the reduced time-side pairing on the canonical positive
boundary source.

The reduced channel has prime, archimedean, and residual completion faces.  Prime and
archimedean are reconstructed by their channel tomography lemmas; completion vanishes in the
current completed normalization. -/
theorem completedPositiveBoundary_reducedTimeChannel_re_eq_twoFace
    (f : ZetaAdmissibleFunction) :
    Complex.re (completedBoundaryReducedChannel (convolutionPair f f)) =
      Complex.re (zetaCompletedPrimeTwoFaceGNSBoundaryCoefficient f) +
        ZetaHermitianPacketEnsemble.archimedeanPacketGram
          (zetaCompletedHermitianBoundaryDefect f) := by
  have hprime :
      Complex.re (primeBoundaryChannel (convolutionPair f f)) =
        Complex.re (zetaCompletedPrimeTwoFaceGNSBoundaryCoefficient f) :=
    completedPositiveBoundary_primeTimeChannel_re_eq_twoFaceMatrixCoefficient f
  have harch :
      Complex.re (archimedeanBoundaryChannel (convolutionPair f f)) =
        ZetaHermitianPacketEnsemble.archimedeanPacketGram
          (zetaCompletedHermitianBoundaryDefect f) :=
    completedPositiveBoundary_archimedeanTimeChannel_re_eq_packetGram f
  have hcompletion :
      Complex.re (completionBoundaryChannel (convolutionPair f f)) = 0 :=
    completedPositiveBoundary_completionTimeChannel_re_eq_zero f
  unfold completedBoundaryReducedChannel
  let P : ℂ := primeBoundaryChannel (convolutionPair f f)
  let A : ℂ := archimedeanBoundaryChannel (convolutionPair f f)
  let C : ℂ := completionBoundaryChannel (convolutionPair f f)
  change Complex.re (P + A + C) =
    Complex.re (zetaCompletedPrimeTwoFaceGNSBoundaryCoefficient f) +
      ZetaHermitianPacketEnsemble.archimedeanPacketGram
        (zetaCompletedHermitianBoundaryDefect f)
  calc
    Complex.re (P + A + C) =
        Complex.re (P + A) + Complex.re C := by
      exact Complex.add_re (P + A) C
    _ = (Complex.re P + Complex.re A) + Complex.re C := by
      exact congrArg
        (fun x : ℝ => x + Complex.re C)
        (Complex.add_re P A)
    _ = (Complex.re P + Complex.re A) + 0 := by
      exact congrArg
        (fun x : ℝ => (Complex.re P + Complex.re A) + x)
        hcompletion
    _ = Complex.re P + Complex.re A := by
      exact add_zero (Complex.re P + Complex.re A)
    _ =
        Complex.re (zetaCompletedPrimeTwoFaceGNSBoundaryCoefficient f) +
          ZetaHermitianPacketEnsemble.archimedeanPacketGram
            (zetaCompletedHermitianBoundaryDefect f) := by
      exact congrArg₂ HAdd.hAdd hprime harch

/-- Scalar reconstruction for the canonical positive boundary source before quotient
wrapping. -/
theorem completedPositiveBoundary_timePairingScalar_eq_twoFaceScalar
    (f : ZetaAdmissibleFunction) :
    completedBoundaryTimePairingScalar
        (completedPositiveBoundaryOrderedHeartClass f) =
      Complex.re (zetaCompletedPrimeTwoFaceGNSBoundaryCoefficient f) +
        ZetaHermitianPacketEnsemble.archimedeanPacketGram
          (zetaCompletedHermitianBoundaryDefect f) +
        ZetaHermitianPacketEnsemble.correctionPacketGram
          (zetaCompletedHermitianBoundaryDefect f) := by
  have hreduced :
      Complex.re (completedBoundaryReducedChannel (convolutionPair f f)) =
        Complex.re (zetaCompletedPrimeTwoFaceGNSBoundaryCoefficient f) +
          ZetaHermitianPacketEnsemble.archimedeanPacketGram
            (zetaCompletedHermitianBoundaryDefect f) :=
    completedPositiveBoundary_reducedTimeChannel_re_eq_twoFace f
  have hcorr :
      zetaCompletionCorrectionPacketCoordinate *
          zetaCompletionCorrectionPacketCoordinate =
        ZetaHermitianPacketEnsemble.correctionPacketGram
          (zetaCompletedHermitianBoundaryDefect f) :=
    completedPositiveBoundary_correctionCoordinate_sq_eq_packetGram f
  unfold completedBoundaryTimePairingScalar
  unfold completedPositiveBoundaryOrderedHeartClass
  unfold completedBoundaryHilbertPairing
  unfold completedBoundaryHilbertSource
  calc
    Complex.re (completedBoundaryReducedChannel (convolutionPair f f)) +
        zetaCompletionCorrectionPacketCoordinate *
          zetaCompletionCorrectionPacketCoordinate =
        (Complex.re (zetaCompletedPrimeTwoFaceGNSBoundaryCoefficient f) +
            ZetaHermitianPacketEnsemble.archimedeanPacketGram
              (zetaCompletedHermitianBoundaryDefect f)) +
          zetaCompletionCorrectionPacketCoordinate *
            zetaCompletionCorrectionPacketCoordinate := by
      exact congrArg
        (fun x : ℝ =>
          x + zetaCompletionCorrectionPacketCoordinate *
            zetaCompletionCorrectionPacketCoordinate)
        hreduced
    _ =
        (Complex.re (zetaCompletedPrimeTwoFaceGNSBoundaryCoefficient f) +
            ZetaHermitianPacketEnsemble.archimedeanPacketGram
              (zetaCompletedHermitianBoundaryDefect f)) +
          ZetaHermitianPacketEnsemble.correctionPacketGram
            (zetaCompletedHermitianBoundaryDefect f) := by
      exact congrArg
        (fun x : ℝ =>
          (Complex.re (zetaCompletedPrimeTwoFaceGNSBoundaryCoefficient f) +
            ZetaHermitianPacketEnsemble.archimedeanPacketGram
              (zetaCompletedHermitianBoundaryDefect f)) + x)
        hcorr
    _ =
        Complex.re (zetaCompletedPrimeTwoFaceGNSBoundaryCoefficient f) +
          ZetaHermitianPacketEnsemble.archimedeanPacketGram
            (zetaCompletedHermitianBoundaryDefect f) +
          ZetaHermitianPacketEnsemble.correctionPacketGram
            (zetaCompletedHermitianBoundaryDefect f) := by
      rfl

/-- The ordered-heart scalar of the canonical positive boundary source unfolds to the
completed positive defect-kernel scalar. -/
theorem completedPositiveBoundary_orderedHeartScalar_eq_positiveDefectScalar
    (f : ZetaAdmissibleFunction) :
    completedOrderedHeartScalar
        (completedPositiveBoundaryOrderedHeartClass f) =
      Complex.re (zetaCompletedPrimeDefectKernelPositiveForm f) +
        ZetaHermitianPacketEnsemble.archimedeanPacketGram
          (zetaCompletedHermitianBoundaryDefect f) +
        ZetaHermitianPacketEnsemble.correctionPacketGram
          (zetaCompletedHermitianBoundaryDefect f) := by
  have hsource :
      completedOrderedHeartScalar
          (completedPositiveBoundaryOrderedHeartClass f) =
        zetaCompletedGNSPositiveBoundaryPresentationScalar f := by
    unfold completedOrderedHeartScalar
    unfold completedPositiveBoundaryOrderedHeartClass
    exact completedBoundaryHermitianGNSScalar_source_eq_positivePresentationScalar f
  have hnormal :
      zetaCompletedGNSPositiveBoundaryPresentationScalar f =
        Complex.re (zetaCompletedPrimeDefectKernelPositiveForm f) +
          ZetaHermitianPacketEnsemble.archimedeanPacketGram
            (zetaCompletedHermitianBoundaryDefect f) +
          ZetaHermitianPacketEnsemble.correctionPacketGram
            (zetaCompletedHermitianBoundaryDefect f) :=
    zetaCompletedGNSPositiveBoundaryPresentationScalar_eq_primeDefect_add_archimedean_add_correction
      f
  exact hsource.trans hnormal

/-- The ordered-heart positive defect scalar differs from the raw two-face time scalar by
the completed prime diagonal debt.

This is the concrete weight-triangular calculation.  The diagonal debt must be absorbed by
the lower-weight radical before one can identify the raw time scalar with the ordered-heart
positive scalar. -/
theorem completedPositiveBoundary_orderedHeartScalar_eq_timePairingScalar_add_primeDiagonalDebt
    (f : ZetaAdmissibleFunction) :
    completedOrderedHeartScalar
        (completedPositiveBoundaryOrderedHeartClass f) =
      completedBoundaryTimePairingScalar
          (completedPositiveBoundaryOrderedHeartClass f) +
        Complex.re (zetaCompletedPrimeDefectKernelDiagonalDebt f) := by
  have htime :
      completedBoundaryTimePairingScalar
          (completedPositiveBoundaryOrderedHeartClass f) =
        Complex.re (zetaCompletedPrimeTwoFaceGNSBoundaryCoefficient f) +
          ZetaHermitianPacketEnsemble.archimedeanPacketGram
            (zetaCompletedHermitianBoundaryDefect f) +
          ZetaHermitianPacketEnsemble.correctionPacketGram
            (zetaCompletedHermitianBoundaryDefect f) :=
    completedPositiveBoundary_timePairingScalar_eq_twoFaceScalar f
  have hordered :
      completedOrderedHeartScalar
          (completedPositiveBoundaryOrderedHeartClass f) =
        Complex.re (zetaCompletedPrimeDefectKernelPositiveForm f) +
          ZetaHermitianPacketEnsemble.archimedeanPacketGram
            (zetaCompletedHermitianBoundaryDefect f) +
          ZetaHermitianPacketEnsemble.correctionPacketGram
            (zetaCompletedHermitianBoundaryDefect f) :=
    completedPositiveBoundary_orderedHeartScalar_eq_positiveDefectScalar f
  have hprime :
      zetaCompletedPrimeDefectKernelPositiveForm f =
        zetaCompletedPrimeDefectKernelDiagonalDebt f +
          zetaCompletedPrimeTwoFaceGNSBoundaryCoefficient f :=
    zetaCompletedPrimeDefectKernelPositiveForm_eq_diagonalDebt_add_boundaryCoefficient
      f
  let B : ℝ := Complex.re (zetaCompletedPrimeTwoFaceGNSBoundaryCoefficient f)
  let D : ℝ := Complex.re (zetaCompletedPrimeDefectKernelDiagonalDebt f)
  let A : ℝ :=
    ZetaHermitianPacketEnsemble.archimedeanPacketGram
      (zetaCompletedHermitianBoundaryDefect f)
  let C : ℝ :=
    ZetaHermitianPacketEnsemble.correctionPacketGram
      (zetaCompletedHermitianBoundaryDefect f)
  have hprime_re :
      Complex.re (zetaCompletedPrimeDefectKernelPositiveForm f) = D + B := by
    calc
      Complex.re (zetaCompletedPrimeDefectKernelPositiveForm f) =
          Complex.re
            (zetaCompletedPrimeDefectKernelDiagonalDebt f +
              zetaCompletedPrimeTwoFaceGNSBoundaryCoefficient f) := by
        exact congrArg Complex.re hprime
      _ =
          Complex.re (zetaCompletedPrimeDefectKernelDiagonalDebt f) +
            Complex.re (zetaCompletedPrimeTwoFaceGNSBoundaryCoefficient f) := by
        exact Complex.add_re
          (zetaCompletedPrimeDefectKernelDiagonalDebt f)
          (zetaCompletedPrimeTwoFaceGNSBoundaryCoefficient f)
      _ = D + B := by
        rfl
  calc
    completedOrderedHeartScalar
        (completedPositiveBoundaryOrderedHeartClass f) =
        Complex.re (zetaCompletedPrimeDefectKernelPositiveForm f) + A + C := by
      exact hordered
    _ = (D + B) + A + C := by
      exact congrArg (fun x : ℝ => x + A + C) hprime_re
    _ = (B + A + C) + D := by
      calc
        (D + B) + A + C = (D + (B + A)) + C := by
          exact congrArg (fun x : ℝ => x + C) (add_assoc D B A)
        _ = D + ((B + A) + C) := by
          exact add_assoc D (B + A) C
        _ = ((B + A) + C) + D := by
          exact add_comm D ((B + A) + C)
        _ = (B + A + C) + D := by
          rfl
    _ =
        completedBoundaryTimePairingScalar
            (completedPositiveBoundaryOrderedHeartClass f) + D := by
      exact congrArg (fun x : ℝ => x + D) htime.symm

/-- Weight-triangular transport identifies the reduced time-side scalar plus diagonal debt
with its completed ordered-heart scalar.

This is the corrected owner scalar transport theorem before quotienting the diagonal debt
through the lower-weight radical. -/
theorem completedPositiveBoundaryTimePairingScalar_add_primeDiagonalDebt_eq_orderedHeartScalar
    (f : ZetaAdmissibleFunction) :
    completedBoundaryTimePairingScalar
        (completedPositiveBoundaryOrderedHeartClass f) +
        Complex.re (zetaCompletedPrimeDefectKernelDiagonalDebt f) =
      completedOrderedHeartScalar
        (completedPositiveBoundaryOrderedHeartClass f) := by
  exact
    (completedPositiveBoundary_orderedHeartScalar_eq_timePairingScalar_add_primeDiagonalDebt
      f).symm

/-- Completed lower-weight reconstruction with explicit diagonal debt transports the
completed two-face time scalar to the completed positive defect-kernel scalar.

This is the remaining top-level holographic reconstruction claim after the prime support
upgrade: it is not an algebraic identity between the two prime channels, but the
ordered-heart/lower-weight transport identifying their completed scalar realizations after
the diagonal debt has been made visible. -/
theorem completedPositiveBoundary_twoFaceScalar_add_primeDiagonalDebt_eq_positiveDefectScalar
    (f : ZetaAdmissibleFunction) :
    (Complex.re (zetaCompletedPrimeTwoFaceGNSBoundaryCoefficient f) +
        ZetaHermitianPacketEnsemble.archimedeanPacketGram
          (zetaCompletedHermitianBoundaryDefect f) +
        ZetaHermitianPacketEnsemble.correctionPacketGram
          (zetaCompletedHermitianBoundaryDefect f)) +
        Complex.re (zetaCompletedPrimeDefectKernelDiagonalDebt f) =
      Complex.re (zetaCompletedPrimeDefectKernelPositiveForm f) +
        ZetaHermitianPacketEnsemble.archimedeanPacketGram
          (zetaCompletedHermitianBoundaryDefect f) +
        ZetaHermitianPacketEnsemble.correctionPacketGram
          (zetaCompletedHermitianBoundaryDefect f) := by
  have htime :
      completedBoundaryTimePairingScalar
          (completedPositiveBoundaryOrderedHeartClass f) =
        Complex.re (zetaCompletedPrimeTwoFaceGNSBoundaryCoefficient f) +
          ZetaHermitianPacketEnsemble.archimedeanPacketGram
            (zetaCompletedHermitianBoundaryDefect f) +
          ZetaHermitianPacketEnsemble.correctionPacketGram
            (zetaCompletedHermitianBoundaryDefect f) :=
    completedPositiveBoundary_timePairingScalar_eq_twoFaceScalar f
  have htransport_add :
      completedBoundaryTimePairingScalar
          (completedPositiveBoundaryOrderedHeartClass f) +
          Complex.re (zetaCompletedPrimeDefectKernelDiagonalDebt f) =
        completedOrderedHeartScalar
          (completedPositiveBoundaryOrderedHeartClass f) :=
    completedPositiveBoundaryTimePairingScalar_add_primeDiagonalDebt_eq_orderedHeartScalar
      f
  have hordered :
      completedOrderedHeartScalar
          (completedPositiveBoundaryOrderedHeartClass f) =
        Complex.re (zetaCompletedPrimeDefectKernelPositiveForm f) +
          ZetaHermitianPacketEnsemble.archimedeanPacketGram
            (zetaCompletedHermitianBoundaryDefect f) +
          ZetaHermitianPacketEnsemble.correctionPacketGram
            (zetaCompletedHermitianBoundaryDefect f) :=
    completedPositiveBoundary_orderedHeartScalar_eq_positiveDefectScalar f
  have hleft :
      (Complex.re (zetaCompletedPrimeTwoFaceGNSBoundaryCoefficient f) +
          ZetaHermitianPacketEnsemble.archimedeanPacketGram
            (zetaCompletedHermitianBoundaryDefect f) +
          ZetaHermitianPacketEnsemble.correctionPacketGram
            (zetaCompletedHermitianBoundaryDefect f)) +
          Complex.re (zetaCompletedPrimeDefectKernelDiagonalDebt f) =
        completedBoundaryTimePairingScalar
            (completedPositiveBoundaryOrderedHeartClass f) +
          Complex.re (zetaCompletedPrimeDefectKernelDiagonalDebt f) :=
    congrArg
      (fun x : ℝ =>
        x + Complex.re (zetaCompletedPrimeDefectKernelDiagonalDebt f))
      htime.symm
  exact hleft.trans (htransport_add.trans hordered)

/-- The positive-boundary representative's time-pairing scalar plus prime diagonal debt is
its ordered-heart scalar.

This is the owner quotient-realization assertion for the positive GNS source: the reduced
time-side pairing reaches the completed ordered-heart GNS scalar after the prime diagonal
debt has been made explicit. -/
theorem completedPositiveBoundaryTimePairingScalar_add_primeDiagonalDebt_eq_orderedHeartScalar_ownerRealization
    (f : ZetaAdmissibleFunction) :
    completedBoundaryTimePairingScalar
        (completedPositiveBoundaryOrderedHeartClass f) +
        Complex.re (zetaCompletedPrimeDefectKernelDiagonalDebt f) =
      completedOrderedHeartScalar
        (completedPositiveBoundaryOrderedHeartClass f) := by
  exact completedPositiveBoundaryTimePairingScalar_add_primeDiagonalDebt_eq_orderedHeartScalar
    f

/-- The finite-part representative's time-pairing scalar plus prime diagonal debt is its
ordered-heart scalar.

This is the representative-level quotient-realization assertion.  It is intentionally placed
before the quotient-class scalar wrapper so downstream lower-weight transport cannot prove it
by circularly reusing the wrapper. -/
theorem completedFinitePartBoundaryTimePairingScalar_add_primeDiagonalDebt_eq_orderedHeartScalar_by_quotientRealization
    (f : ZetaAdmissibleFunction) :
    completedBoundaryTimePairingScalar
        (completedFinitePartBoundaryOrderedHeartClass f) +
        Complex.re (zetaCompletedPrimeDefectKernelDiagonalDebt f) =
      completedOrderedHeartScalar
        (completedFinitePartBoundaryOrderedHeartClass f) := by
  have hclass :
      completedFinitePartBoundaryOrderedHeartClass f =
        completedPositiveBoundaryOrderedHeartClass f :=
    completedFinitePartBoundaryOrderedHeartClass_eq_positiveBoundary f
  have htime :
      completedBoundaryTimePairingScalar
          (completedFinitePartBoundaryOrderedHeartClass f) =
        completedBoundaryTimePairingScalar
          (completedPositiveBoundaryOrderedHeartClass f) :=
    congrArg completedBoundaryTimePairingScalar hclass
  have hpositive :
      completedBoundaryTimePairingScalar
          (completedPositiveBoundaryOrderedHeartClass f) +
          Complex.re (zetaCompletedPrimeDefectKernelDiagonalDebt f) =
        completedOrderedHeartScalar
          (completedPositiveBoundaryOrderedHeartClass f) :=
    completedPositiveBoundaryTimePairingScalar_add_primeDiagonalDebt_eq_orderedHeartScalar_ownerRealization
      f
  have hordered :
      completedOrderedHeartScalar
          (completedPositiveBoundaryOrderedHeartClass f) =
        completedOrderedHeartScalar
          (completedFinitePartBoundaryOrderedHeartClass f) :=
    congrArg completedOrderedHeartScalar hclass.symm
  have htime_debt :
      completedBoundaryTimePairingScalar
          (completedFinitePartBoundaryOrderedHeartClass f) +
          Complex.re (zetaCompletedPrimeDefectKernelDiagonalDebt f) =
        completedBoundaryTimePairingScalar
          (completedPositiveBoundaryOrderedHeartClass f) +
          Complex.re (zetaCompletedPrimeDefectKernelDiagonalDebt f) :=
    congrArg
      (fun x : ℝ =>
        x + Complex.re (zetaCompletedPrimeDefectKernelDiagonalDebt f))
      htime
  exact htime_debt.trans (hpositive.trans hordered)

/-- The finite-part time-pairing scalar plus prime diagonal debt descends to the finite-part
ordered-heart quotient scalar. -/
theorem completedFinitePartBoundaryTimePairingScalar_add_primeDiagonalDebt_eq_orderedHeartQuotientScalar_by_quotientRealization
    (f : ZetaAdmissibleFunction) :
    completedBoundaryTimePairingScalar
        (completedFinitePartBoundaryOrderedHeartClass f) +
        Complex.re (zetaCompletedPrimeDefectKernelDiagonalDebt f) =
      completedBoundaryOrderedHeartClassScalar
        (completedFinitePartBoundaryOrderedHeartQuotientClass f) := by
  have hrepresentative :
      completedBoundaryTimePairingScalar
          (completedFinitePartBoundaryOrderedHeartClass f) +
          Complex.re (zetaCompletedPrimeDefectKernelDiagonalDebt f) =
        completedOrderedHeartScalar
          (completedFinitePartBoundaryOrderedHeartClass f) :=
    completedFinitePartBoundaryTimePairingScalar_add_primeDiagonalDebt_eq_orderedHeartScalar_by_quotientRealization
      f
  have hquotient :
      completedOrderedHeartScalar
          (completedFinitePartBoundaryOrderedHeartClass f) =
        completedBoundaryOrderedHeartClassScalar
          (completedFinitePartBoundaryOrderedHeartQuotientClass f) :=
    (completedFinitePartBoundaryOrderedHeartQuotientScalar_eq_orderedHeartScalar
      f).symm
  exact hrepresentative.trans hquotient

/-- The raw finite-part boundary scalar plus prime diagonal debt descends to the finite-part
ordered-heart quotient scalar.

This is the quotient-realization map for the finite-part representative: the real scalar
defined by the completed time-side boundary channel is the scalar induced by the completed
ordered-heart quotient class after the diagonal debt is made visible. -/
theorem completedFinitePartBoundaryChannel_add_primeDiagonalDebt_eq_orderedHeartQuotientScalar_by_quotientRealization
    (f : ZetaAdmissibleFunction) :
    completedFinitePartBoundaryChannel f +
        Complex.re (zetaCompletedPrimeDefectKernelDiagonalDebt f) =
      completedBoundaryOrderedHeartClassScalar
        (completedFinitePartBoundaryOrderedHeartQuotientClass f) := by
  have htime :
      completedFinitePartBoundaryChannel f =
        completedBoundaryTimePairingScalar
          (completedFinitePartBoundaryOrderedHeartClass f) :=
    completedFinitePartBoundaryChannel_eq_timePairingScalar f
  have hquotient :
      completedBoundaryTimePairingScalar
          (completedFinitePartBoundaryOrderedHeartClass f) +
          Complex.re (zetaCompletedPrimeDefectKernelDiagonalDebt f) =
        completedBoundaryOrderedHeartClassScalar
          (completedFinitePartBoundaryOrderedHeartQuotientClass f) :=
    completedFinitePartBoundaryTimePairingScalar_add_primeDiagonalDebt_eq_orderedHeartQuotientScalar_by_quotientRealization
      f
  have htime_debt :
      completedFinitePartBoundaryChannel f +
          Complex.re (zetaCompletedPrimeDefectKernelDiagonalDebt f) =
        completedBoundaryTimePairingScalar
          (completedFinitePartBoundaryOrderedHeartClass f) +
          Complex.re (zetaCompletedPrimeDefectKernelDiagonalDebt f) :=
    congrArg
      (fun x : ℝ =>
        x + Complex.re (zetaCompletedPrimeDefectKernelDiagonalDebt f))
      htime
  exact htime_debt.trans hquotient

/-- The finite-part ordered-heart quotient scalar is the positive defect-kernel scalar. -/
theorem completedFinitePartBoundaryOrderedHeartQuotientScalar_eq_positiveDefectKernelBoundaryScalar
    (f : ZetaAdmissibleFunction) :
    completedBoundaryOrderedHeartClassScalar
        (completedFinitePartBoundaryOrderedHeartQuotientClass f) =
      completedPositiveDefectKernelBoundaryScalar f := by
  have hquotient :
      completedBoundaryOrderedHeartClassScalar
          (completedFinitePartBoundaryOrderedHeartQuotientClass f) =
        completedRenormalizedDefectKernelBoundaryChannel f :=
    completedFinitePartBoundaryOrderedHeartQuotientScalar_eq_renormalizedDefectKernel
      f
  have hpositive :
      completedRenormalizedDefectKernelBoundaryChannel f =
        completedPositiveDefectKernelBoundaryScalar f :=
    completedRenormalizedDefectKernelBoundaryChannel_eq_positiveDefectKernelBoundaryScalar
      f
  exact hquotient.trans hpositive

/-- Quotient realization identifies the raw time-side scalar plus prime diagonal debt with
the positive defect-kernel ordered-heart scalar. -/
theorem completedRawTimeBoundaryScalar_add_primeDiagonalDebt_eq_positiveDefectKernelBoundaryScalar_by_quotientRealization
    (f : ZetaAdmissibleFunction) :
    completedRawTimeBoundaryScalar f +
        Complex.re (zetaCompletedPrimeDefectKernelDiagonalDebt f) =
      completedPositiveDefectKernelBoundaryScalar f := by
  have hraw :
      completedRawTimeBoundaryScalar f =
        completedFinitePartBoundaryChannel f :=
    completedRawTimeBoundaryScalar_eq_finitePartBoundaryChannel f
  have hquotient :
      completedFinitePartBoundaryChannel f +
          Complex.re (zetaCompletedPrimeDefectKernelDiagonalDebt f) =
        completedBoundaryOrderedHeartClassScalar
          (completedFinitePartBoundaryOrderedHeartQuotientClass f) :=
    completedFinitePartBoundaryChannel_add_primeDiagonalDebt_eq_orderedHeartQuotientScalar_by_quotientRealization
      f
  have hpositive :
      completedBoundaryOrderedHeartClassScalar
          (completedFinitePartBoundaryOrderedHeartQuotientClass f) =
        completedPositiveDefectKernelBoundaryScalar f :=
    completedFinitePartBoundaryOrderedHeartQuotientScalar_eq_positiveDefectKernelBoundaryScalar
      f
  have hraw_debt :
      completedRawTimeBoundaryScalar f +
          Complex.re (zetaCompletedPrimeDefectKernelDiagonalDebt f) =
        completedFinitePartBoundaryChannel f +
          Complex.re (zetaCompletedPrimeDefectKernelDiagonalDebt f) :=
    congrArg
      (fun x : ℝ =>
        x + Complex.re (zetaCompletedPrimeDefectKernelDiagonalDebt f))
      hraw
  exact hraw_debt.trans (hquotient.trans hpositive)

/-- The positive-boundary time-pairing scalar plus prime diagonal debt is the positive
ordered-heart GNS scalar after lower-weight quotient realization. -/
theorem completedPositiveBoundaryTimePairingScalar_add_primeDiagonalDebt_eq_orderedHeartScalar_by_quotientRealization
    (f : ZetaAdmissibleFunction) :
    completedBoundaryTimePairingScalar
        (completedPositiveBoundaryOrderedHeartClass f) +
        Complex.re (zetaCompletedPrimeDefectKernelDiagonalDebt f) =
      completedOrderedHeartScalar
        (completedPositiveBoundaryOrderedHeartClass f) := by
  exact completedPositiveBoundaryTimePairingScalar_add_primeDiagonalDebt_eq_orderedHeartScalar_ownerRealization
    f

/-- Radical absorption identifies the absorbed positive-boundary precone scalar plus prime
diagonal debt with the positive ordered-heart scalar.

This is the genuine lower-weight transport theorem: the absorbed finite representatives
define the same completed scalar as the positive square class because their difference is the
lower-weight radical absorption face. -/
theorem completedPositiveBoundaryPreconeElement_scalar_add_primeDiagonalDebt_eq_orderedHeartScalar_of_radicalAbsorption
    (f : ZetaAdmissibleFunction)
    (habsorption :
      CompletedBoundaryHilbertSource.LowerWeightRadical
        (completedPositiveBoundaryAbsorptionDefectOrderedHeartClass f)) :
    (completedPositiveBoundaryPreconeElement f).scalar +
        Complex.re (zetaCompletedPrimeDefectKernelDiagonalDebt f) =
      completedOrderedHeartScalar
        (completedPositiveBoundaryOrderedHeartClass f) := by
  have hsource :
      (completedPositiveBoundaryPreconeElement f).scalar =
        completedBoundaryTimePairingScalar
          (completedPositiveBoundaryAbsorbedOrderedHeartClass f) :=
    completedPositiveBoundaryPreconeElement_scalar_eq_absorbedOrderedHeartTimePairingScalar
      f
  have habsorbed :
      completedBoundaryTimePairingScalar
          (completedPositiveBoundaryAbsorbedOrderedHeartClass f) =
        completedBoundaryTimePairingScalar
          (completedPositiveBoundaryOrderedHeartClass f) :=
    completedPositiveBoundaryAbsorbedOrderedHeartTimePairingScalar_eq_positiveBoundaryTimePairingScalar
      f habsorption
  have hpositive :
      completedBoundaryTimePairingScalar
          (completedPositiveBoundaryOrderedHeartClass f) +
          Complex.re (zetaCompletedPrimeDefectKernelDiagonalDebt f) =
        completedOrderedHeartScalar
          (completedPositiveBoundaryOrderedHeartClass f) :=
    completedPositiveBoundaryTimePairingScalar_add_primeDiagonalDebt_eq_orderedHeartScalar_by_quotientRealization
      f
  have hsource_debt :
      (completedPositiveBoundaryPreconeElement f).scalar +
          Complex.re (zetaCompletedPrimeDefectKernelDiagonalDebt f) =
        completedBoundaryTimePairingScalar
          (completedPositiveBoundaryAbsorbedOrderedHeartClass f) +
          Complex.re (zetaCompletedPrimeDefectKernelDiagonalDebt f) :=
    congrArg
      (fun x : ℝ =>
        x + Complex.re (zetaCompletedPrimeDefectKernelDiagonalDebt f))
      hsource
  have habsorbed_debt :
      completedBoundaryTimePairingScalar
          (completedPositiveBoundaryAbsorbedOrderedHeartClass f) +
          Complex.re (zetaCompletedPrimeDefectKernelDiagonalDebt f) =
        completedBoundaryTimePairingScalar
          (completedPositiveBoundaryOrderedHeartClass f) +
          Complex.re (zetaCompletedPrimeDefectKernelDiagonalDebt f) :=
    congrArg
      (fun x : ℝ =>
        x + Complex.re (zetaCompletedPrimeDefectKernelDiagonalDebt f))
      habsorbed
  exact hsource_debt.trans (habsorbed_debt.trans hpositive)

/-- The absorbed positive-boundary precone scalar plus prime diagonal debt is the
ordered-heart scalar of its class.

This is the limit-level lower-weight transport assertion: the finite absorbed representatives
converge to the same completed scalar as the positive GNS ordered-heart class.  The proof
belongs to the radical/nullspace transport from finite diagonal-debt absorption to the
completed ordered-heart quotient. -/
theorem completedPositiveBoundaryPreconeElement_scalar_add_primeDiagonalDebt_eq_orderedHeartScalar_by_lowerWeightTriangularTransport
    (f : ZetaAdmissibleFunction) :
    (completedPositiveBoundaryPreconeElement f).scalar +
        Complex.re (zetaCompletedPrimeDefectKernelDiagonalDebt f) =
      completedOrderedHeartScalar
        (completedPositiveBoundaryOrderedHeartClass f) := by
  exact
    completedPositiveBoundaryPreconeElement_scalar_add_primeDiagonalDebt_eq_orderedHeartScalar_of_radicalAbsorption
      f
      (completedPositiveBoundaryPreconeElement_absorptionDefect_lowerWeightRadical f)

/-- The finite-part class and positive-boundary class have the same ordered-heart scalar. -/
theorem completedFinitePartBoundaryOrderedHeartScalar_eq_positiveBoundary
    (f : ZetaAdmissibleFunction) :
    completedOrderedHeartScalar
        (completedPositiveBoundaryOrderedHeartClass f) =
      completedOrderedHeartScalar
        (completedFinitePartBoundaryOrderedHeartClass f) := by
  exact congrArg completedOrderedHeartScalar
    (completedFinitePartBoundaryOrderedHeartClass_eq_positiveBoundary f).symm

/-- Lower-weight triangular transport identifies the time-pairing scalar plus prime diagonal
debt of the finite-part representative with the ordered-heart GNS scalar of the same
completed class.

This is the radical/nullspace payoff theorem.  The finite-part representative is evaluated by
the time-side completed pairing, while the ordered-heart scalar is evaluated by the positive
defect-kernel GNS pairing.  Diagonal-debt absorption says these are the same scalar after
quotienting by the lower-weight radical. -/
theorem completedFinitePartBoundaryTimePairingScalar_add_primeDiagonalDebt_eq_orderedHeartScalar_by_lowerWeightTriangularTransport
    (f : ZetaAdmissibleFunction) :
    completedBoundaryTimePairingScalar
        (completedFinitePartBoundaryOrderedHeartClass f) +
        Complex.re (zetaCompletedPrimeDefectKernelDiagonalDebt f) =
      completedOrderedHeartScalar
        (completedFinitePartBoundaryOrderedHeartClass f) := by
  have htime :
      completedBoundaryTimePairingScalar
          (completedFinitePartBoundaryOrderedHeartClass f) =
        (completedPositiveBoundaryPreconeElement f).scalar :=
    completedFinitePartBoundaryTimePairingScalar_eq_positivePreconeScalar f
  have hprecone :
      (completedPositiveBoundaryPreconeElement f).scalar +
          Complex.re (zetaCompletedPrimeDefectKernelDiagonalDebt f) =
        completedOrderedHeartScalar
          (completedPositiveBoundaryOrderedHeartClass f) :=
    completedPositiveBoundaryPreconeElement_scalar_add_primeDiagonalDebt_eq_orderedHeartScalar_by_lowerWeightTriangularTransport
      f
  have hclass :
      completedOrderedHeartScalar
          (completedPositiveBoundaryOrderedHeartClass f) =
        completedOrderedHeartScalar
          (completedFinitePartBoundaryOrderedHeartClass f) :=
    completedFinitePartBoundaryOrderedHeartScalar_eq_positiveBoundary f
  have htime_debt :
      completedBoundaryTimePairingScalar
          (completedFinitePartBoundaryOrderedHeartClass f) +
          Complex.re (zetaCompletedPrimeDefectKernelDiagonalDebt f) =
        (completedPositiveBoundaryPreconeElement f).scalar +
          Complex.re (zetaCompletedPrimeDefectKernelDiagonalDebt f) :=
    congrArg
      (fun x : ℝ =>
        x + Complex.re (zetaCompletedPrimeDefectKernelDiagonalDebt f))
      htime
  exact htime_debt.trans (hprecone.trans hclass)

/-- The finite-part representative stream shifted by prime diagonal debt converges to the
ordered-heart quotient scalar.

This is the precise tomographic reconstruction burden for the completed finite-part stream:
the finite representatives converge to the time-side boundary scalar, and weight-triangular
transport identifies the scalar after the diagonal debt is made visible. -/
theorem completedBoundaryWeightStream_finitePart_add_primeDiagonalDebt_tendsto_orderedHeartQuotientScalar
    (f : ZetaAdmissibleFunction) :
    Tendsto
      (fun N : ℕ =>
        FiniteBoundaryWeightObject.finitePartRepresentative
          ((completedBoundaryWeightStream f).object N) +
          Complex.re (zetaCompletedPrimeDefectKernelDiagonalDebt f))
      atTop
      (𝓝
        (completedBoundaryOrderedHeartClassScalar
          (completedFinitePartBoundaryOrderedHeartQuotientClass f))) := by
  have hwindow :
      Tendsto
        (fun N : ℕ => finitePartBoundaryWindow N f)
        atTop
        (𝓝 (completedFinitePartBoundaryChannel f)) :=
    finitePartBoundaryWindow_tendsto_completedFinitePartBoundaryChannel f
  have hobject :
      (fun N : ℕ =>
        FiniteBoundaryWeightObject.finitePartRepresentative
          ((completedBoundaryWeightStream f).object N)) =
        (fun N : ℕ => finitePartBoundaryWindow N f) := by
    funext N
    exact finiteBoundaryWeightObject_finitePartRepresentative_eq_finitePartBoundaryWindow
      N f
  have hobject_tendsto_finite :
      Tendsto
        (fun N : ℕ =>
          FiniteBoundaryWeightObject.finitePartRepresentative
            ((completedBoundaryWeightStream f).object N))
        atTop
        (𝓝 (completedFinitePartBoundaryChannel f)) :=
    Eq.subst
      (motive := fun u : ℕ → ℝ =>
        Tendsto u atTop (𝓝 (completedFinitePartBoundaryChannel f)))
      hobject.symm
      hwindow
  have hfinite_to_quotient :
      completedFinitePartBoundaryChannel f +
          Complex.re (zetaCompletedPrimeDefectKernelDiagonalDebt f) =
        completedBoundaryOrderedHeartClassScalar
          (completedFinitePartBoundaryOrderedHeartQuotientClass f) := by
    exact completedFinitePartBoundaryChannel_add_primeDiagonalDebt_eq_orderedHeartQuotientScalar_by_quotientRealization
      f
  have hshifted :
      Tendsto
        (fun N : ℕ =>
          FiniteBoundaryWeightObject.finitePartRepresentative
            ((completedBoundaryWeightStream f).object N) +
            Complex.re (zetaCompletedPrimeDefectKernelDiagonalDebt f))
        atTop
        (𝓝
          (completedFinitePartBoundaryChannel f +
            Complex.re (zetaCompletedPrimeDefectKernelDiagonalDebt f))) :=
    hobject_tendsto_finite.add tendsto_const_nhds
  exact Eq.subst
    (motive := fun x : ℝ =>
      Tendsto
        (fun N : ℕ =>
          FiniteBoundaryWeightObject.finitePartRepresentative
            ((completedBoundaryWeightStream f).object N) +
            Complex.re (zetaCompletedPrimeDefectKernelDiagonalDebt f))
        atTop
        (𝓝 x))
    hfinite_to_quotient
    hshifted

/-- The positive-cone completed boundary weight stream plus prime diagonal debt realizes in
the completed ordered-heart quotient scalar.

This is the stream-level lower-weight projection theorem: finite square representatives and
their lower-weight absorption certificates define the same completed scalar as the ordered
heart quotient class. -/
theorem completedBoundaryWeightStream_scalar_add_primeDiagonalDebt_eq_orderedHeartQuotientScalar_by_positiveCone
    (f : ZetaAdmissibleFunction) :
    (completedBoundaryWeightStream f).scalar +
        Complex.re (zetaCompletedPrimeDefectKernelDiagonalDebt f) =
      completedBoundaryOrderedHeartClassScalar
        (completedFinitePartBoundaryOrderedHeartQuotientClass f) := by
  have hscalar :
      Tendsto
        (fun N : ℕ =>
          FiniteBoundaryWeightObject.finitePartRepresentative
            ((completedBoundaryWeightStream f).object N) +
            Complex.re (zetaCompletedPrimeDefectKernelDiagonalDebt f))
        atTop
        (𝓝
          ((completedBoundaryWeightStream f).scalar +
            Complex.re (zetaCompletedPrimeDefectKernelDiagonalDebt f))) :=
    (completedBoundaryWeightStream f).finitePart_tendsto_scalar.add tendsto_const_nhds
  have hquotient :
      Tendsto
        (fun N : ℕ =>
          FiniteBoundaryWeightObject.finitePartRepresentative
            ((completedBoundaryWeightStream f).object N) +
            Complex.re (zetaCompletedPrimeDefectKernelDiagonalDebt f))
        atTop
        (𝓝
          (completedBoundaryOrderedHeartClassScalar
            (completedFinitePartBoundaryOrderedHeartQuotientClass f))) :=
    completedBoundaryWeightStream_finitePart_add_primeDiagonalDebt_tendsto_orderedHeartQuotientScalar f
  exact tendsto_nhds_unique hscalar hquotient

/-- The completed boundary weight stream scalar plus prime diagonal debt is represented by
the completed renormalized positive defect-kernel channel after projection to the
ordered-heart quotient. -/
theorem completedBoundaryWeightStream_scalar_add_primeDiagonalDebt_eq_renormalizedDefectKernel
    (f : ZetaAdmissibleFunction) :
    (completedBoundaryWeightStream f).scalar +
        Complex.re (zetaCompletedPrimeDefectKernelDiagonalDebt f) =
      completedRenormalizedDefectKernelBoundaryChannel f := by
  have hquotient :
      (completedBoundaryWeightStream f).scalar +
          Complex.re (zetaCompletedPrimeDefectKernelDiagonalDebt f) =
        completedBoundaryOrderedHeartClassScalar
          (completedFinitePartBoundaryOrderedHeartQuotientClass f) :=
    completedBoundaryWeightStream_scalar_add_primeDiagonalDebt_eq_orderedHeartQuotientScalar_by_positiveCone
      f
  have hrenormalized :
      completedBoundaryOrderedHeartClassScalar
          (completedFinitePartBoundaryOrderedHeartQuotientClass f) =
        completedRenormalizedDefectKernelBoundaryChannel f :=
    completedFinitePartBoundaryOrderedHeartQuotientScalar_eq_renormalizedDefectKernel
      f
  exact hquotient.trans hrenormalized

/-- Owner channel-level lower-weight descent: the completed finite-part boundary channel
plus prime diagonal debt is represented by the completed renormalized positive defect-kernel
channel.

This is the channel form of the lower-weight triangular transport theorem. -/
theorem completedFinitePartBoundaryChannel_add_primeDiagonalDebt_eq_renormalizedDefectKernel_ownerDescent
    (f : ZetaAdmissibleFunction) :
    completedFinitePartBoundaryChannel f +
        Complex.re (zetaCompletedPrimeDefectKernelDiagonalDebt f) =
      completedRenormalizedDefectKernelBoundaryChannel f := by
  have hfinite :
      completedFinitePartBoundaryChannel f =
        (completedBoundaryWeightStream f).scalar :=
    (completedBoundaryWeightStream_scalar_eq_completedFinitePartBoundaryChannel f).symm
  have hstream :
      (completedBoundaryWeightStream f).scalar +
          Complex.re (zetaCompletedPrimeDefectKernelDiagonalDebt f) =
        completedRenormalizedDefectKernelBoundaryChannel f :=
    completedBoundaryWeightStream_scalar_add_primeDiagonalDebt_eq_renormalizedDefectKernel f
  have hfinite_debt :
      completedFinitePartBoundaryChannel f +
          Complex.re (zetaCompletedPrimeDefectKernelDiagonalDebt f) =
        (completedBoundaryWeightStream f).scalar +
          Complex.re (zetaCompletedPrimeDefectKernelDiagonalDebt f) :=
    congrArg
      (fun x : ℝ =>
        x + Complex.re (zetaCompletedPrimeDefectKernelDiagonalDebt f))
      hfinite
  exact hfinite_debt.trans hstream

/-- Lower-weight triangular transport identifies the symmetrized two-face representative
plus prime diagonal debt with the positive defect-kernel representative in the completed
ordered-heart scalar.

This is the exact radical-absorption step: the prime two-face cross term is not asserted to
be positive.  Instead, the completed ordered-heart transport replaces it by the positive
defect-square representative after the diagonal debt has been absorbed as lower-weight
radical data. -/
theorem completedSymmetrizedTwoFaceBoundaryScalar_add_primeDiagonalDebt_eq_positiveDefectKernelBoundaryScalar
    (f : ZetaAdmissibleFunction) :
    completedSymmetrizedTwoFaceBoundaryScalar f +
        Complex.re (zetaCompletedPrimeDefectKernelDiagonalDebt f) =
      completedPositiveDefectKernelBoundaryScalar f := by
  have hsymm_to_finite :
      completedSymmetrizedTwoFaceBoundaryScalar f =
        completedFinitePartBoundaryChannel f :=
    (completedFinitePartBoundaryChannel_eq_symmetrizedTwoFaceBoundaryScalar f).symm
  have hfinite_to_time :
      completedFinitePartBoundaryChannel f =
        completedBoundaryTimePairingScalar
          (completedFinitePartBoundaryOrderedHeartClass f) :=
    completedFinitePartBoundaryChannel_eq_timePairingScalar f
  have htime_to_ordered :
      completedBoundaryTimePairingScalar
          (completedFinitePartBoundaryOrderedHeartClass f) +
          Complex.re (zetaCompletedPrimeDefectKernelDiagonalDebt f) =
        completedOrderedHeartScalar
          (completedFinitePartBoundaryOrderedHeartClass f) :=
    completedFinitePartBoundaryTimePairingScalar_add_primeDiagonalDebt_eq_orderedHeartScalar_by_lowerWeightTriangularTransport
      f
  have hordered_to_renormalized :
      completedOrderedHeartScalar
          (completedFinitePartBoundaryOrderedHeartClass f) =
        completedRenormalizedDefectKernelBoundaryChannel f :=
    completedFinitePartBoundaryOrderedHeartScalar_eq_renormalizedDefectKernel f
  have hrenormalized_to_positive :
      completedRenormalizedDefectKernelBoundaryChannel f =
        completedPositiveDefectKernelBoundaryScalar f :=
    completedRenormalizedDefectKernelBoundaryChannel_eq_positiveDefectKernelBoundaryScalar
      f
  have hsymm_to_finite_debt :
      completedSymmetrizedTwoFaceBoundaryScalar f +
          Complex.re (zetaCompletedPrimeDefectKernelDiagonalDebt f) =
        completedFinitePartBoundaryChannel f +
          Complex.re (zetaCompletedPrimeDefectKernelDiagonalDebt f) :=
    congrArg
      (fun x : ℝ =>
        x + Complex.re (zetaCompletedPrimeDefectKernelDiagonalDebt f))
      hsymm_to_finite
  have hfinite_to_time_debt :
      completedFinitePartBoundaryChannel f +
          Complex.re (zetaCompletedPrimeDefectKernelDiagonalDebt f) =
        completedBoundaryTimePairingScalar
          (completedFinitePartBoundaryOrderedHeartClass f) +
          Complex.re (zetaCompletedPrimeDefectKernelDiagonalDebt f) :=
    congrArg
      (fun x : ℝ =>
        x + Complex.re (zetaCompletedPrimeDefectKernelDiagonalDebt f))
      hfinite_to_time
  exact hsymm_to_finite_debt.trans
    (hfinite_to_time_debt.trans
      (htime_to_ordered.trans
        (hordered_to_renormalized.trans hrenormalized_to_positive)))

/-- Weight-triangular scalar descent identifies the raw completed finite-part channel plus
prime diagonal debt with the completed renormalized positive defect-kernel channel.

This is the finite-window payoff theorem: diagonal debt is absorbed as lower-weight radical
data, and the resulting completed scalar is represented by the positive defect-kernel
realization. -/
theorem completedFinitePartBoundaryChannel_add_primeDiagonalDebt_eq_renormalizedDefectKernel_by_weightTriangularDescent
    (f : ZetaAdmissibleFunction) :
    completedFinitePartBoundaryChannel f +
        Complex.re (zetaCompletedPrimeDefectKernelDiagonalDebt f) =
      completedRenormalizedDefectKernelBoundaryChannel f := by
  exact
    completedFinitePartBoundaryChannel_add_primeDiagonalDebt_eq_renormalizedDefectKernel_ownerDescent
      f

/-- The finite-part boundary class has completed time-pairing scalar plus prime diagonal
debt equal to the ordered-heart Hermitian GNS scalar.

This is the owner reconstruction theorem for lower-weight descent: the time-side contour
representative is evaluated through the same completed ordered-heart class as the Hermitian
positive realization. -/
theorem completedFinitePartBoundaryTimePairingScalar_add_primeDiagonalDebt_eq_orderedHeartScalar
    (f : ZetaAdmissibleFunction) :
    completedBoundaryTimePairingScalar
        (completedFinitePartBoundaryOrderedHeartClass f) +
        Complex.re (zetaCompletedPrimeDefectKernelDiagonalDebt f) =
      completedOrderedHeartScalar
        (completedFinitePartBoundaryOrderedHeartClass f) := by
  exact
    completedFinitePartBoundaryTimePairingScalar_add_primeDiagonalDebt_eq_orderedHeartScalar_by_lowerWeightTriangularTransport
      f

/-- The finite-part boundary class has time-pairing scalar plus prime diagonal debt equal to
the owner analytic boundary realization scalar. -/
theorem completedFinitePartBoundaryTimePairingScalar_add_primeDiagonalDebt_eq_completedAnalyticBoundaryRealizationScalar
    (f : ZetaAdmissibleFunction) :
    completedBoundaryTimePairingScalar
        (completedFinitePartBoundaryOrderedHeartClass f) +
        Complex.re (zetaCompletedPrimeDefectKernelDiagonalDebt f) =
      completedAnalyticBoundaryRealizationScalar f := by
  exact
    (completedFinitePartBoundaryTimePairingScalar_add_primeDiagonalDebt_eq_orderedHeartScalar f).trans
      (completedAnalyticBoundaryRealizationScalar_eq_finitePartOrderedHeartScalar f).symm

/-- The raw completed finite-part boundary scalar plus prime diagonal debt descends to the
owner completed analytic boundary realization scalar.

This is the scalar form of lower-weight ordered-heart descent.  The left side is the raw
time-side finite-part representative, while the right side is the scalar induced by the
completed ordered-heart quotient class. -/
theorem completedFinitePartBoundaryChannel_add_primeDiagonalDebt_eq_completedAnalyticBoundaryRealizationScalar
    (f : ZetaAdmissibleFunction) :
    completedFinitePartBoundaryChannel f +
        Complex.re (zetaCompletedPrimeDefectKernelDiagonalDebt f) =
      completedAnalyticBoundaryRealizationScalar f := by
  have htime :
      completedFinitePartBoundaryChannel f =
        completedBoundaryTimePairingScalar
          (completedFinitePartBoundaryOrderedHeartClass f) :=
    completedFinitePartBoundaryChannel_eq_timePairingScalar f
  have htime_debt :
      completedFinitePartBoundaryChannel f +
          Complex.re (zetaCompletedPrimeDefectKernelDiagonalDebt f) =
        completedBoundaryTimePairingScalar
          (completedFinitePartBoundaryOrderedHeartClass f) +
          Complex.re (zetaCompletedPrimeDefectKernelDiagonalDebt f) :=
    congrArg
      (fun x : ℝ =>
        x + Complex.re (zetaCompletedPrimeDefectKernelDiagonalDebt f))
      htime
  exact htime_debt.trans
    (completedFinitePartBoundaryTimePairingScalar_add_primeDiagonalDebt_eq_completedAnalyticBoundaryRealizationScalar
      f)

/-- The scalar of the completed positive-boundary precone element is the scalar of the
completed boundary weight stream. -/
theorem completedPositiveBoundaryPreconeElement_scalar_eq_weightStream_scalar
    (f : ZetaAdmissibleFunction) :
    (completedPositiveBoundaryPreconeElement f).scalar =
      (completedBoundaryWeightStream f).scalar := by
  rfl

/-- The completed positive-boundary precone element is represented by a completed boundary
weight stream in the positive cone. -/
theorem completedPositiveBoundaryPreconeElement_weightStream_mem_positiveCone
    (f : ZetaAdmissibleFunction) :
    CompletedBoundaryWeightStream.InPositiveCone
      (completedBoundaryWeightStream f) := by
  exact completedBoundaryWeightStream_mem_positiveCone f

/-- The positive representative is exactly the finite positive square-energy window. -/
theorem completedPositiveBoundaryPreconeElement_positiveRepresentative_eq_squareEnergyWindow
    (N : ℕ) (f : ZetaAdmissibleFunction) :
    (completedPositiveBoundaryPreconeElement f).positiveRepresentative N =
      finitePositiveSquareEnergyWindow N f := by
  rfl

/-- The precone positive representative is the square representative of the finite boundary
weight object. -/
theorem completedPositiveBoundaryPreconeElement_positiveRepresentative_eq_weightSquare
    (N : ℕ) (f : ZetaAdmissibleFunction) :
    (completedPositiveBoundaryPreconeElement f).positiveRepresentative N =
      FiniteBoundaryWeightObject.squareRepresentative
        (finiteBoundaryWeightObject N f) := by
  exact
    (completedPositiveBoundaryPreconeElement_positiveRepresentative_eq_squareEnergyWindow
      N f).trans
      (finiteBoundaryWeightObject_squareRepresentative_eq_squareEnergyWindow N f).symm

/-- The positive representative of the completed positive-boundary precone element is
pointwise nonnegative. -/
theorem completedPositiveBoundaryPreconeElement_positiveRepresentative_nonnegative
    (N : ℕ) (f : ZetaAdmissibleFunction) :
    0 ≤ (completedPositiveBoundaryPreconeElement f).positiveRepresentative N := by
  exact (completedPositiveBoundaryPreconeElement f).positiveRepresentative_nonnegative N

/-- The absorbed representative of the completed positive-boundary precone element converges
to its scalar realization. -/
theorem completedPositiveBoundaryPreconeElement_absorbedRepresentative_tendsto_scalar
    (f : ZetaAdmissibleFunction) :
    Tendsto
      (completedPositiveBoundaryPreconeElement f).absorbedRepresentative
      atTop
      (𝓝 (completedPositiveBoundaryPreconeElement f).scalar) := by
  exact (completedPositiveBoundaryPreconeElement f).absorbedRepresentative_tendsto_scalar

/-- The absorbed representative is obtained from the positive square representative by adding
the named finite diagonal-debt absorption defect. -/
theorem completedPositiveBoundaryPreconeElement_absorbed_eq_positive_add_absorptionDefect
    (N : ℕ) (f : ZetaAdmissibleFunction) :
    (completedPositiveBoundaryPreconeElement f).absorbedRepresentative N =
      (completedPositiveBoundaryPreconeElement f).positiveRepresentative N +
        (completedPositiveBoundaryPreconeElement f).absorptionDefect N := by
  have hdef :
      (completedPositiveBoundaryPreconeElement f).absorptionDefect N =
        (completedPositiveBoundaryPreconeElement f).absorbedRepresentative N -
          (completedPositiveBoundaryPreconeElement f).positiveRepresentative N :=
    (completedPositiveBoundaryPreconeElement f).absorptionDefect_eq N
  let A : ℝ := (completedPositiveBoundaryPreconeElement f).absorbedRepresentative N
  let Q : ℝ := (completedPositiveBoundaryPreconeElement f).positiveRepresentative N
  let E : ℝ := (completedPositiveBoundaryPreconeElement f).absorptionDefect N
  change A = Q + E
  have hE : E = A - Q := hdef
  calc
    A = Q + (A - Q) := by
      exact zetaBoundaryDebt_add_sub_cancel A Q
    _ = Q + E := by
      exact congrArg (fun x : ℝ => Q + x) hE.symm

/-- The absorbed representative is exactly the finite positive renormalized boundary window. -/
theorem completedPositiveBoundaryPreconeElement_absorbedRepresentative_eq_renormalizedWindow
    (N : ℕ) (f : ZetaAdmissibleFunction) :
    (completedPositiveBoundaryPreconeElement f).absorbedRepresentative N =
      finitePositiveRenormalizedBoundaryWindow N f := by
  rfl

/-- The absorbed representative is exactly the finite-part boundary window. -/
theorem completedPositiveBoundaryPreconeElement_absorbedRepresentative_eq_finitePartWindow
    (N : ℕ) (f : ZetaAdmissibleFunction) :
    (completedPositiveBoundaryPreconeElement f).absorbedRepresentative N =
      finitePartBoundaryWindow N f := by
  exact
    (completedPositiveBoundaryPreconeElement_absorbedRepresentative_eq_renormalizedWindow
      N f).trans
      (finitePositiveRenormalizedBoundaryWindow_eq_finitePartBoundaryWindow N f)

/-- The precone absorbed representative is the finite-part representative of the finite
boundary weight object. -/
theorem completedPositiveBoundaryPreconeElement_absorbedRepresentative_eq_weightFinitePart
    (N : ℕ) (f : ZetaAdmissibleFunction) :
    (completedPositiveBoundaryPreconeElement f).absorbedRepresentative N =
      FiniteBoundaryWeightObject.finitePartRepresentative
        (finiteBoundaryWeightObject N f) := by
  exact
    (completedPositiveBoundaryPreconeElement_absorbedRepresentative_eq_finitePartWindow
      N f).trans
      (finiteBoundaryWeightObject_finitePartRepresentative_eq_finitePartBoundaryWindow
        N f).symm

/-- The precone absorption defect is the negative face of the finite diagonal debt. -/
theorem completedPositiveBoundaryPreconeElement_absorptionDefect_eq_neg_diagonalDebt
    (N : ℕ) (f : ZetaAdmissibleFunction) :
    (completedPositiveBoundaryPreconeElement f).absorptionDefect N =
      - (finiteBoundaryWeightObject N f).diagonalDebt := by
  have hdefect :
      (completedPositiveBoundaryPreconeElement f).absorptionDefect N =
        finitePartDebtAbsorptionWindow N f :=
    completedPositiveBoundaryPreconeElement_absorptionDefect_eq_debtAbsorption N f
  have habs :
      finitePartDebtAbsorptionWindow N f =
        (finiteBoundaryWeightObject N f).debtAbsorption := by
    rfl
  have hneg :
      (finiteBoundaryWeightObject N f).debtAbsorption =
        - (finiteBoundaryWeightObject N f).diagonalDebt :=
    finiteBoundaryWeightObject_debtAbsorption_eq_neg_diagonalDebt N f
  exact hdefect.trans (habs.trans hneg)

/-- Completed precone-level weight-triangular transport: the positive square representative,
after adding the lower-weight absorption defect, is the finite-part weight representative. -/
theorem completedPositiveBoundaryPreconeElement_weightTriangularTransport
    (N : ℕ) (f : ZetaAdmissibleFunction) :
    (completedPositiveBoundaryPreconeElement f).positiveRepresentative N +
        (completedPositiveBoundaryPreconeElement f).absorptionDefect N =
      FiniteBoundaryWeightObject.finitePartRepresentative
        (finiteBoundaryWeightObject N f) := by
  have habsorbed :
      (completedPositiveBoundaryPreconeElement f).absorbedRepresentative N =
        (completedPositiveBoundaryPreconeElement f).positiveRepresentative N +
          (completedPositiveBoundaryPreconeElement f).absorptionDefect N :=
    completedPositiveBoundaryPreconeElement_absorbed_eq_positive_add_absorptionDefect N f
  have hfinite :
      (completedPositiveBoundaryPreconeElement f).absorbedRepresentative N =
        FiniteBoundaryWeightObject.finitePartRepresentative
          (finiteBoundaryWeightObject N f) :=
    completedPositiveBoundaryPreconeElement_absorbedRepresentative_eq_weightFinitePart N f
  exact habsorbed.symm.trans hfinite

/-- Completed precone-level transport with the diagonal face written explicitly. -/
theorem completedPositiveBoundaryPreconeElement_positive_sub_diagonalDebt_eq_weightFinitePart
    (N : ℕ) (f : ZetaAdmissibleFunction) :
    (completedPositiveBoundaryPreconeElement f).positiveRepresentative N -
        (finiteBoundaryWeightObject N f).diagonalDebt =
      FiniteBoundaryWeightObject.finitePartRepresentative
        (finiteBoundaryWeightObject N f) := by
  have hdefect :
      (completedPositiveBoundaryPreconeElement f).absorptionDefect N =
        - (finiteBoundaryWeightObject N f).diagonalDebt :=
    completedPositiveBoundaryPreconeElement_absorptionDefect_eq_neg_diagonalDebt N f
  calc
    (completedPositiveBoundaryPreconeElement f).positiveRepresentative N -
        (finiteBoundaryWeightObject N f).diagonalDebt =
        (completedPositiveBoundaryPreconeElement f).positiveRepresentative N +
          - (finiteBoundaryWeightObject N f).diagonalDebt := by
      exact sub_eq_add_neg
        ((completedPositiveBoundaryPreconeElement f).positiveRepresentative N)
        ((finiteBoundaryWeightObject N f).diagonalDebt)
    _ =
        (completedPositiveBoundaryPreconeElement f).positiveRepresentative N +
          (completedPositiveBoundaryPreconeElement f).absorptionDefect N := by
      exact congrArg
        (fun x : ℝ =>
          (completedPositiveBoundaryPreconeElement f).positiveRepresentative N + x)
        hdefect.symm
    _ =
        FiniteBoundaryWeightObject.finitePartRepresentative
          (finiteBoundaryWeightObject N f) := by
      exact completedPositiveBoundaryPreconeElement_weightTriangularTransport N f

/-- The absorbed representative is exactly the raw completed boundary window, because the
finite diagonal debt has been added and cancelled inside the finite-part normalization. -/
theorem completedPositiveBoundaryPreconeElement_absorbedRepresentative_eq_completedWindow
    (N : ℕ) (f : ZetaAdmissibleFunction) :
    (completedPositiveBoundaryPreconeElement f).absorbedRepresentative N =
      completedBoundaryWindow N f := by
  exact
    (completedPositiveBoundaryPreconeElement_absorbedRepresentative_eq_finitePartWindow
      N f).trans
      (finitePartBoundaryWindow_eq_completedBoundaryWindow N f)

/-- The completed finite-part boundary form in the linear boundary normalization.  Positivity
is not owned by this scalar directly; it is compared to the positive Hermitian GNS scalar by
the ordered-heart transport layer. -/
noncomputable def completedFinitePartGNSBoundaryForm
    (f : ZetaAdmissibleFunction) : ℝ :=
  completedFinitePartBoundaryChannel f

/-- The completed finite-part boundary form realizes as the completed boundary scalar. -/
theorem completedFinitePartGNSBoundaryForm_eq_boundaryChannel_re
    (f : ZetaAdmissibleFunction) :
    completedFinitePartGNSBoundaryForm f =
      Complex.re (completedBoundaryChannel (convolutionAutocorrelation f)) := by
  unfold completedFinitePartGNSBoundaryForm
  exact completedFinitePartBoundaryChannel_eq_completedBoundaryChannel f

/-- The raw completed physical boundary windows converge to the completed boundary channel
after diagonal debt has been cancelled inside the finite-part normalization. -/
theorem completedBoundaryWindow_tendsto_boundaryChannel
    (f : ZetaAdmissibleFunction) :
    Tendsto
      (fun N : ℕ => completedBoundaryWindow N f)
      atTop
      (𝓝 (Complex.re (completedBoundaryChannel (convolutionAutocorrelation f)))) := by
  have hfinite :
      (fun N : ℕ => completedBoundaryWindow N f) =
        (fun N : ℕ => finitePartBoundaryWindow N f) := by
    funext N
    exact (finitePartBoundaryWindow_eq_completedBoundaryWindow N f).symm
  exact Eq.subst
    (motive := fun u : ℕ → ℝ =>
      Tendsto u atTop
        (𝓝 (Complex.re (completedBoundaryChannel (convolutionAutocorrelation f)))))
    hfinite.symm
    (finitePartBoundaryWindow_tendsto_boundaryChannel f)

/-- Compatibility wrapper for the explicit finite-window expression after the diagonal debt has
already been cancelled in the finite-part normalization. -/
theorem completedBoundaryWindow_tendsto
    (f : ZetaAdmissibleFunction) :
    Tendsto
      (fun N : ℕ => completedBoundaryWindow N f)
      atTop
      (𝓝 (Complex.re (completedBoundaryChannel (convolutionAutocorrelation f)))) := by
  exact completedBoundaryWindow_tendsto_boundaryChannel f

/-- The finite-window completed physical channel is nonnegative after adding its matching
prime diagonal debt. -/
theorem completedBoundaryWindow_add_diagonalDebt_nonnegative
    (N : ℕ) (f : ZetaAdmissibleFunction) :
    0 ≤ completedBoundaryWindow N f + zetaPrimeDiagonalDebt N f := by
  exact completedCorrectedBoundaryWindow_nonnegative N f

/-- The completed boundary channel on an autocorrelation probe has real part represented by
the completed finite-part boundary channel. -/
theorem completedBoundaryChannel_convolutionAutocorrelation_re_eq_completedFinitePartBoundaryChannel
    (f : ZetaAdmissibleFunction) :
    Complex.re (completedBoundaryChannel (convolutionAutocorrelation f)) =
    completedFinitePartBoundaryChannel f := by
  exact (completedFinitePartBoundaryChannel_eq_completedBoundaryChannel f).symm

end ZetaAdmissibleFunction

end
end LFunctions
end Boundary
