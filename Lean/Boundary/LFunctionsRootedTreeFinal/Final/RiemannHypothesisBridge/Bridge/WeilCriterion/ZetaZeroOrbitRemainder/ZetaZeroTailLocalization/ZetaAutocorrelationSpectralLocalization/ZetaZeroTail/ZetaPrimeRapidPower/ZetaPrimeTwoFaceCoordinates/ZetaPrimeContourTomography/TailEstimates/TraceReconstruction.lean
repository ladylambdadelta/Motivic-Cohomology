import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaZeroTail.ZetaPrimeRapidPower.ZetaPrimeTwoFaceCoordinates.ZetaPrimeContourTomography.TailEstimates.TraceTransport

/-!
# Completed prime trace reconstruction

This file owns the non-circular reconstruction input for visible prime
contour/time transport: the completed time/log prime pairing and the
completed contour-realized prime pairing are the same trace scalar.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open Filter
open scoped Topology

namespace ZetaAdmissibleFunction

/-- Trace reconstruction identifies the time-side prime-power contribution and
the contour spectral-sample prime-power contribution on an autocorrelation
probe. -/
theorem zetaCompletedExplicitFormulaPrimePowerContribution_re_eq_spectralSampleContribution_re_ownerTraceReconstruction
    (f : ZetaAdmissibleFunction)
    (D : CompletedFiniteWindowPrimeDistributionReconstruction f) :
    Complex.re
        (zetaCompletedExplicitFormulaPrimePowerContribution
          (convolutionAutocorrelation f)) =
      Complex.re
        (zetaCompletedExplicitFormulaPrimePowerSpectralSampleContribution
          (convolutionAutocorrelation f)) :=
  sub_eq_zero.mp
    ((completedPrimeTraceFunctionalGap_eq f).symm.trans
      (completedPrimeTraceFunctionalGap_eq_zero_traceTransport_source_core f D))

/-- Trace reconstruction identifies the physical completed prime off-diagonal
channel with the contour-realized spectral completed prime channel. -/
theorem completedPrimeOffDiagonalChannel_eq_completedSpectralPrimeOffDiagonalChannel_ownerTraceReconstruction
    (f : ZetaAdmissibleFunction)
    (D : CompletedFiniteWindowPrimeDistributionReconstruction f) :
    completedPrimeOffDiagonalChannel f =
      completedSpectralPrimeOffDiagonalChannel f :=
  let htime :
      completedPrimeOffDiagonalChannel f =
        Complex.re
          (zetaCompletedExplicitFormulaPrimePowerContribution
            (convolutionAutocorrelation f)) :=
    completedPrimeOffDiagonalChannel_eq_primePowerContribution_re f
  let hspectral :
      completedSpectralPrimeOffDiagonalChannel f =
        Complex.re
          (zetaCompletedExplicitFormulaPrimePowerSpectralSampleContribution
            (convolutionAutocorrelation f)) :=
    completedSpectralPrimeOffDiagonalChannel_eq_spectralSampleContribution_re
      f
  htime.trans
    ((zetaCompletedExplicitFormulaPrimePowerContribution_re_eq_spectralSampleContribution_re_ownerTraceReconstruction
      f D).trans hspectral.symm)

/-- The finite spectral prime window is the finite contour-realized prime
window for the autocorrelation probe. -/
theorem finiteSpectralPrimeOffDiagonalWindow_eq_contourRealizedTimeDistributionWindow
    (N : ℕ) (f : ZetaAdmissibleFunction) :
    finiteSpectralPrimeOffDiagonalWindow N f =
      finitePrimeContourRealizedTimeDistributionWindow N
        (convolutionAutocorrelation f) :=
  finiteSpectralPrimeOffDiagonalWindow_eq_contourRealizedTimeDistributionWindow_traceTransport_source
    N f

/-- The finite sum of symmetrized completed two-face coordinates is the
completed two-face/GNS matrix window. -/
theorem zetaCompletedPrimeTwoFaceGNSSymmetrizedCoordinate_sum_eq_matrixWindow
    (N : ℕ) (f : ZetaAdmissibleFunction) :
    (∑ ι in ZetaPrimePowerIndex.window N,
        zetaCompletedPrimeTwoFaceGNSSymmetrizedCoordinate ι f) =
      zetaCompletedPrimeTwoFaceGNSMatrixCoefficientWindow N f :=
  zetaCompletedPrimeTwoFaceGNSSymmetrizedCoordinate_sum_eq_matrixWindow_traceTransport_source
    N f

/-- The finite spectral prime window is the negative real part of the finite
completed two-face/GNS matrix window. -/
theorem finiteSpectralPrimeOffDiagonalWindow_eq_neg_twoFaceWindow_re
    (N : ℕ) (f : ZetaAdmissibleFunction) :
    finiteSpectralPrimeOffDiagonalWindow N f =
      -Complex.re (zetaCompletedPrimeTwoFaceGNSMatrixCoefficientWindow N f) :=
  finiteSpectralPrimeOffDiagonalWindow_eq_neg_twoFaceWindow_re_traceTransport_source
    N f

/-- Lower-weight contour reconstruction kills the finite completed two-face
GNS matrix-window real scalars in the limit. -/
theorem zetaCompletedPrimeTwoFaceGNSMatrixCoefficientWindow_re_eq_diagonalDebt_sub_positiveWindow_re
    (N : ℕ) (f : ZetaAdmissibleFunction) :
    Complex.re (zetaCompletedPrimeTwoFaceGNSMatrixCoefficientWindow N f) =
      zetaCompletedPrimeDefectKernelDiagonalDebtRealWindow N f -
        zetaCompletedPrimeDefectKernelPositiveRealWindow N f :=
  zetaCompletedPrimeTwoFaceGNSMatrixCoefficientWindow_re_eq_diagonalDebt_sub_positiveWindow_re_traceTransport_source
    N f

/-- Source lower-weight annihilation of the positive completed prime-defect
coordinate trace. -/
theorem zetaCompletedPrimeDefectKernelPositiveCoordinateTsumRe_eq_zero_source_core
    (f : ZetaAdmissibleFunction)
    (hmajorant : Summable (fun index : ZetaPrimePowerIndex =>
      zetaCompletedPrimeSpectralCoordinateMajorant index f))
    (hcoordinateZero :
      Complex.re (zetaCompletedPrimeDefectKernelDiagonalDebtCoordinateTsum f) =
        0) :
    zetaCompletedPrimeDefectKernelPositiveCoordinateTsumRe f = 0 :=
  zetaCompletedPrimeDefectKernelPositiveCoordinateTsumRe_eq_zero_traceTransport_source_core
    f hmajorant hcoordinateZero

/-- Source lower-weight annihilation of the diagonal completed prime-defect
coordinate trace. -/
theorem zetaCompletedPrimeDefectKernelDiagonalDebtCoordinateTsum_re_eq_zero_source_core
    (f : ZetaAdmissibleFunction)
    (hmajorant : Summable (fun index : ZetaPrimePowerIndex =>
      zetaCompletedPrimeSpectralCoordinateMajorant index f))
    (hcoordinateZero :
      Complex.re (zetaCompletedPrimeDefectKernelDiagonalDebtCoordinateTsum f) =
        0) :
    Complex.re (zetaCompletedPrimeDefectKernelDiagonalDebtCoordinateTsum f) =
      0 :=
  let hcoordinate :
      Complex.re (zetaCompletedPrimeDefectKernelDiagonalDebtCoordinateTsum f) =
        Complex.re (zetaCompletedPrimeDefectKernelDiagonalDebt f) :=
    zetaCompletedPrimeDefectKernelDiagonalDebtCoordinateTsum_re_eq_ownerDiagonalDebt_re_source_core
      f hmajorant hcoordinateZero
  let howner :
      Complex.re (zetaCompletedPrimeDefectKernelDiagonalDebt f) = 0 :=
    zetaCompletedPrimeDefectKernelDiagonalDebt_re_eq_zero_source_core f hmajorant
      hcoordinateZero
  hcoordinate.trans howner

/-- Source lower-weight coordinate trace annihilation. -/
theorem completedPrimeDefectCoordinateTraceAnnihilation_source_core
    (f : ZetaAdmissibleFunction)
    (hmajorant : Summable (fun index : ZetaPrimePowerIndex =>
      zetaCompletedPrimeSpectralCoordinateMajorant index f))
    (hcoordinateZero :
      Complex.re (zetaCompletedPrimeDefectKernelDiagonalDebtCoordinateTsum f) =
        0) :
    CompletedPrimeDefectCoordinateTraceAnnihilation f :=
  completedPrimeDefectCoordinateTraceAnnihilation_traceTransport_source_core
    f hmajorant hcoordinateZero

/-- Lower-weight coordinate trace annihilation gives the positive-coordinate
zero scalar. -/
theorem completedPrimeDefectCoordinateTraceAnnihilation_positive_eq_zero
    (f : ZetaAdmissibleFunction)
    (hannihilation :
      CompletedPrimeDefectCoordinateTraceAnnihilation f) :
    zetaCompletedPrimeDefectKernelPositiveCoordinateTsumRe f = 0 :=
  hannihilation.1

/-- Lower-weight coordinate trace annihilation gives the diagonal-coordinate
zero scalar. -/
theorem completedPrimeDefectCoordinateTraceAnnihilation_diagonal_re_eq_zero
    (f : ZetaAdmissibleFunction)
    (hannihilation :
      CompletedPrimeDefectCoordinateTraceAnnihilation f) :
    Complex.re (zetaCompletedPrimeDefectKernelDiagonalDebtCoordinateTsum f) =
      0 :=
  hannihilation.2

/-- Lower-weight trace reconstruction annihilates the positive completed
prime-defect coordinate trace. -/
theorem zetaCompletedPrimeDefectKernelPositiveCoordinateTsumRe_eq_zero_ownerTraceLowerWeight
    (f : ZetaAdmissibleFunction)
    (hmajorant : Summable (fun index : ZetaPrimePowerIndex =>
      zetaCompletedPrimeSpectralCoordinateMajorant index f))
    (hcoordinateZero :
      Complex.re (zetaCompletedPrimeDefectKernelDiagonalDebtCoordinateTsum f) =
        0) :
    zetaCompletedPrimeDefectKernelPositiveCoordinateTsumRe f = 0 :=
  completedPrimeDefectCoordinateTraceAnnihilation_positive_eq_zero
    f
    (completedPrimeDefectCoordinateTraceAnnihilation_source_core f hmajorant
      hcoordinateZero)

/-- Lower-weight trace reconstruction annihilates the diagonal completed
prime-defect coordinate trace. -/
theorem zetaCompletedPrimeDefectKernelDiagonalDebtCoordinateTsum_re_eq_zero_ownerTraceLowerWeight
    (f : ZetaAdmissibleFunction)
    (hmajorant : Summable (fun index : ZetaPrimePowerIndex =>
      zetaCompletedPrimeSpectralCoordinateMajorant index f))
    (hcoordinateZero :
      Complex.re (zetaCompletedPrimeDefectKernelDiagonalDebtCoordinateTsum f) =
        0) :
    Complex.re (zetaCompletedPrimeDefectKernelDiagonalDebtCoordinateTsum f) =
      0 :=
  zetaCompletedPrimeDefectKernelDiagonalDebtCoordinateTsum_re_eq_zero_traceTransport_source_core
    f hmajorant hcoordinateZero

/-- Lower-weight contour reconstruction kills the finite completed positive
prime-defect windows in the limit. -/
theorem zetaCompletedPrimeDefectKernelPositiveRealWindow_tendsto_zero_ownerTraceLowerWeight
    (f : ZetaAdmissibleFunction)
    (hmajorant : Summable (fun index : ZetaPrimePowerIndex =>
      zetaCompletedPrimeSpectralCoordinateMajorant index f))
    (hcoordinateZero :
      Complex.re (zetaCompletedPrimeDefectKernelDiagonalDebtCoordinateTsum f) =
        0) :
    Tendsto
      (fun N : ℕ => zetaCompletedPrimeDefectKernelPositiveRealWindow N f)
      atTop
      (𝓝 0) :=
  let hcoordinate :
      Tendsto
        (fun N : ℕ => zetaCompletedPrimeDefectKernelPositiveRealWindow N f)
        atTop
        (𝓝 (zetaCompletedPrimeDefectKernelPositiveCoordinateTsumRe f)) :=
    zetaCompletedPrimeDefectKernelPositiveRealWindow_tendsto_coordinateTsum_re_of_spectralMajorant
      f
      hmajorant
  let hzero :
      zetaCompletedPrimeDefectKernelPositiveCoordinateTsumRe f = 0 :=
    zetaCompletedPrimeDefectKernelPositiveCoordinateTsumRe_eq_zero_ownerTraceLowerWeight
      f hmajorant hcoordinateZero
  Eq.subst
    (motive := fun value : ℝ =>
      Tendsto
        (fun N : ℕ => zetaCompletedPrimeDefectKernelPositiveRealWindow N f)
        atTop
        (𝓝 value))
    hzero
    hcoordinate

/-- Lower-weight contour reconstruction kills the finite completed diagonal
debt windows in the limit. -/
theorem zetaCompletedPrimeDefectKernelDiagonalDebtRealWindow_tendsto_zero_ownerTraceLowerWeight
    (f : ZetaAdmissibleFunction)
    (hmajorant : Summable (fun index : ZetaPrimePowerIndex =>
      zetaCompletedPrimeSpectralCoordinateMajorant index f))
    (hcoordinateZero :
      Complex.re (zetaCompletedPrimeDefectKernelDiagonalDebtCoordinateTsum f) =
        0) :
    Tendsto
      (fun N : ℕ => zetaCompletedPrimeDefectKernelDiagonalDebtRealWindow N f)
      atTop
      (𝓝 0) :=
  zetaCompletedPrimeDefectKernelDiagonalDebtRealWindow_tendsto_zero_traceTransport_source_core
    f
    hmajorant
    hcoordinateZero

/-- The finite two-face matrix real window is the diagonal-minus-positive
defect window as a function of the cutoff. -/
theorem zetaCompletedPrimeTwoFaceGNSMatrixCoefficientWindow_re_fun_eq_diagonalDebt_sub_positiveWindow_re
    (f : ZetaAdmissibleFunction) :
    (fun N : ℕ =>
      Complex.re (zetaCompletedPrimeTwoFaceGNSMatrixCoefficientWindow N f)) =
      fun N : ℕ =>
        zetaCompletedPrimeDefectKernelDiagonalDebtRealWindow N f -
          zetaCompletedPrimeDefectKernelPositiveRealWindow N f :=
  funext
    (fun N : ℕ =>
      zetaCompletedPrimeTwoFaceGNSMatrixCoefficientWindow_re_eq_diagonalDebt_sub_positiveWindow_re
        N f)

theorem zetaCompletedPrimeTwoFaceGNSMatrixCoefficientWindow_re_tendsto_zero_ownerTraceLowerWeight
    (f : ZetaAdmissibleFunction)
    (hmajorant : Summable (fun index : ZetaPrimePowerIndex =>
      zetaCompletedPrimeSpectralCoordinateMajorant index f))
    (hcoordinateZero :
      Complex.re (zetaCompletedPrimeDefectKernelDiagonalDebtCoordinateTsum f) =
        0) :
    Tendsto
      (fun N : ℕ =>
        Complex.re (zetaCompletedPrimeTwoFaceGNSMatrixCoefficientWindow N f))
      atTop
      (𝓝 0) :=
  let hdiagonal :
      Tendsto
        (fun N : ℕ => zetaCompletedPrimeDefectKernelDiagonalDebtRealWindow N f)
        atTop
        (𝓝 0) :=
    zetaCompletedPrimeDefectKernelDiagonalDebtRealWindow_tendsto_zero_ownerTraceLowerWeight
      f hmajorant hcoordinateZero
  let hpositive :
      Tendsto
        (fun N : ℕ => zetaCompletedPrimeDefectKernelPositiveRealWindow N f)
        atTop
        (𝓝 0) :=
    zetaCompletedPrimeDefectKernelPositiveRealWindow_tendsto_zero_ownerTraceLowerWeight
      f
      hmajorant
      hcoordinateZero
  let hsub :
      Tendsto
        (fun N : ℕ =>
          zetaCompletedPrimeDefectKernelDiagonalDebtRealWindow N f -
            zetaCompletedPrimeDefectKernelPositiveRealWindow N f)
        atTop
        (𝓝 (0 - 0)) :=
    hdiagonal.sub hpositive
  let hzero : 0 - 0 = (0 : ℝ) :=
    sub_self 0
  let htarget :
      Tendsto
        (fun N : ℕ =>
          zetaCompletedPrimeDefectKernelDiagonalDebtRealWindow N f -
            zetaCompletedPrimeDefectKernelPositiveRealWindow N f)
        atTop
        (𝓝 0) :=
    Eq.subst
      (motive := fun value : ℝ =>
        Tendsto
          (fun N : ℕ =>
            zetaCompletedPrimeDefectKernelDiagonalDebtRealWindow N f -
              zetaCompletedPrimeDefectKernelPositiveRealWindow N f)
          atTop
          (𝓝 value))
      hzero
      hsub
  let hfun :
      (fun N : ℕ =>
        Complex.re (zetaCompletedPrimeTwoFaceGNSMatrixCoefficientWindow N f)) =
        fun N : ℕ =>
          zetaCompletedPrimeDefectKernelDiagonalDebtRealWindow N f -
            zetaCompletedPrimeDefectKernelPositiveRealWindow N f :=
    zetaCompletedPrimeTwoFaceGNSMatrixCoefficientWindow_re_fun_eq_diagonalDebt_sub_positiveWindow_re
      f
  Eq.subst
    (motive := fun u : ℕ → ℝ => Tendsto u atTop (𝓝 0))
    hfun.symm
    htarget

/-- The finite spectral prime window is the negative two-face real window as a
function of the cutoff. -/
theorem finiteSpectralPrimeOffDiagonalWindow_fun_eq_neg_twoFaceWindow_re
    (f : ZetaAdmissibleFunction) :
    (fun N : ℕ => finiteSpectralPrimeOffDiagonalWindow N f) =
      fun N : ℕ =>
        -Complex.re (zetaCompletedPrimeTwoFaceGNSMatrixCoefficientWindow N f) :=
  funext
    (fun N : ℕ =>
      finiteSpectralPrimeOffDiagonalWindow_eq_neg_twoFaceWindow_re N f)

/-- Lower-weight contour reconstruction makes the finite spectral prime
windows converge to zero on autocorrelation probes. -/
theorem finiteSpectralPrimeOffDiagonalWindow_tendsto_zero_ownerTraceLowerWeight
    (f : ZetaAdmissibleFunction)
    (hmajorant : Summable (fun index : ZetaPrimePowerIndex =>
      zetaCompletedPrimeSpectralCoordinateMajorant index f))
    (hcoordinateZero :
      Complex.re (zetaCompletedPrimeDefectKernelDiagonalDebtCoordinateTsum f) =
        0) :
    Tendsto
      (fun N : ℕ => finiteSpectralPrimeOffDiagonalWindow N f)
      atTop
      (𝓝 0) :=
  let htwoFace :
      Tendsto
        (fun N : ℕ =>
          Complex.re (zetaCompletedPrimeTwoFaceGNSMatrixCoefficientWindow N f))
        atTop
        (𝓝 0) :=
    zetaCompletedPrimeTwoFaceGNSMatrixCoefficientWindow_re_tendsto_zero_ownerTraceLowerWeight
      f hmajorant hcoordinateZero
  let hneg :
      Tendsto
        (fun N : ℕ =>
          -Complex.re (zetaCompletedPrimeTwoFaceGNSMatrixCoefficientWindow N f))
        atTop
        (𝓝 (-0)) :=
    htwoFace.neg
  let hzero : -0 = (0 : ℝ) :=
    neg_zero
  let htarget :
      Tendsto
        (fun N : ℕ =>
          -Complex.re (zetaCompletedPrimeTwoFaceGNSMatrixCoefficientWindow N f))
        atTop
        (𝓝 0) :=
    Eq.subst
      (motive := fun value : ℝ =>
        Tendsto
          (fun N : ℕ =>
            -Complex.re (zetaCompletedPrimeTwoFaceGNSMatrixCoefficientWindow N f))
          atTop
          (𝓝 value))
      hzero
      hneg
  let hfun :
      (fun N : ℕ => finiteSpectralPrimeOffDiagonalWindow N f) =
        fun N : ℕ =>
          -Complex.re (zetaCompletedPrimeTwoFaceGNSMatrixCoefficientWindow N f) :=
    finiteSpectralPrimeOffDiagonalWindow_fun_eq_neg_twoFaceWindow_re f
  Eq.subst
    (motive := fun u : ℕ → ℝ => Tendsto u atTop (𝓝 0))
    hfun.symm
    htarget

/-- The finite contour-realized prime windows converge to zero after
lower-weight normalization on autocorrelation probes. -/
theorem finitePrimeContourRealizedTimeDistributionWindow_tendsto_zero_ownerTraceLowerWeight
    (f : ZetaAdmissibleFunction)
    (hmajorant : Summable (fun index : ZetaPrimePowerIndex =>
      zetaCompletedPrimeSpectralCoordinateMajorant index f)) :
    Tendsto
      (fun N : ℕ =>
        finitePrimeContourRealizedTimeDistributionWindow N
          (convolutionAutocorrelation f))
      atTop
      (𝓝 0) :=
  finitePrimeContourRealizedTimeDistributionWindow_tendsto_zero_traceTransport_source_core
    f hmajorant

/-- The finite contour-realized prime windows converge to the completed
contour-realized prime trace. -/
theorem finitePrimeContourRealizedTimeDistributionWindow_tendsto_completedPairing
    (f : ZetaAdmissibleFunction)
    (hmajorant : Summable (fun index : ZetaPrimePowerIndex =>
      zetaCompletedPrimeSpectralCoordinateMajorant index f)) :
    Tendsto
      (fun N : ℕ =>
        finitePrimeContourRealizedTimeDistributionWindow N
          (convolutionAutocorrelation f))
      atTop
      (𝓝 (completedPrimeContourRealizedTimeDistributionPairing
        (convolutionAutocorrelation f))) :=
  finitePrimeContourRealizedTimeDistributionWindow_tendsto_completedPairing_ownerTailEstimate
    f hmajorant

/-- The completed contour-realized spectral prime trace vanishes as the limit
of the lower-weight finite spectral windows. -/
theorem completedPrimeContourRealizedTimeDistributionPairing_eq_zero_ownerTraceLowerWeight
    (f : ZetaAdmissibleFunction) :
    completedPrimeContourRealizedTimeDistributionPairing
        (convolutionAutocorrelation f) = 0 :=
  completedPrimeContourRealizedTimeDistributionPairing_eq_zero_traceTransport_source_core
    f

/-- Lower-weight normalization kills the reconstructed completed spectral
prime off-diagonal trace scalar. -/
theorem completedSpectralPrimeOffDiagonalChannel_eq_zero_ownerTraceLowerWeight
    (f : ZetaAdmissibleFunction) :
    completedSpectralPrimeOffDiagonalChannel f = 0 :=
  completedSpectralPrimeOffDiagonalChannel_eq_zero_traceTransport_source_core
    f

/-- Holographic trace reconstruction and lower-weight normalization kill the
completed physical prime off-diagonal trace scalar. -/
theorem completedPrimeOffDiagonalChannel_eq_zero_ownerTraceReconstruction
    (f : ZetaAdmissibleFunction)
    (D : CompletedFiniteWindowPrimeDistributionReconstruction f) :
    completedPrimeOffDiagonalChannel f = 0 :=
  completedPrimeOffDiagonalChannel_eq_zero_traceTransport_source_core f D

/-- The contour-realized pairing is definitionally the spectral distribution
pairing for the transformed autocorrelation probe. -/
theorem completedPrimeContourRealizedTimeDistributionPairing_eq_spectralDistributionPairing
    (f : ZetaAdmissibleFunction) :
    completedPrimeContourRealizedTimeDistributionPairing
        (convolutionAutocorrelation f) =
      completedPrimeSpectralDistributionPairing
        (zetaCompletedSpectralLaplaceTransform
          (convolutionAutocorrelation f)) :=
  Eq.refl
    (completedPrimeContourRealizedTimeDistributionPairing
      (convolutionAutocorrelation f))

/-- The completed contour-realized time distribution pairing is the completed
spectral prime off-diagonal channel. -/
theorem completedPrimeContourRealizedTimeDistributionPairing_eq_completedSpectralPrimeOffDiagonalChannel
    (f : ZetaAdmissibleFunction) :
    completedPrimeContourRealizedTimeDistributionPairing
        (convolutionAutocorrelation f) =
      completedSpectralPrimeOffDiagonalChannel f :=
  let hrealized :
      completedPrimeContourRealizedTimeDistributionPairing
          (convolutionAutocorrelation f) =
        completedPrimeSpectralDistributionPairing
          (zetaCompletedSpectralLaplaceTransform
            (convolutionAutocorrelation f)) :=
    completedPrimeContourRealizedTimeDistributionPairing_eq_spectralDistributionPairing
      f
  let hspectral :
      completedSpectralPrimeOffDiagonalChannel f =
        completedPrimeSpectralDistributionPairing
          (zetaCompletedSpectralLaplaceTransform
            (convolutionAutocorrelation f)) :=
    completedSpectralPrimeOffDiagonalChannel_eq_spectralDistributionPairing
      f
  hrealized.trans hspectral.symm

/-- Trace reconstruction identifies the completed time/log prime pairing with
the completed contour-realized prime pairing. -/
theorem completedPrimeDistributionTransport_timePairing_eq_contourRealizedPairing_ownerTraceReconstruction
    (f : ZetaAdmissibleFunction)
    (D : CompletedFiniteWindowPrimeDistributionReconstruction f) :
    completedPrimeTimeDistributionPairing (convolutionAutocorrelation f) =
      completedPrimeContourRealizedTimeDistributionPairing
        (convolutionAutocorrelation f) :=
  let htime :
      completedPrimeTimeDistributionPairing (convolutionAutocorrelation f) =
        completedPrimeOffDiagonalChannel f :=
    completedPrimeTimeDistributionPairing_eq_completedPrimeOffDiagonalChannel f
  let hchannels :
      completedPrimeOffDiagonalChannel f =
        completedSpectralPrimeOffDiagonalChannel f :=
    completedPrimeOffDiagonalChannel_eq_completedSpectralPrimeOffDiagonalChannel_ownerTraceReconstruction
      f D
  let hcontour :
      completedSpectralPrimeOffDiagonalChannel f =
        completedPrimeContourRealizedTimeDistributionPairing
          (convolutionAutocorrelation f) :=
    (completedPrimeContourRealizedTimeDistributionPairing_eq_completedSpectralPrimeOffDiagonalChannel
      f).symm
  htime.trans (hchannels.trans hcontour)

/-- Trace-reconstruction convergence of the completed prime contour/time
visible coordinate-remainder window. -/
theorem finitePrimeContourTransportCoordinateRemainderWindow_tendsto_zero_ownerTraceReconstruction
    (f : ZetaAdmissibleFunction)
    (D : CompletedFiniteWindowPrimeDistributionReconstruction f) :
    Tendsto
      (fun N : ℕ => finitePrimeContourTransportCoordinateRemainderWindow N f)
      atTop
      (𝓝 0) :=
  finitePrimeContourTransportCoordinateRemainderWindow_tendsto_zero_ownerTailEstimate
    f D

end ZetaAdmissibleFunction

end
end LFunctions
end Boundary
