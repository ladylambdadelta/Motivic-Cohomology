import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaZeroTail.ZetaPrimeRapidPower.ZetaPrimeTwoFaceCoordinates.ZetaPrimeContourTomography.TailEstimates.TraceReconstruction
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaZeroTail.ZetaPrimeRapidPower.ZetaPrimeTwoFaceCoordinates.ZetaPrimeContourTomography.TailEstimates.TraceTransportConditional

/-!
# Conditional completed prime trace reconstruction

This file exposes trace reconstruction consequences from explicit completed
diagonal-debt real-coordinate `HasSum` inputs.
-/

namespace Boundary
namespace LFunctions

noncomputable section

namespace ZetaAdmissibleFunction

/-- Explicit diagonal-debt real-coordinate `HasSum` inputs transport the raw
diagonal-debt coordinate presentation to the owner diagonal-debt scalar at the
trace reconstruction level. -/
theorem zetaCompletedPrimeDefectKernelDiagonalDebtCoordinateTsum_re_eq_ownerDiagonalDebt_re_of_diagonalDebtCoordinate_re_hasSum_ownerTraceReconstruction
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
        Creflect) :
    Complex.re (zetaCompletedPrimeDefectKernelDiagonalDebtCoordinateTsum f) =
      Complex.re (zetaCompletedPrimeDefectKernelDiagonalDebt f) :=
  zetaCompletedPrimeDefectKernelDiagonalDebtCoordinateTsum_re_eq_ownerDiagonalDebt_re_of_diagonalDebtCoordinate_re_hasSum_source_core
    f C Creflect hhasSum hhasSumReflect

/-- Explicit diagonal-debt real-coordinate `HasSum` inputs give owner
transport for the completed prime-defect residual coordinates at the trace
reconstruction level. -/
theorem completedPrimeDefectCoordinateOwnerTransport_of_diagonalDebtCoordinate_re_hasSum_ownerTraceReconstruction
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
        Creflect) :
    CompletedPrimeDefectCoordinateOwnerTransport f :=
  completedPrimeDefectCoordinateOwnerTransport_of_diagonalDebtCoordinate_re_hasSum_traceTransport_source_core
    f C Creflect hhasSum hhasSumReflect

/-- Explicit diagonal-debt real-coordinate `HasSum` inputs give convergence of
completed diagonal-debt real windows to the owner diagonal-debt scalar at the
trace reconstruction level. -/
theorem zetaCompletedPrimeDefectKernelDiagonalDebtRealWindow_tendsto_ownerDiagonalDebt_re_of_diagonalDebtCoordinate_re_hasSum_ownerTraceReconstruction
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
        Creflect) :
    Tendsto
      (fun N : ℕ => zetaCompletedPrimeDefectKernelDiagonalDebtRealWindow N f)
      atTop
      (𝓝 (Complex.re (zetaCompletedPrimeDefectKernelDiagonalDebt f))) :=
  zetaCompletedPrimeDefectKernelDiagonalDebtRealWindow_tendsto_ownerDiagonalDebt_re_of_diagonalDebtCoordinate_re_hasSum_source_core
    f C Creflect hhasSum hhasSumReflect

/-- Explicit diagonal-debt real-coordinate `HasSum` inputs transport the raw
positive coordinate presentation to the owner completed positive prime-defect
channel at the trace reconstruction level. -/
theorem zetaCompletedPrimeDefectKernelPositiveCoordinateTsumRe_eq_ownerPositiveChannel_of_diagonalDebtCoordinate_re_hasSum_ownerTraceReconstruction
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
        Creflect) :
    zetaCompletedPrimeDefectKernelPositiveCoordinateTsumRe f =
      completedPrimeDefectKernelPositiveChannel f :=
  zetaCompletedPrimeDefectKernelPositiveCoordinateTsumRe_eq_ownerPositiveChannel_of_diagonalDebtCoordinate_re_hasSum_source_core
    f C Creflect hhasSum hhasSumReflect

/-- Explicit diagonal-debt real-coordinate `HasSum` inputs give the spectral
coordinate majorant used by completed finite trace reconstruction. -/
theorem zetaCompletedPrimeSpectralCoordinateMajorant_summable_of_diagonalDebtCoordinate_re_hasSum_ownerTraceReconstruction
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
        Creflect) :
    Summable
      (fun index : ZetaPrimePowerIndex =>
        zetaCompletedPrimeSpectralCoordinateMajorant index f) :=
  zetaCompletedPrimeSpectralCoordinateMajorant_summable_of_diagonalDebtCoordinate_re_hasSum_positiveRealWindowLimit
    f C Creflect hhasSum hhasSumReflect

/-- Explicit diagonal-debt real-coordinate `HasSum` inputs for the
autocorrelation probe give the spectral coordinate majorant needed by the
transport coordinate remainder. -/
theorem zetaCompletedPrimeSpectralCoordinateMajorant_summable_of_autocorrelation_diagonalDebtCoordinate_re_hasSum_ownerTraceReconstruction
    (f : ZetaAdmissibleFunction) (C Creflect : ℝ)
    (hhasSum :
      HasSum
        (fun index : ZetaPrimePowerIndex =>
          Complex.re
            (zetaCompletedPrimeDefectKernelDiagonalDebtCoordinate
              index (convolutionAutocorrelation f)))
        C)
    (hhasSumReflect :
      HasSum
        (fun index : ZetaPrimePowerIndex =>
          Complex.re
            (zetaCompletedPrimeDefectKernelDiagonalDebtCoordinate
              index
              (ZetaAdmissibleFunction.reflect
                (convolutionAutocorrelation f))))
        Creflect) :
    Summable
      (fun index : ZetaPrimePowerIndex =>
        zetaCompletedPrimeSpectralCoordinateMajorant index
          (convolutionAutocorrelation f)) :=
  zetaCompletedPrimeSpectralCoordinateMajorant_summable_of_diagonalDebtCoordinate_re_hasSum_positiveRealWindowLimit
    (convolutionAutocorrelation f) C Creflect hhasSum hhasSumReflect

/-- Explicit diagonal-debt real-coordinate `HasSum` inputs give convergence of
finite completed contour-realized prime windows to the completed pairing. -/
theorem finitePrimeContourRealizedTimeDistributionWindow_tendsto_completedPairing_of_diagonalDebtCoordinate_re_hasSum
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
        Creflect) :
    Tendsto
      (fun N : ℕ =>
        finitePrimeContourRealizedTimeDistributionWindow N
          (convolutionAutocorrelation f))
      atTop
      (𝓝 (completedPrimeContourRealizedTimeDistributionPairing
        (convolutionAutocorrelation f))) :=
  finitePrimeContourRealizedTimeDistributionWindow_tendsto_completedPairing_ownerTailEstimate
    f
    (zetaCompletedPrimeSpectralCoordinateMajorant_summable_of_diagonalDebtCoordinate_re_hasSum_ownerTraceReconstruction
      f C Creflect hhasSum hhasSumReflect)

/-- Explicit diagonal-debt real-coordinate `HasSum` inputs for the
autocorrelation probe give trace-reconstruction convergence of the completed
prime contour/time visible coordinate-remainder window. -/
theorem finitePrimeContourTransportCoordinateRemainderWindow_tendsto_zero_of_diagonalDebtCoordinate_re_hasSum_ownerTraceReconstruction
    (f : ZetaAdmissibleFunction) (C Creflect : ℝ)
    (hhasSum :
      HasSum
        (fun index : ZetaPrimePowerIndex =>
          Complex.re
            (zetaCompletedPrimeDefectKernelDiagonalDebtCoordinate
              index (convolutionAutocorrelation f)))
        C)
    (hhasSumReflect :
      HasSum
        (fun index : ZetaPrimePowerIndex =>
          Complex.re
            (zetaCompletedPrimeDefectKernelDiagonalDebtCoordinate
              index
              (ZetaAdmissibleFunction.reflect
                (convolutionAutocorrelation f))))
        Creflect) :
    Tendsto
      (fun N : ℕ => finitePrimeContourTransportCoordinateRemainderWindow N f)
      atTop
      (𝓝 0) :=
  finitePrimeContourTransportCoordinateRemainderWindow_tendsto_zero_of_pairingEquality
    f
    (zetaCompletedPrimeSpectralCoordinateMajorant_summable_of_autocorrelation_diagonalDebtCoordinate_re_hasSum_ownerTraceReconstruction
      f C Creflect hhasSum hhasSumReflect)
    (completedPrimeDistributionTransport_timePairing_eq_contourRealizedPairing_ownerTraceReconstruction
      f)

end ZetaAdmissibleFunction

end
end LFunctions
end Boundary
