import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaZeroTail.ZetaPrimeRapidPower.ZetaPrimeTwoFaceCoordinates.ZetaPrimeContourTomography.TailEstimates.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaZeroTail.ZetaPrimeRapidPower.ZetaPrimeTwoFaceCoordinates.ZetaPrimeContourTomography.TailEstimates.VisibleRemainderConvergence
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaCompletedHilbertSource.ZetaHermitianPacket.PrimeCenterSamplingDecayParts.TraceBesselParts.PrimeWeightedSamplingBesselSource
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaCompletedHilbertSource.ZetaHermitianPacket.PrimeSpectralMajorantSummability

/-!
# Honest summed prime contour transport

This file assembles the visible-remainder transport.  It does not identify the
finite time and contour windows: their exact difference remains a named window
whose convergence is supplied separately.
-/

namespace Boundary
namespace LFunctions

noncomputable section

namespace ZetaAdmissibleFunction

/-- The contour coordinate majorant gives convergence of the contour window. -/
theorem finitePrimeContourWindow_tendsto_of_spectralMajorant
    (f : ZetaAdmissibleFunction)
    (hmajorant :
      Summable
        (fun index : ZetaPrimePowerIndex =>
          zetaCompletedPrimeSpectralCoordinateMajorant index f)) :
    Tendsto
      (fun N : ℕ =>
        finitePrimeContourRealizedTimeDistributionWindow N
          (convolutionAutocorrelation f))
      atTop
      (𝓝
        (completedPrimeContourRealizedTimeDistributionPairing
          (convolutionAutocorrelation f))) :=
  finitePrimeContourRealizedTimeDistributionWindow_tendsto_completedPairing_ownerTailEstimate
    f hmajorant

/-- Exact finite additive transport through the visible coordinate remainder. -/
theorem finitePrimeTimeWindow_add_coordinateRemainder_eq_contourWindow
    (f : ZetaAdmissibleFunction) (N : ℕ) :
    finitePrimeTimeDistributionWindow N (convolutionAutocorrelation f) +
        finitePrimeContourTransportCoordinateRemainderWindow N f =
      finitePrimeContourRealizedTimeDistributionWindow N
        (convolutionAutocorrelation f) :=
  finitePrimeTimeDistributionWindow_add_coordinateRemainderWindow N f

/-- Spectral-majorant summability and vanishing of the visible remainder construct
the honest completed summed prime contour/time transport. -/
noncomputable def completedSummedPrimeContourTimeTransport_of_remainder
    (f : ZetaAdmissibleFunction)
    (hmajorant :
      Summable
        (fun index : ZetaPrimePowerIndex =>
          zetaCompletedPrimeSpectralCoordinateMajorant index f))
    (hremainder :
      Tendsto
        (fun N : ℕ => finitePrimeContourTransportCoordinateRemainderWindow N f)
        atTop
        (𝓝 0)) :
    CompletedSummedPrimeContourTimeTransport f :=
  { timeWindow :=
      fun N : ℕ => finitePrimeTimeDistributionWindow N (convolutionAutocorrelation f)
    contourWindow :=
      fun N : ℕ =>
        finitePrimeContourRealizedTimeDistributionWindow N
          (convolutionAutocorrelation f)
    remainderWindow :=
      fun N : ℕ => finitePrimeContourTransportCoordinateRemainderWindow N f
    timeWindow_eq := fun N : ℕ => rfl
    contourWindow_eq := fun N : ℕ => rfl
    finite_additive_transport :=
      finitePrimeTimeWindow_add_coordinateRemainder_eq_contourWindow f
    timeWindow_tendsto := finitePrimeTimeDistributionWindow_tendsto_completed f
    remainderWindow_tendsto_zero := hremainder
    contourWindow_tendsto :=
      finitePrimeContourWindow_tendsto_of_spectralMajorant f hmajorant }

/-- Owner theorem for summed prime contour/time transport. -/
theorem completedSummedPrimeContourTimeTransport_owner
    (f : ZetaAdmissibleFunction)
    (hmajorant : Summable (fun index : ZetaPrimePowerIndex =>
      zetaCompletedPrimeSpectralCoordinateMajorant index f))
    (hcoordinateZero :
      Complex.re
          (zetaCompletedPrimeDefectKernelDiagonalDebtCoordinateTsum f) =
        0) :
    CompletedSummedPrimeContourTimeTransport f :=
  completedSummedPrimeContourTimeTransport_of_remainder
    f
    hmajorant
    (finitePrimeContourTransportCoordinateRemainderWindow_tendsto_zero_owner
      f)

/-- Explicit diagonal-debt real-coordinate `HasSum` inputs for the
autocorrelation probe construct the honest completed summed prime
contour/time transport. -/
theorem completedSummedPrimeContourTimeTransport_owner_of_autocorrelation_diagonalDebtCoordinate_re_hasSum
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
    CompletedSummedPrimeContourTimeTransport f :=
  completedPrimeContourTransportSummedTransport_of_diagonalDebtCoordinate_re_hasSum_owner
    f C Creflect hhasSum hhasSumReflect

/-- Pointwise diagonal-debt real-coordinate `HasSum` inputs for every
autocorrelation seed construct the completed summed prime transport family. -/
theorem completedSummedPrimeContourTimeTransport_family_owner_of_autocorrelation_diagonalDebtCoordinate_re_hasSum
    (C Creflect : ZetaAdmissibleFunction → ℝ)
    (hhasSum :
      ∀ f : ZetaAdmissibleFunction,
        HasSum
          (fun index : ZetaPrimePowerIndex =>
            Complex.re
              (zetaCompletedPrimeDefectKernelDiagonalDebtCoordinate
                index (convolutionAutocorrelation f)))
          (C f))
    (hhasSumReflect :
      ∀ f : ZetaAdmissibleFunction,
        HasSum
          (fun index : ZetaPrimePowerIndex =>
            Complex.re
              (zetaCompletedPrimeDefectKernelDiagonalDebtCoordinate
                index
                (ZetaAdmissibleFunction.reflect
                  (convolutionAutocorrelation f))))
          (Creflect f)) :
    ∀ f : ZetaAdmissibleFunction,
      CompletedSummedPrimeContourTimeTransport f :=
  fun f =>
    completedSummedPrimeContourTimeTransport_owner_of_autocorrelation_diagonalDebtCoordinate_re_hasSum
      f (C f) (Creflect f) (hhasSum f) (hhasSumReflect f)

/-- Summability of the diagonal-debt real-coordinate streams for every
autocorrelation seed constructs the completed summed prime transport family
with the canonical `tsum` values. -/
theorem completedSummedPrimeContourTimeTransport_family_owner_of_autocorrelation_diagonalDebtCoordinate_re_summable
    (hsummable :
      ∀ f : ZetaAdmissibleFunction,
        Summable
          (fun index : ZetaPrimePowerIndex =>
            Complex.re
              (zetaCompletedPrimeDefectKernelDiagonalDebtCoordinate
                index (convolutionAutocorrelation f))))
    (hsummableReflect :
      ∀ f : ZetaAdmissibleFunction,
        Summable
          (fun index : ZetaPrimePowerIndex =>
            Complex.re
              (zetaCompletedPrimeDefectKernelDiagonalDebtCoordinate
                index
                (ZetaAdmissibleFunction.reflect
                  (convolutionAutocorrelation f))))) :
    ∀ f : ZetaAdmissibleFunction,
      CompletedSummedPrimeContourTimeTransport f :=
  completedSummedPrimeContourTimeTransport_family_owner_of_autocorrelation_diagonalDebtCoordinate_re_hasSum
    (fun f : ZetaAdmissibleFunction =>
      ∑' index : ZetaPrimePowerIndex,
        Complex.re
          (zetaCompletedPrimeDefectKernelDiagonalDebtCoordinate
            index (convolutionAutocorrelation f)))
    (fun f : ZetaAdmissibleFunction =>
      ∑' index : ZetaPrimePowerIndex,
        Complex.re
          (zetaCompletedPrimeDefectKernelDiagonalDebtCoordinate
            index
            (ZetaAdmissibleFunction.reflect
              (convolutionAutocorrelation f))))
    (fun f : ZetaAdmissibleFunction => (hsummable f).hasSum)
    (fun f : ZetaAdmissibleFunction => (hsummableReflect f).hasSum)

/-- The trace-Bessel source gives the diagonal-debt real-coordinate
summability needed by every autocorrelation seed. -/
theorem autocorrelation_diagonalDebtCoordinate_re_summable_family_owner
    (f : ZetaAdmissibleFunction) :
    Summable
      (fun index : ZetaPrimePowerIndex =>
        Complex.re
          (zetaCompletedPrimeDefectKernelDiagonalDebtCoordinate
            index (convolutionAutocorrelation f))) :=
  zetaCompletedPrimeDefectKernelDiagonalDebtCoordinate_re_summable_traceBessel_source
    (convolutionAutocorrelation f)

/-- The trace-Bessel source gives the reflected diagonal-debt real-coordinate
summability needed by every autocorrelation seed. -/
theorem autocorrelation_reflect_diagonalDebtCoordinate_re_summable_family_owner
    (f : ZetaAdmissibleFunction) :
    Summable
      (fun index : ZetaPrimePowerIndex =>
        Complex.re
          (zetaCompletedPrimeDefectKernelDiagonalDebtCoordinate
            index
            (ZetaAdmissibleFunction.reflect
              (convolutionAutocorrelation f)))) :=
  zetaCompletedPrimeDefectKernelDiagonalDebtCoordinate_re_summable_traceBessel_source
    (ZetaAdmissibleFunction.reflect (convolutionAutocorrelation f))

/-- The trace-Bessel source constructs the completed summed prime transport
family for every autocorrelation seed. -/
theorem completedSummedPrimeContourTimeTransport_family_owner_traceBessel
    (f : ZetaAdmissibleFunction) :
    CompletedSummedPrimeContourTimeTransport f :=
  completedSummedPrimeContourTimeTransport_family_owner_of_autocorrelation_diagonalDebtCoordinate_re_summable
    autocorrelation_diagonalDebtCoordinate_re_summable_family_owner
    autocorrelation_reflect_diagonalDebtCoordinate_re_summable_family_owner
    f

end ZetaAdmissibleFunction

end
end LFunctions
end Boundary
