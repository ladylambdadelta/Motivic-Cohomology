import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaZeroTail.ZetaPrimeRapidPower.ZetaPrimeTwoFaceCoordinates.ZetaPrimeContourTomography.TailEstimates.Owner

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
          (convolutionAutocorrelation f))) := by
  exact finitePrimeContourRealizedTimeDistributionWindow_tendsto_completedPairing_ownerTailEstimate
    f hmajorant

/-- Exact finite additive transport through the visible coordinate remainder. -/
theorem finitePrimeTimeWindow_add_coordinateRemainder_eq_contourWindow
    (f : ZetaAdmissibleFunction) (N : ℕ) :
    finitePrimeTimeDistributionWindow N (convolutionAutocorrelation f) +
        finitePrimeContourTransportCoordinateRemainderWindow N f =
      finitePrimeContourRealizedTimeDistributionWindow N
        (convolutionAutocorrelation f) := by
  exact finitePrimeTimeDistributionWindow_add_coordinateRemainderWindow N f

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

end ZetaAdmissibleFunction

end
end LFunctions
end Boundary
