import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaZeroTail.ZetaPrimeRapidPower.ZetaPrimeTwoFaceCoordinates.ZetaPrimeContourTomography.GNSNormalization.Core

/-!
# Schedule-parametric GNS tail normalization

This file owns the GNS normalization statements before specializing the prime
contour height schedule.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open Filter
open scoped Topology

namespace ZetaAdmissibleFunction

/-- The scheduled prime coordinate-remainder tail vanishes after finite-window
renormalization. -/
theorem completedPrimeContourTransportCoordinateRemainderTailAt_tendsto_zero
    (S : CompletedPrimeContourTransportScheduledFamily)
    (f : ZetaAdmissibleFunction)
    (hPhi : ZetaPhiAnalyticControl (convolutionAutocorrelation f))
    (hHorizontal :
      ExplicitFormulaScheduledHorizontalLogDerivControl
        (convolutionAutocorrelation f)
        completedPrimeContourTransportFamily
        S.height_schedule) :
    Tendsto
      (fun N : ℕ =>
        completedPrimeContourTransportCoordinateRemainderTailAt
          S.height_schedule N f)
      atTop
      (𝓝 0) := by
  exact
    completedPrimeContourTransportCoordinateRemainderTailAt_tendsto_zero_ownerTailEstimate
      S
      f
      hPhi
      hHorizontal

/-- Completed prime contour normalization-to-heart transport, schedule-parametrically. -/
theorem completedPrimeContourNormalizationToHeartAt_transport
    (S : CompletedPrimeContourTransportScheduledFamily)
    (f : ZetaAdmissibleFunction)
    (hPhi : ZetaPhiAnalyticControl (convolutionAutocorrelation f))
    (hHorizontal :
      ExplicitFormulaScheduledHorizontalLogDerivControl
        (convolutionAutocorrelation f)
        completedPrimeContourTransportFamily
        S.height_schedule) :
    completedPrimeContourRealizedFiniteWindowPairing f =
        completedPrimeContourGNSHeartScalar f ∧
      Tendsto
        (fun N : ℕ =>
          completedPrimeContourTransportCoordinateRemainderTailAt
            S.height_schedule N f)
        atTop
        (𝓝 0) := by
  exact
    ⟨completedPrimeContourRealizedFiniteWindowPairing_eq_GNSHeartScalar S f,
      completedPrimeContourTransportCoordinateRemainderTailAt_tendsto_zero
        S f hPhi hHorizontal⟩

/-- Prime tail convergence after finite-window contour normalization,
schedule-parametrically. -/
theorem completedPrimeContourPrimeTailAtRenormalization_tendsto_zero
    (S : CompletedPrimeContourTransportScheduledFamily)
    (f : ZetaAdmissibleFunction)
    (hPhi : ZetaPhiAnalyticControl (convolutionAutocorrelation f))
    (hHorizontal :
      ExplicitFormulaScheduledHorizontalLogDerivControl
        (convolutionAutocorrelation f)
        completedPrimeContourTransportFamily
        S.height_schedule) :
    Tendsto
      (fun N : ℕ =>
        completedPrimeContourTransportCoordinateRemainderTailAt
          S.height_schedule N f)
      atTop
      (𝓝 0) := by
  exact
    completedPrimeContourTransportCoordinateRemainderTailAt_tendsto_zero
      S f hPhi hHorizontal

/-- Completed finite-window/GNS contour reconstruction at the ordered-heart scalar,
schedule-parametrically. -/
theorem completedPrimeFiniteWindowGNSContourReconstructionAt_twoFaceComparison_and_tailConvergence
    (S : CompletedPrimeContourTransportScheduledFamily)
    (f : ZetaAdmissibleFunction)
    (hPhi : ZetaPhiAnalyticControl (convolutionAutocorrelation f))
    (hHorizontal :
      ExplicitFormulaScheduledHorizontalLogDerivControl
        (convolutionAutocorrelation f)
        completedPrimeContourTransportFamily
        S.height_schedule) :
    completedPrimeContourRealizedFiniteWindowPairing f =
        completedPrimeContourGNSHeartScalar f ∧
      Tendsto
        (fun N : ℕ =>
          completedPrimeContourTransportCoordinateRemainderTailAt
            S.height_schedule N f)
        atTop
        (𝓝 0) := by
  exact
    ⟨completedPrimeContourRealizedFiniteWindowPairing_eq_GNSHeartScalar S f,
      completedPrimeContourPrimeTailAtRenormalization_tendsto_zero
        S f hPhi hHorizontal⟩

/-- The omitted scheduled prime tail vanishes after finite-window/GNS contour transport. -/
theorem completedPrimeFiniteWindowGNSContourRealization_primeTailAt_tendsto_after_finiteWindowTransport
    (S : CompletedPrimeContourTransportScheduledFamily)
    (f : ZetaAdmissibleFunction)
    (hPhi : ZetaPhiAnalyticControl (convolutionAutocorrelation f))
    (hHorizontal :
      ExplicitFormulaScheduledHorizontalLogDerivControl
        (convolutionAutocorrelation f)
        completedPrimeContourTransportFamily
        S.height_schedule) :
    Tendsto
      (fun N : ℕ =>
        completedPrimeContourTransportCoordinateRemainderTailAt
          S.height_schedule N f)
      atTop
      (𝓝 0) := by
  exact
    completedPrimeContourTransportCoordinateRemainderTailAt_tendsto_zero
      S f hPhi hHorizontal

/-- Completed prime finite-window/GNS contour realization, schedule-parametrically. -/
theorem completedPrimeFiniteWindowGNSContourRealizationAt_identifies_rawSpectral_and_tail_tendsto
    (S : CompletedPrimeContourTransportScheduledFamily)
    (f : ZetaAdmissibleFunction)
    (hPhi : ZetaPhiAnalyticControl (convolutionAutocorrelation f))
    (hHorizontal :
      ExplicitFormulaScheduledHorizontalLogDerivControl
        (convolutionAutocorrelation f)
        completedPrimeContourTransportFamily
        S.height_schedule) :
    completedPrimeContourRealizedFiniteWindowPairing f =
        completedPrimeContourRealizedTimeDistributionPairing
          (convolutionAutocorrelation f) ∧
      Tendsto
        (fun N : ℕ =>
          completedPrimeContourTransportCoordinateRemainderTailAt
            S.height_schedule N f)
        atTop
        (𝓝 0) := by
  have hgns :
    completedPrimeContourRealizedFiniteWindowPairing f =
        completedPrimeContourGNSHeartScalar f :=
    completedPrimeContourRealizedFiniteWindowPairing_eq_GNSHeartScalar S f
  have hraw :
      completedPrimeContourRealizedTimeDistributionPairing
          (convolutionAutocorrelation f) =
        completedPrimeContourGNSHeartScalar f :=
    completedPrimeContourRawSpectralPairing_eq_twoFaceGNSBoundaryCoefficient_re f
  have htail :
      Tendsto
        (fun N : ℕ =>
          completedPrimeContourTransportCoordinateRemainderTailAt
            S.height_schedule N f)
        atTop
        (𝓝 0) :=
    completedPrimeFiniteWindowGNSContourRealization_primeTailAt_tendsto_after_finiteWindowTransport
      S
      f
      hPhi
      hHorizontal
  exact ⟨hgns.trans hraw.symm, htail⟩

end ZetaAdmissibleFunction

end
end LFunctions
end Boundary
