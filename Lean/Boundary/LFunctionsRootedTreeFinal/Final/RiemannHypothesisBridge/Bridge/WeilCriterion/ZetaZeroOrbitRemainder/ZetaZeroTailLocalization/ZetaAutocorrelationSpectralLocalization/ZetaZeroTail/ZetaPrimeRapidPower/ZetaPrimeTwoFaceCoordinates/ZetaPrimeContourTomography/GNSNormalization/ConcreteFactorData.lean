import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaZeroTail.ZetaPrimeRapidPower.ZetaPrimeTwoFaceCoordinates.ZetaPrimeContourTomography.GNSNormalization.Owner

/-!
# Concrete factor data wrapper for GNS normalization

This file contains the concrete-factor-data wrapper over the schedule-explicit
GNS normalization owner theorem.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open Filter
open scoped Topology

namespace ZetaAdmissibleFunction

/-- Completed prime finite-window/GNS contour realization.

This compatibility wrapper packages the two split prime owner facts under the
historical horizontal-decay owner name consumed by the finite-window transport
layer. -/
theorem completedPrimeContourFiniteWindowGNSRealization_ownerHorizontalDecay
    (S : CompletedPrimeContourTransportScheduledFamily)
    (hheight :
      S.height_schedule = completedPrimeContourTransportHeightSchedule_owner)
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
        (fun N : ℕ => completedPrimeContourTransportCoordinateRemainderTail N f)
        atTop
        (𝓝 0) :=
  completedPrimeFiniteWindowGNSContourRealization_identifies_rawSpectral_and_tail_tendsto
    S
    hheight
    f
    hPhi
    hHorizontal

/-- Completed prime finite-window/GNS contour realization from concrete separated
factor bounds on the scheduled horizontal carrier. -/
theorem completedPrimeContourFiniteWindowGNSRealization_of_concreteFactorData
    (S : CompletedPrimeContourTransportScheduledFamily)
    (hheight :
      S.height_schedule = completedPrimeContourTransportHeightSchedule_owner)
    (f : ZetaAdmissibleFunction)
    (hPhi : ZetaPhiAnalyticControl (convolutionAutocorrelation f))
    (D :
      CompletedPrimeContourTransportConcreteFactorData
        S.toScheduleGeometry) :
    completedPrimeContourRealizedFiniteWindowPairing f =
        completedPrimeContourRealizedTimeDistributionPairing
          (convolutionAutocorrelation f) ∧
      Tendsto
        (fun N : ℕ => completedPrimeContourTransportCoordinateRemainderTail N f)
        atTop
        (𝓝 0) :=
  completedPrimeContourFiniteWindowGNSRealization_ownerHorizontalDecay
    S
    hheight
    f
    hPhi
    (D.toScheduledHorizontalLogDerivControl f)

end ZetaAdmissibleFunction

end
end LFunctions
end Boundary
