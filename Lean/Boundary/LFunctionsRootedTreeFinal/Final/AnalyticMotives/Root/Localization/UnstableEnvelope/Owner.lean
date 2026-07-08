import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Root.Localization.UnstableEnvelope.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Root.Localization.Cancellation.Owner

/-!
# Top-root unstable localization envelope

This file exposes the unstable-envelope isomorphism identifications induced by
the calculus localization inputs at the public root.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- The analytic-motives root exposes unstable descent-channel inversion. -/
theorem AnalyticMotivesRoot.unstableDescentChannelIso_eq
    (source target : QTraceExpression) :
    TraceUnstableAnalyticMotive.descentChannelIso source target =
      TraceLocalizationInput.descentChannelLocalizedIso source target :=
  TraceAnalyticMotive.unstableDescentChannelIso_eq
    source
    target

/-- The analytic-motives root exposes unstable descent-refinement inversion. -/
theorem AnalyticMotivesRoot.unstableDescentRefinementIso_eq
    (source target : QTraceExpression) :
    TraceUnstableAnalyticMotive.descentRefinementIso source target =
      TraceLocalizationInput.descentRefinementLocalizedIso source target :=
  TraceAnalyticMotive.unstableDescentRefinementIso_eq
    source
    target

/-- The analytic-motives root exposes unstable descent-schedule inversion. -/
theorem AnalyticMotivesRoot.unstableDescentScheduleIso_eq
    (source target : QTraceExpression) :
    TraceUnstableAnalyticMotive.descentScheduleIso source target =
      TraceLocalizationInput.descentScheduleLocalizedIso source target :=
  TraceAnalyticMotive.unstableDescentScheduleIso_eq
    source
    target

/-- The analytic-motives root exposes unstable interval-Stokes inversion. -/
theorem AnalyticMotivesRoot.unstableIntervalStokesIso_eq
    (source target : QTraceExpression) :
    TraceUnstableAnalyticMotive.intervalStokesIso source target =
      TraceLocalizationInput.intervalStokesLocalizedIso source target :=
  TraceAnalyticMotive.unstableIntervalStokesIso_eq
    source
    target

/-- The analytic-motives root exposes unstable interval-Fubini inversion. -/
theorem AnalyticMotivesRoot.unstableIntervalFubiniIso_eq
    (source target : QTraceExpression) :
    TraceUnstableAnalyticMotive.intervalFubiniIso source target =
      TraceLocalizationInput.intervalFubiniLocalizedIso source target :=
  TraceAnalyticMotive.unstableIntervalFubiniIso_eq
    source
    target

/-- The analytic-motives root exposes unstable Tate-weight-drop inversion. -/
theorem AnalyticMotivesRoot.unstableTateWeightDropIso_eq
    (source target : QTraceExpression) :
    TraceUnstableAnalyticMotive.tateWeightDropIso source target =
      TraceLocalizationInput.tateWeightDropLocalizedIso source target :=
  TraceAnalyticMotive.unstableTateWeightDropIso_eq
    source
    target

end AnalyticMotives
end LFunctions
end Boundary
