import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Root.Localization.Cancellation.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Unstable.Owner

/-!
# Motive-root unstable localization envelope

This file exposes the unstable-envelope isomorphism identifications induced by
the calculus localization inputs.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- The unstable envelope exposes descent-channel inversion. -/
theorem TraceAnalyticMotive.unstableDescentChannelIso_eq
    (source target : QTraceExpression) :
    TraceUnstableAnalyticMotive.descentChannelIso source target =
      TraceLocalizationInput.descentChannelLocalizedIso source target :=
  TraceUnstableAnalyticMotive.descentChannelIso_eq
    source
    target

/-- The unstable envelope exposes descent-refinement inversion. -/
theorem TraceAnalyticMotive.unstableDescentRefinementIso_eq
    (source target : QTraceExpression) :
    TraceUnstableAnalyticMotive.descentRefinementIso source target =
      TraceLocalizationInput.descentRefinementLocalizedIso source target :=
  TraceUnstableAnalyticMotive.descentRefinementIso_eq
    source
    target

/-- The unstable envelope exposes descent-schedule inversion. -/
theorem TraceAnalyticMotive.unstableDescentScheduleIso_eq
    (source target : QTraceExpression) :
    TraceUnstableAnalyticMotive.descentScheduleIso source target =
      TraceLocalizationInput.descentScheduleLocalizedIso source target :=
  TraceUnstableAnalyticMotive.descentScheduleIso_eq
    source
    target

/-- The unstable envelope exposes interval-Stokes inversion. -/
theorem TraceAnalyticMotive.unstableIntervalStokesIso_eq
    (source target : QTraceExpression) :
    TraceUnstableAnalyticMotive.intervalStokesIso source target =
      TraceLocalizationInput.intervalStokesLocalizedIso source target :=
  TraceUnstableAnalyticMotive.intervalStokesIso_eq
    source
    target

/-- The unstable envelope exposes interval-Fubini inversion. -/
theorem TraceAnalyticMotive.unstableIntervalFubiniIso_eq
    (source target : QTraceExpression) :
    TraceUnstableAnalyticMotive.intervalFubiniIso source target =
      TraceLocalizationInput.intervalFubiniLocalizedIso source target :=
  TraceUnstableAnalyticMotive.intervalFubiniIso_eq
    source
    target

/-- The unstable envelope exposes Tate-weight-drop inversion. -/
theorem TraceAnalyticMotive.unstableTateWeightDropIso_eq
    (source target : QTraceExpression) :
    TraceUnstableAnalyticMotive.tateWeightDropIso source target =
      TraceLocalizationInput.tateWeightDropLocalizedIso source target :=
  TraceUnstableAnalyticMotive.tateWeightDropIso_eq
    source
    target

end AnalyticMotives
end LFunctions
end Boundary
