import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Root.Unstable.Inputs.ImportedRectangles.Counts.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Root.Unstable.Inputs.ImportedRectangles.ArrowEndpoints.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Root.Unstable.Inputs.ImportedRectangles.LedgerRectangles.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Unstable.Inputs.ByKind.Payload.ImportedRectangles.Owner

/-!
# Root all-kind unstable input imported rectangles

This file exposes endpoint imported-rectangle lists for hom and inverse arrows
of all six named unstable localization isomorphisms at the motive-root
namespace.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- By-kind descent-channel hom endpoint rectangles are source followed by target. -/
theorem TraceAnalyticMotive.unstableByKindDescentChannelIso_hom_endpointImportedRectangles
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.descentChannelIso
      source
      target).hom.endpointImportedRectangles =
      (TraceLocalizationInput.descentChannel source target).sourceObject.importedRectangles ++
        (TraceLocalizationInput.descentChannel source target).targetObject.importedRectangles :=
  TraceUnstableAnalyticMotive.descentChannelIso_hom_endpointImportedRectangles
    source
    target

/-- By-kind descent-channel inverse endpoint rectangles are target followed by source. -/
theorem TraceAnalyticMotive.unstableByKindDescentChannelIso_inv_endpointImportedRectangles
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.descentChannelIso
      source
      target).inv.endpointImportedRectangles =
      (TraceLocalizationInput.descentChannel source target).targetObject.importedRectangles ++
        (TraceLocalizationInput.descentChannel source target).sourceObject.importedRectangles :=
  TraceUnstableAnalyticMotive.descentChannelIso_inv_endpointImportedRectangles
    source
    target

/-- By-kind descent-refinement hom endpoint rectangles are source followed by target. -/
theorem TraceAnalyticMotive.unstableByKindDescentRefinementIso_hom_endpointImportedRectangles
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.descentRefinementIso
      source
      target).hom.endpointImportedRectangles =
      (TraceLocalizationInput.descentRefinement source target).sourceObject.importedRectangles ++
        (TraceLocalizationInput.descentRefinement source target).targetObject.importedRectangles :=
  TraceUnstableAnalyticMotive.descentRefinementIso_hom_endpointImportedRectangles
    source
    target

/-- By-kind descent-refinement inverse endpoint rectangles are target followed by source. -/
theorem TraceAnalyticMotive.unstableByKindDescentRefinementIso_inv_endpointImportedRectangles
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.descentRefinementIso
      source
      target).inv.endpointImportedRectangles =
      (TraceLocalizationInput.descentRefinement source target).targetObject.importedRectangles ++
        (TraceLocalizationInput.descentRefinement source target).sourceObject.importedRectangles :=
  TraceUnstableAnalyticMotive.descentRefinementIso_inv_endpointImportedRectangles
    source
    target

/-- By-kind descent-schedule hom endpoint rectangles are source followed by target. -/
theorem TraceAnalyticMotive.unstableByKindDescentScheduleIso_hom_endpointImportedRectangles
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.descentScheduleIso
      source
      target).hom.endpointImportedRectangles =
      (TraceLocalizationInput.descentSchedule source target).sourceObject.importedRectangles ++
        (TraceLocalizationInput.descentSchedule source target).targetObject.importedRectangles :=
  TraceUnstableAnalyticMotive.descentScheduleIso_hom_endpointImportedRectangles
    source
    target

/-- By-kind descent-schedule inverse endpoint rectangles are target followed by source. -/
theorem TraceAnalyticMotive.unstableByKindDescentScheduleIso_inv_endpointImportedRectangles
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.descentScheduleIso
      source
      target).inv.endpointImportedRectangles =
      (TraceLocalizationInput.descentSchedule source target).targetObject.importedRectangles ++
        (TraceLocalizationInput.descentSchedule source target).sourceObject.importedRectangles :=
  TraceUnstableAnalyticMotive.descentScheduleIso_inv_endpointImportedRectangles
    source
    target

/-- By-kind interval-Stokes hom endpoint rectangles are source followed by target. -/
theorem TraceAnalyticMotive.unstableByKindIntervalStokesIso_hom_endpointImportedRectangles
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.intervalStokesIso
      source
      target).hom.endpointImportedRectangles =
      (TraceLocalizationInput.intervalStokes source target).sourceObject.importedRectangles ++
        (TraceLocalizationInput.intervalStokes source target).targetObject.importedRectangles :=
  TraceUnstableAnalyticMotive.intervalStokesIso_hom_endpointImportedRectangles
    source
    target

/-- By-kind interval-Stokes inverse endpoint rectangles are target followed by source. -/
theorem TraceAnalyticMotive.unstableByKindIntervalStokesIso_inv_endpointImportedRectangles
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.intervalStokesIso
      source
      target).inv.endpointImportedRectangles =
      (TraceLocalizationInput.intervalStokes source target).targetObject.importedRectangles ++
        (TraceLocalizationInput.intervalStokes source target).sourceObject.importedRectangles :=
  TraceUnstableAnalyticMotive.intervalStokesIso_inv_endpointImportedRectangles
    source
    target

/-- By-kind interval-Fubini hom endpoint rectangles are source followed by target. -/
theorem TraceAnalyticMotive.unstableByKindIntervalFubiniIso_hom_endpointImportedRectangles
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.intervalFubiniIso
      source
      target).hom.endpointImportedRectangles =
      (TraceLocalizationInput.intervalFubini source target).sourceObject.importedRectangles ++
        (TraceLocalizationInput.intervalFubini source target).targetObject.importedRectangles :=
  TraceUnstableAnalyticMotive.intervalFubiniIso_hom_endpointImportedRectangles
    source
    target

/-- By-kind interval-Fubini inverse endpoint rectangles are target followed by source. -/
theorem TraceAnalyticMotive.unstableByKindIntervalFubiniIso_inv_endpointImportedRectangles
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.intervalFubiniIso
      source
      target).inv.endpointImportedRectangles =
      (TraceLocalizationInput.intervalFubini source target).targetObject.importedRectangles ++
        (TraceLocalizationInput.intervalFubini source target).sourceObject.importedRectangles :=
  TraceUnstableAnalyticMotive.intervalFubiniIso_inv_endpointImportedRectangles
    source
    target

/-- By-kind Tate-weight-drop hom endpoint rectangles are source followed by target. -/
theorem TraceAnalyticMotive.unstableByKindTateWeightDropIso_hom_endpointImportedRectangles
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.tateWeightDropIso
      source
      target).hom.endpointImportedRectangles =
      (TraceLocalizationInput.tateWeightDrop source target).sourceObject.importedRectangles ++
        (TraceLocalizationInput.tateWeightDrop source target).targetObject.importedRectangles :=
  TraceUnstableAnalyticMotive.tateWeightDropIso_hom_endpointImportedRectangles
    source
    target

/-- By-kind Tate-weight-drop inverse endpoint rectangles are target followed by source. -/
theorem TraceAnalyticMotive.unstableByKindTateWeightDropIso_inv_endpointImportedRectangles
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.tateWeightDropIso
      source
      target).inv.endpointImportedRectangles =
      (TraceLocalizationInput.tateWeightDrop source target).targetObject.importedRectangles ++
        (TraceLocalizationInput.tateWeightDrop source target).sourceObject.importedRectangles :=
  TraceUnstableAnalyticMotive.tateWeightDropIso_inv_endpointImportedRectangles
    source
    target

end AnalyticMotives
end LFunctions
end Boundary
