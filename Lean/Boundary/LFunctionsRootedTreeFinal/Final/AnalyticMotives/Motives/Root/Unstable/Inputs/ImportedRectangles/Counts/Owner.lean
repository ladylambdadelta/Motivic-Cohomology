import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Unstable.Inputs.ByKind.Payload.ImportedRectangles.Counts.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Root.Unstable.Inputs.ImportedRectangles.Counts.ArrowEndpoints.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Root.Unstable.Inputs.ImportedRectangles.Counts.Lengths.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Root.Unstable.Inputs.ImportedRectangles.Counts.LedgerCounts.Owner

/-!
# Root all-kind unstable input imported-rectangle counts

This file exposes endpoint imported-rectangle counts for hom and inverse arrows
of all six named unstable localization isomorphisms at the motive-root
namespace.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- By-kind descent-channel hom endpoint count is source count plus target count. -/
theorem TraceAnalyticMotive.unstableByKindDescentChannelIso_hom_endpointImportedRectangleCount
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.descentChannelIso
      source
      target).hom.endpointImportedRectangleCount =
      (TraceLocalizationInput.descentChannel source target).sourceObject.importedRectangleCount +
        (TraceLocalizationInput.descentChannel source target).targetObject.importedRectangleCount :=
  TraceUnstableAnalyticMotive.descentChannelIso_hom_endpointImportedRectangleCount
    source
    target

/-- By-kind descent-channel inverse endpoint count is target count plus source count. -/
theorem TraceAnalyticMotive.unstableByKindDescentChannelIso_inv_endpointImportedRectangleCount
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.descentChannelIso
      source
      target).inv.endpointImportedRectangleCount =
      (TraceLocalizationInput.descentChannel source target).targetObject.importedRectangleCount +
        (TraceLocalizationInput.descentChannel source target).sourceObject.importedRectangleCount :=
  TraceUnstableAnalyticMotive.descentChannelIso_inv_endpointImportedRectangleCount
    source
    target

/-- By-kind descent-refinement hom endpoint count is source count plus target count. -/
theorem TraceAnalyticMotive.unstableByKindDescentRefinementIso_hom_endpointImportedRectangleCount
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.descentRefinementIso
      source
      target).hom.endpointImportedRectangleCount =
      (TraceLocalizationInput.descentRefinement source target).sourceObject.importedRectangleCount +
        (TraceLocalizationInput.descentRefinement source target).targetObject.importedRectangleCount :=
  TraceUnstableAnalyticMotive.descentRefinementIso_hom_endpointImportedRectangleCount
    source
    target

/-- By-kind descent-refinement inverse endpoint count is target count plus source count. -/
theorem TraceAnalyticMotive.unstableByKindDescentRefinementIso_inv_endpointImportedRectangleCount
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.descentRefinementIso
      source
      target).inv.endpointImportedRectangleCount =
      (TraceLocalizationInput.descentRefinement source target).targetObject.importedRectangleCount +
        (TraceLocalizationInput.descentRefinement source target).sourceObject.importedRectangleCount :=
  TraceUnstableAnalyticMotive.descentRefinementIso_inv_endpointImportedRectangleCount
    source
    target

/-- By-kind descent-schedule hom endpoint count is source count plus target count. -/
theorem TraceAnalyticMotive.unstableByKindDescentScheduleIso_hom_endpointImportedRectangleCount
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.descentScheduleIso
      source
      target).hom.endpointImportedRectangleCount =
      (TraceLocalizationInput.descentSchedule source target).sourceObject.importedRectangleCount +
        (TraceLocalizationInput.descentSchedule source target).targetObject.importedRectangleCount :=
  TraceUnstableAnalyticMotive.descentScheduleIso_hom_endpointImportedRectangleCount
    source
    target

/-- By-kind descent-schedule inverse endpoint count is target count plus source count. -/
theorem TraceAnalyticMotive.unstableByKindDescentScheduleIso_inv_endpointImportedRectangleCount
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.descentScheduleIso
      source
      target).inv.endpointImportedRectangleCount =
      (TraceLocalizationInput.descentSchedule source target).targetObject.importedRectangleCount +
        (TraceLocalizationInput.descentSchedule source target).sourceObject.importedRectangleCount :=
  TraceUnstableAnalyticMotive.descentScheduleIso_inv_endpointImportedRectangleCount
    source
    target

/-- By-kind interval-Stokes hom endpoint count is source count plus target count. -/
theorem TraceAnalyticMotive.unstableByKindIntervalStokesIso_hom_endpointImportedRectangleCount
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.intervalStokesIso
      source
      target).hom.endpointImportedRectangleCount =
      (TraceLocalizationInput.intervalStokes source target).sourceObject.importedRectangleCount +
        (TraceLocalizationInput.intervalStokes source target).targetObject.importedRectangleCount :=
  TraceUnstableAnalyticMotive.intervalStokesIso_hom_endpointImportedRectangleCount
    source
    target

/-- By-kind interval-Stokes inverse endpoint count is target count plus source count. -/
theorem TraceAnalyticMotive.unstableByKindIntervalStokesIso_inv_endpointImportedRectangleCount
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.intervalStokesIso
      source
      target).inv.endpointImportedRectangleCount =
      (TraceLocalizationInput.intervalStokes source target).targetObject.importedRectangleCount +
        (TraceLocalizationInput.intervalStokes source target).sourceObject.importedRectangleCount :=
  TraceUnstableAnalyticMotive.intervalStokesIso_inv_endpointImportedRectangleCount
    source
    target

/-- By-kind interval-Fubini hom endpoint count is source count plus target count. -/
theorem TraceAnalyticMotive.unstableByKindIntervalFubiniIso_hom_endpointImportedRectangleCount
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.intervalFubiniIso
      source
      target).hom.endpointImportedRectangleCount =
      (TraceLocalizationInput.intervalFubini source target).sourceObject.importedRectangleCount +
        (TraceLocalizationInput.intervalFubini source target).targetObject.importedRectangleCount :=
  TraceUnstableAnalyticMotive.intervalFubiniIso_hom_endpointImportedRectangleCount
    source
    target

/-- By-kind interval-Fubini inverse endpoint count is target count plus source count. -/
theorem TraceAnalyticMotive.unstableByKindIntervalFubiniIso_inv_endpointImportedRectangleCount
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.intervalFubiniIso
      source
      target).inv.endpointImportedRectangleCount =
      (TraceLocalizationInput.intervalFubini source target).targetObject.importedRectangleCount +
        (TraceLocalizationInput.intervalFubini source target).sourceObject.importedRectangleCount :=
  TraceUnstableAnalyticMotive.intervalFubiniIso_inv_endpointImportedRectangleCount
    source
    target

/-- By-kind Tate-weight-drop hom endpoint count is source count plus target count. -/
theorem TraceAnalyticMotive.unstableByKindTateWeightDropIso_hom_endpointImportedRectangleCount
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.tateWeightDropIso
      source
      target).hom.endpointImportedRectangleCount =
      (TraceLocalizationInput.tateWeightDrop source target).sourceObject.importedRectangleCount +
        (TraceLocalizationInput.tateWeightDrop source target).targetObject.importedRectangleCount :=
  TraceUnstableAnalyticMotive.tateWeightDropIso_hom_endpointImportedRectangleCount
    source
    target

/-- By-kind Tate-weight-drop inverse endpoint count is target count plus source count. -/
theorem TraceAnalyticMotive.unstableByKindTateWeightDropIso_inv_endpointImportedRectangleCount
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.tateWeightDropIso
      source
      target).inv.endpointImportedRectangleCount =
      (TraceLocalizationInput.tateWeightDrop source target).targetObject.importedRectangleCount +
        (TraceLocalizationInput.tateWeightDrop source target).sourceObject.importedRectangleCount :=
  TraceUnstableAnalyticMotive.tateWeightDropIso_inv_endpointImportedRectangleCount
    source
    target

end AnalyticMotives
end LFunctions
end Boundary
