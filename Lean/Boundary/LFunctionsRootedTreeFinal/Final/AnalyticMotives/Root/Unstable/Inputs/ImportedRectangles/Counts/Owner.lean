import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Root.Unstable.Inputs.ImportedRectangles.Counts.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Root.Unstable.Inputs.ImportedRectangles.Counts.ArrowEndpoints.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Root.Unstable.Inputs.ImportedRectangles.Counts.Lengths.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Root.Unstable.Inputs.ImportedRectangles.Counts.LedgerCounts.Owner

/-!
# Top-root all-kind unstable input imported-rectangle counts

This file mirrors the motive-root endpoint imported-rectangle count surface for
hom and inverse arrows of all six named unstable localization isomorphisms.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- The root exposes by-kind descent-channel hom endpoint rectangle counts. -/
theorem AnalyticMotivesRoot.unstableByKindDescentChannelIso_hom_endpointImportedRectangleCount
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.descentChannelIso
      source
      target).hom.endpointImportedRectangleCount =
      (TraceLocalizationInput.descentChannel source target).sourceObject.importedRectangleCount +
        (TraceLocalizationInput.descentChannel source target).targetObject.importedRectangleCount :=
  TraceAnalyticMotive.unstableByKindDescentChannelIso_hom_endpointImportedRectangleCount
    source
    target

/-- The root exposes by-kind descent-channel inverse endpoint rectangle counts. -/
theorem AnalyticMotivesRoot.unstableByKindDescentChannelIso_inv_endpointImportedRectangleCount
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.descentChannelIso
      source
      target).inv.endpointImportedRectangleCount =
      (TraceLocalizationInput.descentChannel source target).targetObject.importedRectangleCount +
        (TraceLocalizationInput.descentChannel source target).sourceObject.importedRectangleCount :=
  TraceAnalyticMotive.unstableByKindDescentChannelIso_inv_endpointImportedRectangleCount
    source
    target

/-- The root exposes by-kind descent-refinement hom endpoint rectangle counts. -/
theorem AnalyticMotivesRoot.unstableByKindDescentRefinementIso_hom_endpointImportedRectangleCount
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.descentRefinementIso
      source
      target).hom.endpointImportedRectangleCount =
      (TraceLocalizationInput.descentRefinement source target).sourceObject.importedRectangleCount +
        (TraceLocalizationInput.descentRefinement source target).targetObject.importedRectangleCount :=
  TraceAnalyticMotive.unstableByKindDescentRefinementIso_hom_endpointImportedRectangleCount
    source
    target

/-- The root exposes by-kind descent-refinement inverse endpoint rectangle counts. -/
theorem AnalyticMotivesRoot.unstableByKindDescentRefinementIso_inv_endpointImportedRectangleCount
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.descentRefinementIso
      source
      target).inv.endpointImportedRectangleCount =
      (TraceLocalizationInput.descentRefinement source target).targetObject.importedRectangleCount +
        (TraceLocalizationInput.descentRefinement source target).sourceObject.importedRectangleCount :=
  TraceAnalyticMotive.unstableByKindDescentRefinementIso_inv_endpointImportedRectangleCount
    source
    target

/-- The root exposes by-kind descent-schedule hom endpoint rectangle counts. -/
theorem AnalyticMotivesRoot.unstableByKindDescentScheduleIso_hom_endpointImportedRectangleCount
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.descentScheduleIso
      source
      target).hom.endpointImportedRectangleCount =
      (TraceLocalizationInput.descentSchedule source target).sourceObject.importedRectangleCount +
        (TraceLocalizationInput.descentSchedule source target).targetObject.importedRectangleCount :=
  TraceAnalyticMotive.unstableByKindDescentScheduleIso_hom_endpointImportedRectangleCount
    source
    target

/-- The root exposes by-kind descent-schedule inverse endpoint rectangle counts. -/
theorem AnalyticMotivesRoot.unstableByKindDescentScheduleIso_inv_endpointImportedRectangleCount
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.descentScheduleIso
      source
      target).inv.endpointImportedRectangleCount =
      (TraceLocalizationInput.descentSchedule source target).targetObject.importedRectangleCount +
        (TraceLocalizationInput.descentSchedule source target).sourceObject.importedRectangleCount :=
  TraceAnalyticMotive.unstableByKindDescentScheduleIso_inv_endpointImportedRectangleCount
    source
    target

/-- The root exposes by-kind interval-Stokes hom endpoint rectangle counts. -/
theorem AnalyticMotivesRoot.unstableByKindIntervalStokesIso_hom_endpointImportedRectangleCount
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.intervalStokesIso
      source
      target).hom.endpointImportedRectangleCount =
      (TraceLocalizationInput.intervalStokes source target).sourceObject.importedRectangleCount +
        (TraceLocalizationInput.intervalStokes source target).targetObject.importedRectangleCount :=
  TraceAnalyticMotive.unstableByKindIntervalStokesIso_hom_endpointImportedRectangleCount
    source
    target

/-- The root exposes by-kind interval-Stokes inverse endpoint rectangle counts. -/
theorem AnalyticMotivesRoot.unstableByKindIntervalStokesIso_inv_endpointImportedRectangleCount
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.intervalStokesIso
      source
      target).inv.endpointImportedRectangleCount =
      (TraceLocalizationInput.intervalStokes source target).targetObject.importedRectangleCount +
        (TraceLocalizationInput.intervalStokes source target).sourceObject.importedRectangleCount :=
  TraceAnalyticMotive.unstableByKindIntervalStokesIso_inv_endpointImportedRectangleCount
    source
    target

/-- The root exposes by-kind interval-Fubini hom endpoint rectangle counts. -/
theorem AnalyticMotivesRoot.unstableByKindIntervalFubiniIso_hom_endpointImportedRectangleCount
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.intervalFubiniIso
      source
      target).hom.endpointImportedRectangleCount =
      (TraceLocalizationInput.intervalFubini source target).sourceObject.importedRectangleCount +
        (TraceLocalizationInput.intervalFubini source target).targetObject.importedRectangleCount :=
  TraceAnalyticMotive.unstableByKindIntervalFubiniIso_hom_endpointImportedRectangleCount
    source
    target

/-- The root exposes by-kind interval-Fubini inverse endpoint rectangle counts. -/
theorem AnalyticMotivesRoot.unstableByKindIntervalFubiniIso_inv_endpointImportedRectangleCount
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.intervalFubiniIso
      source
      target).inv.endpointImportedRectangleCount =
      (TraceLocalizationInput.intervalFubini source target).targetObject.importedRectangleCount +
        (TraceLocalizationInput.intervalFubini source target).sourceObject.importedRectangleCount :=
  TraceAnalyticMotive.unstableByKindIntervalFubiniIso_inv_endpointImportedRectangleCount
    source
    target

/-- The root exposes by-kind Tate-weight-drop hom endpoint rectangle counts. -/
theorem AnalyticMotivesRoot.unstableByKindTateWeightDropIso_hom_endpointImportedRectangleCount
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.tateWeightDropIso
      source
      target).hom.endpointImportedRectangleCount =
      (TraceLocalizationInput.tateWeightDrop source target).sourceObject.importedRectangleCount +
        (TraceLocalizationInput.tateWeightDrop source target).targetObject.importedRectangleCount :=
  TraceAnalyticMotive.unstableByKindTateWeightDropIso_hom_endpointImportedRectangleCount
    source
    target

/-- The root exposes by-kind Tate-weight-drop inverse endpoint rectangle counts. -/
theorem AnalyticMotivesRoot.unstableByKindTateWeightDropIso_inv_endpointImportedRectangleCount
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.tateWeightDropIso
      source
      target).inv.endpointImportedRectangleCount =
      (TraceLocalizationInput.tateWeightDrop source target).targetObject.importedRectangleCount +
        (TraceLocalizationInput.tateWeightDrop source target).sourceObject.importedRectangleCount :=
  TraceAnalyticMotive.unstableByKindTateWeightDropIso_inv_endpointImportedRectangleCount
    source
    target

end AnalyticMotives
end LFunctions
end Boundary
