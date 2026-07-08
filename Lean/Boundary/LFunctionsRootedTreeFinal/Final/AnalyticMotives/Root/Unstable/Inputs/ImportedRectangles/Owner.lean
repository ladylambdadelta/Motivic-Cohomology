import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Root.Unstable.Inputs.ImportedRectangles.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Root.Unstable.Inputs.ImportedRectangles.ArrowEndpoints.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Root.Unstable.Inputs.ImportedRectangles.LedgerRectangles.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Root.Unstable.Inputs.ImportedRectangles.Counts.Owner

/-!
# Top-root all-kind unstable input imported rectangles

This file mirrors the motive-root endpoint imported-rectangle list surface for
hom and inverse arrows of all six named unstable localization isomorphisms.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- The root exposes by-kind descent-channel hom endpoint rectangles. -/
theorem AnalyticMotivesRoot.unstableByKindDescentChannelIso_hom_endpointImportedRectangles
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.descentChannelIso
      source
      target).hom.endpointImportedRectangles =
      (TraceLocalizationInput.descentChannel source target).sourceObject.importedRectangles ++
        (TraceLocalizationInput.descentChannel source target).targetObject.importedRectangles :=
  TraceAnalyticMotive.unstableByKindDescentChannelIso_hom_endpointImportedRectangles
    source
    target

/-- The root exposes by-kind descent-channel inverse endpoint rectangles. -/
theorem AnalyticMotivesRoot.unstableByKindDescentChannelIso_inv_endpointImportedRectangles
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.descentChannelIso
      source
      target).inv.endpointImportedRectangles =
      (TraceLocalizationInput.descentChannel source target).targetObject.importedRectangles ++
        (TraceLocalizationInput.descentChannel source target).sourceObject.importedRectangles :=
  TraceAnalyticMotive.unstableByKindDescentChannelIso_inv_endpointImportedRectangles
    source
    target

/-- The root exposes by-kind descent-refinement hom endpoint rectangles. -/
theorem AnalyticMotivesRoot.unstableByKindDescentRefinementIso_hom_endpointImportedRectangles
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.descentRefinementIso
      source
      target).hom.endpointImportedRectangles =
      (TraceLocalizationInput.descentRefinement source target).sourceObject.importedRectangles ++
        (TraceLocalizationInput.descentRefinement source target).targetObject.importedRectangles :=
  TraceAnalyticMotive.unstableByKindDescentRefinementIso_hom_endpointImportedRectangles
    source
    target

/-- The root exposes by-kind descent-refinement inverse endpoint rectangles. -/
theorem AnalyticMotivesRoot.unstableByKindDescentRefinementIso_inv_endpointImportedRectangles
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.descentRefinementIso
      source
      target).inv.endpointImportedRectangles =
      (TraceLocalizationInput.descentRefinement source target).targetObject.importedRectangles ++
        (TraceLocalizationInput.descentRefinement source target).sourceObject.importedRectangles :=
  TraceAnalyticMotive.unstableByKindDescentRefinementIso_inv_endpointImportedRectangles
    source
    target

/-- The root exposes by-kind descent-schedule hom endpoint rectangles. -/
theorem AnalyticMotivesRoot.unstableByKindDescentScheduleIso_hom_endpointImportedRectangles
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.descentScheduleIso
      source
      target).hom.endpointImportedRectangles =
      (TraceLocalizationInput.descentSchedule source target).sourceObject.importedRectangles ++
        (TraceLocalizationInput.descentSchedule source target).targetObject.importedRectangles :=
  TraceAnalyticMotive.unstableByKindDescentScheduleIso_hom_endpointImportedRectangles
    source
    target

/-- The root exposes by-kind descent-schedule inverse endpoint rectangles. -/
theorem AnalyticMotivesRoot.unstableByKindDescentScheduleIso_inv_endpointImportedRectangles
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.descentScheduleIso
      source
      target).inv.endpointImportedRectangles =
      (TraceLocalizationInput.descentSchedule source target).targetObject.importedRectangles ++
        (TraceLocalizationInput.descentSchedule source target).sourceObject.importedRectangles :=
  TraceAnalyticMotive.unstableByKindDescentScheduleIso_inv_endpointImportedRectangles
    source
    target

/-- The root exposes by-kind interval-Stokes hom endpoint rectangles. -/
theorem AnalyticMotivesRoot.unstableByKindIntervalStokesIso_hom_endpointImportedRectangles
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.intervalStokesIso
      source
      target).hom.endpointImportedRectangles =
      (TraceLocalizationInput.intervalStokes source target).sourceObject.importedRectangles ++
        (TraceLocalizationInput.intervalStokes source target).targetObject.importedRectangles :=
  TraceAnalyticMotive.unstableByKindIntervalStokesIso_hom_endpointImportedRectangles
    source
    target

/-- The root exposes by-kind interval-Stokes inverse endpoint rectangles. -/
theorem AnalyticMotivesRoot.unstableByKindIntervalStokesIso_inv_endpointImportedRectangles
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.intervalStokesIso
      source
      target).inv.endpointImportedRectangles =
      (TraceLocalizationInput.intervalStokes source target).targetObject.importedRectangles ++
        (TraceLocalizationInput.intervalStokes source target).sourceObject.importedRectangles :=
  TraceAnalyticMotive.unstableByKindIntervalStokesIso_inv_endpointImportedRectangles
    source
    target

/-- The root exposes by-kind interval-Fubini hom endpoint rectangles. -/
theorem AnalyticMotivesRoot.unstableByKindIntervalFubiniIso_hom_endpointImportedRectangles
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.intervalFubiniIso
      source
      target).hom.endpointImportedRectangles =
      (TraceLocalizationInput.intervalFubini source target).sourceObject.importedRectangles ++
        (TraceLocalizationInput.intervalFubini source target).targetObject.importedRectangles :=
  TraceAnalyticMotive.unstableByKindIntervalFubiniIso_hom_endpointImportedRectangles
    source
    target

/-- The root exposes by-kind interval-Fubini inverse endpoint rectangles. -/
theorem AnalyticMotivesRoot.unstableByKindIntervalFubiniIso_inv_endpointImportedRectangles
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.intervalFubiniIso
      source
      target).inv.endpointImportedRectangles =
      (TraceLocalizationInput.intervalFubini source target).targetObject.importedRectangles ++
        (TraceLocalizationInput.intervalFubini source target).sourceObject.importedRectangles :=
  TraceAnalyticMotive.unstableByKindIntervalFubiniIso_inv_endpointImportedRectangles
    source
    target

/-- The root exposes by-kind Tate-weight-drop hom endpoint rectangles. -/
theorem AnalyticMotivesRoot.unstableByKindTateWeightDropIso_hom_endpointImportedRectangles
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.tateWeightDropIso
      source
      target).hom.endpointImportedRectangles =
      (TraceLocalizationInput.tateWeightDrop source target).sourceObject.importedRectangles ++
        (TraceLocalizationInput.tateWeightDrop source target).targetObject.importedRectangles :=
  TraceAnalyticMotive.unstableByKindTateWeightDropIso_hom_endpointImportedRectangles
    source
    target

/-- The root exposes by-kind Tate-weight-drop inverse endpoint rectangles. -/
theorem AnalyticMotivesRoot.unstableByKindTateWeightDropIso_inv_endpointImportedRectangles
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.tateWeightDropIso
      source
      target).inv.endpointImportedRectangles =
      (TraceLocalizationInput.tateWeightDrop source target).targetObject.importedRectangles ++
        (TraceLocalizationInput.tateWeightDrop source target).sourceObject.importedRectangles :=
  TraceAnalyticMotive.unstableByKindTateWeightDropIso_inv_endpointImportedRectangles
    source
    target

end AnalyticMotives
end LFunctions
end Boundary
