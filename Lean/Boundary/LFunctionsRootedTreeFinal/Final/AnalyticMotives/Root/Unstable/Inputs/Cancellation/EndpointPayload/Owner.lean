import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Root.Unstable.Inputs.Cancellation.Laws.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Root.Unstable.Inputs.Cancellation.Counts.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Root.Unstable.Inputs.Cancellation.LedgerRectangles.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Root.Unstable.Inputs.Cancellation.TraceCalculus.Owner

/-!
# Top-root all-kind unstable cancellation endpoint payload
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- The root exposes by-kind descent-channel hom-inverse endpoint rectangles. -/
theorem AnalyticMotivesRoot.unstableByKindDescentChannelIso_hom_comp_inv_endpointImportedRectangles
    (source target : QTraceExpression) :
    (TraceLocalizationWordClass.comp
      (TraceUnstableAnalyticMotive.descentChannelIso source target).hom
      (TraceUnstableAnalyticMotive.descentChannelIso source target).inv).endpointImportedRectangles =
      (TraceLocalizationInput.descentChannel source target).localizedSourceObject.importedRectangles ++
        (TraceLocalizationInput.descentChannel source target).localizedSourceObject.importedRectangles :=
  TraceAnalyticMotive.unstableByKindDescentChannelIso_hom_comp_inv_endpointImportedRectangles
    source
    target

/-- The root exposes by-kind descent-channel inverse-hom endpoint rectangles. -/
theorem AnalyticMotivesRoot.unstableByKindDescentChannelIso_inv_comp_hom_endpointImportedRectangles
    (source target : QTraceExpression) :
    (TraceLocalizationWordClass.comp
      (TraceUnstableAnalyticMotive.descentChannelIso source target).inv
      (TraceUnstableAnalyticMotive.descentChannelIso source target).hom).endpointImportedRectangles =
      (TraceLocalizationInput.descentChannel source target).localizedTargetObject.importedRectangles ++
        (TraceLocalizationInput.descentChannel source target).localizedTargetObject.importedRectangles :=
  TraceAnalyticMotive.unstableByKindDescentChannelIso_inv_comp_hom_endpointImportedRectangles
    source
    target

/-- The root exposes by-kind descent-refinement hom-inverse endpoint rectangles. -/
theorem AnalyticMotivesRoot.unstableByKindDescentRefinementIso_hom_comp_inv_endpointImportedRectangles
    (source target : QTraceExpression) :
    (TraceLocalizationWordClass.comp
      (TraceUnstableAnalyticMotive.descentRefinementIso source target).hom
      (TraceUnstableAnalyticMotive.descentRefinementIso source target).inv).endpointImportedRectangles =
      (TraceLocalizationInput.descentRefinement source target).localizedSourceObject.importedRectangles ++
        (TraceLocalizationInput.descentRefinement source target).localizedSourceObject.importedRectangles :=
  TraceAnalyticMotive.unstableByKindDescentRefinementIso_hom_comp_inv_endpointImportedRectangles
    source
    target

/-- The root exposes by-kind descent-refinement inverse-hom endpoint rectangles. -/
theorem AnalyticMotivesRoot.unstableByKindDescentRefinementIso_inv_comp_hom_endpointImportedRectangles
    (source target : QTraceExpression) :
    (TraceLocalizationWordClass.comp
      (TraceUnstableAnalyticMotive.descentRefinementIso source target).inv
      (TraceUnstableAnalyticMotive.descentRefinementIso source target).hom).endpointImportedRectangles =
      (TraceLocalizationInput.descentRefinement source target).localizedTargetObject.importedRectangles ++
        (TraceLocalizationInput.descentRefinement source target).localizedTargetObject.importedRectangles :=
  TraceAnalyticMotive.unstableByKindDescentRefinementIso_inv_comp_hom_endpointImportedRectangles
    source
    target

/-- The root exposes by-kind descent-schedule hom-inverse endpoint rectangles. -/
theorem AnalyticMotivesRoot.unstableByKindDescentScheduleIso_hom_comp_inv_endpointImportedRectangles
    (source target : QTraceExpression) :
    (TraceLocalizationWordClass.comp
      (TraceUnstableAnalyticMotive.descentScheduleIso source target).hom
      (TraceUnstableAnalyticMotive.descentScheduleIso source target).inv).endpointImportedRectangles =
      (TraceLocalizationInput.descentSchedule source target).localizedSourceObject.importedRectangles ++
        (TraceLocalizationInput.descentSchedule source target).localizedSourceObject.importedRectangles :=
  TraceAnalyticMotive.unstableByKindDescentScheduleIso_hom_comp_inv_endpointImportedRectangles
    source
    target

/-- The root exposes by-kind descent-schedule inverse-hom endpoint rectangles. -/
theorem AnalyticMotivesRoot.unstableByKindDescentScheduleIso_inv_comp_hom_endpointImportedRectangles
    (source target : QTraceExpression) :
    (TraceLocalizationWordClass.comp
      (TraceUnstableAnalyticMotive.descentScheduleIso source target).inv
      (TraceUnstableAnalyticMotive.descentScheduleIso source target).hom).endpointImportedRectangles =
      (TraceLocalizationInput.descentSchedule source target).localizedTargetObject.importedRectangles ++
        (TraceLocalizationInput.descentSchedule source target).localizedTargetObject.importedRectangles :=
  TraceAnalyticMotive.unstableByKindDescentScheduleIso_inv_comp_hom_endpointImportedRectangles
    source
    target

/-- The root exposes by-kind interval-Stokes hom-inverse endpoint rectangles. -/
theorem AnalyticMotivesRoot.unstableByKindIntervalStokesIso_hom_comp_inv_endpointImportedRectangles
    (source target : QTraceExpression) :
    (TraceLocalizationWordClass.comp
      (TraceUnstableAnalyticMotive.intervalStokesIso source target).hom
      (TraceUnstableAnalyticMotive.intervalStokesIso source target).inv).endpointImportedRectangles =
      (TraceLocalizationInput.intervalStokes source target).localizedSourceObject.importedRectangles ++
        (TraceLocalizationInput.intervalStokes source target).localizedSourceObject.importedRectangles :=
  TraceAnalyticMotive.unstableByKindIntervalStokesIso_hom_comp_inv_endpointImportedRectangles
    source
    target

/-- The root exposes by-kind interval-Stokes inverse-hom endpoint rectangles. -/
theorem AnalyticMotivesRoot.unstableByKindIntervalStokesIso_inv_comp_hom_endpointImportedRectangles
    (source target : QTraceExpression) :
    (TraceLocalizationWordClass.comp
      (TraceUnstableAnalyticMotive.intervalStokesIso source target).inv
      (TraceUnstableAnalyticMotive.intervalStokesIso source target).hom).endpointImportedRectangles =
      (TraceLocalizationInput.intervalStokes source target).localizedTargetObject.importedRectangles ++
        (TraceLocalizationInput.intervalStokes source target).localizedTargetObject.importedRectangles :=
  TraceAnalyticMotive.unstableByKindIntervalStokesIso_inv_comp_hom_endpointImportedRectangles
    source
    target

/-- The root exposes by-kind interval-Fubini hom-inverse endpoint rectangles. -/
theorem AnalyticMotivesRoot.unstableByKindIntervalFubiniIso_hom_comp_inv_endpointImportedRectangles
    (source target : QTraceExpression) :
    (TraceLocalizationWordClass.comp
      (TraceUnstableAnalyticMotive.intervalFubiniIso source target).hom
      (TraceUnstableAnalyticMotive.intervalFubiniIso source target).inv).endpointImportedRectangles =
      (TraceLocalizationInput.intervalFubini source target).localizedSourceObject.importedRectangles ++
        (TraceLocalizationInput.intervalFubini source target).localizedSourceObject.importedRectangles :=
  TraceAnalyticMotive.unstableByKindIntervalFubiniIso_hom_comp_inv_endpointImportedRectangles
    source
    target

/-- The root exposes by-kind interval-Fubini inverse-hom endpoint rectangles. -/
theorem AnalyticMotivesRoot.unstableByKindIntervalFubiniIso_inv_comp_hom_endpointImportedRectangles
    (source target : QTraceExpression) :
    (TraceLocalizationWordClass.comp
      (TraceUnstableAnalyticMotive.intervalFubiniIso source target).inv
      (TraceUnstableAnalyticMotive.intervalFubiniIso source target).hom).endpointImportedRectangles =
      (TraceLocalizationInput.intervalFubini source target).localizedTargetObject.importedRectangles ++
        (TraceLocalizationInput.intervalFubini source target).localizedTargetObject.importedRectangles :=
  TraceAnalyticMotive.unstableByKindIntervalFubiniIso_inv_comp_hom_endpointImportedRectangles
    source
    target

/-- The root exposes by-kind Tate-weight-drop hom-inverse endpoint rectangles. -/
theorem AnalyticMotivesRoot.unstableByKindTateWeightDropIso_hom_comp_inv_endpointImportedRectangles
    (source target : QTraceExpression) :
    (TraceLocalizationWordClass.comp
      (TraceUnstableAnalyticMotive.tateWeightDropIso source target).hom
      (TraceUnstableAnalyticMotive.tateWeightDropIso source target).inv).endpointImportedRectangles =
      (TraceLocalizationInput.tateWeightDrop source target).localizedSourceObject.importedRectangles ++
        (TraceLocalizationInput.tateWeightDrop source target).localizedSourceObject.importedRectangles :=
  TraceAnalyticMotive.unstableByKindTateWeightDropIso_hom_comp_inv_endpointImportedRectangles
    source
    target

/-- The root exposes by-kind Tate-weight-drop inverse-hom endpoint rectangles. -/
theorem AnalyticMotivesRoot.unstableByKindTateWeightDropIso_inv_comp_hom_endpointImportedRectangles
    (source target : QTraceExpression) :
    (TraceLocalizationWordClass.comp
      (TraceUnstableAnalyticMotive.tateWeightDropIso source target).inv
      (TraceUnstableAnalyticMotive.tateWeightDropIso source target).hom).endpointImportedRectangles =
      (TraceLocalizationInput.tateWeightDrop source target).localizedTargetObject.importedRectangles ++
        (TraceLocalizationInput.tateWeightDrop source target).localizedTargetObject.importedRectangles :=
  TraceAnalyticMotive.unstableByKindTateWeightDropIso_inv_comp_hom_endpointImportedRectangles
    source
    target

end AnalyticMotives
end LFunctions
end Boundary
