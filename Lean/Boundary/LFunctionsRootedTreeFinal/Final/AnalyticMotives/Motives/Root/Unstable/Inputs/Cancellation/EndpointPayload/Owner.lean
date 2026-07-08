import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Root.Unstable.Inputs.Cancellation.Laws.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Root.Unstable.Inputs.Cancellation.Counts.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Root.Unstable.Inputs.Cancellation.LedgerRectangles.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Root.Unstable.Inputs.Cancellation.TraceCalculus.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Unstable.Inputs.ByKind.Cancellation.Payload.ImportedRectangles.Endpoint.Owner

/-!
# Motive-root all-kind unstable cancellation endpoint payload
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- By-kind descent-channel hom-inverse cancellation endpoint rectangles are source rectangles twice. -/
theorem TraceAnalyticMotive.unstableByKindDescentChannelIso_hom_comp_inv_endpointImportedRectangles
    (source target : QTraceExpression) :
    (TraceLocalizationWordClass.comp
      (TraceUnstableAnalyticMotive.descentChannelIso source target).hom
      (TraceUnstableAnalyticMotive.descentChannelIso source target).inv).endpointImportedRectangles =
      (TraceLocalizationInput.descentChannel source target).localizedSourceObject.importedRectangles ++
        (TraceLocalizationInput.descentChannel source target).localizedSourceObject.importedRectangles :=
  TraceUnstableAnalyticMotive.descentChannelIso_hom_comp_inv_endpointImportedRectangles
    source
    target

/-- By-kind descent-channel inverse-hom cancellation endpoint rectangles are target rectangles twice. -/
theorem TraceAnalyticMotive.unstableByKindDescentChannelIso_inv_comp_hom_endpointImportedRectangles
    (source target : QTraceExpression) :
    (TraceLocalizationWordClass.comp
      (TraceUnstableAnalyticMotive.descentChannelIso source target).inv
      (TraceUnstableAnalyticMotive.descentChannelIso source target).hom).endpointImportedRectangles =
      (TraceLocalizationInput.descentChannel source target).localizedTargetObject.importedRectangles ++
        (TraceLocalizationInput.descentChannel source target).localizedTargetObject.importedRectangles :=
  TraceUnstableAnalyticMotive.descentChannelIso_inv_comp_hom_endpointImportedRectangles
    source
    target

/-- By-kind descent-refinement hom-inverse cancellation endpoint rectangles are source rectangles twice. -/
theorem TraceAnalyticMotive.unstableByKindDescentRefinementIso_hom_comp_inv_endpointImportedRectangles
    (source target : QTraceExpression) :
    (TraceLocalizationWordClass.comp
      (TraceUnstableAnalyticMotive.descentRefinementIso source target).hom
      (TraceUnstableAnalyticMotive.descentRefinementIso source target).inv).endpointImportedRectangles =
      (TraceLocalizationInput.descentRefinement source target).localizedSourceObject.importedRectangles ++
        (TraceLocalizationInput.descentRefinement source target).localizedSourceObject.importedRectangles :=
  TraceUnstableAnalyticMotive.descentRefinementIso_hom_comp_inv_endpointImportedRectangles
    source
    target

/-- By-kind descent-refinement inverse-hom cancellation endpoint rectangles are target rectangles twice. -/
theorem TraceAnalyticMotive.unstableByKindDescentRefinementIso_inv_comp_hom_endpointImportedRectangles
    (source target : QTraceExpression) :
    (TraceLocalizationWordClass.comp
      (TraceUnstableAnalyticMotive.descentRefinementIso source target).inv
      (TraceUnstableAnalyticMotive.descentRefinementIso source target).hom).endpointImportedRectangles =
      (TraceLocalizationInput.descentRefinement source target).localizedTargetObject.importedRectangles ++
        (TraceLocalizationInput.descentRefinement source target).localizedTargetObject.importedRectangles :=
  TraceUnstableAnalyticMotive.descentRefinementIso_inv_comp_hom_endpointImportedRectangles
    source
    target

/-- By-kind descent-schedule hom-inverse cancellation endpoint rectangles are source rectangles twice. -/
theorem TraceAnalyticMotive.unstableByKindDescentScheduleIso_hom_comp_inv_endpointImportedRectangles
    (source target : QTraceExpression) :
    (TraceLocalizationWordClass.comp
      (TraceUnstableAnalyticMotive.descentScheduleIso source target).hom
      (TraceUnstableAnalyticMotive.descentScheduleIso source target).inv).endpointImportedRectangles =
      (TraceLocalizationInput.descentSchedule source target).localizedSourceObject.importedRectangles ++
        (TraceLocalizationInput.descentSchedule source target).localizedSourceObject.importedRectangles :=
  TraceUnstableAnalyticMotive.descentScheduleIso_hom_comp_inv_endpointImportedRectangles
    source
    target

/-- By-kind descent-schedule inverse-hom cancellation endpoint rectangles are target rectangles twice. -/
theorem TraceAnalyticMotive.unstableByKindDescentScheduleIso_inv_comp_hom_endpointImportedRectangles
    (source target : QTraceExpression) :
    (TraceLocalizationWordClass.comp
      (TraceUnstableAnalyticMotive.descentScheduleIso source target).inv
      (TraceUnstableAnalyticMotive.descentScheduleIso source target).hom).endpointImportedRectangles =
      (TraceLocalizationInput.descentSchedule source target).localizedTargetObject.importedRectangles ++
        (TraceLocalizationInput.descentSchedule source target).localizedTargetObject.importedRectangles :=
  TraceUnstableAnalyticMotive.descentScheduleIso_inv_comp_hom_endpointImportedRectangles
    source
    target

/-- By-kind interval-Stokes hom-inverse cancellation endpoint rectangles are source rectangles twice. -/
theorem TraceAnalyticMotive.unstableByKindIntervalStokesIso_hom_comp_inv_endpointImportedRectangles
    (source target : QTraceExpression) :
    (TraceLocalizationWordClass.comp
      (TraceUnstableAnalyticMotive.intervalStokesIso source target).hom
      (TraceUnstableAnalyticMotive.intervalStokesIso source target).inv).endpointImportedRectangles =
      (TraceLocalizationInput.intervalStokes source target).localizedSourceObject.importedRectangles ++
        (TraceLocalizationInput.intervalStokes source target).localizedSourceObject.importedRectangles :=
  TraceUnstableAnalyticMotive.intervalStokesIso_hom_comp_inv_endpointImportedRectangles
    source
    target

/-- By-kind interval-Stokes inverse-hom cancellation endpoint rectangles are target rectangles twice. -/
theorem TraceAnalyticMotive.unstableByKindIntervalStokesIso_inv_comp_hom_endpointImportedRectangles
    (source target : QTraceExpression) :
    (TraceLocalizationWordClass.comp
      (TraceUnstableAnalyticMotive.intervalStokesIso source target).inv
      (TraceUnstableAnalyticMotive.intervalStokesIso source target).hom).endpointImportedRectangles =
      (TraceLocalizationInput.intervalStokes source target).localizedTargetObject.importedRectangles ++
        (TraceLocalizationInput.intervalStokes source target).localizedTargetObject.importedRectangles :=
  TraceUnstableAnalyticMotive.intervalStokesIso_inv_comp_hom_endpointImportedRectangles
    source
    target

/-- By-kind interval-Fubini hom-inverse cancellation endpoint rectangles are source rectangles twice. -/
theorem TraceAnalyticMotive.unstableByKindIntervalFubiniIso_hom_comp_inv_endpointImportedRectangles
    (source target : QTraceExpression) :
    (TraceLocalizationWordClass.comp
      (TraceUnstableAnalyticMotive.intervalFubiniIso source target).hom
      (TraceUnstableAnalyticMotive.intervalFubiniIso source target).inv).endpointImportedRectangles =
      (TraceLocalizationInput.intervalFubini source target).localizedSourceObject.importedRectangles ++
        (TraceLocalizationInput.intervalFubini source target).localizedSourceObject.importedRectangles :=
  TraceUnstableAnalyticMotive.intervalFubiniIso_hom_comp_inv_endpointImportedRectangles
    source
    target

/-- By-kind interval-Fubini inverse-hom cancellation endpoint rectangles are target rectangles twice. -/
theorem TraceAnalyticMotive.unstableByKindIntervalFubiniIso_inv_comp_hom_endpointImportedRectangles
    (source target : QTraceExpression) :
    (TraceLocalizationWordClass.comp
      (TraceUnstableAnalyticMotive.intervalFubiniIso source target).inv
      (TraceUnstableAnalyticMotive.intervalFubiniIso source target).hom).endpointImportedRectangles =
      (TraceLocalizationInput.intervalFubini source target).localizedTargetObject.importedRectangles ++
        (TraceLocalizationInput.intervalFubini source target).localizedTargetObject.importedRectangles :=
  TraceUnstableAnalyticMotive.intervalFubiniIso_inv_comp_hom_endpointImportedRectangles
    source
    target

/-- By-kind Tate-weight-drop hom-inverse cancellation endpoint rectangles are source rectangles twice. -/
theorem TraceAnalyticMotive.unstableByKindTateWeightDropIso_hom_comp_inv_endpointImportedRectangles
    (source target : QTraceExpression) :
    (TraceLocalizationWordClass.comp
      (TraceUnstableAnalyticMotive.tateWeightDropIso source target).hom
      (TraceUnstableAnalyticMotive.tateWeightDropIso source target).inv).endpointImportedRectangles =
      (TraceLocalizationInput.tateWeightDrop source target).localizedSourceObject.importedRectangles ++
        (TraceLocalizationInput.tateWeightDrop source target).localizedSourceObject.importedRectangles :=
  TraceUnstableAnalyticMotive.tateWeightDropIso_hom_comp_inv_endpointImportedRectangles
    source
    target

/-- By-kind Tate-weight-drop inverse-hom cancellation endpoint rectangles are target rectangles twice. -/
theorem TraceAnalyticMotive.unstableByKindTateWeightDropIso_inv_comp_hom_endpointImportedRectangles
    (source target : QTraceExpression) :
    (TraceLocalizationWordClass.comp
      (TraceUnstableAnalyticMotive.tateWeightDropIso source target).inv
      (TraceUnstableAnalyticMotive.tateWeightDropIso source target).hom).endpointImportedRectangles =
      (TraceLocalizationInput.tateWeightDrop source target).localizedTargetObject.importedRectangles ++
        (TraceLocalizationInput.tateWeightDrop source target).localizedTargetObject.importedRectangles :=
  TraceUnstableAnalyticMotive.tateWeightDropIso_inv_comp_hom_endpointImportedRectangles
    source
    target

end AnalyticMotives
end LFunctions
end Boundary
