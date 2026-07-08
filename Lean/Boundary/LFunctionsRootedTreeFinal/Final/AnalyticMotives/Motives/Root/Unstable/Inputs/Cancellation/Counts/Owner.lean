import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Unstable.Inputs.ByKind.Cancellation.Payload.ImportedRectangles.Counts.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Root.Unstable.Inputs.Cancellation.Counts.LedgerCounts.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Root.Unstable.Inputs.Cancellation.Counts.Lengths.Owner

/-!
# Root all-kind unstable cancellation endpoint counts

This file exposes endpoint imported-rectangle counts for all six named
unstable localization cancellation composites at the motive-root namespace.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- By-kind descent-channel hom-inverse cancellation endpoint count is source count twice. -/
theorem TraceAnalyticMotive.unstableByKindDescentChannelIso_hom_comp_inv_endpointImportedRectangleCount
    (source target : QTraceExpression) :
    (TraceLocalizationWordClass.comp
      (TraceUnstableAnalyticMotive.descentChannelIso source target).hom
      (TraceUnstableAnalyticMotive.descentChannelIso source target).inv).endpointImportedRectangleCount =
      (TraceLocalizationInput.descentChannel source target).localizedSourceObject.importedRectangleCount +
        (TraceLocalizationInput.descentChannel source target).localizedSourceObject.importedRectangleCount :=
  TraceUnstableAnalyticMotive.descentChannelIso_hom_comp_inv_endpointImportedRectangleCount
    source
    target

/-- By-kind descent-channel inverse-hom cancellation endpoint count is target count twice. -/
theorem TraceAnalyticMotive.unstableByKindDescentChannelIso_inv_comp_hom_endpointImportedRectangleCount
    (source target : QTraceExpression) :
    (TraceLocalizationWordClass.comp
      (TraceUnstableAnalyticMotive.descentChannelIso source target).inv
      (TraceUnstableAnalyticMotive.descentChannelIso source target).hom).endpointImportedRectangleCount =
      (TraceLocalizationInput.descentChannel source target).localizedTargetObject.importedRectangleCount +
        (TraceLocalizationInput.descentChannel source target).localizedTargetObject.importedRectangleCount :=
  TraceUnstableAnalyticMotive.descentChannelIso_inv_comp_hom_endpointImportedRectangleCount
    source
    target

/-- By-kind descent-refinement hom-inverse cancellation endpoint count is source count twice. -/
theorem TraceAnalyticMotive.unstableByKindDescentRefinementIso_hom_comp_inv_endpointImportedRectangleCount
    (source target : QTraceExpression) :
    (TraceLocalizationWordClass.comp
      (TraceUnstableAnalyticMotive.descentRefinementIso source target).hom
      (TraceUnstableAnalyticMotive.descentRefinementIso source target).inv).endpointImportedRectangleCount =
      (TraceLocalizationInput.descentRefinement source target).localizedSourceObject.importedRectangleCount +
        (TraceLocalizationInput.descentRefinement source target).localizedSourceObject.importedRectangleCount :=
  TraceUnstableAnalyticMotive.descentRefinementIso_hom_comp_inv_endpointImportedRectangleCount
    source
    target

/-- By-kind descent-refinement inverse-hom cancellation endpoint count is target count twice. -/
theorem TraceAnalyticMotive.unstableByKindDescentRefinementIso_inv_comp_hom_endpointImportedRectangleCount
    (source target : QTraceExpression) :
    (TraceLocalizationWordClass.comp
      (TraceUnstableAnalyticMotive.descentRefinementIso source target).inv
      (TraceUnstableAnalyticMotive.descentRefinementIso source target).hom).endpointImportedRectangleCount =
      (TraceLocalizationInput.descentRefinement source target).localizedTargetObject.importedRectangleCount +
        (TraceLocalizationInput.descentRefinement source target).localizedTargetObject.importedRectangleCount :=
  TraceUnstableAnalyticMotive.descentRefinementIso_inv_comp_hom_endpointImportedRectangleCount
    source
    target

/-- By-kind descent-schedule hom-inverse cancellation endpoint count is source count twice. -/
theorem TraceAnalyticMotive.unstableByKindDescentScheduleIso_hom_comp_inv_endpointImportedRectangleCount
    (source target : QTraceExpression) :
    (TraceLocalizationWordClass.comp
      (TraceUnstableAnalyticMotive.descentScheduleIso source target).hom
      (TraceUnstableAnalyticMotive.descentScheduleIso source target).inv).endpointImportedRectangleCount =
      (TraceLocalizationInput.descentSchedule source target).localizedSourceObject.importedRectangleCount +
        (TraceLocalizationInput.descentSchedule source target).localizedSourceObject.importedRectangleCount :=
  TraceUnstableAnalyticMotive.descentScheduleIso_hom_comp_inv_endpointImportedRectangleCount
    source
    target

/-- By-kind descent-schedule inverse-hom cancellation endpoint count is target count twice. -/
theorem TraceAnalyticMotive.unstableByKindDescentScheduleIso_inv_comp_hom_endpointImportedRectangleCount
    (source target : QTraceExpression) :
    (TraceLocalizationWordClass.comp
      (TraceUnstableAnalyticMotive.descentScheduleIso source target).inv
      (TraceUnstableAnalyticMotive.descentScheduleIso source target).hom).endpointImportedRectangleCount =
      (TraceLocalizationInput.descentSchedule source target).localizedTargetObject.importedRectangleCount +
        (TraceLocalizationInput.descentSchedule source target).localizedTargetObject.importedRectangleCount :=
  TraceUnstableAnalyticMotive.descentScheduleIso_inv_comp_hom_endpointImportedRectangleCount
    source
    target

/-- By-kind interval-Stokes hom-inverse cancellation endpoint count is source count twice. -/
theorem TraceAnalyticMotive.unstableByKindIntervalStokesIso_hom_comp_inv_endpointImportedRectangleCount
    (source target : QTraceExpression) :
    (TraceLocalizationWordClass.comp
      (TraceUnstableAnalyticMotive.intervalStokesIso source target).hom
      (TraceUnstableAnalyticMotive.intervalStokesIso source target).inv).endpointImportedRectangleCount =
      (TraceLocalizationInput.intervalStokes source target).localizedSourceObject.importedRectangleCount +
        (TraceLocalizationInput.intervalStokes source target).localizedSourceObject.importedRectangleCount :=
  TraceUnstableAnalyticMotive.intervalStokesIso_hom_comp_inv_endpointImportedRectangleCount
    source
    target

/-- By-kind interval-Stokes inverse-hom cancellation endpoint count is target count twice. -/
theorem TraceAnalyticMotive.unstableByKindIntervalStokesIso_inv_comp_hom_endpointImportedRectangleCount
    (source target : QTraceExpression) :
    (TraceLocalizationWordClass.comp
      (TraceUnstableAnalyticMotive.intervalStokesIso source target).inv
      (TraceUnstableAnalyticMotive.intervalStokesIso source target).hom).endpointImportedRectangleCount =
      (TraceLocalizationInput.intervalStokes source target).localizedTargetObject.importedRectangleCount +
        (TraceLocalizationInput.intervalStokes source target).localizedTargetObject.importedRectangleCount :=
  TraceUnstableAnalyticMotive.intervalStokesIso_inv_comp_hom_endpointImportedRectangleCount
    source
    target

/-- By-kind interval-Fubini hom-inverse cancellation endpoint count is source count twice. -/
theorem TraceAnalyticMotive.unstableByKindIntervalFubiniIso_hom_comp_inv_endpointImportedRectangleCount
    (source target : QTraceExpression) :
    (TraceLocalizationWordClass.comp
      (TraceUnstableAnalyticMotive.intervalFubiniIso source target).hom
      (TraceUnstableAnalyticMotive.intervalFubiniIso source target).inv).endpointImportedRectangleCount =
      (TraceLocalizationInput.intervalFubini source target).localizedSourceObject.importedRectangleCount +
        (TraceLocalizationInput.intervalFubini source target).localizedSourceObject.importedRectangleCount :=
  TraceUnstableAnalyticMotive.intervalFubiniIso_hom_comp_inv_endpointImportedRectangleCount
    source
    target

/-- By-kind interval-Fubini inverse-hom cancellation endpoint count is target count twice. -/
theorem TraceAnalyticMotive.unstableByKindIntervalFubiniIso_inv_comp_hom_endpointImportedRectangleCount
    (source target : QTraceExpression) :
    (TraceLocalizationWordClass.comp
      (TraceUnstableAnalyticMotive.intervalFubiniIso source target).inv
      (TraceUnstableAnalyticMotive.intervalFubiniIso source target).hom).endpointImportedRectangleCount =
      (TraceLocalizationInput.intervalFubini source target).localizedTargetObject.importedRectangleCount +
        (TraceLocalizationInput.intervalFubini source target).localizedTargetObject.importedRectangleCount :=
  TraceUnstableAnalyticMotive.intervalFubiniIso_inv_comp_hom_endpointImportedRectangleCount
    source
    target

/-- By-kind Tate-weight-drop hom-inverse cancellation endpoint count is source count twice. -/
theorem TraceAnalyticMotive.unstableByKindTateWeightDropIso_hom_comp_inv_endpointImportedRectangleCount
    (source target : QTraceExpression) :
    (TraceLocalizationWordClass.comp
      (TraceUnstableAnalyticMotive.tateWeightDropIso source target).hom
      (TraceUnstableAnalyticMotive.tateWeightDropIso source target).inv).endpointImportedRectangleCount =
      (TraceLocalizationInput.tateWeightDrop source target).localizedSourceObject.importedRectangleCount +
        (TraceLocalizationInput.tateWeightDrop source target).localizedSourceObject.importedRectangleCount :=
  TraceUnstableAnalyticMotive.tateWeightDropIso_hom_comp_inv_endpointImportedRectangleCount
    source
    target

/-- By-kind Tate-weight-drop inverse-hom cancellation endpoint count is target count twice. -/
theorem TraceAnalyticMotive.unstableByKindTateWeightDropIso_inv_comp_hom_endpointImportedRectangleCount
    (source target : QTraceExpression) :
    (TraceLocalizationWordClass.comp
      (TraceUnstableAnalyticMotive.tateWeightDropIso source target).inv
      (TraceUnstableAnalyticMotive.tateWeightDropIso source target).hom).endpointImportedRectangleCount =
      (TraceLocalizationInput.tateWeightDrop source target).localizedTargetObject.importedRectangleCount +
        (TraceLocalizationInput.tateWeightDrop source target).localizedTargetObject.importedRectangleCount :=
  TraceUnstableAnalyticMotive.tateWeightDropIso_inv_comp_hom_endpointImportedRectangleCount
    source
    target

end AnalyticMotives
end LFunctions
end Boundary
