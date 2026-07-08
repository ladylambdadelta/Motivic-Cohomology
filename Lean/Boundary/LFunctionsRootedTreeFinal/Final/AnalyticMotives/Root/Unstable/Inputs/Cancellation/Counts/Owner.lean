import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Root.Unstable.Inputs.Cancellation.Counts.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Root.Unstable.Inputs.Cancellation.Counts.LedgerCounts.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Root.Unstable.Inputs.Cancellation.Counts.Lengths.Owner

/-!
# Top-root all-kind unstable cancellation endpoint counts

This file mirrors endpoint imported-rectangle count formulas for all six named
unstable localization cancellation composites.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- The root exposes by-kind descent-channel hom-inverse cancellation endpoint counts. -/
theorem AnalyticMotivesRoot.unstableByKindDescentChannelIso_hom_comp_inv_endpointImportedRectangleCount
    (source target : QTraceExpression) :
    (TraceLocalizationWordClass.comp
      (TraceUnstableAnalyticMotive.descentChannelIso source target).hom
      (TraceUnstableAnalyticMotive.descentChannelIso source target).inv).endpointImportedRectangleCount =
      (TraceLocalizationInput.descentChannel source target).localizedSourceObject.importedRectangleCount +
        (TraceLocalizationInput.descentChannel source target).localizedSourceObject.importedRectangleCount :=
  TraceAnalyticMotive.unstableByKindDescentChannelIso_hom_comp_inv_endpointImportedRectangleCount
    source
    target

/-- The root exposes by-kind descent-channel inverse-hom cancellation endpoint counts. -/
theorem AnalyticMotivesRoot.unstableByKindDescentChannelIso_inv_comp_hom_endpointImportedRectangleCount
    (source target : QTraceExpression) :
    (TraceLocalizationWordClass.comp
      (TraceUnstableAnalyticMotive.descentChannelIso source target).inv
      (TraceUnstableAnalyticMotive.descentChannelIso source target).hom).endpointImportedRectangleCount =
      (TraceLocalizationInput.descentChannel source target).localizedTargetObject.importedRectangleCount +
        (TraceLocalizationInput.descentChannel source target).localizedTargetObject.importedRectangleCount :=
  TraceAnalyticMotive.unstableByKindDescentChannelIso_inv_comp_hom_endpointImportedRectangleCount
    source
    target

/-- The root exposes by-kind descent-refinement hom-inverse cancellation endpoint counts. -/
theorem AnalyticMotivesRoot.unstableByKindDescentRefinementIso_hom_comp_inv_endpointImportedRectangleCount
    (source target : QTraceExpression) :
    (TraceLocalizationWordClass.comp
      (TraceUnstableAnalyticMotive.descentRefinementIso source target).hom
      (TraceUnstableAnalyticMotive.descentRefinementIso source target).inv).endpointImportedRectangleCount =
      (TraceLocalizationInput.descentRefinement source target).localizedSourceObject.importedRectangleCount +
        (TraceLocalizationInput.descentRefinement source target).localizedSourceObject.importedRectangleCount :=
  TraceAnalyticMotive.unstableByKindDescentRefinementIso_hom_comp_inv_endpointImportedRectangleCount
    source
    target

/-- The root exposes by-kind descent-refinement inverse-hom cancellation endpoint counts. -/
theorem AnalyticMotivesRoot.unstableByKindDescentRefinementIso_inv_comp_hom_endpointImportedRectangleCount
    (source target : QTraceExpression) :
    (TraceLocalizationWordClass.comp
      (TraceUnstableAnalyticMotive.descentRefinementIso source target).inv
      (TraceUnstableAnalyticMotive.descentRefinementIso source target).hom).endpointImportedRectangleCount =
      (TraceLocalizationInput.descentRefinement source target).localizedTargetObject.importedRectangleCount +
        (TraceLocalizationInput.descentRefinement source target).localizedTargetObject.importedRectangleCount :=
  TraceAnalyticMotive.unstableByKindDescentRefinementIso_inv_comp_hom_endpointImportedRectangleCount
    source
    target

/-- The root exposes by-kind descent-schedule hom-inverse cancellation endpoint counts. -/
theorem AnalyticMotivesRoot.unstableByKindDescentScheduleIso_hom_comp_inv_endpointImportedRectangleCount
    (source target : QTraceExpression) :
    (TraceLocalizationWordClass.comp
      (TraceUnstableAnalyticMotive.descentScheduleIso source target).hom
      (TraceUnstableAnalyticMotive.descentScheduleIso source target).inv).endpointImportedRectangleCount =
      (TraceLocalizationInput.descentSchedule source target).localizedSourceObject.importedRectangleCount +
        (TraceLocalizationInput.descentSchedule source target).localizedSourceObject.importedRectangleCount :=
  TraceAnalyticMotive.unstableByKindDescentScheduleIso_hom_comp_inv_endpointImportedRectangleCount
    source
    target

/-- The root exposes by-kind descent-schedule inverse-hom cancellation endpoint counts. -/
theorem AnalyticMotivesRoot.unstableByKindDescentScheduleIso_inv_comp_hom_endpointImportedRectangleCount
    (source target : QTraceExpression) :
    (TraceLocalizationWordClass.comp
      (TraceUnstableAnalyticMotive.descentScheduleIso source target).inv
      (TraceUnstableAnalyticMotive.descentScheduleIso source target).hom).endpointImportedRectangleCount =
      (TraceLocalizationInput.descentSchedule source target).localizedTargetObject.importedRectangleCount +
        (TraceLocalizationInput.descentSchedule source target).localizedTargetObject.importedRectangleCount :=
  TraceAnalyticMotive.unstableByKindDescentScheduleIso_inv_comp_hom_endpointImportedRectangleCount
    source
    target

/-- The root exposes by-kind interval-Stokes hom-inverse cancellation endpoint counts. -/
theorem AnalyticMotivesRoot.unstableByKindIntervalStokesIso_hom_comp_inv_endpointImportedRectangleCount
    (source target : QTraceExpression) :
    (TraceLocalizationWordClass.comp
      (TraceUnstableAnalyticMotive.intervalStokesIso source target).hom
      (TraceUnstableAnalyticMotive.intervalStokesIso source target).inv).endpointImportedRectangleCount =
      (TraceLocalizationInput.intervalStokes source target).localizedSourceObject.importedRectangleCount +
        (TraceLocalizationInput.intervalStokes source target).localizedSourceObject.importedRectangleCount :=
  TraceAnalyticMotive.unstableByKindIntervalStokesIso_hom_comp_inv_endpointImportedRectangleCount
    source
    target

/-- The root exposes by-kind interval-Stokes inverse-hom cancellation endpoint counts. -/
theorem AnalyticMotivesRoot.unstableByKindIntervalStokesIso_inv_comp_hom_endpointImportedRectangleCount
    (source target : QTraceExpression) :
    (TraceLocalizationWordClass.comp
      (TraceUnstableAnalyticMotive.intervalStokesIso source target).inv
      (TraceUnstableAnalyticMotive.intervalStokesIso source target).hom).endpointImportedRectangleCount =
      (TraceLocalizationInput.intervalStokes source target).localizedTargetObject.importedRectangleCount +
        (TraceLocalizationInput.intervalStokes source target).localizedTargetObject.importedRectangleCount :=
  TraceAnalyticMotive.unstableByKindIntervalStokesIso_inv_comp_hom_endpointImportedRectangleCount
    source
    target

/-- The root exposes by-kind interval-Fubini hom-inverse cancellation endpoint counts. -/
theorem AnalyticMotivesRoot.unstableByKindIntervalFubiniIso_hom_comp_inv_endpointImportedRectangleCount
    (source target : QTraceExpression) :
    (TraceLocalizationWordClass.comp
      (TraceUnstableAnalyticMotive.intervalFubiniIso source target).hom
      (TraceUnstableAnalyticMotive.intervalFubiniIso source target).inv).endpointImportedRectangleCount =
      (TraceLocalizationInput.intervalFubini source target).localizedSourceObject.importedRectangleCount +
        (TraceLocalizationInput.intervalFubini source target).localizedSourceObject.importedRectangleCount :=
  TraceAnalyticMotive.unstableByKindIntervalFubiniIso_hom_comp_inv_endpointImportedRectangleCount
    source
    target

/-- The root exposes by-kind interval-Fubini inverse-hom cancellation endpoint counts. -/
theorem AnalyticMotivesRoot.unstableByKindIntervalFubiniIso_inv_comp_hom_endpointImportedRectangleCount
    (source target : QTraceExpression) :
    (TraceLocalizationWordClass.comp
      (TraceUnstableAnalyticMotive.intervalFubiniIso source target).inv
      (TraceUnstableAnalyticMotive.intervalFubiniIso source target).hom).endpointImportedRectangleCount =
      (TraceLocalizationInput.intervalFubini source target).localizedTargetObject.importedRectangleCount +
        (TraceLocalizationInput.intervalFubini source target).localizedTargetObject.importedRectangleCount :=
  TraceAnalyticMotive.unstableByKindIntervalFubiniIso_inv_comp_hom_endpointImportedRectangleCount
    source
    target

/-- The root exposes by-kind Tate-weight-drop hom-inverse cancellation endpoint counts. -/
theorem AnalyticMotivesRoot.unstableByKindTateWeightDropIso_hom_comp_inv_endpointImportedRectangleCount
    (source target : QTraceExpression) :
    (TraceLocalizationWordClass.comp
      (TraceUnstableAnalyticMotive.tateWeightDropIso source target).hom
      (TraceUnstableAnalyticMotive.tateWeightDropIso source target).inv).endpointImportedRectangleCount =
      (TraceLocalizationInput.tateWeightDrop source target).localizedSourceObject.importedRectangleCount +
        (TraceLocalizationInput.tateWeightDrop source target).localizedSourceObject.importedRectangleCount :=
  TraceAnalyticMotive.unstableByKindTateWeightDropIso_hom_comp_inv_endpointImportedRectangleCount
    source
    target

/-- The root exposes by-kind Tate-weight-drop inverse-hom cancellation endpoint counts. -/
theorem AnalyticMotivesRoot.unstableByKindTateWeightDropIso_inv_comp_hom_endpointImportedRectangleCount
    (source target : QTraceExpression) :
    (TraceLocalizationWordClass.comp
      (TraceUnstableAnalyticMotive.tateWeightDropIso source target).inv
      (TraceUnstableAnalyticMotive.tateWeightDropIso source target).hom).endpointImportedRectangleCount =
      (TraceLocalizationInput.tateWeightDrop source target).localizedTargetObject.importedRectangleCount +
        (TraceLocalizationInput.tateWeightDrop source target).localizedTargetObject.importedRectangleCount :=
  TraceAnalyticMotive.unstableByKindTateWeightDropIso_inv_comp_hom_endpointImportedRectangleCount
    source
    target

end AnalyticMotives
end LFunctions
end Boundary
