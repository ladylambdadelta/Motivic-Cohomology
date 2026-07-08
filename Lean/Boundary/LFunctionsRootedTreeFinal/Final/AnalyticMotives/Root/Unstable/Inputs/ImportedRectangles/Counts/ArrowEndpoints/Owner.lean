import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Root.Unstable.Inputs.ImportedRectangles.Counts.ArrowEndpoints.Owner

/-!
# Top-root all-kind unstable input imported-rectangle arrow-endpoint counts

This file mirrors the motive-root source and target imported-rectangle count
surface for hom and inverse arrows of all six named unstable localization
isomorphisms.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- The root exposes by-kind descent-channel hom source rectangle counts. -/
theorem AnalyticMotivesRoot.unstableByKindDescentChannelIso_hom_sourceImportedRectangleCount
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.descentChannelIso source target).hom.sourceImportedRectangleCount =
      (TraceLocalizationInput.descentChannel source target).sourceObject.importedRectangleCount :=
  TraceAnalyticMotive.unstableByKindDescentChannelIso_hom_sourceImportedRectangleCount
    source
    target

/-- The root exposes by-kind descent-channel hom target rectangle counts. -/
theorem AnalyticMotivesRoot.unstableByKindDescentChannelIso_hom_targetImportedRectangleCount
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.descentChannelIso source target).hom.targetImportedRectangleCount =
      (TraceLocalizationInput.descentChannel source target).targetObject.importedRectangleCount :=
  TraceAnalyticMotive.unstableByKindDescentChannelIso_hom_targetImportedRectangleCount
    source
    target

/-- The root exposes by-kind descent-channel inverse source rectangle counts. -/
theorem AnalyticMotivesRoot.unstableByKindDescentChannelIso_inv_sourceImportedRectangleCount
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.descentChannelIso source target).inv.sourceImportedRectangleCount =
      (TraceLocalizationInput.descentChannel source target).targetObject.importedRectangleCount :=
  TraceAnalyticMotive.unstableByKindDescentChannelIso_inv_sourceImportedRectangleCount
    source
    target

/-- The root exposes by-kind descent-channel inverse target rectangle counts. -/
theorem AnalyticMotivesRoot.unstableByKindDescentChannelIso_inv_targetImportedRectangleCount
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.descentChannelIso source target).inv.targetImportedRectangleCount =
      (TraceLocalizationInput.descentChannel source target).sourceObject.importedRectangleCount :=
  TraceAnalyticMotive.unstableByKindDescentChannelIso_inv_targetImportedRectangleCount
    source
    target

/-- The root exposes by-kind descent-refinement hom source rectangle counts. -/
theorem AnalyticMotivesRoot.unstableByKindDescentRefinementIso_hom_sourceImportedRectangleCount
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.descentRefinementIso source target).hom.sourceImportedRectangleCount =
      (TraceLocalizationInput.descentRefinement source target).sourceObject.importedRectangleCount :=
  TraceAnalyticMotive.unstableByKindDescentRefinementIso_hom_sourceImportedRectangleCount
    source
    target

/-- The root exposes by-kind descent-refinement hom target rectangle counts. -/
theorem AnalyticMotivesRoot.unstableByKindDescentRefinementIso_hom_targetImportedRectangleCount
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.descentRefinementIso source target).hom.targetImportedRectangleCount =
      (TraceLocalizationInput.descentRefinement source target).targetObject.importedRectangleCount :=
  TraceAnalyticMotive.unstableByKindDescentRefinementIso_hom_targetImportedRectangleCount
    source
    target

/-- The root exposes by-kind descent-refinement inverse source rectangle counts. -/
theorem AnalyticMotivesRoot.unstableByKindDescentRefinementIso_inv_sourceImportedRectangleCount
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.descentRefinementIso source target).inv.sourceImportedRectangleCount =
      (TraceLocalizationInput.descentRefinement source target).targetObject.importedRectangleCount :=
  TraceAnalyticMotive.unstableByKindDescentRefinementIso_inv_sourceImportedRectangleCount
    source
    target

/-- The root exposes by-kind descent-refinement inverse target rectangle counts. -/
theorem AnalyticMotivesRoot.unstableByKindDescentRefinementIso_inv_targetImportedRectangleCount
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.descentRefinementIso source target).inv.targetImportedRectangleCount =
      (TraceLocalizationInput.descentRefinement source target).sourceObject.importedRectangleCount :=
  TraceAnalyticMotive.unstableByKindDescentRefinementIso_inv_targetImportedRectangleCount
    source
    target

/-- The root exposes by-kind descent-schedule hom source rectangle counts. -/
theorem AnalyticMotivesRoot.unstableByKindDescentScheduleIso_hom_sourceImportedRectangleCount
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.descentScheduleIso source target).hom.sourceImportedRectangleCount =
      (TraceLocalizationInput.descentSchedule source target).sourceObject.importedRectangleCount :=
  TraceAnalyticMotive.unstableByKindDescentScheduleIso_hom_sourceImportedRectangleCount
    source
    target

/-- The root exposes by-kind descent-schedule hom target rectangle counts. -/
theorem AnalyticMotivesRoot.unstableByKindDescentScheduleIso_hom_targetImportedRectangleCount
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.descentScheduleIso source target).hom.targetImportedRectangleCount =
      (TraceLocalizationInput.descentSchedule source target).targetObject.importedRectangleCount :=
  TraceAnalyticMotive.unstableByKindDescentScheduleIso_hom_targetImportedRectangleCount
    source
    target

/-- The root exposes by-kind descent-schedule inverse source rectangle counts. -/
theorem AnalyticMotivesRoot.unstableByKindDescentScheduleIso_inv_sourceImportedRectangleCount
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.descentScheduleIso source target).inv.sourceImportedRectangleCount =
      (TraceLocalizationInput.descentSchedule source target).targetObject.importedRectangleCount :=
  TraceAnalyticMotive.unstableByKindDescentScheduleIso_inv_sourceImportedRectangleCount
    source
    target

/-- The root exposes by-kind descent-schedule inverse target rectangle counts. -/
theorem AnalyticMotivesRoot.unstableByKindDescentScheduleIso_inv_targetImportedRectangleCount
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.descentScheduleIso source target).inv.targetImportedRectangleCount =
      (TraceLocalizationInput.descentSchedule source target).sourceObject.importedRectangleCount :=
  TraceAnalyticMotive.unstableByKindDescentScheduleIso_inv_targetImportedRectangleCount
    source
    target

/-- The root exposes by-kind interval-Stokes hom source rectangle counts. -/
theorem AnalyticMotivesRoot.unstableByKindIntervalStokesIso_hom_sourceImportedRectangleCount
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.intervalStokesIso source target).hom.sourceImportedRectangleCount =
      (TraceLocalizationInput.intervalStokes source target).sourceObject.importedRectangleCount :=
  TraceAnalyticMotive.unstableByKindIntervalStokesIso_hom_sourceImportedRectangleCount
    source
    target

/-- The root exposes by-kind interval-Stokes hom target rectangle counts. -/
theorem AnalyticMotivesRoot.unstableByKindIntervalStokesIso_hom_targetImportedRectangleCount
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.intervalStokesIso source target).hom.targetImportedRectangleCount =
      (TraceLocalizationInput.intervalStokes source target).targetObject.importedRectangleCount :=
  TraceAnalyticMotive.unstableByKindIntervalStokesIso_hom_targetImportedRectangleCount
    source
    target

/-- The root exposes by-kind interval-Stokes inverse source rectangle counts. -/
theorem AnalyticMotivesRoot.unstableByKindIntervalStokesIso_inv_sourceImportedRectangleCount
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.intervalStokesIso source target).inv.sourceImportedRectangleCount =
      (TraceLocalizationInput.intervalStokes source target).targetObject.importedRectangleCount :=
  TraceAnalyticMotive.unstableByKindIntervalStokesIso_inv_sourceImportedRectangleCount
    source
    target

/-- The root exposes by-kind interval-Stokes inverse target rectangle counts. -/
theorem AnalyticMotivesRoot.unstableByKindIntervalStokesIso_inv_targetImportedRectangleCount
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.intervalStokesIso source target).inv.targetImportedRectangleCount =
      (TraceLocalizationInput.intervalStokes source target).sourceObject.importedRectangleCount :=
  TraceAnalyticMotive.unstableByKindIntervalStokesIso_inv_targetImportedRectangleCount
    source
    target

/-- The root exposes by-kind interval-Fubini hom source rectangle counts. -/
theorem AnalyticMotivesRoot.unstableByKindIntervalFubiniIso_hom_sourceImportedRectangleCount
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.intervalFubiniIso source target).hom.sourceImportedRectangleCount =
      (TraceLocalizationInput.intervalFubini source target).sourceObject.importedRectangleCount :=
  TraceAnalyticMotive.unstableByKindIntervalFubiniIso_hom_sourceImportedRectangleCount
    source
    target

/-- The root exposes by-kind interval-Fubini hom target rectangle counts. -/
theorem AnalyticMotivesRoot.unstableByKindIntervalFubiniIso_hom_targetImportedRectangleCount
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.intervalFubiniIso source target).hom.targetImportedRectangleCount =
      (TraceLocalizationInput.intervalFubini source target).targetObject.importedRectangleCount :=
  TraceAnalyticMotive.unstableByKindIntervalFubiniIso_hom_targetImportedRectangleCount
    source
    target

/-- The root exposes by-kind interval-Fubini inverse source rectangle counts. -/
theorem AnalyticMotivesRoot.unstableByKindIntervalFubiniIso_inv_sourceImportedRectangleCount
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.intervalFubiniIso source target).inv.sourceImportedRectangleCount =
      (TraceLocalizationInput.intervalFubini source target).targetObject.importedRectangleCount :=
  TraceAnalyticMotive.unstableByKindIntervalFubiniIso_inv_sourceImportedRectangleCount
    source
    target

/-- The root exposes by-kind interval-Fubini inverse target rectangle counts. -/
theorem AnalyticMotivesRoot.unstableByKindIntervalFubiniIso_inv_targetImportedRectangleCount
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.intervalFubiniIso source target).inv.targetImportedRectangleCount =
      (TraceLocalizationInput.intervalFubini source target).sourceObject.importedRectangleCount :=
  TraceAnalyticMotive.unstableByKindIntervalFubiniIso_inv_targetImportedRectangleCount
    source
    target

/-- The root exposes by-kind Tate-weight-drop hom source rectangle counts. -/
theorem AnalyticMotivesRoot.unstableByKindTateWeightDropIso_hom_sourceImportedRectangleCount
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.tateWeightDropIso source target).hom.sourceImportedRectangleCount =
      (TraceLocalizationInput.tateWeightDrop source target).sourceObject.importedRectangleCount :=
  TraceAnalyticMotive.unstableByKindTateWeightDropIso_hom_sourceImportedRectangleCount
    source
    target

/-- The root exposes by-kind Tate-weight-drop hom target rectangle counts. -/
theorem AnalyticMotivesRoot.unstableByKindTateWeightDropIso_hom_targetImportedRectangleCount
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.tateWeightDropIso source target).hom.targetImportedRectangleCount =
      (TraceLocalizationInput.tateWeightDrop source target).targetObject.importedRectangleCount :=
  TraceAnalyticMotive.unstableByKindTateWeightDropIso_hom_targetImportedRectangleCount
    source
    target

/-- The root exposes by-kind Tate-weight-drop inverse source rectangle counts. -/
theorem AnalyticMotivesRoot.unstableByKindTateWeightDropIso_inv_sourceImportedRectangleCount
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.tateWeightDropIso source target).inv.sourceImportedRectangleCount =
      (TraceLocalizationInput.tateWeightDrop source target).targetObject.importedRectangleCount :=
  TraceAnalyticMotive.unstableByKindTateWeightDropIso_inv_sourceImportedRectangleCount
    source
    target

/-- The root exposes by-kind Tate-weight-drop inverse target rectangle counts. -/
theorem AnalyticMotivesRoot.unstableByKindTateWeightDropIso_inv_targetImportedRectangleCount
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.tateWeightDropIso source target).inv.targetImportedRectangleCount =
      (TraceLocalizationInput.tateWeightDrop source target).sourceObject.importedRectangleCount :=
  TraceAnalyticMotive.unstableByKindTateWeightDropIso_inv_targetImportedRectangleCount
    source
    target

end AnalyticMotives
end LFunctions
end Boundary
