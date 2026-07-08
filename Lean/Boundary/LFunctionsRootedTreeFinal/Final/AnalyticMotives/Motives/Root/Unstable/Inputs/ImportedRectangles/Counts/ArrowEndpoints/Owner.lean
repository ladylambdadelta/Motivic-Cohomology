import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Unstable.Inputs.ByKind.Payload.ImportedRectangles.Counts.ArrowEndpoints.Owner

/-!
# Root all-kind unstable input imported-rectangle arrow-endpoint counts

This file exposes source and target imported-rectangle counts for hom and
inverse arrows of all six named unstable localization isomorphisms at the
motive-root namespace.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- By-kind descent-channel hom source rectangle count is the input source count. -/
theorem TraceAnalyticMotive.unstableByKindDescentChannelIso_hom_sourceImportedRectangleCount
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.descentChannelIso source target).hom.sourceImportedRectangleCount =
      (TraceLocalizationInput.descentChannel source target).sourceObject.importedRectangleCount :=
  TraceUnstableAnalyticMotive.descentChannelIso_hom_sourceImportedRectangleCount
    source
    target

/-- By-kind descent-channel hom target rectangle count is the input target count. -/
theorem TraceAnalyticMotive.unstableByKindDescentChannelIso_hom_targetImportedRectangleCount
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.descentChannelIso source target).hom.targetImportedRectangleCount =
      (TraceLocalizationInput.descentChannel source target).targetObject.importedRectangleCount :=
  TraceUnstableAnalyticMotive.descentChannelIso_hom_targetImportedRectangleCount
    source
    target

/-- By-kind descent-channel inverse source rectangle count is the input target count. -/
theorem TraceAnalyticMotive.unstableByKindDescentChannelIso_inv_sourceImportedRectangleCount
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.descentChannelIso source target).inv.sourceImportedRectangleCount =
      (TraceLocalizationInput.descentChannel source target).targetObject.importedRectangleCount :=
  TraceUnstableAnalyticMotive.descentChannelIso_inv_sourceImportedRectangleCount
    source
    target

/-- By-kind descent-channel inverse target rectangle count is the input source count. -/
theorem TraceAnalyticMotive.unstableByKindDescentChannelIso_inv_targetImportedRectangleCount
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.descentChannelIso source target).inv.targetImportedRectangleCount =
      (TraceLocalizationInput.descentChannel source target).sourceObject.importedRectangleCount :=
  TraceUnstableAnalyticMotive.descentChannelIso_inv_targetImportedRectangleCount
    source
    target

/-- By-kind descent-refinement hom source rectangle count is the input source count. -/
theorem TraceAnalyticMotive.unstableByKindDescentRefinementIso_hom_sourceImportedRectangleCount
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.descentRefinementIso source target).hom.sourceImportedRectangleCount =
      (TraceLocalizationInput.descentRefinement source target).sourceObject.importedRectangleCount :=
  TraceUnstableAnalyticMotive.descentRefinementIso_hom_sourceImportedRectangleCount
    source
    target

/-- By-kind descent-refinement hom target rectangle count is the input target count. -/
theorem TraceAnalyticMotive.unstableByKindDescentRefinementIso_hom_targetImportedRectangleCount
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.descentRefinementIso source target).hom.targetImportedRectangleCount =
      (TraceLocalizationInput.descentRefinement source target).targetObject.importedRectangleCount :=
  TraceUnstableAnalyticMotive.descentRefinementIso_hom_targetImportedRectangleCount
    source
    target

/-- By-kind descent-refinement inverse source rectangle count is the input target count. -/
theorem TraceAnalyticMotive.unstableByKindDescentRefinementIso_inv_sourceImportedRectangleCount
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.descentRefinementIso source target).inv.sourceImportedRectangleCount =
      (TraceLocalizationInput.descentRefinement source target).targetObject.importedRectangleCount :=
  TraceUnstableAnalyticMotive.descentRefinementIso_inv_sourceImportedRectangleCount
    source
    target

/-- By-kind descent-refinement inverse target rectangle count is the input source count. -/
theorem TraceAnalyticMotive.unstableByKindDescentRefinementIso_inv_targetImportedRectangleCount
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.descentRefinementIso source target).inv.targetImportedRectangleCount =
      (TraceLocalizationInput.descentRefinement source target).sourceObject.importedRectangleCount :=
  TraceUnstableAnalyticMotive.descentRefinementIso_inv_targetImportedRectangleCount
    source
    target

/-- By-kind descent-schedule hom source rectangle count is the input source count. -/
theorem TraceAnalyticMotive.unstableByKindDescentScheduleIso_hom_sourceImportedRectangleCount
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.descentScheduleIso source target).hom.sourceImportedRectangleCount =
      (TraceLocalizationInput.descentSchedule source target).sourceObject.importedRectangleCount :=
  TraceUnstableAnalyticMotive.descentScheduleIso_hom_sourceImportedRectangleCount
    source
    target

/-- By-kind descent-schedule hom target rectangle count is the input target count. -/
theorem TraceAnalyticMotive.unstableByKindDescentScheduleIso_hom_targetImportedRectangleCount
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.descentScheduleIso source target).hom.targetImportedRectangleCount =
      (TraceLocalizationInput.descentSchedule source target).targetObject.importedRectangleCount :=
  TraceUnstableAnalyticMotive.descentScheduleIso_hom_targetImportedRectangleCount
    source
    target

/-- By-kind descent-schedule inverse source rectangle count is the input target count. -/
theorem TraceAnalyticMotive.unstableByKindDescentScheduleIso_inv_sourceImportedRectangleCount
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.descentScheduleIso source target).inv.sourceImportedRectangleCount =
      (TraceLocalizationInput.descentSchedule source target).targetObject.importedRectangleCount :=
  TraceUnstableAnalyticMotive.descentScheduleIso_inv_sourceImportedRectangleCount
    source
    target

/-- By-kind descent-schedule inverse target rectangle count is the input source count. -/
theorem TraceAnalyticMotive.unstableByKindDescentScheduleIso_inv_targetImportedRectangleCount
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.descentScheduleIso source target).inv.targetImportedRectangleCount =
      (TraceLocalizationInput.descentSchedule source target).sourceObject.importedRectangleCount :=
  TraceUnstableAnalyticMotive.descentScheduleIso_inv_targetImportedRectangleCount
    source
    target

/-- By-kind interval-Stokes hom source rectangle count is the input source count. -/
theorem TraceAnalyticMotive.unstableByKindIntervalStokesIso_hom_sourceImportedRectangleCount
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.intervalStokesIso source target).hom.sourceImportedRectangleCount =
      (TraceLocalizationInput.intervalStokes source target).sourceObject.importedRectangleCount :=
  TraceUnstableAnalyticMotive.intervalStokesIso_hom_sourceImportedRectangleCount
    source
    target

/-- By-kind interval-Stokes hom target rectangle count is the input target count. -/
theorem TraceAnalyticMotive.unstableByKindIntervalStokesIso_hom_targetImportedRectangleCount
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.intervalStokesIso source target).hom.targetImportedRectangleCount =
      (TraceLocalizationInput.intervalStokes source target).targetObject.importedRectangleCount :=
  TraceUnstableAnalyticMotive.intervalStokesIso_hom_targetImportedRectangleCount
    source
    target

/-- By-kind interval-Stokes inverse source rectangle count is the input target count. -/
theorem TraceAnalyticMotive.unstableByKindIntervalStokesIso_inv_sourceImportedRectangleCount
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.intervalStokesIso source target).inv.sourceImportedRectangleCount =
      (TraceLocalizationInput.intervalStokes source target).targetObject.importedRectangleCount :=
  TraceUnstableAnalyticMotive.intervalStokesIso_inv_sourceImportedRectangleCount
    source
    target

/-- By-kind interval-Stokes inverse target rectangle count is the input source count. -/
theorem TraceAnalyticMotive.unstableByKindIntervalStokesIso_inv_targetImportedRectangleCount
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.intervalStokesIso source target).inv.targetImportedRectangleCount =
      (TraceLocalizationInput.intervalStokes source target).sourceObject.importedRectangleCount :=
  TraceUnstableAnalyticMotive.intervalStokesIso_inv_targetImportedRectangleCount
    source
    target

/-- By-kind interval-Fubini hom source rectangle count is the input source count. -/
theorem TraceAnalyticMotive.unstableByKindIntervalFubiniIso_hom_sourceImportedRectangleCount
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.intervalFubiniIso source target).hom.sourceImportedRectangleCount =
      (TraceLocalizationInput.intervalFubini source target).sourceObject.importedRectangleCount :=
  TraceUnstableAnalyticMotive.intervalFubiniIso_hom_sourceImportedRectangleCount
    source
    target

/-- By-kind interval-Fubini hom target rectangle count is the input target count. -/
theorem TraceAnalyticMotive.unstableByKindIntervalFubiniIso_hom_targetImportedRectangleCount
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.intervalFubiniIso source target).hom.targetImportedRectangleCount =
      (TraceLocalizationInput.intervalFubini source target).targetObject.importedRectangleCount :=
  TraceUnstableAnalyticMotive.intervalFubiniIso_hom_targetImportedRectangleCount
    source
    target

/-- By-kind interval-Fubini inverse source rectangle count is the input target count. -/
theorem TraceAnalyticMotive.unstableByKindIntervalFubiniIso_inv_sourceImportedRectangleCount
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.intervalFubiniIso source target).inv.sourceImportedRectangleCount =
      (TraceLocalizationInput.intervalFubini source target).targetObject.importedRectangleCount :=
  TraceUnstableAnalyticMotive.intervalFubiniIso_inv_sourceImportedRectangleCount
    source
    target

/-- By-kind interval-Fubini inverse target rectangle count is the input source count. -/
theorem TraceAnalyticMotive.unstableByKindIntervalFubiniIso_inv_targetImportedRectangleCount
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.intervalFubiniIso source target).inv.targetImportedRectangleCount =
      (TraceLocalizationInput.intervalFubini source target).sourceObject.importedRectangleCount :=
  TraceUnstableAnalyticMotive.intervalFubiniIso_inv_targetImportedRectangleCount
    source
    target

/-- By-kind Tate-weight-drop hom source rectangle count is the input source count. -/
theorem TraceAnalyticMotive.unstableByKindTateWeightDropIso_hom_sourceImportedRectangleCount
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.tateWeightDropIso source target).hom.sourceImportedRectangleCount =
      (TraceLocalizationInput.tateWeightDrop source target).sourceObject.importedRectangleCount :=
  TraceUnstableAnalyticMotive.tateWeightDropIso_hom_sourceImportedRectangleCount
    source
    target

/-- By-kind Tate-weight-drop hom target rectangle count is the input target count. -/
theorem TraceAnalyticMotive.unstableByKindTateWeightDropIso_hom_targetImportedRectangleCount
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.tateWeightDropIso source target).hom.targetImportedRectangleCount =
      (TraceLocalizationInput.tateWeightDrop source target).targetObject.importedRectangleCount :=
  TraceUnstableAnalyticMotive.tateWeightDropIso_hom_targetImportedRectangleCount
    source
    target

/-- By-kind Tate-weight-drop inverse source rectangle count is the input target count. -/
theorem TraceAnalyticMotive.unstableByKindTateWeightDropIso_inv_sourceImportedRectangleCount
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.tateWeightDropIso source target).inv.sourceImportedRectangleCount =
      (TraceLocalizationInput.tateWeightDrop source target).targetObject.importedRectangleCount :=
  TraceUnstableAnalyticMotive.tateWeightDropIso_inv_sourceImportedRectangleCount
    source
    target

/-- By-kind Tate-weight-drop inverse target rectangle count is the input source count. -/
theorem TraceAnalyticMotive.unstableByKindTateWeightDropIso_inv_targetImportedRectangleCount
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.tateWeightDropIso source target).inv.targetImportedRectangleCount =
      (TraceLocalizationInput.tateWeightDrop source target).sourceObject.importedRectangleCount :=
  TraceUnstableAnalyticMotive.tateWeightDropIso_inv_targetImportedRectangleCount
    source
    target

end AnalyticMotives
end LFunctions
end Boundary
