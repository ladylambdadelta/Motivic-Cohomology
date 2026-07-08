import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Unstable.Inputs.ByKind.Payload.ImportedRectangles.ArrowEndpoints.Owner

/-!
# Root all-kind unstable input imported-rectangle arrow endpoints

This file exposes source and target imported-rectangle lists for hom and
inverse arrows of all six named unstable localization isomorphisms at the
motive-root namespace.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- By-kind descent-channel hom source rectangles are the input source rectangles. -/
theorem TraceAnalyticMotive.unstableByKindDescentChannelIso_hom_sourceImportedRectangles
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.descentChannelIso source target).hom.sourceImportedRectangles =
      (TraceLocalizationInput.descentChannel source target).sourceObject.importedRectangles :=
  TraceUnstableAnalyticMotive.descentChannelIso_hom_sourceImportedRectangles
    source
    target

/-- By-kind descent-channel hom target rectangles are the input target rectangles. -/
theorem TraceAnalyticMotive.unstableByKindDescentChannelIso_hom_targetImportedRectangles
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.descentChannelIso source target).hom.targetImportedRectangles =
      (TraceLocalizationInput.descentChannel source target).targetObject.importedRectangles :=
  TraceUnstableAnalyticMotive.descentChannelIso_hom_targetImportedRectangles
    source
    target

/-- By-kind descent-channel inverse source rectangles are the input target rectangles. -/
theorem TraceAnalyticMotive.unstableByKindDescentChannelIso_inv_sourceImportedRectangles
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.descentChannelIso source target).inv.sourceImportedRectangles =
      (TraceLocalizationInput.descentChannel source target).targetObject.importedRectangles :=
  TraceUnstableAnalyticMotive.descentChannelIso_inv_sourceImportedRectangles
    source
    target

/-- By-kind descent-channel inverse target rectangles are the input source rectangles. -/
theorem TraceAnalyticMotive.unstableByKindDescentChannelIso_inv_targetImportedRectangles
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.descentChannelIso source target).inv.targetImportedRectangles =
      (TraceLocalizationInput.descentChannel source target).sourceObject.importedRectangles :=
  TraceUnstableAnalyticMotive.descentChannelIso_inv_targetImportedRectangles
    source
    target

/-- By-kind descent-refinement hom source rectangles are the input source rectangles. -/
theorem TraceAnalyticMotive.unstableByKindDescentRefinementIso_hom_sourceImportedRectangles
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.descentRefinementIso source target).hom.sourceImportedRectangles =
      (TraceLocalizationInput.descentRefinement source target).sourceObject.importedRectangles :=
  TraceUnstableAnalyticMotive.descentRefinementIso_hom_sourceImportedRectangles
    source
    target

/-- By-kind descent-refinement hom target rectangles are the input target rectangles. -/
theorem TraceAnalyticMotive.unstableByKindDescentRefinementIso_hom_targetImportedRectangles
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.descentRefinementIso source target).hom.targetImportedRectangles =
      (TraceLocalizationInput.descentRefinement source target).targetObject.importedRectangles :=
  TraceUnstableAnalyticMotive.descentRefinementIso_hom_targetImportedRectangles
    source
    target

/-- By-kind descent-refinement inverse source rectangles are the input target rectangles. -/
theorem TraceAnalyticMotive.unstableByKindDescentRefinementIso_inv_sourceImportedRectangles
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.descentRefinementIso source target).inv.sourceImportedRectangles =
      (TraceLocalizationInput.descentRefinement source target).targetObject.importedRectangles :=
  TraceUnstableAnalyticMotive.descentRefinementIso_inv_sourceImportedRectangles
    source
    target

/-- By-kind descent-refinement inverse target rectangles are the input source rectangles. -/
theorem TraceAnalyticMotive.unstableByKindDescentRefinementIso_inv_targetImportedRectangles
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.descentRefinementIso source target).inv.targetImportedRectangles =
      (TraceLocalizationInput.descentRefinement source target).sourceObject.importedRectangles :=
  TraceUnstableAnalyticMotive.descentRefinementIso_inv_targetImportedRectangles
    source
    target

/-- By-kind descent-schedule hom source rectangles are the input source rectangles. -/
theorem TraceAnalyticMotive.unstableByKindDescentScheduleIso_hom_sourceImportedRectangles
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.descentScheduleIso source target).hom.sourceImportedRectangles =
      (TraceLocalizationInput.descentSchedule source target).sourceObject.importedRectangles :=
  TraceUnstableAnalyticMotive.descentScheduleIso_hom_sourceImportedRectangles
    source
    target

/-- By-kind descent-schedule hom target rectangles are the input target rectangles. -/
theorem TraceAnalyticMotive.unstableByKindDescentScheduleIso_hom_targetImportedRectangles
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.descentScheduleIso source target).hom.targetImportedRectangles =
      (TraceLocalizationInput.descentSchedule source target).targetObject.importedRectangles :=
  TraceUnstableAnalyticMotive.descentScheduleIso_hom_targetImportedRectangles
    source
    target

/-- By-kind descent-schedule inverse source rectangles are the input target rectangles. -/
theorem TraceAnalyticMotive.unstableByKindDescentScheduleIso_inv_sourceImportedRectangles
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.descentScheduleIso source target).inv.sourceImportedRectangles =
      (TraceLocalizationInput.descentSchedule source target).targetObject.importedRectangles :=
  TraceUnstableAnalyticMotive.descentScheduleIso_inv_sourceImportedRectangles
    source
    target

/-- By-kind descent-schedule inverse target rectangles are the input source rectangles. -/
theorem TraceAnalyticMotive.unstableByKindDescentScheduleIso_inv_targetImportedRectangles
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.descentScheduleIso source target).inv.targetImportedRectangles =
      (TraceLocalizationInput.descentSchedule source target).sourceObject.importedRectangles :=
  TraceUnstableAnalyticMotive.descentScheduleIso_inv_targetImportedRectangles
    source
    target

/-- By-kind interval-Stokes hom source rectangles are the input source rectangles. -/
theorem TraceAnalyticMotive.unstableByKindIntervalStokesIso_hom_sourceImportedRectangles
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.intervalStokesIso source target).hom.sourceImportedRectangles =
      (TraceLocalizationInput.intervalStokes source target).sourceObject.importedRectangles :=
  TraceUnstableAnalyticMotive.intervalStokesIso_hom_sourceImportedRectangles
    source
    target

/-- By-kind interval-Stokes hom target rectangles are the input target rectangles. -/
theorem TraceAnalyticMotive.unstableByKindIntervalStokesIso_hom_targetImportedRectangles
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.intervalStokesIso source target).hom.targetImportedRectangles =
      (TraceLocalizationInput.intervalStokes source target).targetObject.importedRectangles :=
  TraceUnstableAnalyticMotive.intervalStokesIso_hom_targetImportedRectangles
    source
    target

/-- By-kind interval-Stokes inverse source rectangles are the input target rectangles. -/
theorem TraceAnalyticMotive.unstableByKindIntervalStokesIso_inv_sourceImportedRectangles
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.intervalStokesIso source target).inv.sourceImportedRectangles =
      (TraceLocalizationInput.intervalStokes source target).targetObject.importedRectangles :=
  TraceUnstableAnalyticMotive.intervalStokesIso_inv_sourceImportedRectangles
    source
    target

/-- By-kind interval-Stokes inverse target rectangles are the input source rectangles. -/
theorem TraceAnalyticMotive.unstableByKindIntervalStokesIso_inv_targetImportedRectangles
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.intervalStokesIso source target).inv.targetImportedRectangles =
      (TraceLocalizationInput.intervalStokes source target).sourceObject.importedRectangles :=
  TraceUnstableAnalyticMotive.intervalStokesIso_inv_targetImportedRectangles
    source
    target

/-- By-kind interval-Fubini hom source rectangles are the input source rectangles. -/
theorem TraceAnalyticMotive.unstableByKindIntervalFubiniIso_hom_sourceImportedRectangles
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.intervalFubiniIso source target).hom.sourceImportedRectangles =
      (TraceLocalizationInput.intervalFubini source target).sourceObject.importedRectangles :=
  TraceUnstableAnalyticMotive.intervalFubiniIso_hom_sourceImportedRectangles
    source
    target

/-- By-kind interval-Fubini hom target rectangles are the input target rectangles. -/
theorem TraceAnalyticMotive.unstableByKindIntervalFubiniIso_hom_targetImportedRectangles
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.intervalFubiniIso source target).hom.targetImportedRectangles =
      (TraceLocalizationInput.intervalFubini source target).targetObject.importedRectangles :=
  TraceUnstableAnalyticMotive.intervalFubiniIso_hom_targetImportedRectangles
    source
    target

/-- By-kind interval-Fubini inverse source rectangles are the input target rectangles. -/
theorem TraceAnalyticMotive.unstableByKindIntervalFubiniIso_inv_sourceImportedRectangles
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.intervalFubiniIso source target).inv.sourceImportedRectangles =
      (TraceLocalizationInput.intervalFubini source target).targetObject.importedRectangles :=
  TraceUnstableAnalyticMotive.intervalFubiniIso_inv_sourceImportedRectangles
    source
    target

/-- By-kind interval-Fubini inverse target rectangles are the input source rectangles. -/
theorem TraceAnalyticMotive.unstableByKindIntervalFubiniIso_inv_targetImportedRectangles
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.intervalFubiniIso source target).inv.targetImportedRectangles =
      (TraceLocalizationInput.intervalFubini source target).sourceObject.importedRectangles :=
  TraceUnstableAnalyticMotive.intervalFubiniIso_inv_targetImportedRectangles
    source
    target

/-- By-kind Tate-weight-drop hom source rectangles are the input source rectangles. -/
theorem TraceAnalyticMotive.unstableByKindTateWeightDropIso_hom_sourceImportedRectangles
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.tateWeightDropIso source target).hom.sourceImportedRectangles =
      (TraceLocalizationInput.tateWeightDrop source target).sourceObject.importedRectangles :=
  TraceUnstableAnalyticMotive.tateWeightDropIso_hom_sourceImportedRectangles
    source
    target

/-- By-kind Tate-weight-drop hom target rectangles are the input target rectangles. -/
theorem TraceAnalyticMotive.unstableByKindTateWeightDropIso_hom_targetImportedRectangles
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.tateWeightDropIso source target).hom.targetImportedRectangles =
      (TraceLocalizationInput.tateWeightDrop source target).targetObject.importedRectangles :=
  TraceUnstableAnalyticMotive.tateWeightDropIso_hom_targetImportedRectangles
    source
    target

/-- By-kind Tate-weight-drop inverse source rectangles are the input target rectangles. -/
theorem TraceAnalyticMotive.unstableByKindTateWeightDropIso_inv_sourceImportedRectangles
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.tateWeightDropIso source target).inv.sourceImportedRectangles =
      (TraceLocalizationInput.tateWeightDrop source target).targetObject.importedRectangles :=
  TraceUnstableAnalyticMotive.tateWeightDropIso_inv_sourceImportedRectangles
    source
    target

/-- By-kind Tate-weight-drop inverse target rectangles are the input source rectangles. -/
theorem TraceAnalyticMotive.unstableByKindTateWeightDropIso_inv_targetImportedRectangles
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.tateWeightDropIso source target).inv.targetImportedRectangles =
      (TraceLocalizationInput.tateWeightDrop source target).sourceObject.importedRectangles :=
  TraceUnstableAnalyticMotive.tateWeightDropIso_inv_targetImportedRectangles
    source
    target

end AnalyticMotives
end LFunctions
end Boundary
