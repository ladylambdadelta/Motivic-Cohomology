import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Root.Unstable.Inputs.ImportedRectangles.ArrowEndpoints.Owner

/-!
# Top-root all-kind unstable input imported-rectangle arrow endpoints

This file mirrors the motive-root source and target imported-rectangle list
surface for hom and inverse arrows of all six named unstable localization
isomorphisms.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- The root exposes by-kind descent-channel hom source rectangles. -/
theorem AnalyticMotivesRoot.unstableByKindDescentChannelIso_hom_sourceImportedRectangles
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.descentChannelIso source target).hom.sourceImportedRectangles =
      (TraceLocalizationInput.descentChannel source target).sourceObject.importedRectangles :=
  TraceAnalyticMotive.unstableByKindDescentChannelIso_hom_sourceImportedRectangles
    source
    target

/-- The root exposes by-kind descent-channel hom target rectangles. -/
theorem AnalyticMotivesRoot.unstableByKindDescentChannelIso_hom_targetImportedRectangles
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.descentChannelIso source target).hom.targetImportedRectangles =
      (TraceLocalizationInput.descentChannel source target).targetObject.importedRectangles :=
  TraceAnalyticMotive.unstableByKindDescentChannelIso_hom_targetImportedRectangles
    source
    target

/-- The root exposes by-kind descent-channel inverse source rectangles. -/
theorem AnalyticMotivesRoot.unstableByKindDescentChannelIso_inv_sourceImportedRectangles
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.descentChannelIso source target).inv.sourceImportedRectangles =
      (TraceLocalizationInput.descentChannel source target).targetObject.importedRectangles :=
  TraceAnalyticMotive.unstableByKindDescentChannelIso_inv_sourceImportedRectangles
    source
    target

/-- The root exposes by-kind descent-channel inverse target rectangles. -/
theorem AnalyticMotivesRoot.unstableByKindDescentChannelIso_inv_targetImportedRectangles
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.descentChannelIso source target).inv.targetImportedRectangles =
      (TraceLocalizationInput.descentChannel source target).sourceObject.importedRectangles :=
  TraceAnalyticMotive.unstableByKindDescentChannelIso_inv_targetImportedRectangles
    source
    target

/-- The root exposes by-kind descent-refinement hom source rectangles. -/
theorem AnalyticMotivesRoot.unstableByKindDescentRefinementIso_hom_sourceImportedRectangles
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.descentRefinementIso source target).hom.sourceImportedRectangles =
      (TraceLocalizationInput.descentRefinement source target).sourceObject.importedRectangles :=
  TraceAnalyticMotive.unstableByKindDescentRefinementIso_hom_sourceImportedRectangles
    source
    target

/-- The root exposes by-kind descent-refinement hom target rectangles. -/
theorem AnalyticMotivesRoot.unstableByKindDescentRefinementIso_hom_targetImportedRectangles
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.descentRefinementIso source target).hom.targetImportedRectangles =
      (TraceLocalizationInput.descentRefinement source target).targetObject.importedRectangles :=
  TraceAnalyticMotive.unstableByKindDescentRefinementIso_hom_targetImportedRectangles
    source
    target

/-- The root exposes by-kind descent-refinement inverse source rectangles. -/
theorem AnalyticMotivesRoot.unstableByKindDescentRefinementIso_inv_sourceImportedRectangles
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.descentRefinementIso source target).inv.sourceImportedRectangles =
      (TraceLocalizationInput.descentRefinement source target).targetObject.importedRectangles :=
  TraceAnalyticMotive.unstableByKindDescentRefinementIso_inv_sourceImportedRectangles
    source
    target

/-- The root exposes by-kind descent-refinement inverse target rectangles. -/
theorem AnalyticMotivesRoot.unstableByKindDescentRefinementIso_inv_targetImportedRectangles
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.descentRefinementIso source target).inv.targetImportedRectangles =
      (TraceLocalizationInput.descentRefinement source target).sourceObject.importedRectangles :=
  TraceAnalyticMotive.unstableByKindDescentRefinementIso_inv_targetImportedRectangles
    source
    target

/-- The root exposes by-kind descent-schedule hom source rectangles. -/
theorem AnalyticMotivesRoot.unstableByKindDescentScheduleIso_hom_sourceImportedRectangles
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.descentScheduleIso source target).hom.sourceImportedRectangles =
      (TraceLocalizationInput.descentSchedule source target).sourceObject.importedRectangles :=
  TraceAnalyticMotive.unstableByKindDescentScheduleIso_hom_sourceImportedRectangles
    source
    target

/-- The root exposes by-kind descent-schedule hom target rectangles. -/
theorem AnalyticMotivesRoot.unstableByKindDescentScheduleIso_hom_targetImportedRectangles
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.descentScheduleIso source target).hom.targetImportedRectangles =
      (TraceLocalizationInput.descentSchedule source target).targetObject.importedRectangles :=
  TraceAnalyticMotive.unstableByKindDescentScheduleIso_hom_targetImportedRectangles
    source
    target

/-- The root exposes by-kind descent-schedule inverse source rectangles. -/
theorem AnalyticMotivesRoot.unstableByKindDescentScheduleIso_inv_sourceImportedRectangles
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.descentScheduleIso source target).inv.sourceImportedRectangles =
      (TraceLocalizationInput.descentSchedule source target).targetObject.importedRectangles :=
  TraceAnalyticMotive.unstableByKindDescentScheduleIso_inv_sourceImportedRectangles
    source
    target

/-- The root exposes by-kind descent-schedule inverse target rectangles. -/
theorem AnalyticMotivesRoot.unstableByKindDescentScheduleIso_inv_targetImportedRectangles
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.descentScheduleIso source target).inv.targetImportedRectangles =
      (TraceLocalizationInput.descentSchedule source target).sourceObject.importedRectangles :=
  TraceAnalyticMotive.unstableByKindDescentScheduleIso_inv_targetImportedRectangles
    source
    target

/-- The root exposes by-kind interval-Stokes hom source rectangles. -/
theorem AnalyticMotivesRoot.unstableByKindIntervalStokesIso_hom_sourceImportedRectangles
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.intervalStokesIso source target).hom.sourceImportedRectangles =
      (TraceLocalizationInput.intervalStokes source target).sourceObject.importedRectangles :=
  TraceAnalyticMotive.unstableByKindIntervalStokesIso_hom_sourceImportedRectangles
    source
    target

/-- The root exposes by-kind interval-Stokes hom target rectangles. -/
theorem AnalyticMotivesRoot.unstableByKindIntervalStokesIso_hom_targetImportedRectangles
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.intervalStokesIso source target).hom.targetImportedRectangles =
      (TraceLocalizationInput.intervalStokes source target).targetObject.importedRectangles :=
  TraceAnalyticMotive.unstableByKindIntervalStokesIso_hom_targetImportedRectangles
    source
    target

/-- The root exposes by-kind interval-Stokes inverse source rectangles. -/
theorem AnalyticMotivesRoot.unstableByKindIntervalStokesIso_inv_sourceImportedRectangles
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.intervalStokesIso source target).inv.sourceImportedRectangles =
      (TraceLocalizationInput.intervalStokes source target).targetObject.importedRectangles :=
  TraceAnalyticMotive.unstableByKindIntervalStokesIso_inv_sourceImportedRectangles
    source
    target

/-- The root exposes by-kind interval-Stokes inverse target rectangles. -/
theorem AnalyticMotivesRoot.unstableByKindIntervalStokesIso_inv_targetImportedRectangles
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.intervalStokesIso source target).inv.targetImportedRectangles =
      (TraceLocalizationInput.intervalStokes source target).sourceObject.importedRectangles :=
  TraceAnalyticMotive.unstableByKindIntervalStokesIso_inv_targetImportedRectangles
    source
    target

/-- The root exposes by-kind interval-Fubini hom source rectangles. -/
theorem AnalyticMotivesRoot.unstableByKindIntervalFubiniIso_hom_sourceImportedRectangles
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.intervalFubiniIso source target).hom.sourceImportedRectangles =
      (TraceLocalizationInput.intervalFubini source target).sourceObject.importedRectangles :=
  TraceAnalyticMotive.unstableByKindIntervalFubiniIso_hom_sourceImportedRectangles
    source
    target

/-- The root exposes by-kind interval-Fubini hom target rectangles. -/
theorem AnalyticMotivesRoot.unstableByKindIntervalFubiniIso_hom_targetImportedRectangles
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.intervalFubiniIso source target).hom.targetImportedRectangles =
      (TraceLocalizationInput.intervalFubini source target).targetObject.importedRectangles :=
  TraceAnalyticMotive.unstableByKindIntervalFubiniIso_hom_targetImportedRectangles
    source
    target

/-- The root exposes by-kind interval-Fubini inverse source rectangles. -/
theorem AnalyticMotivesRoot.unstableByKindIntervalFubiniIso_inv_sourceImportedRectangles
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.intervalFubiniIso source target).inv.sourceImportedRectangles =
      (TraceLocalizationInput.intervalFubini source target).targetObject.importedRectangles :=
  TraceAnalyticMotive.unstableByKindIntervalFubiniIso_inv_sourceImportedRectangles
    source
    target

/-- The root exposes by-kind interval-Fubini inverse target rectangles. -/
theorem AnalyticMotivesRoot.unstableByKindIntervalFubiniIso_inv_targetImportedRectangles
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.intervalFubiniIso source target).inv.targetImportedRectangles =
      (TraceLocalizationInput.intervalFubini source target).sourceObject.importedRectangles :=
  TraceAnalyticMotive.unstableByKindIntervalFubiniIso_inv_targetImportedRectangles
    source
    target

/-- The root exposes by-kind Tate-weight-drop hom source rectangles. -/
theorem AnalyticMotivesRoot.unstableByKindTateWeightDropIso_hom_sourceImportedRectangles
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.tateWeightDropIso source target).hom.sourceImportedRectangles =
      (TraceLocalizationInput.tateWeightDrop source target).sourceObject.importedRectangles :=
  TraceAnalyticMotive.unstableByKindTateWeightDropIso_hom_sourceImportedRectangles
    source
    target

/-- The root exposes by-kind Tate-weight-drop hom target rectangles. -/
theorem AnalyticMotivesRoot.unstableByKindTateWeightDropIso_hom_targetImportedRectangles
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.tateWeightDropIso source target).hom.targetImportedRectangles =
      (TraceLocalizationInput.tateWeightDrop source target).targetObject.importedRectangles :=
  TraceAnalyticMotive.unstableByKindTateWeightDropIso_hom_targetImportedRectangles
    source
    target

/-- The root exposes by-kind Tate-weight-drop inverse source rectangles. -/
theorem AnalyticMotivesRoot.unstableByKindTateWeightDropIso_inv_sourceImportedRectangles
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.tateWeightDropIso source target).inv.sourceImportedRectangles =
      (TraceLocalizationInput.tateWeightDrop source target).targetObject.importedRectangles :=
  TraceAnalyticMotive.unstableByKindTateWeightDropIso_inv_sourceImportedRectangles
    source
    target

/-- The root exposes by-kind Tate-weight-drop inverse target rectangles. -/
theorem AnalyticMotivesRoot.unstableByKindTateWeightDropIso_inv_targetImportedRectangles
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.tateWeightDropIso source target).inv.targetImportedRectangles =
      (TraceLocalizationInput.tateWeightDrop source target).sourceObject.importedRectangles :=
  TraceAnalyticMotive.unstableByKindTateWeightDropIso_inv_targetImportedRectangles
    source
    target

end AnalyticMotives
end LFunctions
end Boundary
