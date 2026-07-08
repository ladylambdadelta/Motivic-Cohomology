import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Unstable.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.LocalizationInput.WordQuotient.Category.Inputs.ByKind.Isomorphisms.Payload.ImportedRectangles.ArrowEndpoints.Owner

/-!
# Imported-rectangle arrow endpoints for unstable named isomorphisms

This file exposes source and target imported finite-rectangle payload through
the hom and inverse arrows of the six named unstable analytic-motive
localization isomorphisms.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Descent-channel unstable hom source rectangles are the input source rectangles. -/
theorem TraceUnstableAnalyticMotive.descentChannelIso_hom_sourceImportedRectangles
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.descentChannelIso source target).hom.sourceImportedRectangles =
      (TraceLocalizationInput.descentChannel source target).sourceObject.importedRectangles :=
  TraceLocalizationInput.descentChannelLocalizedIso_hom_sourceImportedRectangles
    source
    target

/-- Descent-channel unstable hom target rectangles are the input target rectangles. -/
theorem TraceUnstableAnalyticMotive.descentChannelIso_hom_targetImportedRectangles
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.descentChannelIso source target).hom.targetImportedRectangles =
      (TraceLocalizationInput.descentChannel source target).targetObject.importedRectangles :=
  TraceLocalizationInput.descentChannelLocalizedIso_hom_targetImportedRectangles
    source
    target

/-- Descent-channel unstable inverse source rectangles are the input target rectangles. -/
theorem TraceUnstableAnalyticMotive.descentChannelIso_inv_sourceImportedRectangles
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.descentChannelIso source target).inv.sourceImportedRectangles =
      (TraceLocalizationInput.descentChannel source target).targetObject.importedRectangles :=
  TraceLocalizationInput.descentChannelLocalizedIso_inv_sourceImportedRectangles
    source
    target

/-- Descent-channel unstable inverse target rectangles are the input source rectangles. -/
theorem TraceUnstableAnalyticMotive.descentChannelIso_inv_targetImportedRectangles
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.descentChannelIso source target).inv.targetImportedRectangles =
      (TraceLocalizationInput.descentChannel source target).sourceObject.importedRectangles :=
  TraceLocalizationInput.descentChannelLocalizedIso_inv_targetImportedRectangles
    source
    target

/-- Descent-refinement unstable hom source rectangles are the input source rectangles. -/
theorem TraceUnstableAnalyticMotive.descentRefinementIso_hom_sourceImportedRectangles
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.descentRefinementIso source target).hom.sourceImportedRectangles =
      (TraceLocalizationInput.descentRefinement source target).sourceObject.importedRectangles :=
  TraceLocalizationInput.descentRefinementLocalizedIso_hom_sourceImportedRectangles
    source
    target

/-- Descent-refinement unstable hom target rectangles are the input target rectangles. -/
theorem TraceUnstableAnalyticMotive.descentRefinementIso_hom_targetImportedRectangles
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.descentRefinementIso source target).hom.targetImportedRectangles =
      (TraceLocalizationInput.descentRefinement source target).targetObject.importedRectangles :=
  TraceLocalizationInput.descentRefinementLocalizedIso_hom_targetImportedRectangles
    source
    target

/-- Descent-refinement unstable inverse source rectangles are the input target rectangles. -/
theorem TraceUnstableAnalyticMotive.descentRefinementIso_inv_sourceImportedRectangles
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.descentRefinementIso source target).inv.sourceImportedRectangles =
      (TraceLocalizationInput.descentRefinement source target).targetObject.importedRectangles :=
  TraceLocalizationInput.descentRefinementLocalizedIso_inv_sourceImportedRectangles
    source
    target

/-- Descent-refinement unstable inverse target rectangles are the input source rectangles. -/
theorem TraceUnstableAnalyticMotive.descentRefinementIso_inv_targetImportedRectangles
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.descentRefinementIso source target).inv.targetImportedRectangles =
      (TraceLocalizationInput.descentRefinement source target).sourceObject.importedRectangles :=
  TraceLocalizationInput.descentRefinementLocalizedIso_inv_targetImportedRectangles
    source
    target

/-- Descent-schedule unstable hom source rectangles are the input source rectangles. -/
theorem TraceUnstableAnalyticMotive.descentScheduleIso_hom_sourceImportedRectangles
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.descentScheduleIso source target).hom.sourceImportedRectangles =
      (TraceLocalizationInput.descentSchedule source target).sourceObject.importedRectangles :=
  TraceLocalizationInput.descentScheduleLocalizedIso_hom_sourceImportedRectangles
    source
    target

/-- Descent-schedule unstable hom target rectangles are the input target rectangles. -/
theorem TraceUnstableAnalyticMotive.descentScheduleIso_hom_targetImportedRectangles
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.descentScheduleIso source target).hom.targetImportedRectangles =
      (TraceLocalizationInput.descentSchedule source target).targetObject.importedRectangles :=
  TraceLocalizationInput.descentScheduleLocalizedIso_hom_targetImportedRectangles
    source
    target

/-- Descent-schedule unstable inverse source rectangles are the input target rectangles. -/
theorem TraceUnstableAnalyticMotive.descentScheduleIso_inv_sourceImportedRectangles
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.descentScheduleIso source target).inv.sourceImportedRectangles =
      (TraceLocalizationInput.descentSchedule source target).targetObject.importedRectangles :=
  TraceLocalizationInput.descentScheduleLocalizedIso_inv_sourceImportedRectangles
    source
    target

/-- Descent-schedule unstable inverse target rectangles are the input source rectangles. -/
theorem TraceUnstableAnalyticMotive.descentScheduleIso_inv_targetImportedRectangles
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.descentScheduleIso source target).inv.targetImportedRectangles =
      (TraceLocalizationInput.descentSchedule source target).sourceObject.importedRectangles :=
  TraceLocalizationInput.descentScheduleLocalizedIso_inv_targetImportedRectangles
    source
    target

/-- Interval-Stokes unstable hom source rectangles are the input source rectangles. -/
theorem TraceUnstableAnalyticMotive.intervalStokesIso_hom_sourceImportedRectangles
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.intervalStokesIso source target).hom.sourceImportedRectangles =
      (TraceLocalizationInput.intervalStokes source target).sourceObject.importedRectangles :=
  TraceLocalizationInput.intervalStokesLocalizedIso_hom_sourceImportedRectangles
    source
    target

/-- Interval-Stokes unstable hom target rectangles are the input target rectangles. -/
theorem TraceUnstableAnalyticMotive.intervalStokesIso_hom_targetImportedRectangles
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.intervalStokesIso source target).hom.targetImportedRectangles =
      (TraceLocalizationInput.intervalStokes source target).targetObject.importedRectangles :=
  TraceLocalizationInput.intervalStokesLocalizedIso_hom_targetImportedRectangles
    source
    target

/-- Interval-Stokes unstable inverse source rectangles are the input target rectangles. -/
theorem TraceUnstableAnalyticMotive.intervalStokesIso_inv_sourceImportedRectangles
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.intervalStokesIso source target).inv.sourceImportedRectangles =
      (TraceLocalizationInput.intervalStokes source target).targetObject.importedRectangles :=
  TraceLocalizationInput.intervalStokesLocalizedIso_inv_sourceImportedRectangles
    source
    target

/-- Interval-Stokes unstable inverse target rectangles are the input source rectangles. -/
theorem TraceUnstableAnalyticMotive.intervalStokesIso_inv_targetImportedRectangles
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.intervalStokesIso source target).inv.targetImportedRectangles =
      (TraceLocalizationInput.intervalStokes source target).sourceObject.importedRectangles :=
  TraceLocalizationInput.intervalStokesLocalizedIso_inv_targetImportedRectangles
    source
    target

/-- Interval-Fubini unstable hom source rectangles are the input source rectangles. -/
theorem TraceUnstableAnalyticMotive.intervalFubiniIso_hom_sourceImportedRectangles
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.intervalFubiniIso source target).hom.sourceImportedRectangles =
      (TraceLocalizationInput.intervalFubini source target).sourceObject.importedRectangles :=
  TraceLocalizationInput.intervalFubiniLocalizedIso_hom_sourceImportedRectangles
    source
    target

/-- Interval-Fubini unstable hom target rectangles are the input target rectangles. -/
theorem TraceUnstableAnalyticMotive.intervalFubiniIso_hom_targetImportedRectangles
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.intervalFubiniIso source target).hom.targetImportedRectangles =
      (TraceLocalizationInput.intervalFubini source target).targetObject.importedRectangles :=
  TraceLocalizationInput.intervalFubiniLocalizedIso_hom_targetImportedRectangles
    source
    target

/-- Interval-Fubini unstable inverse source rectangles are the input target rectangles. -/
theorem TraceUnstableAnalyticMotive.intervalFubiniIso_inv_sourceImportedRectangles
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.intervalFubiniIso source target).inv.sourceImportedRectangles =
      (TraceLocalizationInput.intervalFubini source target).targetObject.importedRectangles :=
  TraceLocalizationInput.intervalFubiniLocalizedIso_inv_sourceImportedRectangles
    source
    target

/-- Interval-Fubini unstable inverse target rectangles are the input source rectangles. -/
theorem TraceUnstableAnalyticMotive.intervalFubiniIso_inv_targetImportedRectangles
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.intervalFubiniIso source target).inv.targetImportedRectangles =
      (TraceLocalizationInput.intervalFubini source target).sourceObject.importedRectangles :=
  TraceLocalizationInput.intervalFubiniLocalizedIso_inv_targetImportedRectangles
    source
    target

/-- Tate-weight-drop unstable hom source rectangles are the input source rectangles. -/
theorem TraceUnstableAnalyticMotive.tateWeightDropIso_hom_sourceImportedRectangles
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.tateWeightDropIso source target).hom.sourceImportedRectangles =
      (TraceLocalizationInput.tateWeightDrop source target).sourceObject.importedRectangles :=
  TraceLocalizationInput.tateWeightDropLocalizedIso_hom_sourceImportedRectangles
    source
    target

/-- Tate-weight-drop unstable hom target rectangles are the input target rectangles. -/
theorem TraceUnstableAnalyticMotive.tateWeightDropIso_hom_targetImportedRectangles
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.tateWeightDropIso source target).hom.targetImportedRectangles =
      (TraceLocalizationInput.tateWeightDrop source target).targetObject.importedRectangles :=
  TraceLocalizationInput.tateWeightDropLocalizedIso_hom_targetImportedRectangles
    source
    target

/-- Tate-weight-drop unstable inverse source rectangles are the input target rectangles. -/
theorem TraceUnstableAnalyticMotive.tateWeightDropIso_inv_sourceImportedRectangles
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.tateWeightDropIso source target).inv.sourceImportedRectangles =
      (TraceLocalizationInput.tateWeightDrop source target).targetObject.importedRectangles :=
  TraceLocalizationInput.tateWeightDropLocalizedIso_inv_sourceImportedRectangles
    source
    target

/-- Tate-weight-drop unstable inverse target rectangles are the input source rectangles. -/
theorem TraceUnstableAnalyticMotive.tateWeightDropIso_inv_targetImportedRectangles
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.tateWeightDropIso source target).inv.targetImportedRectangles =
      (TraceLocalizationInput.tateWeightDrop source target).sourceObject.importedRectangles :=
  TraceLocalizationInput.tateWeightDropLocalizedIso_inv_targetImportedRectangles
    source
    target

end AnalyticMotives
end LFunctions
end Boundary
