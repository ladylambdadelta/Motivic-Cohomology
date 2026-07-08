import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Unstable.Inputs.ByKind.Payload.ImportedRectangles.ArrowEndpoints.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.LocalizationInput.WordQuotient.Category.Inputs.ByKind.Isomorphisms.Payload.ImportedRectangles.Counts.ArrowEndpoints.Owner

/-!
# Imported-rectangle arrow-endpoint counts for unstable named isomorphisms

This file exposes source and target imported-rectangle counts through the hom
and inverse arrows of the six named unstable analytic-motive localization
isomorphisms.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Descent-channel unstable hom source rectangle count is the input source count. -/
theorem TraceUnstableAnalyticMotive.descentChannelIso_hom_sourceImportedRectangleCount
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.descentChannelIso source target).hom.sourceImportedRectangleCount =
      (TraceLocalizationInput.descentChannel source target).sourceObject.importedRectangleCount :=
  TraceLocalizationInput.descentChannelLocalizedIso_hom_sourceImportedRectangleCount
    source
    target

/-- Descent-channel unstable hom target rectangle count is the input target count. -/
theorem TraceUnstableAnalyticMotive.descentChannelIso_hom_targetImportedRectangleCount
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.descentChannelIso source target).hom.targetImportedRectangleCount =
      (TraceLocalizationInput.descentChannel source target).targetObject.importedRectangleCount :=
  TraceLocalizationInput.descentChannelLocalizedIso_hom_targetImportedRectangleCount
    source
    target

/-- Descent-channel unstable inverse source rectangle count is the input target count. -/
theorem TraceUnstableAnalyticMotive.descentChannelIso_inv_sourceImportedRectangleCount
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.descentChannelIso source target).inv.sourceImportedRectangleCount =
      (TraceLocalizationInput.descentChannel source target).targetObject.importedRectangleCount :=
  TraceLocalizationInput.descentChannelLocalizedIso_inv_sourceImportedRectangleCount
    source
    target

/-- Descent-channel unstable inverse target rectangle count is the input source count. -/
theorem TraceUnstableAnalyticMotive.descentChannelIso_inv_targetImportedRectangleCount
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.descentChannelIso source target).inv.targetImportedRectangleCount =
      (TraceLocalizationInput.descentChannel source target).sourceObject.importedRectangleCount :=
  TraceLocalizationInput.descentChannelLocalizedIso_inv_targetImportedRectangleCount
    source
    target

/-- Descent-refinement unstable hom source rectangle count is the input source count. -/
theorem TraceUnstableAnalyticMotive.descentRefinementIso_hom_sourceImportedRectangleCount
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.descentRefinementIso source target).hom.sourceImportedRectangleCount =
      (TraceLocalizationInput.descentRefinement source target).sourceObject.importedRectangleCount :=
  TraceLocalizationInput.descentRefinementLocalizedIso_hom_sourceImportedRectangleCount
    source
    target

/-- Descent-refinement unstable hom target rectangle count is the input target count. -/
theorem TraceUnstableAnalyticMotive.descentRefinementIso_hom_targetImportedRectangleCount
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.descentRefinementIso source target).hom.targetImportedRectangleCount =
      (TraceLocalizationInput.descentRefinement source target).targetObject.importedRectangleCount :=
  TraceLocalizationInput.descentRefinementLocalizedIso_hom_targetImportedRectangleCount
    source
    target

/-- Descent-refinement unstable inverse source rectangle count is the input target count. -/
theorem TraceUnstableAnalyticMotive.descentRefinementIso_inv_sourceImportedRectangleCount
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.descentRefinementIso source target).inv.sourceImportedRectangleCount =
      (TraceLocalizationInput.descentRefinement source target).targetObject.importedRectangleCount :=
  TraceLocalizationInput.descentRefinementLocalizedIso_inv_sourceImportedRectangleCount
    source
    target

/-- Descent-refinement unstable inverse target rectangle count is the input source count. -/
theorem TraceUnstableAnalyticMotive.descentRefinementIso_inv_targetImportedRectangleCount
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.descentRefinementIso source target).inv.targetImportedRectangleCount =
      (TraceLocalizationInput.descentRefinement source target).sourceObject.importedRectangleCount :=
  TraceLocalizationInput.descentRefinementLocalizedIso_inv_targetImportedRectangleCount
    source
    target

/-- Descent-schedule unstable hom source rectangle count is the input source count. -/
theorem TraceUnstableAnalyticMotive.descentScheduleIso_hom_sourceImportedRectangleCount
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.descentScheduleIso source target).hom.sourceImportedRectangleCount =
      (TraceLocalizationInput.descentSchedule source target).sourceObject.importedRectangleCount :=
  TraceLocalizationInput.descentScheduleLocalizedIso_hom_sourceImportedRectangleCount
    source
    target

/-- Descent-schedule unstable hom target rectangle count is the input target count. -/
theorem TraceUnstableAnalyticMotive.descentScheduleIso_hom_targetImportedRectangleCount
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.descentScheduleIso source target).hom.targetImportedRectangleCount =
      (TraceLocalizationInput.descentSchedule source target).targetObject.importedRectangleCount :=
  TraceLocalizationInput.descentScheduleLocalizedIso_hom_targetImportedRectangleCount
    source
    target

/-- Descent-schedule unstable inverse source rectangle count is the input target count. -/
theorem TraceUnstableAnalyticMotive.descentScheduleIso_inv_sourceImportedRectangleCount
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.descentScheduleIso source target).inv.sourceImportedRectangleCount =
      (TraceLocalizationInput.descentSchedule source target).targetObject.importedRectangleCount :=
  TraceLocalizationInput.descentScheduleLocalizedIso_inv_sourceImportedRectangleCount
    source
    target

/-- Descent-schedule unstable inverse target rectangle count is the input source count. -/
theorem TraceUnstableAnalyticMotive.descentScheduleIso_inv_targetImportedRectangleCount
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.descentScheduleIso source target).inv.targetImportedRectangleCount =
      (TraceLocalizationInput.descentSchedule source target).sourceObject.importedRectangleCount :=
  TraceLocalizationInput.descentScheduleLocalizedIso_inv_targetImportedRectangleCount
    source
    target

/-- Interval-Stokes unstable hom source rectangle count is the input source count. -/
theorem TraceUnstableAnalyticMotive.intervalStokesIso_hom_sourceImportedRectangleCount
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.intervalStokesIso source target).hom.sourceImportedRectangleCount =
      (TraceLocalizationInput.intervalStokes source target).sourceObject.importedRectangleCount :=
  TraceLocalizationInput.intervalStokesLocalizedIso_hom_sourceImportedRectangleCount
    source
    target

/-- Interval-Stokes unstable hom target rectangle count is the input target count. -/
theorem TraceUnstableAnalyticMotive.intervalStokesIso_hom_targetImportedRectangleCount
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.intervalStokesIso source target).hom.targetImportedRectangleCount =
      (TraceLocalizationInput.intervalStokes source target).targetObject.importedRectangleCount :=
  TraceLocalizationInput.intervalStokesLocalizedIso_hom_targetImportedRectangleCount
    source
    target

/-- Interval-Stokes unstable inverse source rectangle count is the input target count. -/
theorem TraceUnstableAnalyticMotive.intervalStokesIso_inv_sourceImportedRectangleCount
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.intervalStokesIso source target).inv.sourceImportedRectangleCount =
      (TraceLocalizationInput.intervalStokes source target).targetObject.importedRectangleCount :=
  TraceLocalizationInput.intervalStokesLocalizedIso_inv_sourceImportedRectangleCount
    source
    target

/-- Interval-Stokes unstable inverse target rectangle count is the input source count. -/
theorem TraceUnstableAnalyticMotive.intervalStokesIso_inv_targetImportedRectangleCount
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.intervalStokesIso source target).inv.targetImportedRectangleCount =
      (TraceLocalizationInput.intervalStokes source target).sourceObject.importedRectangleCount :=
  TraceLocalizationInput.intervalStokesLocalizedIso_inv_targetImportedRectangleCount
    source
    target

/-- Interval-Fubini unstable hom source rectangle count is the input source count. -/
theorem TraceUnstableAnalyticMotive.intervalFubiniIso_hom_sourceImportedRectangleCount
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.intervalFubiniIso source target).hom.sourceImportedRectangleCount =
      (TraceLocalizationInput.intervalFubini source target).sourceObject.importedRectangleCount :=
  TraceLocalizationInput.intervalFubiniLocalizedIso_hom_sourceImportedRectangleCount
    source
    target

/-- Interval-Fubini unstable hom target rectangle count is the input target count. -/
theorem TraceUnstableAnalyticMotive.intervalFubiniIso_hom_targetImportedRectangleCount
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.intervalFubiniIso source target).hom.targetImportedRectangleCount =
      (TraceLocalizationInput.intervalFubini source target).targetObject.importedRectangleCount :=
  TraceLocalizationInput.intervalFubiniLocalizedIso_hom_targetImportedRectangleCount
    source
    target

/-- Interval-Fubini unstable inverse source rectangle count is the input target count. -/
theorem TraceUnstableAnalyticMotive.intervalFubiniIso_inv_sourceImportedRectangleCount
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.intervalFubiniIso source target).inv.sourceImportedRectangleCount =
      (TraceLocalizationInput.intervalFubini source target).targetObject.importedRectangleCount :=
  TraceLocalizationInput.intervalFubiniLocalizedIso_inv_sourceImportedRectangleCount
    source
    target

/-- Interval-Fubini unstable inverse target rectangle count is the input source count. -/
theorem TraceUnstableAnalyticMotive.intervalFubiniIso_inv_targetImportedRectangleCount
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.intervalFubiniIso source target).inv.targetImportedRectangleCount =
      (TraceLocalizationInput.intervalFubini source target).sourceObject.importedRectangleCount :=
  TraceLocalizationInput.intervalFubiniLocalizedIso_inv_targetImportedRectangleCount
    source
    target

/-- Tate-weight-drop unstable hom source rectangle count is the input source count. -/
theorem TraceUnstableAnalyticMotive.tateWeightDropIso_hom_sourceImportedRectangleCount
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.tateWeightDropIso source target).hom.sourceImportedRectangleCount =
      (TraceLocalizationInput.tateWeightDrop source target).sourceObject.importedRectangleCount :=
  TraceLocalizationInput.tateWeightDropLocalizedIso_hom_sourceImportedRectangleCount
    source
    target

/-- Tate-weight-drop unstable hom target rectangle count is the input target count. -/
theorem TraceUnstableAnalyticMotive.tateWeightDropIso_hom_targetImportedRectangleCount
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.tateWeightDropIso source target).hom.targetImportedRectangleCount =
      (TraceLocalizationInput.tateWeightDrop source target).targetObject.importedRectangleCount :=
  TraceLocalizationInput.tateWeightDropLocalizedIso_hom_targetImportedRectangleCount
    source
    target

/-- Tate-weight-drop unstable inverse source rectangle count is the input target count. -/
theorem TraceUnstableAnalyticMotive.tateWeightDropIso_inv_sourceImportedRectangleCount
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.tateWeightDropIso source target).inv.sourceImportedRectangleCount =
      (TraceLocalizationInput.tateWeightDrop source target).targetObject.importedRectangleCount :=
  TraceLocalizationInput.tateWeightDropLocalizedIso_inv_sourceImportedRectangleCount
    source
    target

/-- Tate-weight-drop unstable inverse target rectangle count is the input source count. -/
theorem TraceUnstableAnalyticMotive.tateWeightDropIso_inv_targetImportedRectangleCount
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.tateWeightDropIso source target).inv.targetImportedRectangleCount =
      (TraceLocalizationInput.tateWeightDrop source target).sourceObject.importedRectangleCount :=
  TraceLocalizationInput.tateWeightDropLocalizedIso_inv_targetImportedRectangleCount
    source
    target

end AnalyticMotives
end LFunctions
end Boundary
