import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Unstable.Inputs.ByKind.Payload.ImportedRectangles.Counts.ArrowEndpoints.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Unstable.Inputs.ByKind.Payload.ImportedRectangles.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.LocalizationInput.WordQuotient.Category.Inputs.ByKind.Isomorphisms.Payload.ImportedRectangles.Counts.Owner

/-!
# By-kind unstable imported-rectangle counts

This file exposes endpoint imported finite-rectangle counts for the six named
unstable analytic-motive isomorphisms.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Descent-channel unstable hom endpoint count is source count plus target count. -/
theorem TraceUnstableAnalyticMotive.descentChannelIso_hom_endpointImportedRectangleCount
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.descentChannelIso
      source
      target).hom.endpointImportedRectangleCount =
      (TraceLocalizationInput.descentChannel source target).sourceObject.importedRectangleCount +
        (TraceLocalizationInput.descentChannel source target).targetObject.importedRectangleCount :=
  TraceLocalizationInput.descentChannelLocalizedIso_hom_endpointImportedRectangleCount
    source
    target

/-- Descent-channel unstable inverse endpoint count is target count plus source count. -/
theorem TraceUnstableAnalyticMotive.descentChannelIso_inv_endpointImportedRectangleCount
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.descentChannelIso
      source
      target).inv.endpointImportedRectangleCount =
      (TraceLocalizationInput.descentChannel source target).targetObject.importedRectangleCount +
        (TraceLocalizationInput.descentChannel source target).sourceObject.importedRectangleCount :=
  TraceLocalizationInput.descentChannelLocalizedIso_inv_endpointImportedRectangleCount
    source
    target

/-- Descent-refinement unstable hom endpoint count is source count plus target count. -/
theorem TraceUnstableAnalyticMotive.descentRefinementIso_hom_endpointImportedRectangleCount
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.descentRefinementIso
      source
      target).hom.endpointImportedRectangleCount =
      (TraceLocalizationInput.descentRefinement source target).sourceObject.importedRectangleCount +
        (TraceLocalizationInput.descentRefinement source target).targetObject.importedRectangleCount :=
  TraceLocalizationInput.descentRefinementLocalizedIso_hom_endpointImportedRectangleCount
    source
    target

/-- Descent-refinement unstable inverse endpoint count is target count plus source count. -/
theorem TraceUnstableAnalyticMotive.descentRefinementIso_inv_endpointImportedRectangleCount
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.descentRefinementIso
      source
      target).inv.endpointImportedRectangleCount =
      (TraceLocalizationInput.descentRefinement source target).targetObject.importedRectangleCount +
        (TraceLocalizationInput.descentRefinement source target).sourceObject.importedRectangleCount :=
  TraceLocalizationInput.descentRefinementLocalizedIso_inv_endpointImportedRectangleCount
    source
    target

/-- Descent-schedule unstable hom endpoint count is source count plus target count. -/
theorem TraceUnstableAnalyticMotive.descentScheduleIso_hom_endpointImportedRectangleCount
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.descentScheduleIso
      source
      target).hom.endpointImportedRectangleCount =
      (TraceLocalizationInput.descentSchedule source target).sourceObject.importedRectangleCount +
        (TraceLocalizationInput.descentSchedule source target).targetObject.importedRectangleCount :=
  TraceLocalizationInput.descentScheduleLocalizedIso_hom_endpointImportedRectangleCount
    source
    target

/-- Descent-schedule unstable inverse endpoint count is target count plus source count. -/
theorem TraceUnstableAnalyticMotive.descentScheduleIso_inv_endpointImportedRectangleCount
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.descentScheduleIso
      source
      target).inv.endpointImportedRectangleCount =
      (TraceLocalizationInput.descentSchedule source target).targetObject.importedRectangleCount +
        (TraceLocalizationInput.descentSchedule source target).sourceObject.importedRectangleCount :=
  TraceLocalizationInput.descentScheduleLocalizedIso_inv_endpointImportedRectangleCount
    source
    target

/-- Interval-Stokes unstable hom endpoint count is source count plus target count. -/
theorem TraceUnstableAnalyticMotive.intervalStokesIso_hom_endpointImportedRectangleCount
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.intervalStokesIso
      source
      target).hom.endpointImportedRectangleCount =
      (TraceLocalizationInput.intervalStokes source target).sourceObject.importedRectangleCount +
        (TraceLocalizationInput.intervalStokes source target).targetObject.importedRectangleCount :=
  TraceLocalizationInput.intervalStokesLocalizedIso_hom_endpointImportedRectangleCount
    source
    target

/-- Interval-Stokes unstable inverse endpoint count is target count plus source count. -/
theorem TraceUnstableAnalyticMotive.intervalStokesIso_inv_endpointImportedRectangleCount
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.intervalStokesIso
      source
      target).inv.endpointImportedRectangleCount =
      (TraceLocalizationInput.intervalStokes source target).targetObject.importedRectangleCount +
        (TraceLocalizationInput.intervalStokes source target).sourceObject.importedRectangleCount :=
  TraceLocalizationInput.intervalStokesLocalizedIso_inv_endpointImportedRectangleCount
    source
    target

/-- Interval-Fubini unstable hom endpoint count is source count plus target count. -/
theorem TraceUnstableAnalyticMotive.intervalFubiniIso_hom_endpointImportedRectangleCount
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.intervalFubiniIso
      source
      target).hom.endpointImportedRectangleCount =
      (TraceLocalizationInput.intervalFubini source target).sourceObject.importedRectangleCount +
        (TraceLocalizationInput.intervalFubini source target).targetObject.importedRectangleCount :=
  TraceLocalizationInput.intervalFubiniLocalizedIso_hom_endpointImportedRectangleCount
    source
    target

/-- Interval-Fubini unstable inverse endpoint count is target count plus source count. -/
theorem TraceUnstableAnalyticMotive.intervalFubiniIso_inv_endpointImportedRectangleCount
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.intervalFubiniIso
      source
      target).inv.endpointImportedRectangleCount =
      (TraceLocalizationInput.intervalFubini source target).targetObject.importedRectangleCount +
        (TraceLocalizationInput.intervalFubini source target).sourceObject.importedRectangleCount :=
  TraceLocalizationInput.intervalFubiniLocalizedIso_inv_endpointImportedRectangleCount
    source
    target

/-- Tate-weight-drop unstable hom endpoint count is source count plus target count. -/
theorem TraceUnstableAnalyticMotive.tateWeightDropIso_hom_endpointImportedRectangleCount
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.tateWeightDropIso
      source
      target).hom.endpointImportedRectangleCount =
      (TraceLocalizationInput.tateWeightDrop source target).sourceObject.importedRectangleCount +
        (TraceLocalizationInput.tateWeightDrop source target).targetObject.importedRectangleCount :=
  TraceLocalizationInput.tateWeightDropLocalizedIso_hom_endpointImportedRectangleCount
    source
    target

/-- Tate-weight-drop unstable inverse endpoint count is target count plus source count. -/
theorem TraceUnstableAnalyticMotive.tateWeightDropIso_inv_endpointImportedRectangleCount
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.tateWeightDropIso
      source
      target).inv.endpointImportedRectangleCount =
      (TraceLocalizationInput.tateWeightDrop source target).targetObject.importedRectangleCount +
        (TraceLocalizationInput.tateWeightDrop source target).sourceObject.importedRectangleCount :=
  TraceLocalizationInput.tateWeightDropLocalizedIso_inv_endpointImportedRectangleCount
    source
    target

end AnalyticMotives
end LFunctions
end Boundary
