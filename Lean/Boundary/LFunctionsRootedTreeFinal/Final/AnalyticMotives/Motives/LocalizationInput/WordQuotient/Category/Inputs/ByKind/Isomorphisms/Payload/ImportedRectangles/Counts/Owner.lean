import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.LocalizationInput.WordQuotient.Category.Inputs.ByKind.Isomorphisms.Payload.ImportedRectangles.Counts.ArrowEndpoints.Owner

/-!
# Imported finite-rectangle counts for named localized isomorphisms

This file exposes concatenated endpoint imported-rectangle counts through the
hom and inverse arrows of the named by-kind localized isomorphisms.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Descent-channel isomorphism hom endpoint imported count is source count plus target count. -/
theorem TraceLocalizationInput.descentChannelLocalizedIso_hom_endpointImportedRectangleCount
    (source target : QTraceExpression) :
    (TraceLocalizationInput.descentChannelLocalizedIso
      source
      target).hom.endpointImportedRectangleCount =
      (TraceLocalizationInput.descentChannel source target).sourceObject.importedRectangleCount +
        (TraceLocalizationInput.descentChannel source target).targetObject.importedRectangleCount :=
  TraceLocalizationInput.descentChannelForwardArrow_endpointImportedRectangleCount
    source
    target

/-- Descent-channel isomorphism inverse endpoint imported count is target count plus source count. -/
theorem TraceLocalizationInput.descentChannelLocalizedIso_inv_endpointImportedRectangleCount
    (source target : QTraceExpression) :
    (TraceLocalizationInput.descentChannelLocalizedIso
      source
      target).inv.endpointImportedRectangleCount =
      (TraceLocalizationInput.descentChannel source target).targetObject.importedRectangleCount +
        (TraceLocalizationInput.descentChannel source target).sourceObject.importedRectangleCount :=
  TraceLocalizationInput.descentChannelInverseArrow_endpointImportedRectangleCount
    source
    target

/-- Descent-refinement isomorphism hom endpoint imported count is source count plus target count. -/
theorem TraceLocalizationInput.descentRefinementLocalizedIso_hom_endpointImportedRectangleCount
    (source target : QTraceExpression) :
    (TraceLocalizationInput.descentRefinementLocalizedIso
      source
      target).hom.endpointImportedRectangleCount =
      (TraceLocalizationInput.descentRefinement source target).sourceObject.importedRectangleCount +
        (TraceLocalizationInput.descentRefinement source target).targetObject.importedRectangleCount :=
  TraceLocalizationInput.descentRefinementForwardArrow_endpointImportedRectangleCount
    source
    target

/-- Descent-refinement isomorphism inverse endpoint imported count is target count plus source count. -/
theorem TraceLocalizationInput.descentRefinementLocalizedIso_inv_endpointImportedRectangleCount
    (source target : QTraceExpression) :
    (TraceLocalizationInput.descentRefinementLocalizedIso
      source
      target).inv.endpointImportedRectangleCount =
      (TraceLocalizationInput.descentRefinement source target).targetObject.importedRectangleCount +
        (TraceLocalizationInput.descentRefinement source target).sourceObject.importedRectangleCount :=
  TraceLocalizationInput.descentRefinementInverseArrow_endpointImportedRectangleCount
    source
    target

/-- Descent-schedule isomorphism hom endpoint imported count is source count plus target count. -/
theorem TraceLocalizationInput.descentScheduleLocalizedIso_hom_endpointImportedRectangleCount
    (source target : QTraceExpression) :
    (TraceLocalizationInput.descentScheduleLocalizedIso
      source
      target).hom.endpointImportedRectangleCount =
      (TraceLocalizationInput.descentSchedule source target).sourceObject.importedRectangleCount +
        (TraceLocalizationInput.descentSchedule source target).targetObject.importedRectangleCount :=
  TraceLocalizationInput.descentScheduleForwardArrow_endpointImportedRectangleCount
    source
    target

/-- Descent-schedule isomorphism inverse endpoint imported count is target count plus source count. -/
theorem TraceLocalizationInput.descentScheduleLocalizedIso_inv_endpointImportedRectangleCount
    (source target : QTraceExpression) :
    (TraceLocalizationInput.descentScheduleLocalizedIso
      source
      target).inv.endpointImportedRectangleCount =
      (TraceLocalizationInput.descentSchedule source target).targetObject.importedRectangleCount +
        (TraceLocalizationInput.descentSchedule source target).sourceObject.importedRectangleCount :=
  TraceLocalizationInput.descentScheduleInverseArrow_endpointImportedRectangleCount
    source
    target

/-- Interval-Stokes isomorphism hom endpoint imported count is source count plus target count. -/
theorem TraceLocalizationInput.intervalStokesLocalizedIso_hom_endpointImportedRectangleCount
    (source target : QTraceExpression) :
    (TraceLocalizationInput.intervalStokesLocalizedIso
      source
      target).hom.endpointImportedRectangleCount =
      (TraceLocalizationInput.intervalStokes source target).sourceObject.importedRectangleCount +
        (TraceLocalizationInput.intervalStokes source target).targetObject.importedRectangleCount :=
  TraceLocalizationInput.intervalStokesForwardArrow_endpointImportedRectangleCount
    source
    target

/-- Interval-Stokes isomorphism inverse endpoint imported count is target count plus source count. -/
theorem TraceLocalizationInput.intervalStokesLocalizedIso_inv_endpointImportedRectangleCount
    (source target : QTraceExpression) :
    (TraceLocalizationInput.intervalStokesLocalizedIso
      source
      target).inv.endpointImportedRectangleCount =
      (TraceLocalizationInput.intervalStokes source target).targetObject.importedRectangleCount +
        (TraceLocalizationInput.intervalStokes source target).sourceObject.importedRectangleCount :=
  TraceLocalizationInput.intervalStokesInverseArrow_endpointImportedRectangleCount
    source
    target

/-- Interval-Fubini isomorphism hom endpoint imported count is source count plus target count. -/
theorem TraceLocalizationInput.intervalFubiniLocalizedIso_hom_endpointImportedRectangleCount
    (source target : QTraceExpression) :
    (TraceLocalizationInput.intervalFubiniLocalizedIso
      source
      target).hom.endpointImportedRectangleCount =
      (TraceLocalizationInput.intervalFubini source target).sourceObject.importedRectangleCount +
        (TraceLocalizationInput.intervalFubini source target).targetObject.importedRectangleCount :=
  TraceLocalizationInput.intervalFubiniForwardArrow_endpointImportedRectangleCount
    source
    target

/-- Interval-Fubini isomorphism inverse endpoint imported count is target count plus source count. -/
theorem TraceLocalizationInput.intervalFubiniLocalizedIso_inv_endpointImportedRectangleCount
    (source target : QTraceExpression) :
    (TraceLocalizationInput.intervalFubiniLocalizedIso
      source
      target).inv.endpointImportedRectangleCount =
      (TraceLocalizationInput.intervalFubini source target).targetObject.importedRectangleCount +
        (TraceLocalizationInput.intervalFubini source target).sourceObject.importedRectangleCount :=
  TraceLocalizationInput.intervalFubiniInverseArrow_endpointImportedRectangleCount
    source
    target

/-- Tate-weight-drop isomorphism hom endpoint imported count is source count plus target count. -/
theorem TraceLocalizationInput.tateWeightDropLocalizedIso_hom_endpointImportedRectangleCount
    (source target : QTraceExpression) :
    (TraceLocalizationInput.tateWeightDropLocalizedIso
      source
      target).hom.endpointImportedRectangleCount =
      (TraceLocalizationInput.tateWeightDrop source target).sourceObject.importedRectangleCount +
        (TraceLocalizationInput.tateWeightDrop source target).targetObject.importedRectangleCount :=
  TraceLocalizationInput.tateWeightDropForwardArrow_endpointImportedRectangleCount
    source
    target

/-- Tate-weight-drop isomorphism inverse endpoint imported count is target count plus source count. -/
theorem TraceLocalizationInput.tateWeightDropLocalizedIso_inv_endpointImportedRectangleCount
    (source target : QTraceExpression) :
    (TraceLocalizationInput.tateWeightDropLocalizedIso
      source
      target).inv.endpointImportedRectangleCount =
      (TraceLocalizationInput.tateWeightDrop source target).targetObject.importedRectangleCount +
        (TraceLocalizationInput.tateWeightDrop source target).sourceObject.importedRectangleCount :=
  TraceLocalizationInput.tateWeightDropInverseArrow_endpointImportedRectangleCount
    source
    target

end AnalyticMotives
end LFunctions
end Boundary
