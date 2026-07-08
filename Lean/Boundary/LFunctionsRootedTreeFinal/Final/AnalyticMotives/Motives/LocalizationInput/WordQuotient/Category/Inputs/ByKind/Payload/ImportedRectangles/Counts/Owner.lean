import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.LocalizationInput.WordQuotient.Category.Inputs.ByKind.Payload.ImportedRectangles.Counts.ArrowEndpoints.Owner

/-!
# Endpoint imported finite-rectangle counts for named input arrows by kind

This file gives by-kind names to the imported finite-rectangle endpoint counts
carried by the forward and inverse arrows attached to localization inputs.
Source and target endpoint counts live in the `ArrowEndpoints` child.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Descent-channel forward endpoint imported count is source count plus target count. -/
theorem TraceLocalizationInput.descentChannelForwardArrow_endpointImportedRectangleCount
    (source target : QTraceExpression) :
    (TraceLocalizationInput.descentChannelForwardArrow
      source
      target).endpointImportedRectangleCount =
      (TraceLocalizationInput.descentChannel source target).sourceObject.importedRectangleCount +
        (TraceLocalizationInput.descentChannel source target).targetObject.importedRectangleCount :=
  TraceLocalizationInput.localizedForwardArrow_endpointImportedRectangleCount
    (TraceLocalizationInput.descentChannel source target)

/-- Descent-refinement forward endpoint imported count is source count plus target count. -/
theorem TraceLocalizationInput.descentRefinementForwardArrow_endpointImportedRectangleCount
    (source target : QTraceExpression) :
    (TraceLocalizationInput.descentRefinementForwardArrow
      source
      target).endpointImportedRectangleCount =
      (TraceLocalizationInput.descentRefinement source target).sourceObject.importedRectangleCount +
        (TraceLocalizationInput.descentRefinement source target).targetObject.importedRectangleCount :=
  TraceLocalizationInput.localizedForwardArrow_endpointImportedRectangleCount
    (TraceLocalizationInput.descentRefinement source target)

/-- Descent-schedule forward endpoint imported count is source count plus target count. -/
theorem TraceLocalizationInput.descentScheduleForwardArrow_endpointImportedRectangleCount
    (source target : QTraceExpression) :
    (TraceLocalizationInput.descentScheduleForwardArrow
      source
      target).endpointImportedRectangleCount =
      (TraceLocalizationInput.descentSchedule source target).sourceObject.importedRectangleCount +
        (TraceLocalizationInput.descentSchedule source target).targetObject.importedRectangleCount :=
  TraceLocalizationInput.localizedForwardArrow_endpointImportedRectangleCount
    (TraceLocalizationInput.descentSchedule source target)

/-- Interval-Stokes forward endpoint imported count is source count plus target count. -/
theorem TraceLocalizationInput.intervalStokesForwardArrow_endpointImportedRectangleCount
    (source target : QTraceExpression) :
    (TraceLocalizationInput.intervalStokesForwardArrow
      source
      target).endpointImportedRectangleCount =
      (TraceLocalizationInput.intervalStokes source target).sourceObject.importedRectangleCount +
        (TraceLocalizationInput.intervalStokes source target).targetObject.importedRectangleCount :=
  TraceLocalizationInput.localizedForwardArrow_endpointImportedRectangleCount
    (TraceLocalizationInput.intervalStokes source target)

/-- Interval-Fubini forward endpoint imported count is source count plus target count. -/
theorem TraceLocalizationInput.intervalFubiniForwardArrow_endpointImportedRectangleCount
    (source target : QTraceExpression) :
    (TraceLocalizationInput.intervalFubiniForwardArrow
      source
      target).endpointImportedRectangleCount =
      (TraceLocalizationInput.intervalFubini source target).sourceObject.importedRectangleCount +
        (TraceLocalizationInput.intervalFubini source target).targetObject.importedRectangleCount :=
  TraceLocalizationInput.localizedForwardArrow_endpointImportedRectangleCount
    (TraceLocalizationInput.intervalFubini source target)

/-- Tate-weight-drop forward endpoint imported count is source count plus target count. -/
theorem TraceLocalizationInput.tateWeightDropForwardArrow_endpointImportedRectangleCount
    (source target : QTraceExpression) :
    (TraceLocalizationInput.tateWeightDropForwardArrow
      source
      target).endpointImportedRectangleCount =
      (TraceLocalizationInput.tateWeightDrop source target).sourceObject.importedRectangleCount +
        (TraceLocalizationInput.tateWeightDrop source target).targetObject.importedRectangleCount :=
  TraceLocalizationInput.localizedForwardArrow_endpointImportedRectangleCount
    (TraceLocalizationInput.tateWeightDrop source target)

/-- Descent-channel inverse endpoint imported count is target count plus source count. -/
theorem TraceLocalizationInput.descentChannelInverseArrow_endpointImportedRectangleCount
    (source target : QTraceExpression) :
    (TraceLocalizationInput.descentChannelInverseArrow
      source
      target).endpointImportedRectangleCount =
      (TraceLocalizationInput.descentChannel source target).targetObject.importedRectangleCount +
        (TraceLocalizationInput.descentChannel source target).sourceObject.importedRectangleCount :=
  TraceLocalizationInput.localizedInverseArrow_endpointImportedRectangleCount
    (TraceLocalizationInput.descentChannel source target)

/-- Descent-refinement inverse endpoint imported count is target count plus source count. -/
theorem TraceLocalizationInput.descentRefinementInverseArrow_endpointImportedRectangleCount
    (source target : QTraceExpression) :
    (TraceLocalizationInput.descentRefinementInverseArrow
      source
      target).endpointImportedRectangleCount =
      (TraceLocalizationInput.descentRefinement source target).targetObject.importedRectangleCount +
        (TraceLocalizationInput.descentRefinement source target).sourceObject.importedRectangleCount :=
  TraceLocalizationInput.localizedInverseArrow_endpointImportedRectangleCount
    (TraceLocalizationInput.descentRefinement source target)

/-- Descent-schedule inverse endpoint imported count is target count plus source count. -/
theorem TraceLocalizationInput.descentScheduleInverseArrow_endpointImportedRectangleCount
    (source target : QTraceExpression) :
    (TraceLocalizationInput.descentScheduleInverseArrow
      source
      target).endpointImportedRectangleCount =
      (TraceLocalizationInput.descentSchedule source target).targetObject.importedRectangleCount +
        (TraceLocalizationInput.descentSchedule source target).sourceObject.importedRectangleCount :=
  TraceLocalizationInput.localizedInverseArrow_endpointImportedRectangleCount
    (TraceLocalizationInput.descentSchedule source target)

/-- Interval-Stokes inverse endpoint imported count is target count plus source count. -/
theorem TraceLocalizationInput.intervalStokesInverseArrow_endpointImportedRectangleCount
    (source target : QTraceExpression) :
    (TraceLocalizationInput.intervalStokesInverseArrow
      source
      target).endpointImportedRectangleCount =
      (TraceLocalizationInput.intervalStokes source target).targetObject.importedRectangleCount +
        (TraceLocalizationInput.intervalStokes source target).sourceObject.importedRectangleCount :=
  TraceLocalizationInput.localizedInverseArrow_endpointImportedRectangleCount
    (TraceLocalizationInput.intervalStokes source target)

/-- Interval-Fubini inverse endpoint imported count is target count plus source count. -/
theorem TraceLocalizationInput.intervalFubiniInverseArrow_endpointImportedRectangleCount
    (source target : QTraceExpression) :
    (TraceLocalizationInput.intervalFubiniInverseArrow
      source
      target).endpointImportedRectangleCount =
      (TraceLocalizationInput.intervalFubini source target).targetObject.importedRectangleCount +
        (TraceLocalizationInput.intervalFubini source target).sourceObject.importedRectangleCount :=
  TraceLocalizationInput.localizedInverseArrow_endpointImportedRectangleCount
    (TraceLocalizationInput.intervalFubini source target)

/-- Tate-weight-drop inverse endpoint imported count is target count plus source count. -/
theorem TraceLocalizationInput.tateWeightDropInverseArrow_endpointImportedRectangleCount
    (source target : QTraceExpression) :
    (TraceLocalizationInput.tateWeightDropInverseArrow
      source
      target).endpointImportedRectangleCount =
      (TraceLocalizationInput.tateWeightDrop source target).targetObject.importedRectangleCount +
        (TraceLocalizationInput.tateWeightDrop source target).sourceObject.importedRectangleCount :=
  TraceLocalizationInput.localizedInverseArrow_endpointImportedRectangleCount
    (TraceLocalizationInput.tateWeightDrop source target)

end AnalyticMotives
end LFunctions
end Boundary
