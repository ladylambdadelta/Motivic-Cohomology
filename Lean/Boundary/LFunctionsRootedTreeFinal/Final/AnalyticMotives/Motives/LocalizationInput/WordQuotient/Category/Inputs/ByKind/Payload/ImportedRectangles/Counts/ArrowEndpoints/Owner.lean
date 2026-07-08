import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.LocalizationInput.WordQuotient.Category.Inputs.ByKind.Payload.ImportedRectangles.Owner

/-!
# Imported finite-rectangle counts for named input-arrow endpoints

This file gives by-kind names to the source and target imported finite-rectangle
counts carried by the forward and inverse arrows attached to localization
inputs.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Descent-channel forward source rectangle count is the input source count. -/
theorem TraceLocalizationInput.descentChannelForwardArrow_sourceImportedRectangleCount
    (source target : QTraceExpression) :
    (TraceLocalizationInput.descentChannelForwardArrow
      source
      target).sourceImportedRectangleCount =
      (TraceLocalizationInput.descentChannel source target).sourceObject.importedRectangleCount :=
  TraceLocalizationInput.localizedForwardArrow_sourceImportedRectangleCount
    (TraceLocalizationInput.descentChannel source target)

/-- Descent-refinement forward source rectangle count is the input source count. -/
theorem TraceLocalizationInput.descentRefinementForwardArrow_sourceImportedRectangleCount
    (source target : QTraceExpression) :
    (TraceLocalizationInput.descentRefinementForwardArrow
      source
      target).sourceImportedRectangleCount =
      (TraceLocalizationInput.descentRefinement source target).sourceObject.importedRectangleCount :=
  TraceLocalizationInput.localizedForwardArrow_sourceImportedRectangleCount
    (TraceLocalizationInput.descentRefinement source target)

/-- Descent-schedule forward source rectangle count is the input source count. -/
theorem TraceLocalizationInput.descentScheduleForwardArrow_sourceImportedRectangleCount
    (source target : QTraceExpression) :
    (TraceLocalizationInput.descentScheduleForwardArrow
      source
      target).sourceImportedRectangleCount =
      (TraceLocalizationInput.descentSchedule source target).sourceObject.importedRectangleCount :=
  TraceLocalizationInput.localizedForwardArrow_sourceImportedRectangleCount
    (TraceLocalizationInput.descentSchedule source target)

/-- Interval-Stokes forward source rectangle count is the input source count. -/
theorem TraceLocalizationInput.intervalStokesForwardArrow_sourceImportedRectangleCount
    (source target : QTraceExpression) :
    (TraceLocalizationInput.intervalStokesForwardArrow
      source
      target).sourceImportedRectangleCount =
      (TraceLocalizationInput.intervalStokes source target).sourceObject.importedRectangleCount :=
  TraceLocalizationInput.localizedForwardArrow_sourceImportedRectangleCount
    (TraceLocalizationInput.intervalStokes source target)

/-- Interval-Fubini forward source rectangle count is the input source count. -/
theorem TraceLocalizationInput.intervalFubiniForwardArrow_sourceImportedRectangleCount
    (source target : QTraceExpression) :
    (TraceLocalizationInput.intervalFubiniForwardArrow
      source
      target).sourceImportedRectangleCount =
      (TraceLocalizationInput.intervalFubini source target).sourceObject.importedRectangleCount :=
  TraceLocalizationInput.localizedForwardArrow_sourceImportedRectangleCount
    (TraceLocalizationInput.intervalFubini source target)

/-- Tate-weight-drop forward source rectangle count is the input source count. -/
theorem TraceLocalizationInput.tateWeightDropForwardArrow_sourceImportedRectangleCount
    (source target : QTraceExpression) :
    (TraceLocalizationInput.tateWeightDropForwardArrow
      source
      target).sourceImportedRectangleCount =
      (TraceLocalizationInput.tateWeightDrop source target).sourceObject.importedRectangleCount :=
  TraceLocalizationInput.localizedForwardArrow_sourceImportedRectangleCount
    (TraceLocalizationInput.tateWeightDrop source target)

/-- Descent-channel forward target rectangle count is the input target count. -/
theorem TraceLocalizationInput.descentChannelForwardArrow_targetImportedRectangleCount
    (source target : QTraceExpression) :
    (TraceLocalizationInput.descentChannelForwardArrow
      source
      target).targetImportedRectangleCount =
      (TraceLocalizationInput.descentChannel source target).targetObject.importedRectangleCount :=
  TraceLocalizationInput.localizedForwardArrow_targetImportedRectangleCount
    (TraceLocalizationInput.descentChannel source target)

/-- Descent-refinement forward target rectangle count is the input target count. -/
theorem TraceLocalizationInput.descentRefinementForwardArrow_targetImportedRectangleCount
    (source target : QTraceExpression) :
    (TraceLocalizationInput.descentRefinementForwardArrow
      source
      target).targetImportedRectangleCount =
      (TraceLocalizationInput.descentRefinement source target).targetObject.importedRectangleCount :=
  TraceLocalizationInput.localizedForwardArrow_targetImportedRectangleCount
    (TraceLocalizationInput.descentRefinement source target)

/-- Descent-schedule forward target rectangle count is the input target count. -/
theorem TraceLocalizationInput.descentScheduleForwardArrow_targetImportedRectangleCount
    (source target : QTraceExpression) :
    (TraceLocalizationInput.descentScheduleForwardArrow
      source
      target).targetImportedRectangleCount =
      (TraceLocalizationInput.descentSchedule source target).targetObject.importedRectangleCount :=
  TraceLocalizationInput.localizedForwardArrow_targetImportedRectangleCount
    (TraceLocalizationInput.descentSchedule source target)

/-- Interval-Stokes forward target rectangle count is the input target count. -/
theorem TraceLocalizationInput.intervalStokesForwardArrow_targetImportedRectangleCount
    (source target : QTraceExpression) :
    (TraceLocalizationInput.intervalStokesForwardArrow
      source
      target).targetImportedRectangleCount =
      (TraceLocalizationInput.intervalStokes source target).targetObject.importedRectangleCount :=
  TraceLocalizationInput.localizedForwardArrow_targetImportedRectangleCount
    (TraceLocalizationInput.intervalStokes source target)

/-- Interval-Fubini forward target rectangle count is the input target count. -/
theorem TraceLocalizationInput.intervalFubiniForwardArrow_targetImportedRectangleCount
    (source target : QTraceExpression) :
    (TraceLocalizationInput.intervalFubiniForwardArrow
      source
      target).targetImportedRectangleCount =
      (TraceLocalizationInput.intervalFubini source target).targetObject.importedRectangleCount :=
  TraceLocalizationInput.localizedForwardArrow_targetImportedRectangleCount
    (TraceLocalizationInput.intervalFubini source target)

/-- Tate-weight-drop forward target rectangle count is the input target count. -/
theorem TraceLocalizationInput.tateWeightDropForwardArrow_targetImportedRectangleCount
    (source target : QTraceExpression) :
    (TraceLocalizationInput.tateWeightDropForwardArrow
      source
      target).targetImportedRectangleCount =
      (TraceLocalizationInput.tateWeightDrop source target).targetObject.importedRectangleCount :=
  TraceLocalizationInput.localizedForwardArrow_targetImportedRectangleCount
    (TraceLocalizationInput.tateWeightDrop source target)

/-- Descent-channel inverse source rectangle count is the input target count. -/
theorem TraceLocalizationInput.descentChannelInverseArrow_sourceImportedRectangleCount
    (source target : QTraceExpression) :
    (TraceLocalizationInput.descentChannelInverseArrow
      source
      target).sourceImportedRectangleCount =
      (TraceLocalizationInput.descentChannel source target).targetObject.importedRectangleCount :=
  TraceLocalizationInput.localizedInverseArrow_sourceImportedRectangleCount
    (TraceLocalizationInput.descentChannel source target)

/-- Descent-refinement inverse source rectangle count is the input target count. -/
theorem TraceLocalizationInput.descentRefinementInverseArrow_sourceImportedRectangleCount
    (source target : QTraceExpression) :
    (TraceLocalizationInput.descentRefinementInverseArrow
      source
      target).sourceImportedRectangleCount =
      (TraceLocalizationInput.descentRefinement source target).targetObject.importedRectangleCount :=
  TraceLocalizationInput.localizedInverseArrow_sourceImportedRectangleCount
    (TraceLocalizationInput.descentRefinement source target)

/-- Descent-schedule inverse source rectangle count is the input target count. -/
theorem TraceLocalizationInput.descentScheduleInverseArrow_sourceImportedRectangleCount
    (source target : QTraceExpression) :
    (TraceLocalizationInput.descentScheduleInverseArrow
      source
      target).sourceImportedRectangleCount =
      (TraceLocalizationInput.descentSchedule source target).targetObject.importedRectangleCount :=
  TraceLocalizationInput.localizedInverseArrow_sourceImportedRectangleCount
    (TraceLocalizationInput.descentSchedule source target)

/-- Interval-Stokes inverse source rectangle count is the input target count. -/
theorem TraceLocalizationInput.intervalStokesInverseArrow_sourceImportedRectangleCount
    (source target : QTraceExpression) :
    (TraceLocalizationInput.intervalStokesInverseArrow
      source
      target).sourceImportedRectangleCount =
      (TraceLocalizationInput.intervalStokes source target).targetObject.importedRectangleCount :=
  TraceLocalizationInput.localizedInverseArrow_sourceImportedRectangleCount
    (TraceLocalizationInput.intervalStokes source target)

/-- Interval-Fubini inverse source rectangle count is the input target count. -/
theorem TraceLocalizationInput.intervalFubiniInverseArrow_sourceImportedRectangleCount
    (source target : QTraceExpression) :
    (TraceLocalizationInput.intervalFubiniInverseArrow
      source
      target).sourceImportedRectangleCount =
      (TraceLocalizationInput.intervalFubini source target).targetObject.importedRectangleCount :=
  TraceLocalizationInput.localizedInverseArrow_sourceImportedRectangleCount
    (TraceLocalizationInput.intervalFubini source target)

/-- Tate-weight-drop inverse source rectangle count is the input target count. -/
theorem TraceLocalizationInput.tateWeightDropInverseArrow_sourceImportedRectangleCount
    (source target : QTraceExpression) :
    (TraceLocalizationInput.tateWeightDropInverseArrow
      source
      target).sourceImportedRectangleCount =
      (TraceLocalizationInput.tateWeightDrop source target).targetObject.importedRectangleCount :=
  TraceLocalizationInput.localizedInverseArrow_sourceImportedRectangleCount
    (TraceLocalizationInput.tateWeightDrop source target)

/-- Descent-channel inverse target rectangle count is the input source count. -/
theorem TraceLocalizationInput.descentChannelInverseArrow_targetImportedRectangleCount
    (source target : QTraceExpression) :
    (TraceLocalizationInput.descentChannelInverseArrow
      source
      target).targetImportedRectangleCount =
      (TraceLocalizationInput.descentChannel source target).sourceObject.importedRectangleCount :=
  TraceLocalizationInput.localizedInverseArrow_targetImportedRectangleCount
    (TraceLocalizationInput.descentChannel source target)

/-- Descent-refinement inverse target rectangle count is the input source count. -/
theorem TraceLocalizationInput.descentRefinementInverseArrow_targetImportedRectangleCount
    (source target : QTraceExpression) :
    (TraceLocalizationInput.descentRefinementInverseArrow
      source
      target).targetImportedRectangleCount =
      (TraceLocalizationInput.descentRefinement source target).sourceObject.importedRectangleCount :=
  TraceLocalizationInput.localizedInverseArrow_targetImportedRectangleCount
    (TraceLocalizationInput.descentRefinement source target)

/-- Descent-schedule inverse target rectangle count is the input source count. -/
theorem TraceLocalizationInput.descentScheduleInverseArrow_targetImportedRectangleCount
    (source target : QTraceExpression) :
    (TraceLocalizationInput.descentScheduleInverseArrow
      source
      target).targetImportedRectangleCount =
      (TraceLocalizationInput.descentSchedule source target).sourceObject.importedRectangleCount :=
  TraceLocalizationInput.localizedInverseArrow_targetImportedRectangleCount
    (TraceLocalizationInput.descentSchedule source target)

/-- Interval-Stokes inverse target rectangle count is the input source count. -/
theorem TraceLocalizationInput.intervalStokesInverseArrow_targetImportedRectangleCount
    (source target : QTraceExpression) :
    (TraceLocalizationInput.intervalStokesInverseArrow
      source
      target).targetImportedRectangleCount =
      (TraceLocalizationInput.intervalStokes source target).sourceObject.importedRectangleCount :=
  TraceLocalizationInput.localizedInverseArrow_targetImportedRectangleCount
    (TraceLocalizationInput.intervalStokes source target)

/-- Interval-Fubini inverse target rectangle count is the input source count. -/
theorem TraceLocalizationInput.intervalFubiniInverseArrow_targetImportedRectangleCount
    (source target : QTraceExpression) :
    (TraceLocalizationInput.intervalFubiniInverseArrow
      source
      target).targetImportedRectangleCount =
      (TraceLocalizationInput.intervalFubini source target).sourceObject.importedRectangleCount :=
  TraceLocalizationInput.localizedInverseArrow_targetImportedRectangleCount
    (TraceLocalizationInput.intervalFubini source target)

/-- Tate-weight-drop inverse target rectangle count is the input source count. -/
theorem TraceLocalizationInput.tateWeightDropInverseArrow_targetImportedRectangleCount
    (source target : QTraceExpression) :
    (TraceLocalizationInput.tateWeightDropInverseArrow
      source
      target).targetImportedRectangleCount =
      (TraceLocalizationInput.tateWeightDrop source target).sourceObject.importedRectangleCount :=
  TraceLocalizationInput.localizedInverseArrow_targetImportedRectangleCount
    (TraceLocalizationInput.tateWeightDrop source target)

end AnalyticMotives
end LFunctions
end Boundary
