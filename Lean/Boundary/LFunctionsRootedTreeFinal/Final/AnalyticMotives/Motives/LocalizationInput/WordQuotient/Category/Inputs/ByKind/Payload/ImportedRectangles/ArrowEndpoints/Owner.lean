import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.LocalizationInput.WordQuotient.Category.Inputs.ByKind.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.LocalizationInput.WordQuotient.Category.Inputs.Payload.ImportedRectangles.Owner

/-!
# Imported finite rectangles for named input-arrow endpoints

This file gives by-kind names to the source and target imported finite-rectangle
payload carried by the forward and inverse arrows attached to localization
inputs.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Descent-channel forward source rectangles are the input source rectangles. -/
theorem TraceLocalizationInput.descentChannelForwardArrow_sourceImportedRectangles
    (source target : QTraceExpression) :
    (TraceLocalizationInput.descentChannelForwardArrow
      source
      target).sourceImportedRectangles =
      (TraceLocalizationInput.descentChannel source target).sourceObject.importedRectangles :=
  TraceLocalizationInput.localizedForwardArrow_sourceImportedRectangles
    (TraceLocalizationInput.descentChannel source target)

/-- Descent-refinement forward source rectangles are the input source rectangles. -/
theorem TraceLocalizationInput.descentRefinementForwardArrow_sourceImportedRectangles
    (source target : QTraceExpression) :
    (TraceLocalizationInput.descentRefinementForwardArrow
      source
      target).sourceImportedRectangles =
      (TraceLocalizationInput.descentRefinement source target).sourceObject.importedRectangles :=
  TraceLocalizationInput.localizedForwardArrow_sourceImportedRectangles
    (TraceLocalizationInput.descentRefinement source target)

/-- Descent-schedule forward source rectangles are the input source rectangles. -/
theorem TraceLocalizationInput.descentScheduleForwardArrow_sourceImportedRectangles
    (source target : QTraceExpression) :
    (TraceLocalizationInput.descentScheduleForwardArrow
      source
      target).sourceImportedRectangles =
      (TraceLocalizationInput.descentSchedule source target).sourceObject.importedRectangles :=
  TraceLocalizationInput.localizedForwardArrow_sourceImportedRectangles
    (TraceLocalizationInput.descentSchedule source target)

/-- Interval-Stokes forward source rectangles are the input source rectangles. -/
theorem TraceLocalizationInput.intervalStokesForwardArrow_sourceImportedRectangles
    (source target : QTraceExpression) :
    (TraceLocalizationInput.intervalStokesForwardArrow
      source
      target).sourceImportedRectangles =
      (TraceLocalizationInput.intervalStokes source target).sourceObject.importedRectangles :=
  TraceLocalizationInput.localizedForwardArrow_sourceImportedRectangles
    (TraceLocalizationInput.intervalStokes source target)

/-- Interval-Fubini forward source rectangles are the input source rectangles. -/
theorem TraceLocalizationInput.intervalFubiniForwardArrow_sourceImportedRectangles
    (source target : QTraceExpression) :
    (TraceLocalizationInput.intervalFubiniForwardArrow
      source
      target).sourceImportedRectangles =
      (TraceLocalizationInput.intervalFubini source target).sourceObject.importedRectangles :=
  TraceLocalizationInput.localizedForwardArrow_sourceImportedRectangles
    (TraceLocalizationInput.intervalFubini source target)

/-- Tate-weight-drop forward source rectangles are the input source rectangles. -/
theorem TraceLocalizationInput.tateWeightDropForwardArrow_sourceImportedRectangles
    (source target : QTraceExpression) :
    (TraceLocalizationInput.tateWeightDropForwardArrow
      source
      target).sourceImportedRectangles =
      (TraceLocalizationInput.tateWeightDrop source target).sourceObject.importedRectangles :=
  TraceLocalizationInput.localizedForwardArrow_sourceImportedRectangles
    (TraceLocalizationInput.tateWeightDrop source target)

/-- Descent-channel forward target rectangles are the input target rectangles. -/
theorem TraceLocalizationInput.descentChannelForwardArrow_targetImportedRectangles
    (source target : QTraceExpression) :
    (TraceLocalizationInput.descentChannelForwardArrow
      source
      target).targetImportedRectangles =
      (TraceLocalizationInput.descentChannel source target).targetObject.importedRectangles :=
  TraceLocalizationInput.localizedForwardArrow_targetImportedRectangles
    (TraceLocalizationInput.descentChannel source target)

/-- Descent-refinement forward target rectangles are the input target rectangles. -/
theorem TraceLocalizationInput.descentRefinementForwardArrow_targetImportedRectangles
    (source target : QTraceExpression) :
    (TraceLocalizationInput.descentRefinementForwardArrow
      source
      target).targetImportedRectangles =
      (TraceLocalizationInput.descentRefinement source target).targetObject.importedRectangles :=
  TraceLocalizationInput.localizedForwardArrow_targetImportedRectangles
    (TraceLocalizationInput.descentRefinement source target)

/-- Descent-schedule forward target rectangles are the input target rectangles. -/
theorem TraceLocalizationInput.descentScheduleForwardArrow_targetImportedRectangles
    (source target : QTraceExpression) :
    (TraceLocalizationInput.descentScheduleForwardArrow
      source
      target).targetImportedRectangles =
      (TraceLocalizationInput.descentSchedule source target).targetObject.importedRectangles :=
  TraceLocalizationInput.localizedForwardArrow_targetImportedRectangles
    (TraceLocalizationInput.descentSchedule source target)

/-- Interval-Stokes forward target rectangles are the input target rectangles. -/
theorem TraceLocalizationInput.intervalStokesForwardArrow_targetImportedRectangles
    (source target : QTraceExpression) :
    (TraceLocalizationInput.intervalStokesForwardArrow
      source
      target).targetImportedRectangles =
      (TraceLocalizationInput.intervalStokes source target).targetObject.importedRectangles :=
  TraceLocalizationInput.localizedForwardArrow_targetImportedRectangles
    (TraceLocalizationInput.intervalStokes source target)

/-- Interval-Fubini forward target rectangles are the input target rectangles. -/
theorem TraceLocalizationInput.intervalFubiniForwardArrow_targetImportedRectangles
    (source target : QTraceExpression) :
    (TraceLocalizationInput.intervalFubiniForwardArrow
      source
      target).targetImportedRectangles =
      (TraceLocalizationInput.intervalFubini source target).targetObject.importedRectangles :=
  TraceLocalizationInput.localizedForwardArrow_targetImportedRectangles
    (TraceLocalizationInput.intervalFubini source target)

/-- Tate-weight-drop forward target rectangles are the input target rectangles. -/
theorem TraceLocalizationInput.tateWeightDropForwardArrow_targetImportedRectangles
    (source target : QTraceExpression) :
    (TraceLocalizationInput.tateWeightDropForwardArrow
      source
      target).targetImportedRectangles =
      (TraceLocalizationInput.tateWeightDrop source target).targetObject.importedRectangles :=
  TraceLocalizationInput.localizedForwardArrow_targetImportedRectangles
    (TraceLocalizationInput.tateWeightDrop source target)

/-- Descent-channel inverse source rectangles are the input target rectangles. -/
theorem TraceLocalizationInput.descentChannelInverseArrow_sourceImportedRectangles
    (source target : QTraceExpression) :
    (TraceLocalizationInput.descentChannelInverseArrow
      source
      target).sourceImportedRectangles =
      (TraceLocalizationInput.descentChannel source target).targetObject.importedRectangles :=
  TraceLocalizationInput.localizedInverseArrow_sourceImportedRectangles
    (TraceLocalizationInput.descentChannel source target)

/-- Descent-refinement inverse source rectangles are the input target rectangles. -/
theorem TraceLocalizationInput.descentRefinementInverseArrow_sourceImportedRectangles
    (source target : QTraceExpression) :
    (TraceLocalizationInput.descentRefinementInverseArrow
      source
      target).sourceImportedRectangles =
      (TraceLocalizationInput.descentRefinement source target).targetObject.importedRectangles :=
  TraceLocalizationInput.localizedInverseArrow_sourceImportedRectangles
    (TraceLocalizationInput.descentRefinement source target)

/-- Descent-schedule inverse source rectangles are the input target rectangles. -/
theorem TraceLocalizationInput.descentScheduleInverseArrow_sourceImportedRectangles
    (source target : QTraceExpression) :
    (TraceLocalizationInput.descentScheduleInverseArrow
      source
      target).sourceImportedRectangles =
      (TraceLocalizationInput.descentSchedule source target).targetObject.importedRectangles :=
  TraceLocalizationInput.localizedInverseArrow_sourceImportedRectangles
    (TraceLocalizationInput.descentSchedule source target)

/-- Interval-Stokes inverse source rectangles are the input target rectangles. -/
theorem TraceLocalizationInput.intervalStokesInverseArrow_sourceImportedRectangles
    (source target : QTraceExpression) :
    (TraceLocalizationInput.intervalStokesInverseArrow
      source
      target).sourceImportedRectangles =
      (TraceLocalizationInput.intervalStokes source target).targetObject.importedRectangles :=
  TraceLocalizationInput.localizedInverseArrow_sourceImportedRectangles
    (TraceLocalizationInput.intervalStokes source target)

/-- Interval-Fubini inverse source rectangles are the input target rectangles. -/
theorem TraceLocalizationInput.intervalFubiniInverseArrow_sourceImportedRectangles
    (source target : QTraceExpression) :
    (TraceLocalizationInput.intervalFubiniInverseArrow
      source
      target).sourceImportedRectangles =
      (TraceLocalizationInput.intervalFubini source target).targetObject.importedRectangles :=
  TraceLocalizationInput.localizedInverseArrow_sourceImportedRectangles
    (TraceLocalizationInput.intervalFubini source target)

/-- Tate-weight-drop inverse source rectangles are the input target rectangles. -/
theorem TraceLocalizationInput.tateWeightDropInverseArrow_sourceImportedRectangles
    (source target : QTraceExpression) :
    (TraceLocalizationInput.tateWeightDropInverseArrow
      source
      target).sourceImportedRectangles =
      (TraceLocalizationInput.tateWeightDrop source target).targetObject.importedRectangles :=
  TraceLocalizationInput.localizedInverseArrow_sourceImportedRectangles
    (TraceLocalizationInput.tateWeightDrop source target)

/-- Descent-channel inverse target rectangles are the input source rectangles. -/
theorem TraceLocalizationInput.descentChannelInverseArrow_targetImportedRectangles
    (source target : QTraceExpression) :
    (TraceLocalizationInput.descentChannelInverseArrow
      source
      target).targetImportedRectangles =
      (TraceLocalizationInput.descentChannel source target).sourceObject.importedRectangles :=
  TraceLocalizationInput.localizedInverseArrow_targetImportedRectangles
    (TraceLocalizationInput.descentChannel source target)

/-- Descent-refinement inverse target rectangles are the input source rectangles. -/
theorem TraceLocalizationInput.descentRefinementInverseArrow_targetImportedRectangles
    (source target : QTraceExpression) :
    (TraceLocalizationInput.descentRefinementInverseArrow
      source
      target).targetImportedRectangles =
      (TraceLocalizationInput.descentRefinement source target).sourceObject.importedRectangles :=
  TraceLocalizationInput.localizedInverseArrow_targetImportedRectangles
    (TraceLocalizationInput.descentRefinement source target)

/-- Descent-schedule inverse target rectangles are the input source rectangles. -/
theorem TraceLocalizationInput.descentScheduleInverseArrow_targetImportedRectangles
    (source target : QTraceExpression) :
    (TraceLocalizationInput.descentScheduleInverseArrow
      source
      target).targetImportedRectangles =
      (TraceLocalizationInput.descentSchedule source target).sourceObject.importedRectangles :=
  TraceLocalizationInput.localizedInverseArrow_targetImportedRectangles
    (TraceLocalizationInput.descentSchedule source target)

/-- Interval-Stokes inverse target rectangles are the input source rectangles. -/
theorem TraceLocalizationInput.intervalStokesInverseArrow_targetImportedRectangles
    (source target : QTraceExpression) :
    (TraceLocalizationInput.intervalStokesInverseArrow
      source
      target).targetImportedRectangles =
      (TraceLocalizationInput.intervalStokes source target).sourceObject.importedRectangles :=
  TraceLocalizationInput.localizedInverseArrow_targetImportedRectangles
    (TraceLocalizationInput.intervalStokes source target)

/-- Interval-Fubini inverse target rectangles are the input source rectangles. -/
theorem TraceLocalizationInput.intervalFubiniInverseArrow_targetImportedRectangles
    (source target : QTraceExpression) :
    (TraceLocalizationInput.intervalFubiniInverseArrow
      source
      target).targetImportedRectangles =
      (TraceLocalizationInput.intervalFubini source target).sourceObject.importedRectangles :=
  TraceLocalizationInput.localizedInverseArrow_targetImportedRectangles
    (TraceLocalizationInput.intervalFubini source target)

/-- Tate-weight-drop inverse target rectangles are the input source rectangles. -/
theorem TraceLocalizationInput.tateWeightDropInverseArrow_targetImportedRectangles
    (source target : QTraceExpression) :
    (TraceLocalizationInput.tateWeightDropInverseArrow
      source
      target).targetImportedRectangles =
      (TraceLocalizationInput.tateWeightDrop source target).sourceObject.importedRectangles :=
  TraceLocalizationInput.localizedInverseArrow_targetImportedRectangles
    (TraceLocalizationInput.tateWeightDrop source target)

end AnalyticMotives
end LFunctions
end Boundary
