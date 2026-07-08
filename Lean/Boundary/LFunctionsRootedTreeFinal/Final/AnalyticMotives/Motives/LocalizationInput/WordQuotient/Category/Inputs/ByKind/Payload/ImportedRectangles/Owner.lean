import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.LocalizationInput.WordQuotient.Category.Inputs.ByKind.Payload.ImportedRectangles.ArrowEndpoints.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.LocalizationInput.WordQuotient.Category.Inputs.ByKind.Payload.ImportedRectangles.LedgerRectangles.Owner

/-!
# Endpoint imported finite-rectangle payload for named input arrows by kind

This file gives by-kind names to the endpoint imported finite-rectangle
payload carried by the forward and inverse arrows attached to localization
inputs.  Source and target endpoint projections live in the `ArrowEndpoints`
child.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Descent-channel forward endpoint rectangles are source rectangles followed by target rectangles. -/
theorem TraceLocalizationInput.descentChannelForwardArrow_endpointImportedRectangles
    (source target : QTraceExpression) :
    (TraceLocalizationInput.descentChannelForwardArrow
      source
      target).endpointImportedRectangles =
      (TraceLocalizationInput.descentChannel source target).sourceObject.importedRectangles ++
        (TraceLocalizationInput.descentChannel source target).targetObject.importedRectangles :=
  TraceLocalizationInput.localizedForwardArrow_endpointImportedRectangles
    (TraceLocalizationInput.descentChannel source target)

/-- Descent-refinement forward endpoint rectangles are source rectangles followed by target rectangles. -/
theorem TraceLocalizationInput.descentRefinementForwardArrow_endpointImportedRectangles
    (source target : QTraceExpression) :
    (TraceLocalizationInput.descentRefinementForwardArrow
      source
      target).endpointImportedRectangles =
      (TraceLocalizationInput.descentRefinement source target).sourceObject.importedRectangles ++
        (TraceLocalizationInput.descentRefinement source target).targetObject.importedRectangles :=
  TraceLocalizationInput.localizedForwardArrow_endpointImportedRectangles
    (TraceLocalizationInput.descentRefinement source target)

/-- Descent-schedule forward endpoint rectangles are source rectangles followed by target rectangles. -/
theorem TraceLocalizationInput.descentScheduleForwardArrow_endpointImportedRectangles
    (source target : QTraceExpression) :
    (TraceLocalizationInput.descentScheduleForwardArrow
      source
      target).endpointImportedRectangles =
      (TraceLocalizationInput.descentSchedule source target).sourceObject.importedRectangles ++
        (TraceLocalizationInput.descentSchedule source target).targetObject.importedRectangles :=
  TraceLocalizationInput.localizedForwardArrow_endpointImportedRectangles
    (TraceLocalizationInput.descentSchedule source target)

/-- Interval-Stokes forward endpoint rectangles are source rectangles followed by target rectangles. -/
theorem TraceLocalizationInput.intervalStokesForwardArrow_endpointImportedRectangles
    (source target : QTraceExpression) :
    (TraceLocalizationInput.intervalStokesForwardArrow
      source
      target).endpointImportedRectangles =
      (TraceLocalizationInput.intervalStokes source target).sourceObject.importedRectangles ++
        (TraceLocalizationInput.intervalStokes source target).targetObject.importedRectangles :=
  TraceLocalizationInput.localizedForwardArrow_endpointImportedRectangles
    (TraceLocalizationInput.intervalStokes source target)

/-- Interval-Fubini forward endpoint rectangles are source rectangles followed by target rectangles. -/
theorem TraceLocalizationInput.intervalFubiniForwardArrow_endpointImportedRectangles
    (source target : QTraceExpression) :
    (TraceLocalizationInput.intervalFubiniForwardArrow
      source
      target).endpointImportedRectangles =
      (TraceLocalizationInput.intervalFubini source target).sourceObject.importedRectangles ++
        (TraceLocalizationInput.intervalFubini source target).targetObject.importedRectangles :=
  TraceLocalizationInput.localizedForwardArrow_endpointImportedRectangles
    (TraceLocalizationInput.intervalFubini source target)

/-- Tate-weight-drop forward endpoint rectangles are source rectangles followed by target rectangles. -/
theorem TraceLocalizationInput.tateWeightDropForwardArrow_endpointImportedRectangles
    (source target : QTraceExpression) :
    (TraceLocalizationInput.tateWeightDropForwardArrow
      source
      target).endpointImportedRectangles =
      (TraceLocalizationInput.tateWeightDrop source target).sourceObject.importedRectangles ++
        (TraceLocalizationInput.tateWeightDrop source target).targetObject.importedRectangles :=
  TraceLocalizationInput.localizedForwardArrow_endpointImportedRectangles
    (TraceLocalizationInput.tateWeightDrop source target)

/-- Descent-channel inverse endpoint rectangles are target rectangles followed by source rectangles. -/
theorem TraceLocalizationInput.descentChannelInverseArrow_endpointImportedRectangles
    (source target : QTraceExpression) :
    (TraceLocalizationInput.descentChannelInverseArrow
      source
      target).endpointImportedRectangles =
      (TraceLocalizationInput.descentChannel source target).targetObject.importedRectangles ++
        (TraceLocalizationInput.descentChannel source target).sourceObject.importedRectangles :=
  TraceLocalizationInput.localizedInverseArrow_endpointImportedRectangles
    (TraceLocalizationInput.descentChannel source target)

/-- Descent-refinement inverse endpoint rectangles are target rectangles followed by source rectangles. -/
theorem TraceLocalizationInput.descentRefinementInverseArrow_endpointImportedRectangles
    (source target : QTraceExpression) :
    (TraceLocalizationInput.descentRefinementInverseArrow
      source
      target).endpointImportedRectangles =
      (TraceLocalizationInput.descentRefinement source target).targetObject.importedRectangles ++
        (TraceLocalizationInput.descentRefinement source target).sourceObject.importedRectangles :=
  TraceLocalizationInput.localizedInverseArrow_endpointImportedRectangles
    (TraceLocalizationInput.descentRefinement source target)

/-- Descent-schedule inverse endpoint rectangles are target rectangles followed by source rectangles. -/
theorem TraceLocalizationInput.descentScheduleInverseArrow_endpointImportedRectangles
    (source target : QTraceExpression) :
    (TraceLocalizationInput.descentScheduleInverseArrow
      source
      target).endpointImportedRectangles =
      (TraceLocalizationInput.descentSchedule source target).targetObject.importedRectangles ++
        (TraceLocalizationInput.descentSchedule source target).sourceObject.importedRectangles :=
  TraceLocalizationInput.localizedInverseArrow_endpointImportedRectangles
    (TraceLocalizationInput.descentSchedule source target)

/-- Interval-Stokes inverse endpoint rectangles are target rectangles followed by source rectangles. -/
theorem TraceLocalizationInput.intervalStokesInverseArrow_endpointImportedRectangles
    (source target : QTraceExpression) :
    (TraceLocalizationInput.intervalStokesInverseArrow
      source
      target).endpointImportedRectangles =
      (TraceLocalizationInput.intervalStokes source target).targetObject.importedRectangles ++
        (TraceLocalizationInput.intervalStokes source target).sourceObject.importedRectangles :=
  TraceLocalizationInput.localizedInverseArrow_endpointImportedRectangles
    (TraceLocalizationInput.intervalStokes source target)

/-- Interval-Fubini inverse endpoint rectangles are target rectangles followed by source rectangles. -/
theorem TraceLocalizationInput.intervalFubiniInverseArrow_endpointImportedRectangles
    (source target : QTraceExpression) :
    (TraceLocalizationInput.intervalFubiniInverseArrow
      source
      target).endpointImportedRectangles =
      (TraceLocalizationInput.intervalFubini source target).targetObject.importedRectangles ++
        (TraceLocalizationInput.intervalFubini source target).sourceObject.importedRectangles :=
  TraceLocalizationInput.localizedInverseArrow_endpointImportedRectangles
    (TraceLocalizationInput.intervalFubini source target)

/-- Tate-weight-drop inverse endpoint rectangles are target rectangles followed by source rectangles. -/
theorem TraceLocalizationInput.tateWeightDropInverseArrow_endpointImportedRectangles
    (source target : QTraceExpression) :
    (TraceLocalizationInput.tateWeightDropInverseArrow
      source
      target).endpointImportedRectangles =
      (TraceLocalizationInput.tateWeightDrop source target).targetObject.importedRectangles ++
        (TraceLocalizationInput.tateWeightDrop source target).sourceObject.importedRectangles :=
  TraceLocalizationInput.localizedInverseArrow_endpointImportedRectangles
    (TraceLocalizationInput.tateWeightDrop source target)

end AnalyticMotives
end LFunctions
end Boundary
