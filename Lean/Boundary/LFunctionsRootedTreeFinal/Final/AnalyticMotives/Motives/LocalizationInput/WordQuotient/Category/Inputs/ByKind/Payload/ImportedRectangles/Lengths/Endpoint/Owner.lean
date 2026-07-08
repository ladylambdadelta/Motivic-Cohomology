import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.LocalizationInput.WordQuotient.Category.Inputs.ByKind.Payload.ImportedRectangles.Counts.Owner

/-!
# Endpoint length facts for named imported finite-rectangle payload

This file gives by-kind names to endpoint imported-rectangle count/length
facts for named forward and inverse localization arrows.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Descent-channel forward endpoint rectangle count is its endpoint rectangle-list length. -/
theorem TraceLocalizationInput.descentChannelForwardArrow_endpointImportedRectangleCount_eq_length
    (source target : QTraceExpression) :
    (TraceLocalizationInput.descentChannelForwardArrow
      source
      target).endpointImportedRectangleCount =
      (TraceLocalizationInput.descentChannelForwardArrow
        source
        target).endpointImportedRectangles.length :=
  TraceLocalizationInput.localizedForwardArrow_endpointImportedRectangleCount_eq_length
    (TraceLocalizationInput.descentChannel source target)

/-- Descent-refinement forward endpoint rectangle count is its endpoint rectangle-list length. -/
theorem TraceLocalizationInput.descentRefinementForwardArrow_endpointImportedRectangleCount_eq_length
    (source target : QTraceExpression) :
    (TraceLocalizationInput.descentRefinementForwardArrow
      source
      target).endpointImportedRectangleCount =
      (TraceLocalizationInput.descentRefinementForwardArrow
        source
        target).endpointImportedRectangles.length :=
  TraceLocalizationInput.localizedForwardArrow_endpointImportedRectangleCount_eq_length
    (TraceLocalizationInput.descentRefinement source target)

/-- Descent-schedule forward endpoint rectangle count is its endpoint rectangle-list length. -/
theorem TraceLocalizationInput.descentScheduleForwardArrow_endpointImportedRectangleCount_eq_length
    (source target : QTraceExpression) :
    (TraceLocalizationInput.descentScheduleForwardArrow
      source
      target).endpointImportedRectangleCount =
      (TraceLocalizationInput.descentScheduleForwardArrow
        source
        target).endpointImportedRectangles.length :=
  TraceLocalizationInput.localizedForwardArrow_endpointImportedRectangleCount_eq_length
    (TraceLocalizationInput.descentSchedule source target)

/-- Interval-Stokes forward endpoint rectangle count is its endpoint rectangle-list length. -/
theorem TraceLocalizationInput.intervalStokesForwardArrow_endpointImportedRectangleCount_eq_length
    (source target : QTraceExpression) :
    (TraceLocalizationInput.intervalStokesForwardArrow
      source
      target).endpointImportedRectangleCount =
      (TraceLocalizationInput.intervalStokesForwardArrow
        source
        target).endpointImportedRectangles.length :=
  TraceLocalizationInput.localizedForwardArrow_endpointImportedRectangleCount_eq_length
    (TraceLocalizationInput.intervalStokes source target)

/-- Interval-Fubini forward endpoint rectangle count is its endpoint rectangle-list length. -/
theorem TraceLocalizationInput.intervalFubiniForwardArrow_endpointImportedRectangleCount_eq_length
    (source target : QTraceExpression) :
    (TraceLocalizationInput.intervalFubiniForwardArrow
      source
      target).endpointImportedRectangleCount =
      (TraceLocalizationInput.intervalFubiniForwardArrow
        source
        target).endpointImportedRectangles.length :=
  TraceLocalizationInput.localizedForwardArrow_endpointImportedRectangleCount_eq_length
    (TraceLocalizationInput.intervalFubini source target)

/-- Tate-weight-drop forward endpoint rectangle count is its endpoint rectangle-list length. -/
theorem TraceLocalizationInput.tateWeightDropForwardArrow_endpointImportedRectangleCount_eq_length
    (source target : QTraceExpression) :
    (TraceLocalizationInput.tateWeightDropForwardArrow
      source
      target).endpointImportedRectangleCount =
      (TraceLocalizationInput.tateWeightDropForwardArrow
        source
        target).endpointImportedRectangles.length :=
  TraceLocalizationInput.localizedForwardArrow_endpointImportedRectangleCount_eq_length
    (TraceLocalizationInput.tateWeightDrop source target)

/-- Descent-channel inverse endpoint rectangle count is its endpoint rectangle-list length. -/
theorem TraceLocalizationInput.descentChannelInverseArrow_endpointImportedRectangleCount_eq_length
    (source target : QTraceExpression) :
    (TraceLocalizationInput.descentChannelInverseArrow
      source
      target).endpointImportedRectangleCount =
      (TraceLocalizationInput.descentChannelInverseArrow
        source
        target).endpointImportedRectangles.length :=
  TraceLocalizationInput.localizedInverseArrow_endpointImportedRectangleCount_eq_length
    (TraceLocalizationInput.descentChannel source target)

/-- Descent-refinement inverse endpoint rectangle count is its endpoint rectangle-list length. -/
theorem TraceLocalizationInput.descentRefinementInverseArrow_endpointImportedRectangleCount_eq_length
    (source target : QTraceExpression) :
    (TraceLocalizationInput.descentRefinementInverseArrow
      source
      target).endpointImportedRectangleCount =
      (TraceLocalizationInput.descentRefinementInverseArrow
        source
        target).endpointImportedRectangles.length :=
  TraceLocalizationInput.localizedInverseArrow_endpointImportedRectangleCount_eq_length
    (TraceLocalizationInput.descentRefinement source target)

/-- Descent-schedule inverse endpoint rectangle count is its endpoint rectangle-list length. -/
theorem TraceLocalizationInput.descentScheduleInverseArrow_endpointImportedRectangleCount_eq_length
    (source target : QTraceExpression) :
    (TraceLocalizationInput.descentScheduleInverseArrow
      source
      target).endpointImportedRectangleCount =
      (TraceLocalizationInput.descentScheduleInverseArrow
        source
        target).endpointImportedRectangles.length :=
  TraceLocalizationInput.localizedInverseArrow_endpointImportedRectangleCount_eq_length
    (TraceLocalizationInput.descentSchedule source target)

/-- Interval-Stokes inverse endpoint rectangle count is its endpoint rectangle-list length. -/
theorem TraceLocalizationInput.intervalStokesInverseArrow_endpointImportedRectangleCount_eq_length
    (source target : QTraceExpression) :
    (TraceLocalizationInput.intervalStokesInverseArrow
      source
      target).endpointImportedRectangleCount =
      (TraceLocalizationInput.intervalStokesInverseArrow
        source
        target).endpointImportedRectangles.length :=
  TraceLocalizationInput.localizedInverseArrow_endpointImportedRectangleCount_eq_length
    (TraceLocalizationInput.intervalStokes source target)

/-- Interval-Fubini inverse endpoint rectangle count is its endpoint rectangle-list length. -/
theorem TraceLocalizationInput.intervalFubiniInverseArrow_endpointImportedRectangleCount_eq_length
    (source target : QTraceExpression) :
    (TraceLocalizationInput.intervalFubiniInverseArrow
      source
      target).endpointImportedRectangleCount =
      (TraceLocalizationInput.intervalFubiniInverseArrow
        source
        target).endpointImportedRectangles.length :=
  TraceLocalizationInput.localizedInverseArrow_endpointImportedRectangleCount_eq_length
    (TraceLocalizationInput.intervalFubini source target)

/-- Tate-weight-drop inverse endpoint rectangle count is its endpoint rectangle-list length. -/
theorem TraceLocalizationInput.tateWeightDropInverseArrow_endpointImportedRectangleCount_eq_length
    (source target : QTraceExpression) :
    (TraceLocalizationInput.tateWeightDropInverseArrow
      source
      target).endpointImportedRectangleCount =
      (TraceLocalizationInput.tateWeightDropInverseArrow
        source
        target).endpointImportedRectangles.length :=
  TraceLocalizationInput.localizedInverseArrow_endpointImportedRectangleCount_eq_length
    (TraceLocalizationInput.tateWeightDrop source target)

end AnalyticMotives
end LFunctions
end Boundary
