import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.LocalizationInput.WordQuotient.Category.Inputs.ByKind.Payload.TraceCalculus.Owner

/-!
# Trace-bookkeeping endpoint counts for named input arrows by kind

This file owns the bookkeeping-count projections for each named
localization-input forward and inverse arrow.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Descent-channel forward arrow source bookkeeping count. -/
theorem TraceLocalizationInput.descentChannelForwardArrow_sourceTraceBookkeepingCount
    (source target : QTraceExpression) :
    (TraceLocalizationInput.descentChannelForwardArrow
      source
      target).sourceTraceBookkeepingCount =
      (TraceLocalizationInput.descentChannel
        source
        target).sourceObject.traceBookkeepingCount :=
  rfl

/-- Descent-channel forward arrow target bookkeeping count. -/
theorem TraceLocalizationInput.descentChannelForwardArrow_targetTraceBookkeepingCount
    (source target : QTraceExpression) :
    (TraceLocalizationInput.descentChannelForwardArrow
      source
      target).targetTraceBookkeepingCount =
      (TraceLocalizationInput.descentChannel
        source
        target).targetObject.traceBookkeepingCount :=
  rfl

/-- Descent-channel inverse arrow source bookkeeping count. -/
theorem TraceLocalizationInput.descentChannelInverseArrow_sourceTraceBookkeepingCount
    (source target : QTraceExpression) :
    (TraceLocalizationInput.descentChannelInverseArrow
      source
      target).sourceTraceBookkeepingCount =
      (TraceLocalizationInput.descentChannel
        source
        target).targetObject.traceBookkeepingCount :=
  rfl

/-- Descent-channel inverse arrow target bookkeeping count. -/
theorem TraceLocalizationInput.descentChannelInverseArrow_targetTraceBookkeepingCount
    (source target : QTraceExpression) :
    (TraceLocalizationInput.descentChannelInverseArrow
      source
      target).targetTraceBookkeepingCount =
      (TraceLocalizationInput.descentChannel
        source
        target).sourceObject.traceBookkeepingCount :=
  rfl

/-- Descent-refinement forward arrow source bookkeeping count. -/
theorem TraceLocalizationInput.descentRefinementForwardArrow_sourceTraceBookkeepingCount
    (source target : QTraceExpression) :
    (TraceLocalizationInput.descentRefinementForwardArrow
      source
      target).sourceTraceBookkeepingCount =
      (TraceLocalizationInput.descentRefinement
        source
        target).sourceObject.traceBookkeepingCount :=
  rfl

/-- Descent-refinement forward arrow target bookkeeping count. -/
theorem TraceLocalizationInput.descentRefinementForwardArrow_targetTraceBookkeepingCount
    (source target : QTraceExpression) :
    (TraceLocalizationInput.descentRefinementForwardArrow
      source
      target).targetTraceBookkeepingCount =
      (TraceLocalizationInput.descentRefinement
        source
        target).targetObject.traceBookkeepingCount :=
  rfl

/-- Descent-refinement inverse arrow source bookkeeping count. -/
theorem TraceLocalizationInput.descentRefinementInverseArrow_sourceTraceBookkeepingCount
    (source target : QTraceExpression) :
    (TraceLocalizationInput.descentRefinementInverseArrow
      source
      target).sourceTraceBookkeepingCount =
      (TraceLocalizationInput.descentRefinement
        source
        target).targetObject.traceBookkeepingCount :=
  rfl

/-- Descent-refinement inverse arrow target bookkeeping count. -/
theorem TraceLocalizationInput.descentRefinementInverseArrow_targetTraceBookkeepingCount
    (source target : QTraceExpression) :
    (TraceLocalizationInput.descentRefinementInverseArrow
      source
      target).targetTraceBookkeepingCount =
      (TraceLocalizationInput.descentRefinement
        source
        target).sourceObject.traceBookkeepingCount :=
  rfl

/-- Descent-schedule forward arrow source bookkeeping count. -/
theorem TraceLocalizationInput.descentScheduleForwardArrow_sourceTraceBookkeepingCount
    (source target : QTraceExpression) :
    (TraceLocalizationInput.descentScheduleForwardArrow
      source
      target).sourceTraceBookkeepingCount =
      (TraceLocalizationInput.descentSchedule
        source
        target).sourceObject.traceBookkeepingCount :=
  rfl

/-- Descent-schedule forward arrow target bookkeeping count. -/
theorem TraceLocalizationInput.descentScheduleForwardArrow_targetTraceBookkeepingCount
    (source target : QTraceExpression) :
    (TraceLocalizationInput.descentScheduleForwardArrow
      source
      target).targetTraceBookkeepingCount =
      (TraceLocalizationInput.descentSchedule
        source
        target).targetObject.traceBookkeepingCount :=
  rfl

/-- Descent-schedule inverse arrow source bookkeeping count. -/
theorem TraceLocalizationInput.descentScheduleInverseArrow_sourceTraceBookkeepingCount
    (source target : QTraceExpression) :
    (TraceLocalizationInput.descentScheduleInverseArrow
      source
      target).sourceTraceBookkeepingCount =
      (TraceLocalizationInput.descentSchedule
        source
        target).targetObject.traceBookkeepingCount :=
  rfl

/-- Descent-schedule inverse arrow target bookkeeping count. -/
theorem TraceLocalizationInput.descentScheduleInverseArrow_targetTraceBookkeepingCount
    (source target : QTraceExpression) :
    (TraceLocalizationInput.descentScheduleInverseArrow
      source
      target).targetTraceBookkeepingCount =
      (TraceLocalizationInput.descentSchedule
        source
        target).sourceObject.traceBookkeepingCount :=
  rfl

/-- Interval-Stokes forward arrow source bookkeeping count. -/
theorem TraceLocalizationInput.intervalStokesForwardArrow_sourceTraceBookkeepingCount
    (source target : QTraceExpression) :
    (TraceLocalizationInput.intervalStokesForwardArrow
      source
      target).sourceTraceBookkeepingCount =
      (TraceLocalizationInput.intervalStokes
        source
        target).sourceObject.traceBookkeepingCount :=
  rfl

/-- Interval-Stokes forward arrow target bookkeeping count. -/
theorem TraceLocalizationInput.intervalStokesForwardArrow_targetTraceBookkeepingCount
    (source target : QTraceExpression) :
    (TraceLocalizationInput.intervalStokesForwardArrow
      source
      target).targetTraceBookkeepingCount =
      (TraceLocalizationInput.intervalStokes
        source
        target).targetObject.traceBookkeepingCount :=
  rfl

/-- Interval-Stokes inverse arrow source bookkeeping count. -/
theorem TraceLocalizationInput.intervalStokesInverseArrow_sourceTraceBookkeepingCount
    (source target : QTraceExpression) :
    (TraceLocalizationInput.intervalStokesInverseArrow
      source
      target).sourceTraceBookkeepingCount =
      (TraceLocalizationInput.intervalStokes
        source
        target).targetObject.traceBookkeepingCount :=
  rfl

/-- Interval-Stokes inverse arrow target bookkeeping count. -/
theorem TraceLocalizationInput.intervalStokesInverseArrow_targetTraceBookkeepingCount
    (source target : QTraceExpression) :
    (TraceLocalizationInput.intervalStokesInverseArrow
      source
      target).targetTraceBookkeepingCount =
      (TraceLocalizationInput.intervalStokes
        source
        target).sourceObject.traceBookkeepingCount :=
  rfl

/-- Interval-Fubini forward arrow source bookkeeping count. -/
theorem TraceLocalizationInput.intervalFubiniForwardArrow_sourceTraceBookkeepingCount
    (source target : QTraceExpression) :
    (TraceLocalizationInput.intervalFubiniForwardArrow
      source
      target).sourceTraceBookkeepingCount =
      (TraceLocalizationInput.intervalFubini
        source
        target).sourceObject.traceBookkeepingCount :=
  rfl

/-- Interval-Fubini forward arrow target bookkeeping count. -/
theorem TraceLocalizationInput.intervalFubiniForwardArrow_targetTraceBookkeepingCount
    (source target : QTraceExpression) :
    (TraceLocalizationInput.intervalFubiniForwardArrow
      source
      target).targetTraceBookkeepingCount =
      (TraceLocalizationInput.intervalFubini
        source
        target).targetObject.traceBookkeepingCount :=
  rfl

/-- Interval-Fubini inverse arrow source bookkeeping count. -/
theorem TraceLocalizationInput.intervalFubiniInverseArrow_sourceTraceBookkeepingCount
    (source target : QTraceExpression) :
    (TraceLocalizationInput.intervalFubiniInverseArrow
      source
      target).sourceTraceBookkeepingCount =
      (TraceLocalizationInput.intervalFubini
        source
        target).targetObject.traceBookkeepingCount :=
  rfl

/-- Interval-Fubini inverse arrow target bookkeeping count. -/
theorem TraceLocalizationInput.intervalFubiniInverseArrow_targetTraceBookkeepingCount
    (source target : QTraceExpression) :
    (TraceLocalizationInput.intervalFubiniInverseArrow
      source
      target).targetTraceBookkeepingCount =
      (TraceLocalizationInput.intervalFubini
        source
        target).sourceObject.traceBookkeepingCount :=
  rfl

/-- Tate-weight-drop forward arrow source bookkeeping count. -/
theorem TraceLocalizationInput.tateWeightDropForwardArrow_sourceTraceBookkeepingCount
    (source target : QTraceExpression) :
    (TraceLocalizationInput.tateWeightDropForwardArrow
      source
      target).sourceTraceBookkeepingCount =
      (TraceLocalizationInput.tateWeightDrop
        source
        target).sourceObject.traceBookkeepingCount :=
  rfl

/-- Tate-weight-drop forward arrow target bookkeeping count. -/
theorem TraceLocalizationInput.tateWeightDropForwardArrow_targetTraceBookkeepingCount
    (source target : QTraceExpression) :
    (TraceLocalizationInput.tateWeightDropForwardArrow
      source
      target).targetTraceBookkeepingCount =
      (TraceLocalizationInput.tateWeightDrop
        source
        target).targetObject.traceBookkeepingCount :=
  rfl

/-- Tate-weight-drop inverse arrow source bookkeeping count. -/
theorem TraceLocalizationInput.tateWeightDropInverseArrow_sourceTraceBookkeepingCount
    (source target : QTraceExpression) :
    (TraceLocalizationInput.tateWeightDropInverseArrow
      source
      target).sourceTraceBookkeepingCount =
      (TraceLocalizationInput.tateWeightDrop
        source
        target).targetObject.traceBookkeepingCount :=
  rfl

/-- Tate-weight-drop inverse arrow target bookkeeping count. -/
theorem TraceLocalizationInput.tateWeightDropInverseArrow_targetTraceBookkeepingCount
    (source target : QTraceExpression) :
    (TraceLocalizationInput.tateWeightDropInverseArrow
      source
      target).targetTraceBookkeepingCount =
      (TraceLocalizationInput.tateWeightDrop
        source
        target).sourceObject.traceBookkeepingCount :=
  rfl

end AnalyticMotives
end LFunctions
end Boundary
