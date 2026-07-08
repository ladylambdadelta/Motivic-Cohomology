import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.LocalizationInput.WordQuotient.Category.Inputs.ByKind.Payload.TraceCalculus.Counts.Bookkeeping.Owner

/-!
# Trace-calculus endpoint counts for named input arrows by kind

This file owns rewrite-step-count projections for each named localization-input
forward and inverse arrow.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Descent-channel forward arrow source rewrite-step count. -/
theorem TraceLocalizationInput.descentChannelForwardArrow_sourceRewriteStepCount
    (source target : QTraceExpression) :
    (TraceLocalizationInput.descentChannelForwardArrow
      source
      target).sourceRewriteStepCount =
      (TraceLocalizationInput.descentChannel
        source
        target).sourceObject.rewriteStepCount :=
  rfl

/-- Descent-channel forward arrow target rewrite-step count. -/
theorem TraceLocalizationInput.descentChannelForwardArrow_targetRewriteStepCount
    (source target : QTraceExpression) :
    (TraceLocalizationInput.descentChannelForwardArrow
      source
      target).targetRewriteStepCount =
      (TraceLocalizationInput.descentChannel
        source
        target).targetObject.rewriteStepCount :=
  rfl

/-- Descent-channel inverse arrow source rewrite-step count. -/
theorem TraceLocalizationInput.descentChannelInverseArrow_sourceRewriteStepCount
    (source target : QTraceExpression) :
    (TraceLocalizationInput.descentChannelInverseArrow
      source
      target).sourceRewriteStepCount =
      (TraceLocalizationInput.descentChannel
        source
        target).targetObject.rewriteStepCount :=
  rfl

/-- Descent-channel inverse arrow target rewrite-step count. -/
theorem TraceLocalizationInput.descentChannelInverseArrow_targetRewriteStepCount
    (source target : QTraceExpression) :
    (TraceLocalizationInput.descentChannelInverseArrow
      source
      target).targetRewriteStepCount =
      (TraceLocalizationInput.descentChannel
        source
        target).sourceObject.rewriteStepCount :=
  rfl

/-- Descent-refinement forward arrow source rewrite-step count. -/
theorem TraceLocalizationInput.descentRefinementForwardArrow_sourceRewriteStepCount
    (source target : QTraceExpression) :
    (TraceLocalizationInput.descentRefinementForwardArrow
      source
      target).sourceRewriteStepCount =
      (TraceLocalizationInput.descentRefinement
        source
        target).sourceObject.rewriteStepCount :=
  rfl

/-- Descent-refinement forward arrow target rewrite-step count. -/
theorem TraceLocalizationInput.descentRefinementForwardArrow_targetRewriteStepCount
    (source target : QTraceExpression) :
    (TraceLocalizationInput.descentRefinementForwardArrow
      source
      target).targetRewriteStepCount =
      (TraceLocalizationInput.descentRefinement
        source
        target).targetObject.rewriteStepCount :=
  rfl

/-- Descent-refinement inverse arrow source rewrite-step count. -/
theorem TraceLocalizationInput.descentRefinementInverseArrow_sourceRewriteStepCount
    (source target : QTraceExpression) :
    (TraceLocalizationInput.descentRefinementInverseArrow
      source
      target).sourceRewriteStepCount =
      (TraceLocalizationInput.descentRefinement
        source
        target).targetObject.rewriteStepCount :=
  rfl

/-- Descent-refinement inverse arrow target rewrite-step count. -/
theorem TraceLocalizationInput.descentRefinementInverseArrow_targetRewriteStepCount
    (source target : QTraceExpression) :
    (TraceLocalizationInput.descentRefinementInverseArrow
      source
      target).targetRewriteStepCount =
      (TraceLocalizationInput.descentRefinement
        source
        target).sourceObject.rewriteStepCount :=
  rfl

/-- Descent-schedule forward arrow source rewrite-step count. -/
theorem TraceLocalizationInput.descentScheduleForwardArrow_sourceRewriteStepCount
    (source target : QTraceExpression) :
    (TraceLocalizationInput.descentScheduleForwardArrow
      source
      target).sourceRewriteStepCount =
      (TraceLocalizationInput.descentSchedule
        source
        target).sourceObject.rewriteStepCount :=
  rfl

/-- Descent-schedule forward arrow target rewrite-step count. -/
theorem TraceLocalizationInput.descentScheduleForwardArrow_targetRewriteStepCount
    (source target : QTraceExpression) :
    (TraceLocalizationInput.descentScheduleForwardArrow
      source
      target).targetRewriteStepCount =
      (TraceLocalizationInput.descentSchedule
        source
        target).targetObject.rewriteStepCount :=
  rfl

/-- Descent-schedule inverse arrow source rewrite-step count. -/
theorem TraceLocalizationInput.descentScheduleInverseArrow_sourceRewriteStepCount
    (source target : QTraceExpression) :
    (TraceLocalizationInput.descentScheduleInverseArrow
      source
      target).sourceRewriteStepCount =
      (TraceLocalizationInput.descentSchedule
        source
        target).targetObject.rewriteStepCount :=
  rfl

/-- Descent-schedule inverse arrow target rewrite-step count. -/
theorem TraceLocalizationInput.descentScheduleInverseArrow_targetRewriteStepCount
    (source target : QTraceExpression) :
    (TraceLocalizationInput.descentScheduleInverseArrow
      source
      target).targetRewriteStepCount =
      (TraceLocalizationInput.descentSchedule
        source
        target).sourceObject.rewriteStepCount :=
  rfl

/-- Interval-Stokes forward arrow source rewrite-step count. -/
theorem TraceLocalizationInput.intervalStokesForwardArrow_sourceRewriteStepCount
    (source target : QTraceExpression) :
    (TraceLocalizationInput.intervalStokesForwardArrow
      source
      target).sourceRewriteStepCount =
      (TraceLocalizationInput.intervalStokes
        source
        target).sourceObject.rewriteStepCount :=
  rfl

/-- Interval-Stokes forward arrow target rewrite-step count. -/
theorem TraceLocalizationInput.intervalStokesForwardArrow_targetRewriteStepCount
    (source target : QTraceExpression) :
    (TraceLocalizationInput.intervalStokesForwardArrow
      source
      target).targetRewriteStepCount =
      (TraceLocalizationInput.intervalStokes
        source
        target).targetObject.rewriteStepCount :=
  rfl

/-- Interval-Stokes inverse arrow source rewrite-step count. -/
theorem TraceLocalizationInput.intervalStokesInverseArrow_sourceRewriteStepCount
    (source target : QTraceExpression) :
    (TraceLocalizationInput.intervalStokesInverseArrow
      source
      target).sourceRewriteStepCount =
      (TraceLocalizationInput.intervalStokes
        source
        target).targetObject.rewriteStepCount :=
  rfl

/-- Interval-Stokes inverse arrow target rewrite-step count. -/
theorem TraceLocalizationInput.intervalStokesInverseArrow_targetRewriteStepCount
    (source target : QTraceExpression) :
    (TraceLocalizationInput.intervalStokesInverseArrow
      source
      target).targetRewriteStepCount =
      (TraceLocalizationInput.intervalStokes
        source
        target).sourceObject.rewriteStepCount :=
  rfl

/-- Interval-Fubini forward arrow source rewrite-step count. -/
theorem TraceLocalizationInput.intervalFubiniForwardArrow_sourceRewriteStepCount
    (source target : QTraceExpression) :
    (TraceLocalizationInput.intervalFubiniForwardArrow
      source
      target).sourceRewriteStepCount =
      (TraceLocalizationInput.intervalFubini
        source
        target).sourceObject.rewriteStepCount :=
  rfl

/-- Interval-Fubini forward arrow target rewrite-step count. -/
theorem TraceLocalizationInput.intervalFubiniForwardArrow_targetRewriteStepCount
    (source target : QTraceExpression) :
    (TraceLocalizationInput.intervalFubiniForwardArrow
      source
      target).targetRewriteStepCount =
      (TraceLocalizationInput.intervalFubini
        source
        target).targetObject.rewriteStepCount :=
  rfl

/-- Interval-Fubini inverse arrow source rewrite-step count. -/
theorem TraceLocalizationInput.intervalFubiniInverseArrow_sourceRewriteStepCount
    (source target : QTraceExpression) :
    (TraceLocalizationInput.intervalFubiniInverseArrow
      source
      target).sourceRewriteStepCount =
      (TraceLocalizationInput.intervalFubini
        source
        target).targetObject.rewriteStepCount :=
  rfl

/-- Interval-Fubini inverse arrow target rewrite-step count. -/
theorem TraceLocalizationInput.intervalFubiniInverseArrow_targetRewriteStepCount
    (source target : QTraceExpression) :
    (TraceLocalizationInput.intervalFubiniInverseArrow
      source
      target).targetRewriteStepCount =
      (TraceLocalizationInput.intervalFubini
        source
        target).sourceObject.rewriteStepCount :=
  rfl

/-- Tate-weight-drop forward arrow source rewrite-step count. -/
theorem TraceLocalizationInput.tateWeightDropForwardArrow_sourceRewriteStepCount
    (source target : QTraceExpression) :
    (TraceLocalizationInput.tateWeightDropForwardArrow
      source
      target).sourceRewriteStepCount =
      (TraceLocalizationInput.tateWeightDrop
        source
        target).sourceObject.rewriteStepCount :=
  rfl

/-- Tate-weight-drop forward arrow target rewrite-step count. -/
theorem TraceLocalizationInput.tateWeightDropForwardArrow_targetRewriteStepCount
    (source target : QTraceExpression) :
    (TraceLocalizationInput.tateWeightDropForwardArrow
      source
      target).targetRewriteStepCount =
      (TraceLocalizationInput.tateWeightDrop
        source
        target).targetObject.rewriteStepCount :=
  rfl

/-- Tate-weight-drop inverse arrow source rewrite-step count. -/
theorem TraceLocalizationInput.tateWeightDropInverseArrow_sourceRewriteStepCount
    (source target : QTraceExpression) :
    (TraceLocalizationInput.tateWeightDropInverseArrow
      source
      target).sourceRewriteStepCount =
      (TraceLocalizationInput.tateWeightDrop
        source
        target).targetObject.rewriteStepCount :=
  rfl

/-- Tate-weight-drop inverse arrow target rewrite-step count. -/
theorem TraceLocalizationInput.tateWeightDropInverseArrow_targetRewriteStepCount
    (source target : QTraceExpression) :
    (TraceLocalizationInput.tateWeightDropInverseArrow
      source
      target).targetRewriteStepCount =
      (TraceLocalizationInput.tateWeightDrop
        source
        target).sourceObject.rewriteStepCount :=
  rfl

end AnalyticMotives
end LFunctions
end Boundary
