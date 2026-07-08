import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.LocalizationInput.WordQuotient.Category.Inputs.ByKind.Isomorphisms.Payload.TraceCalculus.Owner

/-!
# Trace-bookkeeping arrow-endpoint counts for named localized isomorphisms

This file exposes source and target trace-bookkeeping counts through the hom
and inverse arrows of the named by-kind localized isomorphisms.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Descent-channel isomorphism hom source bookkeeping count is the input source count. -/
theorem TraceLocalizationInput.descentChannelLocalizedIso_hom_sourceTraceBookkeepingCount
    (source target : QTraceExpression) :
    (TraceLocalizationInput.descentChannelLocalizedIso
      source
      target).hom.sourceTraceBookkeepingCount =
      (TraceLocalizationInput.descentChannel source target).sourceObject.traceBookkeepingCount :=
  TraceLocalizationInput.descentChannelForwardArrow_sourceTraceBookkeepingCount
    source
    target

/-- Descent-channel isomorphism hom target bookkeeping count is the input target count. -/
theorem TraceLocalizationInput.descentChannelLocalizedIso_hom_targetTraceBookkeepingCount
    (source target : QTraceExpression) :
    (TraceLocalizationInput.descentChannelLocalizedIso
      source
      target).hom.targetTraceBookkeepingCount =
      (TraceLocalizationInput.descentChannel source target).targetObject.traceBookkeepingCount :=
  TraceLocalizationInput.descentChannelForwardArrow_targetTraceBookkeepingCount
    source
    target

/-- Descent-channel isomorphism inverse source bookkeeping count is the input target count. -/
theorem TraceLocalizationInput.descentChannelLocalizedIso_inv_sourceTraceBookkeepingCount
    (source target : QTraceExpression) :
    (TraceLocalizationInput.descentChannelLocalizedIso
      source
      target).inv.sourceTraceBookkeepingCount =
      (TraceLocalizationInput.descentChannel source target).targetObject.traceBookkeepingCount :=
  TraceLocalizationInput.descentChannelInverseArrow_sourceTraceBookkeepingCount
    source
    target

/-- Descent-channel isomorphism inverse target bookkeeping count is the input source count. -/
theorem TraceLocalizationInput.descentChannelLocalizedIso_inv_targetTraceBookkeepingCount
    (source target : QTraceExpression) :
    (TraceLocalizationInput.descentChannelLocalizedIso
      source
      target).inv.targetTraceBookkeepingCount =
      (TraceLocalizationInput.descentChannel source target).sourceObject.traceBookkeepingCount :=
  TraceLocalizationInput.descentChannelInverseArrow_targetTraceBookkeepingCount
    source
    target

/-- Descent-refinement isomorphism hom source bookkeeping count is the input source count. -/
theorem TraceLocalizationInput.descentRefinementLocalizedIso_hom_sourceTraceBookkeepingCount
    (source target : QTraceExpression) :
    (TraceLocalizationInput.descentRefinementLocalizedIso
      source
      target).hom.sourceTraceBookkeepingCount =
      (TraceLocalizationInput.descentRefinement source target).sourceObject.traceBookkeepingCount :=
  TraceLocalizationInput.descentRefinementForwardArrow_sourceTraceBookkeepingCount
    source
    target

/-- Descent-refinement isomorphism hom target bookkeeping count is the input target count. -/
theorem TraceLocalizationInput.descentRefinementLocalizedIso_hom_targetTraceBookkeepingCount
    (source target : QTraceExpression) :
    (TraceLocalizationInput.descentRefinementLocalizedIso
      source
      target).hom.targetTraceBookkeepingCount =
      (TraceLocalizationInput.descentRefinement source target).targetObject.traceBookkeepingCount :=
  TraceLocalizationInput.descentRefinementForwardArrow_targetTraceBookkeepingCount
    source
    target

/-- Descent-refinement isomorphism inverse source bookkeeping count is the input target count. -/
theorem TraceLocalizationInput.descentRefinementLocalizedIso_inv_sourceTraceBookkeepingCount
    (source target : QTraceExpression) :
    (TraceLocalizationInput.descentRefinementLocalizedIso
      source
      target).inv.sourceTraceBookkeepingCount =
      (TraceLocalizationInput.descentRefinement source target).targetObject.traceBookkeepingCount :=
  TraceLocalizationInput.descentRefinementInverseArrow_sourceTraceBookkeepingCount
    source
    target

/-- Descent-refinement isomorphism inverse target bookkeeping count is the input source count. -/
theorem TraceLocalizationInput.descentRefinementLocalizedIso_inv_targetTraceBookkeepingCount
    (source target : QTraceExpression) :
    (TraceLocalizationInput.descentRefinementLocalizedIso
      source
      target).inv.targetTraceBookkeepingCount =
      (TraceLocalizationInput.descentRefinement source target).sourceObject.traceBookkeepingCount :=
  TraceLocalizationInput.descentRefinementInverseArrow_targetTraceBookkeepingCount
    source
    target

/-- Descent-schedule isomorphism hom source bookkeeping count is the input source count. -/
theorem TraceLocalizationInput.descentScheduleLocalizedIso_hom_sourceTraceBookkeepingCount
    (source target : QTraceExpression) :
    (TraceLocalizationInput.descentScheduleLocalizedIso
      source
      target).hom.sourceTraceBookkeepingCount =
      (TraceLocalizationInput.descentSchedule source target).sourceObject.traceBookkeepingCount :=
  TraceLocalizationInput.descentScheduleForwardArrow_sourceTraceBookkeepingCount
    source
    target

/-- Descent-schedule isomorphism hom target bookkeeping count is the input target count. -/
theorem TraceLocalizationInput.descentScheduleLocalizedIso_hom_targetTraceBookkeepingCount
    (source target : QTraceExpression) :
    (TraceLocalizationInput.descentScheduleLocalizedIso
      source
      target).hom.targetTraceBookkeepingCount =
      (TraceLocalizationInput.descentSchedule source target).targetObject.traceBookkeepingCount :=
  TraceLocalizationInput.descentScheduleForwardArrow_targetTraceBookkeepingCount
    source
    target

/-- Descent-schedule isomorphism inverse source bookkeeping count is the input target count. -/
theorem TraceLocalizationInput.descentScheduleLocalizedIso_inv_sourceTraceBookkeepingCount
    (source target : QTraceExpression) :
    (TraceLocalizationInput.descentScheduleLocalizedIso
      source
      target).inv.sourceTraceBookkeepingCount =
      (TraceLocalizationInput.descentSchedule source target).targetObject.traceBookkeepingCount :=
  TraceLocalizationInput.descentScheduleInverseArrow_sourceTraceBookkeepingCount
    source
    target

/-- Descent-schedule isomorphism inverse target bookkeeping count is the input source count. -/
theorem TraceLocalizationInput.descentScheduleLocalizedIso_inv_targetTraceBookkeepingCount
    (source target : QTraceExpression) :
    (TraceLocalizationInput.descentScheduleLocalizedIso
      source
      target).inv.targetTraceBookkeepingCount =
      (TraceLocalizationInput.descentSchedule source target).sourceObject.traceBookkeepingCount :=
  TraceLocalizationInput.descentScheduleInverseArrow_targetTraceBookkeepingCount
    source
    target

/-- Interval-Stokes isomorphism hom source bookkeeping count is the input source count. -/
theorem TraceLocalizationInput.intervalStokesLocalizedIso_hom_sourceTraceBookkeepingCount
    (source target : QTraceExpression) :
    (TraceLocalizationInput.intervalStokesLocalizedIso
      source
      target).hom.sourceTraceBookkeepingCount =
      (TraceLocalizationInput.intervalStokes source target).sourceObject.traceBookkeepingCount :=
  TraceLocalizationInput.intervalStokesForwardArrow_sourceTraceBookkeepingCount
    source
    target

/-- Interval-Stokes isomorphism hom target bookkeeping count is the input target count. -/
theorem TraceLocalizationInput.intervalStokesLocalizedIso_hom_targetTraceBookkeepingCount
    (source target : QTraceExpression) :
    (TraceLocalizationInput.intervalStokesLocalizedIso
      source
      target).hom.targetTraceBookkeepingCount =
      (TraceLocalizationInput.intervalStokes source target).targetObject.traceBookkeepingCount :=
  TraceLocalizationInput.intervalStokesForwardArrow_targetTraceBookkeepingCount
    source
    target

/-- Interval-Stokes isomorphism inverse source bookkeeping count is the input target count. -/
theorem TraceLocalizationInput.intervalStokesLocalizedIso_inv_sourceTraceBookkeepingCount
    (source target : QTraceExpression) :
    (TraceLocalizationInput.intervalStokesLocalizedIso
      source
      target).inv.sourceTraceBookkeepingCount =
      (TraceLocalizationInput.intervalStokes source target).targetObject.traceBookkeepingCount :=
  TraceLocalizationInput.intervalStokesInverseArrow_sourceTraceBookkeepingCount
    source
    target

/-- Interval-Stokes isomorphism inverse target bookkeeping count is the input source count. -/
theorem TraceLocalizationInput.intervalStokesLocalizedIso_inv_targetTraceBookkeepingCount
    (source target : QTraceExpression) :
    (TraceLocalizationInput.intervalStokesLocalizedIso
      source
      target).inv.targetTraceBookkeepingCount =
      (TraceLocalizationInput.intervalStokes source target).sourceObject.traceBookkeepingCount :=
  TraceLocalizationInput.intervalStokesInverseArrow_targetTraceBookkeepingCount
    source
    target

/-- Interval-Fubini isomorphism hom source bookkeeping count is the input source count. -/
theorem TraceLocalizationInput.intervalFubiniLocalizedIso_hom_sourceTraceBookkeepingCount
    (source target : QTraceExpression) :
    (TraceLocalizationInput.intervalFubiniLocalizedIso
      source
      target).hom.sourceTraceBookkeepingCount =
      (TraceLocalizationInput.intervalFubini source target).sourceObject.traceBookkeepingCount :=
  TraceLocalizationInput.intervalFubiniForwardArrow_sourceTraceBookkeepingCount
    source
    target

/-- Interval-Fubini isomorphism hom target bookkeeping count is the input target count. -/
theorem TraceLocalizationInput.intervalFubiniLocalizedIso_hom_targetTraceBookkeepingCount
    (source target : QTraceExpression) :
    (TraceLocalizationInput.intervalFubiniLocalizedIso
      source
      target).hom.targetTraceBookkeepingCount =
      (TraceLocalizationInput.intervalFubini source target).targetObject.traceBookkeepingCount :=
  TraceLocalizationInput.intervalFubiniForwardArrow_targetTraceBookkeepingCount
    source
    target

/-- Interval-Fubini isomorphism inverse source bookkeeping count is the input target count. -/
theorem TraceLocalizationInput.intervalFubiniLocalizedIso_inv_sourceTraceBookkeepingCount
    (source target : QTraceExpression) :
    (TraceLocalizationInput.intervalFubiniLocalizedIso
      source
      target).inv.sourceTraceBookkeepingCount =
      (TraceLocalizationInput.intervalFubini source target).targetObject.traceBookkeepingCount :=
  TraceLocalizationInput.intervalFubiniInverseArrow_sourceTraceBookkeepingCount
    source
    target

/-- Interval-Fubini isomorphism inverse target bookkeeping count is the input source count. -/
theorem TraceLocalizationInput.intervalFubiniLocalizedIso_inv_targetTraceBookkeepingCount
    (source target : QTraceExpression) :
    (TraceLocalizationInput.intervalFubiniLocalizedIso
      source
      target).inv.targetTraceBookkeepingCount =
      (TraceLocalizationInput.intervalFubini source target).sourceObject.traceBookkeepingCount :=
  TraceLocalizationInput.intervalFubiniInverseArrow_targetTraceBookkeepingCount
    source
    target

/-- Tate-weight-drop isomorphism hom source bookkeeping count is the input source count. -/
theorem TraceLocalizationInput.tateWeightDropLocalizedIso_hom_sourceTraceBookkeepingCount
    (source target : QTraceExpression) :
    (TraceLocalizationInput.tateWeightDropLocalizedIso
      source
      target).hom.sourceTraceBookkeepingCount =
      (TraceLocalizationInput.tateWeightDrop source target).sourceObject.traceBookkeepingCount :=
  TraceLocalizationInput.tateWeightDropForwardArrow_sourceTraceBookkeepingCount
    source
    target

/-- Tate-weight-drop isomorphism hom target bookkeeping count is the input target count. -/
theorem TraceLocalizationInput.tateWeightDropLocalizedIso_hom_targetTraceBookkeepingCount
    (source target : QTraceExpression) :
    (TraceLocalizationInput.tateWeightDropLocalizedIso
      source
      target).hom.targetTraceBookkeepingCount =
      (TraceLocalizationInput.tateWeightDrop source target).targetObject.traceBookkeepingCount :=
  TraceLocalizationInput.tateWeightDropForwardArrow_targetTraceBookkeepingCount
    source
    target

/-- Tate-weight-drop isomorphism inverse source bookkeeping count is the input target count. -/
theorem TraceLocalizationInput.tateWeightDropLocalizedIso_inv_sourceTraceBookkeepingCount
    (source target : QTraceExpression) :
    (TraceLocalizationInput.tateWeightDropLocalizedIso
      source
      target).inv.sourceTraceBookkeepingCount =
      (TraceLocalizationInput.tateWeightDrop source target).targetObject.traceBookkeepingCount :=
  TraceLocalizationInput.tateWeightDropInverseArrow_sourceTraceBookkeepingCount
    source
    target

/-- Tate-weight-drop isomorphism inverse target bookkeeping count is the input source count. -/
theorem TraceLocalizationInput.tateWeightDropLocalizedIso_inv_targetTraceBookkeepingCount
    (source target : QTraceExpression) :
    (TraceLocalizationInput.tateWeightDropLocalizedIso
      source
      target).inv.targetTraceBookkeepingCount =
      (TraceLocalizationInput.tateWeightDrop source target).sourceObject.traceBookkeepingCount :=
  TraceLocalizationInput.tateWeightDropInverseArrow_targetTraceBookkeepingCount
    source
    target

end AnalyticMotives
end LFunctions
end Boundary
