import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.LocalizationInput.WordQuotient.Category.Inputs.ByKind.Isomorphisms.Payload.TraceCalculus.Counts.Bookkeeping.ArrowEndpoints.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.LocalizationInput.WordQuotient.Category.InvertedInputs.Payload.TraceCalculus.Owner

/-!
# Trace-bookkeeping counts for named localized isomorphisms

This file exposes concatenated endpoint trace-bookkeeping counts through the
hom and inverse arrows of the named by-kind localized isomorphisms.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Descent-channel isomorphism hom endpoint bookkeeping is source plus target bookkeeping. -/
theorem TraceLocalizationInput.descentChannelLocalizedIso_hom_endpointTraceBookkeepingCount
    (source target : QTraceExpression) :
    (TraceLocalizationInput.descentChannelLocalizedIso source target).hom.endpointTraceBookkeepingCount =
      (TraceLocalizationInput.descentChannel source target).sourceObject.traceBookkeepingCount +
        (TraceLocalizationInput.descentChannel source target).targetObject.traceBookkeepingCount :=
  TraceLocalizationInput.localizedWordIso_hom_endpointTraceBookkeepingCount
    (TraceLocalizationInput.descentChannel source target)

/-- Descent-channel isomorphism inverse endpoint bookkeeping is target plus source bookkeeping. -/
theorem TraceLocalizationInput.descentChannelLocalizedIso_inv_endpointTraceBookkeepingCount
    (source target : QTraceExpression) :
    (TraceLocalizationInput.descentChannelLocalizedIso source target).inv.endpointTraceBookkeepingCount =
      (TraceLocalizationInput.descentChannel source target).targetObject.traceBookkeepingCount +
        (TraceLocalizationInput.descentChannel source target).sourceObject.traceBookkeepingCount :=
  TraceLocalizationInput.localizedWordIso_inv_endpointTraceBookkeepingCount
    (TraceLocalizationInput.descentChannel source target)

/-- Descent-refinement isomorphism hom endpoint bookkeeping is source plus target bookkeeping. -/
theorem TraceLocalizationInput.descentRefinementLocalizedIso_hom_endpointTraceBookkeepingCount
    (source target : QTraceExpression) :
    (TraceLocalizationInput.descentRefinementLocalizedIso source target).hom.endpointTraceBookkeepingCount =
      (TraceLocalizationInput.descentRefinement source target).sourceObject.traceBookkeepingCount +
        (TraceLocalizationInput.descentRefinement source target).targetObject.traceBookkeepingCount :=
  TraceLocalizationInput.localizedWordIso_hom_endpointTraceBookkeepingCount
    (TraceLocalizationInput.descentRefinement source target)

/-- Descent-refinement isomorphism inverse endpoint bookkeeping is target plus source bookkeeping. -/
theorem TraceLocalizationInput.descentRefinementLocalizedIso_inv_endpointTraceBookkeepingCount
    (source target : QTraceExpression) :
    (TraceLocalizationInput.descentRefinementLocalizedIso source target).inv.endpointTraceBookkeepingCount =
      (TraceLocalizationInput.descentRefinement source target).targetObject.traceBookkeepingCount +
        (TraceLocalizationInput.descentRefinement source target).sourceObject.traceBookkeepingCount :=
  TraceLocalizationInput.localizedWordIso_inv_endpointTraceBookkeepingCount
    (TraceLocalizationInput.descentRefinement source target)

/-- Descent-schedule isomorphism hom endpoint bookkeeping is source plus target bookkeeping. -/
theorem TraceLocalizationInput.descentScheduleLocalizedIso_hom_endpointTraceBookkeepingCount
    (source target : QTraceExpression) :
    (TraceLocalizationInput.descentScheduleLocalizedIso source target).hom.endpointTraceBookkeepingCount =
      (TraceLocalizationInput.descentSchedule source target).sourceObject.traceBookkeepingCount +
        (TraceLocalizationInput.descentSchedule source target).targetObject.traceBookkeepingCount :=
  TraceLocalizationInput.localizedWordIso_hom_endpointTraceBookkeepingCount
    (TraceLocalizationInput.descentSchedule source target)

/-- Descent-schedule isomorphism inverse endpoint bookkeeping is target plus source bookkeeping. -/
theorem TraceLocalizationInput.descentScheduleLocalizedIso_inv_endpointTraceBookkeepingCount
    (source target : QTraceExpression) :
    (TraceLocalizationInput.descentScheduleLocalizedIso source target).inv.endpointTraceBookkeepingCount =
      (TraceLocalizationInput.descentSchedule source target).targetObject.traceBookkeepingCount +
        (TraceLocalizationInput.descentSchedule source target).sourceObject.traceBookkeepingCount :=
  TraceLocalizationInput.localizedWordIso_inv_endpointTraceBookkeepingCount
    (TraceLocalizationInput.descentSchedule source target)

/-- Interval-Stokes isomorphism hom endpoint bookkeeping is source plus target bookkeeping. -/
theorem TraceLocalizationInput.intervalStokesLocalizedIso_hom_endpointTraceBookkeepingCount
    (source target : QTraceExpression) :
    (TraceLocalizationInput.intervalStokesLocalizedIso source target).hom.endpointTraceBookkeepingCount =
      (TraceLocalizationInput.intervalStokes source target).sourceObject.traceBookkeepingCount +
        (TraceLocalizationInput.intervalStokes source target).targetObject.traceBookkeepingCount :=
  TraceLocalizationInput.localizedWordIso_hom_endpointTraceBookkeepingCount
    (TraceLocalizationInput.intervalStokes source target)

/-- Interval-Stokes isomorphism inverse endpoint bookkeeping is target plus source bookkeeping. -/
theorem TraceLocalizationInput.intervalStokesLocalizedIso_inv_endpointTraceBookkeepingCount
    (source target : QTraceExpression) :
    (TraceLocalizationInput.intervalStokesLocalizedIso source target).inv.endpointTraceBookkeepingCount =
      (TraceLocalizationInput.intervalStokes source target).targetObject.traceBookkeepingCount +
        (TraceLocalizationInput.intervalStokes source target).sourceObject.traceBookkeepingCount :=
  TraceLocalizationInput.localizedWordIso_inv_endpointTraceBookkeepingCount
    (TraceLocalizationInput.intervalStokes source target)

/-- Interval-Fubini isomorphism hom endpoint bookkeeping is source plus target bookkeeping. -/
theorem TraceLocalizationInput.intervalFubiniLocalizedIso_hom_endpointTraceBookkeepingCount
    (source target : QTraceExpression) :
    (TraceLocalizationInput.intervalFubiniLocalizedIso source target).hom.endpointTraceBookkeepingCount =
      (TraceLocalizationInput.intervalFubini source target).sourceObject.traceBookkeepingCount +
        (TraceLocalizationInput.intervalFubini source target).targetObject.traceBookkeepingCount :=
  TraceLocalizationInput.localizedWordIso_hom_endpointTraceBookkeepingCount
    (TraceLocalizationInput.intervalFubini source target)

/-- Interval-Fubini isomorphism inverse endpoint bookkeeping is target plus source bookkeeping. -/
theorem TraceLocalizationInput.intervalFubiniLocalizedIso_inv_endpointTraceBookkeepingCount
    (source target : QTraceExpression) :
    (TraceLocalizationInput.intervalFubiniLocalizedIso source target).inv.endpointTraceBookkeepingCount =
      (TraceLocalizationInput.intervalFubini source target).targetObject.traceBookkeepingCount +
        (TraceLocalizationInput.intervalFubini source target).sourceObject.traceBookkeepingCount :=
  TraceLocalizationInput.localizedWordIso_inv_endpointTraceBookkeepingCount
    (TraceLocalizationInput.intervalFubini source target)

/-- Tate-weight-drop isomorphism hom endpoint bookkeeping is source plus target bookkeeping. -/
theorem TraceLocalizationInput.tateWeightDropLocalizedIso_hom_endpointTraceBookkeepingCount
    (source target : QTraceExpression) :
    (TraceLocalizationInput.tateWeightDropLocalizedIso source target).hom.endpointTraceBookkeepingCount =
      (TraceLocalizationInput.tateWeightDrop source target).sourceObject.traceBookkeepingCount +
        (TraceLocalizationInput.tateWeightDrop source target).targetObject.traceBookkeepingCount :=
  TraceLocalizationInput.localizedWordIso_hom_endpointTraceBookkeepingCount
    (TraceLocalizationInput.tateWeightDrop source target)

/-- Tate-weight-drop isomorphism inverse endpoint bookkeeping is target plus source bookkeeping. -/
theorem TraceLocalizationInput.tateWeightDropLocalizedIso_inv_endpointTraceBookkeepingCount
    (source target : QTraceExpression) :
    (TraceLocalizationInput.tateWeightDropLocalizedIso source target).inv.endpointTraceBookkeepingCount =
      (TraceLocalizationInput.tateWeightDrop source target).targetObject.traceBookkeepingCount +
        (TraceLocalizationInput.tateWeightDrop source target).sourceObject.traceBookkeepingCount :=
  TraceLocalizationInput.localizedWordIso_inv_endpointTraceBookkeepingCount
    (TraceLocalizationInput.tateWeightDrop source target)

end AnalyticMotives
end LFunctions
end Boundary
