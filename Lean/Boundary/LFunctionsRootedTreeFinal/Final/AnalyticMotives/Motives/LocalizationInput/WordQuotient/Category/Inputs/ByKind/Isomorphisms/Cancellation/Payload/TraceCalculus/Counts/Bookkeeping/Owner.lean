import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.LocalizationInput.WordQuotient.Category.Inputs.ByKind.Isomorphisms.Cancellation.Payload.TraceCalculus.Counts.Bookkeeping.ArrowEndpoints.Owner

/-!
# Endpoint bookkeeping counts for named cancellation composites

This file specializes the generic input-cancellation endpoint trace-bookkeeping
count facts to the six named localization-input constructors.  Source and
target endpoint count facts live in the `ArrowEndpoints` child.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Descent-channel hom-inverse cancellation endpoint bookkeeping is doubled source bookkeeping. -/
theorem TraceLocalizationInput.descentChannelLocalizedIso_hom_comp_inv_endpointTraceBookkeepingCount
    (source target : QTraceExpression) :
    (TraceLocalizationWordClass.comp
      (TraceLocalizationInput.descentChannelLocalizedIso source target).hom
      (TraceLocalizationInput.descentChannelLocalizedIso source target).inv).endpointTraceBookkeepingCount =
      (TraceLocalizationInput.descentChannel source target).localizedSourceObject.traceBookkeepingCount +
        (TraceLocalizationInput.descentChannel source target).localizedSourceObject.traceBookkeepingCount :=
  TraceLocalizationInput.localizedIso_hom_comp_inv_endpointTraceBookkeepingCount
    (TraceLocalizationInput.descentChannel source target)

/-- Descent-channel inverse-hom cancellation endpoint bookkeeping is doubled target bookkeeping. -/
theorem TraceLocalizationInput.descentChannelLocalizedIso_inv_comp_hom_endpointTraceBookkeepingCount
    (source target : QTraceExpression) :
    (TraceLocalizationWordClass.comp
      (TraceLocalizationInput.descentChannelLocalizedIso source target).inv
      (TraceLocalizationInput.descentChannelLocalizedIso source target).hom).endpointTraceBookkeepingCount =
      (TraceLocalizationInput.descentChannel source target).localizedTargetObject.traceBookkeepingCount +
        (TraceLocalizationInput.descentChannel source target).localizedTargetObject.traceBookkeepingCount :=
  TraceLocalizationInput.localizedIso_inv_comp_hom_endpointTraceBookkeepingCount
    (TraceLocalizationInput.descentChannel source target)

/-- Descent-refinement hom-inverse cancellation endpoint bookkeeping is doubled source bookkeeping. -/
theorem TraceLocalizationInput.descentRefinementLocalizedIso_hom_comp_inv_endpointTraceBookkeepingCount
    (source target : QTraceExpression) :
    (TraceLocalizationWordClass.comp
      (TraceLocalizationInput.descentRefinementLocalizedIso source target).hom
      (TraceLocalizationInput.descentRefinementLocalizedIso source target).inv).endpointTraceBookkeepingCount =
      (TraceLocalizationInput.descentRefinement source target).localizedSourceObject.traceBookkeepingCount +
        (TraceLocalizationInput.descentRefinement source target).localizedSourceObject.traceBookkeepingCount :=
  TraceLocalizationInput.localizedIso_hom_comp_inv_endpointTraceBookkeepingCount
    (TraceLocalizationInput.descentRefinement source target)

/-- Descent-refinement inverse-hom cancellation endpoint bookkeeping is doubled target bookkeeping. -/
theorem TraceLocalizationInput.descentRefinementLocalizedIso_inv_comp_hom_endpointTraceBookkeepingCount
    (source target : QTraceExpression) :
    (TraceLocalizationWordClass.comp
      (TraceLocalizationInput.descentRefinementLocalizedIso source target).inv
      (TraceLocalizationInput.descentRefinementLocalizedIso source target).hom).endpointTraceBookkeepingCount =
      (TraceLocalizationInput.descentRefinement source target).localizedTargetObject.traceBookkeepingCount +
        (TraceLocalizationInput.descentRefinement source target).localizedTargetObject.traceBookkeepingCount :=
  TraceLocalizationInput.localizedIso_inv_comp_hom_endpointTraceBookkeepingCount
    (TraceLocalizationInput.descentRefinement source target)

/-- Descent-schedule hom-inverse cancellation endpoint bookkeeping is doubled source bookkeeping. -/
theorem TraceLocalizationInput.descentScheduleLocalizedIso_hom_comp_inv_endpointTraceBookkeepingCount
    (source target : QTraceExpression) :
    (TraceLocalizationWordClass.comp
      (TraceLocalizationInput.descentScheduleLocalizedIso source target).hom
      (TraceLocalizationInput.descentScheduleLocalizedIso source target).inv).endpointTraceBookkeepingCount =
      (TraceLocalizationInput.descentSchedule source target).localizedSourceObject.traceBookkeepingCount +
        (TraceLocalizationInput.descentSchedule source target).localizedSourceObject.traceBookkeepingCount :=
  TraceLocalizationInput.localizedIso_hom_comp_inv_endpointTraceBookkeepingCount
    (TraceLocalizationInput.descentSchedule source target)

/-- Descent-schedule inverse-hom cancellation endpoint bookkeeping is doubled target bookkeeping. -/
theorem TraceLocalizationInput.descentScheduleLocalizedIso_inv_comp_hom_endpointTraceBookkeepingCount
    (source target : QTraceExpression) :
    (TraceLocalizationWordClass.comp
      (TraceLocalizationInput.descentScheduleLocalizedIso source target).inv
      (TraceLocalizationInput.descentScheduleLocalizedIso source target).hom).endpointTraceBookkeepingCount =
      (TraceLocalizationInput.descentSchedule source target).localizedTargetObject.traceBookkeepingCount +
        (TraceLocalizationInput.descentSchedule source target).localizedTargetObject.traceBookkeepingCount :=
  TraceLocalizationInput.localizedIso_inv_comp_hom_endpointTraceBookkeepingCount
    (TraceLocalizationInput.descentSchedule source target)

/-- Interval-Stokes hom-inverse cancellation endpoint bookkeeping is doubled source bookkeeping. -/
theorem TraceLocalizationInput.intervalStokesLocalizedIso_hom_comp_inv_endpointTraceBookkeepingCount
    (source target : QTraceExpression) :
    (TraceLocalizationWordClass.comp
      (TraceLocalizationInput.intervalStokesLocalizedIso source target).hom
      (TraceLocalizationInput.intervalStokesLocalizedIso source target).inv).endpointTraceBookkeepingCount =
      (TraceLocalizationInput.intervalStokes source target).localizedSourceObject.traceBookkeepingCount +
        (TraceLocalizationInput.intervalStokes source target).localizedSourceObject.traceBookkeepingCount :=
  TraceLocalizationInput.localizedIso_hom_comp_inv_endpointTraceBookkeepingCount
    (TraceLocalizationInput.intervalStokes source target)

/-- Interval-Stokes inverse-hom cancellation endpoint bookkeeping is doubled target bookkeeping. -/
theorem TraceLocalizationInput.intervalStokesLocalizedIso_inv_comp_hom_endpointTraceBookkeepingCount
    (source target : QTraceExpression) :
    (TraceLocalizationWordClass.comp
      (TraceLocalizationInput.intervalStokesLocalizedIso source target).inv
      (TraceLocalizationInput.intervalStokesLocalizedIso source target).hom).endpointTraceBookkeepingCount =
      (TraceLocalizationInput.intervalStokes source target).localizedTargetObject.traceBookkeepingCount +
        (TraceLocalizationInput.intervalStokes source target).localizedTargetObject.traceBookkeepingCount :=
  TraceLocalizationInput.localizedIso_inv_comp_hom_endpointTraceBookkeepingCount
    (TraceLocalizationInput.intervalStokes source target)

/-- Interval-Fubini hom-inverse cancellation endpoint bookkeeping is doubled source bookkeeping. -/
theorem TraceLocalizationInput.intervalFubiniLocalizedIso_hom_comp_inv_endpointTraceBookkeepingCount
    (source target : QTraceExpression) :
    (TraceLocalizationWordClass.comp
      (TraceLocalizationInput.intervalFubiniLocalizedIso source target).hom
      (TraceLocalizationInput.intervalFubiniLocalizedIso source target).inv).endpointTraceBookkeepingCount =
      (TraceLocalizationInput.intervalFubini source target).localizedSourceObject.traceBookkeepingCount +
        (TraceLocalizationInput.intervalFubini source target).localizedSourceObject.traceBookkeepingCount :=
  TraceLocalizationInput.localizedIso_hom_comp_inv_endpointTraceBookkeepingCount
    (TraceLocalizationInput.intervalFubini source target)

/-- Interval-Fubini inverse-hom cancellation endpoint bookkeeping is doubled target bookkeeping. -/
theorem TraceLocalizationInput.intervalFubiniLocalizedIso_inv_comp_hom_endpointTraceBookkeepingCount
    (source target : QTraceExpression) :
    (TraceLocalizationWordClass.comp
      (TraceLocalizationInput.intervalFubiniLocalizedIso source target).inv
      (TraceLocalizationInput.intervalFubiniLocalizedIso source target).hom).endpointTraceBookkeepingCount =
      (TraceLocalizationInput.intervalFubini source target).localizedTargetObject.traceBookkeepingCount +
        (TraceLocalizationInput.intervalFubini source target).localizedTargetObject.traceBookkeepingCount :=
  TraceLocalizationInput.localizedIso_inv_comp_hom_endpointTraceBookkeepingCount
    (TraceLocalizationInput.intervalFubini source target)

/-- Tate-weight-drop hom-inverse cancellation endpoint bookkeeping is doubled source bookkeeping. -/
theorem TraceLocalizationInput.tateWeightDropLocalizedIso_hom_comp_inv_endpointTraceBookkeepingCount
    (source target : QTraceExpression) :
    (TraceLocalizationWordClass.comp
      (TraceLocalizationInput.tateWeightDropLocalizedIso source target).hom
      (TraceLocalizationInput.tateWeightDropLocalizedIso source target).inv).endpointTraceBookkeepingCount =
      (TraceLocalizationInput.tateWeightDrop source target).localizedSourceObject.traceBookkeepingCount +
        (TraceLocalizationInput.tateWeightDrop source target).localizedSourceObject.traceBookkeepingCount :=
  TraceLocalizationInput.localizedIso_hom_comp_inv_endpointTraceBookkeepingCount
    (TraceLocalizationInput.tateWeightDrop source target)

/-- Tate-weight-drop inverse-hom cancellation endpoint bookkeeping is doubled target bookkeeping. -/
theorem TraceLocalizationInput.tateWeightDropLocalizedIso_inv_comp_hom_endpointTraceBookkeepingCount
    (source target : QTraceExpression) :
    (TraceLocalizationWordClass.comp
      (TraceLocalizationInput.tateWeightDropLocalizedIso source target).inv
      (TraceLocalizationInput.tateWeightDropLocalizedIso source target).hom).endpointTraceBookkeepingCount =
      (TraceLocalizationInput.tateWeightDrop source target).localizedTargetObject.traceBookkeepingCount +
        (TraceLocalizationInput.tateWeightDrop source target).localizedTargetObject.traceBookkeepingCount :=
  TraceLocalizationInput.localizedIso_inv_comp_hom_endpointTraceBookkeepingCount
    (TraceLocalizationInput.tateWeightDrop source target)

end AnalyticMotives
end LFunctions
end Boundary
