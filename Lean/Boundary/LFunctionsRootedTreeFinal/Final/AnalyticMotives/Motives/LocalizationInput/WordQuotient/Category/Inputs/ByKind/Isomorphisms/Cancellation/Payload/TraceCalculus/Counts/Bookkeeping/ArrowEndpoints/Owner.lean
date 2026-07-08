import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.LocalizationInput.WordQuotient.Category.Inputs.Cancellation.Payload.TraceCalculus.Owner

/-!
# Endpoint bookkeeping counts for named cancellation composites

This file specializes the generic input-cancellation source and target
trace-bookkeeping count facts to the six named localization-input constructors.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Descent-channel hom-inverse cancellation source bookkeeping is the source endpoint bookkeeping. -/
theorem TraceLocalizationInput.descentChannelLocalizedIso_hom_comp_inv_sourceTraceBookkeepingCount
    (source target : QTraceExpression) :
    (TraceLocalizationInput.descentChannel source target).localizedIsoHomInv.sourceTraceBookkeepingCount =
      (TraceLocalizationInput.descentChannel source target).localizedSourceObject.traceBookkeepingCount :=
  TraceLocalizationInput.localizedIso_hom_comp_inv_sourceTraceBookkeepingCount
    (TraceLocalizationInput.descentChannel source target)

/-- Descent-channel hom-inverse cancellation target bookkeeping is the source endpoint bookkeeping. -/
theorem TraceLocalizationInput.descentChannelLocalizedIso_hom_comp_inv_targetTraceBookkeepingCount
    (source target : QTraceExpression) :
    (TraceLocalizationInput.descentChannel source target).localizedIsoHomInv.targetTraceBookkeepingCount =
      (TraceLocalizationInput.descentChannel source target).localizedSourceObject.traceBookkeepingCount :=
  TraceLocalizationInput.localizedIso_hom_comp_inv_targetTraceBookkeepingCount
    (TraceLocalizationInput.descentChannel source target)

/-- Descent-channel inverse-hom cancellation source bookkeeping is the target endpoint bookkeeping. -/
theorem TraceLocalizationInput.descentChannelLocalizedIso_inv_comp_hom_sourceTraceBookkeepingCount
    (source target : QTraceExpression) :
    (TraceLocalizationInput.descentChannel source target).localizedIsoInvHom.sourceTraceBookkeepingCount =
      (TraceLocalizationInput.descentChannel source target).localizedTargetObject.traceBookkeepingCount :=
  TraceLocalizationInput.localizedIso_inv_comp_hom_sourceTraceBookkeepingCount
    (TraceLocalizationInput.descentChannel source target)

/-- Descent-channel inverse-hom cancellation target bookkeeping is the target endpoint bookkeeping. -/
theorem TraceLocalizationInput.descentChannelLocalizedIso_inv_comp_hom_targetTraceBookkeepingCount
    (source target : QTraceExpression) :
    (TraceLocalizationInput.descentChannel source target).localizedIsoInvHom.targetTraceBookkeepingCount =
      (TraceLocalizationInput.descentChannel source target).localizedTargetObject.traceBookkeepingCount :=
  TraceLocalizationInput.localizedIso_inv_comp_hom_targetTraceBookkeepingCount
    (TraceLocalizationInput.descentChannel source target)

/-- Descent-refinement hom-inverse cancellation source bookkeeping is the source endpoint bookkeeping. -/
theorem TraceLocalizationInput.descentRefinementLocalizedIso_hom_comp_inv_sourceTraceBookkeepingCount
    (source target : QTraceExpression) :
    (TraceLocalizationInput.descentRefinement source target).localizedIsoHomInv.sourceTraceBookkeepingCount =
      (TraceLocalizationInput.descentRefinement source target).localizedSourceObject.traceBookkeepingCount :=
  TraceLocalizationInput.localizedIso_hom_comp_inv_sourceTraceBookkeepingCount
    (TraceLocalizationInput.descentRefinement source target)

/-- Descent-refinement hom-inverse cancellation target bookkeeping is the source endpoint bookkeeping. -/
theorem TraceLocalizationInput.descentRefinementLocalizedIso_hom_comp_inv_targetTraceBookkeepingCount
    (source target : QTraceExpression) :
    (TraceLocalizationInput.descentRefinement source target).localizedIsoHomInv.targetTraceBookkeepingCount =
      (TraceLocalizationInput.descentRefinement source target).localizedSourceObject.traceBookkeepingCount :=
  TraceLocalizationInput.localizedIso_hom_comp_inv_targetTraceBookkeepingCount
    (TraceLocalizationInput.descentRefinement source target)

/-- Descent-refinement inverse-hom cancellation source bookkeeping is the target endpoint bookkeeping. -/
theorem TraceLocalizationInput.descentRefinementLocalizedIso_inv_comp_hom_sourceTraceBookkeepingCount
    (source target : QTraceExpression) :
    (TraceLocalizationInput.descentRefinement source target).localizedIsoInvHom.sourceTraceBookkeepingCount =
      (TraceLocalizationInput.descentRefinement source target).localizedTargetObject.traceBookkeepingCount :=
  TraceLocalizationInput.localizedIso_inv_comp_hom_sourceTraceBookkeepingCount
    (TraceLocalizationInput.descentRefinement source target)

/-- Descent-refinement inverse-hom cancellation target bookkeeping is the target endpoint bookkeeping. -/
theorem TraceLocalizationInput.descentRefinementLocalizedIso_inv_comp_hom_targetTraceBookkeepingCount
    (source target : QTraceExpression) :
    (TraceLocalizationInput.descentRefinement source target).localizedIsoInvHom.targetTraceBookkeepingCount =
      (TraceLocalizationInput.descentRefinement source target).localizedTargetObject.traceBookkeepingCount :=
  TraceLocalizationInput.localizedIso_inv_comp_hom_targetTraceBookkeepingCount
    (TraceLocalizationInput.descentRefinement source target)

/-- Descent-schedule hom-inverse cancellation source bookkeeping is the source endpoint bookkeeping. -/
theorem TraceLocalizationInput.descentScheduleLocalizedIso_hom_comp_inv_sourceTraceBookkeepingCount
    (source target : QTraceExpression) :
    (TraceLocalizationInput.descentSchedule source target).localizedIsoHomInv.sourceTraceBookkeepingCount =
      (TraceLocalizationInput.descentSchedule source target).localizedSourceObject.traceBookkeepingCount :=
  TraceLocalizationInput.localizedIso_hom_comp_inv_sourceTraceBookkeepingCount
    (TraceLocalizationInput.descentSchedule source target)

/-- Descent-schedule hom-inverse cancellation target bookkeeping is the source endpoint bookkeeping. -/
theorem TraceLocalizationInput.descentScheduleLocalizedIso_hom_comp_inv_targetTraceBookkeepingCount
    (source target : QTraceExpression) :
    (TraceLocalizationInput.descentSchedule source target).localizedIsoHomInv.targetTraceBookkeepingCount =
      (TraceLocalizationInput.descentSchedule source target).localizedSourceObject.traceBookkeepingCount :=
  TraceLocalizationInput.localizedIso_hom_comp_inv_targetTraceBookkeepingCount
    (TraceLocalizationInput.descentSchedule source target)

/-- Descent-schedule inverse-hom cancellation source bookkeeping is the target endpoint bookkeeping. -/
theorem TraceLocalizationInput.descentScheduleLocalizedIso_inv_comp_hom_sourceTraceBookkeepingCount
    (source target : QTraceExpression) :
    (TraceLocalizationInput.descentSchedule source target).localizedIsoInvHom.sourceTraceBookkeepingCount =
      (TraceLocalizationInput.descentSchedule source target).localizedTargetObject.traceBookkeepingCount :=
  TraceLocalizationInput.localizedIso_inv_comp_hom_sourceTraceBookkeepingCount
    (TraceLocalizationInput.descentSchedule source target)

/-- Descent-schedule inverse-hom cancellation target bookkeeping is the target endpoint bookkeeping. -/
theorem TraceLocalizationInput.descentScheduleLocalizedIso_inv_comp_hom_targetTraceBookkeepingCount
    (source target : QTraceExpression) :
    (TraceLocalizationInput.descentSchedule source target).localizedIsoInvHom.targetTraceBookkeepingCount =
      (TraceLocalizationInput.descentSchedule source target).localizedTargetObject.traceBookkeepingCount :=
  TraceLocalizationInput.localizedIso_inv_comp_hom_targetTraceBookkeepingCount
    (TraceLocalizationInput.descentSchedule source target)

/-- Interval-Stokes hom-inverse cancellation source bookkeeping is the source endpoint bookkeeping. -/
theorem TraceLocalizationInput.intervalStokesLocalizedIso_hom_comp_inv_sourceTraceBookkeepingCount
    (source target : QTraceExpression) :
    (TraceLocalizationInput.intervalStokes source target).localizedIsoHomInv.sourceTraceBookkeepingCount =
      (TraceLocalizationInput.intervalStokes source target).localizedSourceObject.traceBookkeepingCount :=
  TraceLocalizationInput.localizedIso_hom_comp_inv_sourceTraceBookkeepingCount
    (TraceLocalizationInput.intervalStokes source target)

/-- Interval-Stokes hom-inverse cancellation target bookkeeping is the source endpoint bookkeeping. -/
theorem TraceLocalizationInput.intervalStokesLocalizedIso_hom_comp_inv_targetTraceBookkeepingCount
    (source target : QTraceExpression) :
    (TraceLocalizationInput.intervalStokes source target).localizedIsoHomInv.targetTraceBookkeepingCount =
      (TraceLocalizationInput.intervalStokes source target).localizedSourceObject.traceBookkeepingCount :=
  TraceLocalizationInput.localizedIso_hom_comp_inv_targetTraceBookkeepingCount
    (TraceLocalizationInput.intervalStokes source target)

/-- Interval-Stokes inverse-hom cancellation source bookkeeping is the target endpoint bookkeeping. -/
theorem TraceLocalizationInput.intervalStokesLocalizedIso_inv_comp_hom_sourceTraceBookkeepingCount
    (source target : QTraceExpression) :
    (TraceLocalizationInput.intervalStokes source target).localizedIsoInvHom.sourceTraceBookkeepingCount =
      (TraceLocalizationInput.intervalStokes source target).localizedTargetObject.traceBookkeepingCount :=
  TraceLocalizationInput.localizedIso_inv_comp_hom_sourceTraceBookkeepingCount
    (TraceLocalizationInput.intervalStokes source target)

/-- Interval-Stokes inverse-hom cancellation target bookkeeping is the target endpoint bookkeeping. -/
theorem TraceLocalizationInput.intervalStokesLocalizedIso_inv_comp_hom_targetTraceBookkeepingCount
    (source target : QTraceExpression) :
    (TraceLocalizationInput.intervalStokes source target).localizedIsoInvHom.targetTraceBookkeepingCount =
      (TraceLocalizationInput.intervalStokes source target).localizedTargetObject.traceBookkeepingCount :=
  TraceLocalizationInput.localizedIso_inv_comp_hom_targetTraceBookkeepingCount
    (TraceLocalizationInput.intervalStokes source target)

/-- Interval-Fubini hom-inverse cancellation source bookkeeping is the source endpoint bookkeeping. -/
theorem TraceLocalizationInput.intervalFubiniLocalizedIso_hom_comp_inv_sourceTraceBookkeepingCount
    (source target : QTraceExpression) :
    (TraceLocalizationInput.intervalFubini source target).localizedIsoHomInv.sourceTraceBookkeepingCount =
      (TraceLocalizationInput.intervalFubini source target).localizedSourceObject.traceBookkeepingCount :=
  TraceLocalizationInput.localizedIso_hom_comp_inv_sourceTraceBookkeepingCount
    (TraceLocalizationInput.intervalFubini source target)

/-- Interval-Fubini hom-inverse cancellation target bookkeeping is the source endpoint bookkeeping. -/
theorem TraceLocalizationInput.intervalFubiniLocalizedIso_hom_comp_inv_targetTraceBookkeepingCount
    (source target : QTraceExpression) :
    (TraceLocalizationInput.intervalFubini source target).localizedIsoHomInv.targetTraceBookkeepingCount =
      (TraceLocalizationInput.intervalFubini source target).localizedSourceObject.traceBookkeepingCount :=
  TraceLocalizationInput.localizedIso_hom_comp_inv_targetTraceBookkeepingCount
    (TraceLocalizationInput.intervalFubini source target)

/-- Interval-Fubini inverse-hom cancellation source bookkeeping is the target endpoint bookkeeping. -/
theorem TraceLocalizationInput.intervalFubiniLocalizedIso_inv_comp_hom_sourceTraceBookkeepingCount
    (source target : QTraceExpression) :
    (TraceLocalizationInput.intervalFubini source target).localizedIsoInvHom.sourceTraceBookkeepingCount =
      (TraceLocalizationInput.intervalFubini source target).localizedTargetObject.traceBookkeepingCount :=
  TraceLocalizationInput.localizedIso_inv_comp_hom_sourceTraceBookkeepingCount
    (TraceLocalizationInput.intervalFubini source target)

/-- Interval-Fubini inverse-hom cancellation target bookkeeping is the target endpoint bookkeeping. -/
theorem TraceLocalizationInput.intervalFubiniLocalizedIso_inv_comp_hom_targetTraceBookkeepingCount
    (source target : QTraceExpression) :
    (TraceLocalizationInput.intervalFubini source target).localizedIsoInvHom.targetTraceBookkeepingCount =
      (TraceLocalizationInput.intervalFubini source target).localizedTargetObject.traceBookkeepingCount :=
  TraceLocalizationInput.localizedIso_inv_comp_hom_targetTraceBookkeepingCount
    (TraceLocalizationInput.intervalFubini source target)

/-- Tate-weight-drop hom-inverse cancellation source bookkeeping is the source endpoint bookkeeping. -/
theorem TraceLocalizationInput.tateWeightDropLocalizedIso_hom_comp_inv_sourceTraceBookkeepingCount
    (source target : QTraceExpression) :
    (TraceLocalizationInput.tateWeightDrop source target).localizedIsoHomInv.sourceTraceBookkeepingCount =
      (TraceLocalizationInput.tateWeightDrop source target).localizedSourceObject.traceBookkeepingCount :=
  TraceLocalizationInput.localizedIso_hom_comp_inv_sourceTraceBookkeepingCount
    (TraceLocalizationInput.tateWeightDrop source target)

/-- Tate-weight-drop hom-inverse cancellation target bookkeeping is the source endpoint bookkeeping. -/
theorem TraceLocalizationInput.tateWeightDropLocalizedIso_hom_comp_inv_targetTraceBookkeepingCount
    (source target : QTraceExpression) :
    (TraceLocalizationInput.tateWeightDrop source target).localizedIsoHomInv.targetTraceBookkeepingCount =
      (TraceLocalizationInput.tateWeightDrop source target).localizedSourceObject.traceBookkeepingCount :=
  TraceLocalizationInput.localizedIso_hom_comp_inv_targetTraceBookkeepingCount
    (TraceLocalizationInput.tateWeightDrop source target)

/-- Tate-weight-drop inverse-hom cancellation source bookkeeping is the target endpoint bookkeeping. -/
theorem TraceLocalizationInput.tateWeightDropLocalizedIso_inv_comp_hom_sourceTraceBookkeepingCount
    (source target : QTraceExpression) :
    (TraceLocalizationInput.tateWeightDrop source target).localizedIsoInvHom.sourceTraceBookkeepingCount =
      (TraceLocalizationInput.tateWeightDrop source target).localizedTargetObject.traceBookkeepingCount :=
  TraceLocalizationInput.localizedIso_inv_comp_hom_sourceTraceBookkeepingCount
    (TraceLocalizationInput.tateWeightDrop source target)

/-- Tate-weight-drop inverse-hom cancellation target bookkeeping is the target endpoint bookkeeping. -/
theorem TraceLocalizationInput.tateWeightDropLocalizedIso_inv_comp_hom_targetTraceBookkeepingCount
    (source target : QTraceExpression) :
    (TraceLocalizationInput.tateWeightDrop source target).localizedIsoInvHom.targetTraceBookkeepingCount =
      (TraceLocalizationInput.tateWeightDrop source target).localizedTargetObject.traceBookkeepingCount :=
  TraceLocalizationInput.localizedIso_inv_comp_hom_targetTraceBookkeepingCount
    (TraceLocalizationInput.tateWeightDrop source target)

end AnalyticMotives
end LFunctions
end Boundary
