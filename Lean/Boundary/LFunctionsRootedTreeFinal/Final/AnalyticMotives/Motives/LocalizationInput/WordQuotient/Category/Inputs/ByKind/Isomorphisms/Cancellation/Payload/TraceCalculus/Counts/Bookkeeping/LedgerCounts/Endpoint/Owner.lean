import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.LocalizationInput.WordQuotient.Category.Inputs.Cancellation.Payload.TraceCalculus.LedgerCounts.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.LocalizationInput.WordQuotient.Category.Inputs.ByKind.Isomorphisms.Cancellation.Payload.TraceCalculus.Counts.Bookkeeping.Owner

/-!
# Endpoint ledger-count facts for named cancellation bookkeeping payload

This file specializes endpoint trace-bookkeeping ledger-count facts for the
named localization-input cancellation isomorphisms.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Descent-channel hom-inverse cancellation endpoint bookkeeping is counted by its endpoint ledger. -/
theorem TraceLocalizationInput.descentChannelLocalizedIso_hom_comp_inv_endpointTraceBookkeepingCount_eq_certificateLedger_count
    (source target : QTraceExpression) :
    (TraceLocalizationWordClass.comp
      (TraceLocalizationInput.descentChannelLocalizedIso source target).hom
      (TraceLocalizationInput.descentChannelLocalizedIso source target).inv).endpointTraceBookkeepingCount =
      (TraceLocalizationWordClass.comp
        (TraceLocalizationInput.descentChannelLocalizedIso source target).hom
        (TraceLocalizationInput.descentChannelLocalizedIso source target).inv).endpointCertificateLedger.traceBookkeepingCount :=
  TraceLocalizationInput.localizedIso_hom_comp_inv_endpointTraceBookkeepingCount_eq_certificateLedger_count
    (TraceLocalizationInput.descentChannel source target)

/-- Descent-channel inverse-hom cancellation endpoint bookkeeping is counted by its endpoint ledger. -/
theorem TraceLocalizationInput.descentChannelLocalizedIso_inv_comp_hom_endpointTraceBookkeepingCount_eq_certificateLedger_count
    (source target : QTraceExpression) :
    (TraceLocalizationWordClass.comp
      (TraceLocalizationInput.descentChannelLocalizedIso source target).inv
      (TraceLocalizationInput.descentChannelLocalizedIso source target).hom).endpointTraceBookkeepingCount =
      (TraceLocalizationWordClass.comp
        (TraceLocalizationInput.descentChannelLocalizedIso source target).inv
        (TraceLocalizationInput.descentChannelLocalizedIso source target).hom).endpointCertificateLedger.traceBookkeepingCount :=
  TraceLocalizationInput.localizedIso_inv_comp_hom_endpointTraceBookkeepingCount_eq_certificateLedger_count
    (TraceLocalizationInput.descentChannel source target)

/-- Descent-refinement hom-inverse cancellation endpoint bookkeeping is counted by its endpoint ledger. -/
theorem TraceLocalizationInput.descentRefinementLocalizedIso_hom_comp_inv_endpointTraceBookkeepingCount_eq_certificateLedger_count
    (source target : QTraceExpression) :
    (TraceLocalizationWordClass.comp
      (TraceLocalizationInput.descentRefinementLocalizedIso source target).hom
      (TraceLocalizationInput.descentRefinementLocalizedIso source target).inv).endpointTraceBookkeepingCount =
      (TraceLocalizationWordClass.comp
        (TraceLocalizationInput.descentRefinementLocalizedIso source target).hom
        (TraceLocalizationInput.descentRefinementLocalizedIso source target).inv).endpointCertificateLedger.traceBookkeepingCount :=
  TraceLocalizationInput.localizedIso_hom_comp_inv_endpointTraceBookkeepingCount_eq_certificateLedger_count
    (TraceLocalizationInput.descentRefinement source target)

/-- Descent-refinement inverse-hom cancellation endpoint bookkeeping is counted by its endpoint ledger. -/
theorem TraceLocalizationInput.descentRefinementLocalizedIso_inv_comp_hom_endpointTraceBookkeepingCount_eq_certificateLedger_count
    (source target : QTraceExpression) :
    (TraceLocalizationWordClass.comp
      (TraceLocalizationInput.descentRefinementLocalizedIso source target).inv
      (TraceLocalizationInput.descentRefinementLocalizedIso source target).hom).endpointTraceBookkeepingCount =
      (TraceLocalizationWordClass.comp
        (TraceLocalizationInput.descentRefinementLocalizedIso source target).inv
        (TraceLocalizationInput.descentRefinementLocalizedIso source target).hom).endpointCertificateLedger.traceBookkeepingCount :=
  TraceLocalizationInput.localizedIso_inv_comp_hom_endpointTraceBookkeepingCount_eq_certificateLedger_count
    (TraceLocalizationInput.descentRefinement source target)

/-- Descent-schedule hom-inverse cancellation endpoint bookkeeping is counted by its endpoint ledger. -/
theorem TraceLocalizationInput.descentScheduleLocalizedIso_hom_comp_inv_endpointTraceBookkeepingCount_eq_certificateLedger_count
    (source target : QTraceExpression) :
    (TraceLocalizationWordClass.comp
      (TraceLocalizationInput.descentScheduleLocalizedIso source target).hom
      (TraceLocalizationInput.descentScheduleLocalizedIso source target).inv).endpointTraceBookkeepingCount =
      (TraceLocalizationWordClass.comp
        (TraceLocalizationInput.descentScheduleLocalizedIso source target).hom
        (TraceLocalizationInput.descentScheduleLocalizedIso source target).inv).endpointCertificateLedger.traceBookkeepingCount :=
  TraceLocalizationInput.localizedIso_hom_comp_inv_endpointTraceBookkeepingCount_eq_certificateLedger_count
    (TraceLocalizationInput.descentSchedule source target)

/-- Descent-schedule inverse-hom cancellation endpoint bookkeeping is counted by its endpoint ledger. -/
theorem TraceLocalizationInput.descentScheduleLocalizedIso_inv_comp_hom_endpointTraceBookkeepingCount_eq_certificateLedger_count
    (source target : QTraceExpression) :
    (TraceLocalizationWordClass.comp
      (TraceLocalizationInput.descentScheduleLocalizedIso source target).inv
      (TraceLocalizationInput.descentScheduleLocalizedIso source target).hom).endpointTraceBookkeepingCount =
      (TraceLocalizationWordClass.comp
        (TraceLocalizationInput.descentScheduleLocalizedIso source target).inv
        (TraceLocalizationInput.descentScheduleLocalizedIso source target).hom).endpointCertificateLedger.traceBookkeepingCount :=
  TraceLocalizationInput.localizedIso_inv_comp_hom_endpointTraceBookkeepingCount_eq_certificateLedger_count
    (TraceLocalizationInput.descentSchedule source target)

/-- Interval-Stokes hom-inverse cancellation endpoint bookkeeping is counted by its endpoint ledger. -/
theorem TraceLocalizationInput.intervalStokesLocalizedIso_hom_comp_inv_endpointTraceBookkeepingCount_eq_certificateLedger_count
    (source target : QTraceExpression) :
    (TraceLocalizationWordClass.comp
      (TraceLocalizationInput.intervalStokesLocalizedIso source target).hom
      (TraceLocalizationInput.intervalStokesLocalizedIso source target).inv).endpointTraceBookkeepingCount =
      (TraceLocalizationWordClass.comp
        (TraceLocalizationInput.intervalStokesLocalizedIso source target).hom
        (TraceLocalizationInput.intervalStokesLocalizedIso source target).inv).endpointCertificateLedger.traceBookkeepingCount :=
  TraceLocalizationInput.localizedIso_hom_comp_inv_endpointTraceBookkeepingCount_eq_certificateLedger_count
    (TraceLocalizationInput.intervalStokes source target)

/-- Interval-Stokes inverse-hom cancellation endpoint bookkeeping is counted by its endpoint ledger. -/
theorem TraceLocalizationInput.intervalStokesLocalizedIso_inv_comp_hom_endpointTraceBookkeepingCount_eq_certificateLedger_count
    (source target : QTraceExpression) :
    (TraceLocalizationWordClass.comp
      (TraceLocalizationInput.intervalStokesLocalizedIso source target).inv
      (TraceLocalizationInput.intervalStokesLocalizedIso source target).hom).endpointTraceBookkeepingCount =
      (TraceLocalizationWordClass.comp
        (TraceLocalizationInput.intervalStokesLocalizedIso source target).inv
        (TraceLocalizationInput.intervalStokesLocalizedIso source target).hom).endpointCertificateLedger.traceBookkeepingCount :=
  TraceLocalizationInput.localizedIso_inv_comp_hom_endpointTraceBookkeepingCount_eq_certificateLedger_count
    (TraceLocalizationInput.intervalStokes source target)

/-- Interval-Fubini hom-inverse cancellation endpoint bookkeeping is counted by its endpoint ledger. -/
theorem TraceLocalizationInput.intervalFubiniLocalizedIso_hom_comp_inv_endpointTraceBookkeepingCount_eq_certificateLedger_count
    (source target : QTraceExpression) :
    (TraceLocalizationWordClass.comp
      (TraceLocalizationInput.intervalFubiniLocalizedIso source target).hom
      (TraceLocalizationInput.intervalFubiniLocalizedIso source target).inv).endpointTraceBookkeepingCount =
      (TraceLocalizationWordClass.comp
        (TraceLocalizationInput.intervalFubiniLocalizedIso source target).hom
        (TraceLocalizationInput.intervalFubiniLocalizedIso source target).inv).endpointCertificateLedger.traceBookkeepingCount :=
  TraceLocalizationInput.localizedIso_hom_comp_inv_endpointTraceBookkeepingCount_eq_certificateLedger_count
    (TraceLocalizationInput.intervalFubini source target)

/-- Interval-Fubini inverse-hom cancellation endpoint bookkeeping is counted by its endpoint ledger. -/
theorem TraceLocalizationInput.intervalFubiniLocalizedIso_inv_comp_hom_endpointTraceBookkeepingCount_eq_certificateLedger_count
    (source target : QTraceExpression) :
    (TraceLocalizationWordClass.comp
      (TraceLocalizationInput.intervalFubiniLocalizedIso source target).inv
      (TraceLocalizationInput.intervalFubiniLocalizedIso source target).hom).endpointTraceBookkeepingCount =
      (TraceLocalizationWordClass.comp
        (TraceLocalizationInput.intervalFubiniLocalizedIso source target).inv
        (TraceLocalizationInput.intervalFubiniLocalizedIso source target).hom).endpointCertificateLedger.traceBookkeepingCount :=
  TraceLocalizationInput.localizedIso_inv_comp_hom_endpointTraceBookkeepingCount_eq_certificateLedger_count
    (TraceLocalizationInput.intervalFubini source target)

/-- Tate-weight-drop hom-inverse cancellation endpoint bookkeeping is counted by its endpoint ledger. -/
theorem TraceLocalizationInput.tateWeightDropLocalizedIso_hom_comp_inv_endpointTraceBookkeepingCount_eq_certificateLedger_count
    (source target : QTraceExpression) :
    (TraceLocalizationWordClass.comp
      (TraceLocalizationInput.tateWeightDropLocalizedIso source target).hom
      (TraceLocalizationInput.tateWeightDropLocalizedIso source target).inv).endpointTraceBookkeepingCount =
      (TraceLocalizationWordClass.comp
        (TraceLocalizationInput.tateWeightDropLocalizedIso source target).hom
        (TraceLocalizationInput.tateWeightDropLocalizedIso source target).inv).endpointCertificateLedger.traceBookkeepingCount :=
  TraceLocalizationInput.localizedIso_hom_comp_inv_endpointTraceBookkeepingCount_eq_certificateLedger_count
    (TraceLocalizationInput.tateWeightDrop source target)

/-- Tate-weight-drop inverse-hom cancellation endpoint bookkeeping is counted by its endpoint ledger. -/
theorem TraceLocalizationInput.tateWeightDropLocalizedIso_inv_comp_hom_endpointTraceBookkeepingCount_eq_certificateLedger_count
    (source target : QTraceExpression) :
    (TraceLocalizationWordClass.comp
      (TraceLocalizationInput.tateWeightDropLocalizedIso source target).inv
      (TraceLocalizationInput.tateWeightDropLocalizedIso source target).hom).endpointTraceBookkeepingCount =
      (TraceLocalizationWordClass.comp
        (TraceLocalizationInput.tateWeightDropLocalizedIso source target).inv
        (TraceLocalizationInput.tateWeightDropLocalizedIso source target).hom).endpointCertificateLedger.traceBookkeepingCount :=
  TraceLocalizationInput.localizedIso_inv_comp_hom_endpointTraceBookkeepingCount_eq_certificateLedger_count
    (TraceLocalizationInput.tateWeightDrop source target)

end AnalyticMotives
end LFunctions
end Boundary
