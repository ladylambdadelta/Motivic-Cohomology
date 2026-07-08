import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.LocalizationInput.WordQuotient.Category.Inputs.Cancellation.Payload.TraceCalculus.LedgerCounts.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.LocalizationInput.WordQuotient.Category.Inputs.ByKind.Isomorphisms.Cancellation.Payload.TraceCalculus.Counts.Bookkeeping.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.LocalizationInput.WordQuotient.Category.Inputs.ByKind.Isomorphisms.Cancellation.Payload.TraceCalculus.Counts.Bookkeeping.LedgerCounts.Endpoint.Owner

/-!
# Ledger-count facts for named cancellation bookkeeping payload

This file specializes the generic input-cancellation ledger-count facts for
source and target trace-bookkeeping counts to the six named localization-input
constructors. Endpoint ledger-count facts are owned by the `Endpoint` child.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Descent-channel hom-inverse cancellation source bookkeeping is counted by its source ledger. -/
theorem TraceLocalizationInput.descentChannelLocalizedIso_hom_comp_inv_sourceTraceBookkeepingCount_eq_certificateLedger_count
    (source target : QTraceExpression) :
    (TraceLocalizationWordClass.comp
      (TraceLocalizationInput.descentChannelLocalizedIso source target).hom
      (TraceLocalizationInput.descentChannelLocalizedIso source target).inv).sourceTraceBookkeepingCount =
      (TraceLocalizationWordClass.comp
        (TraceLocalizationInput.descentChannelLocalizedIso source target).hom
        (TraceLocalizationInput.descentChannelLocalizedIso source target).inv).sourceCertificateLedger.traceBookkeepingCount :=
  TraceLocalizationInput.localizedIso_hom_comp_inv_sourceTraceBookkeepingCount_eq_certificateLedger_count
    (TraceLocalizationInput.descentChannel source target)

/-- Descent-channel hom-inverse cancellation target bookkeeping is counted by its target ledger. -/
theorem TraceLocalizationInput.descentChannelLocalizedIso_hom_comp_inv_targetTraceBookkeepingCount_eq_certificateLedger_count
    (source target : QTraceExpression) :
    (TraceLocalizationWordClass.comp
      (TraceLocalizationInput.descentChannelLocalizedIso source target).hom
      (TraceLocalizationInput.descentChannelLocalizedIso source target).inv).targetTraceBookkeepingCount =
      (TraceLocalizationWordClass.comp
        (TraceLocalizationInput.descentChannelLocalizedIso source target).hom
        (TraceLocalizationInput.descentChannelLocalizedIso source target).inv).targetCertificateLedger.traceBookkeepingCount :=
  TraceLocalizationInput.localizedIso_hom_comp_inv_targetTraceBookkeepingCount_eq_certificateLedger_count
    (TraceLocalizationInput.descentChannel source target)

/-- Descent-channel inverse-hom cancellation source bookkeeping is counted by its source ledger. -/
theorem TraceLocalizationInput.descentChannelLocalizedIso_inv_comp_hom_sourceTraceBookkeepingCount_eq_certificateLedger_count
    (source target : QTraceExpression) :
    (TraceLocalizationWordClass.comp
      (TraceLocalizationInput.descentChannelLocalizedIso source target).inv
      (TraceLocalizationInput.descentChannelLocalizedIso source target).hom).sourceTraceBookkeepingCount =
      (TraceLocalizationWordClass.comp
        (TraceLocalizationInput.descentChannelLocalizedIso source target).inv
        (TraceLocalizationInput.descentChannelLocalizedIso source target).hom).sourceCertificateLedger.traceBookkeepingCount :=
  TraceLocalizationInput.localizedIso_inv_comp_hom_sourceTraceBookkeepingCount_eq_certificateLedger_count
    (TraceLocalizationInput.descentChannel source target)

/-- Descent-channel inverse-hom cancellation target bookkeeping is counted by its target ledger. -/
theorem TraceLocalizationInput.descentChannelLocalizedIso_inv_comp_hom_targetTraceBookkeepingCount_eq_certificateLedger_count
    (source target : QTraceExpression) :
    (TraceLocalizationWordClass.comp
      (TraceLocalizationInput.descentChannelLocalizedIso source target).inv
      (TraceLocalizationInput.descentChannelLocalizedIso source target).hom).targetTraceBookkeepingCount =
      (TraceLocalizationWordClass.comp
        (TraceLocalizationInput.descentChannelLocalizedIso source target).inv
        (TraceLocalizationInput.descentChannelLocalizedIso source target).hom).targetCertificateLedger.traceBookkeepingCount :=
  TraceLocalizationInput.localizedIso_inv_comp_hom_targetTraceBookkeepingCount_eq_certificateLedger_count
    (TraceLocalizationInput.descentChannel source target)

/-- Descent-refinement hom-inverse cancellation source bookkeeping is counted by its source ledger. -/
theorem TraceLocalizationInput.descentRefinementLocalizedIso_hom_comp_inv_sourceTraceBookkeepingCount_eq_certificateLedger_count
    (source target : QTraceExpression) :
    (TraceLocalizationWordClass.comp
      (TraceLocalizationInput.descentRefinementLocalizedIso source target).hom
      (TraceLocalizationInput.descentRefinementLocalizedIso source target).inv).sourceTraceBookkeepingCount =
      (TraceLocalizationWordClass.comp
        (TraceLocalizationInput.descentRefinementLocalizedIso source target).hom
        (TraceLocalizationInput.descentRefinementLocalizedIso source target).inv).sourceCertificateLedger.traceBookkeepingCount :=
  TraceLocalizationInput.localizedIso_hom_comp_inv_sourceTraceBookkeepingCount_eq_certificateLedger_count
    (TraceLocalizationInput.descentRefinement source target)

/-- Descent-refinement hom-inverse cancellation target bookkeeping is counted by its target ledger. -/
theorem TraceLocalizationInput.descentRefinementLocalizedIso_hom_comp_inv_targetTraceBookkeepingCount_eq_certificateLedger_count
    (source target : QTraceExpression) :
    (TraceLocalizationWordClass.comp
      (TraceLocalizationInput.descentRefinementLocalizedIso source target).hom
      (TraceLocalizationInput.descentRefinementLocalizedIso source target).inv).targetTraceBookkeepingCount =
      (TraceLocalizationWordClass.comp
        (TraceLocalizationInput.descentRefinementLocalizedIso source target).hom
        (TraceLocalizationInput.descentRefinementLocalizedIso source target).inv).targetCertificateLedger.traceBookkeepingCount :=
  TraceLocalizationInput.localizedIso_hom_comp_inv_targetTraceBookkeepingCount_eq_certificateLedger_count
    (TraceLocalizationInput.descentRefinement source target)

/-- Descent-refinement inverse-hom cancellation source bookkeeping is counted by its source ledger. -/
theorem TraceLocalizationInput.descentRefinementLocalizedIso_inv_comp_hom_sourceTraceBookkeepingCount_eq_certificateLedger_count
    (source target : QTraceExpression) :
    (TraceLocalizationWordClass.comp
      (TraceLocalizationInput.descentRefinementLocalizedIso source target).inv
      (TraceLocalizationInput.descentRefinementLocalizedIso source target).hom).sourceTraceBookkeepingCount =
      (TraceLocalizationWordClass.comp
        (TraceLocalizationInput.descentRefinementLocalizedIso source target).inv
        (TraceLocalizationInput.descentRefinementLocalizedIso source target).hom).sourceCertificateLedger.traceBookkeepingCount :=
  TraceLocalizationInput.localizedIso_inv_comp_hom_sourceTraceBookkeepingCount_eq_certificateLedger_count
    (TraceLocalizationInput.descentRefinement source target)

/-- Descent-refinement inverse-hom cancellation target bookkeeping is counted by its target ledger. -/
theorem TraceLocalizationInput.descentRefinementLocalizedIso_inv_comp_hom_targetTraceBookkeepingCount_eq_certificateLedger_count
    (source target : QTraceExpression) :
    (TraceLocalizationWordClass.comp
      (TraceLocalizationInput.descentRefinementLocalizedIso source target).inv
      (TraceLocalizationInput.descentRefinementLocalizedIso source target).hom).targetTraceBookkeepingCount =
      (TraceLocalizationWordClass.comp
        (TraceLocalizationInput.descentRefinementLocalizedIso source target).inv
        (TraceLocalizationInput.descentRefinementLocalizedIso source target).hom).targetCertificateLedger.traceBookkeepingCount :=
  TraceLocalizationInput.localizedIso_inv_comp_hom_targetTraceBookkeepingCount_eq_certificateLedger_count
    (TraceLocalizationInput.descentRefinement source target)

/-- Descent-schedule hom-inverse cancellation source bookkeeping is counted by its source ledger. -/
theorem TraceLocalizationInput.descentScheduleLocalizedIso_hom_comp_inv_sourceTraceBookkeepingCount_eq_certificateLedger_count
    (source target : QTraceExpression) :
    (TraceLocalizationWordClass.comp
      (TraceLocalizationInput.descentScheduleLocalizedIso source target).hom
      (TraceLocalizationInput.descentScheduleLocalizedIso source target).inv).sourceTraceBookkeepingCount =
      (TraceLocalizationWordClass.comp
        (TraceLocalizationInput.descentScheduleLocalizedIso source target).hom
        (TraceLocalizationInput.descentScheduleLocalizedIso source target).inv).sourceCertificateLedger.traceBookkeepingCount :=
  TraceLocalizationInput.localizedIso_hom_comp_inv_sourceTraceBookkeepingCount_eq_certificateLedger_count
    (TraceLocalizationInput.descentSchedule source target)

/-- Descent-schedule hom-inverse cancellation target bookkeeping is counted by its target ledger. -/
theorem TraceLocalizationInput.descentScheduleLocalizedIso_hom_comp_inv_targetTraceBookkeepingCount_eq_certificateLedger_count
    (source target : QTraceExpression) :
    (TraceLocalizationWordClass.comp
      (TraceLocalizationInput.descentScheduleLocalizedIso source target).hom
      (TraceLocalizationInput.descentScheduleLocalizedIso source target).inv).targetTraceBookkeepingCount =
      (TraceLocalizationWordClass.comp
        (TraceLocalizationInput.descentScheduleLocalizedIso source target).hom
        (TraceLocalizationInput.descentScheduleLocalizedIso source target).inv).targetCertificateLedger.traceBookkeepingCount :=
  TraceLocalizationInput.localizedIso_hom_comp_inv_targetTraceBookkeepingCount_eq_certificateLedger_count
    (TraceLocalizationInput.descentSchedule source target)

/-- Descent-schedule inverse-hom cancellation source bookkeeping is counted by its source ledger. -/
theorem TraceLocalizationInput.descentScheduleLocalizedIso_inv_comp_hom_sourceTraceBookkeepingCount_eq_certificateLedger_count
    (source target : QTraceExpression) :
    (TraceLocalizationWordClass.comp
      (TraceLocalizationInput.descentScheduleLocalizedIso source target).inv
      (TraceLocalizationInput.descentScheduleLocalizedIso source target).hom).sourceTraceBookkeepingCount =
      (TraceLocalizationWordClass.comp
        (TraceLocalizationInput.descentScheduleLocalizedIso source target).inv
        (TraceLocalizationInput.descentScheduleLocalizedIso source target).hom).sourceCertificateLedger.traceBookkeepingCount :=
  TraceLocalizationInput.localizedIso_inv_comp_hom_sourceTraceBookkeepingCount_eq_certificateLedger_count
    (TraceLocalizationInput.descentSchedule source target)

/-- Descent-schedule inverse-hom cancellation target bookkeeping is counted by its target ledger. -/
theorem TraceLocalizationInput.descentScheduleLocalizedIso_inv_comp_hom_targetTraceBookkeepingCount_eq_certificateLedger_count
    (source target : QTraceExpression) :
    (TraceLocalizationWordClass.comp
      (TraceLocalizationInput.descentScheduleLocalizedIso source target).inv
      (TraceLocalizationInput.descentScheduleLocalizedIso source target).hom).targetTraceBookkeepingCount =
      (TraceLocalizationWordClass.comp
        (TraceLocalizationInput.descentScheduleLocalizedIso source target).inv
        (TraceLocalizationInput.descentScheduleLocalizedIso source target).hom).targetCertificateLedger.traceBookkeepingCount :=
  TraceLocalizationInput.localizedIso_inv_comp_hom_targetTraceBookkeepingCount_eq_certificateLedger_count
    (TraceLocalizationInput.descentSchedule source target)

/-- Interval-Stokes hom-inverse cancellation source bookkeeping is counted by its source ledger. -/
theorem TraceLocalizationInput.intervalStokesLocalizedIso_hom_comp_inv_sourceTraceBookkeepingCount_eq_certificateLedger_count
    (source target : QTraceExpression) :
    (TraceLocalizationWordClass.comp
      (TraceLocalizationInput.intervalStokesLocalizedIso source target).hom
      (TraceLocalizationInput.intervalStokesLocalizedIso source target).inv).sourceTraceBookkeepingCount =
      (TraceLocalizationWordClass.comp
        (TraceLocalizationInput.intervalStokesLocalizedIso source target).hom
        (TraceLocalizationInput.intervalStokesLocalizedIso source target).inv).sourceCertificateLedger.traceBookkeepingCount :=
  TraceLocalizationInput.localizedIso_hom_comp_inv_sourceTraceBookkeepingCount_eq_certificateLedger_count
    (TraceLocalizationInput.intervalStokes source target)

/-- Interval-Stokes hom-inverse cancellation target bookkeeping is counted by its target ledger. -/
theorem TraceLocalizationInput.intervalStokesLocalizedIso_hom_comp_inv_targetTraceBookkeepingCount_eq_certificateLedger_count
    (source target : QTraceExpression) :
    (TraceLocalizationWordClass.comp
      (TraceLocalizationInput.intervalStokesLocalizedIso source target).hom
      (TraceLocalizationInput.intervalStokesLocalizedIso source target).inv).targetTraceBookkeepingCount =
      (TraceLocalizationWordClass.comp
        (TraceLocalizationInput.intervalStokesLocalizedIso source target).hom
        (TraceLocalizationInput.intervalStokesLocalizedIso source target).inv).targetCertificateLedger.traceBookkeepingCount :=
  TraceLocalizationInput.localizedIso_hom_comp_inv_targetTraceBookkeepingCount_eq_certificateLedger_count
    (TraceLocalizationInput.intervalStokes source target)

/-- Interval-Stokes inverse-hom cancellation source bookkeeping is counted by its source ledger. -/
theorem TraceLocalizationInput.intervalStokesLocalizedIso_inv_comp_hom_sourceTraceBookkeepingCount_eq_certificateLedger_count
    (source target : QTraceExpression) :
    (TraceLocalizationWordClass.comp
      (TraceLocalizationInput.intervalStokesLocalizedIso source target).inv
      (TraceLocalizationInput.intervalStokesLocalizedIso source target).hom).sourceTraceBookkeepingCount =
      (TraceLocalizationWordClass.comp
        (TraceLocalizationInput.intervalStokesLocalizedIso source target).inv
        (TraceLocalizationInput.intervalStokesLocalizedIso source target).hom).sourceCertificateLedger.traceBookkeepingCount :=
  TraceLocalizationInput.localizedIso_inv_comp_hom_sourceTraceBookkeepingCount_eq_certificateLedger_count
    (TraceLocalizationInput.intervalStokes source target)

/-- Interval-Stokes inverse-hom cancellation target bookkeeping is counted by its target ledger. -/
theorem TraceLocalizationInput.intervalStokesLocalizedIso_inv_comp_hom_targetTraceBookkeepingCount_eq_certificateLedger_count
    (source target : QTraceExpression) :
    (TraceLocalizationWordClass.comp
      (TraceLocalizationInput.intervalStokesLocalizedIso source target).inv
      (TraceLocalizationInput.intervalStokesLocalizedIso source target).hom).targetTraceBookkeepingCount =
      (TraceLocalizationWordClass.comp
        (TraceLocalizationInput.intervalStokesLocalizedIso source target).inv
        (TraceLocalizationInput.intervalStokesLocalizedIso source target).hom).targetCertificateLedger.traceBookkeepingCount :=
  TraceLocalizationInput.localizedIso_inv_comp_hom_targetTraceBookkeepingCount_eq_certificateLedger_count
    (TraceLocalizationInput.intervalStokes source target)

/-- Interval-Fubini hom-inverse cancellation source bookkeeping is counted by its source ledger. -/
theorem TraceLocalizationInput.intervalFubiniLocalizedIso_hom_comp_inv_sourceTraceBookkeepingCount_eq_certificateLedger_count
    (source target : QTraceExpression) :
    (TraceLocalizationWordClass.comp
      (TraceLocalizationInput.intervalFubiniLocalizedIso source target).hom
      (TraceLocalizationInput.intervalFubiniLocalizedIso source target).inv).sourceTraceBookkeepingCount =
      (TraceLocalizationWordClass.comp
        (TraceLocalizationInput.intervalFubiniLocalizedIso source target).hom
        (TraceLocalizationInput.intervalFubiniLocalizedIso source target).inv).sourceCertificateLedger.traceBookkeepingCount :=
  TraceLocalizationInput.localizedIso_hom_comp_inv_sourceTraceBookkeepingCount_eq_certificateLedger_count
    (TraceLocalizationInput.intervalFubini source target)

/-- Interval-Fubini hom-inverse cancellation target bookkeeping is counted by its target ledger. -/
theorem TraceLocalizationInput.intervalFubiniLocalizedIso_hom_comp_inv_targetTraceBookkeepingCount_eq_certificateLedger_count
    (source target : QTraceExpression) :
    (TraceLocalizationWordClass.comp
      (TraceLocalizationInput.intervalFubiniLocalizedIso source target).hom
      (TraceLocalizationInput.intervalFubiniLocalizedIso source target).inv).targetTraceBookkeepingCount =
      (TraceLocalizationWordClass.comp
        (TraceLocalizationInput.intervalFubiniLocalizedIso source target).hom
        (TraceLocalizationInput.intervalFubiniLocalizedIso source target).inv).targetCertificateLedger.traceBookkeepingCount :=
  TraceLocalizationInput.localizedIso_hom_comp_inv_targetTraceBookkeepingCount_eq_certificateLedger_count
    (TraceLocalizationInput.intervalFubini source target)

/-- Interval-Fubini inverse-hom cancellation source bookkeeping is counted by its source ledger. -/
theorem TraceLocalizationInput.intervalFubiniLocalizedIso_inv_comp_hom_sourceTraceBookkeepingCount_eq_certificateLedger_count
    (source target : QTraceExpression) :
    (TraceLocalizationWordClass.comp
      (TraceLocalizationInput.intervalFubiniLocalizedIso source target).inv
      (TraceLocalizationInput.intervalFubiniLocalizedIso source target).hom).sourceTraceBookkeepingCount =
      (TraceLocalizationWordClass.comp
        (TraceLocalizationInput.intervalFubiniLocalizedIso source target).inv
        (TraceLocalizationInput.intervalFubiniLocalizedIso source target).hom).sourceCertificateLedger.traceBookkeepingCount :=
  TraceLocalizationInput.localizedIso_inv_comp_hom_sourceTraceBookkeepingCount_eq_certificateLedger_count
    (TraceLocalizationInput.intervalFubini source target)

/-- Interval-Fubini inverse-hom cancellation target bookkeeping is counted by its target ledger. -/
theorem TraceLocalizationInput.intervalFubiniLocalizedIso_inv_comp_hom_targetTraceBookkeepingCount_eq_certificateLedger_count
    (source target : QTraceExpression) :
    (TraceLocalizationWordClass.comp
      (TraceLocalizationInput.intervalFubiniLocalizedIso source target).inv
      (TraceLocalizationInput.intervalFubiniLocalizedIso source target).hom).targetTraceBookkeepingCount =
      (TraceLocalizationWordClass.comp
        (TraceLocalizationInput.intervalFubiniLocalizedIso source target).inv
        (TraceLocalizationInput.intervalFubiniLocalizedIso source target).hom).targetCertificateLedger.traceBookkeepingCount :=
  TraceLocalizationInput.localizedIso_inv_comp_hom_targetTraceBookkeepingCount_eq_certificateLedger_count
    (TraceLocalizationInput.intervalFubini source target)

/-- Tate-weight-drop hom-inverse cancellation source bookkeeping is counted by its source ledger. -/
theorem TraceLocalizationInput.tateWeightDropLocalizedIso_hom_comp_inv_sourceTraceBookkeepingCount_eq_certificateLedger_count
    (source target : QTraceExpression) :
    (TraceLocalizationWordClass.comp
      (TraceLocalizationInput.tateWeightDropLocalizedIso source target).hom
      (TraceLocalizationInput.tateWeightDropLocalizedIso source target).inv).sourceTraceBookkeepingCount =
      (TraceLocalizationWordClass.comp
        (TraceLocalizationInput.tateWeightDropLocalizedIso source target).hom
        (TraceLocalizationInput.tateWeightDropLocalizedIso source target).inv).sourceCertificateLedger.traceBookkeepingCount :=
  TraceLocalizationInput.localizedIso_hom_comp_inv_sourceTraceBookkeepingCount_eq_certificateLedger_count
    (TraceLocalizationInput.tateWeightDrop source target)

/-- Tate-weight-drop hom-inverse cancellation target bookkeeping is counted by its target ledger. -/
theorem TraceLocalizationInput.tateWeightDropLocalizedIso_hom_comp_inv_targetTraceBookkeepingCount_eq_certificateLedger_count
    (source target : QTraceExpression) :
    (TraceLocalizationWordClass.comp
      (TraceLocalizationInput.tateWeightDropLocalizedIso source target).hom
      (TraceLocalizationInput.tateWeightDropLocalizedIso source target).inv).targetTraceBookkeepingCount =
      (TraceLocalizationWordClass.comp
        (TraceLocalizationInput.tateWeightDropLocalizedIso source target).hom
        (TraceLocalizationInput.tateWeightDropLocalizedIso source target).inv).targetCertificateLedger.traceBookkeepingCount :=
  TraceLocalizationInput.localizedIso_hom_comp_inv_targetTraceBookkeepingCount_eq_certificateLedger_count
    (TraceLocalizationInput.tateWeightDrop source target)

/-- Tate-weight-drop inverse-hom cancellation source bookkeeping is counted by its source ledger. -/
theorem TraceLocalizationInput.tateWeightDropLocalizedIso_inv_comp_hom_sourceTraceBookkeepingCount_eq_certificateLedger_count
    (source target : QTraceExpression) :
    (TraceLocalizationWordClass.comp
      (TraceLocalizationInput.tateWeightDropLocalizedIso source target).inv
      (TraceLocalizationInput.tateWeightDropLocalizedIso source target).hom).sourceTraceBookkeepingCount =
      (TraceLocalizationWordClass.comp
        (TraceLocalizationInput.tateWeightDropLocalizedIso source target).inv
        (TraceLocalizationInput.tateWeightDropLocalizedIso source target).hom).sourceCertificateLedger.traceBookkeepingCount :=
  TraceLocalizationInput.localizedIso_inv_comp_hom_sourceTraceBookkeepingCount_eq_certificateLedger_count
    (TraceLocalizationInput.tateWeightDrop source target)

/-- Tate-weight-drop inverse-hom cancellation target bookkeeping is counted by its target ledger. -/
theorem TraceLocalizationInput.tateWeightDropLocalizedIso_inv_comp_hom_targetTraceBookkeepingCount_eq_certificateLedger_count
    (source target : QTraceExpression) :
    (TraceLocalizationWordClass.comp
      (TraceLocalizationInput.tateWeightDropLocalizedIso source target).inv
      (TraceLocalizationInput.tateWeightDropLocalizedIso source target).hom).targetTraceBookkeepingCount =
      (TraceLocalizationWordClass.comp
        (TraceLocalizationInput.tateWeightDropLocalizedIso source target).inv
        (TraceLocalizationInput.tateWeightDropLocalizedIso source target).hom).targetCertificateLedger.traceBookkeepingCount :=
  TraceLocalizationInput.localizedIso_inv_comp_hom_targetTraceBookkeepingCount_eq_certificateLedger_count
    (TraceLocalizationInput.tateWeightDrop source target)

end AnalyticMotives
end LFunctions
end Boundary
