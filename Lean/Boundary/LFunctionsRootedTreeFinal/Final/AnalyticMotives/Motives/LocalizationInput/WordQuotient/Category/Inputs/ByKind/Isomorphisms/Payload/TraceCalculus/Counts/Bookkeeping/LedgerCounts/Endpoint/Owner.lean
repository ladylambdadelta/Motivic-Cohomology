import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.LocalizationInput.WordQuotient.Category.Inputs.ByKind.Isomorphisms.Payload.TraceCalculus.Counts.Bookkeeping.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.LocalizationInput.WordQuotient.Category.Inputs.ByKind.Payload.TraceCalculus.LedgerCounts.Owner

/-!
# Endpoint bookkeeping ledger counts for named localized isomorphisms

This file owns endpoint trace-bookkeeping count-as-ledger-count facts for the
hom and inverse arrows of the named localized isomorphisms.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Descent-channel isomorphism hom endpoint bookkeeping is counted by its endpoint ledger. -/
theorem TraceLocalizationInput.descentChannelLocalizedIso_hom_endpointTraceBookkeepingCount_eq_certificateLedger_count
    (source target : QTraceExpression) :
    (TraceLocalizationInput.descentChannelLocalizedIso
      source
      target).hom.endpointTraceBookkeepingCount =
      (TraceLocalizationInput.descentChannelLocalizedIso
        source
        target).hom.endpointCertificateLedger.traceBookkeepingCount :=
  TraceLocalizationInput.descentChannelForwardArrow_endpointTraceBookkeepingCount_eq_certificateLedger_count
    source
    target

/-- Descent-channel isomorphism inverse endpoint bookkeeping is counted by its endpoint ledger. -/
theorem TraceLocalizationInput.descentChannelLocalizedIso_inv_endpointTraceBookkeepingCount_eq_certificateLedger_count
    (source target : QTraceExpression) :
    (TraceLocalizationInput.descentChannelLocalizedIso
      source
      target).inv.endpointTraceBookkeepingCount =
      (TraceLocalizationInput.descentChannelLocalizedIso
        source
        target).inv.endpointCertificateLedger.traceBookkeepingCount :=
  TraceLocalizationInput.descentChannelInverseArrow_endpointTraceBookkeepingCount_eq_certificateLedger_count
    source
    target

/-- Descent-refinement isomorphism hom endpoint bookkeeping is counted by its endpoint ledger. -/
theorem TraceLocalizationInput.descentRefinementLocalizedIso_hom_endpointTraceBookkeepingCount_eq_certificateLedger_count
    (source target : QTraceExpression) :
    (TraceLocalizationInput.descentRefinementLocalizedIso
      source
      target).hom.endpointTraceBookkeepingCount =
      (TraceLocalizationInput.descentRefinementLocalizedIso
        source
        target).hom.endpointCertificateLedger.traceBookkeepingCount :=
  TraceLocalizationInput.descentRefinementForwardArrow_endpointTraceBookkeepingCount_eq_certificateLedger_count
    source
    target

/-- Descent-refinement isomorphism inverse endpoint bookkeeping is counted by its endpoint ledger. -/
theorem TraceLocalizationInput.descentRefinementLocalizedIso_inv_endpointTraceBookkeepingCount_eq_certificateLedger_count
    (source target : QTraceExpression) :
    (TraceLocalizationInput.descentRefinementLocalizedIso
      source
      target).inv.endpointTraceBookkeepingCount =
      (TraceLocalizationInput.descentRefinementLocalizedIso
        source
        target).inv.endpointCertificateLedger.traceBookkeepingCount :=
  TraceLocalizationInput.descentRefinementInverseArrow_endpointTraceBookkeepingCount_eq_certificateLedger_count
    source
    target

/-- Descent-schedule isomorphism hom endpoint bookkeeping is counted by its endpoint ledger. -/
theorem TraceLocalizationInput.descentScheduleLocalizedIso_hom_endpointTraceBookkeepingCount_eq_certificateLedger_count
    (source target : QTraceExpression) :
    (TraceLocalizationInput.descentScheduleLocalizedIso
      source
      target).hom.endpointTraceBookkeepingCount =
      (TraceLocalizationInput.descentScheduleLocalizedIso
        source
        target).hom.endpointCertificateLedger.traceBookkeepingCount :=
  TraceLocalizationInput.descentScheduleForwardArrow_endpointTraceBookkeepingCount_eq_certificateLedger_count
    source
    target

/-- Descent-schedule isomorphism inverse endpoint bookkeeping is counted by its endpoint ledger. -/
theorem TraceLocalizationInput.descentScheduleLocalizedIso_inv_endpointTraceBookkeepingCount_eq_certificateLedger_count
    (source target : QTraceExpression) :
    (TraceLocalizationInput.descentScheduleLocalizedIso
      source
      target).inv.endpointTraceBookkeepingCount =
      (TraceLocalizationInput.descentScheduleLocalizedIso
        source
        target).inv.endpointCertificateLedger.traceBookkeepingCount :=
  TraceLocalizationInput.descentScheduleInverseArrow_endpointTraceBookkeepingCount_eq_certificateLedger_count
    source
    target

/-- Interval-Stokes isomorphism hom endpoint bookkeeping is counted by its endpoint ledger. -/
theorem TraceLocalizationInput.intervalStokesLocalizedIso_hom_endpointTraceBookkeepingCount_eq_certificateLedger_count
    (source target : QTraceExpression) :
    (TraceLocalizationInput.intervalStokesLocalizedIso
      source
      target).hom.endpointTraceBookkeepingCount =
      (TraceLocalizationInput.intervalStokesLocalizedIso
        source
        target).hom.endpointCertificateLedger.traceBookkeepingCount :=
  TraceLocalizationInput.intervalStokesForwardArrow_endpointTraceBookkeepingCount_eq_certificateLedger_count
    source
    target

/-- Interval-Stokes isomorphism inverse endpoint bookkeeping is counted by its endpoint ledger. -/
theorem TraceLocalizationInput.intervalStokesLocalizedIso_inv_endpointTraceBookkeepingCount_eq_certificateLedger_count
    (source target : QTraceExpression) :
    (TraceLocalizationInput.intervalStokesLocalizedIso
      source
      target).inv.endpointTraceBookkeepingCount =
      (TraceLocalizationInput.intervalStokesLocalizedIso
        source
        target).inv.endpointCertificateLedger.traceBookkeepingCount :=
  TraceLocalizationInput.intervalStokesInverseArrow_endpointTraceBookkeepingCount_eq_certificateLedger_count
    source
    target

/-- Interval-Fubini isomorphism hom endpoint bookkeeping is counted by its endpoint ledger. -/
theorem TraceLocalizationInput.intervalFubiniLocalizedIso_hom_endpointTraceBookkeepingCount_eq_certificateLedger_count
    (source target : QTraceExpression) :
    (TraceLocalizationInput.intervalFubiniLocalizedIso
      source
      target).hom.endpointTraceBookkeepingCount =
      (TraceLocalizationInput.intervalFubiniLocalizedIso
        source
        target).hom.endpointCertificateLedger.traceBookkeepingCount :=
  TraceLocalizationInput.intervalFubiniForwardArrow_endpointTraceBookkeepingCount_eq_certificateLedger_count
    source
    target

/-- Interval-Fubini isomorphism inverse endpoint bookkeeping is counted by its endpoint ledger. -/
theorem TraceLocalizationInput.intervalFubiniLocalizedIso_inv_endpointTraceBookkeepingCount_eq_certificateLedger_count
    (source target : QTraceExpression) :
    (TraceLocalizationInput.intervalFubiniLocalizedIso
      source
      target).inv.endpointTraceBookkeepingCount =
      (TraceLocalizationInput.intervalFubiniLocalizedIso
        source
        target).inv.endpointCertificateLedger.traceBookkeepingCount :=
  TraceLocalizationInput.intervalFubiniInverseArrow_endpointTraceBookkeepingCount_eq_certificateLedger_count
    source
    target

/-- Tate-weight-drop isomorphism hom endpoint bookkeeping is counted by its endpoint ledger. -/
theorem TraceLocalizationInput.tateWeightDropLocalizedIso_hom_endpointTraceBookkeepingCount_eq_certificateLedger_count
    (source target : QTraceExpression) :
    (TraceLocalizationInput.tateWeightDropLocalizedIso
      source
      target).hom.endpointTraceBookkeepingCount =
      (TraceLocalizationInput.tateWeightDropLocalizedIso
        source
        target).hom.endpointCertificateLedger.traceBookkeepingCount :=
  TraceLocalizationInput.tateWeightDropForwardArrow_endpointTraceBookkeepingCount_eq_certificateLedger_count
    source
    target

/-- Tate-weight-drop isomorphism inverse endpoint bookkeeping is counted by its endpoint ledger. -/
theorem TraceLocalizationInput.tateWeightDropLocalizedIso_inv_endpointTraceBookkeepingCount_eq_certificateLedger_count
    (source target : QTraceExpression) :
    (TraceLocalizationInput.tateWeightDropLocalizedIso
      source
      target).inv.endpointTraceBookkeepingCount =
      (TraceLocalizationInput.tateWeightDropLocalizedIso
        source
        target).inv.endpointCertificateLedger.traceBookkeepingCount :=
  TraceLocalizationInput.tateWeightDropInverseArrow_endpointTraceBookkeepingCount_eq_certificateLedger_count
    source
    target

end AnalyticMotives
end LFunctions
end Boundary
