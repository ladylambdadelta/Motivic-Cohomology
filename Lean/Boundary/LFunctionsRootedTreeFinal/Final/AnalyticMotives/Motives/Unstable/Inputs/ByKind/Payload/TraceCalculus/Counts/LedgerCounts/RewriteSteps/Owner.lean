import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Unstable.Inputs.ByKind.Payload.TraceCalculus.Counts.LedgerCounts.Bookkeeping.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.LocalizationInput.WordQuotient.Category.Inputs.ByKind.Isomorphisms.Payload.TraceCalculus.Counts.RewriteSteps.LedgerCounts.Endpoint.Owner

/-!
# By-kind unstable rewrite-step ledger counts

This file exposes endpoint rewrite-step count-as-ledger-count facts for the
six named unstable analytic-motive isomorphisms.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Descent-channel unstable hom endpoint rewrite count is counted by its endpoint ledger. -/
theorem TraceUnstableAnalyticMotive.descentChannelIso_hom_endpointRewriteStepCount_eq_certificateLedger_count
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.descentChannelIso source target).hom.endpointRewriteStepCount =
      (TraceUnstableAnalyticMotive.descentChannelIso
        source
        target).hom.endpointCertificateLedger.rewriteStepCount :=
  TraceLocalizationInput.descentChannelLocalizedIso_hom_endpointRewriteStepCount_eq_certificateLedger_count
    source
    target

/-- Descent-channel unstable inverse endpoint rewrite count is counted by its endpoint ledger. -/
theorem TraceUnstableAnalyticMotive.descentChannelIso_inv_endpointRewriteStepCount_eq_certificateLedger_count
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.descentChannelIso source target).inv.endpointRewriteStepCount =
      (TraceUnstableAnalyticMotive.descentChannelIso
        source
        target).inv.endpointCertificateLedger.rewriteStepCount :=
  TraceLocalizationInput.descentChannelLocalizedIso_inv_endpointRewriteStepCount_eq_certificateLedger_count
    source
    target

/-- Descent-refinement unstable hom endpoint rewrite count is counted by its endpoint ledger. -/
theorem TraceUnstableAnalyticMotive.descentRefinementIso_hom_endpointRewriteStepCount_eq_certificateLedger_count
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.descentRefinementIso source target).hom.endpointRewriteStepCount =
      (TraceUnstableAnalyticMotive.descentRefinementIso
        source
        target).hom.endpointCertificateLedger.rewriteStepCount :=
  TraceLocalizationInput.descentRefinementLocalizedIso_hom_endpointRewriteStepCount_eq_certificateLedger_count
    source
    target

/-- Descent-refinement unstable inverse endpoint rewrite count is counted by its endpoint ledger. -/
theorem TraceUnstableAnalyticMotive.descentRefinementIso_inv_endpointRewriteStepCount_eq_certificateLedger_count
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.descentRefinementIso source target).inv.endpointRewriteStepCount =
      (TraceUnstableAnalyticMotive.descentRefinementIso
        source
        target).inv.endpointCertificateLedger.rewriteStepCount :=
  TraceLocalizationInput.descentRefinementLocalizedIso_inv_endpointRewriteStepCount_eq_certificateLedger_count
    source
    target

/-- Descent-schedule unstable hom endpoint rewrite count is counted by its endpoint ledger. -/
theorem TraceUnstableAnalyticMotive.descentScheduleIso_hom_endpointRewriteStepCount_eq_certificateLedger_count
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.descentScheduleIso source target).hom.endpointRewriteStepCount =
      (TraceUnstableAnalyticMotive.descentScheduleIso
        source
        target).hom.endpointCertificateLedger.rewriteStepCount :=
  TraceLocalizationInput.descentScheduleLocalizedIso_hom_endpointRewriteStepCount_eq_certificateLedger_count
    source
    target

/-- Descent-schedule unstable inverse endpoint rewrite count is counted by its endpoint ledger. -/
theorem TraceUnstableAnalyticMotive.descentScheduleIso_inv_endpointRewriteStepCount_eq_certificateLedger_count
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.descentScheduleIso source target).inv.endpointRewriteStepCount =
      (TraceUnstableAnalyticMotive.descentScheduleIso
        source
        target).inv.endpointCertificateLedger.rewriteStepCount :=
  TraceLocalizationInput.descentScheduleLocalizedIso_inv_endpointRewriteStepCount_eq_certificateLedger_count
    source
    target

/-- Interval-Stokes unstable hom endpoint rewrite count is counted by its endpoint ledger. -/
theorem TraceUnstableAnalyticMotive.intervalStokesIso_hom_endpointRewriteStepCount_eq_certificateLedger_count
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.intervalStokesIso source target).hom.endpointRewriteStepCount =
      (TraceUnstableAnalyticMotive.intervalStokesIso
        source
        target).hom.endpointCertificateLedger.rewriteStepCount :=
  TraceLocalizationInput.intervalStokesLocalizedIso_hom_endpointRewriteStepCount_eq_certificateLedger_count
    source
    target

/-- Interval-Stokes unstable inverse endpoint rewrite count is counted by its endpoint ledger. -/
theorem TraceUnstableAnalyticMotive.intervalStokesIso_inv_endpointRewriteStepCount_eq_certificateLedger_count
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.intervalStokesIso source target).inv.endpointRewriteStepCount =
      (TraceUnstableAnalyticMotive.intervalStokesIso
        source
        target).inv.endpointCertificateLedger.rewriteStepCount :=
  TraceLocalizationInput.intervalStokesLocalizedIso_inv_endpointRewriteStepCount_eq_certificateLedger_count
    source
    target

/-- Interval-Fubini unstable hom endpoint rewrite count is counted by its endpoint ledger. -/
theorem TraceUnstableAnalyticMotive.intervalFubiniIso_hom_endpointRewriteStepCount_eq_certificateLedger_count
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.intervalFubiniIso source target).hom.endpointRewriteStepCount =
      (TraceUnstableAnalyticMotive.intervalFubiniIso
        source
        target).hom.endpointCertificateLedger.rewriteStepCount :=
  TraceLocalizationInput.intervalFubiniLocalizedIso_hom_endpointRewriteStepCount_eq_certificateLedger_count
    source
    target

/-- Interval-Fubini unstable inverse endpoint rewrite count is counted by its endpoint ledger. -/
theorem TraceUnstableAnalyticMotive.intervalFubiniIso_inv_endpointRewriteStepCount_eq_certificateLedger_count
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.intervalFubiniIso source target).inv.endpointRewriteStepCount =
      (TraceUnstableAnalyticMotive.intervalFubiniIso
        source
        target).inv.endpointCertificateLedger.rewriteStepCount :=
  TraceLocalizationInput.intervalFubiniLocalizedIso_inv_endpointRewriteStepCount_eq_certificateLedger_count
    source
    target

/-- Tate-weight-drop unstable hom endpoint rewrite count is counted by its endpoint ledger. -/
theorem TraceUnstableAnalyticMotive.tateWeightDropIso_hom_endpointRewriteStepCount_eq_certificateLedger_count
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.tateWeightDropIso source target).hom.endpointRewriteStepCount =
      (TraceUnstableAnalyticMotive.tateWeightDropIso
        source
        target).hom.endpointCertificateLedger.rewriteStepCount :=
  TraceLocalizationInput.tateWeightDropLocalizedIso_hom_endpointRewriteStepCount_eq_certificateLedger_count
    source
    target

/-- Tate-weight-drop unstable inverse endpoint rewrite count is counted by its endpoint ledger. -/
theorem TraceUnstableAnalyticMotive.tateWeightDropIso_inv_endpointRewriteStepCount_eq_certificateLedger_count
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.tateWeightDropIso source target).inv.endpointRewriteStepCount =
      (TraceUnstableAnalyticMotive.tateWeightDropIso
        source
        target).inv.endpointCertificateLedger.rewriteStepCount :=
  TraceLocalizationInput.tateWeightDropLocalizedIso_inv_endpointRewriteStepCount_eq_certificateLedger_count
    source
    target

end AnalyticMotives
end LFunctions
end Boundary
