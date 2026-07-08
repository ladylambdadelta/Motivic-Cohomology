import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Unstable.Inputs.ByKind.Payload.TraceCalculus.Counts.LedgerCounts.RewriteSteps.Owner

/-!
# Root all-kind unstable input rewrite-step ledger counts

This file exposes endpoint rewrite-step count-as-certificate-ledger-count facts
for hom and inverse arrows of all six named unstable localization isomorphisms
at the motive-root namespace.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- By-kind descent-channel hom endpoint rewrite count is counted by its endpoint ledger. -/
theorem TraceAnalyticMotive.unstableByKindDescentChannelIso_hom_endpointRewriteStepCount_eq_certificateLedger_count
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.descentChannelIso source target).hom.endpointRewriteStepCount =
      (TraceUnstableAnalyticMotive.descentChannelIso
        source
        target).hom.endpointCertificateLedger.rewriteStepCount :=
  TraceUnstableAnalyticMotive.descentChannelIso_hom_endpointRewriteStepCount_eq_certificateLedger_count
    source
    target

/-- By-kind descent-channel inverse endpoint rewrite count is counted by its endpoint ledger. -/
theorem TraceAnalyticMotive.unstableByKindDescentChannelIso_inv_endpointRewriteStepCount_eq_certificateLedger_count
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.descentChannelIso source target).inv.endpointRewriteStepCount =
      (TraceUnstableAnalyticMotive.descentChannelIso
        source
        target).inv.endpointCertificateLedger.rewriteStepCount :=
  TraceUnstableAnalyticMotive.descentChannelIso_inv_endpointRewriteStepCount_eq_certificateLedger_count
    source
    target

/-- By-kind descent-refinement hom endpoint rewrite count is counted by its endpoint ledger. -/
theorem TraceAnalyticMotive.unstableByKindDescentRefinementIso_hom_endpointRewriteStepCount_eq_certificateLedger_count
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.descentRefinementIso source target).hom.endpointRewriteStepCount =
      (TraceUnstableAnalyticMotive.descentRefinementIso
        source
        target).hom.endpointCertificateLedger.rewriteStepCount :=
  TraceUnstableAnalyticMotive.descentRefinementIso_hom_endpointRewriteStepCount_eq_certificateLedger_count
    source
    target

/-- By-kind descent-refinement inverse endpoint rewrite count is counted by its endpoint ledger. -/
theorem TraceAnalyticMotive.unstableByKindDescentRefinementIso_inv_endpointRewriteStepCount_eq_certificateLedger_count
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.descentRefinementIso source target).inv.endpointRewriteStepCount =
      (TraceUnstableAnalyticMotive.descentRefinementIso
        source
        target).inv.endpointCertificateLedger.rewriteStepCount :=
  TraceUnstableAnalyticMotive.descentRefinementIso_inv_endpointRewriteStepCount_eq_certificateLedger_count
    source
    target

/-- By-kind descent-schedule hom endpoint rewrite count is counted by its endpoint ledger. -/
theorem TraceAnalyticMotive.unstableByKindDescentScheduleIso_hom_endpointRewriteStepCount_eq_certificateLedger_count
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.descentScheduleIso source target).hom.endpointRewriteStepCount =
      (TraceUnstableAnalyticMotive.descentScheduleIso
        source
        target).hom.endpointCertificateLedger.rewriteStepCount :=
  TraceUnstableAnalyticMotive.descentScheduleIso_hom_endpointRewriteStepCount_eq_certificateLedger_count
    source
    target

/-- By-kind descent-schedule inverse endpoint rewrite count is counted by its endpoint ledger. -/
theorem TraceAnalyticMotive.unstableByKindDescentScheduleIso_inv_endpointRewriteStepCount_eq_certificateLedger_count
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.descentScheduleIso source target).inv.endpointRewriteStepCount =
      (TraceUnstableAnalyticMotive.descentScheduleIso
        source
        target).inv.endpointCertificateLedger.rewriteStepCount :=
  TraceUnstableAnalyticMotive.descentScheduleIso_inv_endpointRewriteStepCount_eq_certificateLedger_count
    source
    target

/-- By-kind interval-Stokes hom endpoint rewrite count is counted by its endpoint ledger. -/
theorem TraceAnalyticMotive.unstableByKindIntervalStokesIso_hom_endpointRewriteStepCount_eq_certificateLedger_count
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.intervalStokesIso source target).hom.endpointRewriteStepCount =
      (TraceUnstableAnalyticMotive.intervalStokesIso
        source
        target).hom.endpointCertificateLedger.rewriteStepCount :=
  TraceUnstableAnalyticMotive.intervalStokesIso_hom_endpointRewriteStepCount_eq_certificateLedger_count
    source
    target

/-- By-kind interval-Stokes inverse endpoint rewrite count is counted by its endpoint ledger. -/
theorem TraceAnalyticMotive.unstableByKindIntervalStokesIso_inv_endpointRewriteStepCount_eq_certificateLedger_count
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.intervalStokesIso source target).inv.endpointRewriteStepCount =
      (TraceUnstableAnalyticMotive.intervalStokesIso
        source
        target).inv.endpointCertificateLedger.rewriteStepCount :=
  TraceUnstableAnalyticMotive.intervalStokesIso_inv_endpointRewriteStepCount_eq_certificateLedger_count
    source
    target

/-- By-kind interval-Fubini hom endpoint rewrite count is counted by its endpoint ledger. -/
theorem TraceAnalyticMotive.unstableByKindIntervalFubiniIso_hom_endpointRewriteStepCount_eq_certificateLedger_count
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.intervalFubiniIso source target).hom.endpointRewriteStepCount =
      (TraceUnstableAnalyticMotive.intervalFubiniIso
        source
        target).hom.endpointCertificateLedger.rewriteStepCount :=
  TraceUnstableAnalyticMotive.intervalFubiniIso_hom_endpointRewriteStepCount_eq_certificateLedger_count
    source
    target

/-- By-kind interval-Fubini inverse endpoint rewrite count is counted by its endpoint ledger. -/
theorem TraceAnalyticMotive.unstableByKindIntervalFubiniIso_inv_endpointRewriteStepCount_eq_certificateLedger_count
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.intervalFubiniIso source target).inv.endpointRewriteStepCount =
      (TraceUnstableAnalyticMotive.intervalFubiniIso
        source
        target).inv.endpointCertificateLedger.rewriteStepCount :=
  TraceUnstableAnalyticMotive.intervalFubiniIso_inv_endpointRewriteStepCount_eq_certificateLedger_count
    source
    target

/-- By-kind Tate-weight-drop hom endpoint rewrite count is counted by its endpoint ledger. -/
theorem TraceAnalyticMotive.unstableByKindTateWeightDropIso_hom_endpointRewriteStepCount_eq_certificateLedger_count
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.tateWeightDropIso source target).hom.endpointRewriteStepCount =
      (TraceUnstableAnalyticMotive.tateWeightDropIso
        source
        target).hom.endpointCertificateLedger.rewriteStepCount :=
  TraceUnstableAnalyticMotive.tateWeightDropIso_hom_endpointRewriteStepCount_eq_certificateLedger_count
    source
    target

/-- By-kind Tate-weight-drop inverse endpoint rewrite count is counted by its endpoint ledger. -/
theorem TraceAnalyticMotive.unstableByKindTateWeightDropIso_inv_endpointRewriteStepCount_eq_certificateLedger_count
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.tateWeightDropIso source target).inv.endpointRewriteStepCount =
      (TraceUnstableAnalyticMotive.tateWeightDropIso
        source
        target).inv.endpointCertificateLedger.rewriteStepCount :=
  TraceUnstableAnalyticMotive.tateWeightDropIso_inv_endpointRewriteStepCount_eq_certificateLedger_count
    source
    target

end AnalyticMotives
end LFunctions
end Boundary
