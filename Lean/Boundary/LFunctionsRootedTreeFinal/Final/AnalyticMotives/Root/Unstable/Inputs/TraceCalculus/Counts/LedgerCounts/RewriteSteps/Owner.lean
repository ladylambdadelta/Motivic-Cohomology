import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Root.Unstable.Inputs.TraceCalculus.Counts.LedgerCounts.RewriteSteps.Owner

/-!
# Top-root all-kind unstable input rewrite-step ledger counts

This file mirrors the motive-root endpoint rewrite-step
count-as-certificate-ledger-count facts for hom and inverse arrows of all six
named unstable localization isomorphisms.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- The root exposes by-kind descent-channel hom rewrite count-as-ledger-count. -/
theorem AnalyticMotivesRoot.unstableByKindDescentChannelIso_hom_endpointRewriteStepCount_eq_certificateLedger_count
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.descentChannelIso source target).hom.endpointRewriteStepCount =
      (TraceUnstableAnalyticMotive.descentChannelIso
        source
        target).hom.endpointCertificateLedger.rewriteStepCount :=
  TraceAnalyticMotive.unstableByKindDescentChannelIso_hom_endpointRewriteStepCount_eq_certificateLedger_count
    source
    target

/-- The root exposes by-kind descent-channel inverse rewrite count-as-ledger-count. -/
theorem AnalyticMotivesRoot.unstableByKindDescentChannelIso_inv_endpointRewriteStepCount_eq_certificateLedger_count
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.descentChannelIso source target).inv.endpointRewriteStepCount =
      (TraceUnstableAnalyticMotive.descentChannelIso
        source
        target).inv.endpointCertificateLedger.rewriteStepCount :=
  TraceAnalyticMotive.unstableByKindDescentChannelIso_inv_endpointRewriteStepCount_eq_certificateLedger_count
    source
    target

/-- The root exposes by-kind descent-refinement hom rewrite count-as-ledger-count. -/
theorem AnalyticMotivesRoot.unstableByKindDescentRefinementIso_hom_endpointRewriteStepCount_eq_certificateLedger_count
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.descentRefinementIso source target).hom.endpointRewriteStepCount =
      (TraceUnstableAnalyticMotive.descentRefinementIso
        source
        target).hom.endpointCertificateLedger.rewriteStepCount :=
  TraceAnalyticMotive.unstableByKindDescentRefinementIso_hom_endpointRewriteStepCount_eq_certificateLedger_count
    source
    target

/-- The root exposes by-kind descent-refinement inverse rewrite count-as-ledger-count. -/
theorem AnalyticMotivesRoot.unstableByKindDescentRefinementIso_inv_endpointRewriteStepCount_eq_certificateLedger_count
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.descentRefinementIso source target).inv.endpointRewriteStepCount =
      (TraceUnstableAnalyticMotive.descentRefinementIso
        source
        target).inv.endpointCertificateLedger.rewriteStepCount :=
  TraceAnalyticMotive.unstableByKindDescentRefinementIso_inv_endpointRewriteStepCount_eq_certificateLedger_count
    source
    target

/-- The root exposes by-kind descent-schedule hom rewrite count-as-ledger-count. -/
theorem AnalyticMotivesRoot.unstableByKindDescentScheduleIso_hom_endpointRewriteStepCount_eq_certificateLedger_count
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.descentScheduleIso source target).hom.endpointRewriteStepCount =
      (TraceUnstableAnalyticMotive.descentScheduleIso
        source
        target).hom.endpointCertificateLedger.rewriteStepCount :=
  TraceAnalyticMotive.unstableByKindDescentScheduleIso_hom_endpointRewriteStepCount_eq_certificateLedger_count
    source
    target

/-- The root exposes by-kind descent-schedule inverse rewrite count-as-ledger-count. -/
theorem AnalyticMotivesRoot.unstableByKindDescentScheduleIso_inv_endpointRewriteStepCount_eq_certificateLedger_count
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.descentScheduleIso source target).inv.endpointRewriteStepCount =
      (TraceUnstableAnalyticMotive.descentScheduleIso
        source
        target).inv.endpointCertificateLedger.rewriteStepCount :=
  TraceAnalyticMotive.unstableByKindDescentScheduleIso_inv_endpointRewriteStepCount_eq_certificateLedger_count
    source
    target

/-- The root exposes by-kind interval-Stokes hom rewrite count-as-ledger-count. -/
theorem AnalyticMotivesRoot.unstableByKindIntervalStokesIso_hom_endpointRewriteStepCount_eq_certificateLedger_count
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.intervalStokesIso source target).hom.endpointRewriteStepCount =
      (TraceUnstableAnalyticMotive.intervalStokesIso
        source
        target).hom.endpointCertificateLedger.rewriteStepCount :=
  TraceAnalyticMotive.unstableByKindIntervalStokesIso_hom_endpointRewriteStepCount_eq_certificateLedger_count
    source
    target

/-- The root exposes by-kind interval-Stokes inverse rewrite count-as-ledger-count. -/
theorem AnalyticMotivesRoot.unstableByKindIntervalStokesIso_inv_endpointRewriteStepCount_eq_certificateLedger_count
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.intervalStokesIso source target).inv.endpointRewriteStepCount =
      (TraceUnstableAnalyticMotive.intervalStokesIso
        source
        target).inv.endpointCertificateLedger.rewriteStepCount :=
  TraceAnalyticMotive.unstableByKindIntervalStokesIso_inv_endpointRewriteStepCount_eq_certificateLedger_count
    source
    target

/-- The root exposes by-kind interval-Fubini hom rewrite count-as-ledger-count. -/
theorem AnalyticMotivesRoot.unstableByKindIntervalFubiniIso_hom_endpointRewriteStepCount_eq_certificateLedger_count
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.intervalFubiniIso source target).hom.endpointRewriteStepCount =
      (TraceUnstableAnalyticMotive.intervalFubiniIso
        source
        target).hom.endpointCertificateLedger.rewriteStepCount :=
  TraceAnalyticMotive.unstableByKindIntervalFubiniIso_hom_endpointRewriteStepCount_eq_certificateLedger_count
    source
    target

/-- The root exposes by-kind interval-Fubini inverse rewrite count-as-ledger-count. -/
theorem AnalyticMotivesRoot.unstableByKindIntervalFubiniIso_inv_endpointRewriteStepCount_eq_certificateLedger_count
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.intervalFubiniIso source target).inv.endpointRewriteStepCount =
      (TraceUnstableAnalyticMotive.intervalFubiniIso
        source
        target).inv.endpointCertificateLedger.rewriteStepCount :=
  TraceAnalyticMotive.unstableByKindIntervalFubiniIso_inv_endpointRewriteStepCount_eq_certificateLedger_count
    source
    target

/-- The root exposes by-kind Tate-weight-drop hom rewrite count-as-ledger-count. -/
theorem AnalyticMotivesRoot.unstableByKindTateWeightDropIso_hom_endpointRewriteStepCount_eq_certificateLedger_count
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.tateWeightDropIso source target).hom.endpointRewriteStepCount =
      (TraceUnstableAnalyticMotive.tateWeightDropIso
        source
        target).hom.endpointCertificateLedger.rewriteStepCount :=
  TraceAnalyticMotive.unstableByKindTateWeightDropIso_hom_endpointRewriteStepCount_eq_certificateLedger_count
    source
    target

/-- The root exposes by-kind Tate-weight-drop inverse rewrite count-as-ledger-count. -/
theorem AnalyticMotivesRoot.unstableByKindTateWeightDropIso_inv_endpointRewriteStepCount_eq_certificateLedger_count
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.tateWeightDropIso source target).inv.endpointRewriteStepCount =
      (TraceUnstableAnalyticMotive.tateWeightDropIso
        source
        target).inv.endpointCertificateLedger.rewriteStepCount :=
  TraceAnalyticMotive.unstableByKindTateWeightDropIso_inv_endpointRewriteStepCount_eq_certificateLedger_count
    source
    target

end AnalyticMotives
end LFunctions
end Boundary
