import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Unstable.Payload.TraceCalculus.Homs.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Unstable.Payload.TraceCalculus.Objects.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.LocalizationInput.WordQuotient.Category.Payload.TraceCalculus.LedgerCounts.Owner

/-!
# Trace-calculus ledger counts in the unstable envelope

This file records that unstable trace-bookkeeping and rewrite-step payloads are
counted by certificate ledgers.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Object bookkeeping payload is counted by its certificate ledger. -/
theorem TraceUnstableAnalyticMotive.traceBookkeepingCount_eq_certificateLedger_count
    (object : TraceUnstableAnalyticMotive) :
    object.traceBookkeepingCount =
      object.certificateLedger.traceBookkeepingCount :=
  TraceLocalizedWordObject.traceBookkeepingCount_eq_certificateLedger_count
    object

/-- Object rewrite-step payload is counted by its certificate ledger. -/
theorem TraceUnstableAnalyticMotive.rewriteStepCount_eq_certificateLedger_count
    (object : TraceUnstableAnalyticMotive) :
    object.rewriteStepCount =
      object.certificateLedger.rewriteStepCount :=
  TraceLocalizedWordObject.rewriteStepCount_eq_certificateLedger_count
    object

/-- Source endpoint bookkeeping is counted by the source endpoint ledger. -/
theorem TraceUnstableAnalyticMotiveHom.sourceTraceBookkeepingCount_eq_certificateLedger_count
    {source target : TraceUnstableAnalyticMotive}
    (hom : TraceUnstableAnalyticMotiveHom source target) :
    hom.sourceTraceBookkeepingCount =
      hom.sourceCertificateLedger.traceBookkeepingCount :=
  TraceLocalizedWordHom.sourceTraceBookkeepingCount_eq_certificateLedger_count
    hom

/-- Target endpoint bookkeeping is counted by the target endpoint ledger. -/
theorem TraceUnstableAnalyticMotiveHom.targetTraceBookkeepingCount_eq_certificateLedger_count
    {source target : TraceUnstableAnalyticMotive}
    (hom : TraceUnstableAnalyticMotiveHom source target) :
    hom.targetTraceBookkeepingCount =
      hom.targetCertificateLedger.traceBookkeepingCount :=
  TraceLocalizedWordHom.targetTraceBookkeepingCount_eq_certificateLedger_count
    hom

/-- Source endpoint rewrite steps are counted by the source endpoint ledger. -/
theorem TraceUnstableAnalyticMotiveHom.sourceRewriteStepCount_eq_certificateLedger_count
    {source target : TraceUnstableAnalyticMotive}
    (hom : TraceUnstableAnalyticMotiveHom source target) :
    hom.sourceRewriteStepCount =
      hom.sourceCertificateLedger.rewriteStepCount :=
  TraceLocalizedWordHom.sourceRewriteStepCount_eq_certificateLedger_count
    hom

/-- Target endpoint rewrite steps are counted by the target endpoint ledger. -/
theorem TraceUnstableAnalyticMotiveHom.targetRewriteStepCount_eq_certificateLedger_count
    {source target : TraceUnstableAnalyticMotive}
    (hom : TraceUnstableAnalyticMotiveHom source target) :
    hom.targetRewriteStepCount =
      hom.targetCertificateLedger.rewriteStepCount :=
  TraceLocalizedWordHom.targetRewriteStepCount_eq_certificateLedger_count
    hom

/-- Endpoint bookkeeping is counted by the appended endpoint ledger. -/
theorem TraceUnstableAnalyticMotiveHom.endpointTraceBookkeepingCount_eq_certificateLedger_count
    {source target : TraceUnstableAnalyticMotive}
    (hom : TraceUnstableAnalyticMotiveHom source target) :
    hom.endpointTraceBookkeepingCount =
      hom.endpointCertificateLedger.traceBookkeepingCount :=
  TraceLocalizedWordHom.endpointTraceBookkeepingCount_eq_certificateLedger_count
    hom

/-- Endpoint rewrite steps are counted by the appended endpoint ledger. -/
theorem TraceUnstableAnalyticMotiveHom.endpointRewriteStepCount_eq_certificateLedger_count
    {source target : TraceUnstableAnalyticMotive}
    (hom : TraceUnstableAnalyticMotiveHom source target) :
    hom.endpointRewriteStepCount =
      hom.endpointCertificateLedger.rewriteStepCount :=
  TraceLocalizedWordHom.endpointRewriteStepCount_eq_certificateLedger_count
    hom

end AnalyticMotives
end LFunctions
end Boundary
