import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Unstable.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.LocalizationInput.WordQuotient.Category.Payload.TraceCalculus.Owner

/-!
# Trace-calculus object payload in the unstable envelope

This file exposes certificate-ledger, trace-bookkeeping, and rewrite-step
payload carried by arbitrary unstable analytic motives.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- The analytic certificate ledger carried by an unstable analytic motive. -/
def TraceUnstableAnalyticMotive.certificateLedger
    (object : TraceUnstableAnalyticMotive) :
    ResidueChannelCertificateLedger :=
  TraceLocalizedWordObject.certificateLedger object

/-- Trace-bookkeeping payload carried by an unstable analytic motive. -/
def TraceUnstableAnalyticMotive.traceBookkeepingCount
    (object : TraceUnstableAnalyticMotive) :
    Nat :=
  TraceLocalizedWordObject.traceBookkeepingCount object

/-- Rewrite-step payload carried by an unstable analytic motive. -/
def TraceUnstableAnalyticMotive.rewriteStepCount
    (object : TraceUnstableAnalyticMotive) :
    Nat :=
  TraceLocalizedWordObject.rewriteStepCount object

/-- Wrapping a trace object preserves trace-bookkeeping payload. -/
theorem TraceUnstableAnalyticMotive.ofTraceObject_traceBookkeepingCount
    (object : TraceCorQObject) :
    (TraceUnstableAnalyticMotive.ofTraceObject object).traceBookkeepingCount =
      object.traceBookkeepingCount :=
  TraceLocalizedWordObject.ofTraceObject_traceBookkeepingCount
    object

/-- Wrapping a trace object preserves rewrite-step payload. -/
theorem TraceUnstableAnalyticMotive.ofTraceObject_rewriteStepCount
    (object : TraceCorQObject) :
    (TraceUnstableAnalyticMotive.ofTraceObject object).rewriteStepCount =
      object.rewriteStepCount :=
  TraceLocalizedWordObject.ofTraceObject_rewriteStepCount
    object

/-- Wrapping a trace object preserves analytic certificate ledgers. -/
theorem TraceUnstableAnalyticMotive.ofTraceObject_certificateLedger
    (object : TraceCorQObject) :
    (TraceUnstableAnalyticMotive.ofTraceObject object).certificateLedger =
      object.certificateLedger :=
  TraceLocalizedWordObject.ofTraceObject_certificateLedger
    object

end AnalyticMotives
end LFunctions
end Boundary
