import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Quotient.Candidates.Smul.Owner

/-!
# Public quotient-candidate scalar laws

This file exposes concrete quotient-candidate scalar laws under the `TraceCorQ`
aggregate namespace.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- The trace-correspondence root exposes the input of a scaled candidate. -/
theorem TraceCorQ.quotientCandidate_smul_input
    (coefficient : Rat)
    (candidate : TraceCorQQuotientCandidate) :
    (TraceCorQQuotientCandidate.smul coefficient candidate).input =
      TraceCorQQuotientInput.smul coefficient candidate.input :=
  TraceCorQQuotientCandidate.smul_input
    coefficient
    candidate

/-- The trace-correspondence root exposes the formal sum of a scaled candidate. -/
theorem TraceCorQ.quotientCandidate_smul_formalSum
    (coefficient : Rat)
    (candidate : TraceCorQQuotientCandidate) :
    (TraceCorQQuotientCandidate.smul coefficient candidate).formalSum =
      TraceCorQFormalSum.smul coefficient candidate.formalSum :=
  TraceCorQQuotientCandidate.smul_formalSum
    coefficient
    candidate

/-- The trace-correspondence root exposes ledger preservation under candidate scaling. -/
theorem TraceCorQ.quotientCandidate_smul_ledger
    (coefficient : Rat)
    (candidate : TraceCorQQuotientCandidate) :
    (TraceCorQQuotientCandidate.smul coefficient candidate).ledger =
      candidate.ledger :=
  TraceCorQQuotientCandidate.smul_ledger
    coefficient
    candidate

/-- The trace-correspondence root exposes certificate-ledger preservation under candidate scaling. -/
theorem TraceCorQ.quotientCandidate_smul_certificateLedger
    (coefficient : Rat)
    (candidate : TraceCorQQuotientCandidate) :
    (TraceCorQQuotientCandidate.smul coefficient candidate).certificateLedger =
      candidate.certificateLedger :=
  TraceCorQQuotientCandidate.smul_certificateLedger
    coefficient
    candidate

/-- The trace-correspondence root exposes imported-payload preservation under candidate scaling. -/
theorem TraceCorQ.quotientCandidate_smul_importedRectangleCount
    (coefficient : Rat)
    (candidate : TraceCorQQuotientCandidate) :
    (TraceCorQQuotientCandidate.smul coefficient candidate).importedRectangleCount =
      candidate.importedRectangleCount :=
  TraceCorQQuotientCandidate.smul_importedRectangleCount
    coefficient
    candidate

/-- The trace-correspondence root exposes imported-rectangle preservation under candidate scaling. -/
theorem TraceCorQ.quotientCandidate_smul_importedRectangles
    (coefficient : Rat)
    (candidate : TraceCorQQuotientCandidate) :
    (TraceCorQQuotientCandidate.smul coefficient candidate).importedRectangles =
      candidate.importedRectangles :=
  TraceCorQQuotientCandidate.smul_importedRectangles
    coefficient
    candidate

/-- The trace-correspondence root exposes bookkeeping preservation under candidate scaling. -/
theorem TraceCorQ.quotientCandidate_smul_traceBookkeepingCount
    (coefficient : Rat)
    (candidate : TraceCorQQuotientCandidate) :
    (TraceCorQQuotientCandidate.smul coefficient candidate).traceBookkeepingCount =
      candidate.traceBookkeepingCount :=
  TraceCorQQuotientCandidate.smul_traceBookkeepingCount
    coefficient
    candidate

/-- The trace-correspondence root exposes rewrite-step preservation under candidate scaling. -/
theorem TraceCorQ.quotientCandidate_smul_rewriteStepCount
    (coefficient : Rat)
    (candidate : TraceCorQQuotientCandidate) :
    (TraceCorQQuotientCandidate.smul coefficient candidate).rewriteStepCount =
      candidate.rewriteStepCount :=
  TraceCorQQuotientCandidate.smul_rewriteStepCount
    coefficient
    candidate

end AnalyticMotives
end LFunctions
end Boundary
