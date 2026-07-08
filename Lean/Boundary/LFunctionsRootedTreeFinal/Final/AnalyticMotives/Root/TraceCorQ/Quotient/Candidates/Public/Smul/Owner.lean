import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Quotient.Candidates.Public.Smul.Owner

/-!
# Top-root quotient-candidate scalar laws

This file exposes concrete quotient-candidate scalar laws through the top-level
`AnalyticMotivesRoot` namespace.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- The top root exposes the input of a scaled candidate. -/
theorem AnalyticMotivesRoot.traceCorQQuotientCandidate_smul_input
    (coefficient : Rat)
    (candidate : TraceCorQQuotientCandidate) :
    (TraceCorQQuotientCandidate.smul coefficient candidate).input =
      TraceCorQQuotientInput.smul coefficient candidate.input :=
  TraceCorQ.quotientCandidate_smul_input
    coefficient
    candidate

/-- The top root exposes the formal sum of a scaled candidate. -/
theorem AnalyticMotivesRoot.traceCorQQuotientCandidate_smul_formalSum
    (coefficient : Rat)
    (candidate : TraceCorQQuotientCandidate) :
    (TraceCorQQuotientCandidate.smul coefficient candidate).formalSum =
      TraceCorQFormalSum.smul coefficient candidate.formalSum :=
  TraceCorQ.quotientCandidate_smul_formalSum
    coefficient
    candidate

/-- The top root exposes ledger preservation under candidate scaling. -/
theorem AnalyticMotivesRoot.traceCorQQuotientCandidate_smul_ledger
    (coefficient : Rat)
    (candidate : TraceCorQQuotientCandidate) :
    (TraceCorQQuotientCandidate.smul coefficient candidate).ledger =
      candidate.ledger :=
  TraceCorQ.quotientCandidate_smul_ledger
    coefficient
    candidate

/-- The top root exposes certificate-ledger preservation under candidate scaling. -/
theorem AnalyticMotivesRoot.traceCorQQuotientCandidate_smul_certificateLedger
    (coefficient : Rat)
    (candidate : TraceCorQQuotientCandidate) :
    (TraceCorQQuotientCandidate.smul coefficient candidate).certificateLedger =
      candidate.certificateLedger :=
  TraceCorQ.quotientCandidate_smul_certificateLedger
    coefficient
    candidate

/-- The top root exposes imported-payload preservation under candidate scaling. -/
theorem AnalyticMotivesRoot.traceCorQQuotientCandidate_smul_importedRectangleCount
    (coefficient : Rat)
    (candidate : TraceCorQQuotientCandidate) :
    (TraceCorQQuotientCandidate.smul coefficient candidate).importedRectangleCount =
      candidate.importedRectangleCount :=
  TraceCorQ.quotientCandidate_smul_importedRectangleCount
    coefficient
    candidate

/-- The top root exposes imported-rectangle preservation under candidate scaling. -/
theorem AnalyticMotivesRoot.traceCorQQuotientCandidate_smul_importedRectangles
    (coefficient : Rat)
    (candidate : TraceCorQQuotientCandidate) :
    (TraceCorQQuotientCandidate.smul coefficient candidate).importedRectangles =
      candidate.importedRectangles :=
  TraceCorQ.quotientCandidate_smul_importedRectangles
    coefficient
    candidate

/-- The top root exposes bookkeeping preservation under candidate scaling. -/
theorem AnalyticMotivesRoot.traceCorQQuotientCandidate_smul_traceBookkeepingCount
    (coefficient : Rat)
    (candidate : TraceCorQQuotientCandidate) :
    (TraceCorQQuotientCandidate.smul coefficient candidate).traceBookkeepingCount =
      candidate.traceBookkeepingCount :=
  TraceCorQ.quotientCandidate_smul_traceBookkeepingCount
    coefficient
    candidate

/-- The top root exposes rewrite-step preservation under candidate scaling. -/
theorem AnalyticMotivesRoot.traceCorQQuotientCandidate_smul_rewriteStepCount
    (coefficient : Rat)
    (candidate : TraceCorQQuotientCandidate) :
    (TraceCorQQuotientCandidate.smul coefficient candidate).rewriteStepCount =
      candidate.rewriteStepCount :=
  TraceCorQ.quotientCandidate_smul_rewriteStepCount
    coefficient
    candidate

end AnalyticMotives
end LFunctions
end Boundary
