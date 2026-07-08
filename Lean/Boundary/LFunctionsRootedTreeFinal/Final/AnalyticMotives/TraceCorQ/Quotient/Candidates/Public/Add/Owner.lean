import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Quotient.Candidates.Add.Owner

/-!
# Public quotient-candidate addition laws

This file exposes concrete quotient-candidate addition laws under the
`TraceCorQ` aggregate namespace.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- The trace-correspondence root exposes the input of a candidate sum. -/
theorem TraceCorQ.quotientCandidate_add_input
    (left right : TraceCorQQuotientCandidate) :
    (TraceCorQQuotientCandidate.add left right).input =
      TraceCorQQuotientInput.add left.input right.input :=
  TraceCorQQuotientCandidate.add_input
    left
    right

/-- The trace-correspondence root exposes the formal sum of a candidate sum. -/
theorem TraceCorQ.quotientCandidate_add_formalSum
    (left right : TraceCorQQuotientCandidate) :
    (TraceCorQQuotientCandidate.add left right).formalSum =
      TraceCorQFormalSum.add left.formalSum right.formalSum :=
  TraceCorQQuotientCandidate.add_formalSum
    left
    right

/-- The trace-correspondence root exposes the ledger of a candidate sum. -/
theorem TraceCorQ.quotientCandidate_add_ledger
    (left right : TraceCorQQuotientCandidate) :
    (TraceCorQQuotientCandidate.add left right).ledger =
      TraceCorQRelationLedger.append left.ledger right.ledger :=
  TraceCorQQuotientCandidate.add_ledger
    left
    right

/-- The trace-correspondence root exposes the certificate ledger of a candidate sum. -/
theorem TraceCorQ.quotientCandidate_add_certificateLedger
    (left right : TraceCorQQuotientCandidate) :
    (TraceCorQQuotientCandidate.add left right).certificateLedger =
      ResidueChannelCertificateLedger.append
        (ResidueChannelCertificateLedger.append
          left.formalSum.certificateLedger
          right.formalSum.certificateLedger)
        (ResidueChannelCertificateLedger.append
          left.ledger.certificateLedger
          right.ledger.certificateLedger) :=
  TraceCorQQuotientCandidate.add_certificateLedger
    left
    right

/-- The trace-correspondence root exposes imported payload for a candidate sum. -/
theorem TraceCorQ.quotientCandidate_add_importedRectangleCount
    (left right : TraceCorQQuotientCandidate) :
    (TraceCorQQuotientCandidate.add left right).importedRectangleCount =
      (left.formalSum.importedRectangleCount +
        right.formalSum.importedRectangleCount) +
        (left.ledger.importedRectangleCount +
          right.ledger.importedRectangleCount) :=
  TraceCorQQuotientCandidate.add_importedRectangleCount
    left
    right

/-- The trace-correspondence root exposes imported rectangles for a candidate sum. -/
theorem TraceCorQ.quotientCandidate_add_importedRectangles
    (left right : TraceCorQQuotientCandidate) :
    (TraceCorQQuotientCandidate.add left right).importedRectangles =
      (left.formalSum.importedRectangles ++
        right.formalSum.importedRectangles) ++
        (left.ledger.importedRectangles ++
          right.ledger.importedRectangles) :=
  TraceCorQQuotientCandidate.add_importedRectangles
    left
    right

/-- The trace-correspondence root exposes bookkeeping payload for a candidate sum. -/
theorem TraceCorQ.quotientCandidate_add_traceBookkeepingCount
    (left right : TraceCorQQuotientCandidate) :
    (TraceCorQQuotientCandidate.add left right).traceBookkeepingCount =
      (left.formalSum.traceBookkeepingCount +
        right.formalSum.traceBookkeepingCount) +
        (left.ledger.traceBookkeepingCount +
          right.ledger.traceBookkeepingCount) :=
  TraceCorQQuotientCandidate.add_traceBookkeepingCount
    left
    right

/-- The trace-correspondence root exposes rewrite-step payload for a candidate sum. -/
theorem TraceCorQ.quotientCandidate_add_rewriteStepCount
    (left right : TraceCorQQuotientCandidate) :
    (TraceCorQQuotientCandidate.add left right).rewriteStepCount =
      (left.formalSum.rewriteStepCount +
        right.formalSum.rewriteStepCount) +
        (left.ledger.rewriteStepCount +
          right.ledger.rewriteStepCount) :=
  TraceCorQQuotientCandidate.add_rewriteStepCount
    left
    right

end AnalyticMotives
end LFunctions
end Boundary
