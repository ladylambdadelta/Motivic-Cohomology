import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Quotient.Candidates.Comp.Owner

/-!
# Public quotient-candidate composition laws

This file exposes concrete quotient-candidate composition laws under the
`TraceCorQ` aggregate namespace.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- The trace-correspondence root exposes the input of a candidate composition. -/
theorem TraceCorQ.quotientCandidate_comp_input
    (left right : TraceCorQQuotientCandidate) :
    (TraceCorQQuotientCandidate.comp left right).input =
      TraceCorQQuotientInput.comp left.input right.input :=
  TraceCorQQuotientCandidate.comp_input
    left
    right

/-- The trace-correspondence root exposes the formal sum of a candidate composition. -/
theorem TraceCorQ.quotientCandidate_comp_formalSum
    (left right : TraceCorQQuotientCandidate) :
    (TraceCorQQuotientCandidate.comp left right).formalSum =
      TraceCorQFormalSum.comp left.formalSum right.formalSum :=
  TraceCorQQuotientCandidate.comp_formalSum
    left
    right

/-- The trace-correspondence root exposes the ledger of a candidate composition. -/
theorem TraceCorQ.quotientCandidate_comp_ledger
    (left right : TraceCorQQuotientCandidate) :
    (TraceCorQQuotientCandidate.comp left right).ledger =
      TraceCorQRelationLedger.append left.ledger right.ledger :=
  TraceCorQQuotientCandidate.comp_ledger
    left
    right

/-- The trace-correspondence root exposes the certificate ledger of a candidate composition. -/
theorem TraceCorQ.quotientCandidate_comp_certificateLedger
    (left right : TraceCorQQuotientCandidate) :
    (TraceCorQQuotientCandidate.comp left right).certificateLedger =
      ResidueChannelCertificateLedger.append
        (TraceCorQFormalSum.comp left.formalSum right.formalSum).certificateLedger
        (ResidueChannelCertificateLedger.append
          left.ledger.certificateLedger
          right.ledger.certificateLedger) :=
  TraceCorQQuotientCandidate.comp_certificateLedger
    left
    right

/-- The trace-correspondence root exposes imported payload for a candidate composition. -/
theorem TraceCorQ.quotientCandidate_comp_importedRectangleCount
    (left right : TraceCorQQuotientCandidate) :
    (TraceCorQQuotientCandidate.comp left right).importedRectangleCount =
      (TraceCorQFormalSum.comp
        left.formalSum
        right.formalSum).importedRectangleCount +
        (left.ledger.importedRectangleCount +
          right.ledger.importedRectangleCount) :=
  TraceCorQQuotientCandidate.comp_importedRectangleCount
    left
    right

/-- The trace-correspondence root exposes imported rectangles for a candidate composition. -/
theorem TraceCorQ.quotientCandidate_comp_importedRectangles
    (left right : TraceCorQQuotientCandidate) :
    (TraceCorQQuotientCandidate.comp left right).importedRectangles =
      (TraceCorQFormalSum.comp
        left.formalSum
        right.formalSum).importedRectangles ++
        (left.ledger.importedRectangles ++
          right.ledger.importedRectangles) :=
  TraceCorQQuotientCandidate.comp_importedRectangles
    left
    right

/-- The trace-correspondence root exposes bookkeeping payload for a candidate composition. -/
theorem TraceCorQ.quotientCandidate_comp_traceBookkeepingCount
    (left right : TraceCorQQuotientCandidate) :
    (TraceCorQQuotientCandidate.comp left right).traceBookkeepingCount =
      (TraceCorQFormalSum.comp
        left.formalSum
        right.formalSum).traceBookkeepingCount +
        (left.ledger.traceBookkeepingCount +
          right.ledger.traceBookkeepingCount) :=
  TraceCorQQuotientCandidate.comp_traceBookkeepingCount
    left
    right

/-- The trace-correspondence root exposes rewrite-step payload for a candidate composition. -/
theorem TraceCorQ.quotientCandidate_comp_rewriteStepCount
    (left right : TraceCorQQuotientCandidate) :
    (TraceCorQQuotientCandidate.comp left right).rewriteStepCount =
      (TraceCorQFormalSum.comp
        left.formalSum
        right.formalSum).rewriteStepCount +
        (left.ledger.rewriteStepCount +
          right.ledger.rewriteStepCount) :=
  TraceCorQQuotientCandidate.comp_rewriteStepCount
    left
    right

/-- The trace-correspondence root exposes rewrite-step payload for composition with empty right side. -/
theorem TraceCorQ.quotientCandidate_comp_empty_rewriteStepCount
    (candidate : TraceCorQQuotientCandidate) :
    (TraceCorQQuotientCandidate.comp
      candidate
      TraceCorQQuotientCandidate.empty).rewriteStepCount =
      0 +
        (candidate.ledger.rewriteStepCount +
          TraceCorQRelationLedger.empty.rewriteStepCount) :=
  TraceCorQQuotientCandidate.comp_empty_rewriteStepCount
    candidate

/-- The trace-correspondence root exposes imported payload for composition with empty right side. -/
theorem TraceCorQ.quotientCandidate_comp_empty_importedRectangleCount
    (candidate : TraceCorQQuotientCandidate) :
    (TraceCorQQuotientCandidate.comp
      candidate
      TraceCorQQuotientCandidate.empty).importedRectangleCount =
      0 +
        (candidate.ledger.importedRectangleCount +
          TraceCorQRelationLedger.empty.importedRectangleCount) :=
  TraceCorQQuotientCandidate.comp_empty_importedRectangleCount
    candidate

/-- The trace-correspondence root exposes imported rectangles for composition with empty right side. -/
theorem TraceCorQ.quotientCandidate_comp_empty_importedRectangles
    (candidate : TraceCorQQuotientCandidate) :
    (TraceCorQQuotientCandidate.comp
      candidate
      TraceCorQQuotientCandidate.empty).importedRectangles =
      [] ++
        (candidate.ledger.importedRectangles ++
          TraceCorQRelationLedger.empty.importedRectangles) :=
  TraceCorQQuotientCandidate.comp_empty_importedRectangles
    candidate

end AnalyticMotives
end LFunctions
end Boundary
