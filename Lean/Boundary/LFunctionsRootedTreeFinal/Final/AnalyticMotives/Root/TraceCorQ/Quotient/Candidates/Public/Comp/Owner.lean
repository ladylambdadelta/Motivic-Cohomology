import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Quotient.Candidates.Public.Comp.Owner

/-!
# Top-root quotient-candidate composition laws

This file exposes concrete quotient-candidate composition laws through the
top-level `AnalyticMotivesRoot` namespace.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- The top root exposes the input of a candidate composition. -/
theorem AnalyticMotivesRoot.traceCorQQuotientCandidate_comp_input
    (left right : TraceCorQQuotientCandidate) :
    (TraceCorQQuotientCandidate.comp left right).input =
      TraceCorQQuotientInput.comp left.input right.input :=
  TraceCorQ.quotientCandidate_comp_input
    left
    right

/-- The top root exposes the formal sum of a candidate composition. -/
theorem AnalyticMotivesRoot.traceCorQQuotientCandidate_comp_formalSum
    (left right : TraceCorQQuotientCandidate) :
    (TraceCorQQuotientCandidate.comp left right).formalSum =
      TraceCorQFormalSum.comp left.formalSum right.formalSum :=
  TraceCorQ.quotientCandidate_comp_formalSum
    left
    right

/-- The top root exposes the ledger of a candidate composition. -/
theorem AnalyticMotivesRoot.traceCorQQuotientCandidate_comp_ledger
    (left right : TraceCorQQuotientCandidate) :
    (TraceCorQQuotientCandidate.comp left right).ledger =
      TraceCorQRelationLedger.append left.ledger right.ledger :=
  TraceCorQ.quotientCandidate_comp_ledger
    left
    right

/-- The top root exposes the certificate ledger of a candidate composition. -/
theorem AnalyticMotivesRoot.traceCorQQuotientCandidate_comp_certificateLedger
    (left right : TraceCorQQuotientCandidate) :
    (TraceCorQQuotientCandidate.comp left right).certificateLedger =
      ResidueChannelCertificateLedger.append
        (TraceCorQFormalSum.comp left.formalSum right.formalSum).certificateLedger
        (ResidueChannelCertificateLedger.append
          left.ledger.certificateLedger
          right.ledger.certificateLedger) :=
  TraceCorQ.quotientCandidate_comp_certificateLedger
    left
    right

/-- The top root exposes imported payload for a candidate composition. -/
theorem AnalyticMotivesRoot.traceCorQQuotientCandidate_comp_importedRectangleCount
    (left right : TraceCorQQuotientCandidate) :
    (TraceCorQQuotientCandidate.comp left right).importedRectangleCount =
      (TraceCorQFormalSum.comp
        left.formalSum
        right.formalSum).importedRectangleCount +
        (left.ledger.importedRectangleCount +
          right.ledger.importedRectangleCount) :=
  TraceCorQ.quotientCandidate_comp_importedRectangleCount
    left
    right

/-- The top root exposes imported rectangles for a candidate composition. -/
theorem AnalyticMotivesRoot.traceCorQQuotientCandidate_comp_importedRectangles
    (left right : TraceCorQQuotientCandidate) :
    (TraceCorQQuotientCandidate.comp left right).importedRectangles =
      (TraceCorQFormalSum.comp
        left.formalSum
        right.formalSum).importedRectangles ++
        (left.ledger.importedRectangles ++
          right.ledger.importedRectangles) :=
  TraceCorQ.quotientCandidate_comp_importedRectangles
    left
    right

/-- The top root exposes bookkeeping payload for a candidate composition. -/
theorem AnalyticMotivesRoot.traceCorQQuotientCandidate_comp_traceBookkeepingCount
    (left right : TraceCorQQuotientCandidate) :
    (TraceCorQQuotientCandidate.comp left right).traceBookkeepingCount =
      (TraceCorQFormalSum.comp
        left.formalSum
        right.formalSum).traceBookkeepingCount +
        (left.ledger.traceBookkeepingCount +
          right.ledger.traceBookkeepingCount) :=
  TraceCorQ.quotientCandidate_comp_traceBookkeepingCount
    left
    right

/-- The top root exposes rewrite-step payload for a candidate composition. -/
theorem AnalyticMotivesRoot.traceCorQQuotientCandidate_comp_rewriteStepCount
    (left right : TraceCorQQuotientCandidate) :
    (TraceCorQQuotientCandidate.comp left right).rewriteStepCount =
      (TraceCorQFormalSum.comp
        left.formalSum
        right.formalSum).rewriteStepCount +
        (left.ledger.rewriteStepCount +
          right.ledger.rewriteStepCount) :=
  TraceCorQ.quotientCandidate_comp_rewriteStepCount
    left
    right

/-- The top root exposes rewrite-step payload for composition with empty right side. -/
theorem AnalyticMotivesRoot.traceCorQQuotientCandidate_comp_empty_rewriteStepCount
    (candidate : TraceCorQQuotientCandidate) :
    (TraceCorQQuotientCandidate.comp
      candidate
      TraceCorQQuotientCandidate.empty).rewriteStepCount =
      0 +
        (candidate.ledger.rewriteStepCount +
          TraceCorQRelationLedger.empty.rewriteStepCount) :=
  TraceCorQ.quotientCandidate_comp_empty_rewriteStepCount
    candidate

/-- The top root exposes imported payload for composition with empty right side. -/
theorem AnalyticMotivesRoot.traceCorQQuotientCandidate_comp_empty_importedRectangleCount
    (candidate : TraceCorQQuotientCandidate) :
    (TraceCorQQuotientCandidate.comp
      candidate
      TraceCorQQuotientCandidate.empty).importedRectangleCount =
      0 +
        (candidate.ledger.importedRectangleCount +
          TraceCorQRelationLedger.empty.importedRectangleCount) :=
  TraceCorQ.quotientCandidate_comp_empty_importedRectangleCount
    candidate

/-- The top root exposes imported rectangles for composition with empty right side. -/
theorem AnalyticMotivesRoot.traceCorQQuotientCandidate_comp_empty_importedRectangles
    (candidate : TraceCorQQuotientCandidate) :
    (TraceCorQQuotientCandidate.comp
      candidate
      TraceCorQQuotientCandidate.empty).importedRectangles =
      [] ++
        (candidate.ledger.importedRectangles ++
          TraceCorQRelationLedger.empty.importedRectangles) :=
  TraceCorQ.quotientCandidate_comp_empty_importedRectangles
    candidate

end AnalyticMotives
end LFunctions
end Boundary
