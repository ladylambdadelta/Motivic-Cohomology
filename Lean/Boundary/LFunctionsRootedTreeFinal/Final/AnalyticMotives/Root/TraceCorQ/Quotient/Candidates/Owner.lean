import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Root.TraceCorQ.Quotient.Candidates.Public.Owner

/-!
# Top-root TraceCorQ quotient candidates

This file aggregates the top-root projection, additive, scalar, and composition
surfaces for concrete quotient candidates.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Quotient-candidate aggregate: imported rectangle counts are payload lengths. -/
theorem AnalyticMotivesRoot.traceCorQQuotientCandidateSummary_importedRectangleCount_eq_length
    (candidate : TraceCorQQuotientCandidate) :
    candidate.importedRectangleCount =
      candidate.importedRectangles.length :=
  AnalyticMotivesRoot.traceCorQQuotientCandidate_publicSummary_importedRectangleCount_eq_length
    candidate

/-- Quotient-candidate aggregate: addition appends underlying formal sums. -/
theorem AnalyticMotivesRoot.traceCorQQuotientCandidateSummary_add_formalSum
    (left right : TraceCorQQuotientCandidate) :
    (TraceCorQQuotientCandidate.add left right).formalSum =
      TraceCorQFormalSum.add left.formalSum right.formalSum :=
  AnalyticMotivesRoot.traceCorQQuotientCandidate_publicSummary_add_formalSum
    left
    right

/-- Quotient-candidate aggregate: scalar multiplication scales the underlying formal sum. -/
theorem AnalyticMotivesRoot.traceCorQQuotientCandidateSummary_smul_formalSum
    (coefficient : Rat)
    (candidate : TraceCorQQuotientCandidate) :
    (TraceCorQQuotientCandidate.smul coefficient candidate).formalSum =
      TraceCorQFormalSum.smul coefficient candidate.formalSum :=
  AnalyticMotivesRoot.traceCorQQuotientCandidate_publicSummary_smul_formalSum
    coefficient
    candidate

/-- Quotient-candidate aggregate: composition composes the underlying formal sums. -/
theorem AnalyticMotivesRoot.traceCorQQuotientCandidateSummary_comp_formalSum
    (left right : TraceCorQQuotientCandidate) :
    (TraceCorQQuotientCandidate.comp left right).formalSum =
      TraceCorQFormalSum.comp left.formalSum right.formalSum :=
  AnalyticMotivesRoot.traceCorQQuotientCandidate_publicSummary_comp_formalSum
    left
    right

/-- Quotient-candidate aggregate: composition appends relation ledgers. -/
theorem AnalyticMotivesRoot.traceCorQQuotientCandidateSummary_comp_ledger
    (left right : TraceCorQQuotientCandidate) :
    (TraceCorQQuotientCandidate.comp left right).ledger =
      TraceCorQRelationLedger.append left.ledger right.ledger :=
  AnalyticMotivesRoot.traceCorQQuotientCandidate_publicSummary_comp_ledger
    left
    right

end AnalyticMotives
end LFunctions
end Boundary
