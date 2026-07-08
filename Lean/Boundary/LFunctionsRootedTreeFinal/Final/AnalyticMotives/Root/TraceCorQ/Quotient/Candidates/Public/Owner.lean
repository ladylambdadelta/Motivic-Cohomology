import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Root.TraceCorQ.Quotient.Candidates.Public.Add.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Root.TraceCorQ.Quotient.Candidates.Public.Comp.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Root.TraceCorQ.Quotient.Candidates.Public.Projections.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Root.TraceCorQ.Quotient.Candidates.Public.Smul.Owner

/-!
# Top-root public quotient-candidate surfaces

This file aggregates the public projection, additive, scalar, and composition
surfaces for quotient candidates.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Quotient-candidate public aggregate: imported rectangle counts are payload lengths. -/
theorem AnalyticMotivesRoot.traceCorQQuotientCandidate_publicSummary_importedRectangleCount_eq_length
    (candidate : TraceCorQQuotientCandidate) :
    candidate.importedRectangleCount =
      candidate.importedRectangles.length :=
  AnalyticMotivesRoot.traceCorQQuotientCandidate_importedRectangleCount_eq_length
    candidate

/-- Quotient-candidate public aggregate: addition appends the underlying formal sums. -/
theorem AnalyticMotivesRoot.traceCorQQuotientCandidate_publicSummary_add_formalSum
    (left right : TraceCorQQuotientCandidate) :
    (TraceCorQQuotientCandidate.add left right).formalSum =
      TraceCorQFormalSum.add left.formalSum right.formalSum :=
  AnalyticMotivesRoot.traceCorQQuotientCandidate_add_formalSum
    left
    right

/-- Quotient-candidate public aggregate: scalar multiplication scales the underlying formal sum. -/
theorem AnalyticMotivesRoot.traceCorQQuotientCandidate_publicSummary_smul_formalSum
    (coefficient : Rat)
    (candidate : TraceCorQQuotientCandidate) :
    (TraceCorQQuotientCandidate.smul coefficient candidate).formalSum =
      TraceCorQFormalSum.smul coefficient candidate.formalSum :=
  AnalyticMotivesRoot.traceCorQQuotientCandidate_smul_formalSum
    coefficient
    candidate

/-- Quotient-candidate public aggregate: composition composes the underlying formal sums. -/
theorem AnalyticMotivesRoot.traceCorQQuotientCandidate_publicSummary_comp_formalSum
    (left right : TraceCorQQuotientCandidate) :
    (TraceCorQQuotientCandidate.comp left right).formalSum =
      TraceCorQFormalSum.comp left.formalSum right.formalSum :=
  AnalyticMotivesRoot.traceCorQQuotientCandidate_comp_formalSum
    left
    right

/-- Quotient-candidate public aggregate: composition appends relation ledgers. -/
theorem AnalyticMotivesRoot.traceCorQQuotientCandidate_publicSummary_comp_ledger
    (left right : TraceCorQQuotientCandidate) :
    (TraceCorQQuotientCandidate.comp left right).ledger =
      TraceCorQRelationLedger.append left.ledger right.ledger :=
  AnalyticMotivesRoot.traceCorQQuotientCandidate_comp_ledger
    left
    right

/-- Quotient-candidate public aggregate: input-built candidates expose their input. -/
theorem AnalyticMotivesRoot.traceCorQQuotientCandidate_publicSummary_ofInput_input
    (input : TraceCorQQuotientInput) :
    (TraceCorQQuotientCandidate.ofInput input).input =
      input :=
  AnalyticMotivesRoot.traceCorQQuotientCandidate_ofInput_input
    input

end AnalyticMotives
end LFunctions
end Boundary
