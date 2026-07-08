import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Root.TraceCorQ.Quotient.Laws.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Root.TraceCorQ.Quotient.Candidates.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Root.TraceCorQ.Quotient.RelationClosure.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Root.TraceCorQ.Quotient.RelationWitness.NamedCoherence.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Root.TraceCorQ.Quotient.RelationWitness.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Root.TraceCorQ.Quotient.NamedCoherence.Owner

/-!
# Top-root TraceCorQ quotient surface

This file aggregates top-root public surfaces for the ambient
trace-correspondence quotient.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Top-root quotient aggregate: candidate imported rectangle counts are payload lengths. -/
theorem AnalyticMotivesRoot.traceCorQQuotientAggregate_candidate_importedRectangleCount_eq_length
    (candidate : TraceCorQQuotientCandidate) :
    candidate.importedRectangleCount =
      candidate.importedRectangles.length :=
  AnalyticMotivesRoot.traceCorQQuotientCandidateSummary_importedRectangleCount_eq_length
    candidate

/-- Top-root quotient aggregate: candidate addition appends formal sums. -/
theorem AnalyticMotivesRoot.traceCorQQuotientAggregate_candidate_add_formalSum
    (left right : TraceCorQQuotientCandidate) :
    (TraceCorQQuotientCandidate.add left right).formalSum =
      TraceCorQFormalSum.add left.formalSum right.formalSum :=
  AnalyticMotivesRoot.traceCorQQuotientCandidateSummary_add_formalSum
    left
    right

/-- Top-root quotient aggregate: candidate scalar multiplication scales formal sums. -/
theorem AnalyticMotivesRoot.traceCorQQuotientAggregate_candidate_smul_formalSum
    (coefficient : Rat)
    (candidate : TraceCorQQuotientCandidate) :
    (TraceCorQQuotientCandidate.smul coefficient candidate).formalSum =
      TraceCorQFormalSum.smul coefficient candidate.formalSum :=
  AnalyticMotivesRoot.traceCorQQuotientCandidateSummary_smul_formalSum
    coefficient
    candidate

/-- Top-root quotient aggregate: candidate composition composes formal sums. -/
theorem AnalyticMotivesRoot.traceCorQQuotientAggregate_candidate_comp_formalSum
    (left right : TraceCorQQuotientCandidate) :
    (TraceCorQQuotientCandidate.comp left right).formalSum =
      TraceCorQFormalSum.comp left.formalSum right.formalSum :=
  AnalyticMotivesRoot.traceCorQQuotientCandidateSummary_comp_formalSum
    left
    right

/-- Top-root quotient aggregate: same-formal-sum soundness descends to quotient equality. -/
theorem AnalyticMotivesRoot.traceCorQQuotientAggregate_sound_sameFormalSum
    (ledger : TraceCorQRelationLedger)
    {left right : TraceCorQQuotientCandidate}
    (same : left.formalSum = right.formalSum) :
    TraceCorQQuotient.ofCandidate left =
      TraceCorQQuotient.ofCandidate right :=
  AnalyticMotivesRoot.traceCorQQuotient_sound_sameFormalSum
    ledger
    same

/-- Top-root quotient aggregate: quotient zero is the empty candidate class. -/
theorem AnalyticMotivesRoot.traceCorQQuotientAggregate_zero_eq_ofCandidate_empty :
    TraceCorQQuotient.zero =
      TraceCorQQuotient.ofCandidate TraceCorQQuotientCandidate.empty :=
  AnalyticMotivesRoot.traceCorQQuotient_zero_eq_ofCandidate_empty

/-- Top-root quotient aggregate: scalar multiplication acts on representatives. -/
theorem AnalyticMotivesRoot.traceCorQQuotientAggregate_smul_ofCandidate
    (coefficient : Rat)
    (candidate : TraceCorQQuotientCandidate) :
    TraceCorQQuotient.smul
        coefficient
        (TraceCorQQuotient.ofCandidate candidate) =
      TraceCorQQuotient.ofCandidate
        (TraceCorQQuotientCandidate.smul coefficient candidate) :=
  AnalyticMotivesRoot.traceCorQQuotient_smul_ofCandidate
    coefficient
    candidate

/-- Top-root quotient aggregate: composition acts on representatives. -/
theorem AnalyticMotivesRoot.traceCorQQuotientAggregate_comp_ofCandidate
    (left right : TraceCorQQuotientCandidate) :
    TraceCorQQuotient.comp
        (TraceCorQQuotient.ofCandidate left)
        (TraceCorQQuotient.ofCandidate right) =
      TraceCorQQuotient.ofCandidate
        (TraceCorQQuotientCandidate.comp left right) :=
  AnalyticMotivesRoot.traceCorQQuotient_comp_ofCandidate
    left
    right

/-- Top-root quotient aggregate: Fubini formal-sum ledgers vanish in the quotient. -/
theorem AnalyticMotivesRoot.traceCorQQuotientAggregate_fubini_eq_zero
    (source target : TraceRewritePath)
    (support : TraceCorQFormalSum) :
    TraceCorQQuotient.ofFormalSumLedger
      support
      (TraceCorQRelationLedger.fubini source target support) =
      TraceCorQQuotient.zero :=
  AnalyticMotivesRoot.traceCorQQuotient_ofFormalSumLedger_fubini_eq_zero
    source
    target
    support

/-- Top-root quotient aggregate: residue-channel formal-sum ledgers vanish. -/
theorem AnalyticMotivesRoot.traceCorQQuotientAggregate_residueChannel_eq_zero
    (source target : TraceRewritePath)
    (support : TraceCorQFormalSum) :
    TraceCorQQuotient.ofFormalSumLedger
      support
      (TraceCorQRelationLedger.residueChannel source target support) =
      TraceCorQQuotient.zero :=
  AnalyticMotivesRoot.traceCorQQuotient_ofFormalSumLedger_residueChannel_eq_zero
    source
    target
    support

/-- Top-root quotient aggregate: Stokes-residue formal-sum ledgers vanish. -/
theorem AnalyticMotivesRoot.traceCorQQuotientAggregate_stokesResidue_eq_zero
    (source target : TraceRewritePath)
    (support : TraceCorQFormalSum) :
    TraceCorQQuotient.ofFormalSumLedger
      support
      (TraceCorQRelationLedger.stokesResidue source target support) =
      TraceCorQQuotient.zero :=
  AnalyticMotivesRoot.traceCorQQuotient_ofFormalSumLedger_stokesResidue_eq_zero
    source
    target
    support

/-- Top-root quotient aggregate: associativity formal-sum ledgers vanish. -/
theorem AnalyticMotivesRoot.traceCorQQuotientAggregate_associativity_eq_zero
    (source target : TraceRewritePath)
    (support : TraceCorQFormalSum) :
    TraceCorQQuotient.ofFormalSumLedger
      support
      (TraceCorQRelationLedger.associativity source target support) =
      TraceCorQQuotient.zero :=
  AnalyticMotivesRoot.traceCorQQuotient_ofFormalSumLedger_associativity_eq_zero
    source
    target
    support

end AnalyticMotives
end LFunctions
end Boundary
