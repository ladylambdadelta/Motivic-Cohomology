import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Root.TraceCorQ.Quotient.RelationWitness.Core.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Root.TraceCorQ.Quotient.RelationWitness.Ledgers.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Root.TraceCorQ.Quotient.RelationWitness.Certificates.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Root.TraceCorQ.Quotient.RelationWitness.Generators.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Root.TraceCorQ.Quotient.RelationWitness.Generators.Inputs.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Root.TraceCorQ.Quotient.RelationWitness.Generators.Candidates.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Root.TraceCorQ.Quotient.RelationWitness.Generators.Certificates.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Root.TraceCorQ.Quotient.RelationWitness.NamedCoherence.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Root.TraceCorQ.Quotient.RelationWitness.Derived.Owner

/-!
# Top-root TraceCorQ relation witnesses

This file aggregates public relation-witness surfaces for the ambient
trace-correspondence quotient.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Relation-witness aggregate: imported rectangle counts are payload lengths. -/
theorem AnalyticMotivesRoot.traceCorQRelationWitnessSummary_importedRectangleCount_eq_length
    {left right : TraceCorQQuotientCandidate}
    (witness : TraceCorQRelationWitness left right) :
    witness.importedRectangleCount =
      witness.importedRectangles.length :=
  AnalyticMotivesRoot.traceCorQRelationWitness_importedRectangleCount_eq_length_importedRectangles
    witness

/-- Relation-witness aggregate: reflexive witnesses carry the empty ledger. -/
theorem AnalyticMotivesRoot.traceCorQRelationWitnessSummary_refl_ledger
    (candidate : TraceCorQQuotientCandidate) :
    (TraceCorQRelationWitness.refl candidate).ledger =
      TraceCorQRelationLedger.empty :=
  AnalyticMotivesRoot.traceCorQRelationWitness_refl_ledger
    candidate

/-- Relation-witness aggregate: symmetric witnesses preserve their ledger. -/
theorem AnalyticMotivesRoot.traceCorQRelationWitnessSummary_symm_ledger
    {left right : TraceCorQQuotientCandidate}
    (witness : TraceCorQRelationWitness left right) :
    (TraceCorQRelationWitness.symm witness).ledger =
      witness.ledger :=
  AnalyticMotivesRoot.traceCorQRelationWitness_symm_ledger
    witness

/-- Relation-witness aggregate: transitive witnesses append ledgers. -/
theorem AnalyticMotivesRoot.traceCorQRelationWitnessSummary_trans_ledger
    {left middle right : TraceCorQQuotientCandidate}
    (first : TraceCorQRelationWitness left middle)
    (second : TraceCorQRelationWitness middle right) :
    (TraceCorQRelationWitness.trans first second).ledger =
      TraceCorQRelationLedger.append first.ledger second.ledger :=
  AnalyticMotivesRoot.traceCorQRelationWitness_trans_ledger
    first
    second

/-- Relation-witness aggregate: generated support witnesses carry singleton ledgers. -/
theorem AnalyticMotivesRoot.traceCorQRelationWitnessSummary_supportWitness_ledger
    (relation : TraceCorQRelationGenerator) :
    (TraceCorQRelationGenerator.supportWitness relation).ledger =
      TraceCorQRelationLedger.singleton relation :=
  AnalyticMotivesRoot.traceCorQRelationGenerator_supportWitness_ledger
    relation

end AnalyticMotives
end LFunctions
end Boundary
