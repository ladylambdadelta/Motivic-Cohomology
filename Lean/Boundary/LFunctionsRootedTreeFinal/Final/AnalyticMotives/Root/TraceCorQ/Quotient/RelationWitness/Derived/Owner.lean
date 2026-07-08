import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Quotient.RelationWitness.Derived.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Root.TraceCorQ.Quotient.RelationWitness.Generators.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Root.TraceCorQ.Quotient.RelationWitness.Generators.Inputs.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Root.TraceCorQ.Quotient.RelationWitness.Generators.Candidates.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Root.TraceCorQ.Quotient.RelationWitness.Generators.Certificates.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Root.TraceCorQ.Quotient.RelationWitness.Generators.NamedCoherence.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Root.TraceCorQ.Quotient.RelationWitness.Certificates.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Root.TraceCorQ.Quotient.RelationWitness.NamedCoherence.Owner

/-!
# Top-root derived relation witnesses

This file records the public root boundary for concrete relation witnesses
derived from generator, certificate, candidate, and named-coherence payload
layers.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Derived relation-witness aggregate: generated support candidates have singleton ledgers. -/
theorem AnalyticMotivesRoot.traceCorQRelationWitnessDerived_supportCandidate_ledger
    (relation : TraceCorQRelationGenerator) :
    (TraceCorQRelationGenerator.supportCandidate relation).ledger =
      TraceCorQRelationLedger.singleton relation :=
  AnalyticMotivesRoot.traceCorQRelationGenerator_supportCandidate_ledger
    relation

/-- Derived relation-witness aggregate: generated support witnesses are built from their closure. -/
theorem AnalyticMotivesRoot.traceCorQRelationWitnessDerived_supportWitness_eq_ofClosure
    (relation : TraceCorQRelationGenerator) :
    TraceCorQRelationGenerator.supportWitness relation =
      TraceCorQRelationWitness.ofLedgerDerivation
        (TraceCorQRelationLedger.singleton relation)
        (TraceCorQRelationGenerator.supportClosure relation) :=
  AnalyticMotivesRoot.traceCorQRelationGenerator_supportWitness_eq_ofClosure
    relation

/-- Derived relation-witness aggregate: generated support witnesses carry singleton ledgers. -/
theorem AnalyticMotivesRoot.traceCorQRelationWitnessDerived_supportWitness_ledger
    (relation : TraceCorQRelationGenerator) :
    (TraceCorQRelationGenerator.supportWitness relation).ledger =
      TraceCorQRelationLedger.singleton relation :=
  AnalyticMotivesRoot.traceCorQRelationGenerator_supportWitness_ledger
    relation

/-- Derived relation-witness aggregate: support-witness imported count is counted by its ledger. -/
theorem AnalyticMotivesRoot.traceCorQRelationWitnessDerived_supportWitness_importedRectangleCount_eq_ledger
    (relation : TraceCorQRelationGenerator) :
    (TraceCorQRelationGenerator.supportWitness relation).importedRectangleCount =
      (TraceCorQRelationGenerator.supportWitness relation).ledger.importedRectangleCount :=
  AnalyticMotivesRoot.traceCorQRelationWitness_importedRectangleCount_eq_ledger
    (TraceCorQRelationGenerator.supportWitness relation)

/-- Derived relation-witness aggregate: support-witness rewrite count is counted by its ledger. -/
theorem AnalyticMotivesRoot.traceCorQRelationWitnessDerived_supportWitness_rewriteStepCount_eq_ledger
    (relation : TraceCorQRelationGenerator) :
    (TraceCorQRelationGenerator.supportWitness relation).rewriteStepCount =
      (TraceCorQRelationGenerator.supportWitness relation).ledger.rewriteStepCount :=
  AnalyticMotivesRoot.traceCorQRelationWitness_rewriteStepCount_eq_ledger
    (TraceCorQRelationGenerator.supportWitness relation)

end AnalyticMotives
end LFunctions
end Boundary
