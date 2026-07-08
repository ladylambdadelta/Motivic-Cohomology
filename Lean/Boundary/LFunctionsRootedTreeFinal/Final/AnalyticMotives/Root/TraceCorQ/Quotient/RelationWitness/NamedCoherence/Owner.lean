import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Quotient.RelationWitness.Generators.NamedCoherence.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Root.TraceCorQ.Quotient.RelationWitness.NamedCoherence.Inputs.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Root.TraceCorQ.Quotient.RelationWitness.NamedCoherence.Candidates.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Root.TraceCorQ.Quotient.RelationWitness.NamedCoherence.Payload.Owner

/-!
# Top-root named-coherence relation witnesses

This file exposes the canonical finite quotient-relation witnesses generated
by named coherence cells.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- The top root exposes the support candidate of a Fubini coherence relation. -/
def AnalyticMotivesRoot.traceCorQRelationGenerator_fubiniSupportCandidate
    (source target : TraceRewritePath)
    (support : TraceCorQFormalSum) :
    TraceCorQQuotientCandidate :=
  TraceCorQRelationGenerator.fubiniSupportCandidate
    source
    target
    support

/-- The top root exposes the support candidate of a schedule-exchange coherence relation. -/
def AnalyticMotivesRoot.traceCorQRelationGenerator_scheduleExchangeSupportCandidate
    (source target : TraceRewritePath)
    (support : TraceCorQFormalSum) :
    TraceCorQQuotientCandidate :=
  TraceCorQRelationGenerator.scheduleExchangeSupportCandidate
    source
    target
    support

/-- The top root exposes the support candidate of a residue-channel coherence relation. -/
def AnalyticMotivesRoot.traceCorQRelationGenerator_residueChannelSupportCandidate
    (source target : TraceRewritePath)
    (support : TraceCorQFormalSum) :
    TraceCorQQuotientCandidate :=
  TraceCorQRelationGenerator.residueChannelSupportCandidate
    source
    target
    support

/-- The top root exposes the support candidate of a Stokes-residue coherence relation. -/
def AnalyticMotivesRoot.traceCorQRelationGenerator_stokesResidueSupportCandidate
    (source target : TraceRewritePath)
    (support : TraceCorQFormalSum) :
    TraceCorQQuotientCandidate :=
  TraceCorQRelationGenerator.stokesResidueSupportCandidate
    source
    target
    support

/-- The top root exposes the support candidate of a refinement coherence relation. -/
def AnalyticMotivesRoot.traceCorQRelationGenerator_refinementSupportCandidate
    (source target : TraceRewritePath)
    (support : TraceCorQFormalSum) :
    TraceCorQQuotientCandidate :=
  TraceCorQRelationGenerator.refinementSupportCandidate
    source
    target
    support

/-- The top root exposes the support candidate of an associativity coherence relation. -/
def AnalyticMotivesRoot.traceCorQRelationGenerator_associativitySupportCandidate
    (source target : TraceRewritePath)
    (support : TraceCorQFormalSum) :
    TraceCorQQuotientCandidate :=
  TraceCorQRelationGenerator.associativitySupportCandidate
    source
    target
    support

/-- The top root exposes the support candidate of a left-identity coherence relation. -/
def AnalyticMotivesRoot.traceCorQRelationGenerator_leftIdentitySupportCandidate
    (source target : TraceRewritePath)
    (support : TraceCorQFormalSum) :
    TraceCorQQuotientCandidate :=
  TraceCorQRelationGenerator.leftIdentitySupportCandidate
    source
    target
    support

/-- The top root exposes the support candidate of a right-identity coherence relation. -/
def AnalyticMotivesRoot.traceCorQRelationGenerator_rightIdentitySupportCandidate
    (source target : TraceRewritePath)
    (support : TraceCorQFormalSum) :
    TraceCorQQuotientCandidate :=
  TraceCorQRelationGenerator.rightIdentitySupportCandidate
    source
    target
    support

/-- The top root exposes the support witness of a Fubini coherence relation. -/
def AnalyticMotivesRoot.traceCorQRelationGenerator_fubiniSupportWitness
    (source target : TraceRewritePath)
    (support : TraceCorQFormalSum) :
    TraceCorQRelationWitness
      (TraceCorQRelationGenerator.fubiniSupportCandidate
        source
        target
        support)
      TraceCorQQuotientCandidate.empty :=
  TraceCorQRelationGenerator.fubiniSupportWitness
    source
    target
    support

/-- The top root exposes the support witness of a schedule-exchange coherence relation. -/
def AnalyticMotivesRoot.traceCorQRelationGenerator_scheduleExchangeSupportWitness
    (source target : TraceRewritePath)
    (support : TraceCorQFormalSum) :
    TraceCorQRelationWitness
      (TraceCorQRelationGenerator.scheduleExchangeSupportCandidate
        source
        target
        support)
      TraceCorQQuotientCandidate.empty :=
  TraceCorQRelationGenerator.scheduleExchangeSupportWitness
    source
    target
    support

/-- The top root exposes the support witness of a residue-channel coherence relation. -/
def AnalyticMotivesRoot.traceCorQRelationGenerator_residueChannelSupportWitness
    (source target : TraceRewritePath)
    (support : TraceCorQFormalSum) :
    TraceCorQRelationWitness
      (TraceCorQRelationGenerator.residueChannelSupportCandidate
        source
        target
        support)
      TraceCorQQuotientCandidate.empty :=
  TraceCorQRelationGenerator.residueChannelSupportWitness
    source
    target
    support

/-- The top root exposes the support witness of a Stokes-residue coherence relation. -/
def AnalyticMotivesRoot.traceCorQRelationGenerator_stokesResidueSupportWitness
    (source target : TraceRewritePath)
    (support : TraceCorQFormalSum) :
    TraceCorQRelationWitness
      (TraceCorQRelationGenerator.stokesResidueSupportCandidate
        source
        target
        support)
      TraceCorQQuotientCandidate.empty :=
  TraceCorQRelationGenerator.stokesResidueSupportWitness
    source
    target
    support

/-- The top root exposes the support witness of a refinement coherence relation. -/
def AnalyticMotivesRoot.traceCorQRelationGenerator_refinementSupportWitness
    (source target : TraceRewritePath)
    (support : TraceCorQFormalSum) :
    TraceCorQRelationWitness
      (TraceCorQRelationGenerator.refinementSupportCandidate
        source
        target
        support)
      TraceCorQQuotientCandidate.empty :=
  TraceCorQRelationGenerator.refinementSupportWitness
    source
    target
    support

/-- The top root exposes the support witness of an associativity coherence relation. -/
def AnalyticMotivesRoot.traceCorQRelationGenerator_associativitySupportWitness
    (source target : TraceRewritePath)
    (support : TraceCorQFormalSum) :
    TraceCorQRelationWitness
      (TraceCorQRelationGenerator.associativitySupportCandidate
        source
        target
        support)
      TraceCorQQuotientCandidate.empty :=
  TraceCorQRelationGenerator.associativitySupportWitness
    source
    target
    support

/-- The top root exposes the support witness of a left-identity coherence relation. -/
def AnalyticMotivesRoot.traceCorQRelationGenerator_leftIdentitySupportWitness
    (source target : TraceRewritePath)
    (support : TraceCorQFormalSum) :
    TraceCorQRelationWitness
      (TraceCorQRelationGenerator.leftIdentitySupportCandidate
        source
        target
        support)
      TraceCorQQuotientCandidate.empty :=
  TraceCorQRelationGenerator.leftIdentitySupportWitness
    source
    target
    support

/-- The top root exposes the support witness of a right-identity coherence relation. -/
def AnalyticMotivesRoot.traceCorQRelationGenerator_rightIdentitySupportWitness
    (source target : TraceRewritePath)
    (support : TraceCorQFormalSum) :
    TraceCorQRelationWitness
      (TraceCorQRelationGenerator.rightIdentitySupportCandidate
        source
        target
        support)
      TraceCorQQuotientCandidate.empty :=
  TraceCorQRelationGenerator.rightIdentitySupportWitness
    source
    target
    support

/-- The top root exposes the singleton ledger of a Fubini support witness. -/
theorem AnalyticMotivesRoot.traceCorQRelationGenerator_fubiniSupportWitness_ledger
    (source target : TraceRewritePath)
    (support : TraceCorQFormalSum) :
    (TraceCorQRelationGenerator.fubiniSupportWitness
      source
      target
      support).ledger =
      TraceCorQRelationLedger.fubini source target support :=
  TraceCorQRelationGenerator.fubiniSupportWitness_ledger
    source
    target
    support

/-- The top root exposes the singleton ledger of a schedule-exchange support witness. -/
theorem AnalyticMotivesRoot.traceCorQRelationGenerator_scheduleExchangeSupportWitness_ledger
    (source target : TraceRewritePath)
    (support : TraceCorQFormalSum) :
    (TraceCorQRelationGenerator.scheduleExchangeSupportWitness
      source
      target
      support).ledger =
      TraceCorQRelationLedger.scheduleExchange source target support :=
  TraceCorQRelationGenerator.scheduleExchangeSupportWitness_ledger
    source
    target
    support

/-- The top root exposes the singleton ledger of a residue-channel support witness. -/
theorem AnalyticMotivesRoot.traceCorQRelationGenerator_residueChannelSupportWitness_ledger
    (source target : TraceRewritePath)
    (support : TraceCorQFormalSum) :
    (TraceCorQRelationGenerator.residueChannelSupportWitness
      source
      target
      support).ledger =
      TraceCorQRelationLedger.residueChannel source target support :=
  TraceCorQRelationGenerator.residueChannelSupportWitness_ledger
    source
    target
    support

/-- The top root exposes the singleton ledger of a Stokes-residue support witness. -/
theorem AnalyticMotivesRoot.traceCorQRelationGenerator_stokesResidueSupportWitness_ledger
    (source target : TraceRewritePath)
    (support : TraceCorQFormalSum) :
    (TraceCorQRelationGenerator.stokesResidueSupportWitness
      source
      target
      support).ledger =
      TraceCorQRelationLedger.stokesResidue source target support :=
  TraceCorQRelationGenerator.stokesResidueSupportWitness_ledger
    source
    target
    support

/-- The top root exposes the singleton ledger of a refinement support witness. -/
theorem AnalyticMotivesRoot.traceCorQRelationGenerator_refinementSupportWitness_ledger
    (source target : TraceRewritePath)
    (support : TraceCorQFormalSum) :
    (TraceCorQRelationGenerator.refinementSupportWitness
      source
      target
      support).ledger =
      TraceCorQRelationLedger.refinement source target support :=
  TraceCorQRelationGenerator.refinementSupportWitness_ledger
    source
    target
    support

/-- The top root exposes the singleton ledger of an associativity support witness. -/
theorem AnalyticMotivesRoot.traceCorQRelationGenerator_associativitySupportWitness_ledger
    (source target : TraceRewritePath)
    (support : TraceCorQFormalSum) :
    (TraceCorQRelationGenerator.associativitySupportWitness
      source
      target
      support).ledger =
      TraceCorQRelationLedger.associativity source target support :=
  TraceCorQRelationGenerator.associativitySupportWitness_ledger
    source
    target
    support

/-- The top root exposes the singleton ledger of a left-identity support witness. -/
theorem AnalyticMotivesRoot.traceCorQRelationGenerator_leftIdentitySupportWitness_ledger
    (source target : TraceRewritePath)
    (support : TraceCorQFormalSum) :
    (TraceCorQRelationGenerator.leftIdentitySupportWitness
      source
      target
      support).ledger =
      TraceCorQRelationLedger.leftIdentity source target support :=
  TraceCorQRelationGenerator.leftIdentitySupportWitness_ledger
    source
    target
    support

/-- The top root exposes the singleton ledger of a right-identity support witness. -/
theorem AnalyticMotivesRoot.traceCorQRelationGenerator_rightIdentitySupportWitness_ledger
    (source target : TraceRewritePath)
    (support : TraceCorQFormalSum) :
    (TraceCorQRelationGenerator.rightIdentitySupportWitness
      source
      target
      support).ledger =
      TraceCorQRelationLedger.rightIdentity source target support :=
  TraceCorQRelationGenerator.rightIdentitySupportWitness_ledger
    source
    target
    support

end AnalyticMotives
end LFunctions
end Boundary
