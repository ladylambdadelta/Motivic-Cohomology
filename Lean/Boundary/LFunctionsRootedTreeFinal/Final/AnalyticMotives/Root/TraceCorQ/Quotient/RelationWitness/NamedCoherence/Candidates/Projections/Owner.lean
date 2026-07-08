import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Quotient.RelationWitness.Generators.NamedCoherence.Candidates.Projections.Owner

/-!
# Top-root named-coherence candidate projections

This file exposes the formal-support and singleton-ledger projections for
named-coherence support candidates.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- The top root exposes the formal support of a Fubini support candidate. -/
theorem AnalyticMotivesRoot.traceCorQRelationGenerator_fubiniSupportCandidate_formalSum
    (source target : TraceRewritePath)
    (support : TraceCorQFormalSum) :
    (TraceCorQRelationGenerator.fubiniSupportCandidate
      source
      target
      support).formalSum =
      support :=
  TraceCorQRelationGenerator.fubiniSupportCandidate_formalSum
    source
    target
    support

/-- The top root exposes the singleton ledger of a Fubini support candidate. -/
theorem AnalyticMotivesRoot.traceCorQRelationGenerator_fubiniSupportCandidate_ledger
    (source target : TraceRewritePath)
    (support : TraceCorQFormalSum) :
    (TraceCorQRelationGenerator.fubiniSupportCandidate
      source
      target
      support).ledger =
      TraceCorQRelationLedger.fubini source target support :=
  TraceCorQRelationGenerator.fubiniSupportCandidate_ledger
    source
    target
    support

/-- The top root exposes the formal support of a schedule-exchange support candidate. -/
theorem AnalyticMotivesRoot.traceCorQRelationGenerator_scheduleExchangeSupportCandidate_formalSum
    (source target : TraceRewritePath)
    (support : TraceCorQFormalSum) :
    (TraceCorQRelationGenerator.scheduleExchangeSupportCandidate
      source
      target
      support).formalSum =
      support :=
  TraceCorQRelationGenerator.scheduleExchangeSupportCandidate_formalSum
    source
    target
    support

/-- The top root exposes the singleton ledger of a schedule-exchange support candidate. -/
theorem AnalyticMotivesRoot.traceCorQRelationGenerator_scheduleExchangeSupportCandidate_ledger
    (source target : TraceRewritePath)
    (support : TraceCorQFormalSum) :
    (TraceCorQRelationGenerator.scheduleExchangeSupportCandidate
      source
      target
      support).ledger =
      TraceCorQRelationLedger.scheduleExchange source target support :=
  TraceCorQRelationGenerator.scheduleExchangeSupportCandidate_ledger
    source
    target
    support

/-- The top root exposes the formal support of a residue-channel support candidate. -/
theorem AnalyticMotivesRoot.traceCorQRelationGenerator_residueChannelSupportCandidate_formalSum
    (source target : TraceRewritePath)
    (support : TraceCorQFormalSum) :
    (TraceCorQRelationGenerator.residueChannelSupportCandidate
      source
      target
      support).formalSum =
      support :=
  TraceCorQRelationGenerator.residueChannelSupportCandidate_formalSum
    source
    target
    support

/-- The top root exposes the singleton ledger of a residue-channel support candidate. -/
theorem AnalyticMotivesRoot.traceCorQRelationGenerator_residueChannelSupportCandidate_ledger
    (source target : TraceRewritePath)
    (support : TraceCorQFormalSum) :
    (TraceCorQRelationGenerator.residueChannelSupportCandidate
      source
      target
      support).ledger =
      TraceCorQRelationLedger.residueChannel source target support :=
  TraceCorQRelationGenerator.residueChannelSupportCandidate_ledger
    source
    target
    support

/-- The top root exposes the formal support of a Stokes-residue support candidate. -/
theorem AnalyticMotivesRoot.traceCorQRelationGenerator_stokesResidueSupportCandidate_formalSum
    (source target : TraceRewritePath)
    (support : TraceCorQFormalSum) :
    (TraceCorQRelationGenerator.stokesResidueSupportCandidate
      source
      target
      support).formalSum =
      support :=
  TraceCorQRelationGenerator.stokesResidueSupportCandidate_formalSum
    source
    target
    support

/-- The top root exposes the singleton ledger of a Stokes-residue support candidate. -/
theorem AnalyticMotivesRoot.traceCorQRelationGenerator_stokesResidueSupportCandidate_ledger
    (source target : TraceRewritePath)
    (support : TraceCorQFormalSum) :
    (TraceCorQRelationGenerator.stokesResidueSupportCandidate
      source
      target
      support).ledger =
      TraceCorQRelationLedger.stokesResidue source target support :=
  TraceCorQRelationGenerator.stokesResidueSupportCandidate_ledger
    source
    target
    support

/-- The top root exposes the formal support of a refinement support candidate. -/
theorem AnalyticMotivesRoot.traceCorQRelationGenerator_refinementSupportCandidate_formalSum
    (source target : TraceRewritePath)
    (support : TraceCorQFormalSum) :
    (TraceCorQRelationGenerator.refinementSupportCandidate
      source
      target
      support).formalSum =
      support :=
  TraceCorQRelationGenerator.refinementSupportCandidate_formalSum
    source
    target
    support

/-- The top root exposes the singleton ledger of a refinement support candidate. -/
theorem AnalyticMotivesRoot.traceCorQRelationGenerator_refinementSupportCandidate_ledger
    (source target : TraceRewritePath)
    (support : TraceCorQFormalSum) :
    (TraceCorQRelationGenerator.refinementSupportCandidate
      source
      target
      support).ledger =
      TraceCorQRelationLedger.refinement source target support :=
  TraceCorQRelationGenerator.refinementSupportCandidate_ledger
    source
    target
    support

/-- The top root exposes the formal support of an associativity support candidate. -/
theorem AnalyticMotivesRoot.traceCorQRelationGenerator_associativitySupportCandidate_formalSum
    (source target : TraceRewritePath)
    (support : TraceCorQFormalSum) :
    (TraceCorQRelationGenerator.associativitySupportCandidate
      source
      target
      support).formalSum =
      support :=
  TraceCorQRelationGenerator.associativitySupportCandidate_formalSum
    source
    target
    support

/-- The top root exposes the singleton ledger of an associativity support candidate. -/
theorem AnalyticMotivesRoot.traceCorQRelationGenerator_associativitySupportCandidate_ledger
    (source target : TraceRewritePath)
    (support : TraceCorQFormalSum) :
    (TraceCorQRelationGenerator.associativitySupportCandidate
      source
      target
      support).ledger =
      TraceCorQRelationLedger.associativity source target support :=
  TraceCorQRelationGenerator.associativitySupportCandidate_ledger
    source
    target
    support

/-- The top root exposes the formal support of a left-identity support candidate. -/
theorem AnalyticMotivesRoot.traceCorQRelationGenerator_leftIdentitySupportCandidate_formalSum
    (source target : TraceRewritePath)
    (support : TraceCorQFormalSum) :
    (TraceCorQRelationGenerator.leftIdentitySupportCandidate
      source
      target
      support).formalSum =
      support :=
  TraceCorQRelationGenerator.leftIdentitySupportCandidate_formalSum
    source
    target
    support

/-- The top root exposes the singleton ledger of a left-identity support candidate. -/
theorem AnalyticMotivesRoot.traceCorQRelationGenerator_leftIdentitySupportCandidate_ledger
    (source target : TraceRewritePath)
    (support : TraceCorQFormalSum) :
    (TraceCorQRelationGenerator.leftIdentitySupportCandidate
      source
      target
      support).ledger =
      TraceCorQRelationLedger.leftIdentity source target support :=
  TraceCorQRelationGenerator.leftIdentitySupportCandidate_ledger
    source
    target
    support

/-- The top root exposes the formal support of a right-identity support candidate. -/
theorem AnalyticMotivesRoot.traceCorQRelationGenerator_rightIdentitySupportCandidate_formalSum
    (source target : TraceRewritePath)
    (support : TraceCorQFormalSum) :
    (TraceCorQRelationGenerator.rightIdentitySupportCandidate
      source
      target
      support).formalSum =
      support :=
  TraceCorQRelationGenerator.rightIdentitySupportCandidate_formalSum
    source
    target
    support

/-- The top root exposes the singleton ledger of a right-identity support candidate. -/
theorem AnalyticMotivesRoot.traceCorQRelationGenerator_rightIdentitySupportCandidate_ledger
    (source target : TraceRewritePath)
    (support : TraceCorQFormalSum) :
    (TraceCorQRelationGenerator.rightIdentitySupportCandidate
      source
      target
      support).ledger =
      TraceCorQRelationLedger.rightIdentity source target support :=
  TraceCorQRelationGenerator.rightIdentitySupportCandidate_ledger
    source
    target
    support

end AnalyticMotives
end LFunctions
end Boundary
