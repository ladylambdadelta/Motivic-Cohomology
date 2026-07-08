import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Quotient.RelationWitness.Generators.NamedCoherence.Candidates.Projections.Owner

/-!
# Public named-coherence support-candidate projections

This file exposes formal-sum and singleton-ledger projections for named
coherence support candidates under the `TraceCorQ` aggregate namespace.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- The trace-correspondence root exposes Fubini support-candidate formal sums. -/
theorem TraceCorQ.relationGenerator_fubiniSupportCandidate_formalSum
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

/-- The trace-correspondence root exposes Fubini support-candidate ledgers. -/
theorem TraceCorQ.relationGenerator_fubiniSupportCandidate_ledger
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

/-- The trace-correspondence root exposes schedule-exchange support-candidate formal sums. -/
theorem TraceCorQ.relationGenerator_scheduleExchangeSupportCandidate_formalSum
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

/-- The trace-correspondence root exposes schedule-exchange support-candidate ledgers. -/
theorem TraceCorQ.relationGenerator_scheduleExchangeSupportCandidate_ledger
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

/-- The trace-correspondence root exposes residue-channel support-candidate formal sums. -/
theorem TraceCorQ.relationGenerator_residueChannelSupportCandidate_formalSum
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

/-- The trace-correspondence root exposes residue-channel support-candidate ledgers. -/
theorem TraceCorQ.relationGenerator_residueChannelSupportCandidate_ledger
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

/-- The trace-correspondence root exposes Stokes-residue support-candidate formal sums. -/
theorem TraceCorQ.relationGenerator_stokesResidueSupportCandidate_formalSum
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

/-- The trace-correspondence root exposes Stokes-residue support-candidate ledgers. -/
theorem TraceCorQ.relationGenerator_stokesResidueSupportCandidate_ledger
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

/-- The trace-correspondence root exposes refinement support-candidate formal sums. -/
theorem TraceCorQ.relationGenerator_refinementSupportCandidate_formalSum
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

/-- The trace-correspondence root exposes refinement support-candidate ledgers. -/
theorem TraceCorQ.relationGenerator_refinementSupportCandidate_ledger
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

/-- The trace-correspondence root exposes associativity support-candidate formal sums. -/
theorem TraceCorQ.relationGenerator_associativitySupportCandidate_formalSum
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

/-- The trace-correspondence root exposes associativity support-candidate ledgers. -/
theorem TraceCorQ.relationGenerator_associativitySupportCandidate_ledger
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

/-- The trace-correspondence root exposes left-identity support-candidate formal sums. -/
theorem TraceCorQ.relationGenerator_leftIdentitySupportCandidate_formalSum
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

/-- The trace-correspondence root exposes left-identity support-candidate ledgers. -/
theorem TraceCorQ.relationGenerator_leftIdentitySupportCandidate_ledger
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

/-- The trace-correspondence root exposes right-identity support-candidate formal sums. -/
theorem TraceCorQ.relationGenerator_rightIdentitySupportCandidate_formalSum
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

/-- The trace-correspondence root exposes right-identity support-candidate ledgers. -/
theorem TraceCorQ.relationGenerator_rightIdentitySupportCandidate_ledger
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
