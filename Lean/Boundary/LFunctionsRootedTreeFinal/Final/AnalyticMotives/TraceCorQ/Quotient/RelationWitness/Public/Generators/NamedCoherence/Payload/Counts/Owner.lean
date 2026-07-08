import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Quotient.RelationWitness.Generators.NamedCoherence.Payload.Owner

/-!
# Public count payloads for named-coherence support witnesses

This file exposes bookkeeping and rewrite-step payload facts for
named-coherence support witnesses under the `TraceCorQ` aggregate namespace.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- The public Fubini support witness keeps the Fubini ledger bookkeeping payload. -/
theorem TraceCorQ.relationGenerator_fubiniSupportWitness_traceBookkeepingCount
    (source target : TraceRewritePath)
    (support : TraceCorQFormalSum) :
    (TraceCorQRelationGenerator.fubiniSupportWitness
      source
      target
      support).traceBookkeepingCount =
      (TraceCorQRelationLedger.fubini source target support).traceBookkeepingCount :=
  TraceCorQRelationGenerator.fubiniSupportWitness_traceBookkeepingCount
    source
    target
    support

/-- The public schedule-exchange support witness keeps the ledger bookkeeping payload. -/
theorem TraceCorQ.relationGenerator_scheduleExchangeSupportWitness_traceBookkeepingCount
    (source target : TraceRewritePath)
    (support : TraceCorQFormalSum) :
    (TraceCorQRelationGenerator.scheduleExchangeSupportWitness
      source
      target
      support).traceBookkeepingCount =
      (TraceCorQRelationLedger.scheduleExchange source target support).traceBookkeepingCount :=
  TraceCorQRelationGenerator.scheduleExchangeSupportWitness_traceBookkeepingCount
    source
    target
    support

/-- The public residue-channel support witness keeps the ledger bookkeeping payload. -/
theorem TraceCorQ.relationGenerator_residueChannelSupportWitness_traceBookkeepingCount
    (source target : TraceRewritePath)
    (support : TraceCorQFormalSum) :
    (TraceCorQRelationGenerator.residueChannelSupportWitness
      source
      target
      support).traceBookkeepingCount =
      (TraceCorQRelationLedger.residueChannel source target support).traceBookkeepingCount :=
  TraceCorQRelationGenerator.residueChannelSupportWitness_traceBookkeepingCount
    source
    target
    support

/-- The public Stokes-residue support witness keeps the ledger bookkeeping payload. -/
theorem TraceCorQ.relationGenerator_stokesResidueSupportWitness_traceBookkeepingCount
    (source target : TraceRewritePath)
    (support : TraceCorQFormalSum) :
    (TraceCorQRelationGenerator.stokesResidueSupportWitness
      source
      target
      support).traceBookkeepingCount =
      (TraceCorQRelationLedger.stokesResidue source target support).traceBookkeepingCount :=
  TraceCorQRelationGenerator.stokesResidueSupportWitness_traceBookkeepingCount
    source
    target
    support

/-- The public refinement support witness keeps the ledger bookkeeping payload. -/
theorem TraceCorQ.relationGenerator_refinementSupportWitness_traceBookkeepingCount
    (source target : TraceRewritePath)
    (support : TraceCorQFormalSum) :
    (TraceCorQRelationGenerator.refinementSupportWitness
      source
      target
      support).traceBookkeepingCount =
      (TraceCorQRelationLedger.refinement source target support).traceBookkeepingCount :=
  TraceCorQRelationGenerator.refinementSupportWitness_traceBookkeepingCount
    source
    target
    support

/-- The public associativity support witness keeps the ledger bookkeeping payload. -/
theorem TraceCorQ.relationGenerator_associativitySupportWitness_traceBookkeepingCount
    (source target : TraceRewritePath)
    (support : TraceCorQFormalSum) :
    (TraceCorQRelationGenerator.associativitySupportWitness
      source
      target
      support).traceBookkeepingCount =
      (TraceCorQRelationLedger.associativity source target support).traceBookkeepingCount :=
  TraceCorQRelationGenerator.associativitySupportWitness_traceBookkeepingCount
    source
    target
    support

/-- The public left-identity support witness keeps the ledger bookkeeping payload. -/
theorem TraceCorQ.relationGenerator_leftIdentitySupportWitness_traceBookkeepingCount
    (source target : TraceRewritePath)
    (support : TraceCorQFormalSum) :
    (TraceCorQRelationGenerator.leftIdentitySupportWitness
      source
      target
      support).traceBookkeepingCount =
      (TraceCorQRelationLedger.leftIdentity source target support).traceBookkeepingCount :=
  TraceCorQRelationGenerator.leftIdentitySupportWitness_traceBookkeepingCount
    source
    target
    support

/-- The public right-identity support witness keeps the ledger bookkeeping payload. -/
theorem TraceCorQ.relationGenerator_rightIdentitySupportWitness_traceBookkeepingCount
    (source target : TraceRewritePath)
    (support : TraceCorQFormalSum) :
    (TraceCorQRelationGenerator.rightIdentitySupportWitness
      source
      target
      support).traceBookkeepingCount =
      (TraceCorQRelationLedger.rightIdentity source target support).traceBookkeepingCount :=
  TraceCorQRelationGenerator.rightIdentitySupportWitness_traceBookkeepingCount
    source
    target
    support

/-- The public Fubini support witness keeps the Fubini ledger rewrite-step payload. -/
theorem TraceCorQ.relationGenerator_fubiniSupportWitness_rewriteStepCount
    (source target : TraceRewritePath)
    (support : TraceCorQFormalSum) :
    (TraceCorQRelationGenerator.fubiniSupportWitness
      source
      target
      support).rewriteStepCount =
      (TraceCorQRelationLedger.fubini source target support).rewriteStepCount :=
  TraceCorQRelationGenerator.fubiniSupportWitness_rewriteStepCount
    source
    target
    support

/-- The public schedule-exchange support witness keeps the ledger rewrite-step payload. -/
theorem TraceCorQ.relationGenerator_scheduleExchangeSupportWitness_rewriteStepCount
    (source target : TraceRewritePath)
    (support : TraceCorQFormalSum) :
    (TraceCorQRelationGenerator.scheduleExchangeSupportWitness
      source
      target
      support).rewriteStepCount =
      (TraceCorQRelationLedger.scheduleExchange source target support).rewriteStepCount :=
  TraceCorQRelationGenerator.scheduleExchangeSupportWitness_rewriteStepCount
    source
    target
    support

/-- The public residue-channel support witness keeps the ledger rewrite-step payload. -/
theorem TraceCorQ.relationGenerator_residueChannelSupportWitness_rewriteStepCount
    (source target : TraceRewritePath)
    (support : TraceCorQFormalSum) :
    (TraceCorQRelationGenerator.residueChannelSupportWitness
      source
      target
      support).rewriteStepCount =
      (TraceCorQRelationLedger.residueChannel source target support).rewriteStepCount :=
  TraceCorQRelationGenerator.residueChannelSupportWitness_rewriteStepCount
    source
    target
    support

/-- The public Stokes-residue support witness keeps the ledger rewrite-step payload. -/
theorem TraceCorQ.relationGenerator_stokesResidueSupportWitness_rewriteStepCount
    (source target : TraceRewritePath)
    (support : TraceCorQFormalSum) :
    (TraceCorQRelationGenerator.stokesResidueSupportWitness
      source
      target
      support).rewriteStepCount =
      (TraceCorQRelationLedger.stokesResidue source target support).rewriteStepCount :=
  TraceCorQRelationGenerator.stokesResidueSupportWitness_rewriteStepCount
    source
    target
    support

/-- The public refinement support witness keeps the ledger rewrite-step payload. -/
theorem TraceCorQ.relationGenerator_refinementSupportWitness_rewriteStepCount
    (source target : TraceRewritePath)
    (support : TraceCorQFormalSum) :
    (TraceCorQRelationGenerator.refinementSupportWitness
      source
      target
      support).rewriteStepCount =
      (TraceCorQRelationLedger.refinement source target support).rewriteStepCount :=
  TraceCorQRelationGenerator.refinementSupportWitness_rewriteStepCount
    source
    target
    support

/-- The public associativity support witness keeps the ledger rewrite-step payload. -/
theorem TraceCorQ.relationGenerator_associativitySupportWitness_rewriteStepCount
    (source target : TraceRewritePath)
    (support : TraceCorQFormalSum) :
    (TraceCorQRelationGenerator.associativitySupportWitness
      source
      target
      support).rewriteStepCount =
      (TraceCorQRelationLedger.associativity source target support).rewriteStepCount :=
  TraceCorQRelationGenerator.associativitySupportWitness_rewriteStepCount
    source
    target
    support

/-- The public left-identity support witness keeps the ledger rewrite-step payload. -/
theorem TraceCorQ.relationGenerator_leftIdentitySupportWitness_rewriteStepCount
    (source target : TraceRewritePath)
    (support : TraceCorQFormalSum) :
    (TraceCorQRelationGenerator.leftIdentitySupportWitness
      source
      target
      support).rewriteStepCount =
      (TraceCorQRelationLedger.leftIdentity source target support).rewriteStepCount :=
  TraceCorQRelationGenerator.leftIdentitySupportWitness_rewriteStepCount
    source
    target
    support

/-- The public right-identity support witness keeps the ledger rewrite-step payload. -/
theorem TraceCorQ.relationGenerator_rightIdentitySupportWitness_rewriteStepCount
    (source target : TraceRewritePath)
    (support : TraceCorQFormalSum) :
    (TraceCorQRelationGenerator.rightIdentitySupportWitness
      source
      target
      support).rewriteStepCount =
      (TraceCorQRelationLedger.rightIdentity source target support).rewriteStepCount :=
  TraceCorQRelationGenerator.rightIdentitySupportWitness_rewriteStepCount
    source
    target
    support

end AnalyticMotives
end LFunctions
end Boundary
