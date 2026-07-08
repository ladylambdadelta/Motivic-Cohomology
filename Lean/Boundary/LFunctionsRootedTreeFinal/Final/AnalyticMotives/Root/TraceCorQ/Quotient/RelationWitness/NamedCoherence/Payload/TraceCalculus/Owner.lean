import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Quotient.RelationWitness.Generators.NamedCoherence.Payload.Owner

/-!
# Top-root trace-calculus payload for named-coherence witnesses

This file exposes bookkeeping and rewrite-step counts carried by the canonical
named-coherence quotient-relation witnesses.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- The top root exposes Fubini witness bookkeeping counts. -/
theorem AnalyticMotivesRoot.traceCorQRelationGenerator_fubiniSupportWitness_traceBookkeepingCount
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

/-- The top root exposes schedule-exchange witness bookkeeping counts. -/
theorem AnalyticMotivesRoot.traceCorQRelationGenerator_scheduleExchangeSupportWitness_traceBookkeepingCount
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

/-- The top root exposes residue-channel witness bookkeeping counts. -/
theorem AnalyticMotivesRoot.traceCorQRelationGenerator_residueChannelSupportWitness_traceBookkeepingCount
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

/-- The top root exposes Stokes-residue witness bookkeeping counts. -/
theorem AnalyticMotivesRoot.traceCorQRelationGenerator_stokesResidueSupportWitness_traceBookkeepingCount
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

/-- The top root exposes refinement witness bookkeeping counts. -/
theorem AnalyticMotivesRoot.traceCorQRelationGenerator_refinementSupportWitness_traceBookkeepingCount
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

/-- The top root exposes associativity witness bookkeeping counts. -/
theorem AnalyticMotivesRoot.traceCorQRelationGenerator_associativitySupportWitness_traceBookkeepingCount
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

/-- The top root exposes left-identity witness bookkeeping counts. -/
theorem AnalyticMotivesRoot.traceCorQRelationGenerator_leftIdentitySupportWitness_traceBookkeepingCount
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

/-- The top root exposes right-identity witness bookkeeping counts. -/
theorem AnalyticMotivesRoot.traceCorQRelationGenerator_rightIdentitySupportWitness_traceBookkeepingCount
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

/-- The top root exposes Fubini witness rewrite-step counts. -/
theorem AnalyticMotivesRoot.traceCorQRelationGenerator_fubiniSupportWitness_rewriteStepCount
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

/-- The top root exposes schedule-exchange witness rewrite-step counts. -/
theorem AnalyticMotivesRoot.traceCorQRelationGenerator_scheduleExchangeSupportWitness_rewriteStepCount
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

/-- The top root exposes residue-channel witness rewrite-step counts. -/
theorem AnalyticMotivesRoot.traceCorQRelationGenerator_residueChannelSupportWitness_rewriteStepCount
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

/-- The top root exposes Stokes-residue witness rewrite-step counts. -/
theorem AnalyticMotivesRoot.traceCorQRelationGenerator_stokesResidueSupportWitness_rewriteStepCount
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

/-- The top root exposes refinement witness rewrite-step counts. -/
theorem AnalyticMotivesRoot.traceCorQRelationGenerator_refinementSupportWitness_rewriteStepCount
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

/-- The top root exposes associativity witness rewrite-step counts. -/
theorem AnalyticMotivesRoot.traceCorQRelationGenerator_associativitySupportWitness_rewriteStepCount
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

/-- The top root exposes left-identity witness rewrite-step counts. -/
theorem AnalyticMotivesRoot.traceCorQRelationGenerator_leftIdentitySupportWitness_rewriteStepCount
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

/-- The top root exposes right-identity witness rewrite-step counts. -/
theorem AnalyticMotivesRoot.traceCorQRelationGenerator_rightIdentitySupportWitness_rewriteStepCount
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
