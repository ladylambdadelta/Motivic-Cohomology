import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Quotient.RelationWitness.Generators.NamedCoherence.Candidates.Owner

/-!
# Top-root trace-calculus payload for named-coherence candidates

This file exposes bookkeeping and rewrite-step decompositions for
named-coherence support candidates.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- The top root exposes Fubini candidate bookkeeping counts. -/
theorem AnalyticMotivesRoot.traceCorQRelationGenerator_fubiniSupportCandidate_traceBookkeepingCount
    (source target : TraceRewritePath)
    (support : TraceCorQFormalSum) :
    (TraceCorQRelationGenerator.fubiniSupportCandidate
      source
      target
      support).traceBookkeepingCount =
      support.traceBookkeepingCount +
        (TraceCorQRelationLedger.fubini source target support).traceBookkeepingCount :=
  TraceCorQRelationGenerator.fubiniSupportCandidate_traceBookkeepingCount
    source
    target
    support

/-- The top root exposes schedule-exchange candidate bookkeeping counts. -/
theorem AnalyticMotivesRoot.traceCorQRelationGenerator_scheduleExchangeSupportCandidate_traceBookkeepingCount
    (source target : TraceRewritePath)
    (support : TraceCorQFormalSum) :
    (TraceCorQRelationGenerator.scheduleExchangeSupportCandidate
      source
      target
      support).traceBookkeepingCount =
      support.traceBookkeepingCount +
        (TraceCorQRelationLedger.scheduleExchange source target support).traceBookkeepingCount :=
  TraceCorQRelationGenerator.scheduleExchangeSupportCandidate_traceBookkeepingCount
    source
    target
    support

/-- The top root exposes residue-channel candidate bookkeeping counts. -/
theorem AnalyticMotivesRoot.traceCorQRelationGenerator_residueChannelSupportCandidate_traceBookkeepingCount
    (source target : TraceRewritePath)
    (support : TraceCorQFormalSum) :
    (TraceCorQRelationGenerator.residueChannelSupportCandidate
      source
      target
      support).traceBookkeepingCount =
      support.traceBookkeepingCount +
        (TraceCorQRelationLedger.residueChannel source target support).traceBookkeepingCount :=
  TraceCorQRelationGenerator.residueChannelSupportCandidate_traceBookkeepingCount
    source
    target
    support

/-- The top root exposes Stokes-residue candidate bookkeeping counts. -/
theorem AnalyticMotivesRoot.traceCorQRelationGenerator_stokesResidueSupportCandidate_traceBookkeepingCount
    (source target : TraceRewritePath)
    (support : TraceCorQFormalSum) :
    (TraceCorQRelationGenerator.stokesResidueSupportCandidate
      source
      target
      support).traceBookkeepingCount =
      support.traceBookkeepingCount +
        (TraceCorQRelationLedger.stokesResidue source target support).traceBookkeepingCount :=
  TraceCorQRelationGenerator.stokesResidueSupportCandidate_traceBookkeepingCount
    source
    target
    support

/-- The top root exposes refinement candidate bookkeeping counts. -/
theorem AnalyticMotivesRoot.traceCorQRelationGenerator_refinementSupportCandidate_traceBookkeepingCount
    (source target : TraceRewritePath)
    (support : TraceCorQFormalSum) :
    (TraceCorQRelationGenerator.refinementSupportCandidate
      source
      target
      support).traceBookkeepingCount =
      support.traceBookkeepingCount +
        (TraceCorQRelationLedger.refinement source target support).traceBookkeepingCount :=
  TraceCorQRelationGenerator.refinementSupportCandidate_traceBookkeepingCount
    source
    target
    support

/-- The top root exposes associativity candidate bookkeeping counts. -/
theorem AnalyticMotivesRoot.traceCorQRelationGenerator_associativitySupportCandidate_traceBookkeepingCount
    (source target : TraceRewritePath)
    (support : TraceCorQFormalSum) :
    (TraceCorQRelationGenerator.associativitySupportCandidate
      source
      target
      support).traceBookkeepingCount =
      support.traceBookkeepingCount +
        (TraceCorQRelationLedger.associativity source target support).traceBookkeepingCount :=
  TraceCorQRelationGenerator.associativitySupportCandidate_traceBookkeepingCount
    source
    target
    support

/-- The top root exposes left-identity candidate bookkeeping counts. -/
theorem AnalyticMotivesRoot.traceCorQRelationGenerator_leftIdentitySupportCandidate_traceBookkeepingCount
    (source target : TraceRewritePath)
    (support : TraceCorQFormalSum) :
    (TraceCorQRelationGenerator.leftIdentitySupportCandidate
      source
      target
      support).traceBookkeepingCount =
      support.traceBookkeepingCount +
        (TraceCorQRelationLedger.leftIdentity source target support).traceBookkeepingCount :=
  TraceCorQRelationGenerator.leftIdentitySupportCandidate_traceBookkeepingCount
    source
    target
    support

/-- The top root exposes right-identity candidate bookkeeping counts. -/
theorem AnalyticMotivesRoot.traceCorQRelationGenerator_rightIdentitySupportCandidate_traceBookkeepingCount
    (source target : TraceRewritePath)
    (support : TraceCorQFormalSum) :
    (TraceCorQRelationGenerator.rightIdentitySupportCandidate
      source
      target
      support).traceBookkeepingCount =
      support.traceBookkeepingCount +
        (TraceCorQRelationLedger.rightIdentity source target support).traceBookkeepingCount :=
  TraceCorQRelationGenerator.rightIdentitySupportCandidate_traceBookkeepingCount
    source
    target
    support

/-- The top root exposes Fubini candidate rewrite-step counts. -/
theorem AnalyticMotivesRoot.traceCorQRelationGenerator_fubiniSupportCandidate_rewriteStepCount
    (source target : TraceRewritePath)
    (support : TraceCorQFormalSum) :
    (TraceCorQRelationGenerator.fubiniSupportCandidate
      source
      target
      support).rewriteStepCount =
      support.rewriteStepCount +
        (TraceCorQRelationLedger.fubini source target support).rewriteStepCount :=
  TraceCorQRelationGenerator.fubiniSupportCandidate_rewriteStepCount
    source
    target
    support

/-- The top root exposes schedule-exchange candidate rewrite-step counts. -/
theorem AnalyticMotivesRoot.traceCorQRelationGenerator_scheduleExchangeSupportCandidate_rewriteStepCount
    (source target : TraceRewritePath)
    (support : TraceCorQFormalSum) :
    (TraceCorQRelationGenerator.scheduleExchangeSupportCandidate
      source
      target
      support).rewriteStepCount =
      support.rewriteStepCount +
        (TraceCorQRelationLedger.scheduleExchange source target support).rewriteStepCount :=
  TraceCorQRelationGenerator.scheduleExchangeSupportCandidate_rewriteStepCount
    source
    target
    support

/-- The top root exposes residue-channel candidate rewrite-step counts. -/
theorem AnalyticMotivesRoot.traceCorQRelationGenerator_residueChannelSupportCandidate_rewriteStepCount
    (source target : TraceRewritePath)
    (support : TraceCorQFormalSum) :
    (TraceCorQRelationGenerator.residueChannelSupportCandidate
      source
      target
      support).rewriteStepCount =
      support.rewriteStepCount +
        (TraceCorQRelationLedger.residueChannel source target support).rewriteStepCount :=
  TraceCorQRelationGenerator.residueChannelSupportCandidate_rewriteStepCount
    source
    target
    support

/-- The top root exposes Stokes-residue candidate rewrite-step counts. -/
theorem AnalyticMotivesRoot.traceCorQRelationGenerator_stokesResidueSupportCandidate_rewriteStepCount
    (source target : TraceRewritePath)
    (support : TraceCorQFormalSum) :
    (TraceCorQRelationGenerator.stokesResidueSupportCandidate
      source
      target
      support).rewriteStepCount =
      support.rewriteStepCount +
        (TraceCorQRelationLedger.stokesResidue source target support).rewriteStepCount :=
  TraceCorQRelationGenerator.stokesResidueSupportCandidate_rewriteStepCount
    source
    target
    support

/-- The top root exposes refinement candidate rewrite-step counts. -/
theorem AnalyticMotivesRoot.traceCorQRelationGenerator_refinementSupportCandidate_rewriteStepCount
    (source target : TraceRewritePath)
    (support : TraceCorQFormalSum) :
    (TraceCorQRelationGenerator.refinementSupportCandidate
      source
      target
      support).rewriteStepCount =
      support.rewriteStepCount +
        (TraceCorQRelationLedger.refinement source target support).rewriteStepCount :=
  TraceCorQRelationGenerator.refinementSupportCandidate_rewriteStepCount
    source
    target
    support

/-- The top root exposes associativity candidate rewrite-step counts. -/
theorem AnalyticMotivesRoot.traceCorQRelationGenerator_associativitySupportCandidate_rewriteStepCount
    (source target : TraceRewritePath)
    (support : TraceCorQFormalSum) :
    (TraceCorQRelationGenerator.associativitySupportCandidate
      source
      target
      support).rewriteStepCount =
      support.rewriteStepCount +
        (TraceCorQRelationLedger.associativity source target support).rewriteStepCount :=
  TraceCorQRelationGenerator.associativitySupportCandidate_rewriteStepCount
    source
    target
    support

/-- The top root exposes left-identity candidate rewrite-step counts. -/
theorem AnalyticMotivesRoot.traceCorQRelationGenerator_leftIdentitySupportCandidate_rewriteStepCount
    (source target : TraceRewritePath)
    (support : TraceCorQFormalSum) :
    (TraceCorQRelationGenerator.leftIdentitySupportCandidate
      source
      target
      support).rewriteStepCount =
      support.rewriteStepCount +
        (TraceCorQRelationLedger.leftIdentity source target support).rewriteStepCount :=
  TraceCorQRelationGenerator.leftIdentitySupportCandidate_rewriteStepCount
    source
    target
    support

/-- The top root exposes right-identity candidate rewrite-step counts. -/
theorem AnalyticMotivesRoot.traceCorQRelationGenerator_rightIdentitySupportCandidate_rewriteStepCount
    (source target : TraceRewritePath)
    (support : TraceCorQFormalSum) :
    (TraceCorQRelationGenerator.rightIdentitySupportCandidate
      source
      target
      support).rewriteStepCount =
      support.rewriteStepCount +
        (TraceCorQRelationLedger.rightIdentity source target support).rewriteStepCount :=
  TraceCorQRelationGenerator.rightIdentitySupportCandidate_rewriteStepCount
    source
    target
    support

end AnalyticMotives
end LFunctions
end Boundary
