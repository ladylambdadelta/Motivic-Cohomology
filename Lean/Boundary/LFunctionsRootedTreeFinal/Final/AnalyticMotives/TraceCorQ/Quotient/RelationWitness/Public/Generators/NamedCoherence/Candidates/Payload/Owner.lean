import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Quotient.RelationWitness.Generators.NamedCoherence.Candidates.Owner

/-!
# Public named-coherence support-candidate payloads

This file exposes trace-bookkeeping and rewrite-step decompositions for
named-coherence support candidates under the `TraceCorQ` aggregate namespace.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- The trace-correspondence root exposes Fubini support-candidate bookkeeping counts. -/
theorem TraceCorQ.relationGenerator_fubiniSupportCandidate_traceBookkeepingCount
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

/-- The trace-correspondence root exposes schedule-exchange support-candidate bookkeeping counts. -/
theorem TraceCorQ.relationGenerator_scheduleExchangeSupportCandidate_traceBookkeepingCount
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

/-- The trace-correspondence root exposes residue-channel support-candidate bookkeeping counts. -/
theorem TraceCorQ.relationGenerator_residueChannelSupportCandidate_traceBookkeepingCount
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

/-- The trace-correspondence root exposes Stokes-residue support-candidate bookkeeping counts. -/
theorem TraceCorQ.relationGenerator_stokesResidueSupportCandidate_traceBookkeepingCount
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

/-- The trace-correspondence root exposes refinement support-candidate bookkeeping counts. -/
theorem TraceCorQ.relationGenerator_refinementSupportCandidate_traceBookkeepingCount
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

/-- The trace-correspondence root exposes associativity support-candidate bookkeeping counts. -/
theorem TraceCorQ.relationGenerator_associativitySupportCandidate_traceBookkeepingCount
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

/-- The trace-correspondence root exposes left-identity support-candidate bookkeeping counts. -/
theorem TraceCorQ.relationGenerator_leftIdentitySupportCandidate_traceBookkeepingCount
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

/-- The trace-correspondence root exposes right-identity support-candidate bookkeeping counts. -/
theorem TraceCorQ.relationGenerator_rightIdentitySupportCandidate_traceBookkeepingCount
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

/-- The trace-correspondence root exposes Fubini support-candidate rewrite-step counts. -/
theorem TraceCorQ.relationGenerator_fubiniSupportCandidate_rewriteStepCount
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

/-- The trace-correspondence root exposes schedule-exchange support-candidate rewrite-step counts. -/
theorem TraceCorQ.relationGenerator_scheduleExchangeSupportCandidate_rewriteStepCount
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

/-- The trace-correspondence root exposes residue-channel support-candidate rewrite-step counts. -/
theorem TraceCorQ.relationGenerator_residueChannelSupportCandidate_rewriteStepCount
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

/-- The trace-correspondence root exposes Stokes-residue support-candidate rewrite-step counts. -/
theorem TraceCorQ.relationGenerator_stokesResidueSupportCandidate_rewriteStepCount
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

/-- The trace-correspondence root exposes refinement support-candidate rewrite-step counts. -/
theorem TraceCorQ.relationGenerator_refinementSupportCandidate_rewriteStepCount
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

/-- The trace-correspondence root exposes associativity support-candidate rewrite-step counts. -/
theorem TraceCorQ.relationGenerator_associativitySupportCandidate_rewriteStepCount
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

/-- The trace-correspondence root exposes left-identity support-candidate rewrite-step counts. -/
theorem TraceCorQ.relationGenerator_leftIdentitySupportCandidate_rewriteStepCount
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

/-- The trace-correspondence root exposes right-identity support-candidate rewrite-step counts. -/
theorem TraceCorQ.relationGenerator_rightIdentitySupportCandidate_rewriteStepCount
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
