import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Quotient.RelationWitness.Generators.NamedCoherence.Inputs.Payload.Owner

/-!
# Public named-coherence support-input bookkeeping counts

This file exposes trace-bookkeeping and rewrite-step decompositions for
named-coherence support inputs under the `TraceCorQ` aggregate namespace.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- The trace-correspondence root exposes Fubini support-input bookkeeping counts. -/
theorem TraceCorQ.relationGenerator_fubiniSupportInput_traceBookkeepingCount
    (source target : TraceRewritePath)
    (support : TraceCorQFormalSum) :
    (TraceCorQRelationGenerator.fubiniSupportInput
      source
      target
      support).traceBookkeepingCount =
      support.traceBookkeepingCount +
        (TraceCorQRelationLedger.fubini source target support).traceBookkeepingCount :=
  TraceCorQRelationGenerator.fubiniSupportInput_traceBookkeepingCount
    source
    target
    support

/-- The trace-correspondence root exposes schedule-exchange support-input bookkeeping counts. -/
theorem TraceCorQ.relationGenerator_scheduleExchangeSupportInput_traceBookkeepingCount
    (source target : TraceRewritePath)
    (support : TraceCorQFormalSum) :
    (TraceCorQRelationGenerator.scheduleExchangeSupportInput
      source
      target
      support).traceBookkeepingCount =
      support.traceBookkeepingCount +
        (TraceCorQRelationLedger.scheduleExchange source target support).traceBookkeepingCount :=
  TraceCorQRelationGenerator.scheduleExchangeSupportInput_traceBookkeepingCount
    source
    target
    support

/-- The trace-correspondence root exposes residue-channel support-input bookkeeping counts. -/
theorem TraceCorQ.relationGenerator_residueChannelSupportInput_traceBookkeepingCount
    (source target : TraceRewritePath)
    (support : TraceCorQFormalSum) :
    (TraceCorQRelationGenerator.residueChannelSupportInput
      source
      target
      support).traceBookkeepingCount =
      support.traceBookkeepingCount +
        (TraceCorQRelationLedger.residueChannel source target support).traceBookkeepingCount :=
  TraceCorQRelationGenerator.residueChannelSupportInput_traceBookkeepingCount
    source
    target
    support

/-- The trace-correspondence root exposes Stokes-residue support-input bookkeeping counts. -/
theorem TraceCorQ.relationGenerator_stokesResidueSupportInput_traceBookkeepingCount
    (source target : TraceRewritePath)
    (support : TraceCorQFormalSum) :
    (TraceCorQRelationGenerator.stokesResidueSupportInput
      source
      target
      support).traceBookkeepingCount =
      support.traceBookkeepingCount +
        (TraceCorQRelationLedger.stokesResidue source target support).traceBookkeepingCount :=
  TraceCorQRelationGenerator.stokesResidueSupportInput_traceBookkeepingCount
    source
    target
    support

/-- The trace-correspondence root exposes refinement support-input bookkeeping counts. -/
theorem TraceCorQ.relationGenerator_refinementSupportInput_traceBookkeepingCount
    (source target : TraceRewritePath)
    (support : TraceCorQFormalSum) :
    (TraceCorQRelationGenerator.refinementSupportInput
      source
      target
      support).traceBookkeepingCount =
      support.traceBookkeepingCount +
        (TraceCorQRelationLedger.refinement source target support).traceBookkeepingCount :=
  TraceCorQRelationGenerator.refinementSupportInput_traceBookkeepingCount
    source
    target
    support

/-- The trace-correspondence root exposes associativity support-input bookkeeping counts. -/
theorem TraceCorQ.relationGenerator_associativitySupportInput_traceBookkeepingCount
    (source target : TraceRewritePath)
    (support : TraceCorQFormalSum) :
    (TraceCorQRelationGenerator.associativitySupportInput
      source
      target
      support).traceBookkeepingCount =
      support.traceBookkeepingCount +
        (TraceCorQRelationLedger.associativity source target support).traceBookkeepingCount :=
  TraceCorQRelationGenerator.associativitySupportInput_traceBookkeepingCount
    source
    target
    support

/-- The trace-correspondence root exposes left-identity support-input bookkeeping counts. -/
theorem TraceCorQ.relationGenerator_leftIdentitySupportInput_traceBookkeepingCount
    (source target : TraceRewritePath)
    (support : TraceCorQFormalSum) :
    (TraceCorQRelationGenerator.leftIdentitySupportInput
      source
      target
      support).traceBookkeepingCount =
      support.traceBookkeepingCount +
        (TraceCorQRelationLedger.leftIdentity source target support).traceBookkeepingCount :=
  TraceCorQRelationGenerator.leftIdentitySupportInput_traceBookkeepingCount
    source
    target
    support

/-- The trace-correspondence root exposes right-identity support-input bookkeeping counts. -/
theorem TraceCorQ.relationGenerator_rightIdentitySupportInput_traceBookkeepingCount
    (source target : TraceRewritePath)
    (support : TraceCorQFormalSum) :
    (TraceCorQRelationGenerator.rightIdentitySupportInput
      source
      target
      support).traceBookkeepingCount =
      support.traceBookkeepingCount +
        (TraceCorQRelationLedger.rightIdentity source target support).traceBookkeepingCount :=
  TraceCorQRelationGenerator.rightIdentitySupportInput_traceBookkeepingCount
    source
    target
    support

/-- The trace-correspondence root exposes Fubini support-input rewrite-step counts. -/
theorem TraceCorQ.relationGenerator_fubiniSupportInput_rewriteStepCount
    (source target : TraceRewritePath)
    (support : TraceCorQFormalSum) :
    (TraceCorQRelationGenerator.fubiniSupportInput
      source
      target
      support).rewriteStepCount =
      support.rewriteStepCount +
        (TraceCorQRelationLedger.fubini source target support).rewriteStepCount :=
  TraceCorQRelationGenerator.fubiniSupportInput_rewriteStepCount
    source
    target
    support

/-- The trace-correspondence root exposes schedule-exchange support-input rewrite-step counts. -/
theorem TraceCorQ.relationGenerator_scheduleExchangeSupportInput_rewriteStepCount
    (source target : TraceRewritePath)
    (support : TraceCorQFormalSum) :
    (TraceCorQRelationGenerator.scheduleExchangeSupportInput
      source
      target
      support).rewriteStepCount =
      support.rewriteStepCount +
        (TraceCorQRelationLedger.scheduleExchange source target support).rewriteStepCount :=
  TraceCorQRelationGenerator.scheduleExchangeSupportInput_rewriteStepCount
    source
    target
    support

/-- The trace-correspondence root exposes residue-channel support-input rewrite-step counts. -/
theorem TraceCorQ.relationGenerator_residueChannelSupportInput_rewriteStepCount
    (source target : TraceRewritePath)
    (support : TraceCorQFormalSum) :
    (TraceCorQRelationGenerator.residueChannelSupportInput
      source
      target
      support).rewriteStepCount =
      support.rewriteStepCount +
        (TraceCorQRelationLedger.residueChannel source target support).rewriteStepCount :=
  TraceCorQRelationGenerator.residueChannelSupportInput_rewriteStepCount
    source
    target
    support

/-- The trace-correspondence root exposes Stokes-residue support-input rewrite-step counts. -/
theorem TraceCorQ.relationGenerator_stokesResidueSupportInput_rewriteStepCount
    (source target : TraceRewritePath)
    (support : TraceCorQFormalSum) :
    (TraceCorQRelationGenerator.stokesResidueSupportInput
      source
      target
      support).rewriteStepCount =
      support.rewriteStepCount +
        (TraceCorQRelationLedger.stokesResidue source target support).rewriteStepCount :=
  TraceCorQRelationGenerator.stokesResidueSupportInput_rewriteStepCount
    source
    target
    support

/-- The trace-correspondence root exposes refinement support-input rewrite-step counts. -/
theorem TraceCorQ.relationGenerator_refinementSupportInput_rewriteStepCount
    (source target : TraceRewritePath)
    (support : TraceCorQFormalSum) :
    (TraceCorQRelationGenerator.refinementSupportInput
      source
      target
      support).rewriteStepCount =
      support.rewriteStepCount +
        (TraceCorQRelationLedger.refinement source target support).rewriteStepCount :=
  TraceCorQRelationGenerator.refinementSupportInput_rewriteStepCount
    source
    target
    support

/-- The trace-correspondence root exposes associativity support-input rewrite-step counts. -/
theorem TraceCorQ.relationGenerator_associativitySupportInput_rewriteStepCount
    (source target : TraceRewritePath)
    (support : TraceCorQFormalSum) :
    (TraceCorQRelationGenerator.associativitySupportInput
      source
      target
      support).rewriteStepCount =
      support.rewriteStepCount +
        (TraceCorQRelationLedger.associativity source target support).rewriteStepCount :=
  TraceCorQRelationGenerator.associativitySupportInput_rewriteStepCount
    source
    target
    support

/-- The trace-correspondence root exposes left-identity support-input rewrite-step counts. -/
theorem TraceCorQ.relationGenerator_leftIdentitySupportInput_rewriteStepCount
    (source target : TraceRewritePath)
    (support : TraceCorQFormalSum) :
    (TraceCorQRelationGenerator.leftIdentitySupportInput
      source
      target
      support).rewriteStepCount =
      support.rewriteStepCount +
        (TraceCorQRelationLedger.leftIdentity source target support).rewriteStepCount :=
  TraceCorQRelationGenerator.leftIdentitySupportInput_rewriteStepCount
    source
    target
    support

/-- The trace-correspondence root exposes right-identity support-input rewrite-step counts. -/
theorem TraceCorQ.relationGenerator_rightIdentitySupportInput_rewriteStepCount
    (source target : TraceRewritePath)
    (support : TraceCorQFormalSum) :
    (TraceCorQRelationGenerator.rightIdentitySupportInput
      source
      target
      support).rewriteStepCount =
      support.rewriteStepCount +
        (TraceCorQRelationLedger.rightIdentity source target support).rewriteStepCount :=
  TraceCorQRelationGenerator.rightIdentitySupportInput_rewriteStepCount
    source
    target
    support

end AnalyticMotives
end LFunctions
end Boundary
