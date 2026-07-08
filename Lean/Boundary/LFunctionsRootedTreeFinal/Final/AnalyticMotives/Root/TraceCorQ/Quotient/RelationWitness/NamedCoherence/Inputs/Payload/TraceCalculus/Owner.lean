import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Quotient.RelationWitness.Generators.NamedCoherence.Inputs.Payload.Owner

/-!
# Top-root trace-calculus payload for named-coherence inputs

This file exposes bookkeeping and rewrite-step decompositions for
named-coherence support inputs.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- The top root exposes Fubini input bookkeeping counts. -/
theorem AnalyticMotivesRoot.traceCorQRelationGenerator_fubiniSupportInput_traceBookkeepingCount
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

/-- The top root exposes schedule-exchange input bookkeeping counts. -/
theorem AnalyticMotivesRoot.traceCorQRelationGenerator_scheduleExchangeSupportInput_traceBookkeepingCount
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

/-- The top root exposes residue-channel input bookkeeping counts. -/
theorem AnalyticMotivesRoot.traceCorQRelationGenerator_residueChannelSupportInput_traceBookkeepingCount
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

/-- The top root exposes Stokes-residue input bookkeeping counts. -/
theorem AnalyticMotivesRoot.traceCorQRelationGenerator_stokesResidueSupportInput_traceBookkeepingCount
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

/-- The top root exposes refinement input bookkeeping counts. -/
theorem AnalyticMotivesRoot.traceCorQRelationGenerator_refinementSupportInput_traceBookkeepingCount
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

/-- The top root exposes associativity input bookkeeping counts. -/
theorem AnalyticMotivesRoot.traceCorQRelationGenerator_associativitySupportInput_traceBookkeepingCount
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

/-- The top root exposes left-identity input bookkeeping counts. -/
theorem AnalyticMotivesRoot.traceCorQRelationGenerator_leftIdentitySupportInput_traceBookkeepingCount
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

/-- The top root exposes right-identity input bookkeeping counts. -/
theorem AnalyticMotivesRoot.traceCorQRelationGenerator_rightIdentitySupportInput_traceBookkeepingCount
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

/-- The top root exposes Fubini input rewrite-step counts. -/
theorem AnalyticMotivesRoot.traceCorQRelationGenerator_fubiniSupportInput_rewriteStepCount
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

/-- The top root exposes schedule-exchange input rewrite-step counts. -/
theorem AnalyticMotivesRoot.traceCorQRelationGenerator_scheduleExchangeSupportInput_rewriteStepCount
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

/-- The top root exposes residue-channel input rewrite-step counts. -/
theorem AnalyticMotivesRoot.traceCorQRelationGenerator_residueChannelSupportInput_rewriteStepCount
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

/-- The top root exposes Stokes-residue input rewrite-step counts. -/
theorem AnalyticMotivesRoot.traceCorQRelationGenerator_stokesResidueSupportInput_rewriteStepCount
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

/-- The top root exposes refinement input rewrite-step counts. -/
theorem AnalyticMotivesRoot.traceCorQRelationGenerator_refinementSupportInput_rewriteStepCount
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

/-- The top root exposes associativity input rewrite-step counts. -/
theorem AnalyticMotivesRoot.traceCorQRelationGenerator_associativitySupportInput_rewriteStepCount
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

/-- The top root exposes left-identity input rewrite-step counts. -/
theorem AnalyticMotivesRoot.traceCorQRelationGenerator_leftIdentitySupportInput_rewriteStepCount
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

/-- The top root exposes right-identity input rewrite-step counts. -/
theorem AnalyticMotivesRoot.traceCorQRelationGenerator_rightIdentitySupportInput_rewriteStepCount
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
