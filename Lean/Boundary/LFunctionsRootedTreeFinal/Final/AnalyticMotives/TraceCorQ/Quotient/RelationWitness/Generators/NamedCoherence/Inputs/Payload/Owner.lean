import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Quotient.RelationWitness.Generators.NamedCoherence.Inputs.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Quotient.RelationWitness.Generators.NamedCoherence.Inputs.Payload.CertificateLedgers.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Quotient.RelationWitness.Generators.NamedCoherence.Inputs.Payload.ImportedRectangles.Owner

/-!
# Payload facts for named-coherence support inputs

This file records bookkeeping and rewrite-step payload facts for named
coherence support inputs.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- A Fubini support input splits trace bookkeeping into support and ledger payload. -/
theorem TraceCorQRelationGenerator.fubiniSupportInput_traceBookkeepingCount
    (source target : TraceRewritePath)
    (support : TraceCorQFormalSum) :
    (TraceCorQRelationGenerator.fubiniSupportInput
      source
      target
      support).traceBookkeepingCount =
      support.traceBookkeepingCount +
        (TraceCorQRelationLedger.fubini source target support).traceBookkeepingCount :=
  TraceCorQQuotientInput.traceBookkeepingCount_eq_formalSum_ledger
    (TraceCorQRelationGenerator.fubiniSupportInput source target support)

/-- A schedule-exchange support input splits trace bookkeeping. -/
theorem TraceCorQRelationGenerator.scheduleExchangeSupportInput_traceBookkeepingCount
    (source target : TraceRewritePath)
    (support : TraceCorQFormalSum) :
    (TraceCorQRelationGenerator.scheduleExchangeSupportInput
      source
      target
      support).traceBookkeepingCount =
      support.traceBookkeepingCount +
        (TraceCorQRelationLedger.scheduleExchange source target support).traceBookkeepingCount :=
  TraceCorQQuotientInput.traceBookkeepingCount_eq_formalSum_ledger
    (TraceCorQRelationGenerator.scheduleExchangeSupportInput source target support)

/-- A residue-channel support input splits trace bookkeeping. -/
theorem TraceCorQRelationGenerator.residueChannelSupportInput_traceBookkeepingCount
    (source target : TraceRewritePath)
    (support : TraceCorQFormalSum) :
    (TraceCorQRelationGenerator.residueChannelSupportInput
      source
      target
      support).traceBookkeepingCount =
      support.traceBookkeepingCount +
        (TraceCorQRelationLedger.residueChannel source target support).traceBookkeepingCount :=
  TraceCorQQuotientInput.traceBookkeepingCount_eq_formalSum_ledger
    (TraceCorQRelationGenerator.residueChannelSupportInput source target support)

/-- A Stokes-residue support input splits trace bookkeeping. -/
theorem TraceCorQRelationGenerator.stokesResidueSupportInput_traceBookkeepingCount
    (source target : TraceRewritePath)
    (support : TraceCorQFormalSum) :
    (TraceCorQRelationGenerator.stokesResidueSupportInput
      source
      target
      support).traceBookkeepingCount =
      support.traceBookkeepingCount +
        (TraceCorQRelationLedger.stokesResidue source target support).traceBookkeepingCount :=
  TraceCorQQuotientInput.traceBookkeepingCount_eq_formalSum_ledger
    (TraceCorQRelationGenerator.stokesResidueSupportInput source target support)

/-- A refinement support input splits trace bookkeeping. -/
theorem TraceCorQRelationGenerator.refinementSupportInput_traceBookkeepingCount
    (source target : TraceRewritePath)
    (support : TraceCorQFormalSum) :
    (TraceCorQRelationGenerator.refinementSupportInput
      source
      target
      support).traceBookkeepingCount =
      support.traceBookkeepingCount +
        (TraceCorQRelationLedger.refinement source target support).traceBookkeepingCount :=
  TraceCorQQuotientInput.traceBookkeepingCount_eq_formalSum_ledger
    (TraceCorQRelationGenerator.refinementSupportInput source target support)

/-- An associativity support input splits trace bookkeeping. -/
theorem TraceCorQRelationGenerator.associativitySupportInput_traceBookkeepingCount
    (source target : TraceRewritePath)
    (support : TraceCorQFormalSum) :
    (TraceCorQRelationGenerator.associativitySupportInput
      source
      target
      support).traceBookkeepingCount =
      support.traceBookkeepingCount +
        (TraceCorQRelationLedger.associativity source target support).traceBookkeepingCount :=
  TraceCorQQuotientInput.traceBookkeepingCount_eq_formalSum_ledger
    (TraceCorQRelationGenerator.associativitySupportInput source target support)

/-- A left-identity support input splits trace bookkeeping. -/
theorem TraceCorQRelationGenerator.leftIdentitySupportInput_traceBookkeepingCount
    (source target : TraceRewritePath)
    (support : TraceCorQFormalSum) :
    (TraceCorQRelationGenerator.leftIdentitySupportInput
      source
      target
      support).traceBookkeepingCount =
      support.traceBookkeepingCount +
        (TraceCorQRelationLedger.leftIdentity source target support).traceBookkeepingCount :=
  TraceCorQQuotientInput.traceBookkeepingCount_eq_formalSum_ledger
    (TraceCorQRelationGenerator.leftIdentitySupportInput source target support)

/-- A right-identity support input splits trace bookkeeping. -/
theorem TraceCorQRelationGenerator.rightIdentitySupportInput_traceBookkeepingCount
    (source target : TraceRewritePath)
    (support : TraceCorQFormalSum) :
    (TraceCorQRelationGenerator.rightIdentitySupportInput
      source
      target
      support).traceBookkeepingCount =
      support.traceBookkeepingCount +
        (TraceCorQRelationLedger.rightIdentity source target support).traceBookkeepingCount :=
  TraceCorQQuotientInput.traceBookkeepingCount_eq_formalSum_ledger
    (TraceCorQRelationGenerator.rightIdentitySupportInput source target support)

/-- A Fubini support input splits rewrite-step payload into support and ledger payload. -/
theorem TraceCorQRelationGenerator.fubiniSupportInput_rewriteStepCount
    (source target : TraceRewritePath)
    (support : TraceCorQFormalSum) :
    (TraceCorQRelationGenerator.fubiniSupportInput
      source
      target
      support).rewriteStepCount =
      support.rewriteStepCount +
        (TraceCorQRelationLedger.fubini source target support).rewriteStepCount :=
  TraceCorQQuotientInput.rewriteStepCount_eq_formalSum_ledger
    (TraceCorQRelationGenerator.fubiniSupportInput source target support)

/-- A schedule-exchange support input splits rewrite-step payload. -/
theorem TraceCorQRelationGenerator.scheduleExchangeSupportInput_rewriteStepCount
    (source target : TraceRewritePath)
    (support : TraceCorQFormalSum) :
    (TraceCorQRelationGenerator.scheduleExchangeSupportInput
      source
      target
      support).rewriteStepCount =
      support.rewriteStepCount +
        (TraceCorQRelationLedger.scheduleExchange source target support).rewriteStepCount :=
  TraceCorQQuotientInput.rewriteStepCount_eq_formalSum_ledger
    (TraceCorQRelationGenerator.scheduleExchangeSupportInput source target support)

/-- A residue-channel support input splits rewrite-step payload. -/
theorem TraceCorQRelationGenerator.residueChannelSupportInput_rewriteStepCount
    (source target : TraceRewritePath)
    (support : TraceCorQFormalSum) :
    (TraceCorQRelationGenerator.residueChannelSupportInput
      source
      target
      support).rewriteStepCount =
      support.rewriteStepCount +
        (TraceCorQRelationLedger.residueChannel source target support).rewriteStepCount :=
  TraceCorQQuotientInput.rewriteStepCount_eq_formalSum_ledger
    (TraceCorQRelationGenerator.residueChannelSupportInput source target support)

/-- A Stokes-residue support input splits rewrite-step payload. -/
theorem TraceCorQRelationGenerator.stokesResidueSupportInput_rewriteStepCount
    (source target : TraceRewritePath)
    (support : TraceCorQFormalSum) :
    (TraceCorQRelationGenerator.stokesResidueSupportInput
      source
      target
      support).rewriteStepCount =
      support.rewriteStepCount +
        (TraceCorQRelationLedger.stokesResidue source target support).rewriteStepCount :=
  TraceCorQQuotientInput.rewriteStepCount_eq_formalSum_ledger
    (TraceCorQRelationGenerator.stokesResidueSupportInput source target support)

/-- A refinement support input splits rewrite-step payload. -/
theorem TraceCorQRelationGenerator.refinementSupportInput_rewriteStepCount
    (source target : TraceRewritePath)
    (support : TraceCorQFormalSum) :
    (TraceCorQRelationGenerator.refinementSupportInput
      source
      target
      support).rewriteStepCount =
      support.rewriteStepCount +
        (TraceCorQRelationLedger.refinement source target support).rewriteStepCount :=
  TraceCorQQuotientInput.rewriteStepCount_eq_formalSum_ledger
    (TraceCorQRelationGenerator.refinementSupportInput source target support)

/-- An associativity support input splits rewrite-step payload. -/
theorem TraceCorQRelationGenerator.associativitySupportInput_rewriteStepCount
    (source target : TraceRewritePath)
    (support : TraceCorQFormalSum) :
    (TraceCorQRelationGenerator.associativitySupportInput
      source
      target
      support).rewriteStepCount =
      support.rewriteStepCount +
        (TraceCorQRelationLedger.associativity source target support).rewriteStepCount :=
  TraceCorQQuotientInput.rewriteStepCount_eq_formalSum_ledger
    (TraceCorQRelationGenerator.associativitySupportInput source target support)

/-- A left-identity support input splits rewrite-step payload. -/
theorem TraceCorQRelationGenerator.leftIdentitySupportInput_rewriteStepCount
    (source target : TraceRewritePath)
    (support : TraceCorQFormalSum) :
    (TraceCorQRelationGenerator.leftIdentitySupportInput
      source
      target
      support).rewriteStepCount =
      support.rewriteStepCount +
        (TraceCorQRelationLedger.leftIdentity source target support).rewriteStepCount :=
  TraceCorQQuotientInput.rewriteStepCount_eq_formalSum_ledger
    (TraceCorQRelationGenerator.leftIdentitySupportInput source target support)

/-- A right-identity support input splits rewrite-step payload. -/
theorem TraceCorQRelationGenerator.rightIdentitySupportInput_rewriteStepCount
    (source target : TraceRewritePath)
    (support : TraceCorQFormalSum) :
    (TraceCorQRelationGenerator.rightIdentitySupportInput
      source
      target
      support).rewriteStepCount =
      support.rewriteStepCount +
        (TraceCorQRelationLedger.rightIdentity source target support).rewriteStepCount :=
  TraceCorQQuotientInput.rewriteStepCount_eq_formalSum_ledger
    (TraceCorQRelationGenerator.rightIdentitySupportInput source target support)

end AnalyticMotives
end LFunctions
end Boundary
