import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Quotient.RelationWitness.Generators.NamedCoherence.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.RelationLedgers.NamedCoherence.Payload.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Quotient.RelationWitness.Generators.NamedCoherence.Payload.CertificateLedgers.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Quotient.RelationWitness.Generators.NamedCoherence.Payload.ImportedRectangles.Owner

/-!
# Payload facts for named-coherence support witnesses

This file exposes bookkeeping and rewrite-step accounting carried by the
canonical witnesses generated from named coherence relations.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- A Fubini support witness keeps the Fubini ledger bookkeeping payload. -/
theorem TraceCorQRelationGenerator.fubiniSupportWitness_traceBookkeepingCount
    (source target : TraceRewritePath)
    (support : TraceCorQFormalSum) :
    (TraceCorQRelationGenerator.fubiniSupportWitness
      source
      target
      support).traceBookkeepingCount =
      (TraceCorQRelationLedger.fubini source target support).traceBookkeepingCount :=
  TraceCorQRelationWitness.traceBookkeepingCount_eq_ledger
    (TraceCorQRelationGenerator.fubiniSupportWitness source target support)

/-- A schedule-exchange support witness keeps the ledger bookkeeping payload. -/
theorem TraceCorQRelationGenerator.scheduleExchangeSupportWitness_traceBookkeepingCount
    (source target : TraceRewritePath)
    (support : TraceCorQFormalSum) :
    (TraceCorQRelationGenerator.scheduleExchangeSupportWitness
      source
      target
      support).traceBookkeepingCount =
      (TraceCorQRelationLedger.scheduleExchange source target support).traceBookkeepingCount :=
  TraceCorQRelationWitness.traceBookkeepingCount_eq_ledger
    (TraceCorQRelationGenerator.scheduleExchangeSupportWitness source target support)

/-- A residue-channel support witness keeps the ledger bookkeeping payload. -/
theorem TraceCorQRelationGenerator.residueChannelSupportWitness_traceBookkeepingCount
    (source target : TraceRewritePath)
    (support : TraceCorQFormalSum) :
    (TraceCorQRelationGenerator.residueChannelSupportWitness
      source
      target
      support).traceBookkeepingCount =
      (TraceCorQRelationLedger.residueChannel source target support).traceBookkeepingCount :=
  TraceCorQRelationWitness.traceBookkeepingCount_eq_ledger
    (TraceCorQRelationGenerator.residueChannelSupportWitness source target support)

/-- A Stokes-residue support witness keeps the ledger bookkeeping payload. -/
theorem TraceCorQRelationGenerator.stokesResidueSupportWitness_traceBookkeepingCount
    (source target : TraceRewritePath)
    (support : TraceCorQFormalSum) :
    (TraceCorQRelationGenerator.stokesResidueSupportWitness
      source
      target
      support).traceBookkeepingCount =
      (TraceCorQRelationLedger.stokesResidue source target support).traceBookkeepingCount :=
  TraceCorQRelationWitness.traceBookkeepingCount_eq_ledger
    (TraceCorQRelationGenerator.stokesResidueSupportWitness source target support)

/-- A refinement support witness keeps the ledger bookkeeping payload. -/
theorem TraceCorQRelationGenerator.refinementSupportWitness_traceBookkeepingCount
    (source target : TraceRewritePath)
    (support : TraceCorQFormalSum) :
    (TraceCorQRelationGenerator.refinementSupportWitness
      source
      target
      support).traceBookkeepingCount =
      (TraceCorQRelationLedger.refinement source target support).traceBookkeepingCount :=
  TraceCorQRelationWitness.traceBookkeepingCount_eq_ledger
    (TraceCorQRelationGenerator.refinementSupportWitness source target support)

/-- An associativity support witness keeps the ledger bookkeeping payload. -/
theorem TraceCorQRelationGenerator.associativitySupportWitness_traceBookkeepingCount
    (source target : TraceRewritePath)
    (support : TraceCorQFormalSum) :
    (TraceCorQRelationGenerator.associativitySupportWitness
      source
      target
      support).traceBookkeepingCount =
      (TraceCorQRelationLedger.associativity source target support).traceBookkeepingCount :=
  TraceCorQRelationWitness.traceBookkeepingCount_eq_ledger
    (TraceCorQRelationGenerator.associativitySupportWitness source target support)

/-- A left-identity support witness keeps the ledger bookkeeping payload. -/
theorem TraceCorQRelationGenerator.leftIdentitySupportWitness_traceBookkeepingCount
    (source target : TraceRewritePath)
    (support : TraceCorQFormalSum) :
    (TraceCorQRelationGenerator.leftIdentitySupportWitness
      source
      target
      support).traceBookkeepingCount =
      (TraceCorQRelationLedger.leftIdentity source target support).traceBookkeepingCount :=
  TraceCorQRelationWitness.traceBookkeepingCount_eq_ledger
    (TraceCorQRelationGenerator.leftIdentitySupportWitness source target support)

/-- A right-identity support witness keeps the ledger bookkeeping payload. -/
theorem TraceCorQRelationGenerator.rightIdentitySupportWitness_traceBookkeepingCount
    (source target : TraceRewritePath)
    (support : TraceCorQFormalSum) :
    (TraceCorQRelationGenerator.rightIdentitySupportWitness
      source
      target
      support).traceBookkeepingCount =
      (TraceCorQRelationLedger.rightIdentity source target support).traceBookkeepingCount :=
  TraceCorQRelationWitness.traceBookkeepingCount_eq_ledger
    (TraceCorQRelationGenerator.rightIdentitySupportWitness source target support)

/-- A Fubini support witness keeps the Fubini ledger rewrite-step payload. -/
theorem TraceCorQRelationGenerator.fubiniSupportWitness_rewriteStepCount
    (source target : TraceRewritePath)
    (support : TraceCorQFormalSum) :
    (TraceCorQRelationGenerator.fubiniSupportWitness
      source
      target
      support).rewriteStepCount =
      (TraceCorQRelationLedger.fubini source target support).rewriteStepCount :=
  TraceCorQRelationWitness.rewriteStepCount_eq_ledger
    (TraceCorQRelationGenerator.fubiniSupportWitness source target support)

/-- A schedule-exchange support witness keeps the ledger rewrite-step payload. -/
theorem TraceCorQRelationGenerator.scheduleExchangeSupportWitness_rewriteStepCount
    (source target : TraceRewritePath)
    (support : TraceCorQFormalSum) :
    (TraceCorQRelationGenerator.scheduleExchangeSupportWitness
      source
      target
      support).rewriteStepCount =
      (TraceCorQRelationLedger.scheduleExchange source target support).rewriteStepCount :=
  TraceCorQRelationWitness.rewriteStepCount_eq_ledger
    (TraceCorQRelationGenerator.scheduleExchangeSupportWitness source target support)

/-- A residue-channel support witness keeps the ledger rewrite-step payload. -/
theorem TraceCorQRelationGenerator.residueChannelSupportWitness_rewriteStepCount
    (source target : TraceRewritePath)
    (support : TraceCorQFormalSum) :
    (TraceCorQRelationGenerator.residueChannelSupportWitness
      source
      target
      support).rewriteStepCount =
      (TraceCorQRelationLedger.residueChannel source target support).rewriteStepCount :=
  TraceCorQRelationWitness.rewriteStepCount_eq_ledger
    (TraceCorQRelationGenerator.residueChannelSupportWitness source target support)

/-- A Stokes-residue support witness keeps the ledger rewrite-step payload. -/
theorem TraceCorQRelationGenerator.stokesResidueSupportWitness_rewriteStepCount
    (source target : TraceRewritePath)
    (support : TraceCorQFormalSum) :
    (TraceCorQRelationGenerator.stokesResidueSupportWitness
      source
      target
      support).rewriteStepCount =
      (TraceCorQRelationLedger.stokesResidue source target support).rewriteStepCount :=
  TraceCorQRelationWitness.rewriteStepCount_eq_ledger
    (TraceCorQRelationGenerator.stokesResidueSupportWitness source target support)

/-- A refinement support witness keeps the ledger rewrite-step payload. -/
theorem TraceCorQRelationGenerator.refinementSupportWitness_rewriteStepCount
    (source target : TraceRewritePath)
    (support : TraceCorQFormalSum) :
    (TraceCorQRelationGenerator.refinementSupportWitness
      source
      target
      support).rewriteStepCount =
      (TraceCorQRelationLedger.refinement source target support).rewriteStepCount :=
  TraceCorQRelationWitness.rewriteStepCount_eq_ledger
    (TraceCorQRelationGenerator.refinementSupportWitness source target support)

/-- An associativity support witness keeps the ledger rewrite-step payload. -/
theorem TraceCorQRelationGenerator.associativitySupportWitness_rewriteStepCount
    (source target : TraceRewritePath)
    (support : TraceCorQFormalSum) :
    (TraceCorQRelationGenerator.associativitySupportWitness
      source
      target
      support).rewriteStepCount =
      (TraceCorQRelationLedger.associativity source target support).rewriteStepCount :=
  TraceCorQRelationWitness.rewriteStepCount_eq_ledger
    (TraceCorQRelationGenerator.associativitySupportWitness source target support)

/-- A left-identity support witness keeps the ledger rewrite-step payload. -/
theorem TraceCorQRelationGenerator.leftIdentitySupportWitness_rewriteStepCount
    (source target : TraceRewritePath)
    (support : TraceCorQFormalSum) :
    (TraceCorQRelationGenerator.leftIdentitySupportWitness
      source
      target
      support).rewriteStepCount =
      (TraceCorQRelationLedger.leftIdentity source target support).rewriteStepCount :=
  TraceCorQRelationWitness.rewriteStepCount_eq_ledger
    (TraceCorQRelationGenerator.leftIdentitySupportWitness source target support)

/-- A right-identity support witness keeps the ledger rewrite-step payload. -/
theorem TraceCorQRelationGenerator.rightIdentitySupportWitness_rewriteStepCount
    (source target : TraceRewritePath)
    (support : TraceCorQFormalSum) :
    (TraceCorQRelationGenerator.rightIdentitySupportWitness
      source
      target
      support).rewriteStepCount =
      (TraceCorQRelationLedger.rightIdentity source target support).rewriteStepCount :=
  TraceCorQRelationWitness.rewriteStepCount_eq_ledger
    (TraceCorQRelationGenerator.rightIdentitySupportWitness source target support)

end AnalyticMotives
end LFunctions
end Boundary
