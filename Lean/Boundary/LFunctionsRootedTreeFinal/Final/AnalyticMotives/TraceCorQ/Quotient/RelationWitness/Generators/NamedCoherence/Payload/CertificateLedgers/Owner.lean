import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Quotient.RelationWitness.Generators.NamedCoherence.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Quotient.RelationWitness.Certificates.Basic.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Quotient.RelationWitness.Ledgers.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.RelationLedgers.NamedCoherence.Payload.Owner

/-!
# Certificate ledgers for named-coherence support witnesses

This file owns the certificate-ledger projections for named-coherence support
witnesses.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- A Fubini support witness carries the Fubini relation ledger certificates. -/
theorem TraceCorQRelationGenerator.fubiniSupportWitness_certificateLedger
    (source target : TraceRewritePath)
    (support : TraceCorQFormalSum) :
    (TraceCorQRelationGenerator.fubiniSupportWitness
      source
      target
      support).ledger.certificateLedger =
      (TraceCorQRelationLedger.fubini source target support).certificateLedger :=
  TraceCorQRelationWitness.certificateLedger_eq_relationLedger
    (TraceCorQRelationGenerator.fubiniSupportWitness source target support)

/-- A schedule-exchange support witness carries the schedule-exchange ledger certificates. -/
theorem TraceCorQRelationGenerator.scheduleExchangeSupportWitness_certificateLedger
    (source target : TraceRewritePath)
    (support : TraceCorQFormalSum) :
    (TraceCorQRelationGenerator.scheduleExchangeSupportWitness
      source
      target
      support).ledger.certificateLedger =
      (TraceCorQRelationLedger.scheduleExchange source target support).certificateLedger :=
  TraceCorQRelationWitness.certificateLedger_eq_relationLedger
    (TraceCorQRelationGenerator.scheduleExchangeSupportWitness source target support)

/-- A residue-channel support witness carries the residue-channel ledger certificates. -/
theorem TraceCorQRelationGenerator.residueChannelSupportWitness_certificateLedger
    (source target : TraceRewritePath)
    (support : TraceCorQFormalSum) :
    (TraceCorQRelationGenerator.residueChannelSupportWitness
      source
      target
      support).ledger.certificateLedger =
      (TraceCorQRelationLedger.residueChannel source target support).certificateLedger :=
  TraceCorQRelationWitness.certificateLedger_eq_relationLedger
    (TraceCorQRelationGenerator.residueChannelSupportWitness source target support)

/-- A Stokes-residue support witness carries the Stokes-residue ledger certificates. -/
theorem TraceCorQRelationGenerator.stokesResidueSupportWitness_certificateLedger
    (source target : TraceRewritePath)
    (support : TraceCorQFormalSum) :
    (TraceCorQRelationGenerator.stokesResidueSupportWitness
      source
      target
      support).ledger.certificateLedger =
      (TraceCorQRelationLedger.stokesResidue source target support).certificateLedger :=
  TraceCorQRelationWitness.certificateLedger_eq_relationLedger
    (TraceCorQRelationGenerator.stokesResidueSupportWitness source target support)

/-- A refinement support witness carries the refinement relation ledger certificates. -/
theorem TraceCorQRelationGenerator.refinementSupportWitness_certificateLedger
    (source target : TraceRewritePath)
    (support : TraceCorQFormalSum) :
    (TraceCorQRelationGenerator.refinementSupportWitness
      source
      target
      support).ledger.certificateLedger =
      (TraceCorQRelationLedger.refinement source target support).certificateLedger :=
  TraceCorQRelationWitness.certificateLedger_eq_relationLedger
    (TraceCorQRelationGenerator.refinementSupportWitness source target support)

/-- An associativity support witness carries the associativity ledger certificates. -/
theorem TraceCorQRelationGenerator.associativitySupportWitness_certificateLedger
    (source target : TraceRewritePath)
    (support : TraceCorQFormalSum) :
    (TraceCorQRelationGenerator.associativitySupportWitness
      source
      target
      support).ledger.certificateLedger =
      (TraceCorQRelationLedger.associativity source target support).certificateLedger :=
  TraceCorQRelationWitness.certificateLedger_eq_relationLedger
    (TraceCorQRelationGenerator.associativitySupportWitness source target support)

/-- A left-identity support witness carries the left-identity ledger certificates. -/
theorem TraceCorQRelationGenerator.leftIdentitySupportWitness_certificateLedger
    (source target : TraceRewritePath)
    (support : TraceCorQFormalSum) :
    (TraceCorQRelationGenerator.leftIdentitySupportWitness
      source
      target
      support).ledger.certificateLedger =
      (TraceCorQRelationLedger.leftIdentity source target support).certificateLedger :=
  TraceCorQRelationWitness.certificateLedger_eq_relationLedger
    (TraceCorQRelationGenerator.leftIdentitySupportWitness source target support)

/-- A right-identity support witness carries the right-identity ledger certificates. -/
theorem TraceCorQRelationGenerator.rightIdentitySupportWitness_certificateLedger
    (source target : TraceRewritePath)
    (support : TraceCorQFormalSum) :
    (TraceCorQRelationGenerator.rightIdentitySupportWitness
      source
      target
      support).ledger.certificateLedger =
      (TraceCorQRelationLedger.rightIdentity source target support).certificateLedger :=
  TraceCorQRelationWitness.certificateLedger_eq_relationLedger
    (TraceCorQRelationGenerator.rightIdentitySupportWitness source target support)

end AnalyticMotives
end LFunctions
end Boundary
