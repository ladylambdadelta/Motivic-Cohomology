import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Quotient.RelationWitness.Generators.NamedCoherence.Payload.CertificateLedgers.Owner

/-!
# Public named-coherence support-witness certificate ledgers

This file exposes certificate-ledger projections for named-coherence support
witnesses under the `TraceCorQ` aggregate namespace.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- The trace-correspondence root exposes Fubini support-witness certificate ledgers. -/
theorem TraceCorQ.relationGenerator_fubiniSupportWitness_certificateLedger
    (source target : TraceRewritePath)
    (support : TraceCorQFormalSum) :
    (TraceCorQRelationGenerator.fubiniSupportWitness
      source
      target
      support).ledger.certificateLedger =
      (TraceCorQRelationLedger.fubini source target support).certificateLedger :=
  TraceCorQRelationGenerator.fubiniSupportWitness_certificateLedger
    source
    target
    support

/-- The trace-correspondence root exposes schedule-exchange support-witness certificate ledgers. -/
theorem TraceCorQ.relationGenerator_scheduleExchangeSupportWitness_certificateLedger
    (source target : TraceRewritePath)
    (support : TraceCorQFormalSum) :
    (TraceCorQRelationGenerator.scheduleExchangeSupportWitness
      source
      target
      support).ledger.certificateLedger =
      (TraceCorQRelationLedger.scheduleExchange source target support).certificateLedger :=
  TraceCorQRelationGenerator.scheduleExchangeSupportWitness_certificateLedger
    source
    target
    support

/-- The trace-correspondence root exposes residue-channel support-witness certificate ledgers. -/
theorem TraceCorQ.relationGenerator_residueChannelSupportWitness_certificateLedger
    (source target : TraceRewritePath)
    (support : TraceCorQFormalSum) :
    (TraceCorQRelationGenerator.residueChannelSupportWitness
      source
      target
      support).ledger.certificateLedger =
      (TraceCorQRelationLedger.residueChannel source target support).certificateLedger :=
  TraceCorQRelationGenerator.residueChannelSupportWitness_certificateLedger
    source
    target
    support

/-- The trace-correspondence root exposes Stokes-residue support-witness certificate ledgers. -/
theorem TraceCorQ.relationGenerator_stokesResidueSupportWitness_certificateLedger
    (source target : TraceRewritePath)
    (support : TraceCorQFormalSum) :
    (TraceCorQRelationGenerator.stokesResidueSupportWitness
      source
      target
      support).ledger.certificateLedger =
      (TraceCorQRelationLedger.stokesResidue source target support).certificateLedger :=
  TraceCorQRelationGenerator.stokesResidueSupportWitness_certificateLedger
    source
    target
    support

/-- The trace-correspondence root exposes refinement support-witness certificate ledgers. -/
theorem TraceCorQ.relationGenerator_refinementSupportWitness_certificateLedger
    (source target : TraceRewritePath)
    (support : TraceCorQFormalSum) :
    (TraceCorQRelationGenerator.refinementSupportWitness
      source
      target
      support).ledger.certificateLedger =
      (TraceCorQRelationLedger.refinement source target support).certificateLedger :=
  TraceCorQRelationGenerator.refinementSupportWitness_certificateLedger
    source
    target
    support

/-- The trace-correspondence root exposes associativity support-witness certificate ledgers. -/
theorem TraceCorQ.relationGenerator_associativitySupportWitness_certificateLedger
    (source target : TraceRewritePath)
    (support : TraceCorQFormalSum) :
    (TraceCorQRelationGenerator.associativitySupportWitness
      source
      target
      support).ledger.certificateLedger =
      (TraceCorQRelationLedger.associativity source target support).certificateLedger :=
  TraceCorQRelationGenerator.associativitySupportWitness_certificateLedger
    source
    target
    support

/-- The trace-correspondence root exposes left-identity support-witness certificate ledgers. -/
theorem TraceCorQ.relationGenerator_leftIdentitySupportWitness_certificateLedger
    (source target : TraceRewritePath)
    (support : TraceCorQFormalSum) :
    (TraceCorQRelationGenerator.leftIdentitySupportWitness
      source
      target
      support).ledger.certificateLedger =
      (TraceCorQRelationLedger.leftIdentity source target support).certificateLedger :=
  TraceCorQRelationGenerator.leftIdentitySupportWitness_certificateLedger
    source
    target
    support

/-- The trace-correspondence root exposes right-identity support-witness certificate ledgers. -/
theorem TraceCorQ.relationGenerator_rightIdentitySupportWitness_certificateLedger
    (source target : TraceRewritePath)
    (support : TraceCorQFormalSum) :
    (TraceCorQRelationGenerator.rightIdentitySupportWitness
      source
      target
      support).ledger.certificateLedger =
      (TraceCorQRelationLedger.rightIdentity source target support).certificateLedger :=
  TraceCorQRelationGenerator.rightIdentitySupportWitness_certificateLedger
    source
    target
    support

end AnalyticMotives
end LFunctions
end Boundary
