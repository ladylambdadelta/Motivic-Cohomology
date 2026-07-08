import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Quotient.RelationWitness.Generators.NamedCoherence.Payload.CertificateLedgers.Owner

/-!
# Top-root certificate payload for named-coherence witnesses

This file exposes certificate-ledger projections for named-coherence
quotient-relation witnesses.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- The top root exposes Fubini witness certificate ledgers. -/
theorem AnalyticMotivesRoot.traceCorQRelationGenerator_fubiniSupportWitness_certificateLedger
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

/-- The top root exposes schedule-exchange witness certificate ledgers. -/
theorem AnalyticMotivesRoot.traceCorQRelationGenerator_scheduleExchangeSupportWitness_certificateLedger
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

/-- The top root exposes residue-channel witness certificate ledgers. -/
theorem AnalyticMotivesRoot.traceCorQRelationGenerator_residueChannelSupportWitness_certificateLedger
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

/-- The top root exposes Stokes-residue witness certificate ledgers. -/
theorem AnalyticMotivesRoot.traceCorQRelationGenerator_stokesResidueSupportWitness_certificateLedger
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

/-- The top root exposes refinement witness certificate ledgers. -/
theorem AnalyticMotivesRoot.traceCorQRelationGenerator_refinementSupportWitness_certificateLedger
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

/-- The top root exposes associativity witness certificate ledgers. -/
theorem AnalyticMotivesRoot.traceCorQRelationGenerator_associativitySupportWitness_certificateLedger
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

/-- The top root exposes left-identity witness certificate ledgers. -/
theorem AnalyticMotivesRoot.traceCorQRelationGenerator_leftIdentitySupportWitness_certificateLedger
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

/-- The top root exposes right-identity witness certificate ledgers. -/
theorem AnalyticMotivesRoot.traceCorQRelationGenerator_rightIdentitySupportWitness_certificateLedger
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
