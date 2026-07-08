import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Quotient.RelationWitness.Generators.NamedCoherence.Inputs.Payload.CertificateLedgers.Owner

/-!
# Public named-coherence support-input certificate ledgers

This file exposes certificate-ledger decompositions for named-coherence support
inputs under the `TraceCorQ` aggregate namespace.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- The trace-correspondence root exposes Fubini support-input certificate ledgers. -/
theorem TraceCorQ.relationGenerator_fubiniSupportInput_certificateLedger
    (source target : TraceRewritePath)
    (support : TraceCorQFormalSum) :
    (TraceCorQRelationGenerator.fubiniSupportInput
      source
      target
      support).certificateLedger =
      ResidueChannelCertificateLedger.append
        support.certificateLedger
        (TraceCorQRelationLedger.fubini source target support).certificateLedger :=
  TraceCorQRelationGenerator.fubiniSupportInput_certificateLedger
    source
    target
    support

/-- The trace-correspondence root exposes schedule-exchange support-input certificate ledgers. -/
theorem TraceCorQ.relationGenerator_scheduleExchangeSupportInput_certificateLedger
    (source target : TraceRewritePath)
    (support : TraceCorQFormalSum) :
    (TraceCorQRelationGenerator.scheduleExchangeSupportInput
      source
      target
      support).certificateLedger =
      ResidueChannelCertificateLedger.append
        support.certificateLedger
        (TraceCorQRelationLedger.scheduleExchange source target support).certificateLedger :=
  TraceCorQRelationGenerator.scheduleExchangeSupportInput_certificateLedger
    source
    target
    support

/-- The trace-correspondence root exposes residue-channel support-input certificate ledgers. -/
theorem TraceCorQ.relationGenerator_residueChannelSupportInput_certificateLedger
    (source target : TraceRewritePath)
    (support : TraceCorQFormalSum) :
    (TraceCorQRelationGenerator.residueChannelSupportInput
      source
      target
      support).certificateLedger =
      ResidueChannelCertificateLedger.append
        support.certificateLedger
        (TraceCorQRelationLedger.residueChannel source target support).certificateLedger :=
  TraceCorQRelationGenerator.residueChannelSupportInput_certificateLedger
    source
    target
    support

/-- The trace-correspondence root exposes Stokes-residue support-input certificate ledgers. -/
theorem TraceCorQ.relationGenerator_stokesResidueSupportInput_certificateLedger
    (source target : TraceRewritePath)
    (support : TraceCorQFormalSum) :
    (TraceCorQRelationGenerator.stokesResidueSupportInput
      source
      target
      support).certificateLedger =
      ResidueChannelCertificateLedger.append
        support.certificateLedger
        (TraceCorQRelationLedger.stokesResidue source target support).certificateLedger :=
  TraceCorQRelationGenerator.stokesResidueSupportInput_certificateLedger
    source
    target
    support

/-- The trace-correspondence root exposes refinement support-input certificate ledgers. -/
theorem TraceCorQ.relationGenerator_refinementSupportInput_certificateLedger
    (source target : TraceRewritePath)
    (support : TraceCorQFormalSum) :
    (TraceCorQRelationGenerator.refinementSupportInput
      source
      target
      support).certificateLedger =
      ResidueChannelCertificateLedger.append
        support.certificateLedger
        (TraceCorQRelationLedger.refinement source target support).certificateLedger :=
  TraceCorQRelationGenerator.refinementSupportInput_certificateLedger
    source
    target
    support

/-- The trace-correspondence root exposes associativity support-input certificate ledgers. -/
theorem TraceCorQ.relationGenerator_associativitySupportInput_certificateLedger
    (source target : TraceRewritePath)
    (support : TraceCorQFormalSum) :
    (TraceCorQRelationGenerator.associativitySupportInput
      source
      target
      support).certificateLedger =
      ResidueChannelCertificateLedger.append
        support.certificateLedger
        (TraceCorQRelationLedger.associativity source target support).certificateLedger :=
  TraceCorQRelationGenerator.associativitySupportInput_certificateLedger
    source
    target
    support

/-- The trace-correspondence root exposes left-identity support-input certificate ledgers. -/
theorem TraceCorQ.relationGenerator_leftIdentitySupportInput_certificateLedger
    (source target : TraceRewritePath)
    (support : TraceCorQFormalSum) :
    (TraceCorQRelationGenerator.leftIdentitySupportInput
      source
      target
      support).certificateLedger =
      ResidueChannelCertificateLedger.append
        support.certificateLedger
        (TraceCorQRelationLedger.leftIdentity source target support).certificateLedger :=
  TraceCorQRelationGenerator.leftIdentitySupportInput_certificateLedger
    source
    target
    support

/-- The trace-correspondence root exposes right-identity support-input certificate ledgers. -/
theorem TraceCorQ.relationGenerator_rightIdentitySupportInput_certificateLedger
    (source target : TraceRewritePath)
    (support : TraceCorQFormalSum) :
    (TraceCorQRelationGenerator.rightIdentitySupportInput
      source
      target
      support).certificateLedger =
      ResidueChannelCertificateLedger.append
        support.certificateLedger
        (TraceCorQRelationLedger.rightIdentity source target support).certificateLedger :=
  TraceCorQRelationGenerator.rightIdentitySupportInput_certificateLedger
    source
    target
    support

end AnalyticMotives
end LFunctions
end Boundary
