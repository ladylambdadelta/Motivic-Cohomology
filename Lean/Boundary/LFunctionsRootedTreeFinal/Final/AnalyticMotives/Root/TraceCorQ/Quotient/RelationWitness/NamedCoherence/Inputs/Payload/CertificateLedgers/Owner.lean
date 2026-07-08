import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Quotient.RelationWitness.Generators.NamedCoherence.Inputs.Payload.CertificateLedgers.Owner

/-!
# Top-root certificate payload for named-coherence inputs

This file exposes certificate-ledger decompositions for named-coherence support
inputs.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- The top root exposes Fubini input certificate splitting. -/
theorem AnalyticMotivesRoot.traceCorQRelationGenerator_fubiniSupportInput_certificateLedger
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

/-- The top root exposes schedule-exchange input certificate splitting. -/
theorem AnalyticMotivesRoot.traceCorQRelationGenerator_scheduleExchangeSupportInput_certificateLedger
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

/-- The top root exposes residue-channel input certificate splitting. -/
theorem AnalyticMotivesRoot.traceCorQRelationGenerator_residueChannelSupportInput_certificateLedger
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

/-- The top root exposes Stokes-residue input certificate splitting. -/
theorem AnalyticMotivesRoot.traceCorQRelationGenerator_stokesResidueSupportInput_certificateLedger
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

/-- The top root exposes refinement input certificate splitting. -/
theorem AnalyticMotivesRoot.traceCorQRelationGenerator_refinementSupportInput_certificateLedger
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

/-- The top root exposes associativity input certificate splitting. -/
theorem AnalyticMotivesRoot.traceCorQRelationGenerator_associativitySupportInput_certificateLedger
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

/-- The top root exposes left-identity input certificate splitting. -/
theorem AnalyticMotivesRoot.traceCorQRelationGenerator_leftIdentitySupportInput_certificateLedger
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

/-- The top root exposes right-identity input certificate splitting. -/
theorem AnalyticMotivesRoot.traceCorQRelationGenerator_rightIdentitySupportInput_certificateLedger
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
