import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Quotient.RelationWitness.Generators.NamedCoherence.Candidates.CertificateLedgers.Owner

/-!
# Public named-coherence support-candidate certificate ledgers

This file exposes certificate-ledger decompositions for named-coherence
support candidates under the `TraceCorQ` aggregate namespace.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- The trace-correspondence root exposes Fubini support-candidate certificate ledgers. -/
theorem TraceCorQ.relationGenerator_fubiniSupportCandidate_certificateLedger
    (source target : TraceRewritePath)
    (support : TraceCorQFormalSum) :
    (TraceCorQRelationGenerator.fubiniSupportCandidate
      source
      target
      support).certificateLedger =
      ResidueChannelCertificateLedger.append
        support.certificateLedger
        (TraceCorQRelationLedger.fubini source target support).certificateLedger :=
  TraceCorQRelationGenerator.fubiniSupportCandidate_certificateLedger
    source
    target
    support

/-- The trace-correspondence root exposes schedule-exchange support-candidate certificate ledgers. -/
theorem TraceCorQ.relationGenerator_scheduleExchangeSupportCandidate_certificateLedger
    (source target : TraceRewritePath)
    (support : TraceCorQFormalSum) :
    (TraceCorQRelationGenerator.scheduleExchangeSupportCandidate
      source
      target
      support).certificateLedger =
      ResidueChannelCertificateLedger.append
        support.certificateLedger
        (TraceCorQRelationLedger.scheduleExchange source target support).certificateLedger :=
  TraceCorQRelationGenerator.scheduleExchangeSupportCandidate_certificateLedger
    source
    target
    support

/-- The trace-correspondence root exposes residue-channel support-candidate certificate ledgers. -/
theorem TraceCorQ.relationGenerator_residueChannelSupportCandidate_certificateLedger
    (source target : TraceRewritePath)
    (support : TraceCorQFormalSum) :
    (TraceCorQRelationGenerator.residueChannelSupportCandidate
      source
      target
      support).certificateLedger =
      ResidueChannelCertificateLedger.append
        support.certificateLedger
        (TraceCorQRelationLedger.residueChannel source target support).certificateLedger :=
  TraceCorQRelationGenerator.residueChannelSupportCandidate_certificateLedger
    source
    target
    support

/-- The trace-correspondence root exposes Stokes-residue support-candidate certificate ledgers. -/
theorem TraceCorQ.relationGenerator_stokesResidueSupportCandidate_certificateLedger
    (source target : TraceRewritePath)
    (support : TraceCorQFormalSum) :
    (TraceCorQRelationGenerator.stokesResidueSupportCandidate
      source
      target
      support).certificateLedger =
      ResidueChannelCertificateLedger.append
        support.certificateLedger
        (TraceCorQRelationLedger.stokesResidue source target support).certificateLedger :=
  TraceCorQRelationGenerator.stokesResidueSupportCandidate_certificateLedger
    source
    target
    support

/-- The trace-correspondence root exposes refinement support-candidate certificate ledgers. -/
theorem TraceCorQ.relationGenerator_refinementSupportCandidate_certificateLedger
    (source target : TraceRewritePath)
    (support : TraceCorQFormalSum) :
    (TraceCorQRelationGenerator.refinementSupportCandidate
      source
      target
      support).certificateLedger =
      ResidueChannelCertificateLedger.append
        support.certificateLedger
        (TraceCorQRelationLedger.refinement source target support).certificateLedger :=
  TraceCorQRelationGenerator.refinementSupportCandidate_certificateLedger
    source
    target
    support

/-- The trace-correspondence root exposes associativity support-candidate certificate ledgers. -/
theorem TraceCorQ.relationGenerator_associativitySupportCandidate_certificateLedger
    (source target : TraceRewritePath)
    (support : TraceCorQFormalSum) :
    (TraceCorQRelationGenerator.associativitySupportCandidate
      source
      target
      support).certificateLedger =
      ResidueChannelCertificateLedger.append
        support.certificateLedger
        (TraceCorQRelationLedger.associativity source target support).certificateLedger :=
  TraceCorQRelationGenerator.associativitySupportCandidate_certificateLedger
    source
    target
    support

/-- The trace-correspondence root exposes left-identity support-candidate certificate ledgers. -/
theorem TraceCorQ.relationGenerator_leftIdentitySupportCandidate_certificateLedger
    (source target : TraceRewritePath)
    (support : TraceCorQFormalSum) :
    (TraceCorQRelationGenerator.leftIdentitySupportCandidate
      source
      target
      support).certificateLedger =
      ResidueChannelCertificateLedger.append
        support.certificateLedger
        (TraceCorQRelationLedger.leftIdentity source target support).certificateLedger :=
  TraceCorQRelationGenerator.leftIdentitySupportCandidate_certificateLedger
    source
    target
    support

/-- The trace-correspondence root exposes right-identity support-candidate certificate ledgers. -/
theorem TraceCorQ.relationGenerator_rightIdentitySupportCandidate_certificateLedger
    (source target : TraceRewritePath)
    (support : TraceCorQFormalSum) :
    (TraceCorQRelationGenerator.rightIdentitySupportCandidate
      source
      target
      support).certificateLedger =
      ResidueChannelCertificateLedger.append
        support.certificateLedger
        (TraceCorQRelationLedger.rightIdentity source target support).certificateLedger :=
  TraceCorQRelationGenerator.rightIdentitySupportCandidate_certificateLedger
    source
    target
    support

end AnalyticMotives
end LFunctions
end Boundary
