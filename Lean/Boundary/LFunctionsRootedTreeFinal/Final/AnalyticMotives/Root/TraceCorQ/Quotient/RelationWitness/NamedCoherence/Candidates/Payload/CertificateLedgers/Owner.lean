import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Quotient.RelationWitness.Generators.NamedCoherence.Candidates.CertificateLedgers.Owner

/-!
# Top-root certificate payload for named-coherence candidates

This file exposes certificate-ledger decompositions for named-coherence support
candidates.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- The top root exposes Fubini candidate certificate splitting. -/
theorem AnalyticMotivesRoot.traceCorQRelationGenerator_fubiniSupportCandidate_certificateLedger
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

/-- The top root exposes schedule-exchange candidate certificate splitting. -/
theorem AnalyticMotivesRoot.traceCorQRelationGenerator_scheduleExchangeSupportCandidate_certificateLedger
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

/-- The top root exposes residue-channel candidate certificate splitting. -/
theorem AnalyticMotivesRoot.traceCorQRelationGenerator_residueChannelSupportCandidate_certificateLedger
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

/-- The top root exposes Stokes-residue candidate certificate splitting. -/
theorem AnalyticMotivesRoot.traceCorQRelationGenerator_stokesResidueSupportCandidate_certificateLedger
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

/-- The top root exposes refinement candidate certificate splitting. -/
theorem AnalyticMotivesRoot.traceCorQRelationGenerator_refinementSupportCandidate_certificateLedger
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

/-- The top root exposes associativity candidate certificate splitting. -/
theorem AnalyticMotivesRoot.traceCorQRelationGenerator_associativitySupportCandidate_certificateLedger
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

/-- The top root exposes left-identity candidate certificate splitting. -/
theorem AnalyticMotivesRoot.traceCorQRelationGenerator_leftIdentitySupportCandidate_certificateLedger
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

/-- The top root exposes right-identity candidate certificate splitting. -/
theorem AnalyticMotivesRoot.traceCorQRelationGenerator_rightIdentitySupportCandidate_certificateLedger
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
