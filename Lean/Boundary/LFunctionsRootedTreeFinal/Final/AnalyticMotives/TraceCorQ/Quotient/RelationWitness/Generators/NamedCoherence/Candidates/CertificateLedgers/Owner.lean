import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Quotient.RelationWitness.Generators.NamedCoherence.Candidates.Projections.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.RelationLedgers.NamedCoherence.Payload.Owner

/-!
# Certificate ledgers for named-coherence support candidates

This file owns the certificate-ledger decompositions for named-coherence
support candidates.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- A Fubini support candidate splits certificates into support and Fubini ledger certificates. -/
theorem TraceCorQRelationGenerator.fubiniSupportCandidate_certificateLedger
    (source target : TraceRewritePath)
    (support : TraceCorQFormalSum) :
    (TraceCorQRelationGenerator.fubiniSupportCandidate
      source
      target
      support).certificateLedger =
      ResidueChannelCertificateLedger.append
        support.certificateLedger
        (TraceCorQRelationLedger.fubini source target support).certificateLedger :=
  TraceCorQQuotientCandidate.certificateLedger_eq_formalSum_ledger
    (TraceCorQRelationGenerator.fubiniSupportCandidate source target support)

/-- A schedule-exchange support candidate splits certificates into support and ledger certificates. -/
theorem TraceCorQRelationGenerator.scheduleExchangeSupportCandidate_certificateLedger
    (source target : TraceRewritePath)
    (support : TraceCorQFormalSum) :
    (TraceCorQRelationGenerator.scheduleExchangeSupportCandidate
      source
      target
      support).certificateLedger =
      ResidueChannelCertificateLedger.append
        support.certificateLedger
        (TraceCorQRelationLedger.scheduleExchange source target support).certificateLedger :=
  TraceCorQQuotientCandidate.certificateLedger_eq_formalSum_ledger
    (TraceCorQRelationGenerator.scheduleExchangeSupportCandidate source target support)

/-- A residue-channel support candidate splits certificates into support and ledger certificates. -/
theorem TraceCorQRelationGenerator.residueChannelSupportCandidate_certificateLedger
    (source target : TraceRewritePath)
    (support : TraceCorQFormalSum) :
    (TraceCorQRelationGenerator.residueChannelSupportCandidate
      source
      target
      support).certificateLedger =
      ResidueChannelCertificateLedger.append
        support.certificateLedger
        (TraceCorQRelationLedger.residueChannel source target support).certificateLedger :=
  TraceCorQQuotientCandidate.certificateLedger_eq_formalSum_ledger
    (TraceCorQRelationGenerator.residueChannelSupportCandidate source target support)

/-- A Stokes-residue support candidate splits certificates into support and ledger certificates. -/
theorem TraceCorQRelationGenerator.stokesResidueSupportCandidate_certificateLedger
    (source target : TraceRewritePath)
    (support : TraceCorQFormalSum) :
    (TraceCorQRelationGenerator.stokesResidueSupportCandidate
      source
      target
      support).certificateLedger =
      ResidueChannelCertificateLedger.append
        support.certificateLedger
        (TraceCorQRelationLedger.stokesResidue source target support).certificateLedger :=
  TraceCorQQuotientCandidate.certificateLedger_eq_formalSum_ledger
    (TraceCorQRelationGenerator.stokesResidueSupportCandidate source target support)

/-- A refinement support candidate splits certificates into support and ledger certificates. -/
theorem TraceCorQRelationGenerator.refinementSupportCandidate_certificateLedger
    (source target : TraceRewritePath)
    (support : TraceCorQFormalSum) :
    (TraceCorQRelationGenerator.refinementSupportCandidate
      source
      target
      support).certificateLedger =
      ResidueChannelCertificateLedger.append
        support.certificateLedger
        (TraceCorQRelationLedger.refinement source target support).certificateLedger :=
  TraceCorQQuotientCandidate.certificateLedger_eq_formalSum_ledger
    (TraceCorQRelationGenerator.refinementSupportCandidate source target support)

/-- An associativity support candidate splits certificates into support and ledger certificates. -/
theorem TraceCorQRelationGenerator.associativitySupportCandidate_certificateLedger
    (source target : TraceRewritePath)
    (support : TraceCorQFormalSum) :
    (TraceCorQRelationGenerator.associativitySupportCandidate
      source
      target
      support).certificateLedger =
      ResidueChannelCertificateLedger.append
        support.certificateLedger
        (TraceCorQRelationLedger.associativity source target support).certificateLedger :=
  TraceCorQQuotientCandidate.certificateLedger_eq_formalSum_ledger
    (TraceCorQRelationGenerator.associativitySupportCandidate source target support)

/-- A left-identity support candidate splits certificates into support and ledger certificates. -/
theorem TraceCorQRelationGenerator.leftIdentitySupportCandidate_certificateLedger
    (source target : TraceRewritePath)
    (support : TraceCorQFormalSum) :
    (TraceCorQRelationGenerator.leftIdentitySupportCandidate
      source
      target
      support).certificateLedger =
      ResidueChannelCertificateLedger.append
        support.certificateLedger
        (TraceCorQRelationLedger.leftIdentity source target support).certificateLedger :=
  TraceCorQQuotientCandidate.certificateLedger_eq_formalSum_ledger
    (TraceCorQRelationGenerator.leftIdentitySupportCandidate source target support)

/-- A right-identity support candidate splits certificates into support and ledger certificates. -/
theorem TraceCorQRelationGenerator.rightIdentitySupportCandidate_certificateLedger
    (source target : TraceRewritePath)
    (support : TraceCorQFormalSum) :
    (TraceCorQRelationGenerator.rightIdentitySupportCandidate
      source
      target
      support).certificateLedger =
      ResidueChannelCertificateLedger.append
        support.certificateLedger
        (TraceCorQRelationLedger.rightIdentity source target support).certificateLedger :=
  TraceCorQQuotientCandidate.certificateLedger_eq_formalSum_ledger
    (TraceCorQRelationGenerator.rightIdentitySupportCandidate source target support)

end AnalyticMotives
end LFunctions
end Boundary
