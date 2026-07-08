import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Quotient.RelationWitness.Generators.NamedCoherence.Inputs.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.RelationLedgers.NamedCoherence.Payload.Owner

/-!
# Certificate ledgers for named-coherence support inputs

This file owns the certificate-ledger decompositions for named-coherence
support inputs.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- A Fubini support input splits certificates into support and Fubini ledger certificates. -/
theorem TraceCorQRelationGenerator.fubiniSupportInput_certificateLedger
    (source target : TraceRewritePath)
    (support : TraceCorQFormalSum) :
    (TraceCorQRelationGenerator.fubiniSupportInput
      source
      target
      support).certificateLedger =
      ResidueChannelCertificateLedger.append
        support.certificateLedger
        (TraceCorQRelationLedger.fubini source target support).certificateLedger :=
  TraceCorQQuotientInput.certificateLedger_eq_formalSum_ledger
    (TraceCorQRelationGenerator.fubiniSupportInput source target support)

/-- A schedule-exchange support input splits certificates into support and ledger certificates. -/
theorem TraceCorQRelationGenerator.scheduleExchangeSupportInput_certificateLedger
    (source target : TraceRewritePath)
    (support : TraceCorQFormalSum) :
    (TraceCorQRelationGenerator.scheduleExchangeSupportInput
      source
      target
      support).certificateLedger =
      ResidueChannelCertificateLedger.append
        support.certificateLedger
        (TraceCorQRelationLedger.scheduleExchange source target support).certificateLedger :=
  TraceCorQQuotientInput.certificateLedger_eq_formalSum_ledger
    (TraceCorQRelationGenerator.scheduleExchangeSupportInput source target support)

/-- A residue-channel support input splits certificates into support and ledger certificates. -/
theorem TraceCorQRelationGenerator.residueChannelSupportInput_certificateLedger
    (source target : TraceRewritePath)
    (support : TraceCorQFormalSum) :
    (TraceCorQRelationGenerator.residueChannelSupportInput
      source
      target
      support).certificateLedger =
      ResidueChannelCertificateLedger.append
        support.certificateLedger
        (TraceCorQRelationLedger.residueChannel source target support).certificateLedger :=
  TraceCorQQuotientInput.certificateLedger_eq_formalSum_ledger
    (TraceCorQRelationGenerator.residueChannelSupportInput source target support)

/-- A Stokes-residue support input splits certificates into support and ledger certificates. -/
theorem TraceCorQRelationGenerator.stokesResidueSupportInput_certificateLedger
    (source target : TraceRewritePath)
    (support : TraceCorQFormalSum) :
    (TraceCorQRelationGenerator.stokesResidueSupportInput
      source
      target
      support).certificateLedger =
      ResidueChannelCertificateLedger.append
        support.certificateLedger
        (TraceCorQRelationLedger.stokesResidue source target support).certificateLedger :=
  TraceCorQQuotientInput.certificateLedger_eq_formalSum_ledger
    (TraceCorQRelationGenerator.stokesResidueSupportInput source target support)

/-- A refinement support input splits certificates into support and ledger certificates. -/
theorem TraceCorQRelationGenerator.refinementSupportInput_certificateLedger
    (source target : TraceRewritePath)
    (support : TraceCorQFormalSum) :
    (TraceCorQRelationGenerator.refinementSupportInput
      source
      target
      support).certificateLedger =
      ResidueChannelCertificateLedger.append
        support.certificateLedger
        (TraceCorQRelationLedger.refinement source target support).certificateLedger :=
  TraceCorQQuotientInput.certificateLedger_eq_formalSum_ledger
    (TraceCorQRelationGenerator.refinementSupportInput source target support)

/-- An associativity support input splits certificates into support and ledger certificates. -/
theorem TraceCorQRelationGenerator.associativitySupportInput_certificateLedger
    (source target : TraceRewritePath)
    (support : TraceCorQFormalSum) :
    (TraceCorQRelationGenerator.associativitySupportInput
      source
      target
      support).certificateLedger =
      ResidueChannelCertificateLedger.append
        support.certificateLedger
        (TraceCorQRelationLedger.associativity source target support).certificateLedger :=
  TraceCorQQuotientInput.certificateLedger_eq_formalSum_ledger
    (TraceCorQRelationGenerator.associativitySupportInput source target support)

/-- A left-identity support input splits certificates into support and ledger certificates. -/
theorem TraceCorQRelationGenerator.leftIdentitySupportInput_certificateLedger
    (source target : TraceRewritePath)
    (support : TraceCorQFormalSum) :
    (TraceCorQRelationGenerator.leftIdentitySupportInput
      source
      target
      support).certificateLedger =
      ResidueChannelCertificateLedger.append
        support.certificateLedger
        (TraceCorQRelationLedger.leftIdentity source target support).certificateLedger :=
  TraceCorQQuotientInput.certificateLedger_eq_formalSum_ledger
    (TraceCorQRelationGenerator.leftIdentitySupportInput source target support)

/-- A right-identity support input splits certificates into support and ledger certificates. -/
theorem TraceCorQRelationGenerator.rightIdentitySupportInput_certificateLedger
    (source target : TraceRewritePath)
    (support : TraceCorQFormalSum) :
    (TraceCorQRelationGenerator.rightIdentitySupportInput
      source
      target
      support).certificateLedger =
      ResidueChannelCertificateLedger.append
        support.certificateLedger
        (TraceCorQRelationLedger.rightIdentity source target support).certificateLedger :=
  TraceCorQQuotientInput.certificateLedger_eq_formalSum_ledger
    (TraceCorQRelationGenerator.rightIdentitySupportInput source target support)

end AnalyticMotives
end LFunctions
end Boundary
