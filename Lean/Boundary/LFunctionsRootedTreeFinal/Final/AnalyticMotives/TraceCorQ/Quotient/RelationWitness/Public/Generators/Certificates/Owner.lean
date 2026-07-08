import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Quotient.RelationWitness.Generators.Certificates.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Quotient.RelationWitness.Public.Generators.Certificates.Payload.Owner

/-!
# Public generated support-witness certificates

This file exposes certificate-ledger identities for the canonical relation
witness attached to a relation generator under the `TraceCorQ` aggregate
namespace.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- The trace-correspondence root exposes support-witness certificate ledgers by singleton ledger. -/
theorem TraceCorQ.relationGenerator_supportWitness_certificateLedger
    (relation : TraceCorQRelationGenerator) :
    (TraceCorQRelationGenerator.supportWitness relation).certificateLedger =
      (TraceCorQRelationLedger.singleton relation).certificateLedger :=
  TraceCorQRelationGenerator.supportWitness_certificateLedger
    relation

/-- The trace-correspondence root exposes support-witness certificate ledgers by generator. -/
theorem TraceCorQ.relationGenerator_supportWitness_certificateLedger_eq_generator
    (relation : TraceCorQRelationGenerator) :
    (TraceCorQRelationGenerator.supportWitness relation).certificateLedger =
      ResidueChannelCertificateLedger.append
        relation.certificateLedger
        ResidueChannelCertificateLedger.empty :=
  TraceCorQRelationGenerator.supportWitness_certificateLedger_eq_generator
    relation

/-- The trace-correspondence root exposes support-witness certified-coherence-cell ledgers. -/
theorem TraceCorQ.relationGenerator_supportWitness_certificateLedger_eq_certifiedCell
    (relation : TraceCorQRelationGenerator) :
    (TraceCorQRelationGenerator.supportWitness relation).certificateLedger =
      ResidueChannelCertificateLedger.append
        (ResidueChannelCertificateLedger.ofCertifiedCoherenceCell
          relation.cell)
        ResidueChannelCertificateLedger.empty :=
  TraceCorQRelationGenerator.supportWitness_certificateLedger_eq_certifiedCell
    relation

/-- The trace-correspondence root exposes support-witness path and coherence-cell certificates. -/
theorem TraceCorQ.relationGenerator_supportWitness_certificateLedger_eq_paths_cell
    (relation : TraceCorQRelationGenerator) :
    (TraceCorQRelationGenerator.supportWitness relation).certificateLedger =
      ResidueChannelCertificateLedger.append
        (ResidueChannelCertificateAtom.rewritePath relation.cell.source ::
          ResidueChannelCertificateAtom.rewritePath relation.cell.target ::
            ResidueChannelCertificateAtom.coherenceCell relation.cell ::
              ResidueChannelCertificateLedger.empty)
        ResidueChannelCertificateLedger.empty :=
  TraceCorQRelationGenerator.supportWitness_certificateLedger_eq_paths_cell
    relation

end AnalyticMotives
end LFunctions
end Boundary
