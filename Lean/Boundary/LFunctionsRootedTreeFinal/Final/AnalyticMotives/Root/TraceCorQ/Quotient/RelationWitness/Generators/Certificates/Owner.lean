import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Quotient.RelationWitness.Public.Generators.Certificates.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Root.TraceCorQ.Quotient.RelationWitness.Generators.Certificates.Payload.Owner

/-!
# Top-root generated relation-witness certificates

This file exposes certificate-ledger projections for the canonical witness
attached to a single relation generator.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- The top root exposes singleton relation-ledger certificates for support witnesses. -/
theorem AnalyticMotivesRoot.traceCorQRelationGenerator_supportWitness_certificateLedger
  (relation : TraceCorQRelationGenerator) :
    (TraceCorQRelationGenerator.supportWitness relation).certificateLedger =
      (TraceCorQRelationLedger.singleton relation).certificateLedger :=
  TraceCorQ.relationGenerator_supportWitness_certificateLedger
    relation

/-- The top root exposes generator certificates for support witnesses. -/
theorem AnalyticMotivesRoot.traceCorQRelationGenerator_supportWitness_certificateLedger_eq_generator
    (relation : TraceCorQRelationGenerator) :
    (TraceCorQRelationGenerator.supportWitness relation).certificateLedger =
      ResidueChannelCertificateLedger.append
        relation.certificateLedger
        ResidueChannelCertificateLedger.empty :=
  TraceCorQ.relationGenerator_supportWitness_certificateLedger_eq_generator
    relation

/-- The top root exposes certified-cell certificates for support witnesses. -/
theorem AnalyticMotivesRoot.traceCorQRelationGenerator_supportWitness_certificateLedger_eq_certifiedCell
    (relation : TraceCorQRelationGenerator) :
    (TraceCorQRelationGenerator.supportWitness relation).certificateLedger =
      ResidueChannelCertificateLedger.append
        (ResidueChannelCertificateLedger.ofCertifiedCoherenceCell
          relation.cell)
        ResidueChannelCertificateLedger.empty :=
  TraceCorQ.relationGenerator_supportWitness_certificateLedger_eq_certifiedCell
    relation

/-- The top root exposes path and coherence-cell certificates for support witnesses. -/
theorem AnalyticMotivesRoot.traceCorQRelationGenerator_supportWitness_certificateLedger_eq_paths_cell
    (relation : TraceCorQRelationGenerator) :
    (TraceCorQRelationGenerator.supportWitness relation).certificateLedger =
      ResidueChannelCertificateLedger.append
        (ResidueChannelCertificateAtom.rewritePath relation.cell.source ::
          ResidueChannelCertificateAtom.rewritePath relation.cell.target ::
            ResidueChannelCertificateAtom.coherenceCell relation.cell ::
              ResidueChannelCertificateLedger.empty)
        ResidueChannelCertificateLedger.empty :=
  TraceCorQ.relationGenerator_supportWitness_certificateLedger_eq_paths_cell
    relation

end AnalyticMotives
end LFunctions
end Boundary
