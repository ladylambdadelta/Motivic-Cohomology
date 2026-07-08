import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Quotient.RelationWitness.Generators.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Quotient.RelationWitness.Certificates.Owner

/-!
# Certificate ledgers for generated relation witnesses

This file records the analytic certificates carried by the canonical witness
attached to a single relation generator.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- The canonical support witness carries the singleton relation-ledger certificates. -/
theorem TraceCorQRelationGenerator.supportWitness_certificateLedger
    (relation : TraceCorQRelationGenerator) :
    (TraceCorQRelationGenerator.supportWitness relation).certificateLedger =
      (TraceCorQRelationLedger.singleton relation).certificateLedger :=
  rfl

/-- The canonical support witness carries exactly the generator certificates. -/
theorem TraceCorQRelationGenerator.supportWitness_certificateLedger_eq_generator
    (relation : TraceCorQRelationGenerator) :
    (TraceCorQRelationGenerator.supportWitness relation).certificateLedger =
      ResidueChannelCertificateLedger.append
        relation.certificateLedger
        ResidueChannelCertificateLedger.empty :=
  TraceCorQRelationLedger.singleton_certificateLedger relation

/-- The canonical support witness carries the certified coherence-cell ledger and empty tail. -/
theorem TraceCorQRelationGenerator.supportWitness_certificateLedger_eq_certifiedCell
    (relation : TraceCorQRelationGenerator) :
    (TraceCorQRelationGenerator.supportWitness relation).certificateLedger =
      ResidueChannelCertificateLedger.append
        (ResidueChannelCertificateLedger.ofCertifiedCoherenceCell
          relation.cell)
        ResidueChannelCertificateLedger.empty :=
  TraceCorQRelationGenerator.supportWitness_certificateLedger_eq_generator relation

/-- The canonical support witness exposes the source path, target path, and coherence cell. -/
theorem TraceCorQRelationGenerator.supportWitness_certificateLedger_eq_paths_cell
    (relation : TraceCorQRelationGenerator) :
    (TraceCorQRelationGenerator.supportWitness relation).certificateLedger =
      ResidueChannelCertificateLedger.append
        (ResidueChannelCertificateAtom.rewritePath relation.cell.source ::
          ResidueChannelCertificateAtom.rewritePath relation.cell.target ::
            ResidueChannelCertificateAtom.coherenceCell relation.cell ::
              ResidueChannelCertificateLedger.empty)
        ResidueChannelCertificateLedger.empty :=
  rfl

end AnalyticMotives
end LFunctions
end Boundary
