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

/-- The canonical support witness carries the generator's singleton certificates. -/
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

end AnalyticMotives
end LFunctions
end Boundary
