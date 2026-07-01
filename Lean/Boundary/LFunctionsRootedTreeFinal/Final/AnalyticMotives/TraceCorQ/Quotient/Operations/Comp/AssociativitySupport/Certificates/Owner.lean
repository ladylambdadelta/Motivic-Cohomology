import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Quotient.Operations.Comp.AssociativitySupport.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.LedgeredTransports.Certificates.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Quotient.RelationWitness.Generators.Certificates.Owner

/-!
# Certificates for associativity support relations

This file records the analytic certificate ledger carried by the concrete
associativity support witness.  The certificate is the coherence-cell
certificate of the ledgered transport associativity cell.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- The associativity relation generator carries the associativity coherence certificate. -/
theorem LedgeredTraceTransport.associativityRelationGenerator_certificateLedger
    (first second third : LedgeredTraceTransport) :
    (LedgeredTraceTransport.associativityRelationGenerator
      first
      second
      third).certificateLedger =
      LedgeredTraceTransport.associativityCertificateLedger
        first
        second
        third :=
  rfl

/-- The associativity support witness carries the singleton associativity certificate ledger. -/
theorem LedgeredTraceTransport.associativitySupportWitness_certificateLedger
    (first second third : LedgeredTraceTransport) :
    (LedgeredTraceTransport.associativitySupportWitness
      first
      second
      third).certificateLedger =
      ResidueChannelCertificateLedger.append
        (LedgeredTraceTransport.associativityCertificateLedger
          first
          second
          third)
        ResidueChannelCertificateLedger.empty :=
  TraceCorQRelationGenerator.supportWitness_certificateLedger_eq_generator
    (LedgeredTraceTransport.associativityRelationGenerator
      first
      second
      third)

end AnalyticMotives
end LFunctions
end Boundary
