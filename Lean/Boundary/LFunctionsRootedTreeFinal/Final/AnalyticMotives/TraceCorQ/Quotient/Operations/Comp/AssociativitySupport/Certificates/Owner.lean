import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Quotient.Operations.Comp.AssociativitySupport.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.LedgeredTransports.Certificates.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Quotient.RelationWitness.Generators.Certificates.Owner

/-!
# Certificates for associativity support relations

This file records the analytic certificate ledger carried by the concrete
associativity support witness.  The certificate records the two compared
triple-composition paths and the ledgered transport associativity cell.
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

/-- The associativity support witness carries the associativity certificate ledger. -/
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

/-- The associativity support witness exposes both triple-composition paths and the cell. -/
theorem LedgeredTraceTransport.associativitySupportWitness_certificateLedger_eq_paths_cell
    (first second third : LedgeredTraceTransport) :
    (LedgeredTraceTransport.associativitySupportWitness
      first
      second
      third).certificateLedger =
      ResidueChannelCertificateLedger.append
        (ResidueChannelCertificateAtom.rewritePath
          ((first.comp second).comp third).path ::
          ResidueChannelCertificateAtom.rewritePath
            (first.comp (second.comp third)).path ::
            ResidueChannelCertificateAtom.coherenceCell
              (LedgeredTraceTransport.compAssociativityCoherence
                first
                second
                third) ::
              ResidueChannelCertificateLedger.empty)
        ResidueChannelCertificateLedger.empty :=
  rfl

end AnalyticMotives
end LFunctions
end Boundary
