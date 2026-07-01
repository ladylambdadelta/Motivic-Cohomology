import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Quotient.Operations.Comp.IdentitySupport.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.LedgeredTransports.Certificates.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Quotient.RelationWitness.Generators.Certificates.Owner

/-!
# Certificates for identity support relations

This file records the analytic certificate ledgers carried by the concrete
left- and right-identity support witnesses.  These certificates are exactly
the coherence-cell certificates of the corresponding ledgered transport
identity cells.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- The left-identity relation generator carries the left-identity coherence certificate. -/
theorem LedgeredTraceTransport.leftIdentityRelationGenerator_certificateLedger
    (transport : LedgeredTraceTransport) :
    (LedgeredTraceTransport.leftIdentityRelationGenerator transport).certificateLedger =
      LedgeredTraceTransport.leftIdentityCertificateLedger transport :=
  rfl

/-- The right-identity relation generator carries the right-identity coherence certificate. -/
theorem LedgeredTraceTransport.rightIdentityRelationGenerator_certificateLedger
    (transport : LedgeredTraceTransport) :
    (LedgeredTraceTransport.rightIdentityRelationGenerator transport).certificateLedger =
      LedgeredTraceTransport.rightIdentityCertificateLedger transport :=
  rfl

/-- The left-identity support witness carries the singleton left-identity certificate ledger. -/
theorem LedgeredTraceTransport.leftIdentitySupportWitness_certificateLedger
    (transport : LedgeredTraceTransport) :
    (LedgeredTraceTransport.leftIdentitySupportWitness transport).certificateLedger =
      ResidueChannelCertificateLedger.append
        (LedgeredTraceTransport.leftIdentityCertificateLedger transport)
        ResidueChannelCertificateLedger.empty :=
  TraceCorQRelationGenerator.supportWitness_certificateLedger_eq_generator
    (LedgeredTraceTransport.leftIdentityRelationGenerator transport)

/-- The right-identity support witness carries the singleton right-identity certificate ledger. -/
theorem LedgeredTraceTransport.rightIdentitySupportWitness_certificateLedger
    (transport : LedgeredTraceTransport) :
    (LedgeredTraceTransport.rightIdentitySupportWitness transport).certificateLedger =
      ResidueChannelCertificateLedger.append
        (LedgeredTraceTransport.rightIdentityCertificateLedger transport)
        ResidueChannelCertificateLedger.empty :=
  TraceCorQRelationGenerator.supportWitness_certificateLedger_eq_generator
    (LedgeredTraceTransport.rightIdentityRelationGenerator transport)

end AnalyticMotives
end LFunctions
end Boundary
