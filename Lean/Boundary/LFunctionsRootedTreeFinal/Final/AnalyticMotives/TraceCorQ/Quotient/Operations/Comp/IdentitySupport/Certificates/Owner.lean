import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Quotient.Operations.Comp.IdentitySupport.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.LedgeredTransports.Certificates.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Quotient.RelationWitness.Generators.Certificates.Owner

/-!
# Certificates for identity support relations

This file records the analytic certificate ledgers carried by the concrete
left- and right-identity support witnesses.  These certificates record the
identity-composition path, the original path, and the corresponding ledgered
transport identity cell.
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

/-- The left-identity support witness carries the left-identity certificate ledger. -/
theorem LedgeredTraceTransport.leftIdentitySupportWitness_certificateLedger
    (transport : LedgeredTraceTransport) :
    (LedgeredTraceTransport.leftIdentitySupportWitness transport).certificateLedger =
      ResidueChannelCertificateLedger.append
        (LedgeredTraceTransport.leftIdentityCertificateLedger transport)
        ResidueChannelCertificateLedger.empty :=
  TraceCorQRelationGenerator.supportWitness_certificateLedger_eq_generator
    (LedgeredTraceTransport.leftIdentityRelationGenerator transport)

/-- The left-identity support witness exposes the identity-left path, original path, and cell. -/
theorem LedgeredTraceTransport.leftIdentitySupportWitness_certificateLedger_eq_paths_cell
    (transport : LedgeredTraceTransport) :
    (LedgeredTraceTransport.leftIdentitySupportWitness transport).certificateLedger =
      ResidueChannelCertificateLedger.append
        (ResidueChannelCertificateAtom.rewritePath
          ((LedgeredTraceTransport.id transport.source).comp transport).path ::
          ResidueChannelCertificateAtom.rewritePath transport.path ::
            ResidueChannelCertificateAtom.coherenceCell
              (LedgeredTraceTransport.leftIdentityCoherence transport) ::
              ResidueChannelCertificateLedger.empty)
        ResidueChannelCertificateLedger.empty :=
  rfl

/-- The right-identity support witness carries the right-identity certificate ledger. -/
theorem LedgeredTraceTransport.rightIdentitySupportWitness_certificateLedger
    (transport : LedgeredTraceTransport) :
    (LedgeredTraceTransport.rightIdentitySupportWitness transport).certificateLedger =
      ResidueChannelCertificateLedger.append
        (LedgeredTraceTransport.rightIdentityCertificateLedger transport)
        ResidueChannelCertificateLedger.empty :=
  TraceCorQRelationGenerator.supportWitness_certificateLedger_eq_generator
    (LedgeredTraceTransport.rightIdentityRelationGenerator transport)

/-- The right-identity support witness exposes the identity-right path, original path, and cell. -/
theorem LedgeredTraceTransport.rightIdentitySupportWitness_certificateLedger_eq_paths_cell
    (transport : LedgeredTraceTransport) :
    (LedgeredTraceTransport.rightIdentitySupportWitness transport).certificateLedger =
      ResidueChannelCertificateLedger.append
        (ResidueChannelCertificateAtom.rewritePath
          (transport.comp (LedgeredTraceTransport.id transport.target)).path ::
          ResidueChannelCertificateAtom.rewritePath transport.path ::
            ResidueChannelCertificateAtom.coherenceCell
              (LedgeredTraceTransport.rightIdentityCoherence transport) ::
              ResidueChannelCertificateLedger.empty)
        ResidueChannelCertificateLedger.empty :=
  rfl

end AnalyticMotives
end LFunctions
end Boundary
