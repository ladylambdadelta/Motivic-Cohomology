import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceTransport.Certificates.Payload.Lengths.Owner

/-!
# Trace-transport certificate payload facts

This file owns the payload surface for trace-transport certificates.  The
nested length owner proves imported-rectangle count invariants for path
certificate ledgers and identity/composition transports; this owner re-exposes
them at the certificate payload boundary.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- The transport-certificate payload surface exposes path-certificate rectangle counts. -/
theorem TraceTransportCertificatePayload.pathCertificateLedger_importedRectangleCount_eq_length
    (transport : TraceTransport) :
    transport.pathCertificateLedger.importedRectangleCount =
      transport.pathCertificateLedger.importedRectangles.length :=
  TraceTransport.pathCertificateLedger_importedRectangleCount_eq_length
    transport

/-- The transport-certificate payload surface exposes identity path-certificate rectangle counts. -/
theorem TraceTransportCertificatePayload.id_pathCertificateLedger_importedRectangleCount_eq_length
    (object : TraceTransportObject) :
    (TraceTransport.id object).pathCertificateLedger.importedRectangleCount =
      (TraceTransport.id object).pathCertificateLedger.importedRectangles.length :=
  TraceTransport.id_pathCertificateLedger_importedRectangleCount_eq_length
    object

/-- The transport-certificate payload surface exposes composite path-certificate rectangle counts. -/
theorem TraceTransportCertificatePayload.comp_pathCertificateLedger_importedRectangleCount_eq_length
    (first second : TraceTransport) :
    (TraceTransport.comp
      first
      second).pathCertificateLedger.importedRectangleCount =
      (TraceTransport.comp
        first
        second).pathCertificateLedger.importedRectangles.length :=
  TraceTransport.comp_pathCertificateLedger_importedRectangleCount_eq_length
    first
    second

/-- The transport-certificate payload surface exposes identity transport rectangle counts. -/
theorem TraceTransportCertificatePayload.id_importedRectangleCount_eq_length
    (object : TraceTransportObject) :
    (TraceTransport.id object).importedRectangleCount =
      (TraceTransport.id object).importedRectangles.length :=
  TraceTransport.id_importedRectangleCount_eq_length
    object

/-- The transport-certificate payload surface exposes composite transport rectangle counts. -/
theorem TraceTransportCertificatePayload.comp_importedRectangleCount_eq_length
    (first second : TraceTransport) :
    (TraceTransport.comp first second).importedRectangleCount =
      (TraceTransport.comp first second).importedRectangles.length :=
  TraceTransport.comp_importedRectangleCount_eq_length
    first
    second

end AnalyticMotives
end LFunctions
end Boundary
