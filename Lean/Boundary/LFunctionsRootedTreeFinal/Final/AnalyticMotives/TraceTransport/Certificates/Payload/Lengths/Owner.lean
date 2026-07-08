import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceTransport.Certificates.Owner

/-!
# Trace-transport certificate length facts

This file owns imported-rectangle length invariants for transport certificate
ledgers and the identity/composition transport constructors.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- A transport path certificate count is the length of its rectangle list. -/
theorem TraceTransport.pathCertificateLedger_importedRectangleCount_eq_length
    (transport : TraceTransport) :
    transport.pathCertificateLedger.importedRectangleCount =
      transport.pathCertificateLedger.importedRectangles.length :=
  ResidueChannelCertificateLedger.importedRectangleCount_eq_length_importedRectangles
    transport.pathCertificateLedger

/-- The identity path certificate count is the length of its rectangle list. -/
theorem TraceTransport.id_pathCertificateLedger_importedRectangleCount_eq_length
    (object : TraceTransportObject) :
    (TraceTransport.id object).pathCertificateLedger.importedRectangleCount =
      (TraceTransport.id object).pathCertificateLedger.importedRectangles.length :=
  TraceTransport.pathCertificateLedger_importedRectangleCount_eq_length
    (TraceTransport.id object)

/-- The composed path certificate count is the length of its rectangle list. -/
theorem TraceTransport.comp_pathCertificateLedger_importedRectangleCount_eq_length
    (first second : TraceTransport) :
    (TraceTransport.comp
      first
      second).pathCertificateLedger.importedRectangleCount =
      (TraceTransport.comp
        first
        second).pathCertificateLedger.importedRectangles.length :=
  TraceTransport.pathCertificateLedger_importedRectangleCount_eq_length
    (TraceTransport.comp first second)

/-- The identity transport imported count is the length of its rectangle list. -/
theorem TraceTransport.id_importedRectangleCount_eq_length
    (object : TraceTransportObject) :
    (TraceTransport.id object).importedRectangleCount =
      (TraceTransport.id object).importedRectangles.length :=
  TraceTransport.importedRectangleCount_eq_length_importedRectangles
    (TraceTransport.id object)

/-- The composed transport imported count is the length of its rectangle list. -/
theorem TraceTransport.comp_importedRectangleCount_eq_length
    (first second : TraceTransport) :
    (TraceTransport.comp first second).importedRectangleCount =
      (TraceTransport.comp first second).importedRectangles.length :=
  TraceTransport.importedRectangleCount_eq_length_importedRectangles
    (TraceTransport.comp first second)

end AnalyticMotives
end LFunctions
end Boundary
