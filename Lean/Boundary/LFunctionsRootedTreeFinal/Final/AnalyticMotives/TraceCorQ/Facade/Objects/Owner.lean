import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Objects.Owner

/-!
# Trace-correspondence object facade

This file exposes the public `TraceCorQ` wrappers for certified
trace-presentation object payloads.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- The trace-correspondence root exposes object imported-rectangle counts. -/
theorem TraceCorQ.object_importedRectangleCount_eq_length
    (object : TraceCorQObject) :
    object.importedRectangleCount =
      object.importedRectangles.length :=
  TraceCorQObject.importedRectangleCount_eq_length_importedRectangles
    object

/-- The trace-correspondence root exposes object certificate extension. -/
def TraceCorQ.object_withAdditionalCertificates
    (object : TraceCorQObject)
    (certificates : ResidueChannelCertificateLedger) :
    TraceCorQObject :=
  TraceCorQObject.withAdditionalCertificates
    object
    certificates

/-- The trace-correspondence root exposes source preservation under certificate extension. -/
theorem TraceCorQ.object_withAdditionalCertificates_source
    (object : TraceCorQObject)
    (certificates : ResidueChannelCertificateLedger) :
    (object.withAdditionalCertificates certificates).source =
      object.source :=
  TraceCorQObject.withAdditionalCertificates_source
    object
    certificates

/-- The trace-correspondence root exposes ledger preservation under certificate extension. -/
theorem TraceCorQ.object_withAdditionalCertificates_ledger
    (object : TraceCorQObject)
    (certificates : ResidueChannelCertificateLedger) :
    (object.withAdditionalCertificates certificates).ledger =
      object.ledger :=
  TraceCorQObject.withAdditionalCertificates_ledger
    object
    certificates

/-- The trace-correspondence root exposes channel preservation under certificate extension. -/
theorem TraceCorQ.object_withAdditionalCertificates_channels
    (object : TraceCorQObject)
    (certificates : ResidueChannelCertificateLedger) :
    (object.withAdditionalCertificates certificates).channels =
      object.channels :=
  TraceCorQObject.withAdditionalCertificates_channels
    object
    certificates

/-- The trace-correspondence root exposes schedule preservation under certificate extension. -/
theorem TraceCorQ.object_withAdditionalCertificates_schedule
    (object : TraceCorQObject)
    (certificates : ResidueChannelCertificateLedger) :
    (object.withAdditionalCertificates certificates).schedule =
      object.schedule :=
  TraceCorQObject.withAdditionalCertificates_schedule
    object
    certificates

/-- The trace-correspondence root exposes object certificate-ledger extension. -/
theorem TraceCorQ.object_withAdditionalCertificates_certificateLedger
    (object : TraceCorQObject)
    (certificates : ResidueChannelCertificateLedger) :
    (object.withAdditionalCertificates certificates).certificateLedger =
      ResidueChannelCertificateLedger.append
        object.certificateLedger
        certificates :=
  TraceCorQObject.withAdditionalCertificates_certificateLedger
    object
    certificates

/-- The trace-correspondence root exposes object imported-rectangle list extension. -/
theorem TraceCorQ.object_withAdditionalCertificates_importedRectangles
    (object : TraceCorQObject)
    (certificates : ResidueChannelCertificateLedger) :
    (object.withAdditionalCertificates certificates).importedRectangles =
      object.importedRectangles ++
        certificates.importedRectangles :=
  TraceCorQObject.withAdditionalCertificates_importedRectangles
    object
    certificates

/-- The trace-correspondence root exposes object imported-rectangle payload extension. -/
theorem TraceCorQ.object_withAdditionalCertificates_importedRectangleCount
    (object : TraceCorQObject)
    (certificates : ResidueChannelCertificateLedger) :
    (object.withAdditionalCertificates certificates).importedRectangleCount =
      object.importedRectangleCount +
        certificates.importedRectangleCount :=
  TraceCorQObject.withAdditionalCertificates_importedRectangleCount
    object
    certificates

/-- The trace-correspondence root exposes object bookkeeping payload extension. -/
theorem TraceCorQ.object_withAdditionalCertificates_traceBookkeepingCount
    (object : TraceCorQObject)
    (certificates : ResidueChannelCertificateLedger) :
    (object.withAdditionalCertificates certificates).traceBookkeepingCount =
      object.traceBookkeepingCount +
        certificates.traceBookkeepingCount :=
  TraceCorQObject.withAdditionalCertificates_traceBookkeepingCount
    object
    certificates

/-- The trace-correspondence root exposes object rewrite-step payload extension. -/
theorem TraceCorQ.object_withAdditionalCertificates_rewriteStepCount
    (object : TraceCorQObject)
    (certificates : ResidueChannelCertificateLedger) :
    (object.withAdditionalCertificates certificates).rewriteStepCount =
      object.rewriteStepCount +
        certificates.rewriteStepCount :=
  TraceCorQObject.withAdditionalCertificates_rewriteStepCount
    object
    certificates

end AnalyticMotives
end LFunctions
end Boundary
