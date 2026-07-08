import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Facade.Objects.Owner

/-!
# Top-root trace-correspondence object facade

This file exposes `TraceCorQ` object payload wrappers under
`AnalyticMotivesRoot`.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- The top root exposes trace-correspondence object imported-rectangle counts. -/
theorem AnalyticMotivesRoot.traceCorQObject_importedRectangleCount_eq_length
    (object : TraceCorQObject) :
    object.importedRectangleCount =
      object.importedRectangles.length :=
  TraceCorQ.object_importedRectangleCount_eq_length
    object

/-- The top root exposes trace-correspondence object certificate extension. -/
def AnalyticMotivesRoot.traceCorQObject_withAdditionalCertificates
    (object : TraceCorQObject)
    (certificates : ResidueChannelCertificateLedger) :
    TraceCorQObject :=
  TraceCorQ.object_withAdditionalCertificates
    object
    certificates

/-- The top root exposes source preservation under object certificate extension. -/
theorem AnalyticMotivesRoot.traceCorQObject_withAdditionalCertificates_source
    (object : TraceCorQObject)
    (certificates : ResidueChannelCertificateLedger) :
    (object.withAdditionalCertificates certificates).source =
      object.source :=
  TraceCorQ.object_withAdditionalCertificates_source
    object
    certificates

/-- The top root exposes ledger preservation under object certificate extension. -/
theorem AnalyticMotivesRoot.traceCorQObject_withAdditionalCertificates_ledger
    (object : TraceCorQObject)
    (certificates : ResidueChannelCertificateLedger) :
    (object.withAdditionalCertificates certificates).ledger =
      object.ledger :=
  TraceCorQ.object_withAdditionalCertificates_ledger
    object
    certificates

/-- The top root exposes channel preservation under object certificate extension. -/
theorem AnalyticMotivesRoot.traceCorQObject_withAdditionalCertificates_channels
    (object : TraceCorQObject)
    (certificates : ResidueChannelCertificateLedger) :
    (object.withAdditionalCertificates certificates).channels =
      object.channels :=
  TraceCorQ.object_withAdditionalCertificates_channels
    object
    certificates

/-- The top root exposes schedule preservation under object certificate extension. -/
theorem AnalyticMotivesRoot.traceCorQObject_withAdditionalCertificates_schedule
    (object : TraceCorQObject)
    (certificates : ResidueChannelCertificateLedger) :
    (object.withAdditionalCertificates certificates).schedule =
      object.schedule :=
  TraceCorQ.object_withAdditionalCertificates_schedule
    object
    certificates

/-- The top root exposes certificate-ledger extension for trace-correspondence objects. -/
theorem AnalyticMotivesRoot.traceCorQObject_withAdditionalCertificates_certificateLedger
    (object : TraceCorQObject)
    (certificates : ResidueChannelCertificateLedger) :
    (object.withAdditionalCertificates certificates).certificateLedger =
      ResidueChannelCertificateLedger.append
        object.certificateLedger
        certificates :=
  TraceCorQ.object_withAdditionalCertificates_certificateLedger
    object
    certificates

/-- The top root exposes imported-rectangle list extension for trace-correspondence objects. -/
theorem AnalyticMotivesRoot.traceCorQObject_withAdditionalCertificates_importedRectangles
    (object : TraceCorQObject)
    (certificates : ResidueChannelCertificateLedger) :
    (object.withAdditionalCertificates certificates).importedRectangles =
      object.importedRectangles ++
        certificates.importedRectangles :=
  TraceCorQ.object_withAdditionalCertificates_importedRectangles
    object
    certificates

/-- The top root exposes imported-rectangle payload extension for trace-correspondence objects. -/
theorem AnalyticMotivesRoot.traceCorQObject_withAdditionalCertificates_importedRectangleCount
    (object : TraceCorQObject)
    (certificates : ResidueChannelCertificateLedger) :
    (object.withAdditionalCertificates certificates).importedRectangleCount =
      object.importedRectangleCount +
        certificates.importedRectangleCount :=
  TraceCorQ.object_withAdditionalCertificates_importedRectangleCount
    object
    certificates

/-- The top root exposes bookkeeping payload extension for trace-correspondence objects. -/
theorem AnalyticMotivesRoot.traceCorQObject_withAdditionalCertificates_traceBookkeepingCount
    (object : TraceCorQObject)
    (certificates : ResidueChannelCertificateLedger) :
    (object.withAdditionalCertificates certificates).traceBookkeepingCount =
      object.traceBookkeepingCount +
        certificates.traceBookkeepingCount :=
  TraceCorQ.object_withAdditionalCertificates_traceBookkeepingCount
    object
    certificates

/-- The top root exposes rewrite-step payload extension for trace-correspondence objects. -/
theorem AnalyticMotivesRoot.traceCorQObject_withAdditionalCertificates_rewriteStepCount
    (object : TraceCorQObject)
    (certificates : ResidueChannelCertificateLedger) :
    (object.withAdditionalCertificates certificates).rewriteStepCount =
      object.rewriteStepCount +
        certificates.rewriteStepCount :=
  TraceCorQ.object_withAdditionalCertificates_rewriteStepCount
    object
    certificates

end AnalyticMotives
end LFunctions
end Boundary
