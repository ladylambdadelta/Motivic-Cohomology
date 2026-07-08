import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceTransport.Certificates.Owner

/-!
# Trace-transport defect ledgers

This file names the concrete analytic defect carried by a transport: the
certificate ledger of its rewrite path.  Endpoint presentation certificates
belong to the transported objects; the path ledger is the transport debt.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- The concrete analytic defect ledger of a trace transport. -/
def TraceTransport.defectLedger
    (transport : TraceTransport) :
    ResidueChannelCertificateLedger :=
  transport.pathCertificateLedger

/-- The defect ledger is the path certificate ledger. -/
theorem TraceTransport.defectLedger_eq_pathCertificateLedger
    (transport : TraceTransport) :
    transport.defectLedger =
      transport.pathCertificateLedger :=
  rfl

/-- The defect ledger is the certificate ledger of the carried rewrite path. -/
theorem TraceTransport.defectLedger_eq_rewritePath
    (transport : TraceTransport) :
    transport.defectLedger =
      ResidueChannelCertificateLedger.ofRewritePath transport.path :=
  rfl

/-- Identity transport has the identity path as its defect ledger. -/
theorem TraceTransport.id_defectLedger
    (object : TraceTransportObject) :
    (TraceTransport.id object).defectLedger =
      ResidueChannelCertificateLedger.ofRewritePath
        (TraceRewritePath.id object.source) :=
  rfl

/-- Composite transport has the concatenated rewrite path as its defect ledger. -/
theorem TraceTransport.comp_defectLedger
    (first second : TraceTransport) :
    (TraceTransport.comp first second).defectLedger =
      ResidueChannelCertificateLedger.ofRewritePath
        (first.path.comp second.path) :=
  rfl

/-- Identity transport carries no imported finite rectangles in its defect ledger. -/
theorem TraceTransport.id_defectLedger_importedRectangleCount
    (object : TraceTransportObject) :
    (TraceTransport.id object).defectLedger.importedRectangleCount =
      0 + 0 :=
  rfl

/-- Composite transport carries no imported finite rectangles in its path defect ledger. -/
theorem TraceTransport.comp_defectLedger_importedRectangleCount
    (first second : TraceTransport) :
    (TraceTransport.comp first second).defectLedger.importedRectangleCount =
      0 + 0 :=
  rfl

/-- Identity transport has no rewrite steps in its defect ledger. -/
theorem TraceTransport.id_defectLedger_rewriteStepCount
    (object : TraceTransportObject) :
    (TraceTransport.id object).defectLedger.rewriteStepCount =
      0 + 0 :=
  rfl

/-- The composite defect rewrite count is the sum of the two transport-path
rewrite counts. -/
theorem TraceTransport.comp_defectLedger_rewriteStepCount
    (first second : TraceTransport) :
    (TraceTransport.comp first second).defectLedger.rewriteStepCount =
      first.path.stepCount + second.path.stepCount + 0 :=
  rfl

/-- The first defect layer of a two-step transport composition. -/
def TraceTransport.compFirstDefectLayer
    (first second : TraceTransport) :
    ResidueChannelCertificateLedger :=
  first.defectLedger

/-- The second defect layer of a two-step transport composition. -/
def TraceTransport.compSecondDefectLayer
    (first second : TraceTransport) :
    ResidueChannelCertificateLedger :=
  second.defectLedger

/-- The total defect layer of a two-step transport composition. -/
def TraceTransport.compTotalDefectLayer
    (first second : TraceTransport) :
    ResidueChannelCertificateLedger :=
  (TraceTransport.comp first second).defectLedger

/-- The first layer is the first transport defect ledger. -/
theorem TraceTransport.compFirstDefectLayer_eq
    (first second : TraceTransport) :
    TraceTransport.compFirstDefectLayer first second =
      first.defectLedger :=
  rfl

/-- The second layer is the second transport defect ledger. -/
theorem TraceTransport.compSecondDefectLayer_eq
    (first second : TraceTransport) :
    TraceTransport.compSecondDefectLayer first second =
      second.defectLedger :=
  rfl

/-- The total layer is the composite transport defect ledger. -/
theorem TraceTransport.compTotalDefectLayer_eq
    (first second : TraceTransport) :
    TraceTransport.compTotalDefectLayer first second =
      (TraceTransport.comp first second).defectLedger :=
  rfl

/-- The total two-step defect rewrite count is the sum of the first and second
path rewrite counts, expressed through the named defect layers. -/
theorem TraceTransport.compTotalDefectLayer_rewriteStepCount
    (first second : TraceTransport) :
    (TraceTransport.compTotalDefectLayer first second).rewriteStepCount =
      first.path.stepCount + second.path.stepCount + 0 :=
  rfl

end AnalyticMotives
end LFunctions
end Boundary
