import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceTransport.Composition.Owner

/-!
# Core trace-transport certificate ledgers

This file owns the analytic certificate ledger canonically attached to a raw
trace transport.  The ledger records source presentation certificates, target
presentation certificates, and the rewrite path carried by the transport.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- The path certificate ledger of a trace transport. -/
def TraceTransport.pathCertificateLedger
    (transport : TraceTransport) :
    ResidueChannelCertificateLedger :=
  ResidueChannelCertificateLedger.ofRewritePath transport.path

/-- The canonical analytic certificate ledger carried by a trace transport. -/
def TraceTransport.certificateLedger
    (transport : TraceTransport) :
    ResidueChannelCertificateLedger :=
  ResidueChannelCertificateLedger.append
    transport.source.certificateLedger
    (ResidueChannelCertificateLedger.append
      transport.target.certificateLedger
      transport.pathCertificateLedger)

/-- The imported finite-rectangle analytic payload carried by a trace transport. -/
def TraceTransport.importedRectangleCount
    (transport : TraceTransport) :
    Nat :=
  transport.certificateLedger.importedRectangleCount

/-- The imported finite explicit-formula rectangles carried by a trace transport. -/
def TraceTransport.importedRectangles
    (transport : TraceTransport) :
    List ZetaAdmissibleFunction.ExplicitFormulaRectangle :=
  transport.certificateLedger.importedRectangles

/-- The internal trace-bookkeeping payload carried by a trace transport. -/
def TraceTransport.traceBookkeepingCount
    (transport : TraceTransport) :
    Nat :=
  transport.certificateLedger.traceBookkeepingCount

/-- The explicit rewrite-step payload carried by a trace transport. -/
def TraceTransport.rewriteStepCount
    (transport : TraceTransport) :
    Nat :=
  transport.certificateLedger.rewriteStepCount

/-- A transport certificate ledger is source certificates, target certificates, then path certificates. -/
theorem TraceTransport.certificateLedger_eq_source_target_path
    (transport : TraceTransport) :
    transport.certificateLedger =
      ResidueChannelCertificateLedger.append
        transport.source.certificateLedger
        (ResidueChannelCertificateLedger.append
          transport.target.certificateLedger
          transport.pathCertificateLedger) :=
  rfl

/-- A transport's imported payload splits into source, target, and path payload. -/
theorem TraceTransport.importedRectangleCount_eq_source_target_path
    (transport : TraceTransport) :
    transport.importedRectangleCount =
      transport.source.importedRectangleCount +
        (transport.target.importedRectangleCount +
          transport.pathCertificateLedger.importedRectangleCount) :=
  Eq.trans
    (ResidueChannelCertificateLedger.append_importedRectangleCount
      transport.source.certificateLedger
      (ResidueChannelCertificateLedger.append
        transport.target.certificateLedger
        transport.pathCertificateLedger))
    (congrArg
      (fun count => transport.source.importedRectangleCount + count)
      (ResidueChannelCertificateLedger.append_importedRectangleCount
        transport.target.certificateLedger
        transport.pathCertificateLedger))

/-- A transport's imported rectangles split into source, target, and path payload. -/
theorem TraceTransport.importedRectangles_eq_source_target_path
    (transport : TraceTransport) :
    transport.importedRectangles =
      transport.source.importedRectangles ++
        (transport.target.importedRectangles ++
          transport.pathCertificateLedger.importedRectangles) :=
  Eq.trans
    (ResidueChannelCertificateLedger.append_importedRectangles
      transport.source.certificateLedger
      (ResidueChannelCertificateLedger.append
        transport.target.certificateLedger
        transport.pathCertificateLedger))
    (congrArg
      (fun rectangles => transport.source.importedRectangles ++ rectangles)
      (ResidueChannelCertificateLedger.append_importedRectangles
        transport.target.certificateLedger
        transport.pathCertificateLedger))

/-- Imported-rectangle count is the length of the extracted transport rectangle list. -/
theorem TraceTransport.importedRectangleCount_eq_length_importedRectangles
    (transport : TraceTransport) :
    transport.importedRectangleCount =
      transport.importedRectangles.length :=
  ResidueChannelCertificateLedger.importedRectangleCount_eq_length_importedRectangles
    transport.certificateLedger

/-- A transport's bookkeeping payload splits into source, target, and path payload. -/
theorem TraceTransport.traceBookkeepingCount_eq_source_target_path
    (transport : TraceTransport) :
    transport.traceBookkeepingCount =
      transport.source.traceBookkeepingCount +
        (transport.target.traceBookkeepingCount +
          transport.pathCertificateLedger.traceBookkeepingCount) :=
  Eq.trans
    (ResidueChannelCertificateLedger.append_traceBookkeepingCount
      transport.source.certificateLedger
      (ResidueChannelCertificateLedger.append
        transport.target.certificateLedger
        transport.pathCertificateLedger))
    (congrArg
      (fun count => transport.source.traceBookkeepingCount + count)
      (ResidueChannelCertificateLedger.append_traceBookkeepingCount
        transport.target.certificateLedger
        transport.pathCertificateLedger))

/-- A transport's explicit rewrite-step payload splits into source, target, and path payload. -/
theorem TraceTransport.rewriteStepCount_eq_source_target_path
    (transport : TraceTransport) :
    transport.rewriteStepCount =
      transport.source.rewriteStepCount +
        (transport.target.rewriteStepCount +
          transport.pathCertificateLedger.rewriteStepCount) :=
  Eq.trans
    (ResidueChannelCertificateLedger.append_rewriteStepCount
      transport.source.certificateLedger
      (ResidueChannelCertificateLedger.append
        transport.target.certificateLedger
        transport.pathCertificateLedger))
    (congrArg
      (fun count => transport.source.rewriteStepCount + count)
      (ResidueChannelCertificateLedger.append_rewriteStepCount
        transport.target.certificateLedger
        transport.pathCertificateLedger))

end AnalyticMotives
end LFunctions
end Boundary
