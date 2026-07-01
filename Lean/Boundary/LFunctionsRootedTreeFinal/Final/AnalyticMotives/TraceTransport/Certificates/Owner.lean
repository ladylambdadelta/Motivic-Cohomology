import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceTransport.Composition.Owner

/-!
# Trace-transport certificate ledgers

This file owns the analytic certificate ledger canonically attached to a raw
trace transport.  The ledger records the source presentation certificates, the
target presentation certificates, and the rewrite path carried by the
transport.
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

/-- The internal trace-bookkeeping payload carried by a trace transport. -/
def TraceTransport.traceBookkeepingCount
    (transport : TraceTransport) :
    Nat :=
  transport.certificateLedger.traceBookkeepingCount

/-- The identity transport's path certificate ledger is the singleton identity path certificate. -/
theorem TraceTransport.id_pathCertificateLedger
    (object : TraceTransportObject) :
    (TraceTransport.id object).pathCertificateLedger =
      ResidueChannelCertificateLedger.ofRewritePath
        (TraceRewritePath.id object.source) :=
  rfl

/-- The identity transport's certificate ledger contains object certificates and the identity path. -/
theorem TraceTransport.id_certificateLedger
    (object : TraceTransportObject) :
    (TraceTransport.id object).certificateLedger =
      ResidueChannelCertificateLedger.append
        object.certificateLedger
        (ResidueChannelCertificateLedger.append
          object.certificateLedger
          (ResidueChannelCertificateLedger.ofRewritePath
            (TraceRewritePath.id object.source))) :=
  rfl

/-- The identity transport's imported payload comes from its two endpoint presentations. -/
theorem TraceTransport.id_importedRectangleCount
    (object : TraceTransportObject) :
    (TraceTransport.id object).importedRectangleCount =
      object.importedRectangleCount +
        (object.importedRectangleCount +
          (ResidueChannelCertificateLedger.ofRewritePath
            (TraceRewritePath.id object.source)).importedRectangleCount) :=
  Eq.trans
    (ResidueChannelCertificateLedger.append_importedRectangleCount
      object.certificateLedger
      (ResidueChannelCertificateLedger.append
        object.certificateLedger
        (ResidueChannelCertificateLedger.ofRewritePath
          (TraceRewritePath.id object.source))))
    (congrArg
      (fun count => object.importedRectangleCount + count)
      (ResidueChannelCertificateLedger.append_importedRectangleCount
        object.certificateLedger
        (ResidueChannelCertificateLedger.ofRewritePath
          (TraceRewritePath.id object.source))))

/-- The identity transport's bookkeeping payload comes from endpoints and its identity path. -/
theorem TraceTransport.id_traceBookkeepingCount
    (object : TraceTransportObject) :
    (TraceTransport.id object).traceBookkeepingCount =
      object.traceBookkeepingCount +
        (object.traceBookkeepingCount +
          (ResidueChannelCertificateLedger.ofRewritePath
            (TraceRewritePath.id object.source)).traceBookkeepingCount) :=
  Eq.trans
    (ResidueChannelCertificateLedger.append_traceBookkeepingCount
      object.certificateLedger
      (ResidueChannelCertificateLedger.append
        object.certificateLedger
        (ResidueChannelCertificateLedger.ofRewritePath
          (TraceRewritePath.id object.source))))
    (congrArg
      (fun count => object.traceBookkeepingCount + count)
      (ResidueChannelCertificateLedger.append_traceBookkeepingCount
        object.certificateLedger
        (ResidueChannelCertificateLedger.ofRewritePath
          (TraceRewritePath.id object.source))))

/-- The path certificate ledger of a composed transport certifies the concatenated path. -/
theorem TraceTransport.comp_pathCertificateLedger
    (first second : TraceTransport) :
    (TraceTransport.comp first second).pathCertificateLedger =
      ResidueChannelCertificateLedger.ofRewritePath
        (first.path.comp second.path) :=
  rfl

/-- The canonical certificate ledger of a composed transport follows its endpoints and path. -/
theorem TraceTransport.comp_certificateLedger
    (first second : TraceTransport) :
    (TraceTransport.comp first second).certificateLedger =
      ResidueChannelCertificateLedger.append
        first.source.certificateLedger
        (ResidueChannelCertificateLedger.append
          second.target.certificateLedger
          (ResidueChannelCertificateLedger.ofRewritePath
            (first.path.comp second.path))) :=
  rfl

/-- A composed transport's imported payload comes from its exposed endpoints and path. -/
theorem TraceTransport.comp_importedRectangleCount
    (first second : TraceTransport) :
    (TraceTransport.comp first second).importedRectangleCount =
      first.source.importedRectangleCount +
        (second.target.importedRectangleCount +
          (ResidueChannelCertificateLedger.ofRewritePath
            (first.path.comp second.path)).importedRectangleCount) :=
  Eq.trans
    (ResidueChannelCertificateLedger.append_importedRectangleCount
      first.source.certificateLedger
      (ResidueChannelCertificateLedger.append
        second.target.certificateLedger
        (ResidueChannelCertificateLedger.ofRewritePath
          (first.path.comp second.path))))
    (congrArg
      (fun count => first.source.importedRectangleCount + count)
      (ResidueChannelCertificateLedger.append_importedRectangleCount
        second.target.certificateLedger
        (ResidueChannelCertificateLedger.ofRewritePath
          (first.path.comp second.path))))

/-- A composed transport's bookkeeping payload comes from its exposed endpoints and path. -/
theorem TraceTransport.comp_traceBookkeepingCount
    (first second : TraceTransport) :
    (TraceTransport.comp first second).traceBookkeepingCount =
      first.source.traceBookkeepingCount +
        (second.target.traceBookkeepingCount +
          (ResidueChannelCertificateLedger.ofRewritePath
            (first.path.comp second.path)).traceBookkeepingCount) :=
  Eq.trans
    (ResidueChannelCertificateLedger.append_traceBookkeepingCount
      first.source.certificateLedger
      (ResidueChannelCertificateLedger.append
        second.target.certificateLedger
        (ResidueChannelCertificateLedger.ofRewritePath
          (first.path.comp second.path))))
    (congrArg
      (fun count => first.source.traceBookkeepingCount + count)
      (ResidueChannelCertificateLedger.append_traceBookkeepingCount
        second.target.certificateLedger
        (ResidueChannelCertificateLedger.ofRewritePath
          (first.path.comp second.path))))

end AnalyticMotives
end LFunctions
end Boundary
