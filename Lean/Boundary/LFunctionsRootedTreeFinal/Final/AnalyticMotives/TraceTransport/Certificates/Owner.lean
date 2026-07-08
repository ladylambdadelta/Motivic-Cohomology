import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceTransport.Certificates.Core.Owner

/-!
# Trace-transport certificate ledgers

This file records identity and composition computations for the analytic
certificate ledger canonically attached to a raw trace transport.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- The identity transport's path certificate ledger is the singleton identity path certificate. -/
theorem TraceTransport.id_pathCertificateLedger
    (object : TraceTransportObject) :
    (TraceTransport.id object).pathCertificateLedger =
      ResidueChannelCertificateLedger.ofRewritePath
        (TraceRewritePath.id object.source) :=
  rfl

/-- The identity transport path certificate carries no imported finite rectangles. -/
theorem TraceTransport.id_pathCertificateLedger_importedRectangleCount
    (object : TraceTransportObject) :
    (TraceTransport.id object).pathCertificateLedger.importedRectangleCount =
      0 + 0 :=
  rfl

/-- The identity transport path certificate exposes no imported finite rectangles. -/
theorem TraceTransport.id_pathCertificateLedger_importedRectangles
    (object : TraceTransportObject) :
    (TraceTransport.id object).pathCertificateLedger.importedRectangles =
      [] ++ [] :=
  rfl

/-- The identity transport path certificate is one bookkeeping atom. -/
theorem TraceTransport.id_pathCertificateLedger_traceBookkeepingCount
    (object : TraceTransportObject) :
    (TraceTransport.id object).pathCertificateLedger.traceBookkeepingCount =
      1 + 0 :=
  rfl

/-- The identity transport path certificate has no rewrite steps. -/
theorem TraceTransport.id_pathCertificateLedger_rewriteStepCount
    (object : TraceTransportObject) :
    (TraceTransport.id object).pathCertificateLedger.rewriteStepCount =
      0 + 0 :=
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

/-- The identity transport exposes the imported rectangles of the endpoint presentations. -/
theorem TraceTransport.id_importedRectangles
    (object : TraceTransportObject) :
    (TraceTransport.id object).importedRectangles =
      object.importedRectangles ++
        (object.importedRectangles ++
          (ResidueChannelCertificateLedger.ofRewritePath
            (TraceRewritePath.id object.source)).importedRectangles) :=
  Eq.trans
    (ResidueChannelCertificateLedger.append_importedRectangles
      object.certificateLedger
      (ResidueChannelCertificateLedger.append
        object.certificateLedger
        (ResidueChannelCertificateLedger.ofRewritePath
          (TraceRewritePath.id object.source))))
    (congrArg
      (fun rectangles => object.importedRectangles ++ rectangles)
      (ResidueChannelCertificateLedger.append_importedRectangles
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

/-- The identity transport's explicit rewrite-step payload comes from endpoints and its identity path. -/
theorem TraceTransport.id_rewriteStepCount
    (object : TraceTransportObject) :
    (TraceTransport.id object).rewriteStepCount =
      object.rewriteStepCount +
        (object.rewriteStepCount +
          (ResidueChannelCertificateLedger.ofRewritePath
            (TraceRewritePath.id object.source)).rewriteStepCount) :=
  Eq.trans
    (ResidueChannelCertificateLedger.append_rewriteStepCount
      object.certificateLedger
      (ResidueChannelCertificateLedger.append
        object.certificateLedger
        (ResidueChannelCertificateLedger.ofRewritePath
          (TraceRewritePath.id object.source))))
    (congrArg
      (fun count => object.rewriteStepCount + count)
      (ResidueChannelCertificateLedger.append_rewriteStepCount
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

/-- A composed transport path certificate carries no imported finite rectangles. -/
theorem TraceTransport.comp_pathCertificateLedger_importedRectangleCount
    (first second : TraceTransport) :
    (TraceTransport.comp
      first
      second).pathCertificateLedger.importedRectangleCount =
      0 + 0 :=
  rfl

/-- A composed transport path certificate exposes no imported finite rectangles. -/
theorem TraceTransport.comp_pathCertificateLedger_importedRectangles
    (first second : TraceTransport) :
    (TraceTransport.comp
      first
      second).pathCertificateLedger.importedRectangles =
      [] ++ [] :=
  rfl

/-- A composed transport path certificate is one bookkeeping atom. -/
theorem TraceTransport.comp_pathCertificateLedger_traceBookkeepingCount
    (first second : TraceTransport) :
    (TraceTransport.comp
      first
      second).pathCertificateLedger.traceBookkeepingCount =
      1 + 0 :=
  rfl

/-- A composed transport path certificate counts rewrite steps from both factors. -/
theorem TraceTransport.comp_pathCertificateLedger_rewriteStepCount
    (first second : TraceTransport) :
    (TraceTransport.comp
      first
      second).pathCertificateLedger.rewriteStepCount =
      first.path.stepCount + second.path.stepCount + 0 :=
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

/-- A composed transport exposes imported rectangles from its exposed endpoints and path. -/
theorem TraceTransport.comp_importedRectangles
    (first second : TraceTransport) :
    (TraceTransport.comp first second).importedRectangles =
      first.source.importedRectangles ++
        (second.target.importedRectangles ++
          (ResidueChannelCertificateLedger.ofRewritePath
            (first.path.comp second.path)).importedRectangles) :=
  Eq.trans
    (ResidueChannelCertificateLedger.append_importedRectangles
      first.source.certificateLedger
      (ResidueChannelCertificateLedger.append
        second.target.certificateLedger
        (ResidueChannelCertificateLedger.ofRewritePath
          (first.path.comp second.path))))
    (congrArg
      (fun rectangles => first.source.importedRectangles ++ rectangles)
      (ResidueChannelCertificateLedger.append_importedRectangles
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

/-- A composed transport's explicit rewrite-step payload comes from exposed endpoints and path. -/
theorem TraceTransport.comp_rewriteStepCount
    (first second : TraceTransport) :
    (TraceTransport.comp first second).rewriteStepCount =
      first.source.rewriteStepCount +
        (second.target.rewriteStepCount +
          (ResidueChannelCertificateLedger.ofRewritePath
            (first.path.comp second.path)).rewriteStepCount) :=
  Eq.trans
    (ResidueChannelCertificateLedger.append_rewriteStepCount
      first.source.certificateLedger
      (ResidueChannelCertificateLedger.append
        second.target.certificateLedger
        (ResidueChannelCertificateLedger.ofRewritePath
          (first.path.comp second.path))))
    (congrArg
      (fun count => first.source.rewriteStepCount + count)
      (ResidueChannelCertificateLedger.append_rewriteStepCount
        second.target.certificateLedger
        (ResidueChannelCertificateLedger.ofRewritePath
          (first.path.comp second.path))))

end AnalyticMotives
end LFunctions
end Boundary
