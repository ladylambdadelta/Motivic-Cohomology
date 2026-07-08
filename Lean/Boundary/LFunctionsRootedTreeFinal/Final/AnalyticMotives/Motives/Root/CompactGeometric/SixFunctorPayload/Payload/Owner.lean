import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Root.CompactGeometric.SixFunctorPayload.Payload.Counts.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Root.CompactGeometric.SixFunctorPayload.Payload.Lengths.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Root.CompactGeometric.SixFunctorPayload.Payload.Rectangles.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Root.CompactGeometric.SixFunctorPayload.Payload.TraceCalculus.Owner

/-!
# Motive-root pullback-pushforward square payload

This file collects motive-root facades for the base compact
pullback-pushforward square payload.  The aggregate surface exposes the
northwest payload formulas across rectangle, length, and trace-calculus
bookkeeping dimensions.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Motive-root aggregate northwest imported-rectangle count formula. -/
theorem TraceAnalyticMotive.publicPayload_northwestImportedRectangleCount
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : source ⟶ target)
    {probeSource probeTarget : TraceAnalyticGeometricGenerator}
    (probe : probeSource ⟶ probeTarget) :
    TraceSixFunctorPullbackPushforward.northwestImportedRectangleCount
        morphism
        probe =
      source.certificateLedger.importedRectangleCount +
        probeTarget.certificateLedger.importedRectangleCount :=
  TraceAnalyticMotive.publicNorthwestImportedRectangleCount_eq_certificateLedgers
    morphism
    probe

/-- Motive-root aggregate northwest imported-rectangle list formula. -/
theorem TraceAnalyticMotive.publicPayload_northwestImportedRectangles
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : source ⟶ target)
    {probeSource probeTarget : TraceAnalyticGeometricGenerator}
    (probe : probeSource ⟶ probeTarget) :
    TraceSixFunctorPullbackPushforward.northwestImportedRectangles
        morphism
        probe =
      source.certificateLedger.importedRectangles ++
        probeTarget.certificateLedger.importedRectangles :=
  TraceAnalyticMotive.publicNorthwestImportedRectangles_eq_certificateLedgers
    morphism
    probe

/-- Motive-root aggregate northwest imported-rectangle count-as-length formula. -/
theorem TraceAnalyticMotive.publicPayload_northwestImportedRectangles_length
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : source ⟶ target)
    {probeSource probeTarget : TraceAnalyticGeometricGenerator}
    (probe : probeSource ⟶ probeTarget) :
    source.certificateLedger.importedRectangleCount +
        probeTarget.certificateLedger.importedRectangleCount =
      (source.certificateLedger.importedRectangles ++
        probeTarget.certificateLedger.importedRectangles).length :=
  TraceAnalyticMotive.publicNorthwestCertificateLedgerImportedRectangles_length
    morphism
    probe

/-- Motive-root aggregate northwest trace-bookkeeping count formula. -/
theorem TraceAnalyticMotive.publicPayload_northwestTraceBookkeepingCount
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : source ⟶ target)
    {probeSource probeTarget : TraceAnalyticGeometricGenerator}
    (probe : probeSource ⟶ probeTarget) :
    TraceSixFunctorPullbackPushforward.northwestTraceBookkeepingCount
        morphism
        probe =
      source.certificateLedger.traceBookkeepingCount +
        probeTarget.certificateLedger.traceBookkeepingCount :=
  TraceAnalyticMotive.publicNorthwestTraceBookkeepingCount_eq_certificateLedgers
    morphism
    probe

/-- Motive-root aggregate northwest rewrite-step count formula. -/
theorem TraceAnalyticMotive.publicPayload_northwestRewriteStepCount
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : source ⟶ target)
    {probeSource probeTarget : TraceAnalyticGeometricGenerator}
    (probe : probeSource ⟶ probeTarget) :
    TraceSixFunctorPullbackPushforward.northwestRewriteStepCount
        morphism
        probe =
      source.certificateLedger.rewriteStepCount +
        probeTarget.certificateLedger.rewriteStepCount :=
  TraceAnalyticMotive.publicNorthwestRewriteStepCount_eq_certificateLedgers
    morphism
    probe

end AnalyticMotives
end LFunctions
end Boundary
