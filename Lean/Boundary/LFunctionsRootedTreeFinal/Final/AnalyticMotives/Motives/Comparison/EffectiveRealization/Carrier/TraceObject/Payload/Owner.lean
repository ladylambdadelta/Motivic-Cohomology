import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Comparison.EffectiveRealization.Carrier.TraceObject.Spine.Owner

/-!
# Trace-object certificate payload for effective realization

This file exposes the analytic certificate payload attached to a trace-object
carrier input.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- The trace-object carrier certificate ledger is its certified-presentation
certificate ledger. -/
theorem TraceAnalyticEffectiveRealization.traceObject_certificateLedger_eq_certificates
    (object : TraceCorQObject) :
    object.certificateLedger =
      object.certificates :=
  rfl

/-- The trace-object carrier imported rectangles come from its certificate
ledger. -/
theorem TraceAnalyticEffectiveRealization.traceObject_importedRectangles_eq_certificates
    (object : TraceCorQObject) :
    object.importedRectangles =
      object.certificates.importedRectangles :=
  rfl

/-- The trace-object carrier imported-rectangle count comes from its
certificate ledger. -/
theorem TraceAnalyticEffectiveRealization.traceObject_importedRectangleCount_eq_certificates
    (object : TraceCorQObject) :
    object.importedRectangleCount =
      object.certificates.importedRectangleCount :=
  rfl

/-- The trace-object carrier trace-bookkeeping count comes from its certificate
ledger. -/
theorem TraceAnalyticEffectiveRealization.traceObject_traceBookkeepingCount_eq_certificates
    (object : TraceCorQObject) :
    object.traceBookkeepingCount =
      object.certificates.traceBookkeepingCount :=
  rfl

/-- The trace-object carrier rewrite-step count comes from its certificate
ledger. -/
theorem TraceAnalyticEffectiveRealization.traceObject_rewriteStepCount_eq_certificates
    (object : TraceCorQObject) :
    object.rewriteStepCount =
      object.certificates.rewriteStepCount :=
  rfl

end AnalyticMotives
end LFunctions
end Boundary
