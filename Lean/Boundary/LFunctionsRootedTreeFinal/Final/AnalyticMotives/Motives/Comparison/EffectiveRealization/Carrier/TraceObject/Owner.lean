import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Comparison.EffectiveRealization.Carrier.TraceObject.Payload.Owner

/-!
# Trace-object carrier inputs for effective realization

This file exposes the concrete certified trace-object fields consumed by the
effective-realization carrier construction.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- The trace-object carrier input has the certified trace source expression. -/
def TraceAnalyticEffectiveRealization.traceObjectSource
    (object : TraceCorQObject) :
    QTraceExpression :=
  object.source

/-- The trace-object carrier input has a residue ledger. -/
def TraceAnalyticEffectiveRealization.traceObjectResidueLedger
    (object : TraceCorQObject) :
    ResidueLedger :=
  object.ledger

/-- The trace-object carrier input has channel expressions. -/
def TraceAnalyticEffectiveRealization.traceObjectChannels
    (object : TraceCorQObject) :
    ResidueChannelExpressionList :=
  object.channels

/-- The trace-object carrier input has a trace schedule. -/
def TraceAnalyticEffectiveRealization.traceObjectSchedule
    (object : TraceCorQObject) :
    TraceSchedule :=
  object.schedule

/-- The trace-object carrier input has an analytic certificate ledger. -/
def TraceAnalyticEffectiveRealization.traceObjectCertificateLedger
    (object : TraceCorQObject) :
    ResidueChannelCertificateLedger :=
  object.certificateLedger

/-- The trace-object source projection is the underlying trace-correspondence
object source. -/
theorem TraceAnalyticEffectiveRealization.traceObjectSource_eq
    (object : TraceCorQObject) :
    TraceAnalyticEffectiveRealization.traceObjectSource object =
      object.source :=
  rfl

/-- The trace-object residue-ledger projection is the underlying
trace-correspondence object ledger. -/
theorem TraceAnalyticEffectiveRealization.traceObjectResidueLedger_eq
    (object : TraceCorQObject) :
    TraceAnalyticEffectiveRealization.traceObjectResidueLedger object =
      object.ledger :=
  rfl

/-- The trace-object channel projection is the underlying trace-correspondence
object channel list. -/
theorem TraceAnalyticEffectiveRealization.traceObjectChannels_eq
    (object : TraceCorQObject) :
    TraceAnalyticEffectiveRealization.traceObjectChannels object =
      object.channels :=
  rfl

/-- The trace-object schedule projection is the underlying trace-correspondence
object schedule. -/
theorem TraceAnalyticEffectiveRealization.traceObjectSchedule_eq
    (object : TraceCorQObject) :
    TraceAnalyticEffectiveRealization.traceObjectSchedule object =
      object.schedule :=
  rfl

/-- The trace-object certificate projection is the underlying
trace-correspondence object certificate ledger. -/
theorem TraceAnalyticEffectiveRealization.traceObjectCertificateLedger_eq
    (object : TraceCorQObject) :
    TraceAnalyticEffectiveRealization.traceObjectCertificateLedger object =
      object.certificateLedger :=
  rfl

/-- Trace-object imported rectangles are counted by the certificate ledger. -/
theorem TraceAnalyticEffectiveRealization.traceObject_importedRectangleCount_eq_certificateLedger
    (object : TraceCorQObject) :
    object.importedRectangleCount =
      (TraceAnalyticEffectiveRealization.traceObjectCertificateLedger object).importedRectangleCount :=
  rfl

/-- Trace-object imported rectangles are the certificate-ledger rectangles. -/
theorem TraceAnalyticEffectiveRealization.traceObject_importedRectangles_eq_certificateLedger
    (object : TraceCorQObject) :
    object.importedRectangles =
      (TraceAnalyticEffectiveRealization.traceObjectCertificateLedger object).importedRectangles :=
  rfl

/-- Trace-object imported-rectangle count is the length of its imported
rectangle list. -/
theorem TraceAnalyticEffectiveRealization.traceObject_importedRectangleCount_eq_length
    (object : TraceCorQObject) :
    object.importedRectangleCount =
      object.importedRectangles.length :=
  TraceCorQObject.importedRectangleCount_eq_length_importedRectangles object

end AnalyticMotives
end LFunctions
end Boundary
