import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceTransport.Objects.Owner

/-!
# Q-linear trace-category objects

This file owns the objects of the pre-motivic Q-linear trace category.

The intended objects are certified residue-channel trace presentations.  This
keeps the lane on the higher-computadic trace calculus rather than a separate
geometric-object category.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Objects of the raw Q-linear trace category. -/
abbrev TraceCorQObject :=
  TraceTransportObject

/-- The source trace expression of a Q-linear trace-correspondence object. -/
def TraceCorQObject.source
    (object : TraceCorQObject) :
    QTraceExpression :=
  CertifiedResidueChannelPresentation.source object

/-- The residue ledger of a Q-linear trace-correspondence object. -/
def TraceCorQObject.ledger
    (object : TraceCorQObject) :
    ResidueLedger :=
  CertifiedResidueChannelPresentation.ledger object

/-- The channel expressions of a Q-linear trace-correspondence object. -/
def TraceCorQObject.channels
    (object : TraceCorQObject) :
    ResidueChannelExpressionList :=
  CertifiedResidueChannelPresentation.channels object

/-- The trace schedule of a Q-linear trace-correspondence object. -/
def TraceCorQObject.schedule
    (object : TraceCorQObject) :
    TraceSchedule :=
  CertifiedResidueChannelPresentation.schedule object

/-- The analytic certificate ledger of a Q-linear trace-correspondence object. -/
def TraceCorQObject.certificateLedger
    (object : TraceCorQObject) :
    ResidueChannelCertificateLedger :=
  CertifiedResidueChannelPresentation.certificateLedger object

/-- The imported finite-rectangle payload carried by a Q-linear trace-correspondence object. -/
def TraceCorQObject.importedRectangleCount
    (object : TraceCorQObject) :
    Nat :=
  CertifiedResidueChannelPresentation.importedRectangleCount object

/-- The internal trace-bookkeeping payload carried by a Q-linear trace-correspondence object. -/
def TraceCorQObject.traceBookkeepingCount
    (object : TraceCorQObject) :
    Nat :=
  CertifiedResidueChannelPresentation.traceBookkeepingCount object

/-- The explicit rewrite-step payload carried by a Q-linear trace-correspondence object. -/
def TraceCorQObject.rewriteStepCount
    (object : TraceCorQObject) :
    Nat :=
  CertifiedResidueChannelPresentation.rewriteStepCount object

/-- Object imported payload is counted by its analytic certificate ledger. -/
theorem TraceCorQObject.importedRectangleCount_eq_certificateLedger_count
    (object : TraceCorQObject) :
    object.importedRectangleCount =
      object.certificateLedger.importedRectangleCount :=
  rfl

/-- Object bookkeeping payload is counted by its analytic certificate ledger. -/
theorem TraceCorQObject.traceBookkeepingCount_eq_certificateLedger_count
    (object : TraceCorQObject) :
    object.traceBookkeepingCount =
      object.certificateLedger.traceBookkeepingCount :=
  rfl

/-- Object rewrite-step payload is counted by its analytic certificate ledger. -/
theorem TraceCorQObject.rewriteStepCount_eq_certificateLedger_count
    (object : TraceCorQObject) :
    object.rewriteStepCount =
      object.certificateLedger.rewriteStepCount :=
  rfl

end AnalyticMotives
end LFunctions
end Boundary
