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

end AnalyticMotives
end LFunctions
end Boundary
