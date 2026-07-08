import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Weights.Syntax.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Objects.Owner

/-!
# Weight levels of certified trace objects

A trace-correspondence object receives its weight level from the certified
source Q-linear trace expression of its residue-channel presentation.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- The source-expression weight level of a certified trace-correspondence object. -/
def TraceCorQObject.weightLevel
    (object : TraceCorQObject) :
    Nat :=
  object.source.weightLevel

/-- Object weight is the weight of the certified source expression. -/
theorem TraceCorQObject.weightLevel_eq_source
    (object : TraceCorQObject) :
    object.weightLevel =
      object.source.weightLevel :=
  rfl

/-- Adding certificates preserves object weight level. -/
theorem TraceCorQObject.withAdditionalCertificates_weightLevel
    (object : TraceCorQObject)
    (certificates : ResidueChannelCertificateLedger) :
    (object.withAdditionalCertificates certificates).weightLevel =
      object.weightLevel :=
  congrArg
    QTraceExpression.weightLevel
    (TraceCorQObject.withAdditionalCertificates_source
      object
      certificates)

end AnalyticMotives
end LFunctions
end Boundary
