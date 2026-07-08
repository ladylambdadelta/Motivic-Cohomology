import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Stabilization.AdditiveEnvelope.Objects.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Weights.TraceObjects.Owner

/-!
# Weight levels of additive-envelope objects

The weight level of a finite analytic trace family is the maximum of the
weights of its certified trace-presentation components.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- The maximum component weight level of a finite analytic trace family. -/
def TraceAnalyticAdditiveObject.weightLevel :
    TraceAnalyticAdditiveObject → Nat
  | [] => 0
  | object :: tail =>
      Nat.max object.weightLevel tail.weightLevel

/-- The empty finite trace family has weight level zero. -/
theorem TraceAnalyticAdditiveObject.weightLevel_zero :
    TraceAnalyticAdditiveObject.zero.weightLevel =
      0 :=
  rfl

/-- A nonempty finite trace family records the maximum of head and tail weights. -/
theorem TraceAnalyticAdditiveObject.weightLevel_cons
    (object : TraceCorQObject)
    (tail : TraceAnalyticAdditiveObject) :
    (object :: tail).weightLevel =
      Nat.max object.weightLevel tail.weightLevel :=
  rfl

/-- The direct sum with an empty right family preserves weight by definition. -/
theorem TraceAnalyticAdditiveObject.weightLevel_directSum_nil
    (left : TraceAnalyticAdditiveObject) :
    (TraceAnalyticAdditiveObject.directSum left []).weightLevel =
      left.weightLevel :=
  congrArg
    TraceAnalyticAdditiveObject.weightLevel
    (List.append_nil left)

end AnalyticMotives
end LFunctions
end Boundary
