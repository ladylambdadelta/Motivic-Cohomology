import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Stabilization.AdditiveEnvelope.Objects.Singleton.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Weights.AdditiveEnvelope.Bounds.Objects.Owner

/-!
# Bounded singleton additive-envelope objects

This file packages the singleton finite trace family as a bounded additive
object using its concrete computed weight level.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- The canonical numeric bound of a singleton additive-envelope object. -/
def TraceAnalyticAdditiveObject.singletonWeightBound
    (object : TraceCorQObject) :
    Nat :=
  Nat.max object.weightLevel 0

/-- A singleton additive-envelope object is bounded by its computed singleton weight. -/
def TraceAnalyticAdditiveObject.singletonBoundedBy
    (object : TraceCorQObject) :
    TraceAnalyticAdditiveObject.BoundedBy
      (TraceAnalyticAdditiveObject.singletonWeightBound object) :=
  ⟨TraceAnalyticAdditiveObject.singleton object,
    Eq.subst
      (motive := fun weight =>
        weight ≤ TraceAnalyticAdditiveObject.singletonWeightBound object)
      (Eq.symm (TraceAnalyticAdditiveObject.singleton_weightLevel object))
      (Nat.le_refl
        (TraceAnalyticAdditiveObject.singletonWeightBound object))⟩

/-- The underlying object of the bounded singleton package is the singleton object. -/
theorem TraceAnalyticAdditiveObject.singletonBoundedBy_object
    (object : TraceCorQObject) :
    (TraceAnalyticAdditiveObject.singletonBoundedBy object).object =
      TraceAnalyticAdditiveObject.singleton object :=
  rfl

/-- The bounded singleton package is bounded by its concrete singleton weight. -/
theorem TraceAnalyticAdditiveObject.singletonBoundedBy_weightLevel_le
    (object : TraceCorQObject) :
    (TraceAnalyticAdditiveObject.singletonBoundedBy object).object.weightLevel ≤
      TraceAnalyticAdditiveObject.singletonWeightBound object :=
  (TraceAnalyticAdditiveObject.singletonBoundedBy object).weightLevel_le

end AnalyticMotives
end LFunctions
end Boundary
