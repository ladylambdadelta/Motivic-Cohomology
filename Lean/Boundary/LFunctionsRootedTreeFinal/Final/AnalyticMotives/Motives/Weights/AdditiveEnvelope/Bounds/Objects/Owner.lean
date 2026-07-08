import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Weights.AdditiveEnvelope.Objects.Owner

/-!
# Bounded-weight finite analytic trace families

A finite additive-envelope object is bounded by `bound` when its concrete
maximum component weight level is at most `bound`.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- A finite analytic trace family is bounded by a numeric weight level. -/
def TraceAnalyticAdditiveObject.IsBoundedBy
    (object : TraceAnalyticAdditiveObject)
    (bound : Nat) :
    Prop :=
  object.weightLevel ≤ bound

/-- Finite analytic trace families with weight at most `bound`. -/
abbrev TraceAnalyticAdditiveObject.BoundedBy
    (bound : Nat) :=
  { object : TraceAnalyticAdditiveObject //
      object.IsBoundedBy bound }

/-- The underlying finite trace family of a bounded object. -/
def TraceAnalyticAdditiveObject.BoundedBy.object
    {bound : Nat}
    (object : TraceAnalyticAdditiveObject.BoundedBy bound) :
    TraceAnalyticAdditiveObject :=
  object.val

/-- The bounded-object proof is its concrete weight inequality. -/
theorem TraceAnalyticAdditiveObject.BoundedBy.weightLevel_le
    {bound : Nat}
    (object : TraceAnalyticAdditiveObject.BoundedBy bound) :
    object.object.weightLevel ≤ bound :=
  object.property

/-- The empty finite trace family is bounded by every weight level. -/
def TraceAnalyticAdditiveObject.zeroBoundedBy
    (bound : Nat) :
    TraceAnalyticAdditiveObject.BoundedBy bound :=
  ⟨TraceAnalyticAdditiveObject.zero,
    Eq.subst
      (motive := fun weight =>
        weight ≤ bound)
      (Eq.symm TraceAnalyticAdditiveObject.weightLevel_zero)
      (Nat.zero_le bound)⟩

/-- The underlying object of the bounded zero family is the zero family. -/
theorem TraceAnalyticAdditiveObject.zeroBoundedBy_object
    (bound : Nat) :
    (TraceAnalyticAdditiveObject.zeroBoundedBy bound).object =
      TraceAnalyticAdditiveObject.zero :=
  rfl

end AnalyticMotives
end LFunctions
end Boundary
