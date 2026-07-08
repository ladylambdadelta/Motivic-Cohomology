import Mathlib.CategoryTheory.FullSubcategory
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Weights.AdditiveEnvelope.Bounds.Monotone.Objects.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Stabilization.AdditiveEnvelope.Category.Instance.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Weights.AdditiveEnvelope.Bounds.Objects.IsoBounded.Owner

/-!
# Iso-closure of bounded additive objects

An iso-bounded additive object lies in the categorical iso-closure of the
concrete bounded additive objects.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory

namespace TraceAnalyticAdditiveObject

/-- Concrete bounded additive objects as a predicate on the additive-envelope
category object type. -/
def boundedObjectRepresentative
    (bound : Nat)
    (object : TraceAnalyticAdditiveCategoryObject) :
    Prop :=
  ∃ boundedObject : TraceAnalyticAdditiveObject.BoundedBy bound,
    object = boundedObject.object

/-- A concrete bounded additive object belongs to the bounded-object
representative predicate. -/
theorem boundedObjectRepresentative_of_bounded
    {bound : Nat}
    (boundedObject : TraceAnalyticAdditiveObject.BoundedBy bound) :
    TraceAnalyticAdditiveObject.boundedObjectRepresentative
      bound
      boundedObject.object :=
  Exists.intro boundedObject rfl

/-- An iso-bounded additive object belongs to the iso-closure of concrete
bounded additive objects. -/
theorem IsoBoundedBy.mem_isoClosure_boundedObjectRepresentative
    {bound : Nat}
    {object : TraceAnalyticAdditiveObject}
    (isoBounded :
      TraceAnalyticAdditiveObject.IsoBoundedBy object bound) :
    CategoryTheory.isoClosure
      (TraceAnalyticAdditiveObject.boundedObjectRepresentative bound)
      object :=
  let representative_mem :
      TraceAnalyticAdditiveObject.boundedObjectRepresentative
        bound
        isoBounded.boundedRepresentative.object :=
    TraceAnalyticAdditiveObject
      .boundedObjectRepresentative_of_bounded
        isoBounded.boundedRepresentative
  CategoryTheory.mem_of_iso
    (P := TraceAnalyticAdditiveObject.boundedObjectRepresentative bound)
    isoBounded.objectIsoRepresentative.symm
    representative_mem

/-- Increasing the numeric weight bound preserves membership in the
iso-closure of concrete bounded additive objects. -/
theorem boundedObjectRepresentative_isoClosure_monotone
    {lower upper : Nat}
    (bound_le : lower ≤ upper)
    (object : TraceAnalyticAdditiveCategoryObject)
    (mem :
      CategoryTheory.isoClosure
        (TraceAnalyticAdditiveObject.boundedObjectRepresentative lower)
        object) :
    CategoryTheory.isoClosure
      (TraceAnalyticAdditiveObject.boundedObjectRepresentative upper)
      object :=
  CategoryTheory.monotone_isoClosure
    (fun candidate candidate_mem =>
      match candidate_mem with
      | Exists.intro boundedObject object_eq =>
          Exists.intro
            (boundedObject.rebound bound_le)
            object_eq)
    object
    mem

end TraceAnalyticAdditiveObject

end AnalyticMotives
end LFunctions
end Boundary
