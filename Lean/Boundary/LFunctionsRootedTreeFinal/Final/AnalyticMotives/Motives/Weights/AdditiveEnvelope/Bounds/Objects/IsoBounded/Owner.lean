import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Weights.AdditiveEnvelope.Bounds.Objects.Owner

/-!
# Objects bounded up to analytic isomorphism

An additive analytic object may be represented by a bounded finite trace family
without being definitionally equal to that family.  This file records the
chosen bounded representative and the isomorphism to it.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory

/-- An additive analytic object with a bounded representative up to isomorphism. -/
structure TraceAnalyticAdditiveObject.IsoBoundedBy
    (object : TraceAnalyticAdditiveObject)
    (bound : Nat) where
  representative : TraceAnalyticAdditiveObject.BoundedBy bound
  iso : object ≅ representative.object

/-- The bounded representative of an iso-bounded analytic object. -/
def TraceAnalyticAdditiveObject.IsoBoundedBy.boundedRepresentative
    {object : TraceAnalyticAdditiveObject}
    {bound : Nat}
    (isoBounded : TraceAnalyticAdditiveObject.IsoBoundedBy object bound) :
    TraceAnalyticAdditiveObject.BoundedBy bound :=
  isoBounded.representative

/-- The isomorphism from the actual object to the bounded representative. -/
def TraceAnalyticAdditiveObject.IsoBoundedBy.objectIsoRepresentative
    {object : TraceAnalyticAdditiveObject}
    {bound : Nat}
    (isoBounded : TraceAnalyticAdditiveObject.IsoBoundedBy object bound) :
    object ≅ isoBounded.boundedRepresentative.object :=
  isoBounded.iso

/-- The bounded representative satisfies the recorded numeric weight bound. -/
theorem TraceAnalyticAdditiveObject.IsoBoundedBy.representative_weightLevel_le
    {object : TraceAnalyticAdditiveObject}
    {bound : Nat}
    (isoBounded : TraceAnalyticAdditiveObject.IsoBoundedBy object bound) :
    isoBounded.boundedRepresentative.object.weightLevel ≤ bound :=
  isoBounded.boundedRepresentative.weightLevel_le

/-- A definitionally bounded object is iso-bounded by the identity isomorphism. -/
def TraceAnalyticAdditiveObject.BoundedBy.isoBounded
    {bound : Nat}
    (object : TraceAnalyticAdditiveObject.BoundedBy bound) :
    TraceAnalyticAdditiveObject.IsoBoundedBy object.object bound where
  representative := object
  iso := Iso.refl object.object

end AnalyticMotives
end LFunctions
end Boundary
