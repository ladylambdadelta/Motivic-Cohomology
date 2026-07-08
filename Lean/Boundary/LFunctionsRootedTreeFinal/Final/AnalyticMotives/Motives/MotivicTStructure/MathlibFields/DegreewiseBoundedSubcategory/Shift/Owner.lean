import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.MathlibFields.DegreewiseBoundedSubcategory.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Comparison.Source.Bounded.IsoClosure.Shift.Owner

/-!
# Shifts in the degreewise bounded stable source

The degreewise iso-closure bounded predicate is stable under ambient shifts.
This file packages those shifted objects and shifted morphisms inside the
degreewise bounded full subcategory.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory

namespace TraceAnalyticDMgmComparisonSource
namespace DegreewiseBoundedStable

/-- The ambient shift of a degreewise bounded stable source object is again
degreewise bounded. -/
theorem shifted_object_membership
    (object :
      TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable)
    (degree : ℤ) :
    TraceAnalyticDMgmComparisonSource
      .degreewiseIsoClosureBoundedStableObject
        (object.object⟦degree⟧) :=
  TraceAnalyticDMgmComparisonSource
    .degreewiseIsoClosureBoundedStableObject_shift
      object.membership
      degree

/-- The ambient shift of a degreewise bounded stable source object, packaged
again as a degreewise bounded stable source object. -/
def shiftedObject
    (object :
      TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable)
    (degree : ℤ) :
    TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable where
  obj := object.object⟦degree⟧
  property :=
    TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable
      .shifted_object_membership object degree

/-- The packaged shifted degreewise bounded object has the expected ambient
object. -/
theorem shiftedObject_object
    (object :
      TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable)
    (degree : ℤ) :
    (TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable
      .shiftedObject object degree).object =
      object.object⟦degree⟧ :=
  rfl

/-- The ambient shifted morphism, packaged as a morphism between degreewise
bounded shifted objects. -/
def shiftedMap
    (degree : ℤ)
    {source target :
      TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable}
    (morphism : source ⟶ target) :
    TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable
        .shiftedObject source degree ⟶
      TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable
        .shiftedObject target degree :=
  morphism⟦degree⟧'

/-- The packaged shifted morphism is the ambient shifted morphism. -/
theorem shiftedMap_eq_ambient
    (degree : ℤ)
    {source target :
      TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable}
    (morphism : source ⟶ target) :
    TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable
        .shiftedMap degree morphism =
      morphism⟦degree⟧' :=
  rfl

/-- The degreewise bounded stable source shift endofunctor. -/
def shiftFunctor
    (degree : ℤ) :
    TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable ⥤
      TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable where
  obj object :=
    TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable
      .shiftedObject object degree
  map {source target} morphism :=
    TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable
      .shiftedMap degree morphism
  map_id object :=
    rfl
  map_comp {left middle right} first second :=
    rfl

/-- The degreewise bounded shift functor commutes definitionally with the
inclusion into the ambient analytic comparison source. -/
theorem shiftFunctor_comp_inclusion
    (degree : ℤ) :
    TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable
        .shiftFunctor degree ⋙
        TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable
          .inclusion =
      TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable
          .inclusion ⋙
        CategoryTheory.shiftFunctor
          TraceAnalyticDMgmComparisonSource degree :=
  rfl

/-- The degreewise bounded stable source inherits coherent integer shifts from
the ambient analytic comparison source through its fully faithful inclusion. -/
def hasShift :
    HasShift
      TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable ℤ :=
  (CategoryTheory.fullyFaithfulFullSubcategoryInclusion
    TraceAnalyticDMgmComparisonSource
      .degreewiseIsoClosureBoundedStableObject).hasShift
      (fun degree =>
        TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable
          .shiftFunctor degree)
      (fun degree =>
        eqToIso
          (TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable
            .shiftFunctor_comp_inclusion degree))

/-- The degreewise bounded stable source uses the induced coherent integer
shifts as its Mathlib shift instance. -/
instance instHasShift :
    HasShift
      TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable ℤ :=
  TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable.hasShift

/-- The Mathlib shift functor for the degreewise bounded stable source is the
restricted ambient shift functor. -/
theorem mathlib_shiftFunctor_eq_degreewiseShiftFunctor
    (degree : ℤ) :
    CategoryTheory.shiftFunctor
        TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable degree =
      TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable
        .shiftFunctor degree :=
  rfl

end DegreewiseBoundedStable
end TraceAnalyticDMgmComparisonSource

end AnalyticMotives
end LFunctions
end Boundary
