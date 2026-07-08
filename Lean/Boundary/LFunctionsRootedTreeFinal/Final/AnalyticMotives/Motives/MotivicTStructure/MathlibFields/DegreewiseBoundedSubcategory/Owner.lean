import Mathlib.CategoryTheory.FullSubcategory
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Comparison.Source.Bounded.IsoClosure.Owner

/-!
# Degreewise iso-closure bounded stable source

The bounded representative predicate is too narrow for cone closure: chosen
cofibers of bounded maps land naturally in the degreewise iso-closure bounded
predicate.  This file names the corresponding full subcategory, which is the
correct owner layer for the bounded cocone field.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory

namespace TraceAnalyticDMgmComparisonSource

/-- The full subcategory of stable comparison-source objects represented by
degreewise iso-closure bounded analytic cochain complexes. -/
abbrev DegreewiseBoundedStable :=
  CategoryTheory.FullSubcategory
    TraceAnalyticDMgmComparisonSource
      .degreewiseIsoClosureBoundedStableObject

/-- The ambient stable object carried by a degreewise bounded stable source
object. -/
def DegreewiseBoundedStable.object
    (object :
      TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable) :
    TraceAnalyticDMgmComparisonSource :=
  object.obj

/-- The degreewise bounded-source membership carried by a degreewise bounded
stable source object. -/
def DegreewiseBoundedStable.membership
    (object :
      TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable) :
    TraceAnalyticDMgmComparisonSource
      .degreewiseIsoClosureBoundedStableObject object.object :=
  object.property

/-- The inclusion of degreewise bounded stable source objects into the ambient
stable analytic comparison source. -/
abbrev DegreewiseBoundedStable.inclusion :
    TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable ⥤
      TraceAnalyticDMgmComparisonSource :=
  CategoryTheory.fullSubcategoryInclusion
    TraceAnalyticDMgmComparisonSource
      .degreewiseIsoClosureBoundedStableObject

/-- The inclusion sends a degreewise bounded stable source object to its
ambient object. -/
theorem DegreewiseBoundedStable.inclusion_obj
    (object :
      TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable) :
    TraceAnalyticDMgmComparisonSource
        .DegreewiseBoundedStable.inclusion.obj object =
      object.object :=
  rfl

/-- Every bounded stable source object is degreewise iso-closure bounded. -/
def DegreewiseBoundedStable.ofBoundedStable
    (object : TraceAnalyticDMgmComparisonSource.BoundedStable) :
    TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable where
  obj := object.object
  property :=
    TraceAnalyticDMgmComparisonSource
      .degreewiseIsoClosureBoundedStableObject_of_boundedStableObject
        object.membership

/-- The degreewise bounded object obtained from a bounded stable source object
has the same ambient object. -/
theorem DegreewiseBoundedStable.ofBoundedStable_object
    (object : TraceAnalyticDMgmComparisonSource.BoundedStable) :
    (TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable
      .ofBoundedStable object).object =
      object.object :=
  rfl

end TraceAnalyticDMgmComparisonSource

end AnalyticMotives
end LFunctions
end Boundary
