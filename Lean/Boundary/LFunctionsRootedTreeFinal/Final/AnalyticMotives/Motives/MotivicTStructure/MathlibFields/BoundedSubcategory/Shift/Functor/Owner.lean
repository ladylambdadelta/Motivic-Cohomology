import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.MathlibFields.BoundedSubcategory.Shift.Functoriality.Owner

/-!
# Bounded stable shift endofunctors

This file packages the bounded shifted object and bounded shifted map into an
actual endofunctor on the bounded stable source.  The construction is the
ambient stable shift restricted to the bounded full subcategory.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory

namespace TraceAnalyticDMgmComparisonSource
namespace BoundedStable

/-- The bounded stable source shift endofunctor. -/
def shiftFunctor
    (degree : ℤ) :
    TraceAnalyticDMgmComparisonSource.BoundedStable ⥤
      TraceAnalyticDMgmComparisonSource.BoundedStable where
  obj object :=
    TraceAnalyticDMgmComparisonSource.BoundedStable.shiftedObject
      object
      degree
  map {source target} hom :=
    TraceAnalyticDMgmComparisonSource.BoundedStable.shiftedMap
      degree
      hom
  map_id object :=
    TraceAnalyticDMgmComparisonSource.BoundedStable.shiftedMap_id
      degree
      object
  map_comp {left middle right} first second :=
    TraceAnalyticDMgmComparisonSource.BoundedStable.shiftedMap_comp
      degree
      first
      second

/-- The bounded shift functor sends an object to the packaged shifted
object. -/
theorem shiftFunctor_obj
    (degree : ℤ)
    (object : TraceAnalyticDMgmComparisonSource.BoundedStable) :
    (TraceAnalyticDMgmComparisonSource.BoundedStable.shiftFunctor degree).obj
        object =
      TraceAnalyticDMgmComparisonSource.BoundedStable.shiftedObject
        object
        degree :=
  rfl

/-- The bounded shift functor sends a morphism to the bounded shifted map. -/
theorem shiftFunctor_map
    (degree : ℤ)
    {source target : TraceAnalyticDMgmComparisonSource.BoundedStable}
    (hom : source ⟶ target) :
    (TraceAnalyticDMgmComparisonSource.BoundedStable.shiftFunctor degree).map
        hom =
      TraceAnalyticDMgmComparisonSource.BoundedStable.shiftedMap
        degree
        hom :=
  rfl

/-- The bounded shift functor's object map has the expected ambient object. -/
theorem shiftFunctor_obj_object
    (degree : ℤ)
    (object : TraceAnalyticDMgmComparisonSource.BoundedStable) :
    ((TraceAnalyticDMgmComparisonSource.BoundedStable.shiftFunctor degree).obj
        object).object =
      object.object⟦degree⟧ :=
  rfl

/-- The bounded shift functor's morphism map is the ambient shifted
morphism. -/
theorem shiftFunctor_map_eq_ambient
    (degree : ℤ)
    {source target : TraceAnalyticDMgmComparisonSource.BoundedStable}
    (hom : source ⟶ target) :
    (TraceAnalyticDMgmComparisonSource.BoundedStable.shiftFunctor degree).map
        hom =
      hom⟦degree⟧' :=
  rfl

end BoundedStable
end TraceAnalyticDMgmComparisonSource

end AnalyticMotives
end LFunctions
end Boundary
