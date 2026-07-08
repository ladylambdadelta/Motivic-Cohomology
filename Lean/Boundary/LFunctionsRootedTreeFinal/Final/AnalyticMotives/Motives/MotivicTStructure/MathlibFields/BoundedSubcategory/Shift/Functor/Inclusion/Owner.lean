import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.MathlibFields.BoundedSubcategory.Shift.Functor.Owner

/-!
# Inclusion compatibility for bounded stable shift functors

The bounded stable shift functor is the ambient stable shift restricted to the
bounded full subcategory.  This file records the object, morphism, and functor
compatibility with the full-subcategory inclusion.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory

namespace TraceAnalyticDMgmComparisonSource
namespace BoundedStable

/-- The bounded shift functor followed by inclusion has the same object action
as inclusion followed by the ambient shift functor. -/
theorem shiftFunctor_inclusion_obj
    (degree : ℤ)
    (object : TraceAnalyticDMgmComparisonSource.BoundedStable) :
    (TraceAnalyticDMgmComparisonSource.BoundedStable.inclusion.obj
      ((TraceAnalyticDMgmComparisonSource.BoundedStable.shiftFunctor degree)
        .obj object)) =
      ((shiftFunctor TraceAnalyticDMgmComparisonSource degree).obj
        (TraceAnalyticDMgmComparisonSource.BoundedStable.inclusion.obj
          object)) :=
  rfl

/-- The bounded shift functor followed by inclusion has the same morphism
action as inclusion followed by the ambient shift functor. -/
theorem shiftFunctor_inclusion_map
    (degree : ℤ)
    {source target : TraceAnalyticDMgmComparisonSource.BoundedStable}
    (hom : source ⟶ target) :
    TraceAnalyticDMgmComparisonSource.BoundedStable.inclusion.map
        ((TraceAnalyticDMgmComparisonSource.BoundedStable.shiftFunctor degree)
          .map hom) =
      (shiftFunctor TraceAnalyticDMgmComparisonSource degree).map
        (TraceAnalyticDMgmComparisonSource.BoundedStable.inclusion.map hom) :=
  rfl

/-- The bounded shift functor commutes definitionally with the inclusion into
the ambient analytic comparison source. -/
theorem shiftFunctor_comp_inclusion
    (degree : ℤ) :
    TraceAnalyticDMgmComparisonSource.BoundedStable.shiftFunctor degree ⋙
        TraceAnalyticDMgmComparisonSource.BoundedStable.inclusion =
      TraceAnalyticDMgmComparisonSource.BoundedStable.inclusion ⋙
        shiftFunctor TraceAnalyticDMgmComparisonSource degree :=
  rfl

end BoundedStable
end TraceAnalyticDMgmComparisonSource

end AnalyticMotives
end LFunctions
end Boundary
