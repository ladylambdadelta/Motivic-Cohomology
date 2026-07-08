import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Stabilization.AdditiveEnvelope.DirectSum.CategoryMaps.Owner

/-!
# Entry formulas for category-level direct-sum maps

The category-level direct-sum projections and inclusions are the corresponding
sparse matrix maps.  Their entries therefore reduce definitionally to the raw
matrix entries.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Entry formula bridge for the category-level left direct-sum projection. -/
theorem TraceAnalyticAdditiveCategory.leftDirectSumProjection_entry
    (left right : TraceAnalyticAdditiveCategoryObject)
    (sourceIndex : Fin (TraceAnalyticAdditiveObject.directSum left right).length)
    (targetIndex : Fin left.length) :
    (TraceAnalyticAdditiveCategory.leftDirectSumProjection left right).entry
        sourceIndex
        targetIndex =
      (TraceAnalyticAdditiveObject.leftDirectSumProjection left right).entry
        sourceIndex
        targetIndex :=
  rfl

/-- Entry formula bridge for the category-level right direct-sum projection. -/
theorem TraceAnalyticAdditiveCategory.rightDirectSumProjection_entry
    (left right : TraceAnalyticAdditiveCategoryObject)
    (sourceIndex : Fin (TraceAnalyticAdditiveObject.directSum left right).length)
    (targetIndex : Fin right.length) :
    (TraceAnalyticAdditiveCategory.rightDirectSumProjection left right).entry
        sourceIndex
        targetIndex =
      (TraceAnalyticAdditiveObject.rightDirectSumProjection left right).entry
        sourceIndex
        targetIndex :=
  rfl

/-- Entry formula bridge for the category-level left direct-sum inclusion. -/
theorem TraceAnalyticAdditiveCategory.leftDirectSumInclusion_entry
    (left right : TraceAnalyticAdditiveCategoryObject)
    (sourceIndex : Fin left.length)
    (targetIndex : Fin (TraceAnalyticAdditiveObject.directSum left right).length) :
    (TraceAnalyticAdditiveCategory.leftDirectSumInclusion left right).entry
        sourceIndex
        targetIndex =
      (TraceAnalyticAdditiveObject.leftDirectSumInclusion left right).entry
        sourceIndex
        targetIndex :=
  rfl

/-- Entry formula bridge for the category-level right direct-sum inclusion. -/
theorem TraceAnalyticAdditiveCategory.rightDirectSumInclusion_entry
    (left right : TraceAnalyticAdditiveCategoryObject)
    (sourceIndex : Fin right.length)
    (targetIndex : Fin (TraceAnalyticAdditiveObject.directSum left right).length) :
    (TraceAnalyticAdditiveCategory.rightDirectSumInclusion left right).entry
        sourceIndex
        targetIndex =
      (TraceAnalyticAdditiveObject.rightDirectSumInclusion left right).entry
        sourceIndex
        targetIndex :=
  rfl

end AnalyticMotives
end LFunctions
end Boundary
