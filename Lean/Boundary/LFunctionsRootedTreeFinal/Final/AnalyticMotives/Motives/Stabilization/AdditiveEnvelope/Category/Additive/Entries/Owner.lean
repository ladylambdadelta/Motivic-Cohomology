import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Stabilization.AdditiveEnvelope.Category.Additive.Operations.Owner

/-!
# Entry formulas for additive category operations

The additive operations on category-level matrix homs are entrywise operations
on analytic trace correspondences.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Entry formula for the zero category hom. -/
theorem TraceAnalyticAdditiveCategory.zeroHom_entry
    (source target : TraceAnalyticAdditiveCategoryObject)
    (sourceIndex : Fin source.length)
    (targetIndex : Fin target.length) :
    (TraceAnalyticAdditiveCategory.zeroHom source target).entry
        sourceIndex
        targetIndex =
      0 :=
  rfl

/-- Entry formula for category-level hom addition. -/
theorem TraceAnalyticAdditiveCategory.addHom_entry
    {source target : TraceAnalyticAdditiveCategoryObject}
    (left right : TraceAnalyticAdditiveCategoryHom source target)
    (sourceIndex : Fin source.length)
    (targetIndex : Fin target.length) :
    (TraceAnalyticAdditiveCategory.addHom left right).entry
        sourceIndex
        targetIndex =
      TraceCorQHom.add
        (left.entry sourceIndex targetIndex)
        (right.entry sourceIndex targetIndex) :=
  rfl

/-- Entry formula for category-level hom negation. -/
theorem TraceAnalyticAdditiveCategory.negHom_entry
    {source target : TraceAnalyticAdditiveCategoryObject}
    (hom : TraceAnalyticAdditiveCategoryHom source target)
    (sourceIndex : Fin source.length)
    (targetIndex : Fin target.length) :
    (TraceAnalyticAdditiveCategory.negHom hom).entry
        sourceIndex
        targetIndex =
      -hom.entry sourceIndex targetIndex :=
  rfl

/-- Entry formula for category-level rational scalar multiplication. -/
theorem TraceAnalyticAdditiveCategory.smulHom_entry
    (coefficient : Rat)
    {source target : TraceAnalyticAdditiveCategoryObject}
    (hom : TraceAnalyticAdditiveCategoryHom source target)
    (sourceIndex : Fin source.length)
    (targetIndex : Fin target.length) :
    (TraceAnalyticAdditiveCategory.smulHom coefficient hom).entry
        sourceIndex
        targetIndex =
      coefficient • hom.entry sourceIndex targetIndex :=
  rfl

end AnalyticMotives
end LFunctions
end Boundary
