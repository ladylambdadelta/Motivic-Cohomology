import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Stabilization.AdditiveEnvelope.Homs.Ext.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Stabilization.AdditiveEnvelope.DirectSum.Biproduct.Composites.RightOffDiagonal.Owner

/-!
# Full right-right direct-sum composite identity

The right inclusion followed by the right projection is the identity on the
right summand.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Every entry of the right-right direct-sum composite agrees with the identity. -/
theorem TraceAnalyticAdditiveCategory.rightInclusion_comp_rightProjection_entry_eq_id
    (left right : TraceAnalyticAdditiveCategoryObject)
    (sourceIndex targetIndex : Fin right.length) :
    (TraceAnalyticAdditiveCategory.rightInclusion_comp_rightProjection
      left
      right).entry sourceIndex targetIndex =
      (TraceAnalyticAdditiveCategory.id right).entry sourceIndex targetIndex :=
  match Classical.decEq sourceIndex targetIndex with
  | isTrue indices_eq =>
      Eq.subst
        (motive := fun index =>
          (TraceAnalyticAdditiveCategory.rightInclusion_comp_rightProjection
            left
            right).entry sourceIndex index =
            (TraceAnalyticAdditiveCategory.id right).entry sourceIndex index)
        indices_eq
        (TraceAnalyticAdditiveCategory.rightInclusion_comp_rightProjection_entry_self
          left
          right
          sourceIndex)
  | isFalse indices_ne =>
      TraceAnalyticAdditiveCategory.rightInclusion_comp_rightProjection_entry_ne
        left
        right
        sourceIndex
        targetIndex
        indices_ne

/-- The right inclusion followed by the right projection is the identity. -/
theorem TraceAnalyticAdditiveCategory.rightInclusion_comp_rightProjection_eq_id
    (left right : TraceAnalyticAdditiveCategoryObject) :
    TraceAnalyticAdditiveCategory.rightInclusion_comp_rightProjection left right =
      TraceAnalyticAdditiveCategory.id right :=
  TraceAnalyticAdditiveHom.ext
    (fun sourceIndex targetIndex =>
      TraceAnalyticAdditiveCategory.rightInclusion_comp_rightProjection_entry_eq_id
        left
        right
        sourceIndex
        targetIndex)

end AnalyticMotives
end LFunctions
end Boundary
