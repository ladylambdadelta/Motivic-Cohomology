import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Stabilization.AdditiveEnvelope.Homs.Ext.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Stabilization.AdditiveEnvelope.DirectSum.Biproduct.Composites.OffDiagonal.Owner

/-!
# Full left-left direct-sum composite identity

The left inclusion followed by the left projection is the identity on the left
summand.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Every entry of the left-left direct-sum composite agrees with the identity. -/
theorem TraceAnalyticAdditiveCategory.leftInclusion_comp_leftProjection_entry_eq_id
    (left right : TraceAnalyticAdditiveCategoryObject)
    (sourceIndex targetIndex : Fin left.length) :
    (TraceAnalyticAdditiveCategory.leftInclusion_comp_leftProjection
      left
      right).entry sourceIndex targetIndex =
      (TraceAnalyticAdditiveCategory.id left).entry sourceIndex targetIndex :=
  match Classical.decEq sourceIndex targetIndex with
  | isTrue indices_eq =>
      Eq.subst
        (motive := fun index =>
          (TraceAnalyticAdditiveCategory.leftInclusion_comp_leftProjection
            left
            right).entry sourceIndex index =
            (TraceAnalyticAdditiveCategory.id left).entry sourceIndex index)
        indices_eq
        (TraceAnalyticAdditiveCategory.leftInclusion_comp_leftProjection_entry_self
          left
          right
          sourceIndex)
  | isFalse indices_ne =>
      TraceAnalyticAdditiveCategory.leftInclusion_comp_leftProjection_entry_ne
        left
        right
        sourceIndex
        targetIndex
        indices_ne

/-- The left inclusion followed by the left projection is the identity. -/
theorem TraceAnalyticAdditiveCategory.leftInclusion_comp_leftProjection_eq_id
    (left right : TraceAnalyticAdditiveCategoryObject) :
    TraceAnalyticAdditiveCategory.leftInclusion_comp_leftProjection left right =
      TraceAnalyticAdditiveCategory.id left :=
  TraceAnalyticAdditiveHom.ext
    (fun sourceIndex targetIndex =>
      TraceAnalyticAdditiveCategory.leftInclusion_comp_leftProjection_entry_eq_id
        left
        right
        sourceIndex
        targetIndex)

end AnalyticMotives
end LFunctions
end Boundary
