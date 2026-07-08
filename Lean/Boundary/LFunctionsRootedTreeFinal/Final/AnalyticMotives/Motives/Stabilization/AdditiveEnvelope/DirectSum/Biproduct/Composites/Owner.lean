import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Stabilization.AdditiveEnvelope.Category.Entries.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Stabilization.AdditiveEnvelope.DirectSum.CategoryMaps.Entries.Owner

/-!
# Direct-sum composite maps in the analytic additive envelope

This file names the four projection-after-inclusion composites for a binary
direct sum of finite analytic trace families.  The entry formulas expose the
matrix products used by the biproduct identities.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- The left projection after the left inclusion. -/
def TraceAnalyticAdditiveCategory.leftInclusion_comp_leftProjection
    (left right : TraceAnalyticAdditiveCategoryObject) :
    TraceAnalyticAdditiveCategoryHom left left :=
  TraceAnalyticAdditiveCategory.comp
    (TraceAnalyticAdditiveCategory.leftDirectSumInclusion left right)
    (TraceAnalyticAdditiveCategory.leftDirectSumProjection left right)

/-- The right projection after the left inclusion. -/
def TraceAnalyticAdditiveCategory.leftInclusion_comp_rightProjection
    (left right : TraceAnalyticAdditiveCategoryObject) :
    TraceAnalyticAdditiveCategoryHom left right :=
  TraceAnalyticAdditiveCategory.comp
    (TraceAnalyticAdditiveCategory.leftDirectSumInclusion left right)
    (TraceAnalyticAdditiveCategory.rightDirectSumProjection left right)

/-- The left projection after the right inclusion. -/
def TraceAnalyticAdditiveCategory.rightInclusion_comp_leftProjection
    (left right : TraceAnalyticAdditiveCategoryObject) :
    TraceAnalyticAdditiveCategoryHom right left :=
  TraceAnalyticAdditiveCategory.comp
    (TraceAnalyticAdditiveCategory.rightDirectSumInclusion left right)
    (TraceAnalyticAdditiveCategory.leftDirectSumProjection left right)

/-- The right projection after the right inclusion. -/
def TraceAnalyticAdditiveCategory.rightInclusion_comp_rightProjection
    (left right : TraceAnalyticAdditiveCategoryObject) :
    TraceAnalyticAdditiveCategoryHom right right :=
  TraceAnalyticAdditiveCategory.comp
    (TraceAnalyticAdditiveCategory.rightDirectSumInclusion left right)
    (TraceAnalyticAdditiveCategory.rightDirectSumProjection left right)

/-- Entry expansion for the left-projection-after-left-inclusion composite. -/
theorem TraceAnalyticAdditiveCategory.leftInclusion_comp_leftProjection_entry
    (left right : TraceAnalyticAdditiveCategoryObject)
    (sourceIndex targetIndex : Fin left.length) :
    (TraceAnalyticAdditiveCategory.leftInclusion_comp_leftProjection
      left
      right).entry sourceIndex targetIndex =
      Finset.univ.sum
        (fun middleIndex =>
          TraceCorQHom.comp
            ((TraceAnalyticAdditiveCategory.leftDirectSumInclusion
              left
              right).entry sourceIndex middleIndex)
            ((TraceAnalyticAdditiveCategory.leftDirectSumProjection
              left
              right).entry middleIndex targetIndex)) :=
  rfl

/-- Entry expansion for the right-projection-after-left-inclusion composite. -/
theorem TraceAnalyticAdditiveCategory.leftInclusion_comp_rightProjection_entry
    (left right : TraceAnalyticAdditiveCategoryObject)
    (sourceIndex : Fin left.length)
    (targetIndex : Fin right.length) :
    (TraceAnalyticAdditiveCategory.leftInclusion_comp_rightProjection
      left
      right).entry sourceIndex targetIndex =
      Finset.univ.sum
        (fun middleIndex =>
          TraceCorQHom.comp
            ((TraceAnalyticAdditiveCategory.leftDirectSumInclusion
              left
              right).entry sourceIndex middleIndex)
            ((TraceAnalyticAdditiveCategory.rightDirectSumProjection
              left
              right).entry middleIndex targetIndex)) :=
  rfl

/-- Entry expansion for the left-projection-after-right-inclusion composite. -/
theorem TraceAnalyticAdditiveCategory.rightInclusion_comp_leftProjection_entry
    (left right : TraceAnalyticAdditiveCategoryObject)
    (sourceIndex : Fin right.length)
    (targetIndex : Fin left.length) :
    (TraceAnalyticAdditiveCategory.rightInclusion_comp_leftProjection
      left
      right).entry sourceIndex targetIndex =
      Finset.univ.sum
        (fun middleIndex =>
          TraceCorQHom.comp
            ((TraceAnalyticAdditiveCategory.rightDirectSumInclusion
              left
              right).entry sourceIndex middleIndex)
            ((TraceAnalyticAdditiveCategory.leftDirectSumProjection
              left
              right).entry middleIndex targetIndex)) :=
  rfl

/-- Entry expansion for the right-projection-after-right-inclusion composite. -/
theorem TraceAnalyticAdditiveCategory.rightInclusion_comp_rightProjection_entry
    (left right : TraceAnalyticAdditiveCategoryObject)
    (sourceIndex targetIndex : Fin right.length) :
    (TraceAnalyticAdditiveCategory.rightInclusion_comp_rightProjection
      left
      right).entry sourceIndex targetIndex =
      Finset.univ.sum
        (fun middleIndex =>
          TraceCorQHom.comp
            ((TraceAnalyticAdditiveCategory.rightDirectSumInclusion
              left
              right).entry sourceIndex middleIndex)
            ((TraceAnalyticAdditiveCategory.rightDirectSumProjection
              left
              right).entry middleIndex targetIndex)) :=
  rfl

end AnalyticMotives
end LFunctions
end Boundary
