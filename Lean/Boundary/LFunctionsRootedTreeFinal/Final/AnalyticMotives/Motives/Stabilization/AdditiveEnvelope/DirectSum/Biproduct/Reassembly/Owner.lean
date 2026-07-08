import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Stabilization.AdditiveEnvelope.DirectSum.Biproduct.Composites.Owner

/-!
# Direct-sum reassembly maps in the analytic additive envelope

This file names the two projection-then-inclusion endomorphisms of a binary
direct sum and their sum.  These are the matrix terms appearing in the
reassembly identity for biproducts.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- The left-summand endomorphism of a binary direct sum. -/
def TraceAnalyticAdditiveCategory.leftProjection_comp_leftInclusion
    (left right : TraceAnalyticAdditiveCategoryObject) :
    TraceAnalyticAdditiveCategoryHom
      (TraceAnalyticAdditiveObject.directSum left right)
      (TraceAnalyticAdditiveObject.directSum left right) :=
  TraceAnalyticAdditiveCategory.comp
    (TraceAnalyticAdditiveCategory.leftDirectSumProjection left right)
    (TraceAnalyticAdditiveCategory.leftDirectSumInclusion left right)

/-- The right-summand endomorphism of a binary direct sum. -/
def TraceAnalyticAdditiveCategory.rightProjection_comp_rightInclusion
    (left right : TraceAnalyticAdditiveCategoryObject) :
    TraceAnalyticAdditiveCategoryHom
      (TraceAnalyticAdditiveObject.directSum left right)
      (TraceAnalyticAdditiveObject.directSum left right) :=
  TraceAnalyticAdditiveCategory.comp
    (TraceAnalyticAdditiveCategory.rightDirectSumProjection left right)
    (TraceAnalyticAdditiveCategory.rightDirectSumInclusion left right)

/-- The direct-sum reassembly endomorphism as the sum of the two summand projectors. -/
def TraceAnalyticAdditiveCategory.directSumReassembly
    (left right : TraceAnalyticAdditiveCategoryObject) :
    TraceAnalyticAdditiveCategoryHom
      (TraceAnalyticAdditiveObject.directSum left right)
      (TraceAnalyticAdditiveObject.directSum left right) :=
  TraceAnalyticAdditiveHom.add
    (TraceAnalyticAdditiveCategory.leftProjection_comp_leftInclusion left right)
    (TraceAnalyticAdditiveCategory.rightProjection_comp_rightInclusion left right)

/-- Entry expansion for the left-summand direct-sum endomorphism. -/
theorem TraceAnalyticAdditiveCategory.leftProjection_comp_leftInclusion_entry
    (left right : TraceAnalyticAdditiveCategoryObject)
    (sourceIndex targetIndex :
      Fin (TraceAnalyticAdditiveObject.directSum left right).length) :
    (TraceAnalyticAdditiveCategory.leftProjection_comp_leftInclusion
      left
      right).entry sourceIndex targetIndex =
      Finset.univ.sum
        (fun middleIndex =>
          TraceCorQHom.comp
            ((TraceAnalyticAdditiveCategory.leftDirectSumProjection
              left
              right).entry sourceIndex middleIndex)
            ((TraceAnalyticAdditiveCategory.leftDirectSumInclusion
              left
              right).entry middleIndex targetIndex)) :=
  rfl

/-- Entry expansion for the right-summand direct-sum endomorphism. -/
theorem TraceAnalyticAdditiveCategory.rightProjection_comp_rightInclusion_entry
    (left right : TraceAnalyticAdditiveCategoryObject)
    (sourceIndex targetIndex :
      Fin (TraceAnalyticAdditiveObject.directSum left right).length) :
    (TraceAnalyticAdditiveCategory.rightProjection_comp_rightInclusion
      left
      right).entry sourceIndex targetIndex =
      Finset.univ.sum
        (fun middleIndex =>
          TraceCorQHom.comp
            ((TraceAnalyticAdditiveCategory.rightDirectSumProjection
              left
              right).entry sourceIndex middleIndex)
            ((TraceAnalyticAdditiveCategory.rightDirectSumInclusion
              left
              right).entry middleIndex targetIndex)) :=
  rfl

/-- Entry expansion for the direct-sum reassembly endomorphism. -/
theorem TraceAnalyticAdditiveCategory.directSumReassembly_entry
    (left right : TraceAnalyticAdditiveCategoryObject)
    (sourceIndex targetIndex :
      Fin (TraceAnalyticAdditiveObject.directSum left right).length) :
    (TraceAnalyticAdditiveCategory.directSumReassembly
      left
      right).entry sourceIndex targetIndex =
      TraceCorQHom.add
        ((TraceAnalyticAdditiveCategory.leftProjection_comp_leftInclusion
          left
          right).entry sourceIndex targetIndex)
        ((TraceAnalyticAdditiveCategory.rightProjection_comp_rightInclusion
          left
          right).entry sourceIndex targetIndex) :=
  rfl

end AnalyticMotives
end LFunctions
end Boundary
