import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Stabilization.AdditiveEnvelope.DirectSum.Biproduct.Reassembly.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Stabilization.AdditiveEnvelope.Homs.Identity.Entries.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Stabilization.AdditiveEnvelope.Homs.Transport.Composition.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Stabilization.AdditiveEnvelope.DirectSum.Maps.Entries.OffDiagonal.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Category.Laws.Linearity.Instances.Owner

/-!
# Left-range entries of the direct-sum reassembly projector

This file proves the left-summand matrix entries of the projection-then-
inclusion endomorphism of a binary direct sum.  These are concrete finite-sum
collapses using the sparse direct-sum projection and inclusion matrices.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- The matching left-range summand of the left projector is the identity. -/
theorem TraceAnalyticAdditiveCategory.leftProjection_comp_leftInclusion_leftDiagonalSummand
    (left right : TraceAnalyticAdditiveCategoryObject)
    (index : Fin left.length) :
    TraceCorQHom.comp
      ((TraceAnalyticAdditiveCategory.leftDirectSumProjection left right).entry
        (TraceAnalyticAdditiveObject.leftDirectSumIndex left right index)
        index)
      ((TraceAnalyticAdditiveCategory.leftDirectSumInclusion left right).entry
        index
        (TraceAnalyticAdditiveObject.leftDirectSumIndex left right index)) =
      TraceCorQHom.id
        ((TraceAnalyticAdditiveObject.directSum left right).component
          (TraceAnalyticAdditiveObject.leftDirectSumIndex left right index)) :=
  Eq.trans
    (congrArg₂
      TraceCorQHom.comp
      (Eq.trans
        (TraceAnalyticAdditiveCategory.leftDirectSumProjection_entry
          left
          right
          (TraceAnalyticAdditiveObject.leftDirectSumIndex left right index)
          index)
        (TraceAnalyticAdditiveObject.leftDirectSumProjection_entry_leftIndex
          left
          right
          index))
      (Eq.trans
        (TraceAnalyticAdditiveCategory.leftDirectSumInclusion_entry
          left
          right
          index
          (TraceAnalyticAdditiveObject.leftDirectSumIndex left right index))
        (TraceAnalyticAdditiveObject.leftDirectSumInclusion_entry_leftIndex
          left
          right
          index)))
    (TraceAnalyticAdditiveHom.transportedId_comp_symm
      (TraceAnalyticAdditiveObject.leftDirectSumComponent_eq_target
        left
        right
        index))

/-- Away from the matching source summand, a left-range projector summand is zero. -/
theorem TraceAnalyticAdditiveCategory.leftProjection_comp_leftInclusion_leftNeSummand
    (left right : TraceAnalyticAdditiveCategoryObject)
    (sourceIndex targetIndex : Fin left.length)
    (middleIndex : Fin left.length)
    (middle_ne : middleIndex ≠ sourceIndex) :
    TraceCorQHom.comp
      ((TraceAnalyticAdditiveCategory.leftDirectSumProjection left right).entry
        (TraceAnalyticAdditiveObject.leftDirectSumIndex left right sourceIndex)
        middleIndex)
      ((TraceAnalyticAdditiveCategory.leftDirectSumInclusion left right).entry
        middleIndex
        (TraceAnalyticAdditiveObject.leftDirectSumIndex left right targetIndex)) =
      0 :=
  Eq.trans
    (congrArg
      (fun head =>
        TraceCorQHom.comp
          head
          ((TraceAnalyticAdditiveCategory.leftDirectSumInclusion
            left
            right).entry
            middleIndex
            (TraceAnalyticAdditiveObject.leftDirectSumIndex left right targetIndex)))
      (Eq.trans
        (TraceAnalyticAdditiveCategory.leftDirectSumProjection_entry
          left
          right
          (TraceAnalyticAdditiveObject.leftDirectSumIndex left right sourceIndex)
          middleIndex)
        (TraceAnalyticAdditiveObject.leftDirectSumProjection_entry_ne_leftIndex
          left
          right
          (TraceAnalyticAdditiveObject.leftDirectSumIndex left right sourceIndex)
          middleIndex
          (fun index_eq =>
            middle_ne
              (TraceAnalyticAdditiveObject.leftDirectSumIndex_injective
                left
                right
                (Eq.symm index_eq))))))
    (TraceCorQHom.std_zero_comp
      ((TraceAnalyticAdditiveCategory.leftDirectSumInclusion
        left
        right).entry
        middleIndex
        (TraceAnalyticAdditiveObject.leftDirectSumIndex left right targetIndex)))

/-- At the matching source summand, an off-diagonal left-range projector summand is zero. -/
theorem TraceAnalyticAdditiveCategory.leftProjection_comp_leftInclusion_leftSourceSummand_ne
    (left right : TraceAnalyticAdditiveCategoryObject)
    (sourceIndex targetIndex : Fin left.length)
    (indices_ne : sourceIndex ≠ targetIndex) :
    TraceCorQHom.comp
      ((TraceAnalyticAdditiveCategory.leftDirectSumProjection left right).entry
        (TraceAnalyticAdditiveObject.leftDirectSumIndex left right sourceIndex)
        sourceIndex)
      ((TraceAnalyticAdditiveCategory.leftDirectSumInclusion left right).entry
        sourceIndex
        (TraceAnalyticAdditiveObject.leftDirectSumIndex left right targetIndex)) =
      0 :=
  Eq.trans
    (congrArg
      (fun tail =>
        TraceCorQHom.comp
          ((TraceAnalyticAdditiveCategory.leftDirectSumProjection
            left
            right).entry
            (TraceAnalyticAdditiveObject.leftDirectSumIndex left right sourceIndex)
            sourceIndex)
          tail)
      (Eq.trans
        (TraceAnalyticAdditiveCategory.leftDirectSumInclusion_entry
          left
          right
          sourceIndex
          (TraceAnalyticAdditiveObject.leftDirectSumIndex left right targetIndex))
        (TraceAnalyticAdditiveObject.leftDirectSumInclusion_entry_ne_leftIndex
          left
          right
          sourceIndex
          (TraceAnalyticAdditiveObject.leftDirectSumIndex left right targetIndex)
          (fun index_eq =>
            indices_ne
              (TraceAnalyticAdditiveObject.leftDirectSumIndex_injective
                left
                right
                (Eq.symm index_eq))))))
    (TraceCorQHom.std_comp_zero
      ((TraceAnalyticAdditiveCategory.leftDirectSumProjection
        left
        right).entry
        (TraceAnalyticAdditiveObject.leftDirectSumIndex left right sourceIndex)
        sourceIndex))

/-- Every off-diagonal left-range summand of the left projector is zero. -/
theorem TraceAnalyticAdditiveCategory.leftProjection_comp_leftInclusion_leftNeEntrySummand
    (left right : TraceAnalyticAdditiveCategoryObject)
    (sourceIndex targetIndex : Fin left.length)
    (indices_ne : sourceIndex ≠ targetIndex)
    (middleIndex : Fin left.length) :
    TraceCorQHom.comp
      ((TraceAnalyticAdditiveCategory.leftDirectSumProjection left right).entry
        (TraceAnalyticAdditiveObject.leftDirectSumIndex left right sourceIndex)
        middleIndex)
      ((TraceAnalyticAdditiveCategory.leftDirectSumInclusion left right).entry
        middleIndex
        (TraceAnalyticAdditiveObject.leftDirectSumIndex left right targetIndex)) =
      0 :=
  match Classical.decEq middleIndex sourceIndex with
  | isTrue middle_eq =>
      Eq.subst
        (motive := fun index =>
          TraceCorQHom.comp
            ((TraceAnalyticAdditiveCategory.leftDirectSumProjection
              left
              right).entry
              (TraceAnalyticAdditiveObject.leftDirectSumIndex left right sourceIndex)
              index)
            ((TraceAnalyticAdditiveCategory.leftDirectSumInclusion
              left
              right).entry
              index
              (TraceAnalyticAdditiveObject.leftDirectSumIndex left right targetIndex)) =
            0)
        (Eq.symm middle_eq)
        (TraceAnalyticAdditiveCategory.leftProjection_comp_leftInclusion_leftSourceSummand_ne
          left
          right
          sourceIndex
          targetIndex
          indices_ne)
  | isFalse middle_ne =>
      TraceAnalyticAdditiveCategory.leftProjection_comp_leftInclusion_leftNeSummand
        left
        right
        sourceIndex
        targetIndex
        middleIndex
        middle_ne

/-- A left-range diagonal entry of the left projector is the direct-sum identity entry. -/
theorem TraceAnalyticAdditiveCategory.leftProjection_comp_leftInclusion_leftEntry_self
    (left right : TraceAnalyticAdditiveCategoryObject)
    (index : Fin left.length) :
    (TraceAnalyticAdditiveCategory.leftProjection_comp_leftInclusion
      left
      right).entry
      (TraceAnalyticAdditiveObject.leftDirectSumIndex left right index)
      (TraceAnalyticAdditiveObject.leftDirectSumIndex left right index) =
      (TraceAnalyticAdditiveCategory.id
        (TraceAnalyticAdditiveObject.directSum left right)).entry
        (TraceAnalyticAdditiveObject.leftDirectSumIndex left right index)
        (TraceAnalyticAdditiveObject.leftDirectSumIndex left right index) :=
  Eq.trans
    (TraceAnalyticAdditiveCategory.leftProjection_comp_leftInclusion_entry
      left
      right
      (TraceAnalyticAdditiveObject.leftDirectSumIndex left right index)
      (TraceAnalyticAdditiveObject.leftDirectSumIndex left right index))
    (Eq.trans
      (Finset.sum_eq_single
        index
        (fun middleIndex _membership middle_ne =>
          TraceAnalyticAdditiveCategory.leftProjection_comp_leftInclusion_leftNeSummand
            left
            right
            index
            index
            middleIndex
            middle_ne)
        (fun index_not_mem =>
          False.elim
            (index_not_mem
              (Finset.mem_univ index))))
      (Eq.trans
        (TraceAnalyticAdditiveCategory.leftProjection_comp_leftInclusion_leftDiagonalSummand
          left
          right
          index)
        (Eq.symm
          (TraceAnalyticAdditiveHom.id_entry_self
            (TraceAnalyticAdditiveObject.directSum left right)
            (TraceAnalyticAdditiveObject.leftDirectSumIndex left right index)))))

/-- A left-range off-diagonal entry of the left projector is the direct-sum zero identity entry. -/
theorem TraceAnalyticAdditiveCategory.leftProjection_comp_leftInclusion_leftEntry_ne
    (left right : TraceAnalyticAdditiveCategoryObject)
    (sourceIndex targetIndex : Fin left.length)
    (indices_ne : sourceIndex ≠ targetIndex) :
    (TraceAnalyticAdditiveCategory.leftProjection_comp_leftInclusion
      left
      right).entry
      (TraceAnalyticAdditiveObject.leftDirectSumIndex left right sourceIndex)
      (TraceAnalyticAdditiveObject.leftDirectSumIndex left right targetIndex) =
      (TraceAnalyticAdditiveCategory.id
        (TraceAnalyticAdditiveObject.directSum left right)).entry
        (TraceAnalyticAdditiveObject.leftDirectSumIndex left right sourceIndex)
        (TraceAnalyticAdditiveObject.leftDirectSumIndex left right targetIndex) :=
  Eq.trans
    (TraceAnalyticAdditiveCategory.leftProjection_comp_leftInclusion_entry
      left
      right
      (TraceAnalyticAdditiveObject.leftDirectSumIndex left right sourceIndex)
      (TraceAnalyticAdditiveObject.leftDirectSumIndex left right targetIndex))
    (Eq.trans
      (Finset.sum_eq_zero
        (fun middleIndex _membership =>
          TraceAnalyticAdditiveCategory.leftProjection_comp_leftInclusion_leftNeEntrySummand
            left
            right
            sourceIndex
            targetIndex
            indices_ne
            middleIndex))
      (Eq.symm
        (TraceAnalyticAdditiveHom.id_entry_ne
          (TraceAnalyticAdditiveObject.directSum left right)
          (TraceAnalyticAdditiveObject.leftDirectSumIndex left right sourceIndex)
          (TraceAnalyticAdditiveObject.leftDirectSumIndex left right targetIndex)
          (fun index_eq =>
            indices_ne
              (TraceAnalyticAdditiveObject.leftDirectSumIndex_injective
                left
                right
                index_eq)))))

end AnalyticMotives
end LFunctions
end Boundary
