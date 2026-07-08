import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Stabilization.AdditiveEnvelope.Homs.Transport.Composition.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Stabilization.AdditiveEnvelope.Homs.Identity.Entries.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Stabilization.AdditiveEnvelope.DirectSum.Maps.Entries.OffDiagonal.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Stabilization.AdditiveEnvelope.DirectSum.Biproduct.Composites.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Category.Laws.Linearity.Instances.Owner

/-!
# Diagonal entries of direct-sum biproduct composites

This file starts the projection-after-inclusion identities by collapsing the
diagonal entries of the left-left composite.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- The diagonal summand in the left-left direct-sum composite is the identity. -/
theorem TraceAnalyticAdditiveCategory.leftInclusion_comp_leftProjection_diagonalSummand
    (left right : TraceAnalyticAdditiveCategoryObject)
    (index : Fin left.length) :
    TraceCorQHom.comp
      ((TraceAnalyticAdditiveCategory.leftDirectSumInclusion left right).entry
        index
        (TraceAnalyticAdditiveObject.leftDirectSumIndex left right index))
      ((TraceAnalyticAdditiveCategory.leftDirectSumProjection left right).entry
        (TraceAnalyticAdditiveObject.leftDirectSumIndex left right index)
        index) =
      TraceCorQHom.id (left.component index) :=
  Eq.trans
    (congrArg₂
      TraceCorQHom.comp
      (Eq.trans
        (TraceAnalyticAdditiveCategory.leftDirectSumInclusion_entry
          left
          right
          index
          (TraceAnalyticAdditiveObject.leftDirectSumIndex left right index))
        (TraceAnalyticAdditiveObject.leftDirectSumInclusion_entry_leftIndex
          left
          right
          index))
      (Eq.trans
        (TraceAnalyticAdditiveCategory.leftDirectSumProjection_entry
          left
          right
          (TraceAnalyticAdditiveObject.leftDirectSumIndex left right index)
          index)
        (TraceAnalyticAdditiveObject.leftDirectSumProjection_entry_leftIndex
          left
          right
          index)))
    (TraceAnalyticAdditiveHom.transportedId_symm_comp
      (TraceAnalyticAdditiveObject.leftDirectSumComponent_eq_target
        left
        right
        index))

/-- Away from the diagonal summand, the left-left composite summand is zero. -/
theorem TraceAnalyticAdditiveCategory.leftInclusion_comp_leftProjection_neSummand
    (left right : TraceAnalyticAdditiveCategoryObject)
    (sourceIndex targetIndex : Fin left.length)
    (middleIndex :
      Fin (TraceAnalyticAdditiveObject.directSum left right).length)
    (middle_ne :
      middleIndex ≠
        TraceAnalyticAdditiveObject.leftDirectSumIndex left right sourceIndex) :
    TraceCorQHom.comp
      ((TraceAnalyticAdditiveCategory.leftDirectSumInclusion left right).entry
        sourceIndex
        middleIndex)
      ((TraceAnalyticAdditiveCategory.leftDirectSumProjection left right).entry
        middleIndex
        targetIndex) =
      0 :=
  Eq.trans
    (congrArg
      (fun head =>
        TraceCorQHom.comp
          head
          ((TraceAnalyticAdditiveCategory.leftDirectSumProjection
            left
            right).entry middleIndex targetIndex))
      (Eq.trans
        (TraceAnalyticAdditiveCategory.leftDirectSumInclusion_entry
          left
          right
          sourceIndex
          middleIndex)
        (TraceAnalyticAdditiveObject.leftDirectSumInclusion_entry_ne_leftIndex
          left
          right
          sourceIndex
          middleIndex
          middle_ne)))
    (TraceCorQHom.std_zero_comp
      ((TraceAnalyticAdditiveCategory.leftDirectSumProjection
        left
        right).entry middleIndex targetIndex))

/-- A diagonal entry of the left-left direct-sum composite is the identity entry. -/
theorem TraceAnalyticAdditiveCategory.leftInclusion_comp_leftProjection_entry_self
    (left right : TraceAnalyticAdditiveCategoryObject)
    (index : Fin left.length) :
    (TraceAnalyticAdditiveCategory.leftInclusion_comp_leftProjection
      left
      right).entry index index =
      (TraceAnalyticAdditiveCategory.id left).entry index index :=
  Eq.trans
    (TraceAnalyticAdditiveCategory.leftInclusion_comp_leftProjection_entry
      left
      right
      index
      index)
    (Eq.trans
      (Finset.sum_eq_single
        (TraceAnalyticAdditiveObject.leftDirectSumIndex left right index)
        (fun middleIndex _membership middle_ne =>
          TraceAnalyticAdditiveCategory.leftInclusion_comp_leftProjection_neSummand
            left
            right
            index
            index
            middleIndex
            middle_ne)
        (fun index_not_mem =>
          False.elim
            (index_not_mem
              (Finset.mem_univ
                (TraceAnalyticAdditiveObject.leftDirectSumIndex left right index)))))
      (Eq.trans
        (TraceAnalyticAdditiveCategory.leftInclusion_comp_leftProjection_diagonalSummand
          left
          right
          index)
        (Eq.symm
          (TraceAnalyticAdditiveHom.id_entry_self left index))))

end AnalyticMotives
end LFunctions
end Boundary
