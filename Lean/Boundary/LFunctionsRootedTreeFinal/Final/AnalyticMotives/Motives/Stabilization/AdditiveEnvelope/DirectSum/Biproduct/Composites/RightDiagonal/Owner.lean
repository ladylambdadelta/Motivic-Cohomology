import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Stabilization.AdditiveEnvelope.DirectSum.Biproduct.Composites.Full.Owner

/-!
# Diagonal entries of the right-right direct-sum composite

This file collapses the diagonal entries of the right-inclusion followed by
right-projection composite.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- The diagonal summand in the right-right direct-sum composite is the identity. -/
theorem TraceAnalyticAdditiveCategory.rightInclusion_comp_rightProjection_diagonalSummand
    (left right : TraceAnalyticAdditiveCategoryObject)
    (index : Fin right.length) :
    TraceCorQHom.comp
      ((TraceAnalyticAdditiveCategory.rightDirectSumInclusion left right).entry
        index
        (TraceAnalyticAdditiveObject.rightDirectSumIndex left right index))
      ((TraceAnalyticAdditiveCategory.rightDirectSumProjection left right).entry
        (TraceAnalyticAdditiveObject.rightDirectSumIndex left right index)
        index) =
      TraceCorQHom.id (right.component index) :=
  Eq.trans
    (congrArg₂
      TraceCorQHom.comp
      (Eq.trans
        (TraceAnalyticAdditiveCategory.rightDirectSumInclusion_entry
          left
          right
          index
          (TraceAnalyticAdditiveObject.rightDirectSumIndex left right index))
        (TraceAnalyticAdditiveObject.rightDirectSumInclusion_entry_rightIndex
          left
          right
          index))
      (Eq.trans
        (TraceAnalyticAdditiveCategory.rightDirectSumProjection_entry
          left
          right
          (TraceAnalyticAdditiveObject.rightDirectSumIndex left right index)
          index)
        (TraceAnalyticAdditiveObject.rightDirectSumProjection_entry_rightIndex
          left
          right
          index)))
    (TraceAnalyticAdditiveHom.transportedId_symm_comp
      (TraceAnalyticAdditiveObject.rightDirectSumComponent_eq_target
        left
        right
        index))

/-- Away from the diagonal summand, the right-right composite summand is zero. -/
theorem TraceAnalyticAdditiveCategory.rightInclusion_comp_rightProjection_neSummand
    (left right : TraceAnalyticAdditiveCategoryObject)
    (sourceIndex targetIndex : Fin right.length)
    (middleIndex :
      Fin (TraceAnalyticAdditiveObject.directSum left right).length)
    (middle_ne :
      middleIndex ≠
        TraceAnalyticAdditiveObject.rightDirectSumIndex left right sourceIndex) :
    TraceCorQHom.comp
      ((TraceAnalyticAdditiveCategory.rightDirectSumInclusion left right).entry
        sourceIndex
        middleIndex)
      ((TraceAnalyticAdditiveCategory.rightDirectSumProjection left right).entry
        middleIndex
        targetIndex) =
      0 :=
  Eq.trans
    (congrArg
      (fun head =>
        TraceCorQHom.comp
          head
          ((TraceAnalyticAdditiveCategory.rightDirectSumProjection
            left
            right).entry middleIndex targetIndex))
      (Eq.trans
        (TraceAnalyticAdditiveCategory.rightDirectSumInclusion_entry
          left
          right
          sourceIndex
          middleIndex)
        (TraceAnalyticAdditiveObject.rightDirectSumInclusion_entry_ne_rightIndex
          left
          right
          sourceIndex
          middleIndex
          middle_ne)))
    (TraceCorQHom.std_zero_comp
      ((TraceAnalyticAdditiveCategory.rightDirectSumProjection
        left
        right).entry middleIndex targetIndex))

/-- A diagonal entry of the right-right direct-sum composite is the identity entry. -/
theorem TraceAnalyticAdditiveCategory.rightInclusion_comp_rightProjection_entry_self
    (left right : TraceAnalyticAdditiveCategoryObject)
    (index : Fin right.length) :
    (TraceAnalyticAdditiveCategory.rightInclusion_comp_rightProjection
      left
      right).entry index index =
      (TraceAnalyticAdditiveCategory.id right).entry index index :=
  Eq.trans
    (TraceAnalyticAdditiveCategory.rightInclusion_comp_rightProjection_entry
      left
      right
      index
      index)
    (Eq.trans
      (Finset.sum_eq_single
        (TraceAnalyticAdditiveObject.rightDirectSumIndex left right index)
        (fun middleIndex _membership middle_ne =>
          TraceAnalyticAdditiveCategory.rightInclusion_comp_rightProjection_neSummand
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
                (TraceAnalyticAdditiveObject.rightDirectSumIndex left right index)))))
      (Eq.trans
        (TraceAnalyticAdditiveCategory.rightInclusion_comp_rightProjection_diagonalSummand
          left
          right
          index)
        (Eq.symm
          (TraceAnalyticAdditiveHom.id_entry_self right index))))

end AnalyticMotives
end LFunctions
end Boundary
