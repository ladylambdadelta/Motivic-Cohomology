import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Stabilization.AdditiveEnvelope.Category.Laws.Identity.Summands.Owner

/-!
# Finite-sum collapse for identity laws

The finite sums defining left and right identity composites collapse to their
single diagonal summand.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- The left-identity entry sum collapses to the target entry. -/
theorem TraceAnalyticAdditiveCategory.leftIdentityEntrySum_eq_target
    {source target : TraceAnalyticAdditiveCategoryObject}
    (hom : TraceAnalyticAdditiveCategoryHom source target)
    (sourceIndex : Fin source.length)
    (targetIndex : Fin target.length) :
    TraceAnalyticAdditiveCategory.leftIdentityEntrySum
      hom
      sourceIndex
      targetIndex =
      TraceAnalyticAdditiveCategory.identityTargetEntry
        hom
        sourceIndex
        targetIndex :=
  Eq.trans
    (Finset.sum_eq_single
      sourceIndex
      (fun middleIndex _membership middle_ne_source =>
        TraceAnalyticAdditiveCategory.leftIdentitySummand_ne_eq_zero
          hom
          sourceIndex
          targetIndex
          middleIndex
          (fun source_eq_middle =>
            middle_ne_source
              (Eq.symm source_eq_middle)))
      (fun source_not_mem =>
        False.elim
          (source_not_mem
            (Finset.mem_univ sourceIndex))))
    (TraceAnalyticAdditiveCategory.leftIdentitySummand_self_eq_target
      hom
      sourceIndex
      targetIndex)

/-- The right-identity entry sum collapses to the target entry. -/
theorem TraceAnalyticAdditiveCategory.rightIdentityEntrySum_eq_target
    {source target : TraceAnalyticAdditiveCategoryObject}
    (hom : TraceAnalyticAdditiveCategoryHom source target)
    (sourceIndex : Fin source.length)
    (targetIndex : Fin target.length) :
    TraceAnalyticAdditiveCategory.rightIdentityEntrySum
      hom
      sourceIndex
      targetIndex =
      TraceAnalyticAdditiveCategory.identityTargetEntry
        hom
        sourceIndex
        targetIndex :=
  Eq.trans
    (Finset.sum_eq_single
      targetIndex
      (fun middleIndex _membership middle_ne_target =>
        TraceAnalyticAdditiveCategory.rightIdentitySummand_ne_eq_zero
          hom
          sourceIndex
          targetIndex
          middleIndex
          middle_ne_target)
      (fun target_not_mem =>
        False.elim
          (target_not_mem
            (Finset.mem_univ targetIndex))))
    (TraceAnalyticAdditiveCategory.rightIdentitySummand_self_eq_target
      hom
      sourceIndex
      targetIndex)

end AnalyticMotives
end LFunctions
end Boundary
