import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Stabilization.AdditiveEnvelope.Homs.Identity.Entries.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Stabilization.AdditiveEnvelope.Category.Laws.Identity.FiniteSums.Owner

/-!
# Identity-law summand collapse

Each identity-composite summand is either the target matrix entry on the
diagonal or zero away from it.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- The diagonal left-identity summand is the target entry. -/
theorem TraceAnalyticAdditiveCategory.leftIdentitySummand_self_eq_target
    {source target : TraceAnalyticAdditiveCategoryObject}
    (hom : TraceAnalyticAdditiveCategoryHom source target)
    (sourceIndex : Fin source.length)
    (targetIndex : Fin target.length) :
    TraceAnalyticAdditiveCategory.leftIdentitySummand
      hom
      sourceIndex
      targetIndex
      sourceIndex =
      TraceAnalyticAdditiveCategory.identityTargetEntry
        hom
        sourceIndex
        targetIndex :=
  Eq.trans
    (congrArg
      (fun head =>
        TraceCorQHom.comp
          head
          (hom.entry sourceIndex targetIndex))
      (TraceAnalyticAdditiveHom.id_entry_self
        source
        sourceIndex))
    (TraceCorQHom.left_id
      (hom.entry sourceIndex targetIndex))

/-- An off-diagonal left-identity summand is zero. -/
theorem TraceAnalyticAdditiveCategory.leftIdentitySummand_ne_eq_zero
    {source target : TraceAnalyticAdditiveCategoryObject}
    (hom : TraceAnalyticAdditiveCategoryHom source target)
    (sourceIndex : Fin source.length)
    (targetIndex : Fin target.length)
    (middleIndex : Fin source.length)
    (indices_ne : sourceIndex ≠ middleIndex) :
    TraceAnalyticAdditiveCategory.leftIdentitySummand
      hom
      sourceIndex
      targetIndex
      middleIndex =
      0 :=
  Eq.trans
    (congrArg
      (fun head =>
        TraceCorQHom.comp
          head
          (hom.entry middleIndex targetIndex))
      (TraceAnalyticAdditiveHom.id_entry_ne
        source
        sourceIndex
        middleIndex
        indices_ne))
    (TraceCorQHom.zero_comp
      (hom.entry middleIndex targetIndex))

/-- The diagonal right-identity summand is the target entry. -/
theorem TraceAnalyticAdditiveCategory.rightIdentitySummand_self_eq_target
    {source target : TraceAnalyticAdditiveCategoryObject}
    (hom : TraceAnalyticAdditiveCategoryHom source target)
    (sourceIndex : Fin source.length)
    (targetIndex : Fin target.length) :
    TraceAnalyticAdditiveCategory.rightIdentitySummand
      hom
      sourceIndex
      targetIndex
      targetIndex =
      TraceAnalyticAdditiveCategory.identityTargetEntry
        hom
        sourceIndex
        targetIndex :=
  Eq.trans
    (congrArg
      (fun tail =>
        TraceCorQHom.comp
          (hom.entry sourceIndex targetIndex)
          tail)
      (TraceAnalyticAdditiveHom.id_entry_self
        target
        targetIndex))
    (TraceCorQHom.right_id
      (hom.entry sourceIndex targetIndex))

/-- An off-diagonal right-identity summand is zero. -/
theorem TraceAnalyticAdditiveCategory.rightIdentitySummand_ne_eq_zero
    {source target : TraceAnalyticAdditiveCategoryObject}
    (hom : TraceAnalyticAdditiveCategoryHom source target)
    (sourceIndex : Fin source.length)
    (targetIndex : Fin target.length)
    (middleIndex : Fin target.length)
    (indices_ne : middleIndex ≠ targetIndex) :
    TraceAnalyticAdditiveCategory.rightIdentitySummand
      hom
      sourceIndex
      targetIndex
      middleIndex =
      0 :=
  Eq.trans
    (congrArg
      (fun tail =>
        TraceCorQHom.comp
          (hom.entry sourceIndex middleIndex)
          tail)
      (TraceAnalyticAdditiveHom.id_entry_ne
        target
        middleIndex
        targetIndex
        indices_ne))
    (TraceCorQHom.comp_zero
      (hom.entry sourceIndex middleIndex))

end AnalyticMotives
end LFunctions
end Boundary
