import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Stabilization.AdditiveEnvelope.Category.Laws.Comparisons.Owner

/-!
# Identity-law summand families

This file names the middle-indexed summand families appearing in the left and
right identity laws for the analytic additive-envelope category.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- The summand family for the left-identity composite entry. -/
def TraceAnalyticAdditiveCategory.leftIdentitySummand
    {source target : TraceAnalyticAdditiveCategoryObject}
    (hom : TraceAnalyticAdditiveCategoryHom source target)
    (sourceIndex : Fin source.length)
    (targetIndex : Fin target.length)
    (middleIndex : Fin source.length) :
    TraceCorQHom
      (source.component sourceIndex)
      (target.component targetIndex) :=
  TraceCorQHom.comp
    ((TraceAnalyticAdditiveCategory.id source).entry
      sourceIndex
      middleIndex)
    (hom.entry middleIndex targetIndex)

/-- The summand family for the right-identity composite entry. -/
def TraceAnalyticAdditiveCategory.rightIdentitySummand
    {source target : TraceAnalyticAdditiveCategoryObject}
    (hom : TraceAnalyticAdditiveCategoryHom source target)
    (sourceIndex : Fin source.length)
    (targetIndex : Fin target.length)
    (middleIndex : Fin target.length) :
    TraceCorQHom
      (source.component sourceIndex)
      (target.component targetIndex) :=
  TraceCorQHom.comp
    (hom.entry sourceIndex middleIndex)
    ((TraceAnalyticAdditiveCategory.id target).entry
      middleIndex
      targetIndex)

/-- The target entry family for identity laws. -/
def TraceAnalyticAdditiveCategory.identityTargetEntry
    {source target : TraceAnalyticAdditiveCategoryObject}
    (hom : TraceAnalyticAdditiveCategoryHom source target)
    (sourceIndex : Fin source.length)
    (targetIndex : Fin target.length) :
    TraceCorQHom
      (source.component sourceIndex)
      (target.component targetIndex) :=
  hom.entry sourceIndex targetIndex

/-- The left-identity summand is the raw matrix-composition summand. -/
theorem TraceAnalyticAdditiveCategory.leftIdentitySummand_eq_raw
    {source target : TraceAnalyticAdditiveCategoryObject}
    (hom : TraceAnalyticAdditiveCategoryHom source target)
    (sourceIndex : Fin source.length)
    (targetIndex : Fin target.length)
    (middleIndex : Fin source.length) :
    TraceAnalyticAdditiveCategory.leftIdentitySummand
      hom
      sourceIndex
      targetIndex
      middleIndex =
      TraceCorQHom.comp
        ((TraceAnalyticAdditiveCategory.id source).entry
          sourceIndex
          middleIndex)
        (hom.entry middleIndex targetIndex) :=
  rfl

/-- The right-identity summand is the raw matrix-composition summand. -/
theorem TraceAnalyticAdditiveCategory.rightIdentitySummand_eq_raw
    {source target : TraceAnalyticAdditiveCategoryObject}
    (hom : TraceAnalyticAdditiveCategoryHom source target)
    (sourceIndex : Fin source.length)
    (targetIndex : Fin target.length)
    (middleIndex : Fin target.length) :
    TraceAnalyticAdditiveCategory.rightIdentitySummand
      hom
      sourceIndex
      targetIndex
      middleIndex =
      TraceCorQHom.comp
        (hom.entry sourceIndex middleIndex)
        ((TraceAnalyticAdditiveCategory.id target).entry
          middleIndex
          targetIndex) :=
  rfl

end AnalyticMotives
end LFunctions
end Boundary
