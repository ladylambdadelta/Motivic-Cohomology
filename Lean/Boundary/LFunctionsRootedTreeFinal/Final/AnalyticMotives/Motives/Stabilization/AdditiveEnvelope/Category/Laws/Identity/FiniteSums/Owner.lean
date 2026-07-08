import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Stabilization.AdditiveEnvelope.Category.Laws.Identity.Families.Owner

/-!
# Identity-law finite sums

This file names the finite sums of the identity-law summand families and links
the comparison-matrix entries to those sums.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- The finite sum for a left-identity composite entry. -/
def TraceAnalyticAdditiveCategory.leftIdentityEntrySum
    {source target : TraceAnalyticAdditiveCategoryObject}
    (hom : TraceAnalyticAdditiveCategoryHom source target)
    (sourceIndex : Fin source.length)
    (targetIndex : Fin target.length) :
    TraceCorQHom
      (source.component sourceIndex)
      (target.component targetIndex) :=
  Finset.univ.sum
    (TraceAnalyticAdditiveCategory.leftIdentitySummand
      hom
      sourceIndex
      targetIndex)

/-- The finite sum for a right-identity composite entry. -/
def TraceAnalyticAdditiveCategory.rightIdentityEntrySum
    {source target : TraceAnalyticAdditiveCategoryObject}
    (hom : TraceAnalyticAdditiveCategoryHom source target)
    (sourceIndex : Fin source.length)
    (targetIndex : Fin target.length) :
    TraceCorQHom
      (source.component sourceIndex)
      (target.component targetIndex) :=
  Finset.univ.sum
    (TraceAnalyticAdditiveCategory.rightIdentitySummand
      hom
      sourceIndex
      targetIndex)

/-- The left-identity comparison entry is its named finite summand-family sum. -/
theorem TraceAnalyticAdditiveCategory.leftIdentityComposite_entry_eq_sum
    {source target : TraceAnalyticAdditiveCategoryObject}
    (hom : TraceAnalyticAdditiveCategoryHom source target)
    (sourceIndex : Fin source.length)
    (targetIndex : Fin target.length) :
    (TraceAnalyticAdditiveCategory.leftIdentityComposite hom).entry
      sourceIndex
      targetIndex =
      TraceAnalyticAdditiveCategory.leftIdentityEntrySum
        hom
        sourceIndex
        targetIndex :=
  rfl

/-- The right-identity comparison entry is its named finite summand-family sum. -/
theorem TraceAnalyticAdditiveCategory.rightIdentityComposite_entry_eq_sum
    {source target : TraceAnalyticAdditiveCategoryObject}
    (hom : TraceAnalyticAdditiveCategoryHom source target)
    (sourceIndex : Fin source.length)
    (targetIndex : Fin target.length) :
    (TraceAnalyticAdditiveCategory.rightIdentityComposite hom).entry
      sourceIndex
      targetIndex =
      TraceAnalyticAdditiveCategory.rightIdentityEntrySum
        hom
        sourceIndex
        targetIndex :=
  rfl

end AnalyticMotives
end LFunctions
end Boundary
