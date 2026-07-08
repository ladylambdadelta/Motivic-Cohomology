import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Stabilization.AdditiveEnvelope.Homs.Ext.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Stabilization.AdditiveEnvelope.Category.Laws.Identity.Collapse.Owner

/-!
# Full identity laws for additive-envelope matrix composition

The finite-sum collapse of identity-composite entries proves the left and right
identity laws for concrete matrix composition.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- The left-identity composite has the same entries as the original hom. -/
theorem TraceAnalyticAdditiveCategory.leftIdentityComposite_entry_eq_target
    {source target : TraceAnalyticAdditiveCategoryObject}
    (hom : TraceAnalyticAdditiveCategoryHom source target)
    (sourceIndex : Fin source.length)
    (targetIndex : Fin target.length) :
    (TraceAnalyticAdditiveCategory.leftIdentityComposite hom).entry
      sourceIndex
      targetIndex =
      hom.entry sourceIndex targetIndex :=
  Eq.trans
    (TraceAnalyticAdditiveCategory.leftIdentityComposite_entry_eq_sum
      hom
      sourceIndex
      targetIndex)
    (TraceAnalyticAdditiveCategory.leftIdentityEntrySum_eq_target
      hom
      sourceIndex
      targetIndex)

/-- The right-identity composite has the same entries as the original hom. -/
theorem TraceAnalyticAdditiveCategory.rightIdentityComposite_entry_eq_target
    {source target : TraceAnalyticAdditiveCategoryObject}
    (hom : TraceAnalyticAdditiveCategoryHom source target)
    (sourceIndex : Fin source.length)
    (targetIndex : Fin target.length) :
    (TraceAnalyticAdditiveCategory.rightIdentityComposite hom).entry
      sourceIndex
      targetIndex =
      hom.entry sourceIndex targetIndex :=
  Eq.trans
    (TraceAnalyticAdditiveCategory.rightIdentityComposite_entry_eq_sum
      hom
      sourceIndex
      targetIndex)
    (TraceAnalyticAdditiveCategory.rightIdentityEntrySum_eq_target
      hom
      sourceIndex
      targetIndex)

/-- Left identity for matrix composition in the analytic additive envelope. -/
theorem TraceAnalyticAdditiveCategory.comp_id_left
    {source target : TraceAnalyticAdditiveCategoryObject}
    (hom : TraceAnalyticAdditiveCategoryHom source target) :
    TraceAnalyticAdditiveCategory.comp
      (TraceAnalyticAdditiveCategory.id source)
      hom =
      hom :=
  TraceAnalyticAdditiveHom.ext
    (fun sourceIndex targetIndex =>
      TraceAnalyticAdditiveCategory.leftIdentityComposite_entry_eq_target
        hom
        sourceIndex
        targetIndex)

/-- Right identity for matrix composition in the analytic additive envelope. -/
theorem TraceAnalyticAdditiveCategory.comp_id_right
    {source target : TraceAnalyticAdditiveCategoryObject}
    (hom : TraceAnalyticAdditiveCategoryHom source target) :
    TraceAnalyticAdditiveCategory.comp
      hom
      (TraceAnalyticAdditiveCategory.id target) =
      hom :=
  TraceAnalyticAdditiveHom.ext
    (fun sourceIndex targetIndex =>
      TraceAnalyticAdditiveCategory.rightIdentityComposite_entry_eq_target
        hom
        sourceIndex
        targetIndex)

end AnalyticMotives
end LFunctions
end Boundary
