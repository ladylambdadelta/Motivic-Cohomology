import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Stabilization.AdditiveEnvelope.Homs.Ext.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Stabilization.AdditiveEnvelope.Category.Laws.Associativity.Fubini.Owner

/-!
# Full associativity for additive-envelope matrix composition

The entrywise Fubini comparison proves associativity of concrete matrix
composition in the analytic additive envelope.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- The two associated triple-composite matrix entries are equal. -/
theorem TraceAnalyticAdditiveCategory.assocComposite_entry_eq
    {first second third fourth : TraceAnalyticAdditiveCategoryObject}
    (left : TraceAnalyticAdditiveCategoryHom first second)
    (middle : TraceAnalyticAdditiveCategoryHom second third)
    (right : TraceAnalyticAdditiveCategoryHom third fourth)
    (sourceIndex : Fin first.length)
    (targetIndex : Fin fourth.length) :
    (TraceAnalyticAdditiveCategory.assocLeftComposite
      left
      middle
      right).entry sourceIndex targetIndex =
      (TraceAnalyticAdditiveCategory.assocRightComposite
        left
        middle
        right).entry sourceIndex targetIndex :=
  Eq.trans
    (TraceAnalyticAdditiveCategory.assocLeftComposite_entry_eq_outerSum
      left
      middle
      right
      sourceIndex
      targetIndex)
    (Eq.trans
      (TraceAnalyticAdditiveCategory.assocLeftOuterEntrySum_eq_rightOuterEntrySum
        left
        middle
        right
        sourceIndex
        targetIndex)
      (Eq.symm
        (TraceAnalyticAdditiveCategory.assocRightComposite_entry_eq_outerSum
          left
          middle
          right
          sourceIndex
          targetIndex)))

/-- Matrix composition in the analytic additive envelope is associative. -/
theorem TraceAnalyticAdditiveCategory.comp_assoc
    {first second third fourth : TraceAnalyticAdditiveCategoryObject}
    (left : TraceAnalyticAdditiveCategoryHom first second)
    (middle : TraceAnalyticAdditiveCategoryHom second third)
    (right : TraceAnalyticAdditiveCategoryHom third fourth) :
    TraceAnalyticAdditiveCategory.comp
      (TraceAnalyticAdditiveCategory.comp left middle)
      right =
      TraceAnalyticAdditiveCategory.comp
        left
        (TraceAnalyticAdditiveCategory.comp middle right) :=
  TraceAnalyticAdditiveHom.ext
    (fun sourceIndex targetIndex =>
      TraceAnalyticAdditiveCategory.assocComposite_entry_eq
        left
        middle
        right
        sourceIndex
        targetIndex)

end AnalyticMotives
end LFunctions
end Boundary
