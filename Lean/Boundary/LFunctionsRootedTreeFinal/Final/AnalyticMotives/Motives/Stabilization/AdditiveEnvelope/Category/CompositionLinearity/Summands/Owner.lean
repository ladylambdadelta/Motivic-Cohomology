import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Stabilization.AdditiveEnvelope.Category.Additive.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Category.Laws.Linearity.Add.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Category.Laws.Linearity.Smul.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Category.Laws.Linearity.Zero.Owner

/-!
# Summand-level composition linearity in the analytic additive envelope

Matrix composition is a finite sum of typed trace-correspondence composites.
This file proves the linearity identities for each individual middle-index
summand, before the finite-sum bookkeeping is applied.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- A zero left matrix entry gives a zero composition summand. -/
theorem TraceAnalyticAdditiveCategory.zero_left_comp_summand
    {source middle target : TraceAnalyticAdditiveCategoryObject}
    (right : TraceAnalyticAdditiveCategoryHom middle target)
    (sourceIndex : Fin source.length)
    (middleIndex : Fin middle.length)
    (targetIndex : Fin target.length) :
    TraceCorQHom.comp
      ((TraceAnalyticAdditiveCategory.zeroHom source middle).entry
        sourceIndex
        middleIndex)
      (right.entry middleIndex targetIndex) =
      (TraceAnalyticAdditiveCategory.zeroHom source target).entry
        sourceIndex
        targetIndex :=
  TraceCorQHom.zero_comp
    (right.entry middleIndex targetIndex)

/-- A zero right matrix entry gives a zero composition summand. -/
theorem TraceAnalyticAdditiveCategory.comp_zero_right_summand
    {source middle target : TraceAnalyticAdditiveCategoryObject}
    (left : TraceAnalyticAdditiveCategoryHom source middle)
    (sourceIndex : Fin source.length)
    (middleIndex : Fin middle.length)
    (targetIndex : Fin target.length) :
    TraceCorQHom.comp
      (left.entry sourceIndex middleIndex)
      ((TraceAnalyticAdditiveCategory.zeroHom middle target).entry
        middleIndex
        targetIndex) =
      (TraceAnalyticAdditiveCategory.zeroHom source target).entry
        sourceIndex
        targetIndex :=
  TraceCorQHom.comp_zero
    (left.entry sourceIndex middleIndex)

/-- Addition in the left matrix entry distributes over a composition summand. -/
theorem TraceAnalyticAdditiveCategory.add_left_comp_summand
    {source middle target : TraceAnalyticAdditiveCategoryObject}
    (left right : TraceAnalyticAdditiveCategoryHom source middle)
    (tail : TraceAnalyticAdditiveCategoryHom middle target)
    (sourceIndex : Fin source.length)
    (middleIndex : Fin middle.length)
    (targetIndex : Fin target.length) :
    TraceCorQHom.comp
      ((TraceAnalyticAdditiveCategory.addHom left right).entry
        sourceIndex
        middleIndex)
      (tail.entry middleIndex targetIndex) =
      TraceCorQHom.add
        (TraceCorQHom.comp
          (left.entry sourceIndex middleIndex)
          (tail.entry middleIndex targetIndex))
        (TraceCorQHom.comp
          (right.entry sourceIndex middleIndex)
          (tail.entry middleIndex targetIndex)) :=
  TraceCorQHom.add_comp
    (left.entry sourceIndex middleIndex)
    (right.entry sourceIndex middleIndex)
    (tail.entry middleIndex targetIndex)

/-- Addition in the right matrix entry distributes over a composition summand. -/
theorem TraceAnalyticAdditiveCategory.comp_add_right_summand
    {source middle target : TraceAnalyticAdditiveCategoryObject}
    (head : TraceAnalyticAdditiveCategoryHom source middle)
    (left right : TraceAnalyticAdditiveCategoryHom middle target)
    (sourceIndex : Fin source.length)
    (middleIndex : Fin middle.length)
    (targetIndex : Fin target.length) :
    TraceCorQHom.comp
      (head.entry sourceIndex middleIndex)
      ((TraceAnalyticAdditiveCategory.addHom left right).entry
        middleIndex
        targetIndex) =
      TraceCorQHom.add
        (TraceCorQHom.comp
          (head.entry sourceIndex middleIndex)
          (left.entry middleIndex targetIndex))
        (TraceCorQHom.comp
          (head.entry sourceIndex middleIndex)
          (right.entry middleIndex targetIndex)) :=
  TraceCorQHom.comp_add
    (head.entry sourceIndex middleIndex)
    (left.entry middleIndex targetIndex)
    (right.entry middleIndex targetIndex)

/-- Scaling the left matrix entry scales a composition summand. -/
theorem TraceAnalyticAdditiveCategory.smul_left_comp_summand
    (coefficient : Rat)
    {source middle target : TraceAnalyticAdditiveCategoryObject}
    (left : TraceAnalyticAdditiveCategoryHom source middle)
    (right : TraceAnalyticAdditiveCategoryHom middle target)
    (sourceIndex : Fin source.length)
    (middleIndex : Fin middle.length)
    (targetIndex : Fin target.length) :
    TraceCorQHom.comp
      ((TraceAnalyticAdditiveCategory.smulHom coefficient left).entry
        sourceIndex
        middleIndex)
      (right.entry middleIndex targetIndex) =
      TraceCorQHom.smul
        coefficient
        (TraceCorQHom.comp
          (left.entry sourceIndex middleIndex)
          (right.entry middleIndex targetIndex)) :=
  TraceCorQHom.smul_comp
    coefficient
    (left.entry sourceIndex middleIndex)
    (right.entry middleIndex targetIndex)

/-- Scaling the right matrix entry scales a composition summand. -/
theorem TraceAnalyticAdditiveCategory.comp_smul_right_summand
    (coefficient : Rat)
    {source middle target : TraceAnalyticAdditiveCategoryObject}
    (left : TraceAnalyticAdditiveCategoryHom source middle)
    (right : TraceAnalyticAdditiveCategoryHom middle target)
    (sourceIndex : Fin source.length)
    (middleIndex : Fin middle.length)
    (targetIndex : Fin target.length) :
    TraceCorQHom.comp
      (left.entry sourceIndex middleIndex)
      ((TraceAnalyticAdditiveCategory.smulHom coefficient right).entry
        middleIndex
        targetIndex) =
      TraceCorQHom.smul
        coefficient
        (TraceCorQHom.comp
          (left.entry sourceIndex middleIndex)
          (right.entry middleIndex targetIndex)) :=
  TraceCorQHom.comp_smul
    coefficient
    (left.entry sourceIndex middleIndex)
    (right.entry middleIndex targetIndex)

end AnalyticMotives
end LFunctions
end Boundary
