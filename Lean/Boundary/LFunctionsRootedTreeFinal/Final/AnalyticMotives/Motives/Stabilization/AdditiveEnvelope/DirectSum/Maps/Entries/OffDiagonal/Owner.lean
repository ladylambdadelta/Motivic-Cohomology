import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Stabilization.AdditiveEnvelope.DirectSum.Maps.Entries.Diagonal.Owner

/-!
# Off-diagonal entries of direct-sum projection and inclusion matrices

This file records the zero entries of the sparse direct-sum maps away from the
matching summand coordinate.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- The left projection is zero away from the matching left summand index. -/
theorem TraceAnalyticAdditiveObject.leftDirectSumProjection_entry_ne_leftIndex
    (left right : TraceAnalyticAdditiveObject)
    (sourceIndex :
      Fin (TraceAnalyticAdditiveObject.directSum left right).length)
    (targetIndex : Fin left.length)
    (indices_ne :
      sourceIndex ≠
        TraceAnalyticAdditiveObject.leftDirectSumIndex left right targetIndex) :
    (TraceAnalyticAdditiveObject.leftDirectSumProjection left right).entry
      sourceIndex
      targetIndex =
      0 :=
  by
    cases h :
      Classical.decEq
        sourceIndex
        (TraceAnalyticAdditiveObject.leftDirectSumIndex left right targetIndex) with
    | isTrue indices_eq =>
        exact False.elim (indices_ne indices_eq)
    | isFalse _ =>
        rfl

/-- The right projection is zero away from the matching right summand index. -/
theorem TraceAnalyticAdditiveObject.rightDirectSumProjection_entry_ne_rightIndex
    (left right : TraceAnalyticAdditiveObject)
    (sourceIndex :
      Fin (TraceAnalyticAdditiveObject.directSum left right).length)
    (targetIndex : Fin right.length)
    (indices_ne :
      sourceIndex ≠
        TraceAnalyticAdditiveObject.rightDirectSumIndex left right targetIndex) :
    (TraceAnalyticAdditiveObject.rightDirectSumProjection left right).entry
      sourceIndex
      targetIndex =
      0 :=
  by
    cases h :
      Classical.decEq
        sourceIndex
        (TraceAnalyticAdditiveObject.rightDirectSumIndex left right targetIndex) with
    | isTrue indices_eq =>
        exact False.elim (indices_ne indices_eq)
    | isFalse _ =>
        rfl

/-- The left inclusion is zero away from the matching left summand index. -/
theorem TraceAnalyticAdditiveObject.leftDirectSumInclusion_entry_ne_leftIndex
    (left right : TraceAnalyticAdditiveObject)
    (sourceIndex : Fin left.length)
    (targetIndex :
      Fin (TraceAnalyticAdditiveObject.directSum left right).length)
    (indices_ne :
      targetIndex ≠
        TraceAnalyticAdditiveObject.leftDirectSumIndex left right sourceIndex) :
    (TraceAnalyticAdditiveObject.leftDirectSumInclusion left right).entry
      sourceIndex
      targetIndex =
      0 :=
  by
    cases h :
      Classical.decEq
        targetIndex
        (TraceAnalyticAdditiveObject.leftDirectSumIndex left right sourceIndex) with
    | isTrue indices_eq =>
        exact False.elim (indices_ne indices_eq)
    | isFalse _ =>
        rfl

/-- The right inclusion is zero away from the matching right summand index. -/
theorem TraceAnalyticAdditiveObject.rightDirectSumInclusion_entry_ne_rightIndex
    (left right : TraceAnalyticAdditiveObject)
    (sourceIndex : Fin right.length)
    (targetIndex :
      Fin (TraceAnalyticAdditiveObject.directSum left right).length)
    (indices_ne :
      targetIndex ≠
        TraceAnalyticAdditiveObject.rightDirectSumIndex left right sourceIndex) :
    (TraceAnalyticAdditiveObject.rightDirectSumInclusion left right).entry
      sourceIndex
      targetIndex =
      0 :=
  by
    cases h :
      Classical.decEq
        targetIndex
        (TraceAnalyticAdditiveObject.rightDirectSumIndex left right sourceIndex) with
    | isTrue indices_eq =>
        exact False.elim (indices_ne indices_eq)
    | isFalse _ =>
        rfl

end AnalyticMotives
end LFunctions
end Boundary
