import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Stabilization.AdditiveEnvelope.DirectSum.Maps.Entries.Owner

/-!
# Diagonal entries of direct-sum projection and inclusion matrices

This file records the nonzero entries of the sparse direct-sum maps.  The
entries are transported trace identities along the component equalities of the
concatenated finite family.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- The left projection has a transported identity at a left summand index. -/
theorem TraceAnalyticAdditiveObject.leftDirectSumProjection_entry_leftIndex
    (left right : TraceAnalyticAdditiveObject)
    (targetIndex : Fin left.length) :
    (TraceAnalyticAdditiveObject.leftDirectSumProjection left right).entry
      (TraceAnalyticAdditiveObject.leftDirectSumIndex left right targetIndex)
      targetIndex =
      TraceAnalyticAdditiveHom.transportedId
        (TraceAnalyticAdditiveObject.leftDirectSumComponent_eq_target
          left
          right
          targetIndex) :=
  by
    cases h :
      Classical.decEq
        (TraceAnalyticAdditiveObject.leftDirectSumIndex left right targetIndex)
        (TraceAnalyticAdditiveObject.leftDirectSumIndex left right targetIndex) with
    | isTrue indices_eq =>
        cases indices_eq
        rfl
    | isFalse indices_ne =>
        exact False.elim (indices_ne rfl)

/-- The right projection has a transported identity at a right summand index. -/
theorem TraceAnalyticAdditiveObject.rightDirectSumProjection_entry_rightIndex
    (left right : TraceAnalyticAdditiveObject)
    (targetIndex : Fin right.length) :
    (TraceAnalyticAdditiveObject.rightDirectSumProjection left right).entry
      (TraceAnalyticAdditiveObject.rightDirectSumIndex left right targetIndex)
      targetIndex =
      TraceAnalyticAdditiveHom.transportedId
        (TraceAnalyticAdditiveObject.rightDirectSumComponent_eq_target
          left
          right
          targetIndex) :=
  by
    cases h :
      Classical.decEq
        (TraceAnalyticAdditiveObject.rightDirectSumIndex left right targetIndex)
        (TraceAnalyticAdditiveObject.rightDirectSumIndex left right targetIndex) with
    | isTrue indices_eq =>
        cases indices_eq
        rfl
    | isFalse indices_ne =>
        exact False.elim (indices_ne rfl)

/-- The left inclusion has a transported identity at a left summand index. -/
theorem TraceAnalyticAdditiveObject.leftDirectSumInclusion_entry_leftIndex
    (left right : TraceAnalyticAdditiveObject)
    (sourceIndex : Fin left.length) :
    (TraceAnalyticAdditiveObject.leftDirectSumInclusion left right).entry
      sourceIndex
      (TraceAnalyticAdditiveObject.leftDirectSumIndex left right sourceIndex) =
      TraceAnalyticAdditiveHom.transportedId
        (Eq.symm
          (TraceAnalyticAdditiveObject.leftDirectSumComponent_eq_target
            left
            right
            sourceIndex)) :=
  by
    cases h :
      Classical.decEq
        (TraceAnalyticAdditiveObject.leftDirectSumIndex left right sourceIndex)
        (TraceAnalyticAdditiveObject.leftDirectSumIndex left right sourceIndex) with
    | isTrue indices_eq =>
        cases indices_eq
        rfl
    | isFalse indices_ne =>
        exact False.elim (indices_ne rfl)

/-- The right inclusion has a transported identity at a right summand index. -/
theorem TraceAnalyticAdditiveObject.rightDirectSumInclusion_entry_rightIndex
    (left right : TraceAnalyticAdditiveObject)
    (sourceIndex : Fin right.length) :
    (TraceAnalyticAdditiveObject.rightDirectSumInclusion left right).entry
      sourceIndex
      (TraceAnalyticAdditiveObject.rightDirectSumIndex left right sourceIndex) =
      TraceAnalyticAdditiveHom.transportedId
        (Eq.symm
          (TraceAnalyticAdditiveObject.rightDirectSumComponent_eq_target
            left
            right
            sourceIndex)) :=
  by
    cases h :
      Classical.decEq
        (TraceAnalyticAdditiveObject.rightDirectSumIndex left right sourceIndex)
        (TraceAnalyticAdditiveObject.rightDirectSumIndex left right sourceIndex) with
    | isTrue indices_eq =>
        cases indices_eq
        rfl
    | isFalse indices_ne =>
        exact False.elim (indices_ne rfl)

end AnalyticMotives
end LFunctions
end Boundary
