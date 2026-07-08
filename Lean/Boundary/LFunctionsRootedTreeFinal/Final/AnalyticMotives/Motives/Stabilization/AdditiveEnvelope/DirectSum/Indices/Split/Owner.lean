import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Stabilization.AdditiveEnvelope.DirectSum.Indices.Owner

/-!
# Splitting indices of a binary direct sum

An index of the concatenated finite trace family lies either in the left
summand range or in the right summand range.  This file gives concrete index
constructors for those two cases and proves that re-embedding recovers the
original direct-sum index.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- A direct-sum index whose value is below the left length gives a left index. -/
def TraceAnalyticAdditiveObject.leftIndexOfDirectSumIndex
    (left right : TraceAnalyticAdditiveObject)
    (index : Fin (TraceAnalyticAdditiveObject.directSum left right).length)
    (index_lt_left : index.val < left.length) :
    Fin left.length :=
  ⟨index.val, index_lt_left⟩

/-- A direct-sum index outside the left range gives a right index. -/
def TraceAnalyticAdditiveObject.rightIndexOfDirectSumIndex
    (left right : TraceAnalyticAdditiveObject)
    (index : Fin (TraceAnalyticAdditiveObject.directSum left right).length)
    (index_not_lt_left : ¬ index.val < left.length) :
    Fin right.length :=
  ⟨index.val - left.length,
    (Nat.sub_lt_iff_lt_add
      (Nat.le_of_not_lt index_not_lt_left)).mpr
      (Eq.subst
        (motive := fun length =>
          index.val < length)
        (TraceAnalyticAdditiveObject.directSum_length left right)
        index.isLt)⟩

/-- Re-embedding a left-range direct-sum index recovers the original index. -/
theorem TraceAnalyticAdditiveObject.leftDirectSumIndex_leftIndexOf_eq
    (left right : TraceAnalyticAdditiveObject)
    (index : Fin (TraceAnalyticAdditiveObject.directSum left right).length)
    (index_lt_left : index.val < left.length) :
    TraceAnalyticAdditiveObject.leftDirectSumIndex
      left
      right
      (TraceAnalyticAdditiveObject.leftIndexOfDirectSumIndex
        left
        right
        index
        index_lt_left) =
      index :=
  Fin.ext
    (TraceAnalyticAdditiveObject.leftDirectSumIndex_val
      left
      right
      (TraceAnalyticAdditiveObject.leftIndexOfDirectSumIndex
        left
        right
        index
        index_lt_left))

/-- Re-embedding a right-range direct-sum index recovers the original index. -/
theorem TraceAnalyticAdditiveObject.rightDirectSumIndex_rightIndexOf_eq
    (left right : TraceAnalyticAdditiveObject)
    (index : Fin (TraceAnalyticAdditiveObject.directSum left right).length)
    (index_not_lt_left : ¬ index.val < left.length) :
    TraceAnalyticAdditiveObject.rightDirectSumIndex
      left
      right
      (TraceAnalyticAdditiveObject.rightIndexOfDirectSumIndex
        left
        right
        index
        index_not_lt_left) =
      index :=
  Fin.ext
    (Eq.trans
      (TraceAnalyticAdditiveObject.rightDirectSumIndex_val
        left
        right
        (TraceAnalyticAdditiveObject.rightIndexOfDirectSumIndex
          left
          right
          index
          index_not_lt_left))
      (Eq.trans
        (Nat.add_comm
          left.length
          (index.val - left.length))
        (Nat.sub_add_cancel
          (Nat.le_of_not_lt index_not_lt_left))))

end AnalyticMotives
end LFunctions
end Boundary
