import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Stabilization.AdditiveEnvelope.Category.Owner

/-!
# Direct-sum indices in the analytic additive envelope

The direct sum of finite trace families is list concatenation.  This file names
the two canonical index embeddings into the concatenated family.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- The left summand index inside a concatenated analytic trace family. -/
def TraceAnalyticAdditiveObject.leftDirectSumIndex
    (left right : TraceAnalyticAdditiveObject)
    (index : Fin left.length) :
    Fin (TraceAnalyticAdditiveObject.directSum left right).length :=
  Fin.cast
    (Eq.symm
      (TraceAnalyticAdditiveObject.directSum_length left right))
    (Fin.castAdd right.length index)

/-- The right summand index inside a concatenated analytic trace family. -/
def TraceAnalyticAdditiveObject.rightDirectSumIndex
    (left right : TraceAnalyticAdditiveObject)
    (index : Fin right.length) :
    Fin (TraceAnalyticAdditiveObject.directSum left right).length :=
  Fin.cast
    (Eq.symm
      (TraceAnalyticAdditiveObject.directSum_length left right))
    (Fin.natAdd left.length index)

/-- The left direct-sum index has the same numeric value as the original left index. -/
theorem TraceAnalyticAdditiveObject.leftDirectSumIndex_val
    (left right : TraceAnalyticAdditiveObject)
    (index : Fin left.length) :
    (TraceAnalyticAdditiveObject.leftDirectSumIndex left right index).val =
      index.val :=
  rfl

/-- The right direct-sum index is shifted by the length of the left summand. -/
theorem TraceAnalyticAdditiveObject.rightDirectSumIndex_val
    (left right : TraceAnalyticAdditiveObject)
    (index : Fin right.length) :
    (TraceAnalyticAdditiveObject.rightDirectSumIndex left right index).val =
      left.length + index.val :=
  rfl

/-- Subtracting the left length from a right direct-sum index recovers the right index. -/
theorem TraceAnalyticAdditiveObject.rightDirectSumIndex_val_sub_left_length
    (left right : TraceAnalyticAdditiveObject)
    (index : Fin right.length) :
    (TraceAnalyticAdditiveObject.rightDirectSumIndex left right index).val -
        left.length =
      index.val :=
  Eq.trans
    (congrArg
      (fun value =>
        value - left.length)
      (TraceAnalyticAdditiveObject.rightDirectSumIndex_val left right index))
    (Nat.add_sub_cancel_left index.val left.length)

/-- The left summand index embedding into a direct sum is injective. -/
theorem TraceAnalyticAdditiveObject.leftDirectSumIndex_injective
    (left right : TraceAnalyticAdditiveObject)
    {first second : Fin left.length}
    (indices_eq :
      TraceAnalyticAdditiveObject.leftDirectSumIndex left right first =
        TraceAnalyticAdditiveObject.leftDirectSumIndex left right second) :
    first = second :=
  Fin.ext
    (Eq.trans
      (Eq.symm
        (TraceAnalyticAdditiveObject.leftDirectSumIndex_val left right first))
      (Eq.trans
        (congrArg Fin.val indices_eq)
        (TraceAnalyticAdditiveObject.leftDirectSumIndex_val left right second)))

/-- The right summand index embedding into a direct sum is injective. -/
theorem TraceAnalyticAdditiveObject.rightDirectSumIndex_injective
    (left right : TraceAnalyticAdditiveObject)
    {first second : Fin right.length}
    (indices_eq :
      TraceAnalyticAdditiveObject.rightDirectSumIndex left right first =
        TraceAnalyticAdditiveObject.rightDirectSumIndex left right second) :
    first = second :=
  Fin.ext
    (Nat.add_left_cancel
      (Eq.trans
        (Eq.symm
          (TraceAnalyticAdditiveObject.rightDirectSumIndex_val left right first))
        (Eq.trans
          (congrArg Fin.val indices_eq)
          (TraceAnalyticAdditiveObject.rightDirectSumIndex_val left right second))))

/-- Left and right summand index embeddings into a direct sum have disjoint images. -/
theorem TraceAnalyticAdditiveObject.leftDirectSumIndex_ne_rightDirectSumIndex
    (left right : TraceAnalyticAdditiveObject)
    (leftIndex : Fin left.length)
    (rightIndex : Fin right.length) :
    TraceAnalyticAdditiveObject.leftDirectSumIndex left right leftIndex ≠
      TraceAnalyticAdditiveObject.rightDirectSumIndex left right rightIndex :=
  fun indices_eq =>
    let val_eq :
        leftIndex.val =
          left.length + rightIndex.val :=
      Eq.trans
        (Eq.symm
          (TraceAnalyticAdditiveObject.leftDirectSumIndex_val left right leftIndex))
        (Eq.trans
          (congrArg Fin.val indices_eq)
          (TraceAnalyticAdditiveObject.rightDirectSumIndex_val left right rightIndex))
    let shifted_lt :
        left.length + rightIndex.val <
          left.length :=
      Eq.subst
        (motive := fun value =>
          value < left.length)
        val_eq
        leftIndex.isLt
    (Nat.not_lt_of_ge
      (Nat.le_add_right left.length rightIndex.val))
      shifted_lt

/-- Right and left summand index embeddings into a direct sum have disjoint images. -/
theorem TraceAnalyticAdditiveObject.rightDirectSumIndex_ne_leftDirectSumIndex
    (left right : TraceAnalyticAdditiveObject)
    (rightIndex : Fin right.length)
    (leftIndex : Fin left.length) :
    TraceAnalyticAdditiveObject.rightDirectSumIndex left right rightIndex ≠
      TraceAnalyticAdditiveObject.leftDirectSumIndex left right leftIndex :=
  fun indices_eq =>
    TraceAnalyticAdditiveObject.leftDirectSumIndex_ne_rightDirectSumIndex
      left
      right
      leftIndex
      rightIndex
      (Eq.symm indices_eq)

end AnalyticMotives
end LFunctions
end Boundary
