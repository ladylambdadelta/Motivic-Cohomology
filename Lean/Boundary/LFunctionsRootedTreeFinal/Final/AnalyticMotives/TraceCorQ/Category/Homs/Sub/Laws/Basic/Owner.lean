import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Category.Homs.Neg.Laws.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Category.Homs.Smul.Laws.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Category.Homs.Sub.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Quotient.Operations.Sub.Laws.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Category.Homs.Sub.Laws.Zero.Owner

/-!
# Basic subtraction laws for typed trace-correspondence hom classes

This file proves the primitive typed subtraction solver and cancellation laws
from the concrete definition `left + neg right`.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Move a right summand across an equality of typed homs. -/
theorem TraceCorQHom.left_eq_sub_of_add_eq
    {source target : TraceCorQObject}
    (left right tail : TraceCorQHom source target)
    (left_add_right_eq_tail :
      TraceCorQHom.add left right = tail) :
    left = TraceCorQHom.sub tail right :=
  Eq.trans
    (Eq.symm (TraceCorQHom.add_zero left))
    (Eq.trans
      (congrArg
        (TraceCorQHom.add left)
        (Eq.symm (TraceCorQHom.add_neg_self right)))
      (Eq.trans
        (Eq.symm
          (TraceCorQHom.add_assoc
            left
            right
            (TraceCorQHom.neg right)))
        (Eq.trans
          (congrArg
            (fun leftRight =>
              TraceCorQHom.add
                leftRight
                (TraceCorQHom.neg right))
            left_add_right_eq_tail)
          (Eq.symm
            (TraceCorQHom.sub_eq_add_neg tail right)))))

/-- Move a left summand across an equality of typed homs. -/
theorem TraceCorQHom.right_eq_sub_of_add_eq
    {source target : TraceCorQObject}
    (left right tail : TraceCorQHom source target)
    (left_add_right_eq_tail :
      TraceCorQHom.add left right = tail) :
    right = TraceCorQHom.sub tail left :=
  TraceCorQHom.left_eq_sub_of_add_eq
    right
    left
    tail
    (Eq.trans
      (TraceCorQHom.add_comm right left)
      left_add_right_eq_tail)

/-- Rebuild a typed hom sum from a left-subtraction solution. -/
theorem TraceCorQHom.add_eq_of_left_eq_sub
    {source target : TraceCorQObject}
    (left right tail : TraceCorQHom source target)
    (left_eq_tail_sub_right :
      left = TraceCorQHom.sub tail right) :
    TraceCorQHom.add left right = tail :=
  Eq.trans
    (congrArg
      (fun leftHom =>
        TraceCorQHom.add leftHom right)
      left_eq_tail_sub_right)
    (Eq.trans
      (congrArg
        (fun tailSubRight =>
          TraceCorQHom.add tailSubRight right)
        (TraceCorQHom.sub_eq_add_neg tail right))
      (Eq.trans
        (TraceCorQHom.add_assoc
          tail
          (TraceCorQHom.neg right)
          right)
        (Eq.trans
          (congrArg
            (TraceCorQHom.add tail)
            (TraceCorQHom.neg_add_self right))
          (TraceCorQHom.add_zero tail))))

/-- Rebuild a typed hom sum from a right-subtraction solution. -/
theorem TraceCorQHom.add_eq_of_right_eq_sub
    {source target : TraceCorQObject}
    (left right tail : TraceCorQHom source target)
    (right_eq_tail_sub_left :
      right = TraceCorQHom.sub tail left) :
    TraceCorQHom.add left right = tail :=
  Eq.trans
    (TraceCorQHom.add_comm left right)
    (TraceCorQHom.add_eq_of_left_eq_sub
      right
      left
      tail
      right_eq_tail_sub_left)

/-- Typed hom subtraction cancels a common right-hand subtrahend. -/
theorem TraceCorQHom.sub_right_cancel
    {source target : TraceCorQObject}
    (left right tail : TraceCorQHom source target)
    (left_sub_tail_eq_right_sub_tail :
      TraceCorQHom.sub left tail =
        TraceCorQHom.sub right tail) :
    left = right :=
  TraceCorQHom.add_right_cancel
    left
    right
    (TraceCorQHom.neg tail)
    (Eq.trans
      (Eq.symm (TraceCorQHom.sub_eq_add_neg left tail))
      (Eq.trans
        left_sub_tail_eq_right_sub_tail
        (TraceCorQHom.sub_eq_add_neg right tail)))

/-- Typed hom subtraction cancels a common left-hand minuend. -/
theorem TraceCorQHom.sub_left_cancel
    {source target : TraceCorQObject}
    (left right tail : TraceCorQHom source target)
    (left_sub_right_eq_left_sub_tail :
      TraceCorQHom.sub left right =
        TraceCorQHom.sub left tail) :
    right = tail :=
  Eq.trans
    (Eq.symm (TraceCorQHom.neg_neg right))
    (Eq.trans
      (congrArg
        TraceCorQHom.neg
        (TraceCorQHom.add_left_cancel
          left
          (TraceCorQHom.neg right)
          (TraceCorQHom.neg tail)
          (Eq.trans
            (Eq.symm (TraceCorQHom.sub_eq_add_neg left right))
            (Eq.trans
              left_sub_right_eq_left_sub_tail
              (TraceCorQHom.sub_eq_add_neg left tail)))))
      (TraceCorQHom.neg_neg tail))

end AnalyticMotives
end LFunctions
end Boundary
