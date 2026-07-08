import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Quotient.Operations.Sub.Laws.Basic.Owner

/-!
# Primitive cancellation laws for quotient subtraction

This file owns equality rearrangement and primitive cancellation laws for
quotient subtraction.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Move a right summand across an equality of quotient classes. -/
theorem TraceCorQQuotient.left_eq_sub_of_add_eq
    (left right tail : TraceCorQQuotient)
    (left_add_right_eq_tail :
      TraceCorQQuotient.add left right = tail) :
    left = TraceCorQQuotient.sub tail right :=
  Eq.trans
    (Eq.symm (TraceCorQQuotient.add_zero left))
    (Eq.trans
      (congrArg
        (TraceCorQQuotient.add left)
        (Eq.symm (TraceCorQQuotient.add_neg_self right)))
      (Eq.trans
        (Eq.symm
          (TraceCorQQuotient.add_assoc
            left
            right
            (TraceCorQQuotient.neg right)))
        (Eq.trans
          (congrArg
            (fun leftRight =>
              TraceCorQQuotient.add
                leftRight
                (TraceCorQQuotient.neg right))
            left_add_right_eq_tail)
          (Eq.symm
            (TraceCorQQuotient.sub_eq_add_neg tail right)))))

/-- Move a left summand across an equality of quotient classes. -/
theorem TraceCorQQuotient.right_eq_sub_of_add_eq
    (left right tail : TraceCorQQuotient)
    (left_add_right_eq_tail :
      TraceCorQQuotient.add left right = tail) :
    right = TraceCorQQuotient.sub tail left :=
  TraceCorQQuotient.left_eq_sub_of_add_eq
    right
    left
    tail
    (Eq.trans
      (TraceCorQQuotient.add_comm right left)
      left_add_right_eq_tail)

/-- Rebuild a quotient sum from a left-subtraction solution. -/
theorem TraceCorQQuotient.add_eq_of_left_eq_sub
    (left right tail : TraceCorQQuotient)
    (left_eq_tail_sub_right :
      left = TraceCorQQuotient.sub tail right) :
    TraceCorQQuotient.add left right = tail :=
  Eq.trans
    (congrArg
      (fun leftClass =>
        TraceCorQQuotient.add leftClass right)
      left_eq_tail_sub_right)
    (Eq.trans
      (congrArg
        (fun tailSubRight =>
          TraceCorQQuotient.add tailSubRight right)
        (TraceCorQQuotient.sub_eq_add_neg tail right))
      (Eq.trans
        (TraceCorQQuotient.add_assoc
          tail
          (TraceCorQQuotient.neg right)
          right)
        (Eq.trans
          (congrArg
            (TraceCorQQuotient.add tail)
            (TraceCorQQuotient.neg_add_self right))
          (TraceCorQQuotient.add_zero tail))))

/-- Rebuild a quotient sum from a right-subtraction solution. -/
theorem TraceCorQQuotient.add_eq_of_right_eq_sub
    (left right tail : TraceCorQQuotient)
    (right_eq_tail_sub_left :
      right = TraceCorQQuotient.sub tail left) :
    TraceCorQQuotient.add left right = tail :=
  Eq.trans
    (TraceCorQQuotient.add_comm left right)
    (TraceCorQQuotient.add_eq_of_left_eq_sub
      right
      left
      tail
      right_eq_tail_sub_left)

/-- Quotient subtraction cancels a common right-hand subtrahend. -/
theorem TraceCorQQuotient.sub_right_cancel
    (left right tail : TraceCorQQuotient)
    (left_sub_tail_eq_right_sub_tail :
      TraceCorQQuotient.sub left tail =
        TraceCorQQuotient.sub right tail) :
    left = right :=
  TraceCorQQuotient.add_right_cancel
    left
    right
    (TraceCorQQuotient.neg tail)
    (Eq.trans
      (Eq.symm (TraceCorQQuotient.sub_eq_add_neg left tail))
      (Eq.trans
        left_sub_tail_eq_right_sub_tail
        (TraceCorQQuotient.sub_eq_add_neg right tail)))

/-- Quotient subtraction cancels a common left-hand minuend. -/
theorem TraceCorQQuotient.sub_left_cancel
    (left right tail : TraceCorQQuotient)
    (left_sub_right_eq_left_sub_tail :
      TraceCorQQuotient.sub left right =
        TraceCorQQuotient.sub left tail) :
    right = tail :=
  Eq.trans
    (Eq.symm (TraceCorQQuotient.neg_neg right))
    (Eq.trans
      (congrArg
        TraceCorQQuotient.neg
        (TraceCorQQuotient.add_left_cancel
          left
          (TraceCorQQuotient.neg right)
          (TraceCorQQuotient.neg tail)
          (Eq.trans
            (Eq.symm (TraceCorQQuotient.sub_eq_add_neg left right))
            (Eq.trans
              left_sub_right_eq_left_sub_tail
              (TraceCorQQuotient.sub_eq_add_neg left tail)))))
      (TraceCorQQuotient.neg_neg tail))

end AnalyticMotives
end LFunctions
end Boundary
