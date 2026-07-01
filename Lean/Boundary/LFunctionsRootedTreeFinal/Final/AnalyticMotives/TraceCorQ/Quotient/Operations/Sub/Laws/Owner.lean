import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Quotient.Operations.Neg.Laws.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Quotient.Operations.Comp.Laws.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Quotient.Operations.Sub.Owner

/-!
# Subtraction laws for quotient trace correspondences

This file proves basic laws for quotient subtraction from the concrete
definition `left + neg right`.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Subtracting zero on the right leaves a quotient class unchanged. -/
theorem TraceCorQQuotient.sub_zero
    (candidateClass : TraceCorQQuotient) :
    TraceCorQQuotient.sub candidateClass TraceCorQQuotient.zero =
      candidateClass :=
  Eq.trans
    (TraceCorQQuotient.sub_eq_add_neg
      candidateClass
      TraceCorQQuotient.zero)
    (Eq.trans
      (congrArg
        (TraceCorQQuotient.add candidateClass)
        TraceCorQQuotient.neg_zero)
      (TraceCorQQuotient.add_zero candidateClass))

/-- Zero minus a quotient class is its negative. -/
theorem TraceCorQQuotient.zero_sub
    (candidateClass : TraceCorQQuotient) :
    TraceCorQQuotient.sub TraceCorQQuotient.zero candidateClass =
      TraceCorQQuotient.neg candidateClass :=
  Eq.trans
    (TraceCorQQuotient.sub_eq_add_neg
      TraceCorQQuotient.zero
      candidateClass)
    (TraceCorQQuotient.zero_add
      (TraceCorQQuotient.neg candidateClass))

/-- A quotient class minus itself is zero. -/
theorem TraceCorQQuotient.sub_self
    (candidateClass : TraceCorQQuotient) :
    TraceCorQQuotient.sub candidateClass candidateClass =
      TraceCorQQuotient.zero :=
  Eq.trans
    (TraceCorQQuotient.sub_eq_add_neg
      candidateClass
      candidateClass)
    (TraceCorQQuotient.add_neg_self candidateClass)

/-- Equal quotient classes have zero subtraction. -/
theorem TraceCorQQuotient.sub_eq_zero_of_eq
    (left right : TraceCorQQuotient)
    (left_eq_right : left = right) :
    TraceCorQQuotient.sub left right =
      TraceCorQQuotient.zero :=
  Eq.trans
    (congrArg
      (fun leftClass =>
        TraceCorQQuotient.sub leftClass right)
      left_eq_right)
    (TraceCorQQuotient.sub_self right)

/-- Zero subtraction detects equality of quotient classes. -/
theorem TraceCorQQuotient.eq_of_sub_eq_zero
    (left right : TraceCorQQuotient)
    (left_sub_right_eq_zero :
      TraceCorQQuotient.sub left right =
        TraceCorQQuotient.zero) :
    left = right :=
  Eq.trans
    (Eq.symm (TraceCorQQuotient.add_zero left))
    (Eq.trans
      (congrArg
        (TraceCorQQuotient.add left)
        (Eq.symm (TraceCorQQuotient.neg_add_self right)))
      (Eq.trans
        (Eq.symm
          (TraceCorQQuotient.add_assoc
            left
            (TraceCorQQuotient.neg right)
            right))
        (Eq.trans
          (congrArg
            (fun leftMinusRight =>
              TraceCorQQuotient.add leftMinusRight right)
            (Eq.trans
              (Eq.symm
                (TraceCorQQuotient.sub_eq_add_neg left right))
              left_sub_right_eq_zero))
          (TraceCorQQuotient.zero_add right))))

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

/-- Negating quotient subtraction reverses its two terms. -/
theorem TraceCorQQuotient.neg_sub
    (left right : TraceCorQQuotient) :
    TraceCorQQuotient.neg
      (TraceCorQQuotient.sub left right) =
      TraceCorQQuotient.sub right left :=
  Eq.trans
    (congrArg
      TraceCorQQuotient.neg
      (TraceCorQQuotient.sub_eq_add_neg left right))
    (Eq.trans
      (TraceCorQQuotient.neg_add left (TraceCorQQuotient.neg right))
      (Eq.trans
        (congrArg
          (TraceCorQQuotient.add (TraceCorQQuotient.neg left))
          (TraceCorQQuotient.neg_neg right))
        (Eq.trans
          (TraceCorQQuotient.add_comm
            (TraceCorQQuotient.neg left)
            right)
          (Eq.symm
            (TraceCorQQuotient.sub_eq_add_neg right left)))))

/-- Subtraction from a sum reassociates as subtraction from the right summand. -/
theorem TraceCorQQuotient.add_sub
    (left right tail : TraceCorQQuotient) :
    TraceCorQQuotient.sub
      (TraceCorQQuotient.add left right)
      tail =
      TraceCorQQuotient.add
        left
        (TraceCorQQuotient.sub right tail) :=
  Eq.trans
    (TraceCorQQuotient.sub_eq_add_neg
      (TraceCorQQuotient.add left right)
      tail)
    (Eq.trans
      (TraceCorQQuotient.add_assoc
        left
        right
        (TraceCorQQuotient.neg tail))
      (congrArg
        (TraceCorQQuotient.add left)
        (Eq.symm
          (TraceCorQQuotient.sub_eq_add_neg right tail))))

/-- Subtracting a sum reassociates as iterated subtraction. -/
theorem TraceCorQQuotient.sub_add
    (left right tail : TraceCorQQuotient) :
    TraceCorQQuotient.sub
      left
      (TraceCorQQuotient.add right tail) =
      TraceCorQQuotient.sub
        (TraceCorQQuotient.sub left right)
        tail :=
  Eq.trans
    (TraceCorQQuotient.sub_eq_add_neg
      left
      (TraceCorQQuotient.add right tail))
    (Eq.trans
      (congrArg
        (TraceCorQQuotient.add left)
        (TraceCorQQuotient.neg_add right tail))
      (Eq.trans
        (Eq.symm
          (TraceCorQQuotient.add_assoc
            left
            (TraceCorQQuotient.neg right)
            (TraceCorQQuotient.neg tail)))
        (Eq.symm
          (Eq.trans
            (TraceCorQQuotient.sub_eq_add_neg
              (TraceCorQQuotient.sub left right)
              tail)
            (congrArg
              (fun leftMinusRight =>
                TraceCorQQuotient.add
                  leftMinusRight
                  (TraceCorQQuotient.neg tail))
              (TraceCorQQuotient.sub_eq_add_neg left right))))))

/-- Subtracting a subtraction reassociates as subtraction followed by addition. -/
theorem TraceCorQQuotient.sub_sub
    (left right tail : TraceCorQQuotient) :
    TraceCorQQuotient.sub
      left
      (TraceCorQQuotient.sub right tail) =
      TraceCorQQuotient.add
        (TraceCorQQuotient.sub left right)
        tail :=
  Eq.trans
    (TraceCorQQuotient.sub_eq_add_neg
      left
      (TraceCorQQuotient.sub right tail))
    (Eq.trans
      (congrArg
        (TraceCorQQuotient.add left)
        (congrArg
          TraceCorQQuotient.neg
          (TraceCorQQuotient.sub_eq_add_neg right tail)))
      (Eq.trans
        (congrArg
          (TraceCorQQuotient.add left)
          (TraceCorQQuotient.neg_add
            right
            (TraceCorQQuotient.neg tail)))
        (Eq.trans
          (congrArg
            (fun negRightNegNegTail =>
              TraceCorQQuotient.add
                left
                (TraceCorQQuotient.add
                  (TraceCorQQuotient.neg right)
                  negRightNegNegTail))
            (TraceCorQQuotient.neg_neg tail))
          (Eq.trans
            (Eq.symm
              (TraceCorQQuotient.add_assoc
                left
                (TraceCorQQuotient.neg right)
                tail))
            (Eq.symm
              (congrArg
                (fun leftMinusRight =>
                  TraceCorQQuotient.add leftMinusRight tail)
                (TraceCorQQuotient.sub_eq_add_neg left right)))))))

/-- Scalar multiplication distributes over quotient subtraction. -/
theorem TraceCorQQuotient.smul_sub
    (coefficient : Rat)
    (left right : TraceCorQQuotient) :
    TraceCorQQuotient.smul
      coefficient
      (TraceCorQQuotient.sub left right) =
      TraceCorQQuotient.sub
        (TraceCorQQuotient.smul coefficient left)
        (TraceCorQQuotient.smul coefficient right) :=
  Eq.trans
    (congrArg
      (TraceCorQQuotient.smul coefficient)
      (TraceCorQQuotient.sub_eq_add_neg left right))
    (Eq.trans
      (TraceCorQQuotient.smul_add
        coefficient
        left
        (TraceCorQQuotient.neg right))
      (Eq.trans
        (congrArg
          (TraceCorQQuotient.add
            (TraceCorQQuotient.smul coefficient left))
          (TraceCorQQuotient.smul_neg coefficient right))
        (Eq.symm
          (TraceCorQQuotient.sub_eq_add_neg
            (TraceCorQQuotient.smul coefficient left)
            (TraceCorQQuotient.smul coefficient right))))))

/-- Composition is left-distributive over quotient subtraction. -/
theorem TraceCorQQuotient.sub_comp
    (left right tail : TraceCorQQuotient) :
    TraceCorQQuotient.comp
      (TraceCorQQuotient.sub left right)
      tail =
      TraceCorQQuotient.sub
        (TraceCorQQuotient.comp left tail)
        (TraceCorQQuotient.comp right tail) :=
  Eq.trans
    (congrArg
      (fun leftRightClass =>
        TraceCorQQuotient.comp leftRightClass tail)
      (TraceCorQQuotient.sub_eq_add_neg left right))
    (Eq.trans
      (TraceCorQQuotient.add_comp
        left
        (TraceCorQQuotient.neg right)
        tail)
      (Eq.trans
        (congrArg
          (fun rightClass =>
            TraceCorQQuotient.add
              (TraceCorQQuotient.comp left tail)
              rightClass)
          (TraceCorQQuotient.smul_comp (-1) right tail))
        (Eq.symm
          (TraceCorQQuotient.sub_eq_add_neg
            (TraceCorQQuotient.comp left tail)
            (TraceCorQQuotient.comp right tail)))))

/-- Composition is right-distributive over quotient subtraction. -/
theorem TraceCorQQuotient.comp_sub
    (left right tail : TraceCorQQuotient) :
    TraceCorQQuotient.comp
      left
      (TraceCorQQuotient.sub right tail) =
      TraceCorQQuotient.sub
        (TraceCorQQuotient.comp left right)
        (TraceCorQQuotient.comp left tail) :=
  Eq.trans
    (congrArg
      (TraceCorQQuotient.comp left)
      (TraceCorQQuotient.sub_eq_add_neg right tail))
    (Eq.trans
      (TraceCorQQuotient.comp_add
        left
        right
        (TraceCorQQuotient.neg tail))
      (Eq.trans
        (congrArg
          (fun tailClass =>
            TraceCorQQuotient.add
              (TraceCorQQuotient.comp left right)
              tailClass)
          (TraceCorQQuotient.comp_smul (-1) left tail))
        (Eq.symm
          (TraceCorQQuotient.sub_eq_add_neg
            (TraceCorQQuotient.comp left right)
            (TraceCorQQuotient.comp left tail)))))

/-- A singleton minus itself is zero. -/
theorem TraceCorQQuotient.singleton_sub_self
    (coefficient : Rat)
    (generator : TraceCorQGenerator) :
    TraceCorQQuotient.sub
      (TraceCorQQuotient.singleton coefficient generator)
      (TraceCorQQuotient.singleton coefficient generator) =
      TraceCorQQuotient.zero :=
  Eq.trans
    (TraceCorQQuotient.sub_eq_add_neg
      (TraceCorQQuotient.singleton coefficient generator)
      (TraceCorQQuotient.singleton coefficient generator))
    (Eq.trans
      (congrArg
        (TraceCorQQuotient.add
          (TraceCorQQuotient.singleton coefficient generator))
        (TraceCorQQuotient.smul_singleton
          (-1)
          coefficient
          generator))
      (Eq.trans
        (congrArg
          (fun negCoefficient =>
            TraceCorQQuotient.add
              (TraceCorQQuotient.singleton coefficient generator)
              (TraceCorQQuotient.singleton negCoefficient generator))
          (neg_one_mul coefficient))
        (TraceCorQQuotient.singleton_add_neg_singleton
          coefficient
          generator)))

end AnalyticMotives
end LFunctions
end Boundary
