import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Quotient.Operations.Neg.Laws.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Quotient.Operations.Comp.Laws.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Quotient.Operations.Sub.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Quotient.Operations.Sub.Laws.PrimitiveCancellation.Owner

/-!
# Subtraction laws for quotient trace correspondences

The basic and primitive-cancellation children own primitive subtraction and
cancellation laws.  This file keeps the remaining additive rearrangement and
distributive laws consumed by the downstream subtraction-law children.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

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
            (TraceCorQQuotient.smul coefficient right)))))

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
