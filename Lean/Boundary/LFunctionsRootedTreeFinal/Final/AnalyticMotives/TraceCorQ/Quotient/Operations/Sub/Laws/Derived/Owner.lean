import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Quotient.Operations.Sub.Laws.Cancellation.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Quotient.Operations.Sub.Laws.Rearrangement.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Quotient.Operations.Sub.Laws.Distribution.Owner

/-!
# Derived quotient subtraction laws

This file re-exports derived quotient subtraction solvers and rearrangement
laws built from the base subtraction law owner.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Derived subtraction-law aggregate: subtracting zero on the right is identity. -/
theorem TraceCorQQuotient.sub_lawsDerived_sub_zero
    (candidateClass : TraceCorQQuotient) :
    TraceCorQQuotient.sub candidateClass TraceCorQQuotient.zero =
      candidateClass :=
  TraceCorQQuotient.sub_zero candidateClass

/-- Derived subtraction-law aggregate: zero minus a class is its negative. -/
theorem TraceCorQQuotient.sub_lawsDerived_zero_sub
    (candidateClass : TraceCorQQuotient) :
    TraceCorQQuotient.sub TraceCorQQuotient.zero candidateClass =
      TraceCorQQuotient.neg candidateClass :=
  TraceCorQQuotient.zero_sub candidateClass

/-- Derived subtraction-law aggregate: a class minus itself is zero. -/
theorem TraceCorQQuotient.sub_lawsDerived_sub_self
    (candidateClass : TraceCorQQuotient) :
    TraceCorQQuotient.sub candidateClass candidateClass =
      TraceCorQQuotient.zero :=
  TraceCorQQuotient.sub_self candidateClass

/-- Derived subtraction-law aggregate: zero subtraction follows from equality. -/
theorem TraceCorQQuotient.sub_lawsDerived_sub_eq_zero_of_eq
    (left right : TraceCorQQuotient)
    (left_eq_right : left = right) :
    TraceCorQQuotient.sub left right =
      TraceCorQQuotient.zero :=
  TraceCorQQuotient.sub_eq_zero_of_eq
    left
    right
    left_eq_right

/-- Derived subtraction-law aggregate: zero subtraction detects equality. -/
theorem TraceCorQQuotient.sub_lawsDerived_eq_of_sub_eq_zero
    (left right : TraceCorQQuotient)
    (left_sub_right_eq_zero :
      TraceCorQQuotient.sub left right =
        TraceCorQQuotient.zero) :
    left = right :=
  TraceCorQQuotient.eq_of_sub_eq_zero
    left
    right
    left_sub_right_eq_zero

/-- Derived subtraction-law aggregate: negating subtraction reverses its terms. -/
theorem TraceCorQQuotient.sub_lawsDerived_neg_sub
    (left right : TraceCorQQuotient) :
    TraceCorQQuotient.neg
      (TraceCorQQuotient.sub left right) =
      TraceCorQQuotient.sub right left :=
  TraceCorQQuotient.neg_sub left right

/-- Derived subtraction-law aggregate: subtraction from a sum pushes to the right. -/
theorem TraceCorQQuotient.sub_lawsDerived_add_sub
    (left right tail : TraceCorQQuotient) :
    TraceCorQQuotient.sub
      (TraceCorQQuotient.add left right)
      tail =
      TraceCorQQuotient.add
        left
        (TraceCorQQuotient.sub right tail) :=
  TraceCorQQuotient.add_sub left right tail

/-- Derived subtraction-law aggregate: subtracting a sum is iterated subtraction. -/
theorem TraceCorQQuotient.sub_lawsDerived_sub_add
    (left right tail : TraceCorQQuotient) :
    TraceCorQQuotient.sub
      left
      (TraceCorQQuotient.add right tail) =
      TraceCorQQuotient.sub
        (TraceCorQQuotient.sub left right)
        tail :=
  TraceCorQQuotient.sub_add left right tail

/-- Derived subtraction-law aggregate: subtracting a subtraction adds the tail. -/
theorem TraceCorQQuotient.sub_lawsDerived_sub_sub
    (left right tail : TraceCorQQuotient) :
    TraceCorQQuotient.sub
      left
      (TraceCorQQuotient.sub right tail) =
      TraceCorQQuotient.add
        (TraceCorQQuotient.sub left right)
        tail :=
  TraceCorQQuotient.sub_sub left right tail

/-- Derived subtraction-law aggregate: scalar multiplication distributes over subtraction. -/
theorem TraceCorQQuotient.sub_lawsDerived_smul_sub
    (coefficient : Rat)
    (left right : TraceCorQQuotient) :
    TraceCorQQuotient.smul
      coefficient
      (TraceCorQQuotient.sub left right) =
      TraceCorQQuotient.sub
        (TraceCorQQuotient.smul coefficient left)
        (TraceCorQQuotient.smul coefficient right) :=
  TraceCorQQuotient.smul_sub coefficient left right

/-- Derived subtraction-law aggregate: composition is left-distributive over subtraction. -/
theorem TraceCorQQuotient.sub_lawsDerived_sub_comp
    (left right tail : TraceCorQQuotient) :
    TraceCorQQuotient.comp
      (TraceCorQQuotient.sub left right)
      tail =
      TraceCorQQuotient.sub
        (TraceCorQQuotient.comp left tail)
        (TraceCorQQuotient.comp right tail) :=
  TraceCorQQuotient.sub_comp left right tail

/-- Derived subtraction-law aggregate: composition is right-distributive over subtraction. -/
theorem TraceCorQQuotient.sub_lawsDerived_comp_sub
    (left right tail : TraceCorQQuotient) :
    TraceCorQQuotient.comp
      left
      (TraceCorQQuotient.sub right tail) =
      TraceCorQQuotient.sub
        (TraceCorQQuotient.comp left right)
        (TraceCorQQuotient.comp left tail) :=
  TraceCorQQuotient.comp_sub left right tail

/-- Derived subtraction-law aggregate: a singleton minus itself is zero. -/
theorem TraceCorQQuotient.sub_lawsDerived_singleton_sub_self
    (coefficient : Rat)
    (generator : TraceCorQGenerator) :
    TraceCorQQuotient.sub
      (TraceCorQQuotient.singleton coefficient generator)
      (TraceCorQQuotient.singleton coefficient generator) =
      TraceCorQQuotient.zero :=
  TraceCorQQuotient.singleton_sub_self coefficient generator

/-- Derived subtraction-law aggregate: solve for the right summand of a sum. -/
theorem TraceCorQQuotient.sub_lawsDerived_sub_left_summand_eq_right
    (left right tail : TraceCorQQuotient)
    (left_eq_right_add_tail :
      left = TraceCorQQuotient.add right tail) :
    TraceCorQQuotient.sub left right = tail :=
  TraceCorQQuotient.sub_left_summand_eq_right
    left
    right
    tail
    left_eq_right_add_tail

/-- Derived subtraction-law aggregate: solve for the left summand of a sum. -/
theorem TraceCorQQuotient.sub_lawsDerived_sub_right_summand_eq_left
    (left right tail : TraceCorQQuotient)
    (left_eq_right_add_tail :
      left = TraceCorQQuotient.add right tail) :
    TraceCorQQuotient.sub left tail = right :=
  TraceCorQQuotient.sub_right_summand_eq_left
    left
    right
    tail
    left_eq_right_add_tail

/-- Derived subtraction-law aggregate: solve subtraction from equality after adding back. -/
theorem TraceCorQQuotient.sub_lawsDerived_sub_eq_of_add_eq
    (left right tail : TraceCorQQuotient)
    (left_eq_tail_add_right :
      left = TraceCorQQuotient.add tail right) :
    TraceCorQQuotient.sub left right = tail :=
  TraceCorQQuotient.sub_eq_of_add_eq
    left
    right
    tail
    left_eq_tail_add_right

/-- Derived subtraction-law aggregate: reassociate a sum whose left summand is a subtraction. -/
theorem TraceCorQQuotient.sub_lawsDerived_sub_add_reassociate
    (left right tail : TraceCorQQuotient) :
    TraceCorQQuotient.add
      (TraceCorQQuotient.sub left right)
      tail =
      TraceCorQQuotient.sub
        (TraceCorQQuotient.add left tail)
        right :=
  TraceCorQQuotient.sub_add_reassociate
    left
    right
    tail

/-- Derived subtraction-law aggregate: reassociate a sum whose right summand is a subtraction. -/
theorem TraceCorQQuotient.sub_lawsDerived_add_sub_reassociate
    (left right tail : TraceCorQQuotient) :
    TraceCorQQuotient.add
      left
      (TraceCorQQuotient.sub right tail) =
      TraceCorQQuotient.sub
        (TraceCorQQuotient.add left right)
        tail :=
  TraceCorQQuotient.add_sub_reassociate
    left
    right
    tail

/-- Derived subtraction-law aggregate: push subtraction through a left-associated triple. -/
theorem TraceCorQQuotient.sub_lawsDerived_add_add_sub
    (first second third tail : TraceCorQQuotient) :
    TraceCorQQuotient.sub
      (TraceCorQQuotient.add
        (TraceCorQQuotient.add first second)
        third)
      tail =
      TraceCorQQuotient.add
        first
        (TraceCorQQuotient.add
          second
          (TraceCorQQuotient.sub third tail)) :=
  TraceCorQQuotient.add_add_sub
    first
    second
    third
    tail

/-- Derived subtraction-law aggregate: push subtraction through a right-associated triple. -/
theorem TraceCorQQuotient.sub_lawsDerived_add_add_sub_right
    (first second third tail : TraceCorQQuotient) :
    TraceCorQQuotient.sub
      (TraceCorQQuotient.add
        first
        (TraceCorQQuotient.add second third))
      tail =
      TraceCorQQuotient.add
        first
        (TraceCorQQuotient.add
          second
          (TraceCorQQuotient.sub third tail)) :=
  TraceCorQQuotient.add_add_sub_right
    first
    second
    third
    tail

end AnalyticMotives
end LFunctions
end Boundary
