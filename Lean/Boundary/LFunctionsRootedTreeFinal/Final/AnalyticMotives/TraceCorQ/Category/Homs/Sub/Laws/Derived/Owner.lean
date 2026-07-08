import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Category.Homs.Sub.Laws.Cancellation.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Category.Homs.Sub.Laws.Rearrangement.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Category.Homs.Sub.Laws.Distribution.Owner

/-!
# Derived typed hom subtraction laws

This file re-exports derived typed hom subtraction solvers and rearrangement
laws built from the base subtraction law owner.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Derived typed-hom subtraction aggregate: subtracting zero is identity. -/
theorem TraceCorQHom.sub_lawsDerived_sub_zero
    {source target : TraceCorQObject}
    (hom : TraceCorQHom source target) :
    TraceCorQHom.sub hom (TraceCorQHom.zero source target) =
      hom :=
  TraceCorQHom.sub_zero
    hom

/-- Derived typed-hom subtraction aggregate: zero minus a hom is its negative. -/
theorem TraceCorQHom.sub_lawsDerived_zero_sub
    {source target : TraceCorQObject}
    (hom : TraceCorQHom source target) :
    TraceCorQHom.sub (TraceCorQHom.zero source target) hom =
      TraceCorQHom.neg hom :=
  TraceCorQHom.zero_sub
    hom

/-- Derived typed-hom subtraction aggregate: a hom minus itself is zero. -/
theorem TraceCorQHom.sub_lawsDerived_sub_self
    {source target : TraceCorQObject}
    (hom : TraceCorQHom source target) :
    TraceCorQHom.sub hom hom =
      TraceCorQHom.zero source target :=
  TraceCorQHom.sub_self
    hom

/-- Derived typed-hom subtraction aggregate: zero subtraction follows from equality. -/
theorem TraceCorQHom.sub_lawsDerived_sub_eq_zero_of_eq
    {source target : TraceCorQObject}
    (left right : TraceCorQHom source target)
    (left_eq_right : left = right) :
    TraceCorQHom.sub left right =
      TraceCorQHom.zero source target :=
  TraceCorQHom.sub_eq_zero_of_eq
    left
    right
    left_eq_right

/-- Derived typed-hom subtraction aggregate: zero subtraction detects equality. -/
theorem TraceCorQHom.sub_lawsDerived_eq_of_sub_eq_zero
    {source target : TraceCorQObject}
    (left right : TraceCorQHom source target)
    (left_sub_right_eq_zero :
      TraceCorQHom.sub left right =
        TraceCorQHom.zero source target) :
    left = right :=
  TraceCorQHom.eq_of_sub_eq_zero
    left
    right
    left_sub_right_eq_zero

/-- Derived typed-hom subtraction aggregate: negating a subtraction reverses terms. -/
theorem TraceCorQHom.sub_lawsDerived_neg_sub
    {source target : TraceCorQObject}
    (left right : TraceCorQHom source target) :
    TraceCorQHom.neg
      (TraceCorQHom.sub left right) =
      TraceCorQHom.sub right left :=
  TraceCorQHom.neg_sub
    left
    right

/-- Derived typed-hom subtraction aggregate: subtraction from a sum pushes right. -/
theorem TraceCorQHom.sub_lawsDerived_add_sub
    {source target : TraceCorQObject}
    (left right tail : TraceCorQHom source target) :
    TraceCorQHom.sub
      (TraceCorQHom.add left right)
      tail =
      TraceCorQHom.add
        left
        (TraceCorQHom.sub right tail) :=
  TraceCorQHom.add_sub
    left
    right
    tail

/-- Derived typed-hom subtraction aggregate: subtracting a sum is iterated subtraction. -/
theorem TraceCorQHom.sub_lawsDerived_sub_add
    {source target : TraceCorQObject}
    (left right tail : TraceCorQHom source target) :
    TraceCorQHom.sub
      left
      (TraceCorQHom.add right tail) =
      TraceCorQHom.sub
        (TraceCorQHom.sub left right)
        tail :=
  TraceCorQHom.sub_add
    left
    right
    tail

/-- Derived typed-hom subtraction aggregate: subtracting a subtraction adds the tail. -/
theorem TraceCorQHom.sub_lawsDerived_sub_sub
    {source target : TraceCorQObject}
    (left right tail : TraceCorQHom source target) :
    TraceCorQHom.sub
      left
      (TraceCorQHom.sub right tail) =
      TraceCorQHom.add
        (TraceCorQHom.sub left right)
        tail :=
  TraceCorQHom.sub_sub
    left
    right
    tail

/-- Derived typed-hom subtraction aggregate: scalar multiplication distributes over subtraction. -/
theorem TraceCorQHom.sub_lawsDerived_smul_sub
    {source target : TraceCorQObject}
    (coefficient : Rat)
    (left right : TraceCorQHom source target) :
    TraceCorQHom.smul
      coefficient
      (TraceCorQHom.sub left right) =
      TraceCorQHom.sub
        (TraceCorQHom.smul coefficient left)
        (TraceCorQHom.smul coefficient right) :=
  TraceCorQHom.smul_sub
    coefficient
    left
    right

/-- Derived typed-hom subtraction aggregate: solve for a right summand. -/
theorem TraceCorQHom.sub_lawsDerived_sub_left_summand_eq_right
    {source target : TraceCorQObject}
    (left right tail : TraceCorQHom source target)
    (left_eq_right_add_tail :
      left = TraceCorQHom.add right tail) :
    TraceCorQHom.sub left right = tail :=
  TraceCorQHom.sub_left_summand_eq_right
    left
    right
    tail
    left_eq_right_add_tail

/-- Derived typed-hom subtraction aggregate: solve for a left summand. -/
theorem TraceCorQHom.sub_lawsDerived_sub_right_summand_eq_left
    {source target : TraceCorQObject}
    (left right tail : TraceCorQHom source target)
    (left_eq_right_add_tail :
      left = TraceCorQHom.add right tail) :
    TraceCorQHom.sub left tail = right :=
  TraceCorQHom.sub_right_summand_eq_left
    left
    right
    tail
    left_eq_right_add_tail

/-- Derived typed-hom subtraction aggregate: solve subtraction from an add-back equality. -/
theorem TraceCorQHom.sub_lawsDerived_sub_eq_of_add_eq
    {source target : TraceCorQObject}
    (left right tail : TraceCorQHom source target)
    (left_eq_tail_add_right :
      left = TraceCorQHom.add tail right) :
    TraceCorQHom.sub left right = tail :=
  TraceCorQHom.sub_eq_of_add_eq
    left
    right
    tail
    left_eq_tail_add_right

/-- Derived typed-hom subtraction aggregate: reassociate a left subtraction summand. -/
theorem TraceCorQHom.sub_lawsDerived_sub_add_reassociate
    {source target : TraceCorQObject}
    (left right tail : TraceCorQHom source target) :
    TraceCorQHom.add
      (TraceCorQHom.sub left right)
      tail =
      TraceCorQHom.sub
        (TraceCorQHom.add left tail)
        right :=
  TraceCorQHom.sub_add_reassociate
    left
    right
    tail

/-- Derived typed-hom subtraction aggregate: push subtraction through a left-associated triple. -/
theorem TraceCorQHom.sub_lawsDerived_add_add_sub
    {source target : TraceCorQObject}
    (first second third tail : TraceCorQHom source target) :
    TraceCorQHom.sub
      (TraceCorQHom.add
        (TraceCorQHom.add first second)
        third)
      tail =
      TraceCorQHom.add
        first
        (TraceCorQHom.add
          second
          (TraceCorQHom.sub third tail)) :=
  TraceCorQHom.add_add_sub
    first
    second
    third
    tail

end AnalyticMotives
end LFunctions
end Boundary
