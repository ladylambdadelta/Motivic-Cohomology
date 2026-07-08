import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Quotient.Operations.Comp.Laws.Distribution.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Quotient.Operations.Comp.Laws.SmulDistribution.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Quotient.Operations.Comp.Laws.NegDistribution.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Quotient.Operations.Comp.Laws.SubDistribution.Owner

/-!
# Derived quotient composition laws

This aggregate owns composition laws downstream from the base quotient
composition laws.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Derived composition-law aggregate: zero composed on the left is zero. -/
theorem TraceCorQQuotient.comp_lawsDerived_zero_comp
    (candidateClass : TraceCorQQuotient) :
    TraceCorQQuotient.comp
      TraceCorQQuotient.zero
      candidateClass =
      TraceCorQQuotient.zero :=
  TraceCorQQuotient.zero_comp candidateClass

/-- Derived composition-law aggregate: zero composed on the right is zero. -/
theorem TraceCorQQuotient.comp_lawsDerived_comp_zero
    (candidateClass : TraceCorQQuotient) :
    TraceCorQQuotient.comp
      candidateClass
      TraceCorQQuotient.zero =
      TraceCorQQuotient.zero :=
  TraceCorQQuotient.comp_zero candidateClass

/-- Derived composition-law aggregate: scaling the left input scales composition. -/
theorem TraceCorQQuotient.comp_lawsDerived_smul_comp
    (coefficient : Rat)
    (left right : TraceCorQQuotient) :
    TraceCorQQuotient.comp
      (TraceCorQQuotient.smul coefficient left)
      right =
      TraceCorQQuotient.smul
        coefficient
        (TraceCorQQuotient.comp left right) :=
  TraceCorQQuotient.smul_comp coefficient left right

/-- Derived composition-law aggregate: scaling the right input scales composition. -/
theorem TraceCorQQuotient.comp_lawsDerived_comp_smul
    (coefficient : Rat)
    (left right : TraceCorQQuotient) :
    TraceCorQQuotient.comp
      left
      (TraceCorQQuotient.smul coefficient right) =
      TraceCorQQuotient.smul
        coefficient
        (TraceCorQQuotient.comp left right) :=
  TraceCorQQuotient.comp_smul coefficient left right

/-- Derived composition-law aggregate: negating the left input negates composition. -/
theorem TraceCorQQuotient.comp_lawsDerived_neg_comp
    (left right : TraceCorQQuotient) :
    TraceCorQQuotient.comp
      (TraceCorQQuotient.neg left)
      right =
      TraceCorQQuotient.neg
        (TraceCorQQuotient.comp left right) :=
  TraceCorQQuotient.neg_comp left right

/-- Derived composition-law aggregate: negating the right input negates composition. -/
theorem TraceCorQQuotient.comp_lawsDerived_comp_neg
    (left right : TraceCorQQuotient) :
    TraceCorQQuotient.comp
      left
      (TraceCorQQuotient.neg right) =
      TraceCorQQuotient.neg
        (TraceCorQQuotient.comp left right) :=
  TraceCorQQuotient.comp_neg left right

/-- Derived composition-law aggregate: composition is left-distributive over addition. -/
theorem TraceCorQQuotient.comp_lawsDerived_add_comp
    (left right tail : TraceCorQQuotient) :
    TraceCorQQuotient.comp
      (TraceCorQQuotient.add left right)
      tail =
      TraceCorQQuotient.add
        (TraceCorQQuotient.comp left tail)
        (TraceCorQQuotient.comp right tail) :=
  TraceCorQQuotient.add_comp left right tail

/-- Derived composition-law aggregate: composition is right-distributive over addition. -/
theorem TraceCorQQuotient.comp_lawsDerived_comp_add
    (left right tail : TraceCorQQuotient) :
    TraceCorQQuotient.comp
      left
      (TraceCorQQuotient.add right tail) =
      TraceCorQQuotient.add
        (TraceCorQQuotient.comp left right)
        (TraceCorQQuotient.comp left tail) :=
  TraceCorQQuotient.comp_add left right tail

/-- Derived composition-law aggregate: composition is left-distributive over subtraction. -/
theorem TraceCorQQuotient.comp_lawsDerived_sub_comp
    (left right tail : TraceCorQQuotient) :
    TraceCorQQuotient.comp
      (TraceCorQQuotient.sub left right)
      tail =
      TraceCorQQuotient.sub
        (TraceCorQQuotient.comp left tail)
        (TraceCorQQuotient.comp right tail) :=
  TraceCorQQuotient.sub_comp left right tail

/-- Derived composition-law aggregate: composition is right-distributive over subtraction. -/
theorem TraceCorQQuotient.comp_lawsDerived_comp_sub
    (left right tail : TraceCorQQuotient) :
    TraceCorQQuotient.comp
      left
      (TraceCorQQuotient.sub right tail) =
      TraceCorQQuotient.sub
        (TraceCorQQuotient.comp left right)
        (TraceCorQQuotient.comp left tail) :=
  TraceCorQQuotient.comp_sub left right tail

/-- Derived composition-law aggregate: compose a left-associated source triple. -/
theorem TraceCorQQuotient.comp_lawsDerived_add_add_comp
    (first second third tail : TraceCorQQuotient) :
    TraceCorQQuotient.comp
      (TraceCorQQuotient.add
        (TraceCorQQuotient.add first second)
        third)
      tail =
      TraceCorQQuotient.add
        (TraceCorQQuotient.comp first tail)
        (TraceCorQQuotient.add
          (TraceCorQQuotient.comp second tail)
          (TraceCorQQuotient.comp third tail)) :=
  TraceCorQQuotient.add_add_comp
    first
    second
    third
    tail

/-- Derived composition-law aggregate: compose into a left-associated target triple. -/
theorem TraceCorQQuotient.comp_lawsDerived_comp_add_add
    (head first second third : TraceCorQQuotient) :
    TraceCorQQuotient.comp
      head
      (TraceCorQQuotient.add
        (TraceCorQQuotient.add first second)
        third) =
      TraceCorQQuotient.add
        (TraceCorQQuotient.comp head first)
        (TraceCorQQuotient.add
          (TraceCorQQuotient.comp head second)
          (TraceCorQQuotient.comp head third)) :=
  TraceCorQQuotient.comp_add_add
    head
    first
    second
    third

/-- Derived composition-law aggregate: scale a composite with a left-associated source triple. -/
theorem TraceCorQQuotient.comp_lawsDerived_smul_add_add_comp
    (coefficient : Rat)
    (first second third post : TraceCorQQuotient) :
    TraceCorQQuotient.smul
      coefficient
      (TraceCorQQuotient.comp
        (TraceCorQQuotient.add
          (TraceCorQQuotient.add first second)
          third)
        post) =
      TraceCorQQuotient.add
        (TraceCorQQuotient.comp (TraceCorQQuotient.smul coefficient first) post)
        (TraceCorQQuotient.add
          (TraceCorQQuotient.comp (TraceCorQQuotient.smul coefficient second) post)
          (TraceCorQQuotient.comp (TraceCorQQuotient.smul coefficient third) post)) :=
  TraceCorQQuotient.smul_add_add_comp
    coefficient
    first
    second
    third
    post

/-- Derived composition-law aggregate: negate a composite with a left-associated source triple. -/
theorem TraceCorQQuotient.comp_lawsDerived_neg_add_add_comp
    (first second third post : TraceCorQQuotient) :
    TraceCorQQuotient.neg
      (TraceCorQQuotient.comp
        (TraceCorQQuotient.add
          (TraceCorQQuotient.add first second)
          third)
        post) =
      TraceCorQQuotient.add
        (TraceCorQQuotient.comp (TraceCorQQuotient.neg first) post)
        (TraceCorQQuotient.add
          (TraceCorQQuotient.comp (TraceCorQQuotient.neg second) post)
          (TraceCorQQuotient.comp (TraceCorQQuotient.neg third) post)) :=
  TraceCorQQuotient.neg_add_add_comp
    first
    second
    third
    post

end AnalyticMotives
end LFunctions
end Boundary
