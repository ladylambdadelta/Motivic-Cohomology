import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Quotient.Operations.Neg.Laws.Distribution.Owner

/-!
# Derived negation laws for quotient trace correspondences

This aggregate owns negation laws downstream from the base additive inverse
and binary negation-distribution theorems.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Derived negation-law aggregate: negating zero gives zero. -/
theorem TraceCorQQuotient.neg_lawsDerived_neg_zero :
    TraceCorQQuotient.neg TraceCorQQuotient.zero =
      TraceCorQQuotient.zero :=
  TraceCorQQuotient.neg_zero

/-- Derived negation-law aggregate: negation distributes over binary sums. -/
theorem TraceCorQQuotient.neg_lawsDerived_neg_add
    (left right : TraceCorQQuotient) :
    TraceCorQQuotient.neg
      (TraceCorQQuotient.add left right) =
      TraceCorQQuotient.add
        (TraceCorQQuotient.neg left)
        (TraceCorQQuotient.neg right) :=
  TraceCorQQuotient.neg_add left right

/-- Derived negation-law aggregate: quotient negation is involutive. -/
theorem TraceCorQQuotient.neg_lawsDerived_neg_neg
    (candidateClass : TraceCorQQuotient) :
    TraceCorQQuotient.neg
      (TraceCorQQuotient.neg candidateClass) =
      candidateClass :=
  TraceCorQQuotient.neg_neg candidateClass

/-- Derived negation-law aggregate: negating a singleton negates its coefficient. -/
theorem TraceCorQQuotient.neg_lawsDerived_neg_singleton_eq_singleton_neg
    (coefficient : Rat)
    (generator : TraceCorQGenerator) :
    TraceCorQQuotient.neg
      (TraceCorQQuotient.singleton coefficient generator) =
      TraceCorQQuotient.singleton (-coefficient) generator :=
  TraceCorQQuotient.neg_singleton_eq_singleton_neg
    coefficient
    generator

/-- Derived negation-law aggregate: a negative singleton cancels on the left. -/
theorem TraceCorQQuotient.neg_lawsDerived_neg_singleton_add_singleton
    (coefficient : Rat)
    (generator : TraceCorQGenerator) :
    TraceCorQQuotient.add
      (TraceCorQQuotient.singleton (-coefficient) generator)
      (TraceCorQQuotient.singleton coefficient generator) =
      TraceCorQQuotient.zero :=
  TraceCorQQuotient.neg_singleton_add_singleton
    coefficient
    generator

/-- Derived negation-law aggregate: a negative singleton cancels on the right. -/
theorem TraceCorQQuotient.neg_lawsDerived_singleton_add_neg_singleton
    (coefficient : Rat)
    (generator : TraceCorQGenerator) :
    TraceCorQQuotient.add
      (TraceCorQQuotient.singleton coefficient generator)
      (TraceCorQQuotient.singleton (-coefficient) generator) =
      TraceCorQQuotient.zero :=
  TraceCorQQuotient.singleton_add_neg_singleton
    coefficient
    generator

/-- Derived negation-law aggregate: every class has a left additive inverse. -/
theorem TraceCorQQuotient.neg_lawsDerived_neg_add_self
    (candidateClass : TraceCorQQuotient) :
    TraceCorQQuotient.add
      (TraceCorQQuotient.neg candidateClass)
      candidateClass =
      TraceCorQQuotient.zero :=
  TraceCorQQuotient.neg_add_self candidateClass

/-- Derived negation-law aggregate: every class has a right additive inverse. -/
theorem TraceCorQQuotient.neg_lawsDerived_add_neg_self
    (candidateClass : TraceCorQQuotient) :
    TraceCorQQuotient.add
      candidateClass
      (TraceCorQQuotient.neg candidateClass) =
      TraceCorQQuotient.zero :=
  TraceCorQQuotient.add_neg_self candidateClass

/-- Derived negation-law aggregate: quotient addition cancels a common left summand. -/
theorem TraceCorQQuotient.neg_lawsDerived_add_left_cancel
    (left right tail : TraceCorQQuotient)
    (left_right_eq_left_tail :
      TraceCorQQuotient.add left right =
        TraceCorQQuotient.add left tail) :
    right = tail :=
  TraceCorQQuotient.add_left_cancel
    left
    right
    tail
    left_right_eq_left_tail

/-- Derived negation-law aggregate: quotient addition cancels a common right summand. -/
theorem TraceCorQQuotient.neg_lawsDerived_add_right_cancel
    (left right tail : TraceCorQQuotient)
    (left_tail_eq_right_tail :
      TraceCorQQuotient.add left tail =
        TraceCorQQuotient.add right tail) :
    left = right :=
  TraceCorQQuotient.add_right_cancel
    left
    right
    tail
    left_tail_eq_right_tail

/-- Derived negation-law aggregate: negation distributes over left-associated triples. -/
theorem TraceCorQQuotient.neg_lawsDerived_neg_add_three_left
    (first second third : TraceCorQQuotient) :
    TraceCorQQuotient.neg
      (TraceCorQQuotient.add
        (TraceCorQQuotient.add first second)
        third) =
      TraceCorQQuotient.add
        (TraceCorQQuotient.neg first)
        (TraceCorQQuotient.add
          (TraceCorQQuotient.neg second)
          (TraceCorQQuotient.neg third)) :=
  TraceCorQQuotient.neg_add_three_left
    first
    second
    third

/-- Derived negation-law aggregate: negation distributes over right-associated triples. -/
theorem TraceCorQQuotient.neg_lawsDerived_neg_add_three_right
    (first second third : TraceCorQQuotient) :
    TraceCorQQuotient.neg
      (TraceCorQQuotient.add
        first
        (TraceCorQQuotient.add second third)) =
      TraceCorQQuotient.add
        (TraceCorQQuotient.neg first)
        (TraceCorQQuotient.add
          (TraceCorQQuotient.neg second)
          (TraceCorQQuotient.neg third)) :=
  TraceCorQQuotient.neg_add_three_right
    first
    second
    third

end AnalyticMotives
end LFunctions
end Boundary
