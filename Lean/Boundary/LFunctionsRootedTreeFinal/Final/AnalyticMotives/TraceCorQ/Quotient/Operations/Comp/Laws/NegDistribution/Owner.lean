import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Quotient.Operations.Comp.Laws.SmulDistribution.Owner

/-!
# Sign distribution through longer quotient composites

This file owns negation normal forms for quotient composites whose source or
target input is a longer additive sum.  These are the `-1` specializations of
the scalar distribution-through-composition theorems.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Negate a quotient composite whose source input is a left-associated three-summand sum. -/
theorem TraceCorQQuotient.neg_add_add_comp
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
  TraceCorQQuotient.smul_add_add_comp
    (-1)
    first
    second
    third
    post

/-- Negate a quotient composite whose source input is a right-associated three-summand sum. -/
theorem TraceCorQQuotient.neg_add_add_comp_right
    (first second third post : TraceCorQQuotient) :
    TraceCorQQuotient.neg
      (TraceCorQQuotient.comp
        (TraceCorQQuotient.add
          first
          (TraceCorQQuotient.add second third))
        post) =
      TraceCorQQuotient.add
        (TraceCorQQuotient.comp (TraceCorQQuotient.neg first) post)
        (TraceCorQQuotient.add
          (TraceCorQQuotient.comp (TraceCorQQuotient.neg second) post)
          (TraceCorQQuotient.comp (TraceCorQQuotient.neg third) post)) :=
  TraceCorQQuotient.smul_add_add_comp_right
    (-1)
    first
    second
    third
    post

/-- Negate a quotient composite whose source input is a left-associated four-summand sum. -/
theorem TraceCorQQuotient.neg_add_add_add_comp
    (first second third fourth post : TraceCorQQuotient) :
    TraceCorQQuotient.neg
      (TraceCorQQuotient.comp
        (TraceCorQQuotient.add
          (TraceCorQQuotient.add
            (TraceCorQQuotient.add first second)
            third)
          fourth)
        post) =
      TraceCorQQuotient.add
        (TraceCorQQuotient.comp (TraceCorQQuotient.neg first) post)
        (TraceCorQQuotient.add
          (TraceCorQQuotient.comp (TraceCorQQuotient.neg second) post)
          (TraceCorQQuotient.add
            (TraceCorQQuotient.comp (TraceCorQQuotient.neg third) post)
            (TraceCorQQuotient.comp (TraceCorQQuotient.neg fourth) post))) :=
  TraceCorQQuotient.smul_add_add_add_comp
    (-1)
    first
    second
    third
    fourth
    post

/-- Negate a quotient composite whose source input is a right-associated four-summand sum. -/
theorem TraceCorQQuotient.neg_add_add_add_comp_right
    (first second third fourth post : TraceCorQQuotient) :
    TraceCorQQuotient.neg
      (TraceCorQQuotient.comp
        (TraceCorQQuotient.add
          first
          (TraceCorQQuotient.add
            second
            (TraceCorQQuotient.add third fourth)))
        post) =
      TraceCorQQuotient.add
        (TraceCorQQuotient.comp (TraceCorQQuotient.neg first) post)
        (TraceCorQQuotient.add
          (TraceCorQQuotient.comp (TraceCorQQuotient.neg second) post)
          (TraceCorQQuotient.add
            (TraceCorQQuotient.comp (TraceCorQQuotient.neg third) post)
            (TraceCorQQuotient.comp (TraceCorQQuotient.neg fourth) post))) :=
  TraceCorQQuotient.smul_add_add_add_comp_right
    (-1)
    first
    second
    third
    fourth
    post

/-- Negate a quotient composite whose target input is a left-associated three-summand sum. -/
theorem TraceCorQQuotient.neg_comp_add_add
    (pre first second third : TraceCorQQuotient) :
    TraceCorQQuotient.neg
      (TraceCorQQuotient.comp
        pre
        (TraceCorQQuotient.add
          (TraceCorQQuotient.add first second)
          third)) =
      TraceCorQQuotient.add
        (TraceCorQQuotient.comp pre (TraceCorQQuotient.neg first))
        (TraceCorQQuotient.add
          (TraceCorQQuotient.comp pre (TraceCorQQuotient.neg second))
          (TraceCorQQuotient.comp pre (TraceCorQQuotient.neg third))) :=
  TraceCorQQuotient.smul_comp_add_add
    (-1)
    pre
    first
    second
    third

/-- Negate a quotient composite whose target input is a right-associated three-summand sum. -/
theorem TraceCorQQuotient.neg_comp_add_add_right
    (pre first second third : TraceCorQQuotient) :
    TraceCorQQuotient.neg
      (TraceCorQQuotient.comp
        pre
        (TraceCorQQuotient.add
          first
          (TraceCorQQuotient.add second third))) =
      TraceCorQQuotient.add
        (TraceCorQQuotient.comp pre (TraceCorQQuotient.neg first))
        (TraceCorQQuotient.add
          (TraceCorQQuotient.comp pre (TraceCorQQuotient.neg second))
          (TraceCorQQuotient.comp pre (TraceCorQQuotient.neg third))) :=
  TraceCorQQuotient.smul_comp_add_add_right
    (-1)
    pre
    first
    second
    third

/-- Negate a quotient composite whose target input is a left-associated four-summand sum. -/
theorem TraceCorQQuotient.neg_comp_add_add_add
    (pre first second third fourth : TraceCorQQuotient) :
    TraceCorQQuotient.neg
      (TraceCorQQuotient.comp
        pre
        (TraceCorQQuotient.add
          (TraceCorQQuotient.add
            (TraceCorQQuotient.add first second)
            third)
          fourth)) =
      TraceCorQQuotient.add
        (TraceCorQQuotient.comp pre (TraceCorQQuotient.neg first))
        (TraceCorQQuotient.add
          (TraceCorQQuotient.comp pre (TraceCorQQuotient.neg second))
          (TraceCorQQuotient.add
            (TraceCorQQuotient.comp pre (TraceCorQQuotient.neg third))
            (TraceCorQQuotient.comp pre (TraceCorQQuotient.neg fourth)))) :=
  TraceCorQQuotient.smul_comp_add_add_add
    (-1)
    pre
    first
    second
    third
    fourth

/-- Negate a quotient composite whose target input is a right-associated four-summand sum. -/
theorem TraceCorQQuotient.neg_comp_add_add_add_right
    (pre first second third fourth : TraceCorQQuotient) :
    TraceCorQQuotient.neg
      (TraceCorQQuotient.comp
        pre
        (TraceCorQQuotient.add
          first
          (TraceCorQQuotient.add
            second
            (TraceCorQQuotient.add third fourth)))) =
      TraceCorQQuotient.add
        (TraceCorQQuotient.comp pre (TraceCorQQuotient.neg first))
        (TraceCorQQuotient.add
          (TraceCorQQuotient.comp pre (TraceCorQQuotient.neg second))
          (TraceCorQQuotient.add
            (TraceCorQQuotient.comp pre (TraceCorQQuotient.neg third))
            (TraceCorQQuotient.comp pre (TraceCorQQuotient.neg fourth)))) :=
  TraceCorQQuotient.smul_comp_add_add_add_right
    (-1)
    pre
    first
    second
    third
    fourth

end AnalyticMotives
end LFunctions
end Boundary
