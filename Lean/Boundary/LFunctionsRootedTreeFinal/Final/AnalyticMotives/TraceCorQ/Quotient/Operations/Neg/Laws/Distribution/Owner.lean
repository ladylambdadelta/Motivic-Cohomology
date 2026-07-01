import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Quotient.Operations.Neg.Laws.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Quotient.Operations.Smul.Laws.Distribution.Owner

/-!
# Negation distribution normal forms for quotient trace correspondences

This file owns longer-sum negation normalizers.  Negation is scalar
multiplication by `-1`, so these are concrete wrappers around the scalar
distribution theorems.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Distribute quotient negation over a left-associated three-summand sum. -/
theorem TraceCorQQuotient.neg_add_three_left
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
  TraceCorQQuotient.smul_add_three_left
    (-1)
    first
    second
    third

/-- Distribute quotient negation over a right-associated three-summand sum. -/
theorem TraceCorQQuotient.neg_add_three_right
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
  TraceCorQQuotient.smul_add_three_right
    (-1)
    first
    second
    third

/-- Distribute quotient negation over a fully left-associated four-summand sum. -/
theorem TraceCorQQuotient.neg_add_four_left
    (first second third fourth : TraceCorQQuotient) :
    TraceCorQQuotient.neg
      (TraceCorQQuotient.add
        (TraceCorQQuotient.add
          (TraceCorQQuotient.add first second)
          third)
        fourth) =
      TraceCorQQuotient.add
        (TraceCorQQuotient.neg first)
        (TraceCorQQuotient.add
          (TraceCorQQuotient.neg second)
          (TraceCorQQuotient.add
            (TraceCorQQuotient.neg third)
            (TraceCorQQuotient.neg fourth))) :=
  TraceCorQQuotient.smul_add_four_left
    (-1)
    first
    second
    third
    fourth

/-- Distribute quotient negation over a fully right-associated four-summand sum. -/
theorem TraceCorQQuotient.neg_add_four_right
    (first second third fourth : TraceCorQQuotient) :
    TraceCorQQuotient.neg
      (TraceCorQQuotient.add
        first
        (TraceCorQQuotient.add
          second
          (TraceCorQQuotient.add third fourth))) =
      TraceCorQQuotient.add
        (TraceCorQQuotient.neg first)
        (TraceCorQQuotient.add
          (TraceCorQQuotient.neg second)
          (TraceCorQQuotient.add
            (TraceCorQQuotient.neg third)
            (TraceCorQQuotient.neg fourth))) :=
  TraceCorQQuotient.smul_add_four_right
    (-1)
    first
    second
    third
    fourth

end AnalyticMotives
end LFunctions
end Boundary
