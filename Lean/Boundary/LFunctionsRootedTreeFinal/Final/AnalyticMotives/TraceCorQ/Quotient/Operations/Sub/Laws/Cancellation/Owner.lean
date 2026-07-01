import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Quotient.Operations.Sub.Laws.Owner

/-!
# Cancellation laws for quotient subtraction

This file collects derived quotient subtraction cancellation and solver laws.
The primitive inverse and cancellation facts live in `Sub.Laws.Owner`.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- If a quotient class is a sum, subtracting the left summand leaves the right summand. -/
theorem TraceCorQQuotient.sub_left_summand_eq_right
    (left right tail : TraceCorQQuotient)
    (left_eq_right_add_tail :
      left = TraceCorQQuotient.add right tail) :
    TraceCorQQuotient.sub left right = tail :=
  Eq.symm
    (TraceCorQQuotient.right_eq_sub_of_add_eq
      right
      tail
      left
      (Eq.symm left_eq_right_add_tail))

/-- If a quotient class is a sum, subtracting the right summand leaves the left summand. -/
theorem TraceCorQQuotient.sub_right_summand_eq_left
    (left right tail : TraceCorQQuotient)
    (left_eq_right_add_tail :
      left = TraceCorQQuotient.add right tail) :
    TraceCorQQuotient.sub left tail = right :=
  Eq.symm
    (TraceCorQQuotient.left_eq_sub_of_add_eq
      right
      tail
      left
      (Eq.symm left_eq_right_add_tail))

/-- A quotient subtraction equality follows from equality after adding the subtrahend. -/
theorem TraceCorQQuotient.sub_eq_of_add_eq
    (left right tail : TraceCorQQuotient)
    (left_eq_tail_add_right :
      left = TraceCorQQuotient.add tail right) :
    TraceCorQQuotient.sub left right = tail :=
  TraceCorQQuotient.sub_right_summand_eq_left
    left
    tail
    right
    left_eq_tail_add_right

end AnalyticMotives
end LFunctions
end Boundary
