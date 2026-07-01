import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Quotient.Operations.Add.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Quotient.Operations.Neg.Owner

/-!
# Subtraction of quotient trace correspondences

This file owns subtraction as the derived operation `left + neg right` in the
quotient trace-correspondence span.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Subtraction of quotient trace-correspondence classes. -/
def TraceCorQQuotient.sub
    (left right : TraceCorQQuotient) :
    TraceCorQQuotient :=
  TraceCorQQuotient.add left (TraceCorQQuotient.neg right)

/-- Quotient subtraction unfolds to addition of the negative. -/
theorem TraceCorQQuotient.sub_eq_add_neg
    (left right : TraceCorQQuotient) :
    TraceCorQQuotient.sub left right =
      TraceCorQQuotient.add left (TraceCorQQuotient.neg right) :=
  rfl

end AnalyticMotives
end LFunctions
end Boundary
