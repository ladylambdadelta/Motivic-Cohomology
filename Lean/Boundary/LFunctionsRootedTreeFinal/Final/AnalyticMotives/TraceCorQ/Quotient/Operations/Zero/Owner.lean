import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Quotient.Setoid.Owner

/-!
# Zero quotient trace correspondence

This file names the zero quotient class represented by the empty raw
candidate.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- The zero quotient trace-correspondence class. -/
def TraceCorQQuotient.zero :
    TraceCorQQuotient :=
  TraceCorQQuotient.ofCandidate TraceCorQQuotientCandidate.empty

/-- The zero quotient class is represented by the empty raw candidate. -/
theorem TraceCorQQuotient.zero_eq_ofCandidate_empty :
    TraceCorQQuotient.zero =
      TraceCorQQuotient.ofCandidate TraceCorQQuotientCandidate.empty :=
  rfl

end AnalyticMotives
end LFunctions
end Boundary
