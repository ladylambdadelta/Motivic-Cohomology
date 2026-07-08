import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.FormalSums.Additive.Owner

/-!
# Top-root formal-sum additive laws

This file exposes raw-list additive laws for finite `Q`-linear formal sums
through the top-level `AnalyticMotivesRoot` namespace.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- The top root exposes left zero for raw formal-sum addition. -/
theorem AnalyticMotivesRoot.traceCorQFormalSum_zero_add
    (formalSum : TraceCorQFormalSum) :
    TraceCorQFormalSum.add
      TraceCorQFormalSum.zero
      formalSum =
      formalSum :=
  TraceCorQ.formalSum_zero_add
    formalSum

/-- The top root exposes right zero for raw formal-sum addition. -/
theorem AnalyticMotivesRoot.traceCorQFormalSum_add_zero
    (formalSum : TraceCorQFormalSum) :
    TraceCorQFormalSum.add
      formalSum
      TraceCorQFormalSum.zero =
      formalSum :=
  TraceCorQ.formalSum_add_zero
    formalSum

/-- The top root exposes associativity for raw formal-sum addition. -/
theorem AnalyticMotivesRoot.traceCorQFormalSum_add_assoc
    (first second third : TraceCorQFormalSum) :
    TraceCorQFormalSum.add
      (TraceCorQFormalSum.add first second)
      third =
      TraceCorQFormalSum.add
        first
        (TraceCorQFormalSum.add second third) :=
  TraceCorQ.formalSum_add_assoc
    first
    second
    third

end AnalyticMotives
end LFunctions
end Boundary
