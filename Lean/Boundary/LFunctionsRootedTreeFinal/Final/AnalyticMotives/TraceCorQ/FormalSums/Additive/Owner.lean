import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.FormalSums.Composition.Basic.Owner

/-!
# Public formal-sum additive laws

This file exposes the concrete raw-list additive laws for finite `Q`-linear
formal sums under the `TraceCorQ` aggregate namespace.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- The trace-correspondence root exposes left zero for raw formal-sum addition. -/
theorem TraceCorQ.formalSum_zero_add
    (formalSum : TraceCorQFormalSum) :
    TraceCorQFormalSum.add
      TraceCorQFormalSum.zero
      formalSum =
      formalSum :=
  TraceCorQFormalSum.zero_add
    formalSum

/-- The trace-correspondence root exposes right zero for raw formal-sum addition. -/
theorem TraceCorQ.formalSum_add_zero
    (formalSum : TraceCorQFormalSum) :
    TraceCorQFormalSum.add
      formalSum
      TraceCorQFormalSum.zero =
      formalSum :=
  TraceCorQFormalSum.add_zero
    formalSum

/-- The trace-correspondence root exposes associativity for raw formal-sum addition. -/
theorem TraceCorQ.formalSum_add_assoc
    (first second third : TraceCorQFormalSum) :
    TraceCorQFormalSum.add
      (TraceCorQFormalSum.add first second)
      third =
      TraceCorQFormalSum.add
        first
        (TraceCorQFormalSum.add second third) :=
  TraceCorQFormalSum.add_assoc
    first
    second
    third

end AnalyticMotives
end LFunctions
end Boundary
