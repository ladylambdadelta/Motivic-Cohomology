import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Root.TraceCorQ.FormalSums.Composition.Laws.Owner

/-!
# Top-root formal-sum composition

This file aggregates the top-root composition laws for finite Q-linear
trace-correspondence formal sums.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Formal-sum composition aggregate: zero on the left composes to zero. -/
theorem AnalyticMotivesRoot.traceCorQFormalSum_compSummary_zero_comp
    (formalSum : TraceCorQFormalSum) :
    TraceCorQFormalSum.comp
      TraceCorQFormalSum.zero
      formalSum =
      TraceCorQFormalSum.zero :=
  AnalyticMotivesRoot.traceCorQFormalSum_zero_comp
    formalSum

/-- Formal-sum composition aggregate: zero on the right composes to zero. -/
theorem AnalyticMotivesRoot.traceCorQFormalSum_compSummary_comp_zero
    (formalSum : TraceCorQFormalSum) :
    TraceCorQFormalSum.comp
      formalSum
      TraceCorQFormalSum.zero =
      TraceCorQFormalSum.zero :=
  AnalyticMotivesRoot.traceCorQFormalSum_comp_zero
    formalSum

/-- Formal-sum composition aggregate: composition distributes over addition on the left. -/
theorem AnalyticMotivesRoot.traceCorQFormalSum_compSummary_add_comp
    (left right tail : TraceCorQFormalSum) :
    TraceCorQFormalSum.comp
      (TraceCorQFormalSum.add left right)
      tail =
      TraceCorQFormalSum.add
        (TraceCorQFormalSum.comp left tail)
        (TraceCorQFormalSum.comp right tail) :=
  AnalyticMotivesRoot.traceCorQFormalSum_add_comp
    left
    right
    tail

/-- Formal-sum composition aggregate: scalar multiplication commutes with left composition. -/
theorem AnalyticMotivesRoot.traceCorQFormalSum_compSummary_smul_comp
    (coefficient : Rat)
    (left right : TraceCorQFormalSum) :
    TraceCorQFormalSum.comp
      (TraceCorQFormalSum.smul coefficient left)
      right =
      TraceCorQFormalSum.smul
        coefficient
        (TraceCorQFormalSum.comp left right) :=
  AnalyticMotivesRoot.traceCorQFormalSum_smul_comp
    coefficient
    left
    right

/-- Formal-sum composition aggregate: scalar multiplication commutes with right composition. -/
theorem AnalyticMotivesRoot.traceCorQFormalSum_compSummary_comp_smul
    (coefficient : Rat)
    (left right : TraceCorQFormalSum) :
    TraceCorQFormalSum.comp
      left
      (TraceCorQFormalSum.smul coefficient right) =
      TraceCorQFormalSum.smul
        coefficient
        (TraceCorQFormalSum.comp left right) :=
  AnalyticMotivesRoot.traceCorQFormalSum_comp_smul
    coefficient
    left
    right

end AnalyticMotives
end LFunctions
end Boundary
