import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.FormalSums.Composition.Laws.Owner

/-!
# Top-root formal-sum composition laws

This file exposes raw formal-sum composition laws through the top-level
`AnalyticMotivesRoot` namespace.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- The top root exposes left-zero formal-sum composition. -/
theorem AnalyticMotivesRoot.traceCorQFormalSum_zero_comp
    (formalSum : TraceCorQFormalSum) :
    TraceCorQFormalSum.comp
      TraceCorQFormalSum.zero
      formalSum =
      TraceCorQFormalSum.zero :=
  TraceCorQ.formalSum_zero_comp
    formalSum

/-- The top root exposes right-zero formal-sum composition. -/
theorem AnalyticMotivesRoot.traceCorQFormalSum_comp_zero
    (formalSum : TraceCorQFormalSum) :
    TraceCorQFormalSum.comp
      formalSum
      TraceCorQFormalSum.zero =
      TraceCorQFormalSum.zero :=
  TraceCorQ.formalSum_comp_zero
    formalSum

/-- The top root exposes left distributivity of formal-sum composition. -/
theorem AnalyticMotivesRoot.traceCorQFormalSum_add_comp
    (left right tail : TraceCorQFormalSum) :
    TraceCorQFormalSum.comp
      (TraceCorQFormalSum.add left right)
      tail =
      TraceCorQFormalSum.add
        (TraceCorQFormalSum.comp left tail)
        (TraceCorQFormalSum.comp right tail) :=
  TraceCorQ.formalSum_add_comp
    left
    right
    tail

/-- The top root exposes right distributivity up to raw-list permutation. -/
theorem AnalyticMotivesRoot.traceCorQFormalSum_comp_add_perm
    (left right tail : TraceCorQFormalSum) :
    List.Perm
      (TraceCorQFormalSum.comp
        left
        (TraceCorQFormalSum.add right tail))
      (TraceCorQFormalSum.add
        (TraceCorQFormalSum.comp left right)
        (TraceCorQFormalSum.comp left tail)) :=
  TraceCorQ.formalSum_comp_add_perm
    left
    right
    tail

/-- The top root exposes scalar compatibility on the left input of composition. -/
theorem AnalyticMotivesRoot.traceCorQFormalSum_smul_comp
    (coefficient : Rat)
    (left right : TraceCorQFormalSum) :
    TraceCorQFormalSum.comp
      (TraceCorQFormalSum.smul coefficient left)
      right =
      TraceCorQFormalSum.smul
        coefficient
        (TraceCorQFormalSum.comp left right) :=
  TraceCorQ.formalSum_smul_comp
    coefficient
    left
    right

/-- The top root exposes scalar compatibility on the right input of composition. -/
theorem AnalyticMotivesRoot.traceCorQFormalSum_comp_smul
    (coefficient : Rat)
    (left right : TraceCorQFormalSum) :
    TraceCorQFormalSum.comp
      left
      (TraceCorQFormalSum.smul coefficient right) =
      TraceCorQFormalSum.smul
        coefficient
        (TraceCorQFormalSum.comp left right) :=
  TraceCorQ.formalSum_comp_smul
    coefficient
    left
    right

end AnalyticMotives
end LFunctions
end Boundary
