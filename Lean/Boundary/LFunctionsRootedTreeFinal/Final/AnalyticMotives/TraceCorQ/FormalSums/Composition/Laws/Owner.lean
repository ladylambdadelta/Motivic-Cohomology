import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.FormalSums.Composition.Basic.Owner

/-!
# Public formal-sum composition laws

This file exposes the concrete raw formal-sum composition laws under the
`TraceCorQ` aggregate namespace.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- The trace-correspondence root exposes left-zero formal-sum composition. -/
theorem TraceCorQ.formalSum_zero_comp
    (formalSum : TraceCorQFormalSum) :
    TraceCorQFormalSum.comp
      TraceCorQFormalSum.zero
      formalSum =
      TraceCorQFormalSum.zero :=
  TraceCorQFormalSum.zero_comp
    formalSum

/-- The trace-correspondence root exposes right-zero formal-sum composition. -/
theorem TraceCorQ.formalSum_comp_zero
    (formalSum : TraceCorQFormalSum) :
    TraceCorQFormalSum.comp
      formalSum
      TraceCorQFormalSum.zero =
      TraceCorQFormalSum.zero :=
  TraceCorQFormalSum.comp_zero
    formalSum

/-- The trace-correspondence root exposes left distributivity of formal-sum composition. -/
theorem TraceCorQ.formalSum_add_comp
    (left right tail : TraceCorQFormalSum) :
    TraceCorQFormalSum.comp
      (TraceCorQFormalSum.add left right)
      tail =
      TraceCorQFormalSum.add
        (TraceCorQFormalSum.comp left tail)
        (TraceCorQFormalSum.comp right tail) :=
  TraceCorQFormalSum.add_comp
    left
    right
    tail

/-- The trace-correspondence root exposes right distributivity up to raw-list permutation. -/
theorem TraceCorQ.formalSum_comp_add_perm
    (left right tail : TraceCorQFormalSum) :
    List.Perm
      (TraceCorQFormalSum.comp
        left
        (TraceCorQFormalSum.add right tail))
      (TraceCorQFormalSum.add
        (TraceCorQFormalSum.comp left right)
        (TraceCorQFormalSum.comp left tail)) :=
  TraceCorQFormalSum.comp_add_perm
    left
    right
    tail

/-- The trace-correspondence root exposes scalar compatibility on the left input of composition. -/
theorem TraceCorQ.formalSum_smul_comp
    (coefficient : Rat)
    (left right : TraceCorQFormalSum) :
    TraceCorQFormalSum.comp
      (TraceCorQFormalSum.smul coefficient left)
      right =
      TraceCorQFormalSum.smul
        coefficient
        (TraceCorQFormalSum.comp left right) :=
  TraceCorQFormalSum.smul_comp
    coefficient
    left
    right

/-- The trace-correspondence root exposes scalar compatibility on the right input of composition. -/
theorem TraceCorQ.formalSum_comp_smul
    (coefficient : Rat)
    (left right : TraceCorQFormalSum) :
    TraceCorQFormalSum.comp
      left
      (TraceCorQFormalSum.smul coefficient right) =
      TraceCorQFormalSum.smul
        coefficient
        (TraceCorQFormalSum.comp left right) :=
  TraceCorQFormalSum.comp_smul
    coefficient
    left
    right

end AnalyticMotives
end LFunctions
end Boundary
