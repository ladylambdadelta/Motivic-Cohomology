import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceExpression.Owner

/-!
# Top-root trace expressions

This file exposes the concrete trace-expression syntax facts under the
top-level `AnalyticMotivesRoot` namespace.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Boundary trace atoms have boundary role at the top root. -/
theorem AnalyticMotivesRoot.traceExpression_boundary_role
    (stage : TraceStageIndex)
    (face : TraceFaceIndex) :
    (TraceAtom.boundary stage face).role =
      TraceAtomRole.boundary :=
  TraceExpression.boundary_role
    stage
    face

/-- Residue trace atoms have residue role at the top root. -/
theorem AnalyticMotivesRoot.traceExpression_residue_role
    (stage : TraceStageIndex)
    (face : TraceFaceIndex) :
    (TraceAtom.residue stage face).role =
      TraceAtomRole.residue :=
  TraceExpression.residue_role
    stage
    face

/-- Formal-sum addition is list append at the top root. -/
theorem AnalyticMotivesRoot.traceFormalSum_add_eq_append
    (left right : TraceFormalSum) :
    TraceFormalSum.add left right =
      left ++ right :=
  TraceExpression.formalSum_add_eq_append
    left
    right

/-- Q-linear expression addition is list append at the top root. -/
theorem AnalyticMotivesRoot.qTraceExpression_add_eq_append
    (left right : QTraceExpression) :
    QTraceExpression.add left right =
      left ++ right :=
  TraceExpression.qTraceExpression_add_eq_append
    left
    right

/-- Q-linear expression scalar multiplication maps coefficients at the top root. -/
theorem AnalyticMotivesRoot.qTraceExpression_smul_eq_map
    (coefficient : Rat)
    (expression : QTraceExpression) :
    QTraceExpression.smul coefficient expression =
      expression.map (fun term => (coefficient * term.1, term.2)) :=
  TraceExpression.qTraceExpression_smul_eq_map
    coefficient
    expression

end AnalyticMotives
end LFunctions
end Boundary
