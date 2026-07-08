import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceExpression.Atoms.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceExpression.FormalSum.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceExpression.QLinear.Owner

/-!
# Trace expressions

Trace expressions are the formal language in which analytic residue-channel
rewriting is stated.  Morphisms and motives are constructed in downstream
owners from this expression layer.

The dependency order is atoms, additive formal sums, then Q-linear
combinations.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- The root trace-expression owner exposes boundary atom roles. -/
theorem TraceExpression.boundary_role
    (stage : TraceStageIndex)
    (face : TraceFaceIndex) :
    (TraceAtom.boundary stage face).role =
      TraceAtomRole.boundary :=
  TraceAtom.role_boundary
    stage
    face

/-- The root trace-expression owner exposes residue atom roles. -/
theorem TraceExpression.residue_role
    (stage : TraceStageIndex)
    (face : TraceFaceIndex) :
    (TraceAtom.residue stage face).role =
      TraceAtomRole.residue :=
  TraceAtom.role_residue
    stage
    face

/-- The root trace-expression owner exposes formal-sum concatenation. -/
theorem TraceExpression.formalSum_add_eq_append
    (left right : TraceFormalSum) :
    TraceFormalSum.add left right =
      left ++ right :=
  TraceFormalSum.add_eq_append
    left
    right

/-- The root trace-expression owner exposes Q-linear trace-expression concatenation. -/
theorem TraceExpression.qTraceExpression_add_eq_append
    (left right : QTraceExpression) :
    QTraceExpression.add left right =
      left ++ right :=
  QTraceExpression.add_eq_append
    left
    right

/-- The root trace-expression owner exposes Q-linear scalar multiplication. -/
theorem TraceExpression.qTraceExpression_smul_eq_map
    (coefficient : Rat)
    (expression : QTraceExpression) :
    QTraceExpression.smul coefficient expression =
      expression.map (fun term => (coefficient * term.1, term.2)) :=
  QTraceExpression.smul_eq_map
    coefficient
    expression

end AnalyticMotives
end LFunctions
end Boundary
