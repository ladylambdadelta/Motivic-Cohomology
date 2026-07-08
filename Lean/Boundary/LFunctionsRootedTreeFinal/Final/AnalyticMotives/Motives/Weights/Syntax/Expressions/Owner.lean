import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Weights.Syntax.Atoms.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceExpression.QLinear.Owner

/-!
# Weight levels of Q-linear trace expressions

The weight level of a finite Q-linear trace expression is the maximum of the
weight levels of its underlying trace atoms.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- The syntactic weight level of a rationally weighted trace term. -/
def QTraceTerm.weightLevel
    (term : QTraceTerm) :
    Nat :=
  term.2.weightLevel

/-- The maximum syntactic weight level in a finite Q-linear trace expression. -/
def QTraceExpression.weightLevel : QTraceExpression → Nat
  | [] => 0
  | term :: tail =>
      Nat.max term.weightLevel tail.weightLevel

/-- The empty Q-linear trace expression has weight level zero. -/
theorem QTraceExpression.weightLevel_zero :
    QTraceExpression.zero.weightLevel =
      0 :=
  rfl

/-- A weighted trace term has the weight level of its atom. -/
theorem QTraceTerm.weightLevel_eq_atom
    (coefficient : Rat)
    (atom : TraceAtom) :
    ((coefficient, atom) : QTraceTerm).weightLevel =
      atom.weightLevel :=
  rfl

/-- A singleton expression has the weight level of its atom. -/
theorem QTraceExpression.weightLevel_singleton
    (coefficient : Rat)
    (atom : TraceAtom) :
    (QTraceExpression.singleton coefficient atom).weightLevel =
      Nat.max atom.weightLevel 0 :=
  rfl

/-- A cons expression records the maximum of head and tail weight levels. -/
theorem QTraceExpression.weightLevel_cons
    (term : QTraceTerm)
    (tail : QTraceExpression) :
    (term :: tail).weightLevel =
      Nat.max term.weightLevel tail.weightLevel :=
  rfl

end AnalyticMotives
end LFunctions
end Boundary
