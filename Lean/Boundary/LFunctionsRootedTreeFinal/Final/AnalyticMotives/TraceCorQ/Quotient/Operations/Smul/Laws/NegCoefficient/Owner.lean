import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Quotient.Operations.Neg.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Quotient.Operations.Smul.Laws.Owner

/-!
# Negative scalar coefficient laws

This file owns negation in the scalar coefficient for quotient
trace-correspondence classes.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Negating the scalar coefficient negates the scaled quotient class. -/
theorem TraceCorQQuotient.neg_smul
    (coefficient : Rat)
    (candidateClass : TraceCorQQuotient) :
    TraceCorQQuotient.smul
      (-coefficient)
      candidateClass =
      TraceCorQQuotient.neg
        (TraceCorQQuotient.smul coefficient candidateClass) :=
  Eq.trans
    (congrArg
      (fun productCoefficient =>
        TraceCorQQuotient.smul productCoefficient candidateClass)
      (Eq.symm
        (neg_one_mul coefficient)))
    (Eq.symm
      (TraceCorQQuotient.smul_smul
        (-1)
        coefficient
        candidateClass))

end AnalyticMotives
end LFunctions
end Boundary
