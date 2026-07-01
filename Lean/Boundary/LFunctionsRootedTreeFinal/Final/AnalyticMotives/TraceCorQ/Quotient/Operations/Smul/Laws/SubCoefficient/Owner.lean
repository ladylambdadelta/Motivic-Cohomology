import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Quotient.Operations.Sub.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Quotient.Operations.Smul.Laws.CoefficientAdditivity.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Quotient.Operations.Smul.Laws.NegCoefficient.Owner

/-!
# Subtraction in scalar coefficients

This file owns subtraction in the scalar coefficient for quotient
trace-correspondence classes.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Scalar multiplication is subtractive in the scalar coefficient. -/
theorem TraceCorQQuotient.sub_smul
    (leftCoefficient rightCoefficient : Rat)
    (candidateClass : TraceCorQQuotient) :
    TraceCorQQuotient.smul
      (leftCoefficient - rightCoefficient)
      candidateClass =
      TraceCorQQuotient.sub
        (TraceCorQQuotient.smul leftCoefficient candidateClass)
        (TraceCorQQuotient.smul rightCoefficient candidateClass) :=
  Eq.trans
    (congrArg
      (fun coefficient =>
        TraceCorQQuotient.smul coefficient candidateClass)
      (sub_eq_add_neg leftCoefficient rightCoefficient))
    (Eq.trans
      (TraceCorQQuotient.add_smul
        leftCoefficient
        (-rightCoefficient)
        candidateClass)
      (Eq.trans
        (congrArg
          (TraceCorQQuotient.add
            (TraceCorQQuotient.smul leftCoefficient candidateClass))
          (TraceCorQQuotient.neg_smul
            rightCoefficient
            candidateClass))
        (Eq.symm
          (TraceCorQQuotient.sub_eq_add_neg
            (TraceCorQQuotient.smul leftCoefficient candidateClass)
            (TraceCorQQuotient.smul rightCoefficient candidateClass)))))

end AnalyticMotives
end LFunctions
end Boundary
