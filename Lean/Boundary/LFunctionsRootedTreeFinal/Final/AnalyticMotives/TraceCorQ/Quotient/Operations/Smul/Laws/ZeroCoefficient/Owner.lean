import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Quotient.Operations.FormalSumClass.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Quotient.Operations.Add.Laws.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Quotient.Operations.Singleton.Laws.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Quotient.Operations.Smul.Laws.Owner

/-!
# Zero-coefficient scalar laws

This file owns the proof that scaling a quotient trace correspondence by zero
gives the zero quotient class.  The proof is by formal-sum induction from
zero-coefficient singleton erasure.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- A formal sum scaled by zero represents the zero quotient class. -/
theorem TraceCorQQuotient.ofFormalSum_zero_smul
    (formalSum : TraceCorQFormalSum) :
    TraceCorQQuotient.ofFormalSum
      (TraceCorQFormalSum.smul 0 formalSum) =
      TraceCorQQuotient.zero :=
  match formalSum with
  | [] => TraceCorQQuotient.ofFormalSum_nil
  | (coefficient, generator) :: tail =>
      Eq.trans
        (TraceCorQQuotient.ofFormalSum_cons
          (0 * coefficient)
          generator
          (TraceCorQFormalSum.smul 0 tail))
        (Eq.trans
          (congrArg
            (fun headClass =>
              TraceCorQQuotient.add
                headClass
                (TraceCorQQuotient.ofFormalSum
                  (TraceCorQFormalSum.smul 0 tail)))
            (Eq.trans
              (congrArg
                (fun headCoefficient =>
                  TraceCorQQuotient.singleton headCoefficient generator)
                (zero_mul coefficient))
              (TraceCorQQuotient.singleton_zero generator)))
          (Eq.trans
            (congrArg
              (fun tailClass =>
                TraceCorQQuotient.add
                  TraceCorQQuotient.zero
                  tailClass)
              (TraceCorQQuotient.ofFormalSum_zero_smul tail))
            (TraceCorQQuotient.zero_add TraceCorQQuotient.zero)))

/-- Scaling any quotient trace-correspondence class by zero gives zero. -/
theorem TraceCorQQuotient.zero_smul
    (candidateClass : TraceCorQQuotient) :
    TraceCorQQuotient.smul 0 candidateClass =
      TraceCorQQuotient.zero :=
  Quotient.inductionOn
    candidateClass
    (fun candidate =>
      Eq.trans
        (TraceCorQQuotient.smul_ofCandidate 0 candidate)
        (Eq.trans
          (TraceCorQQuotient.ofCandidate_eq_ofFormalSum
            (TraceCorQQuotientCandidate.smul 0 candidate))
          (Eq.trans
            (congrArg
              TraceCorQQuotient.ofFormalSum
              (TraceCorQQuotientCandidate.smul_formalSum
                0
                candidate))
            (TraceCorQQuotient.ofFormalSum_zero_smul
              candidate.formalSum))))

end AnalyticMotives
end LFunctions
end Boundary
