import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Quotient.Operations.FormalSumClass.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Quotient.Operations.Add.Laws.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Quotient.Operations.Add.Laws.Full.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Quotient.Operations.Singleton.Laws.CoefficientCombination.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Quotient.Operations.Smul.Laws.Owner

/-!
# Scalar-coefficient additivity

This file owns additivity in the scalar coefficient for quotient
trace-correspondence classes.  The proof is by formal-sum induction from
same-generator singleton coefficient combination.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Scaling a candidate class is the formal-sum class of the scaled formal sum. -/
theorem TraceCorQQuotient.smul_ofCandidate_eq_ofFormalSum_smul
    (coefficient : Rat)
    (candidate : TraceCorQQuotientCandidate) :
    TraceCorQQuotient.smul
      coefficient
      (TraceCorQQuotient.ofCandidate candidate) =
      TraceCorQQuotient.ofFormalSum
        (TraceCorQFormalSum.smul coefficient candidate.formalSum) :=
  Eq.trans
    (TraceCorQQuotient.smul_ofCandidate coefficient candidate)
    (Eq.trans
      (TraceCorQQuotient.ofCandidate_eq_ofFormalSum
        (TraceCorQQuotientCandidate.smul coefficient candidate))
      (congrArg
        TraceCorQQuotient.ofFormalSum
        (TraceCorQQuotientCandidate.smul_formalSum
          coefficient
          candidate)))

/-- Formal-sum scalar coefficient additivity. -/
theorem TraceCorQQuotient.ofFormalSum_add_smul
    (leftCoefficient rightCoefficient : Rat)
    (formalSum : TraceCorQFormalSum) :
    TraceCorQQuotient.ofFormalSum
      (TraceCorQFormalSum.smul
        (leftCoefficient + rightCoefficient)
        formalSum) =
      TraceCorQQuotient.add
        (TraceCorQQuotient.ofFormalSum
          (TraceCorQFormalSum.smul leftCoefficient formalSum))
        (TraceCorQQuotient.ofFormalSum
          (TraceCorQFormalSum.smul rightCoefficient formalSum)) :=
  match formalSum with
  | [] =>
      Eq.symm
        (TraceCorQQuotient.zero_add TraceCorQQuotient.zero)
  | (coefficient, generator) :: tail =>
      Eq.trans
        (TraceCorQQuotient.ofFormalSum_cons
          ((leftCoefficient + rightCoefficient) * coefficient)
          generator
          (TraceCorQFormalSum.smul
            (leftCoefficient + rightCoefficient)
            tail))
        (Eq.trans
          (congrArg
            (fun headClass =>
              TraceCorQQuotient.add
                headClass
                (TraceCorQQuotient.ofFormalSum
                  (TraceCorQFormalSum.smul
                    (leftCoefficient + rightCoefficient)
                    tail)))
            (Eq.trans
              (congrArg
                (fun headCoefficient =>
                  TraceCorQQuotient.singleton headCoefficient generator)
                (add_mul
                  leftCoefficient
                  rightCoefficient
                  coefficient))
              (Eq.symm
                (TraceCorQQuotient.singleton_add_singleton_same_generator
                  (leftCoefficient * coefficient)
                  (rightCoefficient * coefficient)
                  generator))))
          (Eq.trans
            (congrArg
              (fun tailClass =>
                TraceCorQQuotient.add
                  (TraceCorQQuotient.add
                    (TraceCorQQuotient.singleton
                      (leftCoefficient * coefficient)
                      generator)
                    (TraceCorQQuotient.singleton
                      (rightCoefficient * coefficient)
                      generator))
                  tailClass)
              (TraceCorQQuotient.ofFormalSum_add_smul
                leftCoefficient
                rightCoefficient
                tail))
            (Eq.trans
              (TraceCorQQuotient.add_add_add_comm
                (TraceCorQQuotient.singleton
                  (leftCoefficient * coefficient)
                  generator)
                (TraceCorQQuotient.singleton
                  (rightCoefficient * coefficient)
                  generator)
                (TraceCorQQuotient.ofFormalSum
                  (TraceCorQFormalSum.smul leftCoefficient tail))
                (TraceCorQQuotient.ofFormalSum
                  (TraceCorQFormalSum.smul rightCoefficient tail)))
              (Eq.trans
                (congrArg
                  (fun leftHead =>
                    TraceCorQQuotient.add
                      leftHead
                      (TraceCorQQuotient.add
                        (TraceCorQQuotient.singleton
                          (rightCoefficient * coefficient)
                          generator)
                        (TraceCorQQuotient.ofFormalSum
                          (TraceCorQFormalSum.smul rightCoefficient tail))))
                  (Eq.symm
                    (TraceCorQQuotient.ofFormalSum_cons
                      (leftCoefficient * coefficient)
                      generator
                      (TraceCorQFormalSum.smul leftCoefficient tail))))
                (congrArg
                  (TraceCorQQuotient.add
                    (TraceCorQQuotient.ofFormalSum
                      (TraceCorQFormalSum.smul leftCoefficient
                        ((coefficient, generator) :: tail))))
                  (Eq.symm
                    (TraceCorQQuotient.ofFormalSum_cons
                      (rightCoefficient * coefficient)
                      generator
                      (TraceCorQFormalSum.smul
                        rightCoefficient
                        tail))))))))

/-- Scalar multiplication is additive in the scalar coefficient. -/
theorem TraceCorQQuotient.add_smul
    (leftCoefficient rightCoefficient : Rat)
    (candidateClass : TraceCorQQuotient) :
    TraceCorQQuotient.smul
      (leftCoefficient + rightCoefficient)
      candidateClass =
      TraceCorQQuotient.add
        (TraceCorQQuotient.smul leftCoefficient candidateClass)
        (TraceCorQQuotient.smul rightCoefficient candidateClass) :=
  Quotient.inductionOn
    candidateClass
    (fun candidate =>
      Eq.trans
        (TraceCorQQuotient.smul_ofCandidate
          (leftCoefficient + rightCoefficient)
          candidate)
        (Eq.trans
          (TraceCorQQuotient.ofCandidate_eq_ofFormalSum
            (TraceCorQQuotientCandidate.smul
              (leftCoefficient + rightCoefficient)
              candidate))
          (Eq.trans
            (congrArg
              TraceCorQQuotient.ofFormalSum
              (TraceCorQQuotientCandidate.smul_formalSum
                (leftCoefficient + rightCoefficient)
                candidate))
            (Eq.trans
              (TraceCorQQuotient.ofFormalSum_add_smul
                leftCoefficient
                rightCoefficient
                candidate.formalSum)
              (Eq.symm
                (Eq.trans
                  (congrArg
                    (fun leftClass =>
                      TraceCorQQuotient.add
                        leftClass
                        (TraceCorQQuotient.ofFormalSum
                          (TraceCorQFormalSum.smul
                            rightCoefficient
                            candidate.formalSum)))
                    (TraceCorQQuotient.smul_ofCandidate_eq_ofFormalSum_smul
                      leftCoefficient
                      candidate))
                  (congrArg
                    (TraceCorQQuotient.add
                      (TraceCorQQuotient.smul
                        leftCoefficient
                        (TraceCorQQuotient.ofCandidate candidate)))
                    (TraceCorQQuotient.smul_ofCandidate_eq_ofFormalSum_smul
                      rightCoefficient
                      candidate))))))))

end AnalyticMotives
end LFunctions
end Boundary
