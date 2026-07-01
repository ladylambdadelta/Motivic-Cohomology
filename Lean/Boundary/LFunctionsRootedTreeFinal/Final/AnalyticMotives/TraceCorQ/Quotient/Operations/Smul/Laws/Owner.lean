import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Quotient.Operations.Add.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Quotient.Operations.Neg.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Quotient.Operations.Smul.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Quotient.Operations.Zero.Owner

/-!
# Scalar laws for quotient trace correspondences

This file proves the first scalar laws for quotient trace-correspondence
classes by quotient induction from the corresponding candidate laws.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Scaling the zero quotient class gives the zero quotient class. -/
theorem TraceCorQQuotient.smul_zero
    (coefficient : Rat) :
    TraceCorQQuotient.smul
      coefficient
      TraceCorQQuotient.zero =
      TraceCorQQuotient.zero :=
  Eq.trans
    (TraceCorQQuotient.smul_ofCandidate
      coefficient
      TraceCorQQuotientCandidate.empty)
    (congrArg
      TraceCorQQuotient.ofCandidate
      (TraceCorQQuotientCandidate.smul_empty coefficient))

/-- Scalar multiplication distributes over quotient addition. -/
theorem TraceCorQQuotient.smul_add
    (coefficient : Rat)
    (left right : TraceCorQQuotient) :
    TraceCorQQuotient.smul
      coefficient
      (TraceCorQQuotient.add left right) =
      TraceCorQQuotient.add
        (TraceCorQQuotient.smul coefficient left)
        (TraceCorQQuotient.smul coefficient right) :=
  Quotient.inductionOn₂
    left
    right
    (fun leftCandidate rightCandidate =>
      Eq.trans
        (congrArg
          (TraceCorQQuotient.smul coefficient)
          (TraceCorQQuotient.add_ofCandidate
            leftCandidate
            rightCandidate))
        (Eq.trans
          (TraceCorQQuotient.smul_ofCandidate
            coefficient
            (TraceCorQQuotientCandidate.add
              leftCandidate
              rightCandidate))
          (Eq.trans
            (congrArg
              TraceCorQQuotient.ofCandidate
              (TraceCorQQuotientCandidate.smul_add
                coefficient
                leftCandidate
                rightCandidate))
            (Eq.trans
              (Eq.symm
                (TraceCorQQuotient.add_ofCandidate
                  (TraceCorQQuotientCandidate.smul
                    coefficient
                    leftCandidate)
                  (TraceCorQQuotientCandidate.smul
                    coefficient
                    rightCandidate)))
              (Eq.trans
                (congrArg
                  (fun firstClass =>
                    TraceCorQQuotient.add
                      firstClass
                      (TraceCorQQuotient.ofCandidate
                        (TraceCorQQuotientCandidate.smul
                          coefficient
                          rightCandidate)))
                  (Eq.symm
                    (TraceCorQQuotient.smul_ofCandidate
                      coefficient
                      leftCandidate)))
                (congrArg
                  (fun secondClass =>
                    TraceCorQQuotient.add
                      (TraceCorQQuotient.smul
                        coefficient
                        (TraceCorQQuotient.ofCandidate leftCandidate))
                      secondClass)
                  (Eq.symm
                    (TraceCorQQuotient.smul_ofCandidate
                      coefficient
                      rightCandidate))))))))

/-- Scaling a quotient trace-correspondence class by one leaves it unchanged. -/
theorem TraceCorQQuotient.one_smul
    (candidateClass : TraceCorQQuotient) :
    TraceCorQQuotient.smul 1 candidateClass =
      candidateClass :=
  Quotient.inductionOn
    candidateClass
    (fun candidate =>
      Eq.trans
        (TraceCorQQuotient.smul_ofCandidate 1 candidate)
        (congrArg
          TraceCorQQuotient.ofCandidate
          (TraceCorQQuotientCandidate.one_smul candidate)))

/-- Successive scalar multiplications compose by multiplying scalars. -/
theorem TraceCorQQuotient.smul_smul
    (leftCoefficient rightCoefficient : Rat)
    (candidateClass : TraceCorQQuotient) :
    TraceCorQQuotient.smul
      leftCoefficient
      (TraceCorQQuotient.smul rightCoefficient candidateClass) =
      TraceCorQQuotient.smul
        (leftCoefficient * rightCoefficient)
        candidateClass :=
  Quotient.inductionOn
    candidateClass
    (fun candidate =>
      Eq.trans
        (congrArg
          (TraceCorQQuotient.smul leftCoefficient)
          (TraceCorQQuotient.smul_ofCandidate
            rightCoefficient
            candidate))
        (Eq.trans
          (TraceCorQQuotient.smul_ofCandidate
            leftCoefficient
            (TraceCorQQuotientCandidate.smul
              rightCoefficient
              candidate))
          (Eq.trans
            (congrArg
              TraceCorQQuotient.ofCandidate
              (TraceCorQQuotientCandidate.smul_smul
                leftCoefficient
                rightCoefficient
                candidate))
            (Eq.symm
              (TraceCorQQuotient.smul_ofCandidate
                (leftCoefficient * rightCoefficient)
                candidate)))))

/-- Scalar multiplication commutes with quotient negation. -/
theorem TraceCorQQuotient.smul_neg
    (coefficient : Rat)
    (candidateClass : TraceCorQQuotient) :
    TraceCorQQuotient.smul
      coefficient
      (TraceCorQQuotient.neg candidateClass) =
      TraceCorQQuotient.neg
        (TraceCorQQuotient.smul coefficient candidateClass) :=
  Eq.trans
    (TraceCorQQuotient.smul_smul
      coefficient
      (-1)
      candidateClass)
    (Eq.trans
      (congrArg
        (fun productCoefficient =>
          TraceCorQQuotient.smul productCoefficient candidateClass)
        (mul_comm coefficient (-1)))
      (Eq.symm
        (TraceCorQQuotient.smul_smul
          (-1)
          coefficient
          candidateClass)))

end AnalyticMotives
end LFunctions
end Boundary
