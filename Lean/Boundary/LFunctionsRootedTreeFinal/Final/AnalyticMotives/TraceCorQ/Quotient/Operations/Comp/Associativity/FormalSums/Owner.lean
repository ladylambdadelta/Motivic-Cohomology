import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Quotient.Operations.Comp.Associativity.SingletonLeft.Owner

/-!
# Associativity for formal-sum quotient representatives

This file owns the finite-list induction proving quotient composition
associativity for direct formal-sum representatives.

The dependency order is:

1. weighted singleton associativity;
2. singleton-left associativity against arbitrary formal sums;
3. induction over the left formal sum.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Quotient composition is associative for direct formal-sum representatives. -/
theorem TraceCorQQuotient.comp_assoc_ofFormalSum
    (left middle right : TraceCorQFormalSum) :
    TraceCorQQuotient.comp
      (TraceCorQQuotient.comp
        (TraceCorQQuotient.ofFormalSum left)
        (TraceCorQQuotient.ofFormalSum middle))
      (TraceCorQQuotient.ofFormalSum right) =
      TraceCorQQuotient.comp
        (TraceCorQQuotient.ofFormalSum left)
        (TraceCorQQuotient.comp
          (TraceCorQQuotient.ofFormalSum middle)
          (TraceCorQQuotient.ofFormalSum right)) :=
  match left with
  | [] =>
      Eq.trans
        (congrArg
          (fun leftClass =>
            TraceCorQQuotient.comp
              (TraceCorQQuotient.comp
                leftClass
                (TraceCorQQuotient.ofFormalSum middle))
              (TraceCorQQuotient.ofFormalSum right))
          TraceCorQQuotient.ofFormalSum_nil)
        (Eq.trans
          (congrArg
            (fun leftMiddleClass =>
              TraceCorQQuotient.comp
                leftMiddleClass
                (TraceCorQQuotient.ofFormalSum right))
            (TraceCorQQuotient.zero_comp
              (TraceCorQQuotient.ofFormalSum middle)))
          (Eq.trans
            (TraceCorQQuotient.zero_comp
              (TraceCorQQuotient.ofFormalSum right))
            (Eq.symm
              (Eq.trans
                (congrArg
                  (fun leftClass =>
                    TraceCorQQuotient.comp
                      leftClass
                      (TraceCorQQuotient.comp
                        (TraceCorQQuotient.ofFormalSum middle)
                        (TraceCorQQuotient.ofFormalSum right)))
                  TraceCorQQuotient.ofFormalSum_nil)
                (TraceCorQQuotient.zero_comp
                  (TraceCorQQuotient.comp
                    (TraceCorQQuotient.ofFormalSum middle)
                    (TraceCorQQuotient.ofFormalSum right)))))))
  | (leftCoefficient, leftGenerator) :: leftTail =>
      Eq.trans
        (congrArg
          (fun leftClass =>
            TraceCorQQuotient.comp
              (TraceCorQQuotient.comp
                leftClass
                (TraceCorQQuotient.ofFormalSum middle))
              (TraceCorQQuotient.ofFormalSum right))
          (TraceCorQQuotient.ofFormalSum_cons
            leftCoefficient
            leftGenerator
            leftTail))
        (Eq.trans
          (congrArg
            (fun leftMiddleClass =>
              TraceCorQQuotient.comp
                leftMiddleClass
                (TraceCorQQuotient.ofFormalSum right))
            (TraceCorQQuotient.add_comp
              (TraceCorQQuotient.singleton
                leftCoefficient
                leftGenerator)
              (TraceCorQQuotient.ofFormalSum leftTail)
              (TraceCorQQuotient.ofFormalSum middle)))
          (Eq.trans
            (TraceCorQQuotient.add_comp
              (TraceCorQQuotient.comp
                (TraceCorQQuotient.singleton
                  leftCoefficient
                  leftGenerator)
                (TraceCorQQuotient.ofFormalSum middle))
              (TraceCorQQuotient.comp
                (TraceCorQQuotient.ofFormalSum leftTail)
                (TraceCorQQuotient.ofFormalSum middle))
              (TraceCorQQuotient.ofFormalSum right))
            (Eq.trans
              (congrArg
                (fun tailClass =>
                  TraceCorQQuotient.add
                    (TraceCorQQuotient.comp
                      (TraceCorQQuotient.comp
                        (TraceCorQQuotient.singleton
                          leftCoefficient
                          leftGenerator)
                        (TraceCorQQuotient.ofFormalSum middle))
                      (TraceCorQQuotient.ofFormalSum right))
                    tailClass)
                (TraceCorQQuotient.comp_assoc_ofFormalSum
                  leftTail
                  middle
                  right))
              (Eq.trans
                (congrArg
                  (fun headClass =>
                    TraceCorQQuotient.add
                      headClass
                      (TraceCorQQuotient.comp
                        (TraceCorQQuotient.ofFormalSum leftTail)
                        (TraceCorQQuotient.comp
                          (TraceCorQQuotient.ofFormalSum middle)
                          (TraceCorQQuotient.ofFormalSum right))))
                  (TraceCorQQuotient.comp_assoc_singleton_ofFormalSum_ofFormalSum
                    leftCoefficient
                    leftGenerator
                    middle
                    right))
                (Eq.symm
                  (Eq.trans
                    (congrArg
                      (fun leftClass =>
                        TraceCorQQuotient.comp
                          leftClass
                          (TraceCorQQuotient.comp
                            (TraceCorQQuotient.ofFormalSum middle)
                            (TraceCorQQuotient.ofFormalSum right)))
                      (TraceCorQQuotient.ofFormalSum_cons
                        leftCoefficient
                        leftGenerator
                        leftTail))
                    (TraceCorQQuotient.add_comp
                      (TraceCorQQuotient.singleton
                        leftCoefficient
                        leftGenerator)
                      (TraceCorQQuotient.ofFormalSum leftTail)
                      (TraceCorQQuotient.comp
                        (TraceCorQQuotient.ofFormalSum middle)
                        (TraceCorQQuotient.ofFormalSum right)))))))))

/-- Quotient composition is associative. -/
theorem TraceCorQQuotient.comp_assoc
    (left middle right : TraceCorQQuotient) :
    TraceCorQQuotient.comp
      (TraceCorQQuotient.comp left middle)
      right =
      TraceCorQQuotient.comp
        left
        (TraceCorQQuotient.comp middle right) :=
  Quotient.inductionOn₃
    left
    middle
    right
    (fun leftCandidate middleCandidate rightCandidate =>
      Eq.trans
        (congrArg
          (fun leftClass =>
            TraceCorQQuotient.comp
              (TraceCorQQuotient.comp
                leftClass
                (TraceCorQQuotient.ofCandidate middleCandidate))
              (TraceCorQQuotient.ofCandidate rightCandidate))
          (TraceCorQQuotient.ofCandidate_eq_ofFormalSum
            leftCandidate))
        (Eq.trans
          (congrArg
            (fun middleClass =>
              TraceCorQQuotient.comp
                (TraceCorQQuotient.comp
                  (TraceCorQQuotient.ofFormalSum leftCandidate.formalSum)
                  middleClass)
                (TraceCorQQuotient.ofCandidate rightCandidate))
            (TraceCorQQuotient.ofCandidate_eq_ofFormalSum
              middleCandidate))
          (Eq.trans
            (congrArg
              (fun rightClass =>
                TraceCorQQuotient.comp
                  (TraceCorQQuotient.comp
                    (TraceCorQQuotient.ofFormalSum leftCandidate.formalSum)
                    (TraceCorQQuotient.ofFormalSum middleCandidate.formalSum))
                  rightClass)
              (TraceCorQQuotient.ofCandidate_eq_ofFormalSum
                rightCandidate))
            (Eq.trans
              (TraceCorQQuotient.comp_assoc_ofFormalSum
                leftCandidate.formalSum
                middleCandidate.formalSum
                rightCandidate.formalSum)
              (Eq.symm
                (Eq.trans
                  (congrArg
                    (fun leftClass =>
                      TraceCorQQuotient.comp
                        leftClass
                        (TraceCorQQuotient.comp
                          (TraceCorQQuotient.ofCandidate middleCandidate)
                          (TraceCorQQuotient.ofCandidate rightCandidate)))
                    (TraceCorQQuotient.ofCandidate_eq_ofFormalSum
                      leftCandidate))
                  (Eq.trans
                    (congrArg
                      (fun middleClass =>
                        TraceCorQQuotient.comp
                          (TraceCorQQuotient.ofFormalSum leftCandidate.formalSum)
                          (TraceCorQQuotient.comp
                            middleClass
                            (TraceCorQQuotient.ofCandidate rightCandidate)))
                      (TraceCorQQuotient.ofCandidate_eq_ofFormalSum
                        middleCandidate))
                    (congrArg
                      (fun rightClass =>
                        TraceCorQQuotient.comp
                          (TraceCorQQuotient.ofFormalSum leftCandidate.formalSum)
                          (TraceCorQQuotient.comp
                            (TraceCorQQuotient.ofFormalSum
                              middleCandidate.formalSum)
                            rightClass))
                      (TraceCorQQuotient.ofCandidate_eq_ofFormalSum
                        rightCandidate)))))))))

end AnalyticMotives
end LFunctions
end Boundary
