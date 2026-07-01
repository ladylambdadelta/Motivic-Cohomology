import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Quotient.Operations.Comp.AssociativitySupport.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Quotient.Operations.Comp.Laws.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Quotient.Operations.FormalSumClass.Owner

/-!
# Associativity with a singleton left input

This file owns the first induction layer for quotient composition
associativity: one weighted singleton on the left, then arbitrary formal sums
in the middle and right slots.

The proof is built from weighted singleton associativity plus the already
proved distributivity of quotient composition over quotient addition.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/--
Composition is associative for two weighted singleton inputs followed by an
arbitrary formal-sum representative.
-/
theorem TraceCorQQuotient.comp_assoc_singleton_singleton_ofFormalSum
    (firstCoefficient secondCoefficient : Rat)
    (first second : TraceCorQGenerator)
    (right : TraceCorQFormalSum) :
    TraceCorQQuotient.comp
      (TraceCorQQuotient.comp
        (TraceCorQQuotient.singleton firstCoefficient first)
        (TraceCorQQuotient.singleton secondCoefficient second))
      (TraceCorQQuotient.ofFormalSum right) =
      TraceCorQQuotient.comp
        (TraceCorQQuotient.singleton firstCoefficient first)
        (TraceCorQQuotient.comp
          (TraceCorQQuotient.singleton secondCoefficient second)
          (TraceCorQQuotient.ofFormalSum right)) :=
  match right with
  | [] =>
      Eq.trans
        (TraceCorQQuotient.comp_zero
          (TraceCorQQuotient.comp
            (TraceCorQQuotient.singleton firstCoefficient first)
            (TraceCorQQuotient.singleton secondCoefficient second)))
        (Eq.symm
          (Eq.trans
            (congrArg
              (fun rightClass =>
                TraceCorQQuotient.comp
                  (TraceCorQQuotient.singleton firstCoefficient first)
                  rightClass)
              (TraceCorQQuotient.comp_zero
                (TraceCorQQuotient.singleton secondCoefficient second)))
            (TraceCorQQuotient.comp_zero
              (TraceCorQQuotient.singleton firstCoefficient first))))
  | (rightCoefficient, rightGenerator) :: rightTail =>
      Eq.trans
        (congrArg
          (fun rightClass =>
            TraceCorQQuotient.comp
              (TraceCorQQuotient.comp
                (TraceCorQQuotient.singleton firstCoefficient first)
                (TraceCorQQuotient.singleton secondCoefficient second))
              rightClass)
          (TraceCorQQuotient.ofFormalSum_cons
            rightCoefficient
            rightGenerator
            rightTail))
        (Eq.trans
          (TraceCorQQuotient.comp_add
            (TraceCorQQuotient.comp
              (TraceCorQQuotient.singleton firstCoefficient first)
              (TraceCorQQuotient.singleton secondCoefficient second))
            (TraceCorQQuotient.singleton rightCoefficient rightGenerator)
            (TraceCorQQuotient.ofFormalSum rightTail))
          (Eq.trans
            (congrArg
              (fun tailClass =>
                TraceCorQQuotient.add
                  (TraceCorQQuotient.comp
                    (TraceCorQQuotient.comp
                      (TraceCorQQuotient.singleton firstCoefficient first)
                      (TraceCorQQuotient.singleton secondCoefficient second))
                    (TraceCorQQuotient.singleton
                      rightCoefficient
                      rightGenerator))
                  tailClass)
              (TraceCorQQuotient.comp_assoc_singleton_singleton_ofFormalSum
                firstCoefficient
                secondCoefficient
                first
                second
                rightTail))
            (Eq.trans
              (congrArg
                (fun headClass =>
                  TraceCorQQuotient.add
                    headClass
                    (TraceCorQQuotient.comp
                      (TraceCorQQuotient.singleton firstCoefficient first)
                      (TraceCorQQuotient.comp
                        (TraceCorQQuotient.singleton secondCoefficient second)
                        (TraceCorQQuotient.ofFormalSum rightTail))))
                (TraceCorQQuotient.comp_assoc_singleton
                  firstCoefficient
                  secondCoefficient
                  rightCoefficient
                  first
                  second
                  rightGenerator))
              (Eq.symm
                (Eq.trans
                  (TraceCorQQuotient.comp_add
                    (TraceCorQQuotient.singleton firstCoefficient first)
                    (TraceCorQQuotient.comp
                      (TraceCorQQuotient.singleton secondCoefficient second)
                      (TraceCorQQuotient.singleton
                        rightCoefficient
                        rightGenerator))
                    (TraceCorQQuotient.comp
                      (TraceCorQQuotient.singleton secondCoefficient second)
                      (TraceCorQQuotient.ofFormalSum rightTail)))
                  (congrArg
                    (fun rightClass =>
                      TraceCorQQuotient.comp
                        (TraceCorQQuotient.singleton firstCoefficient first)
                        rightClass)
                    (Eq.symm
                      (Eq.trans
                        (TraceCorQQuotient.comp_add
                          (TraceCorQQuotient.singleton secondCoefficient second)
                          (TraceCorQQuotient.singleton
                            rightCoefficient
                            rightGenerator)
                          (TraceCorQQuotient.ofFormalSum rightTail))
                        (congrArg
                          (TraceCorQQuotient.comp
                            (TraceCorQQuotient.singleton secondCoefficient second))
                          (Eq.symm
                            (TraceCorQQuotient.ofFormalSum_cons
                              rightCoefficient
                              rightGenerator
                              rightTail)))))))))))

/--
Composition is associative for one weighted singleton input followed by two
arbitrary formal-sum representatives.
-/
theorem TraceCorQQuotient.comp_assoc_singleton_ofFormalSum_ofFormalSum
    (firstCoefficient : Rat)
    (first : TraceCorQGenerator)
    (middle right : TraceCorQFormalSum) :
    TraceCorQQuotient.comp
      (TraceCorQQuotient.comp
        (TraceCorQQuotient.singleton firstCoefficient first)
        (TraceCorQQuotient.ofFormalSum middle))
      (TraceCorQQuotient.ofFormalSum right) =
      TraceCorQQuotient.comp
        (TraceCorQQuotient.singleton firstCoefficient first)
        (TraceCorQQuotient.comp
          (TraceCorQQuotient.ofFormalSum middle)
          (TraceCorQQuotient.ofFormalSum right)) :=
  match middle with
  | [] =>
      Eq.trans
        (congrArg
          (fun middleClass =>
            TraceCorQQuotient.comp
              (TraceCorQQuotient.comp
                (TraceCorQQuotient.singleton firstCoefficient first)
                middleClass)
              (TraceCorQQuotient.ofFormalSum right))
          TraceCorQQuotient.ofFormalSum_nil)
        (Eq.trans
          (congrArg
            (fun leftClass =>
              TraceCorQQuotient.comp
                leftClass
                (TraceCorQQuotient.ofFormalSum right))
            (TraceCorQQuotient.comp_zero
              (TraceCorQQuotient.singleton firstCoefficient first)))
          (Eq.trans
            (TraceCorQQuotient.zero_comp
              (TraceCorQQuotient.ofFormalSum right))
            (Eq.symm
              (Eq.trans
                (congrArg
                  (fun rightClass =>
                    TraceCorQQuotient.comp
                      (TraceCorQQuotient.singleton firstCoefficient first)
                      rightClass)
                  (Eq.trans
                    (congrArg
                      (fun middleClass =>
                        TraceCorQQuotient.comp
                          middleClass
                          (TraceCorQQuotient.ofFormalSum right))
                      TraceCorQQuotient.ofFormalSum_nil)
                    (TraceCorQQuotient.zero_comp
                      (TraceCorQQuotient.ofFormalSum right))))
                (TraceCorQQuotient.comp_zero
                  (TraceCorQQuotient.singleton firstCoefficient first))))))
  | (middleCoefficient, middleGenerator) :: middleTail =>
      Eq.trans
        (congrArg
          (fun middleClass =>
            TraceCorQQuotient.comp
              (TraceCorQQuotient.comp
                (TraceCorQQuotient.singleton firstCoefficient first)
                middleClass)
              (TraceCorQQuotient.ofFormalSum right))
          (TraceCorQQuotient.ofFormalSum_cons
            middleCoefficient
            middleGenerator
            middleTail))
        (Eq.trans
          (congrArg
            (fun leftClass =>
              TraceCorQQuotient.comp
                leftClass
                (TraceCorQQuotient.ofFormalSum right))
            (TraceCorQQuotient.comp_add
              (TraceCorQQuotient.singleton firstCoefficient first)
              (TraceCorQQuotient.singleton
                middleCoefficient
                middleGenerator)
              (TraceCorQQuotient.ofFormalSum middleTail)))
          (Eq.trans
            (TraceCorQQuotient.add_comp
              (TraceCorQQuotient.comp
                (TraceCorQQuotient.singleton firstCoefficient first)
                (TraceCorQQuotient.singleton
                  middleCoefficient
                  middleGenerator))
              (TraceCorQQuotient.comp
                (TraceCorQQuotient.singleton firstCoefficient first)
                (TraceCorQQuotient.ofFormalSum middleTail))
              (TraceCorQQuotient.ofFormalSum right))
            (Eq.trans
              (congrArg
                (fun tailClass =>
                  TraceCorQQuotient.add
                    (TraceCorQQuotient.comp
                      (TraceCorQQuotient.comp
                        (TraceCorQQuotient.singleton firstCoefficient first)
                        (TraceCorQQuotient.singleton
                          middleCoefficient
                          middleGenerator))
                      (TraceCorQQuotient.ofFormalSum right))
                    tailClass)
                (TraceCorQQuotient.comp_assoc_singleton_ofFormalSum_ofFormalSum
                  firstCoefficient
                  first
                  middleTail
                  right))
              (Eq.trans
                (congrArg
                  (fun headClass =>
                    TraceCorQQuotient.add
                      headClass
                      (TraceCorQQuotient.comp
                        (TraceCorQQuotient.singleton firstCoefficient first)
                        (TraceCorQQuotient.comp
                          (TraceCorQQuotient.ofFormalSum middleTail)
                          (TraceCorQQuotient.ofFormalSum right))))
                  (TraceCorQQuotient.comp_assoc_singleton_singleton_ofFormalSum
                    firstCoefficient
                    middleCoefficient
                    first
                    middleGenerator
                    right))
                (Eq.symm
                  (Eq.trans
                    (TraceCorQQuotient.comp_add
                      (TraceCorQQuotient.singleton firstCoefficient first)
                      (TraceCorQQuotient.comp
                        (TraceCorQQuotient.singleton
                          middleCoefficient
                          middleGenerator)
                        (TraceCorQQuotient.ofFormalSum right))
                      (TraceCorQQuotient.comp
                        (TraceCorQQuotient.ofFormalSum middleTail)
                        (TraceCorQQuotient.ofFormalSum right)))
                    (congrArg
                      (fun rightClass =>
                        TraceCorQQuotient.comp
                          (TraceCorQQuotient.singleton firstCoefficient first)
                          rightClass)
                      (Eq.symm
                        (Eq.trans
                          (TraceCorQQuotient.add_comp
                            (TraceCorQQuotient.singleton
                              middleCoefficient
                              middleGenerator)
                            (TraceCorQQuotient.ofFormalSum middleTail)
                            (TraceCorQQuotient.ofFormalSum right))
                          (congrArg
                            (fun middleClass =>
                              TraceCorQQuotient.comp
                                middleClass
                                (TraceCorQQuotient.ofFormalSum right))
                            (Eq.symm
                              (TraceCorQQuotient.ofFormalSum_cons
                                middleCoefficient
                                middleGenerator
                                middleTail)))))))))))

end AnalyticMotives
end LFunctions
end Boundary
