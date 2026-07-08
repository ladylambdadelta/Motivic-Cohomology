import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Quotient.Operations.Add.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Quotient.Operations.Zero.Owner

/-!
# Additive laws for quotient trace correspondences

This file proves the first additive laws for quotient trace-correspondence
classes by quotient induction from the corresponding candidate laws.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- The empty quotient class is a left zero for quotient addition. -/
theorem TraceCorQQuotient.empty_add
    (candidateClass : TraceCorQQuotient) :
    TraceCorQQuotient.add
      (TraceCorQQuotient.ofCandidate TraceCorQQuotientCandidate.empty)
      candidateClass =
      candidateClass :=
  Quotient.inductionOn
    candidateClass
    (fun candidate =>
      Eq.trans
        (TraceCorQQuotient.add_ofCandidate
          TraceCorQQuotientCandidate.empty
          candidate)
        (congrArg
          TraceCorQQuotient.ofCandidate
          (TraceCorQQuotientCandidate.empty_add candidate)))

/-- The empty quotient class is a right zero for quotient addition. -/
theorem TraceCorQQuotient.add_empty
    (candidateClass : TraceCorQQuotient) :
    TraceCorQQuotient.add
      candidateClass
      (TraceCorQQuotient.ofCandidate TraceCorQQuotientCandidate.empty) =
      candidateClass :=
  Quotient.inductionOn
    candidateClass
    (fun candidate =>
      Eq.trans
        (TraceCorQQuotient.add_ofCandidate
          candidate
          TraceCorQQuotientCandidate.empty)
        (congrArg
          TraceCorQQuotient.ofCandidate
          (TraceCorQQuotientCandidate.add_empty candidate)))

/-- Addition of quotient trace-correspondence classes is associative. -/
theorem TraceCorQQuotient.add_assoc
    (first second third : TraceCorQQuotient) :
    TraceCorQQuotient.add
      (TraceCorQQuotient.add first second)
      third =
      TraceCorQQuotient.add
        first
        (TraceCorQQuotient.add second third) :=
  Quotient.inductionOn₃
    first
    second
    third
    (fun firstCandidate secondCandidate thirdCandidate =>
      Eq.trans
        (congrArg
          (fun candidateClass =>
            TraceCorQQuotient.add
              candidateClass
              (TraceCorQQuotient.ofCandidate thirdCandidate))
          (TraceCorQQuotient.add_ofCandidate
            firstCandidate
            secondCandidate))
        (Eq.trans
          (TraceCorQQuotient.add_ofCandidate
            (TraceCorQQuotientCandidate.add
              firstCandidate
              secondCandidate)
            thirdCandidate)
          (Eq.trans
            (congrArg
              TraceCorQQuotient.ofCandidate
              (TraceCorQQuotientCandidate.add_assoc
                firstCandidate
                secondCandidate
                thirdCandidate))
            (Eq.trans
              (Eq.symm
                (TraceCorQQuotient.add_ofCandidate
                  firstCandidate
                  (TraceCorQQuotientCandidate.add
                    secondCandidate
                    thirdCandidate)))
              (congrArg
                (fun candidateClass =>
                  TraceCorQQuotient.add
                    (TraceCorQQuotient.ofCandidate firstCandidate)
                    candidateClass)
                (Eq.symm
                  (TraceCorQQuotient.add_ofCandidate
                    secondCandidate
                    thirdCandidate)))))))

/-- Addition of quotient trace-correspondence classes is commutative. -/
theorem TraceCorQQuotient.add_comm
    (left right : TraceCorQQuotient) :
    TraceCorQQuotient.add left right =
      TraceCorQQuotient.add right left :=
  Quotient.inductionOn₂
    left
    right
    (fun leftCandidate rightCandidate =>
      Eq.trans
        (TraceCorQQuotient.add_ofCandidate
          leftCandidate
          rightCandidate)
        (Eq.trans
          (TraceCorQQuotient.sound_permFormalSum
            (TraceCorQRelationLedger.append
              leftCandidate.ledger
              rightCandidate.ledger)
            ((List.Perm.of_eq
              (TraceCorQQuotientCandidate.add_formalSum
                leftCandidate
                rightCandidate)).trans
              (List.perm_append_comm.trans
                (List.Perm.of_eq
                  (Eq.symm
                    (TraceCorQQuotientCandidate.add_formalSum
                      rightCandidate
                      leftCandidate))))))
          (Eq.symm
            (TraceCorQQuotient.add_ofCandidate
              rightCandidate
              leftCandidate))))

/-- Reassociate four quotient summands by swapping the middle two terms. -/
theorem TraceCorQQuotient.add_add_add_comm
    (first second third fourth : TraceCorQQuotient) :
    TraceCorQQuotient.add
      (TraceCorQQuotient.add first second)
      (TraceCorQQuotient.add third fourth) =
      TraceCorQQuotient.add
        (TraceCorQQuotient.add first third)
        (TraceCorQQuotient.add second fourth) :=
  Eq.trans
    (TraceCorQQuotient.add_assoc
      first
      second
      (TraceCorQQuotient.add third fourth))
    (Eq.trans
      (congrArg
        (TraceCorQQuotient.add first)
        (Eq.symm
          (TraceCorQQuotient.add_assoc second third fourth)))
      (Eq.trans
        (congrArg
          (fun middle =>
            TraceCorQQuotient.add
              first
              (TraceCorQQuotient.add middle fourth))
          (TraceCorQQuotient.add_comm second third))
        (Eq.trans
          (congrArg
            (TraceCorQQuotient.add first)
            (TraceCorQQuotient.add_assoc third second fourth))
          (Eq.symm
            (TraceCorQQuotient.add_assoc
              first
              third
              (TraceCorQQuotient.add second fourth))))))

/-- Named-zero left law for quotient addition. -/
theorem TraceCorQQuotient.zero_add
    (candidateClass : TraceCorQQuotient) :
    TraceCorQQuotient.add
      TraceCorQQuotient.zero
      candidateClass =
      candidateClass :=
  TraceCorQQuotient.empty_add candidateClass

/-- Named-zero right law for quotient addition. -/
theorem TraceCorQQuotient.add_zero
    (candidateClass : TraceCorQQuotient) :
    TraceCorQQuotient.add
      candidateClass
      TraceCorQQuotient.zero =
      candidateClass :=
  TraceCorQQuotient.add_empty candidateClass

end AnalyticMotives
end LFunctions
end Boundary
