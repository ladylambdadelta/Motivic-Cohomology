import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Quotient.Operations.Add.Laws.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Quotient.Operations.FormalSumClass.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Quotient.Operations.Neg.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Quotient.Operations.Singleton.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Quotient.Operations.Smul.Laws.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Quotient.Operations.Zero.Owner

/-!
# Negation laws for quotient trace correspondences

This file starts the additive inverse theory from the concrete cancellation
relation: adjacent opposite rational multiples of one generator cancel.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- The rational coefficient `(-1) * (-1)` is `1`. -/
theorem TraceCorQ.neg_one_mul_neg_one :
    (-1 : Rat) * (-1 : Rat) = 1 :=
  Eq.trans
    (neg_mul_neg 1 1)
    (one_mul 1)

/-- Negating the zero quotient class gives zero. -/
theorem TraceCorQQuotient.neg_zero :
    TraceCorQQuotient.neg TraceCorQQuotient.zero =
      TraceCorQQuotient.zero :=
  TraceCorQQuotient.smul_zero (-1)

/-- Negation distributes over quotient addition. -/
theorem TraceCorQQuotient.neg_add
    (left right : TraceCorQQuotient) :
    TraceCorQQuotient.neg
      (TraceCorQQuotient.add left right) =
      TraceCorQQuotient.add
        (TraceCorQQuotient.neg left)
        (TraceCorQQuotient.neg right) :=
  TraceCorQQuotient.smul_add (-1) left right

/-- Quotient negation is involutive. -/
theorem TraceCorQQuotient.neg_neg
    (candidateClass : TraceCorQQuotient) :
    TraceCorQQuotient.neg
      (TraceCorQQuotient.neg candidateClass) =
      candidateClass :=
  Eq.trans
    (TraceCorQQuotient.smul_smul
      (-1)
      (-1)
      candidateClass)
    (Eq.trans
      (congrArg
        (fun coefficient =>
          TraceCorQQuotient.smul coefficient candidateClass)
        TraceCorQ.neg_one_mul_neg_one)
      (TraceCorQQuotient.one_smul candidateClass))

/-- Negating a singleton negates its coefficient. -/
theorem TraceCorQQuotient.neg_singleton_eq_singleton_neg
    (coefficient : Rat)
    (generator : TraceCorQGenerator) :
    TraceCorQQuotient.neg
      (TraceCorQQuotient.singleton coefficient generator) =
      TraceCorQQuotient.singleton (-coefficient) generator :=
  Eq.trans
    (TraceCorQQuotient.smul_singleton
      (-1)
      coefficient
      generator)
    (congrArg
      (fun negCoefficient =>
        TraceCorQQuotient.singleton negCoefficient generator)
      (neg_one_mul coefficient))

/-- The formal singleton pair `[-c, c]` matches the cancellation source. -/
theorem TraceCorQFormalSum.neg_singleton_add_singleton_cancel_source
    (coefficient : Rat)
    (generator : TraceCorQGenerator) :
    TraceCorQFormalSum.add
      (TraceCorQFormalSum.singleton (-coefficient) generator)
      (TraceCorQFormalSum.singleton coefficient generator) =
      [(-coefficient, generator), (-(-coefficient), generator)] :=
  congrArg
    (fun secondCoefficient =>
      [(-coefficient, generator), (secondCoefficient, generator)])
    (Eq.symm (neg_neg coefficient))

/-- A negative singleton plus the singleton itself cancels in the quotient. -/
theorem TraceCorQQuotient.neg_singleton_add_singleton
    (coefficient : Rat)
    (generator : TraceCorQGenerator) :
    TraceCorQQuotient.add
      (TraceCorQQuotient.singleton (-coefficient) generator)
      (TraceCorQQuotient.singleton coefficient generator) =
      TraceCorQQuotient.zero :=
  Eq.trans
    (TraceCorQQuotient.add_ofCandidate
      (TraceCorQQuotient.singletonCandidate
        (-coefficient)
        generator
        TraceCorQRelationLedger.empty)
      (TraceCorQQuotient.singletonCandidate
        coefficient
        generator
        TraceCorQRelationLedger.empty))
    (Eq.trans
      (TraceCorQQuotient.sound_sameFormalSum
        (TraceCorQRelationLedger.append
          TraceCorQRelationLedger.empty
          TraceCorQRelationLedger.empty)
        (TraceCorQFormalSum.neg_singleton_add_singleton_cancel_source
          coefficient
          generator))
      (TraceCorQQuotient.sound_cancelAdjacentOpposite
        (TraceCorQRelationLedger.append
          TraceCorQRelationLedger.empty
          TraceCorQRelationLedger.empty)
        []
        []
        (-coefficient)
        generator))

/-- A singleton plus its negative cancels in the quotient. -/
theorem TraceCorQQuotient.singleton_add_neg_singleton
    (coefficient : Rat)
    (generator : TraceCorQGenerator) :
    TraceCorQQuotient.add
      (TraceCorQQuotient.singleton coefficient generator)
      (TraceCorQQuotient.singleton (-coefficient) generator) =
      TraceCorQQuotient.zero :=
  Eq.trans
    (TraceCorQQuotient.add_comm
      (TraceCorQQuotient.singleton coefficient generator)
      (TraceCorQQuotient.singleton (-coefficient) generator))
    (TraceCorQQuotient.neg_singleton_add_singleton
      coefficient
      generator)

/-- A direct formal-sum class has its negation as a left additive inverse. -/
theorem TraceCorQQuotient.neg_ofFormalSum_add_ofFormalSum
    (formalSum : TraceCorQFormalSum) :
    TraceCorQQuotient.add
      (TraceCorQQuotient.neg
        (TraceCorQQuotient.ofFormalSum formalSum))
      (TraceCorQQuotient.ofFormalSum formalSum) =
      TraceCorQQuotient.zero :=
  match formalSum with
  | [] =>
      Eq.trans
        (congrArg
          (fun class =>
            TraceCorQQuotient.add
              (TraceCorQQuotient.neg class)
              class)
          TraceCorQQuotient.ofFormalSum_nil)
        (Eq.trans
          (congrArg
            (fun negClass =>
              TraceCorQQuotient.add
                negClass
                TraceCorQQuotient.zero)
            TraceCorQQuotient.neg_zero)
          (TraceCorQQuotient.add_zero TraceCorQQuotient.zero))
  | (coefficient, generator) :: tail =>
      Eq.trans
        (congrArg
          (fun class =>
            TraceCorQQuotient.add
              (TraceCorQQuotient.neg class)
              class)
          (TraceCorQQuotient.ofFormalSum_cons
            coefficient
            generator
            tail))
        (Eq.trans
          (congrArg
            (fun negClass =>
              TraceCorQQuotient.add
                negClass
                (TraceCorQQuotient.add
                  (TraceCorQQuotient.singleton coefficient generator)
                  (TraceCorQQuotient.ofFormalSum tail)))
            (TraceCorQQuotient.neg_add
              (TraceCorQQuotient.singleton coefficient generator)
              (TraceCorQQuotient.ofFormalSum tail)))
          (Eq.trans
            (TraceCorQQuotient.add_add_add_comm
              (TraceCorQQuotient.neg
                (TraceCorQQuotient.singleton coefficient generator))
              (TraceCorQQuotient.neg
                (TraceCorQQuotient.ofFormalSum tail))
              (TraceCorQQuotient.singleton coefficient generator)
              (TraceCorQQuotient.ofFormalSum tail))
            (Eq.trans
              (congrArg
                (fun leftClass =>
                  TraceCorQQuotient.add
                    leftClass
                    (TraceCorQQuotient.add
                      (TraceCorQQuotient.neg
                        (TraceCorQQuotient.ofFormalSum tail))
                      (TraceCorQQuotient.ofFormalSum tail)))
                (Eq.trans
                  (congrArg
                    (fun negSingleton =>
                      TraceCorQQuotient.add
                        negSingleton
                        (TraceCorQQuotient.singleton coefficient generator))
                    (TraceCorQQuotient.neg_singleton_eq_singleton_neg
                      coefficient
                      generator))
                  (TraceCorQQuotient.neg_singleton_add_singleton
                    coefficient
                    generator)))
              (Eq.trans
                (congrArg
                  (TraceCorQQuotient.add TraceCorQQuotient.zero)
                  (TraceCorQQuotient.neg_ofFormalSum_add_ofFormalSum tail))
                (TraceCorQQuotient.zero_add TraceCorQQuotient.zero)))))

/-- Every quotient class has its negation as a left additive inverse. -/
theorem TraceCorQQuotient.neg_add_self
    (candidateClass : TraceCorQQuotient) :
    TraceCorQQuotient.add
      (TraceCorQQuotient.neg candidateClass)
      candidateClass =
      TraceCorQQuotient.zero :=
  Quotient.inductionOn
    candidateClass
    (fun candidate =>
      Eq.trans
        (congrArg
          (fun class =>
            TraceCorQQuotient.add
              (TraceCorQQuotient.neg class)
              class)
          (TraceCorQQuotient.ofCandidate_eq_ofFormalSum candidate))
        (TraceCorQQuotient.neg_ofFormalSum_add_ofFormalSum
          candidate.formalSum))

/-- Every quotient class has its negation as a right additive inverse. -/
theorem TraceCorQQuotient.add_neg_self
    (candidateClass : TraceCorQQuotient) :
    TraceCorQQuotient.add
      candidateClass
      (TraceCorQQuotient.neg candidateClass) =
      TraceCorQQuotient.zero :=
  Eq.trans
    (TraceCorQQuotient.add_comm
      candidateClass
      (TraceCorQQuotient.neg candidateClass))
    (TraceCorQQuotient.neg_add_self candidateClass)

/-- Quotient addition cancels a common left summand. -/
theorem TraceCorQQuotient.add_left_cancel
    (left right tail : TraceCorQQuotient)
    (left_right_eq_left_tail :
      TraceCorQQuotient.add left right =
        TraceCorQQuotient.add left tail) :
    right = tail :=
  Eq.trans
    (Eq.symm (TraceCorQQuotient.zero_add right))
    (Eq.trans
      (congrArg
        (fun zeroClass =>
          TraceCorQQuotient.add zeroClass right)
        (Eq.symm (TraceCorQQuotient.neg_add_self left)))
      (Eq.trans
        (TraceCorQQuotient.add_assoc
          (TraceCorQQuotient.neg left)
          left
          right)
        (Eq.trans
          (congrArg
            (TraceCorQQuotient.add (TraceCorQQuotient.neg left))
            left_right_eq_left_tail)
          (Eq.trans
            (Eq.symm
              (TraceCorQQuotient.add_assoc
                (TraceCorQQuotient.neg left)
                left
                tail))
            (Eq.trans
              (congrArg
                (fun zeroClass =>
                  TraceCorQQuotient.add zeroClass tail)
                (TraceCorQQuotient.neg_add_self left))
              (TraceCorQQuotient.zero_add tail))))))

/-- Quotient addition cancels a common right summand. -/
theorem TraceCorQQuotient.add_right_cancel
    (left right tail : TraceCorQQuotient)
    (left_tail_eq_right_tail :
      TraceCorQQuotient.add left tail =
        TraceCorQQuotient.add right tail) :
    left = right :=
  TraceCorQQuotient.add_left_cancel
    tail
    left
    right
    (Eq.trans
      (TraceCorQQuotient.add_comm tail left)
      (Eq.trans
        left_tail_eq_right_tail
        (TraceCorQQuotient.add_comm right tail)))

end AnalyticMotives
end LFunctions
end Boundary
