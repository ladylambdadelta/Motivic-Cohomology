import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Quotient.Operations.Singleton.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Quotient.Operations.Zero.Owner

/-!
# Zero-coefficient singleton laws

This file owns the first coefficient-normalization payoff from adjacent
same-generator coefficient combination: a singleton with rational coefficient
zero represents the zero quotient class.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- The pair of zero-coefficient copies matches the adjacent-opposite source. -/
theorem TraceCorQFormalSum.zero_zero_pair_eq_zero_neg_zero_pair
    (generator : TraceCorQGenerator) :
    ((0, generator) :: (0, generator) :: []) =
      ((0, generator) :: (-(0 : Rat), generator) :: []) :=
  congrArg
    (fun coefficient =>
      (0, generator) :: (coefficient, generator) :: [])
    (Eq.symm
      (neg_zero : -(0 : Rat) = 0))

/-- The combined coefficient of two zero terms is zero. -/
theorem TraceCorQFormalSum.zero_add_zero_singleton_eq_zero_singleton
    (generator : TraceCorQGenerator) :
    TraceCorQFormalSum.singleton ((0 : Rat) + 0) generator =
      TraceCorQFormalSum.singleton 0 generator :=
  congrArg
    (fun coefficient =>
      TraceCorQFormalSum.singleton coefficient generator)
    (_root_.zero_add (0 : Rat))

/-- The adjacent pair `0 + 0` represents the zero-coefficient singleton. -/
theorem TraceCorQQuotient.zero_zero_pair_eq_singleton_zero
    (generator : TraceCorQGenerator) :
    TraceCorQQuotient.ofCandidate
        (TraceCorQQuotientInput.ofFormalSumLedger
          ([] ++ ((0, generator) :: (0, generator) :: []))
          TraceCorQRelationLedger.empty) =
      TraceCorQQuotient.singleton 0 generator :=
  Eq.trans
    (TraceCorQQuotient.sound_combineAdjacentSame
      TraceCorQRelationLedger.empty
      []
      []
      0
      0
      generator)
    (TraceCorQQuotient.sound_sameFormalSum
      TraceCorQRelationLedger.empty
      (left :=
        TraceCorQQuotientInput.ofFormalSumLedger
          ([] ++ (((0 : Rat) + 0, generator) :: []))
          TraceCorQRelationLedger.empty)
      (right :=
        TraceCorQQuotient.singletonCandidate
          0
          generator
          TraceCorQRelationLedger.empty)
      (show
        ([] ++ (((0 : Rat) + 0, generator) :: []) : TraceCorQFormalSum) =
          TraceCorQFormalSum.singleton 0 generator from
        Eq.trans
          (List.nil_append
            (((0 : Rat) + 0, generator) :: []))
          (TraceCorQFormalSum.zero_add_zero_singleton_eq_zero_singleton
            generator)))

/-- The adjacent pair `0 + 0` matches the adjacent-opposite cancellation source. -/
theorem TraceCorQQuotient.zero_zero_pair_eq_zero_neg_zero_pair
    (generator : TraceCorQGenerator) :
    TraceCorQQuotient.ofCandidate
        (TraceCorQQuotientInput.ofFormalSumLedger
          ([] ++ ((0, generator) :: (0, generator) :: []))
          TraceCorQRelationLedger.empty) =
      TraceCorQQuotient.ofCandidate
        (TraceCorQQuotientInput.ofFormalSumLedger
          ([] ++ ((0, generator) :: (-(0 : Rat), generator) :: []))
          TraceCorQRelationLedger.empty) :=
  TraceCorQQuotient.sound_sameFormalSum
    TraceCorQRelationLedger.empty
    (left :=
      TraceCorQQuotientInput.ofFormalSumLedger
        ([] ++ ((0, generator) :: (0, generator) :: []))
        TraceCorQRelationLedger.empty)
    (right :=
      TraceCorQQuotientInput.ofFormalSumLedger
        ([] ++ ((0, generator) :: (-(0 : Rat), generator) :: []))
        TraceCorQRelationLedger.empty)
    (show
      ([] ++ ((0, generator) :: (0, generator) :: []) : TraceCorQFormalSum) =
        [] ++ ((0, generator) :: (-(0 : Rat), generator) :: []) from
      Eq.trans
        (List.nil_append
          ((0, generator) :: (0, generator) :: []))
        (Eq.trans
          (TraceCorQFormalSum.zero_zero_pair_eq_zero_neg_zero_pair
            generator)
          (Eq.symm
            (List.nil_append
              ((0, generator) :: (-(0 : Rat), generator) :: [])))))

/-- The adjacent `0 + -0` pair cancels to the quotient zero class. -/
theorem TraceCorQQuotient.zero_neg_zero_pair_eq_zero
    (generator : TraceCorQGenerator) :
    TraceCorQQuotient.ofCandidate
        (TraceCorQQuotientInput.ofFormalSumLedger
          ([] ++ ((0, generator) :: (-(0 : Rat), generator) :: []))
          TraceCorQRelationLedger.empty) =
      TraceCorQQuotient.zero :=
  TraceCorQQuotient.sound_cancelAdjacentOpposite
    TraceCorQRelationLedger.empty
    []
    []
    0
    generator

/-- A zero-coefficient singleton represents the zero quotient class. -/
theorem TraceCorQQuotient.singleton_zero
    (generator : TraceCorQGenerator) :
    TraceCorQQuotient.singleton 0 generator =
      TraceCorQQuotient.zero :=
  Eq.trans
    (Eq.symm
      (TraceCorQQuotient.zero_zero_pair_eq_singleton_zero generator))
    (Eq.trans
      (TraceCorQQuotient.zero_zero_pair_eq_zero_neg_zero_pair generator)
      (TraceCorQQuotient.zero_neg_zero_pair_eq_zero generator))

end AnalyticMotives
end LFunctions
end Boundary
