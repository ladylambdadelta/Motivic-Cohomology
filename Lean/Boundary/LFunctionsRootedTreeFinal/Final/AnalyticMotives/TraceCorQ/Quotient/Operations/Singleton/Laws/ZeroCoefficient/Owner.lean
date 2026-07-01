import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Quotient.Operations.Singleton.Owner

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
    (zero_add (0 : Rat))

/-- A zero-coefficient singleton represents the zero quotient class. -/
theorem TraceCorQQuotient.singleton_zero
    (generator : TraceCorQGenerator) :
    TraceCorQQuotient.singleton 0 generator =
      TraceCorQQuotient.zero :=
  Eq.trans
    (Eq.symm
      (Eq.trans
        (TraceCorQQuotient.sound_combineAdjacentSame
          TraceCorQRelationLedger.empty
          []
          []
          0
          0
          generator)
        (TraceCorQQuotient.sound_sameFormalSum
          TraceCorQRelationLedger.empty
          (TraceCorQFormalSum.zero_add_zero_singleton_eq_zero_singleton
            generator))))
    (Eq.trans
      (TraceCorQQuotient.sound_sameFormalSum
        TraceCorQRelationLedger.empty
        (TraceCorQFormalSum.zero_zero_pair_eq_zero_neg_zero_pair
          generator))
      (TraceCorQQuotient.sound_cancelAdjacentOpposite
        TraceCorQRelationLedger.empty
        []
        []
        0
        generator))

end AnalyticMotives
end LFunctions
end Boundary
