import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Quotient.Operations.Singleton.Laws.ZeroCoefficient.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Quotient.Operations.Singleton.Laws.CoefficientCombination.Owner

/-!
# Singleton quotient laws

This aggregate owns laws specific to singleton quotient trace correspondences.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Singleton-law aggregate: singleton candidates have the expected formal sum. -/
theorem TraceCorQQuotient.singleton_laws_singletonCandidate_formalSum
    (coefficient : Rat)
    (generator : TraceCorQGenerator)
    (ledger : TraceCorQRelationLedger) :
    (TraceCorQQuotient.singletonCandidate
      coefficient
      generator
      ledger).formalSum =
      TraceCorQFormalSum.singleton coefficient generator :=
  TraceCorQQuotient.singletonCandidate_formalSum
    coefficient
    generator
    ledger

/-- Singleton-law aggregate: singleton candidates carry the supplied ledger. -/
theorem TraceCorQQuotient.singleton_laws_singletonCandidate_ledger
    (coefficient : Rat)
    (generator : TraceCorQGenerator)
    (ledger : TraceCorQRelationLedger) :
    (TraceCorQQuotient.singletonCandidate
      coefficient
      generator
      ledger).ledger =
      ledger :=
  TraceCorQQuotient.singletonCandidate_ledger
    coefficient
    generator
    ledger

/-- Singleton-law aggregate: singleton classes are represented by singleton candidates. -/
theorem TraceCorQQuotient.singleton_laws_singleton_eq_ofCandidate
    (coefficient : Rat)
    (generator : TraceCorQGenerator) :
    TraceCorQQuotient.singleton coefficient generator =
      TraceCorQQuotient.ofCandidate
        (TraceCorQQuotient.singletonCandidate
          coefficient
          generator
          TraceCorQRelationLedger.empty) :=
  TraceCorQQuotient.singleton_eq_ofCandidate
    coefficient
    generator

/-- Singleton-law aggregate: scaling a singleton scales its coefficient. -/
theorem TraceCorQQuotient.singleton_laws_smul_singleton
    (leftCoefficient rightCoefficient : Rat)
    (generator : TraceCorQGenerator) :
    TraceCorQQuotient.smul
      leftCoefficient
      (TraceCorQQuotient.singleton rightCoefficient generator) =
      TraceCorQQuotient.singleton
        (leftCoefficient * rightCoefficient)
        generator :=
  TraceCorQQuotient.smul_singleton
    leftCoefficient
    rightCoefficient
    generator

/-- Singleton-law aggregate: a zero-coefficient singleton is the zero quotient class. -/
theorem TraceCorQQuotient.singleton_laws_singleton_zero
    (generator : TraceCorQGenerator) :
    TraceCorQQuotient.singleton 0 generator =
      TraceCorQQuotient.zero :=
  TraceCorQQuotient.singleton_zero generator

/-- Singleton-law aggregate: same-generator singleton classes combine coefficients. -/
theorem TraceCorQQuotient.singleton_laws_singleton_add_singleton_same_generator
    (leftCoefficient rightCoefficient : Rat)
    (generator : TraceCorQGenerator) :
    TraceCorQQuotient.add
      (TraceCorQQuotient.singleton leftCoefficient generator)
      (TraceCorQQuotient.singleton rightCoefficient generator) =
      TraceCorQQuotient.singleton
        (leftCoefficient + rightCoefficient)
        generator :=
  TraceCorQQuotient.singleton_add_singleton_same_generator
    leftCoefficient
    rightCoefficient
    generator

end AnalyticMotives
end LFunctions
end Boundary
