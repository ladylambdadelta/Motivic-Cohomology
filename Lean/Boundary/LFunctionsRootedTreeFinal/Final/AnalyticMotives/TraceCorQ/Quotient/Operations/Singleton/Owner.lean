import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Quotient.Operations.Smul.Owner

/-!
# Singleton quotient trace correspondences

This file names the quotient class represented by one rationally weighted
trace-correspondence generator.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- The raw quotient candidate represented by one weighted trace generator. -/
def TraceCorQQuotient.singletonCandidate
    (coefficient : Rat)
    (generator : TraceCorQGenerator)
    (ledger : TraceCorQRelationLedger) :
    TraceCorQQuotientCandidate :=
  TraceCorQQuotientInput.ofFormalSumLedger
    (TraceCorQFormalSum.singleton coefficient generator)
    ledger

/-- The quotient class represented by one weighted trace generator. -/
def TraceCorQQuotient.singleton
    (coefficient : Rat)
    (generator : TraceCorQGenerator) :
    TraceCorQQuotient :=
  TraceCorQQuotient.ofCandidate
    (TraceCorQQuotient.singletonCandidate
      coefficient
      generator
      TraceCorQRelationLedger.empty)

/-- The singleton candidate has the expected one-term formal sum. -/
theorem TraceCorQQuotient.singletonCandidate_formalSum
    (coefficient : Rat)
    (generator : TraceCorQGenerator)
    (ledger : TraceCorQRelationLedger) :
    (TraceCorQQuotient.singletonCandidate
      coefficient
      generator
      ledger).formalSum =
      TraceCorQFormalSum.singleton coefficient generator :=
  rfl

/-- The singleton candidate carries the supplied relation ledger. -/
theorem TraceCorQQuotient.singletonCandidate_ledger
    (coefficient : Rat)
    (generator : TraceCorQGenerator)
    (ledger : TraceCorQRelationLedger) :
    (TraceCorQQuotient.singletonCandidate
      coefficient
      generator
      ledger).ledger =
      ledger :=
  rfl

/-- The singleton quotient class is represented by the singleton candidate. -/
theorem TraceCorQQuotient.singleton_eq_ofCandidate
    (coefficient : Rat)
    (generator : TraceCorQGenerator) :
    TraceCorQQuotient.singleton coefficient generator =
      TraceCorQQuotient.ofCandidate
        (TraceCorQQuotient.singletonCandidate
          coefficient
          generator
          TraceCorQRelationLedger.empty) :=
  rfl

/-- Scaling a singleton quotient class scales its rational coefficient. -/
theorem TraceCorQQuotient.smul_singleton
    (leftCoefficient rightCoefficient : Rat)
    (generator : TraceCorQGenerator) :
    TraceCorQQuotient.smul
      leftCoefficient
      (TraceCorQQuotient.singleton rightCoefficient generator) =
      TraceCorQQuotient.singleton
        (leftCoefficient * rightCoefficient)
        generator :=
  Eq.trans
    (TraceCorQQuotient.smul_ofCandidate
      leftCoefficient
      (TraceCorQQuotient.singletonCandidate
        rightCoefficient
        generator
        TraceCorQRelationLedger.empty))
    (TraceCorQQuotient.sound_sameFormalSum
      TraceCorQRelationLedger.empty
      rfl)

end AnalyticMotives
end LFunctions
end Boundary
