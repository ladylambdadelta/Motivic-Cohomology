import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Quotient.Operations.Singleton.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Quotient.Operations.Add.Owner

/-!
# Same-generator singleton coefficient combination

This file owns the quotient-level consequence of adjacent same-generator
coefficient combination for singleton classes.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Same-generator singleton classes add by adding their coefficients. -/
theorem TraceCorQQuotient.singleton_add_singleton_same_generator
    (leftCoefficient rightCoefficient : Rat)
    (generator : TraceCorQGenerator) :
    TraceCorQQuotient.add
      (TraceCorQQuotient.singleton leftCoefficient generator)
      (TraceCorQQuotient.singleton rightCoefficient generator) =
      TraceCorQQuotient.singleton
        (leftCoefficient + rightCoefficient)
        generator :=
  Eq.trans
    (TraceCorQQuotient.add_ofCandidate
      (TraceCorQQuotient.singletonCandidate
        leftCoefficient
        generator
        TraceCorQRelationLedger.empty)
      (TraceCorQQuotient.singletonCandidate
        rightCoefficient
        generator
        TraceCorQRelationLedger.empty))
    (TraceCorQQuotient.sound_combineAdjacentSame
      TraceCorQRelationLedger.empty
      []
      []
      leftCoefficient
      rightCoefficient
      generator)

end AnalyticMotives
end LFunctions
end Boundary
