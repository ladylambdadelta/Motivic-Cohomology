import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Quotient.Setoid.Owner

/-!
# Scalar multiplication on quotient trace correspondences

This file defines rational scalar multiplication of quotient
trace-correspondence classes by descending candidate scalar multiplication
through the finite-witness relation.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Rational scalar multiplication of quotient trace-correspondence classes. -/
def TraceCorQQuotient.smul
    (coefficient : Rat)
    (candidateClass : TraceCorQQuotient) :
    TraceCorQQuotient :=
  Quotient.liftOn
    candidateClass
    (fun candidate =>
      TraceCorQQuotient.ofCandidate
        (TraceCorQQuotientCandidate.smul coefficient candidate))
    (fun left right relation =>
      TraceCorQQuotient.sound
        (TraceCorQQuotientRelation.smulCongr
          coefficient
          relation))

/-- Scalar multiplication of quotient classes agrees with scaling representatives. -/
theorem TraceCorQQuotient.smul_ofCandidate
    (coefficient : Rat)
    (candidate : TraceCorQQuotientCandidate) :
    TraceCorQQuotient.smul
      coefficient
      (TraceCorQQuotient.ofCandidate candidate) =
      TraceCorQQuotient.ofCandidate
        (TraceCorQQuotientCandidate.smul coefficient candidate) :=
  rfl

end AnalyticMotives
end LFunctions
end Boundary
