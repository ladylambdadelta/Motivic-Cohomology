import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Quotient.Operations.Smul.Owner

/-!
# Negation of quotient trace correspondences

This file owns negation in the quotient trace-correspondence span.  Negation is
the concrete rational scalar action by `-1`.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Negation of quotient trace-correspondence classes. -/
def TraceCorQQuotient.neg
    (candidateClass : TraceCorQQuotient) :
    TraceCorQQuotient :=
  TraceCorQQuotient.smul (-1) candidateClass

/-- Quotient negation is scalar multiplication by `-1`. -/
theorem TraceCorQQuotient.neg_eq_smul_neg_one
    (candidateClass : TraceCorQQuotient) :
    TraceCorQQuotient.neg candidateClass =
      TraceCorQQuotient.smul (-1) candidateClass :=
  rfl

/-- Negation agrees with candidate scaling. -/
theorem TraceCorQQuotient.neg_ofCandidate
    (candidate : TraceCorQQuotientCandidate) :
    TraceCorQQuotient.neg
      (TraceCorQQuotient.ofCandidate candidate) =
      TraceCorQQuotient.ofCandidate
        (TraceCorQQuotientCandidate.smul (-1) candidate) :=
  TraceCorQQuotient.smul_ofCandidate (-1) candidate

end AnalyticMotives
end LFunctions
end Boundary
