import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Quotient.Operations.Zero.Owner

/-!
# Support-zero quotient equalities

This file owns the operation-level equality saying that the formal support of a
single relation generator is zero in the quotient.

The relation owner provides the support-zero relation.  This file is downstream
from the zero operation, so it can state the corresponding equality using the
named zero quotient class.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- A relation generator's formal support is zero in the quotient. -/
theorem TraceCorQQuotient.supportZero_eq_zero
    (relation : TraceCorQRelationGenerator) :
    TraceCorQQuotient.ofCandidate
      (TraceCorQRelationGenerator.supportCandidate relation) =
      TraceCorQQuotient.zero :=
  TraceCorQQuotient.sound
    (TraceCorQQuotientRelation.supportZero relation)

/-- The support-zero equality is exactly soundness for the support-zero relation. -/
theorem TraceCorQQuotient.supportZero_eq_zero_eq_sound
    (relation : TraceCorQRelationGenerator) :
    TraceCorQQuotient.supportZero_eq_zero relation =
      TraceCorQQuotient.sound
        (TraceCorQQuotientRelation.supportZero relation) :=
  rfl

end AnalyticMotives
end LFunctions
end Boundary
