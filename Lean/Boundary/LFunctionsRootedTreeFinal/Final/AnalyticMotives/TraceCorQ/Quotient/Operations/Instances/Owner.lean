import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Quotient.Operations.Add.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Quotient.Operations.Neg.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Quotient.Operations.Smul.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Quotient.Operations.Sub.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Quotient.Operations.Zero.Owner

/-!
# Operation instances for quotient trace correspondences

This file exposes the concrete quotient operations through Lean's standard
operation classes.  No law-bearing algebraic class is introduced here.

Bridge laws for unfolding this notation live in
`Quotient/Operations/Instances/Laws`.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Standard zero notation for quotient trace correspondences. -/
instance traceCorQQuotientZero : Zero TraceCorQQuotient where
  zero := TraceCorQQuotient.zero

/-- Standard addition notation for quotient trace correspondences. -/
instance traceCorQQuotientAdd : Add TraceCorQQuotient where
  add := TraceCorQQuotient.add

/-- Standard negation notation for quotient trace correspondences. -/
instance traceCorQQuotientNeg : Neg TraceCorQQuotient where
  neg := TraceCorQQuotient.neg

/-- Standard subtraction notation for quotient trace correspondences. -/
instance traceCorQQuotientSub : Sub TraceCorQQuotient where
  sub := TraceCorQQuotient.sub

/-- Standard rational scalar notation for quotient trace correspondences. -/
instance traceCorQQuotientRatSMul : SMul Rat TraceCorQQuotient where
  smul := TraceCorQQuotient.smul

end AnalyticMotives
end LFunctions
end Boundary
