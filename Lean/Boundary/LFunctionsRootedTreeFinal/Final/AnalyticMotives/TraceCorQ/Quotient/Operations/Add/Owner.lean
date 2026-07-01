import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Quotient.Setoid.Owner

/-!
# Addition on quotient trace correspondences

This file defines addition of quotient trace-correspondence classes by
descending candidate addition through the finite-witness relation.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Addition of quotient trace-correspondence classes. -/
def TraceCorQQuotient.add
    (left right : TraceCorQQuotient) :
    TraceCorQQuotient :=
  Quotient.liftOn₂
    left
    right
    (fun leftCandidate rightCandidate =>
      TraceCorQQuotient.ofCandidate
        (TraceCorQQuotientCandidate.add leftCandidate rightCandidate))
    (fun left₁ right₁ left₂ right₂ leftRelation rightRelation =>
      TraceCorQQuotient.sound
        (TraceCorQQuotientRelation.addCongr
          leftRelation
          rightRelation))

/-- Addition of quotient classes agrees with addition of representatives. -/
theorem TraceCorQQuotient.add_ofCandidate
    (left right : TraceCorQQuotientCandidate) :
    TraceCorQQuotient.add
      (TraceCorQQuotient.ofCandidate left)
      (TraceCorQQuotient.ofCandidate right) =
      TraceCorQQuotient.ofCandidate
        (TraceCorQQuotientCandidate.add left right) :=
  rfl

end AnalyticMotives
end LFunctions
end Boundary
