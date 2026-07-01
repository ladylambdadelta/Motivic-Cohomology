import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Quotient.Setoid.Owner

/-!
# Composition on quotient trace correspondences

This file defines composition of quotient trace-correspondence classes by
descending raw candidate composition through the finite-witness relation.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Composition of quotient trace-correspondence classes. -/
def TraceCorQQuotient.comp
    (left right : TraceCorQQuotient) :
    TraceCorQQuotient :=
  Quotient.liftOn₂
    left
    right
    (fun leftCandidate rightCandidate =>
      TraceCorQQuotient.ofCandidate
        (TraceCorQQuotientCandidate.comp leftCandidate rightCandidate))
    (fun left₁ right₁ left₂ right₂ leftRelation rightRelation =>
      TraceCorQQuotient.sound
        (TraceCorQQuotientRelation.compCongr
          leftRelation
          rightRelation))

/-- Composition of quotient classes agrees with composition of representatives. -/
theorem TraceCorQQuotient.comp_ofCandidate
    (left right : TraceCorQQuotientCandidate) :
    TraceCorQQuotient.comp
      (TraceCorQQuotient.ofCandidate left)
      (TraceCorQQuotient.ofCandidate right) =
      TraceCorQQuotient.ofCandidate
        (TraceCorQQuotientCandidate.comp left right) :=
  rfl

end AnalyticMotives
end LFunctions
end Boundary
