import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Root.Unstable.Inputs.ComposableTriples.LocalizedArrows.Payload.Owner

/-!
# Public localized-arrow composites for composable triples

This file exposes the two named localized-forward-arrow composites and their
associativity through the public analytic-motives root.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Public wrapper: the left-associated named localized-arrow composite. -/
def AnalyticMotivesRoot.leftAssociatedLocalizedForwardArrow
    (triple : TraceLocalizationInputComposableTriple) :
    TraceLocalizationWordClass
      triple.first.sourceObject
      triple.third.targetObject :=
  TraceAnalyticMotive.leftAssociatedLocalizedForwardArrow
    triple

/-- Public wrapper: the right-associated named localized-arrow composite. -/
def AnalyticMotivesRoot.rightAssociatedLocalizedForwardArrow
    (triple : TraceLocalizationInputComposableTriple) :
    TraceLocalizationWordClass
      triple.first.sourceObject
      triple.third.targetObject :=
  TraceAnalyticMotive.rightAssociatedLocalizedForwardArrow
    triple

/-- Public wrapper: the two named localized-arrow composites agree. -/
theorem AnalyticMotivesRoot.associatedLocalizedForwardArrow_eq
    (triple : TraceLocalizationInputComposableTriple) :
    AnalyticMotivesRoot.leftAssociatedLocalizedForwardArrow triple =
      AnalyticMotivesRoot.rightAssociatedLocalizedForwardArrow triple :=
  TraceAnalyticMotive.associatedLocalizedForwardArrow_eq
    triple

end AnalyticMotives
end LFunctions
end Boundary
