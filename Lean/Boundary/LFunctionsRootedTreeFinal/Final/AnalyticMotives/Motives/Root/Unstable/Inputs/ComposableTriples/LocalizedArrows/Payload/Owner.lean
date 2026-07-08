import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Unstable.Inputs.ComposableTriples.LocalizedArrows.Payload.Owner

/-!
# Motive-root localized-arrow composites for composable triples

This file exposes the two named localized-forward-arrow composites and their
associativity through the motive-root namespace.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Motive-root wrapper: the left-associated named localized-arrow composite. -/
def TraceAnalyticMotive.leftAssociatedLocalizedForwardArrow
    (triple : TraceLocalizationInputComposableTriple) :
    TraceLocalizationWordClass
      triple.first.sourceObject
      triple.third.targetObject :=
  triple.leftAssociatedLocalizedForwardArrow

/-- Motive-root wrapper: the right-associated named localized-arrow composite. -/
def TraceAnalyticMotive.rightAssociatedLocalizedForwardArrow
    (triple : TraceLocalizationInputComposableTriple) :
    TraceLocalizationWordClass
      triple.first.sourceObject
      triple.third.targetObject :=
  triple.rightAssociatedLocalizedForwardArrow

/-- Motive-root wrapper: the two named localized-arrow composites agree. -/
theorem TraceAnalyticMotive.associatedLocalizedForwardArrow_eq
    (triple : TraceLocalizationInputComposableTriple) :
    TraceAnalyticMotive.leftAssociatedLocalizedForwardArrow triple =
      TraceAnalyticMotive.rightAssociatedLocalizedForwardArrow triple :=
  TraceLocalizationInputComposableTriple.associatedLocalizedForwardArrow_eq
    triple

end AnalyticMotives
end LFunctions
end Boundary
