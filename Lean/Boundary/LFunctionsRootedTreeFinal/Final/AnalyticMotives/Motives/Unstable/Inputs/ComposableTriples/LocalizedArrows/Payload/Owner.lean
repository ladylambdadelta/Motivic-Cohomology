import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Unstable.Inputs.ComposableTriples.LocalizedArrows.Owner

/-!
# Localized-arrow composites for composable unstable input triples

This file gives names to the two parenthesizations of the composite of the
three named localized forward arrows of a composable input triple.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- The left-associated composite of the three named localized forward arrows. -/
def TraceLocalizationInputComposableTriple.leftAssociatedLocalizedForwardArrow
    (triple : TraceLocalizationInputComposableTriple) :
    TraceLocalizationWordClass
      triple.first.sourceObject
      triple.third.targetObject :=
  TraceLocalizationWordClass.comp
    (TraceLocalizationWordClass.comp
      triple.first.localizedForwardArrow
      (match triple.first_middle_eq with
      | rfl => triple.second.localizedForwardArrow))
    (match triple.second_middle_eq with
    | rfl => triple.third.localizedForwardArrow)

/-- The right-associated composite of the three named localized forward arrows. -/
def TraceLocalizationInputComposableTriple.rightAssociatedLocalizedForwardArrow
    (triple : TraceLocalizationInputComposableTriple) :
    TraceLocalizationWordClass
      triple.first.sourceObject
      triple.third.targetObject :=
  TraceLocalizationWordClass.comp
    triple.first.localizedForwardArrow
    (TraceLocalizationWordClass.comp
      (match triple.first_middle_eq with
      | rfl => triple.second.localizedForwardArrow)
      (match triple.second_middle_eq with
      | rfl => triple.third.localizedForwardArrow))

/-- The two parenthesizations of the named localized forward-arrow composite agree. -/
theorem TraceLocalizationInputComposableTriple.associatedLocalizedForwardArrow_eq
    (triple : TraceLocalizationInputComposableTriple) :
    triple.leftAssociatedLocalizedForwardArrow =
      triple.rightAssociatedLocalizedForwardArrow :=
  TraceLocalizationInputComposableTriple.localizedForwardArrow_assoc
    triple

end AnalyticMotives
end LFunctions
end Boundary
