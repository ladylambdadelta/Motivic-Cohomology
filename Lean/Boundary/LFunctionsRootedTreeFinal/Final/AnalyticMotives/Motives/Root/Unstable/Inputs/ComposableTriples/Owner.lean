import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Unstable.Inputs.ComposableTriples.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Root.Unstable.Inputs.ComposableTriples.ForwardWords.Owner

/-!
# Motive-root composable triples inside the unstable envelope

This file exposes unstable endpoint facts for composable triples through the
motive-root namespace.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Motive-root wrapper: the first unstable source is the triple source localized object. -/
theorem TraceAnalyticMotive.first_unstableSource_eq_sourceLocalizedObject
    (triple : TraceLocalizationInputComposableTriple) :
    triple.first.unstableSource =
      triple.sourceLocalizedObject :=
  TraceLocalizationInputComposableTriple.first_unstableSource_eq_sourceLocalizedObject
    triple

/-- Motive-root wrapper: the first unstable target is the first middle localized object. -/
theorem TraceAnalyticMotive.first_unstableTarget_eq_firstMiddleLocalizedObject
    (triple : TraceLocalizationInputComposableTriple) :
    triple.first.unstableTarget =
      triple.firstMiddleLocalizedObject :=
  TraceLocalizationInputComposableTriple.first_unstableTarget_eq_firstMiddleLocalizedObject
    triple

/-- Motive-root wrapper: the second unstable source is the first middle localized object. -/
theorem TraceAnalyticMotive.second_unstableSource_eq_firstMiddleLocalizedObject
    (triple : TraceLocalizationInputComposableTriple) :
    triple.second.unstableSource =
      triple.firstMiddleLocalizedObject :=
  TraceLocalizationInputComposableTriple.second_unstableSource_eq_firstMiddleLocalizedObject
    triple

/-- Motive-root wrapper: the second unstable target is the second middle localized object. -/
theorem TraceAnalyticMotive.second_unstableTarget_eq_secondMiddleLocalizedObject
    (triple : TraceLocalizationInputComposableTriple) :
    triple.second.unstableTarget =
      triple.secondMiddleLocalizedObject :=
  TraceLocalizationInputComposableTriple.second_unstableTarget_eq_secondMiddleLocalizedObject
    triple

/-- Motive-root wrapper: the third unstable source is the second middle localized object. -/
theorem TraceAnalyticMotive.third_unstableSource_eq_secondMiddleLocalizedObject
    (triple : TraceLocalizationInputComposableTriple) :
    triple.third.unstableSource =
      triple.secondMiddleLocalizedObject :=
  TraceLocalizationInputComposableTriple.third_unstableSource_eq_secondMiddleLocalizedObject
    triple

/-- Motive-root wrapper: the third unstable target is the triple target localized object. -/
theorem TraceAnalyticMotive.third_unstableTarget_eq_targetLocalizedObject
    (triple : TraceLocalizationInputComposableTriple) :
    triple.third.unstableTarget =
      triple.targetLocalizedObject :=
  TraceLocalizationInputComposableTriple.third_unstableTarget_eq_targetLocalizedObject
    triple

/-- Motive-root wrapper: the first unstable target is the second unstable source. -/
theorem TraceAnalyticMotive.first_unstableTarget_eq_second_unstableSource
    (triple : TraceLocalizationInputComposableTriple) :
    triple.first.unstableTarget =
      triple.second.unstableSource :=
  TraceLocalizationInputComposableTriple.first_unstableTarget_eq_second_unstableSource
    triple

/-- Motive-root wrapper: the second unstable target is the third unstable source. -/
theorem TraceAnalyticMotive.second_unstableTarget_eq_third_unstableSource
    (triple : TraceLocalizationInputComposableTriple) :
    triple.second.unstableTarget =
      triple.third.unstableSource :=
  TraceLocalizationInputComposableTriple.second_unstableTarget_eq_third_unstableSource
    triple

end AnalyticMotives
end LFunctions
end Boundary
