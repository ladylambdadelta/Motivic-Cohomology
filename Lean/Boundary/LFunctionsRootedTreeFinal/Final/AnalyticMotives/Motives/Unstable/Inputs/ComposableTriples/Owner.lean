import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.CompactGeometric.Generators.Localized.InputEndpoints.ComposablePairs.ComposableTriples.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Unstable.Owner

/-!
# Composable triples inside the unstable analytic-motive envelope

This file projects the concrete endpoint data of a composable triple of
localization inputs into the unstable localized-word envelope.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- The unstable source of the first input is the triple source localized object. -/
theorem TraceLocalizationInputComposableTriple.first_unstableSource_eq_sourceLocalizedObject
    (triple : TraceLocalizationInputComposableTriple) :
    triple.first.unstableSource =
      triple.sourceLocalizedObject :=
  rfl

/-- The unstable target of the first input is the first middle localized object. -/
theorem TraceLocalizationInputComposableTriple.first_unstableTarget_eq_firstMiddleLocalizedObject
    (triple : TraceLocalizationInputComposableTriple) :
    triple.first.unstableTarget =
      triple.firstMiddleLocalizedObject :=
  rfl

/-- The unstable source of the second input agrees with the first middle localized object. -/
theorem TraceLocalizationInputComposableTriple.second_unstableSource_eq_firstMiddleLocalizedObject
    (triple : TraceLocalizationInputComposableTriple) :
    triple.second.unstableSource =
      triple.firstMiddleLocalizedObject :=
  Eq.symm
    (TraceLocalizationInputComposableTriple.firstMiddleLocalizedObject_eq_second_source
      triple)

/-- The unstable target of the second input is the second middle localized object. -/
theorem TraceLocalizationInputComposableTriple.second_unstableTarget_eq_secondMiddleLocalizedObject
    (triple : TraceLocalizationInputComposableTriple) :
    triple.second.unstableTarget =
      triple.secondMiddleLocalizedObject :=
  rfl

/-- The unstable source of the third input agrees with the second middle localized object. -/
theorem TraceLocalizationInputComposableTriple.third_unstableSource_eq_secondMiddleLocalizedObject
    (triple : TraceLocalizationInputComposableTriple) :
    triple.third.unstableSource =
      triple.secondMiddleLocalizedObject :=
  Eq.symm
    (TraceLocalizationInputComposableTriple.secondMiddleLocalizedObject_eq_third_source
      triple)

/-- The unstable target of the third input is the triple target localized object. -/
theorem TraceLocalizationInputComposableTriple.third_unstableTarget_eq_targetLocalizedObject
    (triple : TraceLocalizationInputComposableTriple) :
    triple.third.unstableTarget =
      triple.targetLocalizedObject :=
  rfl

/-- The first unstable middle endpoint is the second unstable source. -/
theorem TraceLocalizationInputComposableTriple.first_unstableTarget_eq_second_unstableSource
    (triple : TraceLocalizationInputComposableTriple) :
    triple.first.unstableTarget =
      triple.second.unstableSource :=
  congrArg
    TraceLocalizedWordObject.ofTraceObject
    triple.first_middle_eq

/-- The second unstable middle endpoint is the third unstable source. -/
theorem TraceLocalizationInputComposableTriple.second_unstableTarget_eq_third_unstableSource
    (triple : TraceLocalizationInputComposableTriple) :
    triple.second.unstableTarget =
      triple.third.unstableSource :=
  congrArg
    TraceLocalizedWordObject.ofTraceObject
    triple.second_middle_eq

end AnalyticMotives
end LFunctions
end Boundary
