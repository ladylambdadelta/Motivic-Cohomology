import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.CompactGeometric.Generators.Localized.InputEndpoints.ComposablePairs.ComposableTriples.Presheaves.Owner

/-!
# Localized-word-object projections for composable triples
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- The source localized-word object of a composable triple. -/
def TraceLocalizationInputComposableTriple.sourceLocalizedObject
    (triple : TraceLocalizationInputComposableTriple) :
    TraceLocalizedWordObject :=
  triple.sourceGenerator.localizedObject

/-- The first middle localized-word object of a composable triple. -/
def TraceLocalizationInputComposableTriple.firstMiddleLocalizedObject
    (triple : TraceLocalizationInputComposableTriple) :
    TraceLocalizedWordObject :=
  triple.firstMiddleGenerator.localizedObject

/-- The second middle localized-word object of a composable triple. -/
def TraceLocalizationInputComposableTriple.secondMiddleLocalizedObject
    (triple : TraceLocalizationInputComposableTriple) :
    TraceLocalizedWordObject :=
  triple.secondMiddleGenerator.localizedObject

/-- The target localized-word object of a composable triple. -/
def TraceLocalizationInputComposableTriple.targetLocalizedObject
    (triple : TraceLocalizationInputComposableTriple) :
    TraceLocalizedWordObject :=
  triple.targetGenerator.localizedObject

/-- The triple source localized object is the first input source localized object. -/
theorem TraceLocalizationInputComposableTriple.sourceLocalizedObject_eq_first
    (triple : TraceLocalizationInputComposableTriple) :
    triple.sourceLocalizedObject =
      triple.first.sourceGenerator.localizedObject :=
  rfl

/-- The first middle localized object is the first input target localized object. -/
theorem TraceLocalizationInputComposableTriple.firstMiddleLocalizedObject_eq_first
    (triple : TraceLocalizationInputComposableTriple) :
    triple.firstMiddleLocalizedObject =
      triple.first.targetGenerator.localizedObject :=
  rfl

/-- The second middle localized object is the second input target localized object. -/
theorem TraceLocalizationInputComposableTriple.secondMiddleLocalizedObject_eq_second
    (triple : TraceLocalizationInputComposableTriple) :
    triple.secondMiddleLocalizedObject =
      triple.second.targetGenerator.localizedObject :=
  rfl

/-- The triple target localized object is the third input target localized object. -/
theorem TraceLocalizationInputComposableTriple.targetLocalizedObject_eq_third
    (triple : TraceLocalizationInputComposableTriple) :
    triple.targetLocalizedObject =
      triple.third.targetGenerator.localizedObject :=
  rfl

/-- The source localized object has the triple source trace object underneath. -/
theorem TraceLocalizationInputComposableTriple.sourceLocalizedObject_underlying
    (triple : TraceLocalizationInputComposableTriple) :
    triple.sourceLocalizedObject.underlying =
      triple.sourceObject :=
  rfl

/-- The first middle localized object has the first target trace object underneath. -/
theorem TraceLocalizationInputComposableTriple.firstMiddleLocalizedObject_underlying
    (triple : TraceLocalizationInputComposableTriple) :
    triple.firstMiddleLocalizedObject.underlying =
      triple.firstMiddleObject :=
  rfl

/-- The second middle localized object has the second target trace object underneath. -/
theorem TraceLocalizationInputComposableTriple.secondMiddleLocalizedObject_underlying
    (triple : TraceLocalizationInputComposableTriple) :
    triple.secondMiddleLocalizedObject.underlying =
      triple.secondMiddleObject :=
  rfl

/-- The target localized object has the third target trace object underneath. -/
theorem TraceLocalizationInputComposableTriple.targetLocalizedObject_underlying
    (triple : TraceLocalizationInputComposableTriple) :
    triple.targetLocalizedObject.underlying =
      triple.targetObject :=
  rfl

/-- The first middle localized object agrees with the second input source localized object. -/
theorem TraceLocalizationInputComposableTriple.firstMiddleLocalizedObject_eq_second_source
    (triple : TraceLocalizationInputComposableTriple) :
    triple.firstMiddleLocalizedObject =
      triple.second.sourceGenerator.localizedObject :=
  congrArg
    TraceAnalyticGeometricGenerator.localizedObject
    (TraceLocalizationInputComposableTriple.firstMiddleGenerator_eq_second_source
      triple)

/-- The second middle localized object agrees with the third input source localized object. -/
theorem TraceLocalizationInputComposableTriple.secondMiddleLocalizedObject_eq_third_source
    (triple : TraceLocalizationInputComposableTriple) :
    triple.secondMiddleLocalizedObject =
      triple.third.sourceGenerator.localizedObject :=
  congrArg
    TraceAnalyticGeometricGenerator.localizedObject
    (TraceLocalizationInputComposableTriple.secondMiddleGenerator_eq_third_source
      triple)

end AnalyticMotives
end LFunctions
end Boundary
