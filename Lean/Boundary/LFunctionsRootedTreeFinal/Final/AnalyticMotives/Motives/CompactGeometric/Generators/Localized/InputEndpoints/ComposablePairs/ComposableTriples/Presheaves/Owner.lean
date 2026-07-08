import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.CompactGeometric.Generators.Localized.InputEndpoints.ComposablePairs.ComposableTriples.Generators.Owner

/-!
# Representable-presheaf projections for composable triples
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- The source representable presheaf of a composable triple. -/
def TraceLocalizationInputComposableTriple.sourcePresheaf
    (triple : TraceLocalizationInputComposableTriple) :
    TraceCorQPresheaf :=
  triple.first.sourcePresheaf

/-- The first middle representable presheaf of a composable triple. -/
def TraceLocalizationInputComposableTriple.firstMiddlePresheaf
    (triple : TraceLocalizationInputComposableTriple) :
    TraceCorQPresheaf :=
  triple.first.targetPresheaf

/-- The second middle representable presheaf of a composable triple. -/
def TraceLocalizationInputComposableTriple.secondMiddlePresheaf
    (triple : TraceLocalizationInputComposableTriple) :
    TraceCorQPresheaf :=
  triple.second.targetPresheaf

/-- The target representable presheaf of a composable triple. -/
def TraceLocalizationInputComposableTriple.targetPresheaf
    (triple : TraceLocalizationInputComposableTriple) :
    TraceCorQPresheaf :=
  triple.third.targetPresheaf

/-- The triple source presheaf is the first input source presheaf. -/
theorem TraceLocalizationInputComposableTriple.sourcePresheaf_eq_first
    (triple : TraceLocalizationInputComposableTriple) :
    triple.sourcePresheaf =
      triple.first.sourcePresheaf :=
  rfl

/-- The first middle presheaf is the first input target presheaf. -/
theorem TraceLocalizationInputComposableTriple.firstMiddlePresheaf_eq_first
    (triple : TraceLocalizationInputComposableTriple) :
    triple.firstMiddlePresheaf =
      triple.first.targetPresheaf :=
  rfl

/-- The second middle presheaf is the second input target presheaf. -/
theorem TraceLocalizationInputComposableTriple.secondMiddlePresheaf_eq_second
    (triple : TraceLocalizationInputComposableTriple) :
    triple.secondMiddlePresheaf =
      triple.second.targetPresheaf :=
  rfl

/-- The triple target presheaf is the third input target presheaf. -/
theorem TraceLocalizationInputComposableTriple.targetPresheaf_eq_third
    (triple : TraceLocalizationInputComposableTriple) :
    triple.targetPresheaf =
      triple.third.targetPresheaf :=
  rfl

/-- The first middle presheaf agrees with the second input source presheaf. -/
theorem TraceLocalizationInputComposableTriple.firstMiddlePresheaf_eq_second_source
    (triple : TraceLocalizationInputComposableTriple) :
    triple.firstMiddlePresheaf =
      triple.second.sourcePresheaf :=
  congrArg
    TraceCorQPresheaf.representable
    (TraceLocalizationInputComposableTriple.firstMiddleObject_eq triple)

/-- The second middle presheaf agrees with the third input source presheaf. -/
theorem TraceLocalizationInputComposableTriple.secondMiddlePresheaf_eq_third_source
    (triple : TraceLocalizationInputComposableTriple) :
    triple.secondMiddlePresheaf =
      triple.third.sourcePresheaf :=
  congrArg
    TraceCorQPresheaf.representable
    (TraceLocalizationInputComposableTriple.secondMiddleObject_eq triple)

/-- The source generator has the triple source presheaf. -/
theorem TraceLocalizationInputComposableTriple.sourceGenerator_presheaf
    (triple : TraceLocalizationInputComposableTriple) :
    triple.sourceGenerator.presheaf =
      triple.sourcePresheaf :=
  rfl

/-- The first middle generator has the first middle presheaf. -/
theorem TraceLocalizationInputComposableTriple.firstMiddleGenerator_presheaf
    (triple : TraceLocalizationInputComposableTriple) :
    triple.firstMiddleGenerator.presheaf =
      triple.firstMiddlePresheaf :=
  rfl

/-- The second middle generator has the second middle presheaf. -/
theorem TraceLocalizationInputComposableTriple.secondMiddleGenerator_presheaf
    (triple : TraceLocalizationInputComposableTriple) :
    triple.secondMiddleGenerator.presheaf =
      triple.secondMiddlePresheaf :=
  rfl

/-- The target generator has the triple target presheaf. -/
theorem TraceLocalizationInputComposableTriple.targetGenerator_presheaf
    (triple : TraceLocalizationInputComposableTriple) :
    triple.targetGenerator.presheaf =
      triple.targetPresheaf :=
  rfl

end AnalyticMotives
end LFunctions
end Boundary
