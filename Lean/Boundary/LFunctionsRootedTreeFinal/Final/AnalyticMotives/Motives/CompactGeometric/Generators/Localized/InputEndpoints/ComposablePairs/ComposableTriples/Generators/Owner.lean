import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.CompactGeometric.Generators.Localized.InputEndpoints.ComposablePairs.ComposableTriples.Objects.Owner

/-!
# Compact-generator projections for composable triples
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- The source compact generator of a composable triple. -/
def TraceLocalizationInputComposableTriple.sourceGenerator
    (triple : TraceLocalizationInputComposableTriple) :
    TraceAnalyticGeometricGenerator :=
  triple.first.sourceGenerator

/-- The first middle compact generator of a composable triple. -/
def TraceLocalizationInputComposableTriple.firstMiddleGenerator
    (triple : TraceLocalizationInputComposableTriple) :
    TraceAnalyticGeometricGenerator :=
  triple.first.targetGenerator

/-- The second middle compact generator of a composable triple. -/
def TraceLocalizationInputComposableTriple.secondMiddleGenerator
    (triple : TraceLocalizationInputComposableTriple) :
    TraceAnalyticGeometricGenerator :=
  triple.second.targetGenerator

/-- The target compact generator of a composable triple. -/
def TraceLocalizationInputComposableTriple.targetGenerator
    (triple : TraceLocalizationInputComposableTriple) :
    TraceAnalyticGeometricGenerator :=
  triple.third.targetGenerator

/-- The triple source generator is the first input source generator. -/
theorem TraceLocalizationInputComposableTriple.sourceGenerator_eq_first
    (triple : TraceLocalizationInputComposableTriple) :
    triple.sourceGenerator =
      triple.first.sourceGenerator :=
  rfl

/-- The first middle generator is the first input target generator. -/
theorem TraceLocalizationInputComposableTriple.firstMiddleGenerator_eq_first
    (triple : TraceLocalizationInputComposableTriple) :
    triple.firstMiddleGenerator =
      triple.first.targetGenerator :=
  rfl

/-- The second middle generator is the second input target generator. -/
theorem TraceLocalizationInputComposableTriple.secondMiddleGenerator_eq_second
    (triple : TraceLocalizationInputComposableTriple) :
    triple.secondMiddleGenerator =
      triple.second.targetGenerator :=
  rfl

/-- The triple target generator is the third input target generator. -/
theorem TraceLocalizationInputComposableTriple.targetGenerator_eq_third
    (triple : TraceLocalizationInputComposableTriple) :
    triple.targetGenerator =
      triple.third.targetGenerator :=
  rfl

/-- The first middle generator agrees with the second input source generator. -/
theorem TraceLocalizationInputComposableTriple.firstMiddleGenerator_eq_second_source
    (triple : TraceLocalizationInputComposableTriple) :
    triple.firstMiddleGenerator =
      triple.second.sourceGenerator :=
  TraceLocalizationInputComposablePair.middleGenerator_eq_right_source
    triple.leftPair

/-- The second middle generator agrees with the third input source generator. -/
theorem TraceLocalizationInputComposableTriple.secondMiddleGenerator_eq_third_source
    (triple : TraceLocalizationInputComposableTriple) :
    triple.secondMiddleGenerator =
      triple.third.sourceGenerator :=
  TraceLocalizationInputComposablePair.middleGenerator_eq_right_source
    triple.rightPair

end AnalyticMotives
end LFunctions
end Boundary
