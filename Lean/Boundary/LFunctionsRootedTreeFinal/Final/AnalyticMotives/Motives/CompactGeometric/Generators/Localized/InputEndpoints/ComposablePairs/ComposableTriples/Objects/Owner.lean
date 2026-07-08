import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.CompactGeometric.Generators.Localized.InputEndpoints.ComposablePairs.ComposableTriples.Core.Owner

/-!
# Trace-object projections for composable triples
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- The source trace object of a composable triple. -/
def TraceLocalizationInputComposableTriple.sourceObject
    (triple : TraceLocalizationInputComposableTriple) :
    TraceCorQObject :=
  triple.first.sourceObject

/-- The first middle trace object of a composable triple. -/
def TraceLocalizationInputComposableTriple.firstMiddleObject
    (triple : TraceLocalizationInputComposableTriple) :
    TraceCorQObject :=
  triple.first.targetObject

/-- The second middle trace object of a composable triple. -/
def TraceLocalizationInputComposableTriple.secondMiddleObject
    (triple : TraceLocalizationInputComposableTriple) :
    TraceCorQObject :=
  triple.second.targetObject

/-- The target trace object of a composable triple. -/
def TraceLocalizationInputComposableTriple.targetObject
    (triple : TraceLocalizationInputComposableTriple) :
    TraceCorQObject :=
  triple.third.targetObject

/-- The triple source object is the first input source object. -/
theorem TraceLocalizationInputComposableTriple.sourceObject_eq_first
    (triple : TraceLocalizationInputComposableTriple) :
    triple.sourceObject =
      triple.first.sourceObject :=
  rfl

/-- The first middle object is the first input target object. -/
theorem TraceLocalizationInputComposableTriple.firstMiddleObject_eq_first
    (triple : TraceLocalizationInputComposableTriple) :
    triple.firstMiddleObject =
      triple.first.targetObject :=
  rfl

/-- The second middle object is the second input target object. -/
theorem TraceLocalizationInputComposableTriple.secondMiddleObject_eq_second
    (triple : TraceLocalizationInputComposableTriple) :
    triple.secondMiddleObject =
      triple.second.targetObject :=
  rfl

/-- The triple target object is the third input target object. -/
theorem TraceLocalizationInputComposableTriple.targetObject_eq_third
    (triple : TraceLocalizationInputComposableTriple) :
    triple.targetObject =
      triple.third.targetObject :=
  rfl

/-- The first middle object agrees with the second input source object. -/
theorem TraceLocalizationInputComposableTriple.firstMiddleObject_eq_second_source
    (triple : TraceLocalizationInputComposableTriple) :
    triple.firstMiddleObject =
      triple.second.sourceObject :=
  Eq.trans
    (TraceLocalizationInputComposableTriple.firstMiddleObject_eq_first triple)
    (TraceLocalizationInputComposableTriple.firstMiddleObject_eq triple)

/-- The second middle object agrees with the third input source object. -/
theorem TraceLocalizationInputComposableTriple.secondMiddleObject_eq_third_source
    (triple : TraceLocalizationInputComposableTriple) :
    triple.secondMiddleObject =
      triple.third.sourceObject :=
  Eq.trans
    (TraceLocalizationInputComposableTriple.secondMiddleObject_eq_second triple)
    (TraceLocalizationInputComposableTriple.secondMiddleObject_eq triple)

end AnalyticMotives
end LFunctions
end Boundary
