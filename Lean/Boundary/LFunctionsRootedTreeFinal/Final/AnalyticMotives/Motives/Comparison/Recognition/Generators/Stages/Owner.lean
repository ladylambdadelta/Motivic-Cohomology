import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Comparison.Endpoints.Source.TraceObject.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Comparison.Recognition.Generators.Owner

/-!
# Recognition generator source stages

This file exposes the additive, complex, homotopy, and stable comparison-source
images of a concrete rewrite generator's certified trace correspondence.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- The additive-envelope source map of a concrete rewrite generator. -/
def TraceAnalyticMotiveRecognition.rewriteGeneratorAdditiveMap
    (generator : TraceRewriteGenerator) :
    TraceAnalyticMotiveComparison.sourceTraceAdditiveObject
        generator.sourceObject ⟶
      TraceAnalyticMotiveComparison.sourceTraceAdditiveObject
        generator.targetObject :=
  TraceAnalyticMotiveComparison.sourceTraceAdditiveMap generator.traceHom

/-- The additive-envelope source map of a rewrite generator is the singleton
additive-envelope map of its certified trace hom. -/
theorem TraceAnalyticMotiveRecognition.rewriteGeneratorAdditiveMap_eq_singletonFunctor_map
    (generator : TraceRewriteGenerator) :
    TraceAnalyticMotiveRecognition.rewriteGeneratorAdditiveMap generator =
      TraceAnalyticAdditiveObject.singletonFunctor.map generator.traceHom :=
  TraceAnalyticMotiveComparison.sourceTraceAdditiveMap_eq_singletonFunctor_map
    generator.traceHom

/-- The additive-envelope source map of a rewrite generator is the singleton
matrix of its certified trace hom. -/
theorem TraceAnalyticMotiveRecognition.rewriteGeneratorAdditiveMap_eq_singletonMap
    (generator : TraceRewriteGenerator) :
    TraceAnalyticMotiveRecognition.rewriteGeneratorAdditiveMap generator =
      TraceAnalyticAdditiveHom.singletonMap generator.traceHom :=
  TraceAnalyticMotiveComparison.sourceTraceAdditiveMap_eq_singletonMap
    generator.traceHom

/-- The degree-zero complex source map of a concrete rewrite generator. -/
def TraceAnalyticMotiveRecognition.rewriteGeneratorComplexMap
    (generator : TraceRewriteGenerator) :
    TraceAnalyticMotiveComparison.sourceTraceComplex generator.sourceObject ⟶
      TraceAnalyticMotiveComparison.sourceTraceComplex generator.targetObject :=
  TraceAnalyticMotiveComparison.sourceTraceComplexMap generator.traceHom

/-- The complex source map of a rewrite generator is the degree-zero single
complex image of its additive-envelope source map. -/
theorem TraceAnalyticMotiveRecognition.rewriteGeneratorComplexMap_eq_additiveMap
    (generator : TraceRewriteGenerator) :
    TraceAnalyticMotiveRecognition.rewriteGeneratorComplexMap generator =
      (CochainComplex.singleFunctor TraceAnalyticAdditiveCategoryObject
        (0 : ℤ)).map
        (TraceAnalyticMotiveRecognition.rewriteGeneratorAdditiveMap
          generator) :=
  TraceAnalyticMotiveComparison.sourceTraceComplexMap_eq_sourceTraceAdditiveMap
    generator.traceHom

/-- The complex source map of a rewrite generator is the degree-zero single
complex image of the singleton matrix of its certified trace hom. -/
theorem TraceAnalyticMotiveRecognition.rewriteGeneratorComplexMap_eq_singletonMap
    (generator : TraceRewriteGenerator) :
    TraceAnalyticMotiveRecognition.rewriteGeneratorComplexMap generator =
      (CochainComplex.singleFunctor TraceAnalyticAdditiveCategoryObject
        (0 : ℤ)).map
        (TraceAnalyticAdditiveHom.singletonMap generator.traceHom) :=
  TraceAnalyticMotiveComparison.sourceTraceComplexMap_eq_singletonMap
    generator.traceHom

/-- The additive-homotopy source map of a concrete rewrite generator. -/
def TraceAnalyticMotiveRecognition.rewriteGeneratorHomotopyMap
    (generator : TraceRewriteGenerator) :
    TraceAnalyticMotiveComparison.sourceTraceHomotopyObject
        generator.sourceObject ⟶
      TraceAnalyticMotiveComparison.sourceTraceHomotopyObject
        generator.targetObject :=
  TraceAnalyticMotiveComparison.sourceTraceHomotopyMap generator.traceHom

/-- The homotopy source map of a rewrite generator is the additive homotopy
quotient image of its degree-zero complex source map. -/
theorem TraceAnalyticMotiveRecognition.rewriteGeneratorHomotopyMap_eq_mapOf
    (generator : TraceRewriteGenerator) :
    TraceAnalyticMotiveRecognition.rewriteGeneratorHomotopyMap generator =
      TraceAnalyticAdditiveHomotopyCategory.mapOf
        (TraceAnalyticMotiveRecognition.rewriteGeneratorComplexMap generator) :=
  TraceAnalyticMotiveComparison.sourceTraceHomotopyMap_eq_mapOf
    generator.traceHom

/-- The stable comparison-source map of a concrete rewrite generator. -/
def TraceAnalyticMotiveRecognition.rewriteGeneratorStableMap
    (generator : TraceRewriteGenerator) :
    TraceAnalyticMotiveComparison.sourceTraceObject generator.sourceObject ⟶
      TraceAnalyticMotiveComparison.sourceTraceObject generator.targetObject :=
  TraceAnalyticMotiveComparison.sourceTraceMap generator.traceHom

/-- The stable source map of a rewrite generator is the stable quotient image
of its homotopy source map. -/
theorem TraceAnalyticMotiveRecognition.rewriteGeneratorStableMap_eq_sourceMapOf
    (generator : TraceRewriteGenerator) :
    TraceAnalyticMotiveRecognition.rewriteGeneratorStableMap generator =
      TraceAnalyticMotiveComparison.sourceMapOf
        (TraceAnalyticMotiveRecognition.rewriteGeneratorHomotopyMap
          generator) :=
  TraceAnalyticMotiveComparison.sourceTraceMap_eq_sourceMapOf
    generator.traceHom

/-- The stable source map of a rewrite generator is the stable analytic
quotient image of its homotopy source map. -/
theorem TraceAnalyticMotiveRecognition.rewriteGeneratorStableMap_eq_stable
    (generator : TraceRewriteGenerator) :
    TraceAnalyticMotiveRecognition.rewriteGeneratorStableMap generator =
      TraceAnalyticStableMotiveCategory.mapOf
        (TraceAnalyticMotiveRecognition.rewriteGeneratorHomotopyMap
          generator) :=
  TraceAnalyticMotiveComparison.sourceTraceMap_eq_stable
    generator.traceHom

/-- The stable source map of a rewrite generator is the Verdier quotient
functor image of its homotopy source map. -/
theorem TraceAnalyticMotiveRecognition.rewriteGeneratorStableMap_eq_quotientFunctor_map
    (generator : TraceRewriteGenerator) :
    TraceAnalyticMotiveRecognition.rewriteGeneratorStableMap generator =
      TraceAnalyticStableMotiveCategory.quotientFunctor.map
        (TraceAnalyticMotiveRecognition.rewriteGeneratorHomotopyMap
          generator) :=
  TraceAnalyticMotiveComparison.sourceTraceMap_eq_quotientFunctor_map
    generator.traceHom

end AnalyticMotives
end LFunctions
end Boundary
