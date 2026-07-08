import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Comparison.Endpoints.Source.TraceObject.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.CompactGeometric.Generators.Functors.Forgetful.Owner

/-!
# Compact-generator formulas for the comparison source endpoint

This file exposes compact geometric analytic generators as source-side
comparison objects by forgetting them to certified trace correspondences and
then applying the stable trace-source endpoint functor.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory

/-- The stable comparison-source object represented by a compact geometric
analytic generator. -/
def TraceAnalyticMotiveComparison.sourceGeneratorObject
    (generator : TraceAnalyticGeometricGenerator) :
    TraceAnalyticDMgmComparisonSource :=
  TraceAnalyticMotiveComparison.sourceTraceObject generator.traceObject

/-- The source generator object is the source trace object of the underlying
certified trace object. -/
theorem TraceAnalyticMotiveComparison.sourceGeneratorObject_eq_sourceTraceObject
    (generator : TraceAnalyticGeometricGenerator) :
    TraceAnalyticMotiveComparison.sourceGeneratorObject generator =
      TraceAnalyticMotiveComparison.sourceTraceObject generator.traceObject :=
  rfl

/-- The source generator object is the source trace functor applied to the
underlying certified trace object. -/
theorem TraceAnalyticMotiveComparison.sourceGeneratorObject_eq_sourceTraceFunctor_obj
    (generator : TraceAnalyticGeometricGenerator) :
    TraceAnalyticMotiveComparison.sourceGeneratorObject generator =
      TraceAnalyticMotiveComparison.sourceTraceFunctor.obj
        (TraceAnalyticGeometricGenerator.forgetfulFunctor.obj generator) :=
  rfl

/-- The source generator object is the comparison-source image of the
underlying endpoint trace homotopy object. -/
theorem TraceAnalyticMotiveComparison.sourceGeneratorObject_eq_sourceObjectOf
    (generator : TraceAnalyticGeometricGenerator) :
    TraceAnalyticMotiveComparison.sourceGeneratorObject generator =
      TraceAnalyticMotiveComparison.sourceObjectOf
        (TraceAnalyticMotiveComparison.sourceTraceHomotopyObject
          generator.traceObject) :=
  rfl

/-- The source generator object is the stable analytic quotient image of the
underlying endpoint trace homotopy object. -/
theorem TraceAnalyticMotiveComparison.sourceGeneratorObject_eq_stable
    (generator : TraceAnalyticGeometricGenerator) :
    TraceAnalyticMotiveComparison.sourceGeneratorObject generator =
      TraceAnalyticStableMotiveCategory.objectOf
        (TraceAnalyticMotiveComparison.sourceTraceHomotopyObject
          generator.traceObject) :=
  TraceAnalyticMotiveComparison.sourceTraceObject_eq_stable
    generator.traceObject

/-- The source generator object is the Verdier quotient-functor image of the
underlying endpoint trace homotopy object. -/
theorem TraceAnalyticMotiveComparison.sourceGeneratorObject_eq_quotientFunctor_obj
    (generator : TraceAnalyticGeometricGenerator) :
    TraceAnalyticMotiveComparison.sourceGeneratorObject generator =
      TraceAnalyticStableMotiveCategory.quotientFunctor.obj
        (TraceAnalyticMotiveComparison.sourceTraceHomotopyObject
          generator.traceObject) :=
  TraceAnalyticMotiveComparison.sourceTraceObject_eq_quotientFunctor_obj
    generator.traceObject

/-- The stable comparison-source map represented by a compact geometric
analytic generator morphism. -/
def TraceAnalyticMotiveComparison.sourceGeneratorMap
    {source target : TraceAnalyticGeometricGenerator}
    (hom : source ⟶ target) :
    TraceAnalyticMotiveComparison.sourceGeneratorObject source ⟶
      TraceAnalyticMotiveComparison.sourceGeneratorObject target :=
  TraceAnalyticMotiveComparison.sourceTraceMap hom.traceHom

/-- The source generator map is the source trace map of the underlying trace
correspondence. -/
theorem TraceAnalyticMotiveComparison.sourceGeneratorMap_eq_sourceTraceMap
    {source target : TraceAnalyticGeometricGenerator}
    (hom : source ⟶ target) :
    TraceAnalyticMotiveComparison.sourceGeneratorMap hom =
      TraceAnalyticMotiveComparison.sourceTraceMap hom.traceHom :=
  rfl

/-- The source generator map is the source trace functor map of the underlying
trace correspondence. -/
theorem TraceAnalyticMotiveComparison.sourceGeneratorMap_eq_sourceTraceFunctor_map
    {source target : TraceAnalyticGeometricGenerator}
    (hom : source ⟶ target) :
    TraceAnalyticMotiveComparison.sourceGeneratorMap hom =
      TraceAnalyticMotiveComparison.sourceTraceFunctor.map
        (TraceAnalyticGeometricGenerator.forgetfulFunctor.map hom) :=
  rfl

/-- The source generator map is the comparison-source image of the underlying
endpoint trace homotopy map. -/
theorem TraceAnalyticMotiveComparison.sourceGeneratorMap_eq_sourceMapOf
    {source target : TraceAnalyticGeometricGenerator}
    (hom : source ⟶ target) :
    TraceAnalyticMotiveComparison.sourceGeneratorMap hom =
      TraceAnalyticMotiveComparison.sourceMapOf
        (TraceAnalyticMotiveComparison.sourceTraceHomotopyMap hom.traceHom) :=
  rfl

/-- The source generator map is the stable analytic quotient image of the
underlying endpoint trace homotopy map. -/
theorem TraceAnalyticMotiveComparison.sourceGeneratorMap_eq_stable
    {source target : TraceAnalyticGeometricGenerator}
    (hom : source ⟶ target) :
    TraceAnalyticMotiveComparison.sourceGeneratorMap hom =
      TraceAnalyticStableMotiveCategory.mapOf
        (TraceAnalyticMotiveComparison.sourceTraceHomotopyMap hom.traceHom) :=
  TraceAnalyticMotiveComparison.sourceTraceMap_eq_stable hom.traceHom

/-- The source generator map is the Verdier quotient-functor image of the
underlying endpoint trace homotopy map. -/
theorem TraceAnalyticMotiveComparison.sourceGeneratorMap_eq_quotientFunctor_map
    {source target : TraceAnalyticGeometricGenerator}
    (hom : source ⟶ target) :
    TraceAnalyticMotiveComparison.sourceGeneratorMap hom =
      TraceAnalyticStableMotiveCategory.quotientFunctor.map
        (TraceAnalyticMotiveComparison.sourceTraceHomotopyMap hom.traceHom) :=
  TraceAnalyticMotiveComparison.sourceTraceMap_eq_quotientFunctor_map
    hom.traceHom

/-- The comparison-source functor represented by compact geometric analytic
generators. -/
def TraceAnalyticMotiveComparison.sourceGeneratorFunctor :
    TraceAnalyticGeometricGenerator ⥤ TraceAnalyticDMgmComparisonSource :=
  TraceAnalyticGeometricGenerator.forgetfulFunctor ⋙
    TraceAnalyticMotiveComparison.sourceTraceFunctor

/-- The source generator functor factors through the forgetful functor to trace
correspondences followed by the stable trace-source endpoint. -/
theorem TraceAnalyticMotiveComparison.sourceGeneratorFunctor_eq_forgetful_comp_sourceTrace :
    TraceAnalyticMotiveComparison.sourceGeneratorFunctor =
      TraceAnalyticGeometricGenerator.forgetfulFunctor ⋙
        TraceAnalyticMotiveComparison.sourceTraceFunctor :=
  rfl

/-- The source generator functor is the full four-stage source construction:
forget compact generators to certified trace objects, take singleton additive
objects, take degree-zero complexes, pass to additive homotopy, and then pass
to the stable Verdier quotient. -/
theorem TraceAnalyticMotiveComparison.sourceGeneratorFunctor_eq_full_composite :
    TraceAnalyticMotiveComparison.sourceGeneratorFunctor =
      TraceAnalyticGeometricGenerator.forgetfulFunctor ⋙
        TraceAnalyticAdditiveObject.singletonFunctor ⋙
          CochainComplex.singleFunctor TraceAnalyticAdditiveCategoryObject
            (0 : ℤ) ⋙
            TraceAnalyticAdditiveHomotopyCategory.quotientFunctor ⋙
              TraceAnalyticDMgmComparisonSource.quotientFunctor :=
  rfl

/-- Object formula for the source generator functor. -/
theorem TraceAnalyticMotiveComparison.sourceGeneratorFunctor_obj
    (generator : TraceAnalyticGeometricGenerator) :
    TraceAnalyticMotiveComparison.sourceGeneratorFunctor.obj generator =
      TraceAnalyticMotiveComparison.sourceGeneratorObject generator :=
  rfl

/-- Map formula for the source generator functor. -/
theorem TraceAnalyticMotiveComparison.sourceGeneratorFunctor_map
    {source target : TraceAnalyticGeometricGenerator}
    (hom : source ⟶ target) :
    TraceAnalyticMotiveComparison.sourceGeneratorFunctor.map hom =
      TraceAnalyticMotiveComparison.sourceGeneratorMap hom :=
  rfl

end AnalyticMotives
end LFunctions
end Boundary
