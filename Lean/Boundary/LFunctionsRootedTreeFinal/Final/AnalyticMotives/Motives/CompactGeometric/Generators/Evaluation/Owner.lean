import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.CompactGeometric.Generators.Functors.Forgetful.Owner

/-!
# Evaluation at compact geometric analytic generators

This file records evaluation of trace presheaves at the trace object
underlying a compact analytic generator.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Evaluation of trace presheaves at a compact analytic generator. -/
def TraceAnalyticGeometricGenerator.evaluation
    (generator : TraceAnalyticGeometricGenerator) :
    TraceCorQPresheaf ⥤ ModuleCat Rat :=
  TraceCorQPresheaf.evaluation generator.traceObject

/-- Sections of a trace presheaf over a compact analytic generator. -/
def TraceAnalyticGeometricGenerator.sections
    (generator : TraceAnalyticGeometricGenerator)
    (presheaf : TraceCorQPresheaf) :
    ModuleCat Rat :=
  presheaf.sections generator.traceObject

/-- Evaluation at a compact generator is evaluation at its underlying trace object. -/
theorem TraceAnalyticGeometricGenerator.evaluation_eq_traceObject
    (generator : TraceAnalyticGeometricGenerator) :
    generator.evaluation =
      TraceCorQPresheaf.evaluation generator.traceObject :=
  rfl

/-- Evaluation at a compact generator is evaluation at the forgetful functor object. -/
theorem TraceAnalyticGeometricGenerator.evaluation_eq_forgetful_obj
    (generator : TraceAnalyticGeometricGenerator) :
    generator.evaluation =
      TraceCorQPresheaf.evaluation
        (TraceAnalyticGeometricGenerator.forgetfulFunctor.obj generator) :=
  rfl

/-- Evaluation sends a presheaf to its sections over the generator. -/
theorem TraceAnalyticGeometricGenerator.evaluation_obj
    (generator : TraceAnalyticGeometricGenerator)
    (presheaf : TraceCorQPresheaf) :
    generator.evaluation.obj presheaf =
      generator.sections presheaf :=
  rfl

/-- Evaluation sends a presheaf morphism to its component over the generator. -/
theorem TraceAnalyticGeometricGenerator.evaluation_map
    (generator : TraceAnalyticGeometricGenerator)
    {source target : TraceCorQPresheaf}
    (morphism : source ⟶ target) :
    generator.evaluation.map morphism =
      morphism.component generator.traceObject :=
  rfl

/-- Sections over a compact generator are sections over its underlying trace object. -/
theorem TraceAnalyticGeometricGenerator.sections_eq_traceObject
    (generator : TraceAnalyticGeometricGenerator)
    (presheaf : TraceCorQPresheaf) :
    generator.sections presheaf =
      presheaf.sections generator.traceObject :=
  rfl

/-- Sections of a representable over a compact generator are trace correspondences. -/
theorem TraceAnalyticGeometricGenerator.representable_sections
    (source target : TraceAnalyticGeometricGenerator) :
    source.sections target.presheaf =
      ModuleCat.of Rat (source.traceObject ⟶ target.traceObject) :=
  TraceCorQPresheaf.representable_sections
    source.traceObject
    target.traceObject

/-- Evaluation of the compact presheaf functor at a source generator gives trace homs. -/
theorem TraceAnalyticGeometricGenerator.evaluation_presheafFunctor_obj
    (source target : TraceAnalyticGeometricGenerator) :
    source.evaluation.obj
        (TraceAnalyticGeometricGenerator.presheafFunctor.obj target) =
      ModuleCat.of Rat (source.traceObject ⟶ target.traceObject) :=
  TraceCorQPresheaf.representable_sections
    source.traceObject
    target.traceObject

end AnalyticMotives
end LFunctions
end Boundary
