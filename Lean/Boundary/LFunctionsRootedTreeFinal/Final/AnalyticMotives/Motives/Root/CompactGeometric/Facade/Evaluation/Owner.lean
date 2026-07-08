import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Root.CompactGeometric.Facade.Category.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Root.CompactGeometric.Evaluation.Owner

/-!
# Motive-root compact-geometric evaluation facade

This file exposes compact-generator evaluation and section facts under the
`TraceAnalyticMotive` root facade.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Compact-generator evaluation is evaluation at the underlying trace object. -/
theorem TraceAnalyticMotive.compactGenerator_evaluation_eq_traceObject
    (generator : TraceAnalyticGeometricGenerator) :
    generator.evaluation =
      TraceCorQPresheaf.evaluation generator.traceObject :=
  TraceAnalyticCompactGeometric.evaluation_eq_traceObject
    generator

/-- Compact-generator evaluation is evaluation at the forgetful functor object. -/
theorem TraceAnalyticMotive.compactGenerator_evaluation_eq_forgetful_obj
    (generator : TraceAnalyticGeometricGenerator) :
    generator.evaluation =
      TraceCorQPresheaf.evaluation
        (TraceAnalyticGeometricGenerator.forgetfulFunctor.obj generator) :=
  TraceAnalyticCompactGeometric.evaluation_eq_forgetful_obj
    generator

/-- Compact-generator evaluation sends a presheaf to sections over the generator. -/
theorem TraceAnalyticMotive.compactGenerator_evaluation_obj
    (generator : TraceAnalyticGeometricGenerator)
    (presheaf : TraceCorQPresheaf) :
    generator.evaluation.obj presheaf =
      generator.sections presheaf :=
  TraceAnalyticCompactGeometric.evaluation_obj
    generator
    presheaf

/-- Compact-generator evaluation sends a presheaf morphism to its component. -/
theorem TraceAnalyticMotive.compactGenerator_evaluation_map
    (generator : TraceAnalyticGeometricGenerator)
    {source target : TraceCorQPresheaf}
    (morphism : source ⟶ target) :
    generator.evaluation.map morphism =
      morphism.component generator.traceObject :=
  TraceAnalyticCompactGeometric.evaluation_map
    generator
    morphism

/-- Compact-generator sections are sections over the underlying trace object. -/
theorem TraceAnalyticMotive.compactGenerator_sections_eq_traceObject
    (generator : TraceAnalyticGeometricGenerator)
    (presheaf : TraceCorQPresheaf) :
    generator.sections presheaf =
      presheaf.sections generator.traceObject :=
  TraceAnalyticCompactGeometric.sections_eq_traceObject
    generator
    presheaf

/-- Sections of a compact-generator representable are trace correspondences. -/
theorem TraceAnalyticMotive.compactGenerator_representable_sections
    (source target : TraceAnalyticGeometricGenerator) :
    source.sections target.presheaf =
      ModuleCat.of Rat (source.traceObject ⟶ target.traceObject) :=
  TraceAnalyticCompactGeometric.representable_sections
    source
    target

/-- Evaluating the compact presheaf functor gives trace homs. -/
theorem TraceAnalyticMotive.compactGenerator_evaluation_presheafFunctor_obj
    (source target : TraceAnalyticGeometricGenerator) :
    source.evaluation.obj
        (TraceAnalyticGeometricGenerator.presheafFunctor.obj target) =
      ModuleCat.of Rat (source.traceObject ⟶ target.traceObject) :=
  TraceAnalyticCompactGeometric.evaluation_presheafFunctor_obj
    source
    target

end AnalyticMotives
end LFunctions
end Boundary
