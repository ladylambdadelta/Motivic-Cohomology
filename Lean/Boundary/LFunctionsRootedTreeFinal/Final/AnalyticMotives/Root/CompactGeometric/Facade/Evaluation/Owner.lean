import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Root.CompactGeometric.Evaluation.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Root.CompactGeometric.Facade.RepresentableCategory.Owner

/-!
# Top-root compact-geometric evaluation facade
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- The analytic-motives root exposes compact-generator evaluation at the trace object. -/
theorem AnalyticMotivesRoot.compactGenerator_evaluation_eq_traceObject
    (generator : TraceAnalyticGeometricGenerator) :
    generator.evaluation =
      TraceCorQPresheaf.evaluation generator.traceObject :=
  TraceAnalyticMotive.compactGenerator_evaluation_eq_traceObject
    generator

/-- The analytic-motives root exposes compact-generator evaluation at the forgetful object. -/
theorem AnalyticMotivesRoot.compactGenerator_evaluation_eq_forgetful_obj
    (generator : TraceAnalyticGeometricGenerator) :
    generator.evaluation =
      TraceCorQPresheaf.evaluation
        (TraceAnalyticGeometricGenerator.forgetfulFunctor.obj generator) :=
  TraceAnalyticMotive.compactGenerator_evaluation_eq_forgetful_obj
    generator

/-- The analytic-motives root exposes compact-generator evaluation on presheaves. -/
theorem AnalyticMotivesRoot.compactGenerator_evaluation_obj
    (generator : TraceAnalyticGeometricGenerator)
    (presheaf : TraceCorQPresheaf) :
    generator.evaluation.obj presheaf =
      generator.sections presheaf :=
  TraceAnalyticMotive.compactGenerator_evaluation_obj
    generator
    presheaf

/-- The analytic-motives root exposes compact-generator evaluation on presheaf morphisms. -/
theorem AnalyticMotivesRoot.compactGenerator_evaluation_map
    (generator : TraceAnalyticGeometricGenerator)
    {source target : TraceCorQPresheaf}
    (morphism : source ⟶ target) :
    generator.evaluation.map morphism =
      morphism.component generator.traceObject :=
  TraceAnalyticMotive.compactGenerator_evaluation_map
    generator
    morphism

/-- The analytic-motives root exposes compact-generator sections over trace objects. -/
theorem AnalyticMotivesRoot.compactGenerator_sections_eq_traceObject
    (generator : TraceAnalyticGeometricGenerator)
    (presheaf : TraceCorQPresheaf) :
    generator.sections presheaf =
      presheaf.sections generator.traceObject :=
  TraceAnalyticMotive.compactGenerator_sections_eq_traceObject
    generator
    presheaf

/-- The analytic-motives root exposes compact-generator representable sections. -/
theorem AnalyticMotivesRoot.compactGenerator_representable_sections
    (source target : TraceAnalyticGeometricGenerator) :
    source.sections target.presheaf =
      ModuleCat.of Rat (source.traceObject ⟶ target.traceObject) :=
  TraceAnalyticMotive.compactGenerator_representable_sections
    source
    target

/-- The analytic-motives root exposes compact presheaf-functor evaluation. -/
theorem AnalyticMotivesRoot.compactGenerator_evaluation_presheafFunctor_obj
    (source target : TraceAnalyticGeometricGenerator) :
    source.evaluation.obj
        (TraceAnalyticGeometricGenerator.presheafFunctor.obj target) =
      ModuleCat.of Rat (source.traceObject ⟶ target.traceObject) :=
  TraceAnalyticMotive.compactGenerator_evaluation_presheafFunctor_obj
    source
    target

end AnalyticMotives
end LFunctions
end Boundary
