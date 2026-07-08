import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Root.Presheaves.Base.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Root.Presheaves.Linear.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Root.Presheaves.Representables.Owner

/-!
# Top-root trace presheaves

This file collects public base, linear, and representable trace-presheaf
surfaces under the `AnalyticMotivesRoot` namespace.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Presheaf aggregate: sections are evaluation at the opposite trace object. -/
theorem AnalyticMotivesRoot.tracePresheafSummary_sections_eq_obj_op
    (presheaf : TraceCorQPresheaf)
    (object : TraceCorQObject) :
    presheaf.sections object =
      presheaf.obj (Opposite.op object) :=
  AnalyticMotivesRoot.traceCorQPresheaf_sections_eq_obj_op
    presheaf
    object

/-- Presheaf aggregate: objectwise evaluation sends a presheaf to its sections. -/
theorem AnalyticMotivesRoot.tracePresheafSummary_evaluation_obj
    (object : TraceCorQObject)
    (presheaf : TraceCorQPresheaf) :
    (TraceCorQPresheaf.evaluation object).obj presheaf =
      presheaf.sections object :=
  AnalyticMotivesRoot.traceCorQPresheaf_evaluation_obj
    object
    presheaf

/-- Presheaf aggregate: representable sections recover trace correspondences. -/
theorem AnalyticMotivesRoot.tracePresheafSummary_representable_sections
    (source target : TraceCorQObject) :
    (TraceCorQPresheaf.representable target).sections source =
      ModuleCat.of Rat (source ⟶ target) :=
  AnalyticMotivesRoot.traceCorQRepresentable_sections
    source
    target

/-- Presheaf aggregate: representable preimage recovers the original trace hom. -/
theorem AnalyticMotivesRoot.tracePresheafSummary_representablePreimage_representableMap
    {source target : TraceCorQObject}
    (morphism : source ⟶ target) :
    TraceCorQPresheaf.representablePreimage
      (TraceCorQPresheaf.representableMap morphism) =
      morphism :=
  AnalyticMotivesRoot.traceCorQRepresentablePreimage_representableMap
    morphism

/-- Presheaf aggregate: representable maps preserve composition. -/
theorem AnalyticMotivesRoot.tracePresheafSummary_representableMap_comp
    {first second third : TraceCorQObject}
    (left : first ⟶ second)
    (right : second ⟶ third) :
    TraceCorQPresheaf.representableMap (left ≫ right) =
      TraceCorQPresheaf.representableMap left ≫
        TraceCorQPresheaf.representableMap right :=
  AnalyticMotivesRoot.traceCorQRepresentableMap_comp
    left
    right

/-- Presheaf aggregate: evaluation preserves addition of presheaf morphisms. -/
theorem AnalyticMotivesRoot.tracePresheafSummary_evaluation_map_add
    (object : TraceCorQObject)
    {source target : TraceCorQPresheaf}
    (left right : source ⟶ target) :
    (TraceCorQPresheaf.evaluation object).map (left + right) =
      (TraceCorQPresheaf.evaluation object).map left +
        (TraceCorQPresheaf.evaluation object).map right :=
  AnalyticMotivesRoot.traceCorQPresheaf_evaluation_map_add
    object
    left
    right

/-- Presheaf aggregate: evaluation preserves rational scalar multiplication. -/
theorem AnalyticMotivesRoot.tracePresheafSummary_evaluation_map_smul
    (object : TraceCorQObject)
    {source target : TraceCorQPresheaf}
    (coefficient : Rat)
    (morphism : source ⟶ target) :
    (TraceCorQPresheaf.evaluation object).map (coefficient • morphism) =
      coefficient • (TraceCorQPresheaf.evaluation object).map morphism :=
  AnalyticMotivesRoot.traceCorQPresheaf_evaluation_map_smul
    object
    coefficient
    morphism

end AnalyticMotives
end LFunctions
end Boundary
