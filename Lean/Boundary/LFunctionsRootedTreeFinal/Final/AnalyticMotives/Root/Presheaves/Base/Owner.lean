import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Presheaves.Owner

/-!
# Top-root trace presheaf base operations

This file exposes the base Q-module-valued trace-presheaf operations under the
top-level `AnalyticMotivesRoot` namespace.
-/

open scoped CategoryTheory

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- The top root exposes presheaf sections as evaluation at the opposite object. -/
theorem AnalyticMotivesRoot.traceCorQPresheaf_sections_eq_obj_op
    (presheaf : TraceCorQPresheaf)
    (object : TraceCorQObject) :
    presheaf.sections object =
      presheaf.obj (Opposite.op object) :=
  TraceCorQPresheaf.sections_eq_obj_op
    presheaf
    object

/-- The top root exposes pullback as functorial action on opposite morphisms. -/
theorem AnalyticMotivesRoot.traceCorQPresheaf_pullback_eq_map_op
    (presheaf : TraceCorQPresheaf)
    {source target : TraceCorQObject}
    (morphism : TraceCorQHom source target) :
    presheaf.pullback morphism =
      presheaf.map (TraceCorQPresheaf.opHom morphism) :=
  TraceCorQPresheaf.pullback_eq_map_op
    presheaf
    morphism

/-- The top root exposes pullback along identity trace correspondences. -/
theorem AnalyticMotivesRoot.traceCorQPresheaf_pullback_id
    (presheaf : TraceCorQPresheaf)
    (object : TraceCorQObject) :
    presheaf.pullback (TraceCorQHom.id object) =
      𝟙 (presheaf.sections object) :=
  TraceCorQPresheaf.pullback_id
    presheaf
    object

/-- The top root exposes contravariant functoriality of pullback. -/
theorem AnalyticMotivesRoot.traceCorQPresheaf_pullback_comp
    (presheaf : TraceCorQPresheaf)
    {first second third : TraceCorQObject}
    (left : TraceCorQHom first second)
    (right : TraceCorQHom second third) :
    presheaf.pullback (TraceCorQHom.comp left right) =
      presheaf.pullback right ≫ presheaf.pullback left :=
  TraceCorQPresheaf.pullback_comp
    presheaf
    left
    right

/-- The top root exposes presheaf morphism components. -/
theorem AnalyticMotivesRoot.traceCorQPresheafHom_component_eq_app_op
    {source target : TraceCorQPresheaf}
    (morphism : TraceCorQPresheafHom source target)
    (object : TraceCorQObject) :
    morphism.component object =
      morphism.app (Opposite.op object) :=
  TraceCorQPresheafHom.component_eq_app_op
    morphism
    object

/-- The top root exposes naturality of presheaf morphism components. -/
theorem AnalyticMotivesRoot.traceCorQPresheafHom_pullback_naturality
    {sourcePresheaf targetPresheaf : TraceCorQPresheaf}
    (presheafMorphism :
      TraceCorQPresheafHom sourcePresheaf targetPresheaf)
    {source target : TraceCorQObject}
    (traceMorphism : TraceCorQHom source target) :
    sourcePresheaf.pullback traceMorphism ≫
        presheafMorphism.component source =
      presheafMorphism.component target ≫
        targetPresheaf.pullback traceMorphism :=
  TraceCorQPresheafHom.pullback_naturality
    presheafMorphism
    traceMorphism

/-- The top root exposes presheaf isomorphism components. -/
theorem AnalyticMotivesRoot.traceCorQPresheafIso_component_eq_app_op
    {source target : TraceCorQPresheaf}
    (isomorphism : TraceCorQPresheafIso source target)
    (object : TraceCorQObject) :
    isomorphism.component object =
      isomorphism.app (Opposite.op object) :=
  TraceCorQPresheafIso.component_eq_app_op
    isomorphism
    object

/-- The top root exposes evaluation of a presheaf on one trace object. -/
theorem AnalyticMotivesRoot.traceCorQPresheaf_evaluation_obj
    (object : TraceCorQObject)
    (presheaf : TraceCorQPresheaf) :
    (TraceCorQPresheaf.evaluation object).obj presheaf =
      presheaf.sections object :=
  TraceCorQPresheaf.evaluation_obj
    object
    presheaf

/-- The top root exposes evaluation of a presheaf morphism on one trace object. -/
theorem AnalyticMotivesRoot.traceCorQPresheaf_evaluation_map
    (object : TraceCorQObject)
    {source target : TraceCorQPresheaf}
    (morphism : TraceCorQPresheafHom source target) :
    (TraceCorQPresheaf.evaluation object).map morphism =
      morphism.component object :=
  TraceCorQPresheaf.evaluation_map
    object
    morphism

end AnalyticMotives
end LFunctions
end Boundary
