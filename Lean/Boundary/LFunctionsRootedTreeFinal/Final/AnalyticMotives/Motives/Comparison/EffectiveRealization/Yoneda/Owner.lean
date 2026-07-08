import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.CompactGeometric.Generators.Functors.Forgetful.Owner

/-!
# Analytic Yoneda source for effective realization

This file records the analytic source side of the effective-realization
comparison: compact certified trace generators enter the comparison through
their concrete trace-Yoneda representable objects.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- The analytic representable-source functor for effective realization. -/
def TraceAnalyticEffectiveRealization.yonedaSourceFunctor :
    TraceAnalyticGeometricGenerator ⥤ TraceCorQRepresentablePresheaf :=
  TraceAnalyticGeometricGenerator.representableObjectFunctor

/-- The analytic representable-source functor sends a generator to its lifted
trace-Yoneda object. -/
theorem TraceAnalyticEffectiveRealization.yonedaSourceFunctor_obj
    (generator : TraceAnalyticGeometricGenerator) :
    TraceAnalyticEffectiveRealization.yonedaSourceFunctor.obj generator =
      generator.representableObject :=
  rfl

/-- The analytic representable-source functor sends a compact-generator
morphism to its lifted trace-Yoneda map. -/
theorem TraceAnalyticEffectiveRealization.yonedaSourceFunctor_map
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : source ⟶ target) :
    TraceAnalyticEffectiveRealization.yonedaSourceFunctor.map morphism =
      morphism.representableObjectMap :=
  rfl

/-- The analytic representable-source functor sends compact-generator
identities to lifted trace-Yoneda identities. -/
theorem TraceAnalyticEffectiveRealization.yonedaSourceFunctor_map_id
    (generator : TraceAnalyticGeometricGenerator) :
    TraceAnalyticEffectiveRealization.yonedaSourceFunctor.map
        (𝟙 generator) =
      𝟙 (TraceAnalyticEffectiveRealization.yonedaSourceFunctor.obj generator) :=
  TraceAnalyticEffectiveRealization.yonedaSourceFunctor.map_id generator

/-- The analytic representable-source functor sends compact-generator
composites to composites of lifted trace-Yoneda maps. -/
theorem TraceAnalyticEffectiveRealization.yonedaSourceFunctor_map_comp
    {first second third : TraceAnalyticGeometricGenerator}
    (left : first ⟶ second)
    (right : second ⟶ third) :
    TraceAnalyticEffectiveRealization.yonedaSourceFunctor.map
        (left ≫ right) =
      TraceAnalyticEffectiveRealization.yonedaSourceFunctor.map left ≫
        TraceAnalyticEffectiveRealization.yonedaSourceFunctor.map right :=
  TraceAnalyticEffectiveRealization.yonedaSourceFunctor.map_comp left right

/-- The analytic representable-source functor is the trace-correspondence
forgetful functor followed by lifted trace Yoneda. -/
theorem TraceAnalyticEffectiveRealization.yonedaSourceFunctor_eq_forgetful_comp_yoneda :
    TraceAnalyticEffectiveRealization.yonedaSourceFunctor =
      TraceAnalyticGeometricGenerator.forgetfulFunctor ⋙
        TraceCorQRepresentablePresheaf.yoneda :=
  rfl

/-- Including the analytic representable-source functor into trace presheaves
recovers the compact-generator presheaf functor. -/
theorem TraceAnalyticEffectiveRealization.yonedaSourceFunctor_comp_inclusion :
    TraceAnalyticEffectiveRealization.yonedaSourceFunctor ⋙
        TraceCorQRepresentablePresheaf.inclusion =
      TraceAnalyticGeometricGenerator.presheafFunctor :=
  rfl

end AnalyticMotives
end LFunctions
end Boundary
