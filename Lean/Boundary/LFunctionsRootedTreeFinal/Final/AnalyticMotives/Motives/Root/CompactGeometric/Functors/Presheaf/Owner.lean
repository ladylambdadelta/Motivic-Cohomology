import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.CompactGeometric.Generators.Functors.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Root.CompactGeometric.Functors.Presheaf.Embedding.Owner

/-!
# Motive-root compact-generator presheaf functor wrappers

This file mirrors the compact-generator presheaf and lifted representable
functor facts under `TraceAnalyticMotive`.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Motive-root presheaf functor object wrapper. -/
theorem TraceAnalyticMotive.compactGenerator_presheafFunctor_obj
    (generator : TraceAnalyticGeometricGenerator) :
    TraceAnalyticGeometricGenerator.presheafFunctor.obj generator =
      generator.presheaf :=
  TraceAnalyticGeometricGenerator.presheafFunctor_obj
    generator

/-- Motive-root presheaf functor map wrapper. -/
theorem TraceAnalyticMotive.compactGenerator_presheafFunctor_map
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : source ⟶ target) :
    TraceAnalyticGeometricGenerator.presheafFunctor.map morphism =
      morphism.representableMap :=
  TraceAnalyticGeometricGenerator.presheafFunctor_map
    morphism

/-- Motive-root lifted representable functor object wrapper. -/
theorem TraceAnalyticMotive.compactGenerator_representableObjectFunctor_obj
    (generator : TraceAnalyticGeometricGenerator) :
    TraceAnalyticGeometricGenerator.representableObjectFunctor.obj generator =
      generator.representableObject :=
  TraceAnalyticGeometricGenerator.representableObjectFunctor_obj
    generator

/-- Motive-root lifted representable functor map wrapper. -/
theorem TraceAnalyticMotive.compactGenerator_representableObjectFunctor_map
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : source ⟶ target) :
    TraceAnalyticGeometricGenerator.representableObjectFunctor.map morphism =
      morphism.representableObjectMap :=
  TraceAnalyticGeometricGenerator.representableObjectFunctor_map
    morphism

/-- Motive-root lifted representable functor includes to the presheaf functor. -/
theorem TraceAnalyticMotive.compactGenerator_representableObjectFunctor_comp_inclusion :
    TraceAnalyticGeometricGenerator.representableObjectFunctor ⋙
        TraceCorQRepresentablePresheaf.inclusion =
      TraceAnalyticGeometricGenerator.presheafFunctor :=
  TraceAnalyticGeometricGenerator.representableObjectFunctor_comp_inclusion

/-- Motive-root lifted representable functor object is trace Yoneda. -/
theorem TraceAnalyticMotive.compactGenerator_representableObjectFunctor_obj_eq_yoneda
    (generator : TraceAnalyticGeometricGenerator) :
    TraceAnalyticGeometricGenerator.representableObjectFunctor.obj generator =
      (TraceCorQRepresentablePresheaf.yoneda).obj generator.traceObject :=
  TraceAnalyticGeometricGenerator.representableObjectFunctor_obj_eq_yoneda
    generator

/-- Motive-root lifted representable functor map is trace Yoneda. -/
theorem TraceAnalyticMotive.compactGenerator_representableObjectFunctor_map_eq_yoneda
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : source ⟶ target) :
    TraceAnalyticGeometricGenerator.representableObjectFunctor.map morphism =
      (TraceCorQRepresentablePresheaf.yoneda).map morphism.traceHom :=
  TraceAnalyticGeometricGenerator.representableObjectFunctor_map_eq_yoneda
    morphism

end AnalyticMotives
end LFunctions
end Boundary
