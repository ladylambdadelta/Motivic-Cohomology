import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Root.CompactGeometric.Functors.Presheaf.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Root.CompactGeometric.Functors.Presheaf.Embedding.Owner

/-!
# Top-root compact-generator presheaf functor wrappers

This file mirrors motive-root compact-generator presheaf and lifted
representable functor facts under `AnalyticMotivesRoot`.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Top-root presheaf functor object wrapper. -/
theorem AnalyticMotivesRoot.compactGenerator_presheafFunctor_obj
    (generator : TraceAnalyticGeometricGenerator) :
    TraceAnalyticGeometricGenerator.presheafFunctor.obj generator =
      generator.presheaf :=
  TraceAnalyticMotive.compactGenerator_presheafFunctor_obj
    generator

/-- Top-root presheaf functor map wrapper. -/
theorem AnalyticMotivesRoot.compactGenerator_presheafFunctor_map
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : source ⟶ target) :
    TraceAnalyticGeometricGenerator.presheafFunctor.map morphism =
      morphism.representableMap :=
  TraceAnalyticMotive.compactGenerator_presheafFunctor_map
    morphism

/-- Top-root lifted representable functor object wrapper. -/
theorem AnalyticMotivesRoot.compactGenerator_representableObjectFunctor_obj
    (generator : TraceAnalyticGeometricGenerator) :
    TraceAnalyticGeometricGenerator.representableObjectFunctor.obj generator =
      generator.representableObject :=
  TraceAnalyticMotive.compactGenerator_representableObjectFunctor_obj
    generator

/-- Top-root lifted representable functor map wrapper. -/
theorem AnalyticMotivesRoot.compactGenerator_representableObjectFunctor_map
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : source ⟶ target) :
    TraceAnalyticGeometricGenerator.representableObjectFunctor.map morphism =
      morphism.representableObjectMap :=
  TraceAnalyticMotive.compactGenerator_representableObjectFunctor_map
    morphism

/-- Top-root lifted representable functor includes to the presheaf functor. -/
theorem AnalyticMotivesRoot.compactGenerator_representableObjectFunctor_comp_inclusion :
    TraceAnalyticGeometricGenerator.representableObjectFunctor ⋙
        TraceCorQRepresentablePresheaf.inclusion =
      TraceAnalyticGeometricGenerator.presheafFunctor :=
  TraceAnalyticMotive.compactGenerator_representableObjectFunctor_comp_inclusion

/-- Top-root lifted representable functor object is trace Yoneda. -/
theorem AnalyticMotivesRoot.compactGenerator_representableObjectFunctor_obj_eq_yoneda
    (generator : TraceAnalyticGeometricGenerator) :
    TraceAnalyticGeometricGenerator.representableObjectFunctor.obj generator =
      (TraceCorQRepresentablePresheaf.yoneda).obj generator.traceObject :=
  TraceAnalyticMotive.compactGenerator_representableObjectFunctor_obj_eq_yoneda
    generator

/-- Top-root lifted representable functor map is trace Yoneda. -/
theorem AnalyticMotivesRoot.compactGenerator_representableObjectFunctor_map_eq_yoneda
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : source ⟶ target) :
    TraceAnalyticGeometricGenerator.representableObjectFunctor.map morphism =
      (TraceCorQRepresentablePresheaf.yoneda).map morphism.traceHom :=
  TraceAnalyticMotive.compactGenerator_representableObjectFunctor_map_eq_yoneda
    morphism

end AnalyticMotives
end LFunctions
end Boundary
