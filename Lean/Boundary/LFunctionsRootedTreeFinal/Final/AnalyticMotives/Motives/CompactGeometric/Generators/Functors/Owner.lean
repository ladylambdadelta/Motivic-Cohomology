import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.CompactGeometric.Generators.Category.Owner

/-!
# Functors out of compact geometric analytic generators

This file packages the concrete functors already supplied by the generator
data: the representable-presheaf functor into all trace presheaves and its
lift into the representable full subcategory.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- The representable presheaf functor on compact analytic generators. -/
def TraceAnalyticGeometricGenerator.presheafFunctor :
    TraceAnalyticGeometricGenerator ⥤ TraceCorQPresheaf where
  obj := fun generator =>
    generator.presheaf
  map := fun morphism =>
    morphism.representableMap
  map_id := fun generator =>
    TraceAnalyticGeometricGenerator.id_representableMap generator
  map_comp := fun left right =>
    TraceAnalyticGeometricGenerator.comp_representableMap left right

/-- The lifted representable-subcategory functor on compact analytic generators. -/
def TraceAnalyticGeometricGenerator.representableObjectFunctor :
    TraceAnalyticGeometricGenerator ⥤ TraceCorQRepresentablePresheaf where
  obj := fun generator =>
    generator.representableObject
  map := fun morphism =>
    morphism.representableObjectMap
  map_id := fun generator =>
    (TraceCorQRepresentablePresheaf.yoneda).map_id generator.traceObject
  map_comp := fun left right =>
    (TraceCorQRepresentablePresheaf.yoneda).map_comp
      left.traceHom
      right.traceHom

/-- The presheaf functor sends a generator to its representable presheaf. -/
theorem TraceAnalyticGeometricGenerator.presheafFunctor_obj
    (generator : TraceAnalyticGeometricGenerator) :
    TraceAnalyticGeometricGenerator.presheafFunctor.obj generator =
      generator.presheaf :=
  rfl

/-- The presheaf functor sends a morphism to its induced representable map. -/
theorem TraceAnalyticGeometricGenerator.presheafFunctor_map
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : source ⟶ target) :
    TraceAnalyticGeometricGenerator.presheafFunctor.map morphism =
      morphism.representableMap :=
  rfl

/-- The lifted representable functor sends a generator to its lifted representable object. -/
theorem TraceAnalyticGeometricGenerator.representableObjectFunctor_obj
    (generator : TraceAnalyticGeometricGenerator) :
    TraceAnalyticGeometricGenerator.representableObjectFunctor.obj generator =
      generator.representableObject :=
  rfl

/-- The lifted representable functor sends a morphism to its lifted representable map. -/
theorem TraceAnalyticGeometricGenerator.representableObjectFunctor_map
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : source ⟶ target) :
    TraceAnalyticGeometricGenerator.representableObjectFunctor.map morphism =
      morphism.representableObjectMap :=
  rfl

/-- Including the lifted representable functor gives the presheaf functor. -/
theorem TraceAnalyticGeometricGenerator.representableObjectFunctor_comp_inclusion :
    TraceAnalyticGeometricGenerator.representableObjectFunctor ⋙
        TraceCorQRepresentablePresheaf.inclusion =
      TraceAnalyticGeometricGenerator.presheafFunctor :=
  rfl

/-- The lifted representable functor is the trace Yoneda functor after forgetting generators. -/
theorem TraceAnalyticGeometricGenerator.representableObjectFunctor_obj_eq_yoneda
    (generator : TraceAnalyticGeometricGenerator) :
    TraceAnalyticGeometricGenerator.representableObjectFunctor.obj generator =
      (TraceCorQRepresentablePresheaf.yoneda).obj generator.traceObject :=
  rfl

/-- The lifted representable functor map is the trace Yoneda map of the underlying trace hom. -/
theorem TraceAnalyticGeometricGenerator.representableObjectFunctor_map_eq_yoneda
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : source ⟶ target) :
    TraceAnalyticGeometricGenerator.representableObjectFunctor.map morphism =
      (TraceCorQRepresentablePresheaf.yoneda).map morphism.traceHom :=
  rfl

end AnalyticMotives
end LFunctions
end Boundary
