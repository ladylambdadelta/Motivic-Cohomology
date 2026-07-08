import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.CompactGeometric.Generators.Functors.Yoneda.Embedding.Owner

/-!
# Motive-root compact-generator Yoneda embedding wrappers

This file mirrors lifted representable equality-reflection and hom-lifting
facts under `TraceAnalyticMotive`.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Motive-root equality reflection for lifted representable maps. -/
theorem TraceAnalyticMotive.compactGenerator_eq_of_representableObjectMap_eq
    {source target : TraceAnalyticGeometricGenerator}
    {left right : source ⟶ target}
    (map_eq :
      left.representableObjectMap =
        right.representableObjectMap) :
    left = right :=
  TraceAnalyticGeometricGenerator.eq_of_representableObjectMap_eq
    map_eq

/-- Motive-root existence of compact-generator lifts for lifted representable maps. -/
theorem TraceAnalyticMotive.compactGenerator_exists_representableObjectMap_eq
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : source.representableObject ⟶ target.representableObject) :
    ∃ traceMorphism : source ⟶ target,
      traceMorphism.representableObjectMap =
        morphism :=
  TraceAnalyticGeometricGenerator.exists_representableObjectMap_eq
    morphism

/-- Motive-root chosen lifted representable lift maps back to the original map. -/
theorem TraceAnalyticMotive.compactGenerator_liftRepresentableObjectMap_spec
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : source.representableObject ⟶ target.representableObject) :
    (TraceAnalyticGeometricGenerator.liftRepresentableObjectMap morphism).representableObjectMap =
      morphism :=
  TraceAnalyticGeometricGenerator.liftRepresentableObjectMap_spec
    morphism

/-- Motive-root lift of an induced lifted representable map is the original morphism. -/
theorem TraceAnalyticMotive.compactGenerator_liftRepresentableObjectMap_representableObjectMap
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : source ⟶ target) :
    TraceAnalyticGeometricGenerator.liftRepresentableObjectMap
        morphism.representableObjectMap =
      morphism :=
  TraceAnalyticGeometricGenerator.liftRepresentableObjectMap_representableObjectMap
    morphism

end AnalyticMotives
end LFunctions
end Boundary
