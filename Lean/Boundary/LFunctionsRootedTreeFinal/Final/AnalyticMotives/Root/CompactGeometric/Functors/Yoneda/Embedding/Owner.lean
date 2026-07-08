import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Root.CompactGeometric.Functors.Yoneda.Embedding.Owner

/-!
# Top-root compact-generator Yoneda embedding wrappers

This file mirrors motive-root lifted representable equality-reflection and
hom-lifting facts under `AnalyticMotivesRoot`.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Top-root equality reflection for lifted representable maps. -/
theorem AnalyticMotivesRoot.compactGenerator_eq_of_representableObjectMap_eq
    {source target : TraceAnalyticGeometricGenerator}
    {left right : source ⟶ target}
    (map_eq :
      left.representableObjectMap =
        right.representableObjectMap) :
    left = right :=
  TraceAnalyticMotive.compactGenerator_eq_of_representableObjectMap_eq
    map_eq

/-- Top-root existence of compact-generator lifts for lifted representable maps. -/
theorem AnalyticMotivesRoot.compactGenerator_exists_representableObjectMap_eq
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : source.representableObject ⟶ target.representableObject) :
    ∃ traceMorphism : source ⟶ target,
      traceMorphism.representableObjectMap =
        morphism :=
  TraceAnalyticMotive.compactGenerator_exists_representableObjectMap_eq
    morphism

/-- Top-root chosen lifted representable lift maps back to the original map. -/
theorem AnalyticMotivesRoot.compactGenerator_liftRepresentableObjectMap_spec
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : source.representableObject ⟶ target.representableObject) :
    (TraceAnalyticGeometricGenerator.liftRepresentableObjectMap morphism).representableObjectMap =
      morphism :=
  TraceAnalyticMotive.compactGenerator_liftRepresentableObjectMap_spec
    morphism

/-- Top-root lift of an induced lifted representable map is the original morphism. -/
theorem AnalyticMotivesRoot.compactGenerator_liftRepresentableObjectMap_representableObjectMap
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : source ⟶ target) :
    TraceAnalyticGeometricGenerator.liftRepresentableObjectMap
        morphism.representableObjectMap =
      morphism :=
  TraceAnalyticMotive.compactGenerator_liftRepresentableObjectMap_representableObjectMap
    morphism

end AnalyticMotives
end LFunctions
end Boundary
