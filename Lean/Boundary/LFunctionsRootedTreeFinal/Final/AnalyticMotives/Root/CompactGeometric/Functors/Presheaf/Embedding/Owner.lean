import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Root.CompactGeometric.Functors.Presheaf.Embedding.Owner

/-!
# Top-root compact-generator presheaf embedding wrappers

This file mirrors motive-root ambient representable-presheaf equality-reflection
and hom-lifting facts under `AnalyticMotivesRoot`.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Top-root ambient presheaf preimage of an induced map wrapper. -/
theorem AnalyticMotivesRoot.compactGenerator_presheafPreimage_representableMap
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : source ⟶ target) :
    TraceAnalyticGeometricGenerator.presheafPreimage
        morphism.representableMap =
      morphism :=
  TraceAnalyticMotive.compactGenerator_presheafPreimage_representableMap
    morphism

/-- Top-root ambient map is recovered from compact-generator preimage. -/
theorem AnalyticMotivesRoot.compactGenerator_representableMap_presheafPreimage
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : source.presheaf ⟶ target.presheaf) :
    (TraceAnalyticGeometricGenerator.presheafPreimage morphism).representableMap =
      morphism :=
  TraceAnalyticMotive.compactGenerator_representableMap_presheafPreimage
    morphism

/-- Top-root equality reflection for ambient representable maps. -/
theorem AnalyticMotivesRoot.compactGenerator_eq_of_representableMap_eq
    {source target : TraceAnalyticGeometricGenerator}
    {left right : source ⟶ target}
    (map_eq :
      left.representableMap =
        right.representableMap) :
    left = right :=
  TraceAnalyticMotive.compactGenerator_eq_of_representableMap_eq
    map_eq

/-- Top-root existence of compact-generator lifts for ambient presheaf maps. -/
theorem AnalyticMotivesRoot.compactGenerator_exists_representableMap_eq
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : source.presheaf ⟶ target.presheaf) :
    ∃ traceMorphism : source ⟶ target,
      traceMorphism.representableMap =
        morphism :=
  TraceAnalyticMotive.compactGenerator_exists_representableMap_eq
    morphism

/-- Top-root chosen ambient presheaf lift maps back to the original map. -/
theorem AnalyticMotivesRoot.compactGenerator_liftRepresentableMap_spec
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : source.presheaf ⟶ target.presheaf) :
    (TraceAnalyticGeometricGenerator.liftRepresentableMap morphism).representableMap =
      morphism :=
  TraceAnalyticMotive.compactGenerator_liftRepresentableMap_spec
    morphism

end AnalyticMotives
end LFunctions
end Boundary
