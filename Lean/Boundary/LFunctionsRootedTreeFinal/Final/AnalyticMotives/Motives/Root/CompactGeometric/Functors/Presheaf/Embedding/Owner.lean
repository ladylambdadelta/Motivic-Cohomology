import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.CompactGeometric.Generators.Functors.Presheaf.Embedding.Owner

/-!
# Motive-root compact-generator presheaf embedding wrappers

This file mirrors ambient representable-presheaf equality-reflection and
hom-lifting facts under `TraceAnalyticMotive`.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Motive-root ambient presheaf preimage of an induced map wrapper. -/
theorem TraceAnalyticMotive.compactGenerator_presheafPreimage_representableMap
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : source ⟶ target) :
    TraceAnalyticGeometricGenerator.presheafPreimage
        morphism.representableMap =
      morphism :=
  TraceAnalyticGeometricGenerator.presheafPreimage_representableMap
    morphism

/-- Motive-root ambient map is recovered from compact-generator preimage. -/
theorem TraceAnalyticMotive.compactGenerator_representableMap_presheafPreimage
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : source.presheaf ⟶ target.presheaf) :
    (TraceAnalyticGeometricGenerator.presheafPreimage morphism).representableMap =
      morphism :=
  TraceAnalyticGeometricGenerator.representableMap_presheafPreimage
    morphism

/-- Motive-root equality reflection for ambient representable maps. -/
theorem TraceAnalyticMotive.compactGenerator_eq_of_representableMap_eq
    {source target : TraceAnalyticGeometricGenerator}
    {left right : source ⟶ target}
    (map_eq :
      left.representableMap =
        right.representableMap) :
    left = right :=
  TraceAnalyticGeometricGenerator.eq_of_representableMap_eq
    map_eq

/-- Motive-root existence of compact-generator lifts for ambient presheaf maps. -/
theorem TraceAnalyticMotive.compactGenerator_exists_representableMap_eq
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : source.presheaf ⟶ target.presheaf) :
    ∃ traceMorphism : source ⟶ target,
      traceMorphism.representableMap =
        morphism :=
  TraceAnalyticGeometricGenerator.exists_representableMap_eq
    morphism

/-- Motive-root chosen ambient presheaf lift maps back to the original map. -/
theorem TraceAnalyticMotive.compactGenerator_liftRepresentableMap_spec
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : source.presheaf ⟶ target.presheaf) :
    (TraceAnalyticGeometricGenerator.liftRepresentableMap morphism).representableMap =
      morphism :=
  TraceAnalyticGeometricGenerator.liftRepresentableMap_spec
    morphism

end AnalyticMotives
end LFunctions
end Boundary
