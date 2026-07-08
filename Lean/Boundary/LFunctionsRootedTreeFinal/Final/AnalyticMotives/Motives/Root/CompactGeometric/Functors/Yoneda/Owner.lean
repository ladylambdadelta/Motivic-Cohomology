import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.CompactGeometric.Generators.Functors.Yoneda.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Root.CompactGeometric.Functors.Yoneda.Embedding.Owner

/-!
# Motive-root compact-generator Yoneda wrappers

This file mirrors compact-generator Yoneda preimage and hom-equivalence facts
under `TraceAnalyticMotive`.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Motive-root compact Yoneda equivalence forward-map wrapper. -/
theorem TraceAnalyticMotive.compactGenerator_yonedaHomEquiv_apply
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : source ⟶ target) :
    TraceAnalyticGeometricGenerator.yonedaHomEquiv
        source
        target
        morphism =
      morphism.representableObjectMap :=
  TraceAnalyticGeometricGenerator.yonedaHomEquiv_apply
    morphism

/-- Motive-root compact Yoneda equivalence inverse-map wrapper. -/
theorem TraceAnalyticMotive.compactGenerator_yonedaHomEquiv_symm_apply
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : source.representableObject ⟶ target.representableObject) :
    (TraceAnalyticGeometricGenerator.yonedaHomEquiv
        source
        target).symm morphism =
      TraceAnalyticGeometricGenerator.yonedaPreimage morphism :=
  TraceAnalyticGeometricGenerator.yonedaHomEquiv_symm_apply
    morphism

/-- Motive-root compact Yoneda preimage of the lifted map is the original morphism. -/
theorem TraceAnalyticMotive.compactGenerator_yonedaPreimage_representableObjectMap
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : source ⟶ target) :
    TraceAnalyticGeometricGenerator.yonedaPreimage
        morphism.representableObjectMap =
      morphism :=
  TraceAnalyticGeometricGenerator.yonedaPreimage_representableObjectMap
    morphism

/-- Motive-root lifted map is recovered from compact Yoneda preimage. -/
theorem TraceAnalyticMotive.compactGenerator_representableObjectMap_yonedaPreimage
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : source.representableObject ⟶ target.representableObject) :
    (TraceAnalyticGeometricGenerator.yonedaPreimage morphism).representableObjectMap =
      morphism :=
  TraceAnalyticGeometricGenerator.representableObjectMap_yonedaPreimage
    morphism

/-- Motive-root compact Yoneda preimage sends identity to identity. -/
theorem TraceAnalyticMotive.compactGenerator_yonedaPreimage_id
    (generator : TraceAnalyticGeometricGenerator) :
    TraceAnalyticGeometricGenerator.yonedaPreimage
        (𝟙 generator.representableObject) =
      𝟙 generator :=
  TraceAnalyticGeometricGenerator.yonedaPreimage_id
    generator

/-- Motive-root compact Yoneda preimage sends composition to composition. -/
theorem TraceAnalyticMotive.compactGenerator_yonedaPreimage_comp
    {first second third : TraceAnalyticGeometricGenerator}
    (left : first.representableObject ⟶ second.representableObject)
    (right : second.representableObject ⟶ third.representableObject) :
    TraceAnalyticGeometricGenerator.yonedaPreimage
        (left ≫ right) =
      TraceAnalyticGeometricGenerator.yonedaPreimage left ≫
        TraceAnalyticGeometricGenerator.yonedaPreimage right :=
  TraceAnalyticGeometricGenerator.yonedaPreimage_comp
    left
    right

end AnalyticMotives
end LFunctions
end Boundary
