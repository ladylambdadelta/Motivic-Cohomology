import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Root.CompactGeometric.Functors.Yoneda.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Root.CompactGeometric.Functors.Yoneda.Embedding.Owner

/-!
# Top-root compact-generator Yoneda wrappers

This file mirrors motive-root compact-generator Yoneda preimage and
hom-equivalence facts under `AnalyticMotivesRoot`.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Top-root compact Yoneda equivalence forward-map wrapper. -/
theorem AnalyticMotivesRoot.compactGenerator_yonedaHomEquiv_apply
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : source ⟶ target) :
    TraceAnalyticGeometricGenerator.yonedaHomEquiv
        source
        target
        morphism =
      morphism.representableObjectMap :=
  TraceAnalyticMotive.compactGenerator_yonedaHomEquiv_apply
    morphism

/-- Top-root compact Yoneda equivalence inverse-map wrapper. -/
theorem AnalyticMotivesRoot.compactGenerator_yonedaHomEquiv_symm_apply
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : source.representableObject ⟶ target.representableObject) :
    (TraceAnalyticGeometricGenerator.yonedaHomEquiv
        source
        target).symm morphism =
      TraceAnalyticGeometricGenerator.yonedaPreimage morphism :=
  TraceAnalyticMotive.compactGenerator_yonedaHomEquiv_symm_apply
    morphism

/-- Top-root compact Yoneda preimage of the lifted map is the original morphism. -/
theorem AnalyticMotivesRoot.compactGenerator_yonedaPreimage_representableObjectMap
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : source ⟶ target) :
    TraceAnalyticGeometricGenerator.yonedaPreimage
        morphism.representableObjectMap =
      morphism :=
  TraceAnalyticMotive.compactGenerator_yonedaPreimage_representableObjectMap
    morphism

/-- Top-root lifted map is recovered from compact Yoneda preimage. -/
theorem AnalyticMotivesRoot.compactGenerator_representableObjectMap_yonedaPreimage
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : source.representableObject ⟶ target.representableObject) :
    (TraceAnalyticGeometricGenerator.yonedaPreimage morphism).representableObjectMap =
      morphism :=
  TraceAnalyticMotive.compactGenerator_representableObjectMap_yonedaPreimage
    morphism

/-- Top-root compact Yoneda preimage sends identity to identity. -/
theorem AnalyticMotivesRoot.compactGenerator_yonedaPreimage_id
    (generator : TraceAnalyticGeometricGenerator) :
    TraceAnalyticGeometricGenerator.yonedaPreimage
        (𝟙 generator.representableObject) =
      𝟙 generator :=
  TraceAnalyticMotive.compactGenerator_yonedaPreimage_id
    generator

/-- Top-root compact Yoneda preimage sends composition to composition. -/
theorem AnalyticMotivesRoot.compactGenerator_yonedaPreimage_comp
    {first second third : TraceAnalyticGeometricGenerator}
    (left : first.representableObject ⟶ second.representableObject)
    (right : second.representableObject ⟶ third.representableObject) :
    TraceAnalyticGeometricGenerator.yonedaPreimage
        (left ≫ right) =
      TraceAnalyticGeometricGenerator.yonedaPreimage left ≫
        TraceAnalyticGeometricGenerator.yonedaPreimage right :=
  TraceAnalyticMotive.compactGenerator_yonedaPreimage_comp
    left
    right

end AnalyticMotives
end LFunctions
end Boundary
