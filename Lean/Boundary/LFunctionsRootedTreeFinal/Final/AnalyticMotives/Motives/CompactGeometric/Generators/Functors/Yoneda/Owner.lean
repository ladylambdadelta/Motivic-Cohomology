import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.CompactGeometric.Generators.Functors.Owner

/-!
# Yoneda hom equivalence for compact geometric analytic generators

This file specializes the lifted representable-presheaf Yoneda equivalence to
compact analytic generators.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- The lifted-Yoneda preimage of a morphism between compact-generator representables. -/
noncomputable def TraceAnalyticGeometricGenerator.yonedaPreimage
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : source.representableObject ⟶ target.representableObject) :
    source ⟶ target :=
  TraceCorQRepresentablePresheaf.yonedaPreimage morphism

/-- Compact-generator morphisms are equivalent to morphisms between their lifted representables. -/
noncomputable def TraceAnalyticGeometricGenerator.yonedaHomEquiv
    (source target : TraceAnalyticGeometricGenerator) :
    (source ⟶ target) ≃
      (source.representableObject ⟶ target.representableObject) :=
  TraceCorQRepresentablePresheaf.yonedaHomEquiv
    source.traceObject
    target.traceObject

/-- The forward map of the compact-generator Yoneda equivalence is the lifted map. -/
theorem TraceAnalyticGeometricGenerator.yonedaHomEquiv_apply
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : source ⟶ target) :
    TraceAnalyticGeometricGenerator.yonedaHomEquiv
        source
        target
        morphism =
      morphism.representableObjectMap :=
  rfl

/-- The inverse map of the compact-generator Yoneda equivalence is compact Yoneda preimage. -/
theorem TraceAnalyticGeometricGenerator.yonedaHomEquiv_symm_apply
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : source.representableObject ⟶ target.representableObject) :
    (TraceAnalyticGeometricGenerator.yonedaHomEquiv
        source
        target).symm morphism =
      TraceAnalyticGeometricGenerator.yonedaPreimage morphism :=
  rfl

/-- The compact Yoneda preimage of the induced lifted map is the original morphism. -/
theorem TraceAnalyticGeometricGenerator.yonedaPreimage_representableObjectMap
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : source ⟶ target) :
    TraceAnalyticGeometricGenerator.yonedaPreimage
        morphism.representableObjectMap =
      morphism :=
  TraceCorQRepresentablePresheaf.yonedaPreimage_yonedaMap
    morphism.traceHom

/-- Every lifted representable morphism is the lifted map of its compact Yoneda preimage. -/
theorem TraceAnalyticGeometricGenerator.representableObjectMap_yonedaPreimage
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : source.representableObject ⟶ target.representableObject) :
    (TraceAnalyticGeometricGenerator.yonedaPreimage morphism).representableObjectMap =
      morphism :=
  TraceCorQRepresentablePresheaf.yonedaMap_yonedaPreimage morphism

/-- Compact Yoneda preimage sends identity to identity. -/
theorem TraceAnalyticGeometricGenerator.yonedaPreimage_id
    (generator : TraceAnalyticGeometricGenerator) :
    TraceAnalyticGeometricGenerator.yonedaPreimage
        (𝟙 generator.representableObject) =
      𝟙 generator :=
  TraceCorQRepresentablePresheaf.yonedaPreimage_id
    generator.traceObject

/-- Compact Yoneda preimage sends composition to composition. -/
theorem TraceAnalyticGeometricGenerator.yonedaPreimage_comp
    {first second third : TraceAnalyticGeometricGenerator}
    (left : first.representableObject ⟶ second.representableObject)
    (right : second.representableObject ⟶ third.representableObject) :
    TraceAnalyticGeometricGenerator.yonedaPreimage
        (left ≫ right) =
      TraceAnalyticGeometricGenerator.yonedaPreimage left ≫
        TraceAnalyticGeometricGenerator.yonedaPreimage right :=
  TraceCorQRepresentablePresheaf.yonedaPreimage_comp left right

end AnalyticMotives
end LFunctions
end Boundary
