import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Comparison.EffectiveRealization.Yoneda.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.CompactGeometric.Generators.Functors.Yoneda.Owner

/-!
# Yoneda preimages at the effective-realization source boundary

This file exposes the concrete morphism recovered from a morphism of
trace-Yoneda representables.  These are the source-side hom formulas that a
realization comparison preserves.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- The effective-realization source-side Yoneda preimage of a representable
map. -/
noncomputable def TraceAnalyticEffectiveRealization.yonedaSourcePreimage
    {source target : TraceAnalyticGeometricGenerator}
    (morphism :
      (TraceAnalyticEffectiveRealization.yonedaSourceFunctor.obj source) ⟶
        (TraceAnalyticEffectiveRealization.yonedaSourceFunctor.obj target)) :
    source ⟶ target :=
  TraceAnalyticGeometricGenerator.yonedaPreimage morphism

/-- Compact-generator morphisms are equivalent to morphisms between their
effective-realization source representables. -/
noncomputable def TraceAnalyticEffectiveRealization.yonedaSourceHomEquiv
    (source target : TraceAnalyticGeometricGenerator) :
    (source ⟶ target) ≃
      ((TraceAnalyticEffectiveRealization.yonedaSourceFunctor.obj source) ⟶
        (TraceAnalyticEffectiveRealization.yonedaSourceFunctor.obj target)) :=
  TraceAnalyticGeometricGenerator.yonedaHomEquiv source target

/-- The source Yoneda preimage agrees with the compact-generator Yoneda
preimage. -/
theorem TraceAnalyticEffectiveRealization.yonedaSourcePreimage_eq_compact
    {source target : TraceAnalyticGeometricGenerator}
    (morphism :
      (TraceAnalyticEffectiveRealization.yonedaSourceFunctor.obj source) ⟶
        (TraceAnalyticEffectiveRealization.yonedaSourceFunctor.obj target)) :
    TraceAnalyticEffectiveRealization.yonedaSourcePreimage morphism =
      TraceAnalyticGeometricGenerator.yonedaPreimage morphism :=
  rfl

/-- The forward map of the source Yoneda hom equivalence is the
effective-realization source functor on morphisms. -/
theorem TraceAnalyticEffectiveRealization.yonedaSourceHomEquiv_apply
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : source ⟶ target) :
    TraceAnalyticEffectiveRealization.yonedaSourceHomEquiv source target
        morphism =
      TraceAnalyticEffectiveRealization.yonedaSourceFunctor.map morphism :=
  rfl

/-- The inverse map of the source Yoneda hom equivalence is source Yoneda
preimage. -/
theorem TraceAnalyticEffectiveRealization.yonedaSourceHomEquiv_symm_apply
    {source target : TraceAnalyticGeometricGenerator}
    (morphism :
      (TraceAnalyticEffectiveRealization.yonedaSourceFunctor.obj source) ⟶
        (TraceAnalyticEffectiveRealization.yonedaSourceFunctor.obj target)) :
    (TraceAnalyticEffectiveRealization.yonedaSourceHomEquiv source target).symm
        morphism =
      TraceAnalyticEffectiveRealization.yonedaSourcePreimage morphism :=
  rfl

/-- The source Yoneda preimage of the source functor map is the original
compact-generator morphism. -/
theorem TraceAnalyticEffectiveRealization.yonedaSourcePreimage_map
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : source ⟶ target) :
    TraceAnalyticEffectiveRealization.yonedaSourcePreimage
        (TraceAnalyticEffectiveRealization.yonedaSourceFunctor.map morphism) =
      morphism :=
  TraceAnalyticGeometricGenerator.yonedaPreimage_representableObjectMap
    morphism

/-- The source functor map of a source Yoneda preimage is the original
representable morphism. -/
theorem TraceAnalyticEffectiveRealization.yonedaSourceMap_preimage
    {source target : TraceAnalyticGeometricGenerator}
    (morphism :
      (TraceAnalyticEffectiveRealization.yonedaSourceFunctor.obj source) ⟶
        (TraceAnalyticEffectiveRealization.yonedaSourceFunctor.obj target)) :
    TraceAnalyticEffectiveRealization.yonedaSourceFunctor.map
        (TraceAnalyticEffectiveRealization.yonedaSourcePreimage morphism) =
      morphism :=
  TraceAnalyticGeometricGenerator.representableObjectMap_yonedaPreimage
    morphism

/-- Source Yoneda preimage sends identity to identity. -/
theorem TraceAnalyticEffectiveRealization.yonedaSourcePreimage_id
    (generator : TraceAnalyticGeometricGenerator) :
    TraceAnalyticEffectiveRealization.yonedaSourcePreimage
        (𝟙 (TraceAnalyticEffectiveRealization.yonedaSourceFunctor.obj generator)) =
      𝟙 generator :=
  TraceAnalyticGeometricGenerator.yonedaPreimage_id generator

/-- Source Yoneda preimage sends composition to composition. -/
theorem TraceAnalyticEffectiveRealization.yonedaSourcePreimage_comp
    {first second third : TraceAnalyticGeometricGenerator}
    (left :
      (TraceAnalyticEffectiveRealization.yonedaSourceFunctor.obj first) ⟶
        (TraceAnalyticEffectiveRealization.yonedaSourceFunctor.obj second))
    (right :
      (TraceAnalyticEffectiveRealization.yonedaSourceFunctor.obj second) ⟶
        (TraceAnalyticEffectiveRealization.yonedaSourceFunctor.obj third)) :
    TraceAnalyticEffectiveRealization.yonedaSourcePreimage (left ≫ right) =
      TraceAnalyticEffectiveRealization.yonedaSourcePreimage left ≫
        TraceAnalyticEffectiveRealization.yonedaSourcePreimage right :=
  TraceAnalyticGeometricGenerator.yonedaPreimage_comp left right

end AnalyticMotives
end LFunctions
end Boundary
