import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Comparison.EffectiveRealization.Yoneda.Preimage.TraceHom.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Comparison.EffectiveRealization.Yoneda.StableSource.Owner

/-!
# Stable-source maps recovered from Yoneda source preimages

This file sends a morphism between effective-realization Yoneda source
representables to the corresponding stable-source map by taking its Yoneda
preimage and applying the stable source functor.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory

/-- The stable-source map recovered from a morphism of effective-realization
Yoneda source representables. -/
def TraceAnalyticEffectiveRealization.stableSourceMapOfYonedaPreimage
    {source target : TraceAnalyticGeometricGenerator}
    (morphism :
      (TraceAnalyticEffectiveRealization.yonedaSourceFunctor.obj source) ⟶
        (TraceAnalyticEffectiveRealization.yonedaSourceFunctor.obj target)) :
    TraceAnalyticEffectiveRealization.stableSourceFunctor.obj source ⟶
      TraceAnalyticEffectiveRealization.stableSourceFunctor.obj target :=
  TraceAnalyticEffectiveRealization.stableSourceFunctor.map
    (TraceAnalyticEffectiveRealization.yonedaSourcePreimage morphism)

/-- Recovering a stable-source map from a Yoneda source functor map gives the
stable source functor map of the original compact-generator morphism. -/
theorem TraceAnalyticEffectiveRealization.stableSourceMapOfYonedaPreimage_map
    {source target : TraceAnalyticGeometricGenerator}
    (hom : source ⟶ target) :
    TraceAnalyticEffectiveRealization.stableSourceMapOfYonedaPreimage
        (TraceAnalyticEffectiveRealization.yonedaSourceFunctor.map hom) =
      TraceAnalyticEffectiveRealization.stableSourceFunctor.map hom :=
  congrArg
    (fun recovered =>
      TraceAnalyticEffectiveRealization.stableSourceFunctor.map recovered)
    (TraceAnalyticEffectiveRealization.yonedaSourcePreimage_map hom)

/-- The stable-source map recovered from a Yoneda source morphism is the
comparison-source generator map of its compact-generator preimage. -/
theorem TraceAnalyticEffectiveRealization.stableSourceMapOfYonedaPreimage_eq_sourceGeneratorMap
    {source target : TraceAnalyticGeometricGenerator}
    (morphism :
      (TraceAnalyticEffectiveRealization.yonedaSourceFunctor.obj source) ⟶
        (TraceAnalyticEffectiveRealization.yonedaSourceFunctor.obj target)) :
    TraceAnalyticEffectiveRealization.stableSourceMapOfYonedaPreimage
        morphism =
      TraceAnalyticMotiveComparison.sourceGeneratorMap
        (TraceAnalyticEffectiveRealization.yonedaSourcePreimage morphism) :=
  rfl

/-- The stable-source map recovered from a Yoneda source morphism is generated
by the trace-source functor applied to the recovered trace correspondence. -/
theorem TraceAnalyticEffectiveRealization.stableSourceMapOfYonedaPreimage_eq_sourceTraceFunctor_map
    {source target : TraceAnalyticGeometricGenerator}
    (morphism :
      (TraceAnalyticEffectiveRealization.yonedaSourceFunctor.obj source) ⟶
        (TraceAnalyticEffectiveRealization.yonedaSourceFunctor.obj target)) :
    TraceAnalyticEffectiveRealization.stableSourceMapOfYonedaPreimage
        morphism =
      TraceAnalyticMotiveComparison.sourceTraceFunctor.map
        (TraceAnalyticEffectiveRealization.yonedaSourcePreimageTraceHom
          morphism) :=
  rfl

/-- The stable-source map recovered from a Yoneda source morphism is the
stable analytic quotient image of the recovered endpoint trace homotopy map. -/
theorem TraceAnalyticEffectiveRealization.stableSourceMapOfYonedaPreimage_eq_stable
    {source target : TraceAnalyticGeometricGenerator}
    (morphism :
      (TraceAnalyticEffectiveRealization.yonedaSourceFunctor.obj source) ⟶
        (TraceAnalyticEffectiveRealization.yonedaSourceFunctor.obj target)) :
    TraceAnalyticEffectiveRealization.stableSourceMapOfYonedaPreimage
        morphism =
      TraceAnalyticStableMotiveCategory.mapOf
        (TraceAnalyticMotiveComparison.sourceTraceHomotopyMap
          (TraceAnalyticEffectiveRealization.yonedaSourcePreimageTraceHom
            morphism)) :=
  TraceAnalyticMotiveComparison.sourceGeneratorMap_eq_stable
    (TraceAnalyticEffectiveRealization.yonedaSourcePreimage morphism)

/-- The stable-source map recovered from a Yoneda source morphism is the
Verdier quotient-functor image of the recovered endpoint trace homotopy map. -/
theorem TraceAnalyticEffectiveRealization.stableSourceMapOfYonedaPreimage_eq_quotientFunctor_map
    {source target : TraceAnalyticGeometricGenerator}
    (morphism :
      (TraceAnalyticEffectiveRealization.yonedaSourceFunctor.obj source) ⟶
        (TraceAnalyticEffectiveRealization.yonedaSourceFunctor.obj target)) :
    TraceAnalyticEffectiveRealization.stableSourceMapOfYonedaPreimage
        morphism =
      TraceAnalyticStableMotiveCategory.quotientFunctor.map
        (TraceAnalyticMotiveComparison.sourceTraceHomotopyMap
          (TraceAnalyticEffectiveRealization.yonedaSourcePreimageTraceHom
            morphism)) :=
  TraceAnalyticMotiveComparison.sourceGeneratorMap_eq_quotientFunctor_map
    (TraceAnalyticEffectiveRealization.yonedaSourcePreimage morphism)

/-- The stable-source map recovered from a Yoneda source identity is the stable
source identity. -/
theorem TraceAnalyticEffectiveRealization.stableSourceMapOfYonedaPreimage_id
    (generator : TraceAnalyticGeometricGenerator) :
    TraceAnalyticEffectiveRealization.stableSourceMapOfYonedaPreimage
        (𝟙 (TraceAnalyticEffectiveRealization.yonedaSourceFunctor.obj generator)) =
      𝟙 (TraceAnalyticEffectiveRealization.stableSourceFunctor.obj generator) :=
  Eq.trans
    (congrArg
      (fun recovered =>
        TraceAnalyticEffectiveRealization.stableSourceFunctor.map recovered)
      (TraceAnalyticEffectiveRealization.yonedaSourcePreimage_id generator))
    (TraceAnalyticEffectiveRealization.stableSourceFunctor.map_id generator)

/-- The stable-source map recovered from a Yoneda source composite is the
composite of the recovered stable-source maps. -/
theorem TraceAnalyticEffectiveRealization.stableSourceMapOfYonedaPreimage_comp
    {first second third : TraceAnalyticGeometricGenerator}
    (left :
      (TraceAnalyticEffectiveRealization.yonedaSourceFunctor.obj first) ⟶
        (TraceAnalyticEffectiveRealization.yonedaSourceFunctor.obj second))
    (right :
      (TraceAnalyticEffectiveRealization.yonedaSourceFunctor.obj second) ⟶
        (TraceAnalyticEffectiveRealization.yonedaSourceFunctor.obj third)) :
    TraceAnalyticEffectiveRealization.stableSourceMapOfYonedaPreimage
        (left ≫ right) =
      TraceAnalyticEffectiveRealization.stableSourceMapOfYonedaPreimage left ≫
        TraceAnalyticEffectiveRealization.stableSourceMapOfYonedaPreimage right :=
  Eq.trans
    (congrArg
      (fun recovered =>
        TraceAnalyticEffectiveRealization.stableSourceFunctor.map recovered)
      (TraceAnalyticEffectiveRealization.yonedaSourcePreimage_comp
        left
        right))
    (TraceAnalyticEffectiveRealization.stableSourceFunctor.map_comp
      (TraceAnalyticEffectiveRealization.yonedaSourcePreimage left)
      (TraceAnalyticEffectiveRealization.yonedaSourcePreimage right))

end AnalyticMotives
end LFunctions
end Boundary
