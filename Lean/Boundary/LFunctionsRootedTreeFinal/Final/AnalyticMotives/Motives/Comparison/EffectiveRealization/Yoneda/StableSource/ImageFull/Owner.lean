import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Comparison.EffectiveRealization.Yoneda.FullFaithful.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Comparison.EffectiveRealization.Yoneda.StableSource.Preimage.Owner

/-!
# Image fullness for the effective-realization stable source

This file records the part of stable-source fullness that is already supplied
by the Yoneda preimage calculus: every stable-source map in the image of a
compact-generator morphism is recovered from the corresponding Yoneda
representable map.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory

/-- A compact-generator morphism gives a Yoneda representable map whose
recovered stable-source map is the original stable-source image. -/
theorem TraceAnalyticEffectiveRealization.stableSourceFunctor_imageFull_witness
    {source target : TraceAnalyticGeometricGenerator}
    (hom : source ⟶ target) :
    ∃ yonedaMap :
      (TraceAnalyticEffectiveRealization.yonedaSourceFunctor.obj source) ⟶
        (TraceAnalyticEffectiveRealization.yonedaSourceFunctor.obj target),
      TraceAnalyticEffectiveRealization.stableSourceMapOfYonedaPreimage
          yonedaMap =
        TraceAnalyticEffectiveRealization.stableSourceFunctor.map hom :=
  Exists.intro
    (TraceAnalyticEffectiveRealization.yonedaSourceFunctor.map hom)
    (TraceAnalyticEffectiveRealization.stableSourceMapOfYonedaPreimage_map hom)

/-- The canonical Yoneda witness for stable-source image fullness is the
Yoneda source functor map. -/
theorem TraceAnalyticEffectiveRealization.stableSourceFunctor_imageFull_witness_eq_yonedaMap
    {source target : TraceAnalyticGeometricGenerator}
    (hom : source ⟶ target) :
    TraceAnalyticEffectiveRealization.yonedaSourceFunctor.map hom =
      TraceAnalyticEffectiveRealization.yonedaSourceHomEquiv source target hom :=
  Eq.symm
    (TraceAnalyticEffectiveRealization.yonedaSourceHomEquiv_apply hom)

/-- The stable-source image recovered from the Yoneda witness has the
comparison-source generator-map normal form. -/
theorem TraceAnalyticEffectiveRealization.stableSourceFunctor_imageFull_eq_sourceGeneratorMap
    {source target : TraceAnalyticGeometricGenerator}
    (hom : source ⟶ target) :
    TraceAnalyticEffectiveRealization.stableSourceMapOfYonedaPreimage
        (TraceAnalyticEffectiveRealization.yonedaSourceFunctor.map hom) =
      TraceAnalyticMotiveComparison.sourceGeneratorMap hom :=
  Eq.trans
    (TraceAnalyticEffectiveRealization.stableSourceMapOfYonedaPreimage_map hom)
    (TraceAnalyticEffectiveRealization.stableSourceFunctor_map hom)

/-- The stable-source image recovered from the Yoneda witness has the stable
`mapOf` normal form. -/
theorem TraceAnalyticEffectiveRealization.stableSourceFunctor_imageFull_eq_stable
    {source target : TraceAnalyticGeometricGenerator}
    (hom : source ⟶ target) :
    TraceAnalyticEffectiveRealization.stableSourceMapOfYonedaPreimage
        (TraceAnalyticEffectiveRealization.yonedaSourceFunctor.map hom) =
      TraceAnalyticStableMotiveCategory.mapOf
        (TraceAnalyticMotiveComparison.sourceTraceHomotopyMap hom.traceHom) :=
  Eq.trans
    (TraceAnalyticEffectiveRealization.stableSourceMapOfYonedaPreimage_map hom)
    (TraceAnalyticEffectiveRealization.stableSourceFunctor_map_eq_stable hom)

/-- The stable-source image recovered from the Yoneda witness has the Verdier
quotient-functor normal form. -/
theorem TraceAnalyticEffectiveRealization.stableSourceFunctor_imageFull_eq_quotientFunctor_map
    {source target : TraceAnalyticGeometricGenerator}
    (hom : source ⟶ target) :
    TraceAnalyticEffectiveRealization.stableSourceMapOfYonedaPreimage
        (TraceAnalyticEffectiveRealization.yonedaSourceFunctor.map hom) =
      TraceAnalyticStableMotiveCategory.quotientFunctor.map
        (TraceAnalyticMotiveComparison.sourceTraceHomotopyMap hom.traceHom) :=
  Eq.trans
    (TraceAnalyticEffectiveRealization.stableSourceMapOfYonedaPreimage_map hom)
    (TraceAnalyticEffectiveRealization.stableSourceFunctor_map_eq_quotientFunctor_map
      hom)

/-- Equal Yoneda source maps recover equal stable-source maps. -/
theorem TraceAnalyticEffectiveRealization.stableSourceMapOfYonedaPreimage_respects_yoneda_eq
    {source target : TraceAnalyticGeometricGenerator}
    {left right :
      (TraceAnalyticEffectiveRealization.yonedaSourceFunctor.obj source) ⟶
        (TraceAnalyticEffectiveRealization.yonedaSourceFunctor.obj target)}
    (yoneda_eq : left = right) :
    TraceAnalyticEffectiveRealization.stableSourceMapOfYonedaPreimage left =
      TraceAnalyticEffectiveRealization.stableSourceMapOfYonedaPreimage right :=
  congrArg
    (fun morphism =>
      TraceAnalyticEffectiveRealization.stableSourceMapOfYonedaPreimage
        morphism)
    yoneda_eq

end AnalyticMotives
end LFunctions
end Boundary
