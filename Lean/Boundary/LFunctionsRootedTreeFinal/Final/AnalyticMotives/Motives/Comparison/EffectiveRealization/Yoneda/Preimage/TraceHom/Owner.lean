import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Comparison.EffectiveRealization.Yoneda.Preimage.Owner

/-!
# Trace-hom projections of effective-realization source Yoneda preimages

This file exposes the underlying trace correspondence recovered from a
morphism between effective-realization source representables.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- The trace correspondence underlying a source-side Yoneda preimage. -/
noncomputable def TraceAnalyticEffectiveRealization.yonedaSourcePreimageTraceHom
    {source target : TraceAnalyticGeometricGenerator}
    (morphism :
      (TraceAnalyticEffectiveRealization.yonedaSourceFunctor.obj source) ⟶
        (TraceAnalyticEffectiveRealization.yonedaSourceFunctor.obj target)) :
    source.traceObject ⟶ target.traceObject :=
  (TraceAnalyticEffectiveRealization.yonedaSourcePreimage morphism).traceHom

/-- The trace-hom projection of a source Yoneda preimage is the trace hom of
the compact-generator Yoneda preimage. -/
theorem TraceAnalyticEffectiveRealization.yonedaSourcePreimageTraceHom_eq_compact
    {source target : TraceAnalyticGeometricGenerator}
    (morphism :
      (TraceAnalyticEffectiveRealization.yonedaSourceFunctor.obj source) ⟶
        (TraceAnalyticEffectiveRealization.yonedaSourceFunctor.obj target)) :
    TraceAnalyticEffectiveRealization.yonedaSourcePreimageTraceHom morphism =
      (TraceAnalyticGeometricGenerator.yonedaPreimage morphism).traceHom :=
  rfl

/-- The trace-hom projection of the source functor map is the original trace
hom. -/
theorem TraceAnalyticEffectiveRealization.yonedaSourcePreimageTraceHom_map
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : source ⟶ target) :
    TraceAnalyticEffectiveRealization.yonedaSourcePreimageTraceHom
        (TraceAnalyticEffectiveRealization.yonedaSourceFunctor.map morphism) =
      morphism.traceHom :=
  congrArg
    (fun recovered =>
      recovered.traceHom)
    (TraceAnalyticEffectiveRealization.yonedaSourcePreimage_map morphism)

/-- The source functor map is recovered by applying lifted Yoneda to the
trace-hom projection of its source preimage. -/
theorem TraceAnalyticEffectiveRealization.yonedaSourceFunctor_map_eq_yoneda_traceHom
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : source ⟶ target) :
    TraceAnalyticEffectiveRealization.yonedaSourceFunctor.map morphism =
      (TraceCorQRepresentablePresheaf.yoneda).map morphism.traceHom :=
  rfl

/-- The source functor map of a source preimage is lifted Yoneda applied to the
recovered trace hom. -/
theorem TraceAnalyticEffectiveRealization.yonedaSourceMap_preimage_eq_yoneda_traceHom
    {source target : TraceAnalyticGeometricGenerator}
    (morphism :
      (TraceAnalyticEffectiveRealization.yonedaSourceFunctor.obj source) ⟶
        (TraceAnalyticEffectiveRealization.yonedaSourceFunctor.obj target)) :
    TraceAnalyticEffectiveRealization.yonedaSourceFunctor.map
        (TraceAnalyticEffectiveRealization.yonedaSourcePreimage morphism) =
      (TraceCorQRepresentablePresheaf.yoneda).map
        (TraceAnalyticEffectiveRealization.yonedaSourcePreimageTraceHom
          morphism) :=
  rfl

/-- Source Yoneda preimage trace hom sends identity to the trace identity. -/
theorem TraceAnalyticEffectiveRealization.yonedaSourcePreimageTraceHom_id
    (generator : TraceAnalyticGeometricGenerator) :
    TraceAnalyticEffectiveRealization.yonedaSourcePreimageTraceHom
        (𝟙 (TraceAnalyticEffectiveRealization.yonedaSourceFunctor.obj generator)) =
      𝟙 generator.traceObject :=
  Eq.trans
    (congrArg
      (fun recovered =>
        recovered.traceHom)
      (TraceAnalyticEffectiveRealization.yonedaSourcePreimage_id generator))
    (TraceAnalyticGeometricGenerator.id_traceHom generator)

/-- Source Yoneda preimage trace hom sends composition to trace composition. -/
theorem TraceAnalyticEffectiveRealization.yonedaSourcePreimageTraceHom_comp
    {first second third : TraceAnalyticGeometricGenerator}
    (left :
      (TraceAnalyticEffectiveRealization.yonedaSourceFunctor.obj first) ⟶
        (TraceAnalyticEffectiveRealization.yonedaSourceFunctor.obj second))
    (right :
      (TraceAnalyticEffectiveRealization.yonedaSourceFunctor.obj second) ⟶
        (TraceAnalyticEffectiveRealization.yonedaSourceFunctor.obj third)) :
    TraceAnalyticEffectiveRealization.yonedaSourcePreimageTraceHom
        (left ≫ right) =
      TraceAnalyticEffectiveRealization.yonedaSourcePreimageTraceHom left ≫
        TraceAnalyticEffectiveRealization.yonedaSourcePreimageTraceHom right :=
  Eq.trans
    (congrArg
      (fun recovered =>
        recovered.traceHom)
      (TraceAnalyticEffectiveRealization.yonedaSourcePreimage_comp
        left
        right))
    (TraceAnalyticGeometricGenerator.comp_traceHom
      (TraceAnalyticEffectiveRealization.yonedaSourcePreimage left)
      (TraceAnalyticEffectiveRealization.yonedaSourcePreimage right))

end AnalyticMotives
end LFunctions
end Boundary
