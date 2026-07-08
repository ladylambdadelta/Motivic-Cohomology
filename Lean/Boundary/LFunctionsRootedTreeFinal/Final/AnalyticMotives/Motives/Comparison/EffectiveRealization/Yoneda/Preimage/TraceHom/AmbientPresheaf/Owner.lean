import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Comparison.EffectiveRealization.Yoneda.Preimage.TraceHom.Owner

/-!
# Ambient-presheaf formulas for source Yoneda preimage trace homs

This file records how the recovered trace correspondence of a source
representable morphism maps back to the ambient trace-presheaf category.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- The ambient presheaf of a Yoneda source object is the compact generator
representable presheaf. -/
theorem TraceAnalyticEffectiveRealization.yonedaSourceFunctor_obj_inclusion
    (generator : TraceAnalyticGeometricGenerator) :
    TraceCorQRepresentablePresheaf.inclusion.obj
        (TraceAnalyticEffectiveRealization.yonedaSourceFunctor.obj generator) =
      generator.presheaf :=
  rfl

/-- The ambient presheaf of a Yoneda source object is the representable presheaf
of the underlying certified trace object. -/
theorem TraceAnalyticEffectiveRealization.yonedaSourceFunctor_obj_inclusion_eq_representable
    (generator : TraceAnalyticGeometricGenerator) :
    TraceCorQRepresentablePresheaf.inclusion.obj
        (TraceAnalyticEffectiveRealization.yonedaSourceFunctor.obj generator) =
      TraceCorQPresheaf.representable generator.traceObject :=
  rfl

/-- The ambient presheaf map represented by a source-side Yoneda preimage
trace hom. -/
noncomputable def TraceAnalyticEffectiveRealization.yonedaSourcePreimageAmbientMap
    {source target : TraceAnalyticGeometricGenerator}
    (morphism :
      (TraceAnalyticEffectiveRealization.yonedaSourceFunctor.obj source) ⟶
        (TraceAnalyticEffectiveRealization.yonedaSourceFunctor.obj target)) :
    TraceCorQPresheafHom source.presheaf target.presheaf :=
  TraceCorQPresheaf.representableMap
    (TraceAnalyticEffectiveRealization.yonedaSourcePreimageTraceHom
      morphism)

/-- The ambient map of a source preimage trace hom is the inclusion of the
source representable morphism. -/
theorem TraceAnalyticEffectiveRealization.yonedaSourcePreimageAmbientMap_eq_inclusion
    {source target : TraceAnalyticGeometricGenerator}
    (morphism :
      (TraceAnalyticEffectiveRealization.yonedaSourceFunctor.obj source) ⟶
        (TraceAnalyticEffectiveRealization.yonedaSourceFunctor.obj target)) :
    TraceAnalyticEffectiveRealization.yonedaSourcePreimageAmbientMap
        morphism =
      TraceCorQRepresentablePresheaf.inclusion.map morphism :=
  Eq.trans
    (Eq.symm
      (TraceCorQRepresentablePresheaf.yoneda_map_inclusion
        (TraceAnalyticEffectiveRealization.yonedaSourcePreimageTraceHom
          morphism)))
    (Eq.trans
      (Eq.symm
        (congrArg
          (fun sourceMap =>
            TraceCorQRepresentablePresheaf.inclusion.map sourceMap)
          (TraceAnalyticEffectiveRealization.yonedaSourceMap_preimage_eq_yoneda_traceHom
            morphism)))
      (congrArg
        (fun sourceMap =>
          TraceCorQRepresentablePresheaf.inclusion.map sourceMap)
        (TraceAnalyticEffectiveRealization.yonedaSourceMap_preimage
          morphism)))

/-- The ambient map attached to the source functor map is the compact-generator
representable map. -/
theorem TraceAnalyticEffectiveRealization.yonedaSourcePreimageAmbientMap_map
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : source ⟶ target) :
    TraceAnalyticEffectiveRealization.yonedaSourcePreimageAmbientMap
        (TraceAnalyticEffectiveRealization.yonedaSourceFunctor.map morphism) =
      morphism.representableMap :=
  Eq.trans
    (TraceAnalyticEffectiveRealization.yonedaSourcePreimageAmbientMap_eq_inclusion
      (TraceAnalyticEffectiveRealization.yonedaSourceFunctor.map morphism))
    (TraceAnalyticGeometricGenerator.Hom.representableObjectMap_inclusion
      morphism)

/-- The ambient source map of a compact-generator morphism is represented by
its trace hom. -/
theorem TraceAnalyticEffectiveRealization.yonedaSourceFunctor_map_inclusion_eq_representableMap
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : source ⟶ target) :
    TraceCorQRepresentablePresheaf.inclusion.map
        (TraceAnalyticEffectiveRealization.yonedaSourceFunctor.map morphism) =
      TraceCorQPresheaf.representableMap morphism.traceHom :=
  Eq.trans
    (congrArg
      (fun sourceMap =>
        TraceCorQRepresentablePresheaf.inclusion.map sourceMap)
      (TraceAnalyticEffectiveRealization.yonedaSourceFunctor_map_eq_yoneda_traceHom
        morphism))
    (TraceCorQRepresentablePresheaf.yoneda_map_inclusion
      morphism.traceHom)

/-- The ambient image of a Yoneda source identity map is the ambient identity. -/
theorem TraceAnalyticEffectiveRealization.yonedaSourceFunctor_map_id_inclusion
    (generator : TraceAnalyticGeometricGenerator) :
    TraceCorQRepresentablePresheaf.inclusion.map
        (TraceAnalyticEffectiveRealization.yonedaSourceFunctor.map
          (𝟙 generator)) =
      𝟙 generator.presheaf :=
  Eq.trans
    (congrArg
      (fun sourceMap =>
        TraceCorQRepresentablePresheaf.inclusion.map sourceMap)
      (TraceAnalyticEffectiveRealization.yonedaSourceFunctor_map_id
        generator))
    (TraceCorQRepresentablePresheaf.inclusion.map_id
      (TraceAnalyticEffectiveRealization.yonedaSourceFunctor.obj generator))

/-- The ambient image of a Yoneda source composite map is the composite of the
ambient images. -/
theorem TraceAnalyticEffectiveRealization.yonedaSourceFunctor_map_comp_inclusion
    {first second third : TraceAnalyticGeometricGenerator}
    (left : first ⟶ second)
    (right : second ⟶ third) :
    TraceCorQRepresentablePresheaf.inclusion.map
        (TraceAnalyticEffectiveRealization.yonedaSourceFunctor.map
          (left ≫ right)) =
      TraceCorQRepresentablePresheaf.inclusion.map
          (TraceAnalyticEffectiveRealization.yonedaSourceFunctor.map left) ≫
        TraceCorQRepresentablePresheaf.inclusion.map
          (TraceAnalyticEffectiveRealization.yonedaSourceFunctor.map right) :=
  Eq.trans
    (congrArg
      (fun sourceMap =>
        TraceCorQRepresentablePresheaf.inclusion.map sourceMap)
      (TraceAnalyticEffectiveRealization.yonedaSourceFunctor_map_comp
        left
        right))
    (TraceCorQRepresentablePresheaf.inclusion.map_comp
      (TraceAnalyticEffectiveRealization.yonedaSourceFunctor.map left)
      (TraceAnalyticEffectiveRealization.yonedaSourceFunctor.map right))

/-- The ambient map of a source preimage is represented by the recovered trace
hom. -/
theorem TraceAnalyticEffectiveRealization.yonedaSourceMap_preimage_inclusion_eq_representableMap
    {source target : TraceAnalyticGeometricGenerator}
    (morphism :
      (TraceAnalyticEffectiveRealization.yonedaSourceFunctor.obj source) ⟶
        (TraceAnalyticEffectiveRealization.yonedaSourceFunctor.obj target)) :
    TraceCorQRepresentablePresheaf.inclusion.map
        (TraceAnalyticEffectiveRealization.yonedaSourceFunctor.map
          (TraceAnalyticEffectiveRealization.yonedaSourcePreimage morphism)) =
      TraceCorQPresheaf.representableMap
        (TraceAnalyticEffectiveRealization.yonedaSourcePreimageTraceHom
          morphism) :=
  Eq.trans
    (congrArg
      (fun sourceMap =>
        TraceCorQRepresentablePresheaf.inclusion.map sourceMap)
      (TraceAnalyticEffectiveRealization.yonedaSourceMap_preimage_eq_yoneda_traceHom
        morphism))
    (TraceCorQRepresentablePresheaf.yoneda_map_inclusion
      (TraceAnalyticEffectiveRealization.yonedaSourcePreimageTraceHom
        morphism))

/-- The ambient source preimage map sends identity to the ambient identity. -/
theorem TraceAnalyticEffectiveRealization.yonedaSourcePreimageAmbientMap_id
    (generator : TraceAnalyticGeometricGenerator) :
    TraceAnalyticEffectiveRealization.yonedaSourcePreimageAmbientMap
        (𝟙 (TraceAnalyticEffectiveRealization.yonedaSourceFunctor.obj generator)) =
      𝟙 generator.presheaf :=
  Eq.trans
    (congrArg
      (fun traceHom =>
        TraceCorQPresheaf.representableMap traceHom)
      (TraceAnalyticEffectiveRealization.yonedaSourcePreimageTraceHom_id
        generator))
    (TraceCorQPresheaf.representableMap_id generator.traceObject)

/-- The ambient source preimage map sends composition to ambient
composition. -/
theorem TraceAnalyticEffectiveRealization.yonedaSourcePreimageAmbientMap_comp
    {first second third : TraceAnalyticGeometricGenerator}
    (left :
      (TraceAnalyticEffectiveRealization.yonedaSourceFunctor.obj first) ⟶
        (TraceAnalyticEffectiveRealization.yonedaSourceFunctor.obj second))
    (right :
      (TraceAnalyticEffectiveRealization.yonedaSourceFunctor.obj second) ⟶
        (TraceAnalyticEffectiveRealization.yonedaSourceFunctor.obj third)) :
    TraceAnalyticEffectiveRealization.yonedaSourcePreimageAmbientMap
        (left ≫ right) =
      TraceAnalyticEffectiveRealization.yonedaSourcePreimageAmbientMap left ≫
        TraceAnalyticEffectiveRealization.yonedaSourcePreimageAmbientMap right :=
  Eq.trans
    (TraceAnalyticEffectiveRealization.yonedaSourcePreimageAmbientMap_eq_inclusion
      (left ≫ right))
    (Eq.trans
      (TraceCorQRepresentablePresheaf.inclusion.map_comp left right)
      (congrArg₂
        (fun firstMap secondMap =>
          firstMap ≫ secondMap)
        (Eq.symm
          (TraceAnalyticEffectiveRealization.yonedaSourcePreimageAmbientMap_eq_inclusion
            left))
        (Eq.symm
          (TraceAnalyticEffectiveRealization.yonedaSourcePreimageAmbientMap_eq_inclusion
            right))))

end AnalyticMotives
end LFunctions
end Boundary
