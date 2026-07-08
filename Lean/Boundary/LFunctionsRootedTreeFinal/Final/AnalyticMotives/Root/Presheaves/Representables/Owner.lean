import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Presheaves.Representables.Subcategory.Owner

/-!
# Top-root representable trace presheaves

This file exposes the concrete Q-linear representable trace presheaf and lifted
representable-subcategory facts under the top-level `AnalyticMotivesRoot`
namespace.
-/

open scoped CategoryTheory

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- The top root exposes that every concrete trace representable is representable. -/
theorem AnalyticMotivesRoot.traceCorQRepresentable_isRepresentable
    (object : TraceCorQObject) :
    TraceCorQPresheaf.IsRepresentable
      (TraceCorQPresheaf.representable object) :=
  TraceCorQPresheaf.representable_isRepresentable
    object

/-- The top root exposes representables as Yoneda objects. -/
theorem AnalyticMotivesRoot.traceCorQRepresentable_eq_yoneda_obj
    (object : TraceCorQObject) :
    TraceCorQPresheaf.representable object =
      (TraceCorQPresheaf.yoneda).obj object :=
  TraceCorQPresheaf.representable_eq_yoneda_obj
    object

/-- The top root exposes sections of representable trace presheaves. -/
theorem AnalyticMotivesRoot.traceCorQRepresentable_sections
    (source target : TraceCorQObject) :
    (TraceCorQPresheaf.representable target).sections source =
      ModuleCat.of Rat (source ⟶ target) :=
  TraceCorQPresheaf.representable_sections
    source
    target

/-- The top root exposes pullback on representable trace presheaves. -/
theorem AnalyticMotivesRoot.traceCorQRepresentable_pullback
    {source middle : TraceCorQObject}
    (target : TraceCorQObject)
    (morphism : source ⟶ middle) :
    (TraceCorQPresheaf.representable target).pullback morphism =
      ModuleCat.asHom
        (CategoryTheory.Linear.leftComp Rat target morphism) :=
  TraceCorQPresheaf.representable_pullback
    target
    morphism

/-- The top root exposes representable maps as Yoneda maps. -/
theorem AnalyticMotivesRoot.traceCorQRepresentableMap_eq_yoneda_map
    {source target : TraceCorQObject}
    (morphism : source ⟶ target) :
    TraceCorQPresheaf.representableMap morphism =
      (TraceCorQPresheaf.yoneda).map morphism :=
  TraceCorQPresheaf.representableMap_eq_yoneda_map
    morphism

/-- The top root exposes equality reflection for representable maps. -/
theorem AnalyticMotivesRoot.traceCorQ_eq_of_representableMap_eq
    {source target : TraceCorQObject}
    {left right : source ⟶ target}
    (map_eq :
      TraceCorQPresheaf.representableMap left =
        TraceCorQPresheaf.representableMap right) :
    left = right :=
  TraceCorQPresheaf.eq_of_representableMap_eq
    map_eq

/-- The top root exposes representable preimage after representable maps. -/
theorem AnalyticMotivesRoot.traceCorQRepresentablePreimage_representableMap
    {source target : TraceCorQObject}
    (morphism : source ⟶ target) :
    TraceCorQPresheaf.representablePreimage
      (TraceCorQPresheaf.representableMap morphism) =
      morphism :=
  TraceCorQPresheaf.representablePreimage_representableMap
    morphism

/-- The top root exposes representable maps after representable preimages. -/
theorem AnalyticMotivesRoot.traceCorQRepresentableMap_representablePreimage
    {source target : TraceCorQObject}
    (morphism :
      TraceCorQPresheafHom
        (TraceCorQPresheaf.representable source)
        (TraceCorQPresheaf.representable target)) :
    TraceCorQPresheaf.representableMap
      (TraceCorQPresheaf.representablePreimage morphism) =
      morphism :=
  TraceCorQPresheaf.representableMap_representablePreimage
    morphism

/-- The top root exposes the forward map of the representable hom equivalence. -/
theorem AnalyticMotivesRoot.traceCorQRepresentableHomEquiv_apply
    {source target : TraceCorQObject}
    (morphism : source ⟶ target) :
    TraceCorQPresheaf.representableHomEquiv source target morphism =
      TraceCorQPresheaf.representableMap morphism :=
  TraceCorQPresheaf.representableHomEquiv_apply
    morphism

/-- The top root exposes the inverse map of the representable hom equivalence. -/
theorem AnalyticMotivesRoot.traceCorQRepresentableHomEquiv_symm_apply
    {source target : TraceCorQObject}
    (morphism :
      TraceCorQPresheafHom
        (TraceCorQPresheaf.representable source)
        (TraceCorQPresheaf.representable target)) :
    (TraceCorQPresheaf.representableHomEquiv source target).symm morphism =
      TraceCorQPresheaf.representablePreimage morphism :=
  TraceCorQPresheaf.representableHomEquiv_symm_apply
    morphism

/-- The top root exposes preimage of identity representable maps. -/
theorem AnalyticMotivesRoot.traceCorQRepresentablePreimage_id
    (object : TraceCorQObject) :
    TraceCorQPresheaf.representablePreimage
      (𝟙 (TraceCorQPresheaf.representable object)) =
      𝟙 object :=
  TraceCorQPresheaf.representablePreimage_id
    object

/-- The top root exposes preimage compatibility with representable-map composition. -/
theorem AnalyticMotivesRoot.traceCorQRepresentablePreimage_comp
    {first second third : TraceCorQObject}
    (left :
      TraceCorQPresheafHom
        (TraceCorQPresheaf.representable first)
        (TraceCorQPresheaf.representable second))
    (right :
      TraceCorQPresheafHom
        (TraceCorQPresheaf.representable second)
        (TraceCorQPresheaf.representable third)) :
    TraceCorQPresheaf.representablePreimage (left ≫ right) =
      TraceCorQPresheaf.representablePreimage left ≫
        TraceCorQPresheaf.representablePreimage right :=
  TraceCorQPresheaf.representablePreimage_comp
    left
    right

/-- The top root exposes the component of a representable map. -/
theorem AnalyticMotivesRoot.traceCorQRepresentableMap_component
    {source target : TraceCorQObject}
    (morphism : source ⟶ target)
    (object : TraceCorQObject) :
    (TraceCorQPresheaf.representableMap morphism).component object =
      ((TraceCorQPresheaf.yoneda).map morphism).app (Opposite.op object) :=
  TraceCorQPresheaf.representableMap_component
    morphism
    object

/-- The top root exposes representable maps on identity trace correspondences. -/
theorem AnalyticMotivesRoot.traceCorQRepresentableMap_id
    (object : TraceCorQObject) :
    TraceCorQPresheaf.representableMap (𝟙 object) =
      𝟙 (TraceCorQPresheaf.representable object) :=
  TraceCorQPresheaf.representableMap_id
    object

/-- The top root exposes representable maps on composed trace correspondences. -/
theorem AnalyticMotivesRoot.traceCorQRepresentableMap_comp
    {first second third : TraceCorQObject}
    (left : first ⟶ second)
    (right : second ⟶ third) :
    TraceCorQPresheaf.representableMap (left ≫ right) =
      TraceCorQPresheaf.representableMap left ≫
        TraceCorQPresheaf.representableMap right :=
  TraceCorQPresheaf.representableMap_comp
    left
    right

/-- The top root exposes the lifted Yoneda object as the expected representable presheaf. -/
theorem AnalyticMotivesRoot.traceCorQYoneda_obj_presheaf
    (object : TraceCorQObject) :
    ((TraceCorQRepresentablePresheaf.yoneda).obj object).presheaf =
      TraceCorQPresheaf.representable object :=
  TraceCorQRepresentablePresheaf.yoneda_obj_presheaf
    object

/-- The top root exposes the ambient presheaf carried by a representable object. -/
def AnalyticMotivesRoot.traceCorQRepresentablePresheaf_presheaf
    (object : TraceCorQRepresentablePresheaf) :
    TraceCorQPresheaf :=
  TraceCorQRepresentablePresheaf.presheaf
    object

/-- The top root exposes the representability certificate carried by a representable object. -/
def AnalyticMotivesRoot.traceCorQRepresentablePresheaf_isRepresentable
    (object : TraceCorQRepresentablePresheaf) :
    TraceCorQPresheaf.IsRepresentable object.presheaf :=
  TraceCorQRepresentablePresheaf.isRepresentable
    object

/-- The top root exposes inclusion after lifted Yoneda. -/
theorem AnalyticMotivesRoot.traceCorQYoneda_comp_inclusion :
    TraceCorQRepresentablePresheaf.yoneda ⋙
        TraceCorQRepresentablePresheaf.inclusion =
      TraceCorQPresheaf.yoneda :=
  TraceCorQRepresentablePresheaf.yoneda_comp_inclusion

/-- The top root exposes morphisms in the representable full subcategory as presheaf morphisms. -/
theorem AnalyticMotivesRoot.traceCorQRepresentablePresheaf_hom_eq_presheaf_hom
    (source target : TraceCorQRepresentablePresheaf) :
    (source ⟶ target) =
      TraceCorQPresheafHom source.presheaf target.presheaf :=
  TraceCorQRepresentablePresheaf.hom_eq_presheaf_hom
    source
    target

/-- The top root exposes lifted Yoneda maps after inclusion. -/
theorem AnalyticMotivesRoot.traceCorQYoneda_map_inclusion
    {source target : TraceCorQObject}
    (morphism : source ⟶ target) :
    TraceCorQRepresentablePresheaf.inclusion.map
        ((TraceCorQRepresentablePresheaf.yoneda).map morphism) =
      TraceCorQPresheaf.representableMap morphism :=
  TraceCorQRepresentablePresheaf.yoneda_map_inclusion
    morphism

/-- The top root exposes lifted-Yoneda preimage after lifted-Yoneda maps. -/
theorem AnalyticMotivesRoot.traceCorQYonedaPreimage_yonedaMap
    {source target : TraceCorQObject}
    (morphism : source ⟶ target) :
    TraceCorQRepresentablePresheaf.yonedaPreimage
      ((TraceCorQRepresentablePresheaf.yoneda).map morphism) =
      morphism :=
  TraceCorQRepresentablePresheaf.yonedaPreimage_yonedaMap
    morphism

/-- The top root exposes lifted-Yoneda maps after lifted-Yoneda preimages. -/
theorem AnalyticMotivesRoot.traceCorQYonedaMap_yonedaPreimage
    {source target : TraceCorQObject}
    (morphism :
      (TraceCorQRepresentablePresheaf.yoneda).obj source ⟶
        (TraceCorQRepresentablePresheaf.yoneda).obj target) :
    (TraceCorQRepresentablePresheaf.yoneda).map
        (TraceCorQRepresentablePresheaf.yonedaPreimage morphism) =
      morphism :=
  TraceCorQRepresentablePresheaf.yonedaMap_yonedaPreimage
    morphism

/-- The top root exposes the forward map of the lifted-Yoneda hom equivalence. -/
theorem AnalyticMotivesRoot.traceCorQYonedaHomEquiv_apply
    {source target : TraceCorQObject}
    (morphism : source ⟶ target) :
    TraceCorQRepresentablePresheaf.yonedaHomEquiv source target morphism =
      (TraceCorQRepresentablePresheaf.yoneda).map morphism :=
  TraceCorQRepresentablePresheaf.yonedaHomEquiv_apply
    morphism

/-- The top root exposes the inverse map of the lifted-Yoneda hom equivalence. -/
theorem AnalyticMotivesRoot.traceCorQYonedaHomEquiv_symm_apply
    {source target : TraceCorQObject}
    (morphism :
      (TraceCorQRepresentablePresheaf.yoneda).obj source ⟶
        (TraceCorQRepresentablePresheaf.yoneda).obj target) :
    (TraceCorQRepresentablePresheaf.yonedaHomEquiv source target).symm morphism =
      TraceCorQRepresentablePresheaf.yonedaPreimage morphism :=
  TraceCorQRepresentablePresheaf.yonedaHomEquiv_symm_apply
    morphism

/-- The top root exposes lifted-Yoneda preimage on identities. -/
theorem AnalyticMotivesRoot.traceCorQYonedaPreimage_id
    (object : TraceCorQObject) :
    TraceCorQRepresentablePresheaf.yonedaPreimage
      (𝟙 ((TraceCorQRepresentablePresheaf.yoneda).obj object)) =
      𝟙 object :=
  TraceCorQRepresentablePresheaf.yonedaPreimage_id
    object

/-- The top root exposes lifted-Yoneda preimage on composition. -/
theorem AnalyticMotivesRoot.traceCorQYonedaPreimage_comp
    {first second third : TraceCorQObject}
    (left :
      (TraceCorQRepresentablePresheaf.yoneda).obj first ⟶
        (TraceCorQRepresentablePresheaf.yoneda).obj second)
    (right :
      (TraceCorQRepresentablePresheaf.yoneda).obj second ⟶
        (TraceCorQRepresentablePresheaf.yoneda).obj third) :
    TraceCorQRepresentablePresheaf.yonedaPreimage (left ≫ right) =
      TraceCorQRepresentablePresheaf.yonedaPreimage left ≫
        TraceCorQRepresentablePresheaf.yonedaPreimage right :=
  TraceCorQRepresentablePresheaf.yonedaPreimage_comp
    left
    right

end AnalyticMotives
end LFunctions
end Boundary
