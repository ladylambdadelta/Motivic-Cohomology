import Mathlib.CategoryTheory.FullSubcategory
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Presheaves.Representables.Owner

/-!
# The full subcategory of representable trace presheaves

This file owns the full subcategory of Q-module-valued trace presheaves that
are isomorphic to a concrete trace representable.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- A trace presheaf is representable when it is isomorphic to a concrete trace representable. -/
def TraceCorQPresheaf.IsRepresentable
    (presheaf : TraceCorQPresheaf) :
    Prop :=
  ∃ object : TraceCorQObject,
    Nonempty (presheaf ≅ TraceCorQPresheaf.representable object)

/-- Every concrete trace representable is representable. -/
theorem TraceCorQPresheaf.representable_isRepresentable
    (object : TraceCorQObject) :
    TraceCorQPresheaf.IsRepresentable
      (TraceCorQPresheaf.representable object) :=
  Exists.intro object
    (Nonempty.intro
      (CategoryTheory.Iso.refl
        (TraceCorQPresheaf.representable object)))

/-- The full subcategory of Q-module-valued trace presheaves that are trace representable. -/
abbrev TraceCorQRepresentablePresheaf :=
  CategoryTheory.FullSubcategory TraceCorQPresheaf.IsRepresentable

/-- The ambient presheaf carried by a representable trace presheaf object. -/
def TraceCorQRepresentablePresheaf.presheaf
    (object : TraceCorQRepresentablePresheaf) :
    TraceCorQPresheaf :=
  object.obj

/-- The representability certificate carried by a representable trace presheaf object. -/
def TraceCorQRepresentablePresheaf.isRepresentable
    (object : TraceCorQRepresentablePresheaf) :
    TraceCorQPresheaf.IsRepresentable object.presheaf :=
  object.property

/-- The inclusion of representable trace presheaves into all trace presheaves. -/
abbrev TraceCorQRepresentablePresheaf.inclusion :
    TraceCorQRepresentablePresheaf ⥤ TraceCorQPresheaf :=
  CategoryTheory.fullSubcategoryInclusion TraceCorQPresheaf.IsRepresentable

/-- The Q-linear Yoneda functor lifted into the representable full subcategory. -/
abbrev TraceCorQRepresentablePresheaf.yoneda :
    TraceCorQObject ⥤ TraceCorQRepresentablePresheaf :=
  CategoryTheory.FullSubcategory.lift
    TraceCorQPresheaf.IsRepresentable
    TraceCorQPresheaf.yoneda
    TraceCorQPresheaf.representable_isRepresentable

/-- The lifted Yoneda functor lands on the expected ambient representable presheaf. -/
theorem TraceCorQRepresentablePresheaf.yoneda_obj_presheaf
    (object : TraceCorQObject) :
    ((TraceCorQRepresentablePresheaf.yoneda).obj object).presheaf =
      TraceCorQPresheaf.representable object :=
  rfl

/-- Inclusion after lifted Yoneda is the original Q-linear Yoneda functor. -/
theorem TraceCorQRepresentablePresheaf.yoneda_comp_inclusion :
    TraceCorQRepresentablePresheaf.yoneda ⋙
        TraceCorQRepresentablePresheaf.inclusion =
      TraceCorQPresheaf.yoneda :=
  rfl

/-- Morphisms in the representable full subcategory are ambient presheaf morphisms. -/
theorem TraceCorQRepresentablePresheaf.hom_eq_presheaf_hom
    (source target : TraceCorQRepresentablePresheaf) :
    (source ⟶ target) =
      TraceCorQPresheafHom source.presheaf target.presheaf :=
  rfl

/-- The lifted Yoneda map is the original representable map after forgetting the subcategory. -/
theorem TraceCorQRepresentablePresheaf.yoneda_map_inclusion
    {source target : TraceCorQObject}
    (morphism : source ⟶ target) :
    TraceCorQRepresentablePresheaf.inclusion.map
        ((TraceCorQRepresentablePresheaf.yoneda).map morphism) =
      TraceCorQPresheaf.representableMap morphism :=
  rfl

/-- The trace correspondence represented by a lifted-Yoneda subcategory morphism. -/
noncomputable def TraceCorQRepresentablePresheaf.yonedaPreimage
    {source target : TraceCorQObject}
    (morphism :
      (TraceCorQRepresentablePresheaf.yoneda).obj source ⟶
        (TraceCorQRepresentablePresheaf.yoneda).obj target) :
    source ⟶ target :=
  TraceCorQPresheaf.representablePreimage
    (TraceCorQRepresentablePresheaf.inclusion.map morphism)

/-- The lifted-Yoneda preimage of a lifted-Yoneda map is the original trace correspondence. -/
theorem TraceCorQRepresentablePresheaf.yonedaPreimage_yonedaMap
    {source target : TraceCorQObject}
    (morphism : source ⟶ target) :
    TraceCorQRepresentablePresheaf.yonedaPreimage
      ((TraceCorQRepresentablePresheaf.yoneda).map morphism) =
      morphism :=
  TraceCorQPresheaf.representablePreimage_representableMap morphism

/-- Every lifted-Yoneda subcategory morphism is represented by its trace preimage. -/
theorem TraceCorQRepresentablePresheaf.yonedaMap_yonedaPreimage
    {source target : TraceCorQObject}
    (morphism :
      (TraceCorQRepresentablePresheaf.yoneda).obj source ⟶
        (TraceCorQRepresentablePresheaf.yoneda).obj target) :
    (TraceCorQRepresentablePresheaf.yoneda).map
        (TraceCorQRepresentablePresheaf.yonedaPreimage morphism) =
      morphism :=
  TraceCorQPresheaf.representableMap_representablePreimage morphism

/-- Trace correspondences are equivalent to lifted-Yoneda subcategory morphisms. -/
noncomputable def TraceCorQRepresentablePresheaf.yonedaHomEquiv
    (source target : TraceCorQObject) :
    (source ⟶ target) ≃
      ((TraceCorQRepresentablePresheaf.yoneda).obj source ⟶
        (TraceCorQRepresentablePresheaf.yoneda).obj target) where
  toFun := fun morphism =>
    (TraceCorQRepresentablePresheaf.yoneda).map morphism
  invFun := fun morphism =>
    TraceCorQRepresentablePresheaf.yonedaPreimage morphism
  left_inv := fun morphism =>
    TraceCorQRepresentablePresheaf.yonedaPreimage_yonedaMap morphism
  right_inv := fun morphism =>
    TraceCorQRepresentablePresheaf.yonedaMap_yonedaPreimage morphism

/-- The forward map of the lifted-Yoneda hom equivalence is lifted-Yoneda on morphisms. -/
theorem TraceCorQRepresentablePresheaf.yonedaHomEquiv_apply
    {source target : TraceCorQObject}
    (morphism : source ⟶ target) :
    TraceCorQRepresentablePresheaf.yonedaHomEquiv source target morphism =
      (TraceCorQRepresentablePresheaf.yoneda).map morphism :=
  rfl

/-- The inverse map of the lifted-Yoneda hom equivalence is the lifted-Yoneda preimage. -/
theorem TraceCorQRepresentablePresheaf.yonedaHomEquiv_symm_apply
    {source target : TraceCorQObject}
    (morphism :
      (TraceCorQRepresentablePresheaf.yoneda).obj source ⟶
        (TraceCorQRepresentablePresheaf.yoneda).obj target) :
    (TraceCorQRepresentablePresheaf.yonedaHomEquiv source target).symm morphism =
      TraceCorQRepresentablePresheaf.yonedaPreimage morphism :=
  rfl

/-- The lifted Yoneda functor is full. -/
instance TraceCorQRepresentablePresheaf.yonedaFull :
    (TraceCorQRepresentablePresheaf.yoneda).Full :=
  inferInstance

/-- The lifted Yoneda functor is faithful. -/
instance TraceCorQRepresentablePresheaf.yonedaFaithful :
    (TraceCorQRepresentablePresheaf.yoneda).Faithful :=
  inferInstance

end AnalyticMotives
end LFunctions
end Boundary
