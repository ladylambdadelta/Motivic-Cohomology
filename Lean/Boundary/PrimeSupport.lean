import Boundary.Basic
import Boundary.SmOver
import Boundary.ComponentGeometry
import Geometry.Cycles.Basic
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.AlgebraicGeometry.Limits
import Mathlib.AlgebraicGeometry.Properties
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion

universe u

variable {k : Type u} [Field k] [PerfectField k]

open AlgebraicGeometry CategoryTheory Limits

namespace Boundary

noncomputable section

/-- A plain scheme over `Spec k`, without any smoothness assumption. -/
structure SchemeOverBase (k : Type u) [Field k] where
  scheme : Scheme.{u}
  structMap : scheme ⟶ Spec (CommRingCat.of k)

/-- An integral closed source image inside a smooth ambient source scheme. -/
structure SourceImageSubscheme (X : Geometry.SmSchemeOver k) where
  carrier : SchemeOverBase k
  toAmbient : carrier.scheme ⟶ X.scheme
  toAmbient_overBase : toAmbient ≫ X.structMap = carrier.structMap
  isClosedImmersion : IsClosedImmersion toAmbient
  isIntegral : IsIntegral carrier.scheme

attribute [instance] SourceImageSubscheme.isIntegral

namespace SourceImageSubscheme

@[ext] theorem ext
    {X : Geometry.SmSchemeOver k}
    (C D : SourceImageSubscheme (k := k) X)
    (hBase : C.carrier = D.carrier)
    (hToAmbient : HEq C.toAmbient D.toAmbient) :
    C = D := by
  cases C
  cases D
  cases hBase
  cases hToAmbient
  rfl

theorem extensionality
    {X : Geometry.SmSchemeOver k}
    (C D : SourceImageSubscheme (k := k) X)
    (hBase : C.carrier = D.carrier)
    (hToAmbient : HEq C.toAmbient D.toAmbient) :
    C = D :=
  ext C D hBase hToAmbient

def toIntClosedSubscheme {X : Geometry.SmSchemeOver k}
    (sourceImage : SourceImageSubscheme (k := k) X) :
    IntClosedSubscheme X.scheme where
  scheme := sourceImage.carrier.scheme
  inclusion := sourceImage.toAmbient
  isClosedImm := sourceImage.isClosedImmersion
  isIntegral := sourceImage.isIntegral

def ofSourceIrreducibleComponent {X : Geometry.SmSchemeOver k}
    (component : SourceIrreducibleComponent X) : SourceImageSubscheme (k := k) X where
  carrier :=
    { scheme := component.carrier.scheme
      structMap := component.carrier.structMap }
  toAmbient := component.toAmbient
  toAmbient_overBase := component.toAmbient_overBase
  isClosedImmersion := component.isClosedImmersion
  isIntegral := component.isIntegral

theorem range_nonempty {X : Geometry.SmSchemeOver k}
    (sourceImage : SourceImageSubscheme (k := k) X) :
    (Set.range sourceImage.toAmbient.base).Nonempty := by
  refine ⟨sourceImage.toAmbient.base (genericPoint sourceImage.carrier.scheme), ?_⟩
  exact ⟨genericPoint sourceImage.carrier.scheme, rfl⟩

structure IsoOverAmbient {X : Geometry.SmSchemeOver k}
    (C D : SourceImageSubscheme (k := k) X) where
  iso : C.carrier.scheme ≅ D.carrier.scheme
  hom_toAmbient : iso.hom ≫ D.toAmbient = C.toAmbient

namespace IsoOverAmbient

def refl {X : Geometry.SmSchemeOver k}
    (C : SourceImageSubscheme (k := k) X) : IsoOverAmbient C C where
  iso := Iso.refl _
  hom_toAmbient := Category.id_comp C.toAmbient

def symm {X : Geometry.SmSchemeOver k}
    {C D : SourceImageSubscheme (k := k) X} (h : IsoOverAmbient C D) :
    IsoOverAmbient D C where
  iso := h.iso.symm
  hom_toAmbient := by
    calc
      h.iso.inv ≫ C.toAmbient =
          h.iso.inv ≫ (h.iso.hom ≫ D.toAmbient) :=
          congrArg (fun f => h.iso.inv ≫ f) h.hom_toAmbient.symm
      _ = (h.iso.inv ≫ h.iso.hom) ≫ D.toAmbient :=
          (Category.assoc h.iso.inv h.iso.hom D.toAmbient).symm
      _ = D.toAmbient :=
          Eq.trans
            (congrArg (fun f => f ≫ D.toAmbient) h.iso.inv_hom_id)
            (Category.id_comp D.toAmbient)

def trans {X : Geometry.SmSchemeOver k}
    {C D E : SourceImageSubscheme (k := k) X}
    (hCD : IsoOverAmbient C D) (hDE : IsoOverAmbient D E) :
    IsoOverAmbient C E where
  iso := hCD.iso ≪≫ hDE.iso
  hom_toAmbient := by
    calc
      (hCD.iso ≪≫ hDE.iso).hom ≫ E.toAmbient =
          hCD.iso.hom ≫ (hDE.iso.hom ≫ E.toAmbient) :=
          rfl
      _ = hCD.iso.hom ≫ D.toAmbient :=
          congrArg (fun f => hCD.iso.hom ≫ f) hDE.hom_toAmbient
      _ = C.toAmbient :=
          hCD.hom_toAmbient

theorem hom_structMap {X : Geometry.SmSchemeOver k}
    {C D : SourceImageSubscheme (k := k) X} (h : IsoOverAmbient C D) :
    h.iso.hom ≫ D.carrier.structMap = C.carrier.structMap := by
  calc
    h.iso.hom ≫ D.carrier.structMap =
        h.iso.hom ≫ (D.toAmbient ≫ X.structMap) :=
        congrArg (fun f => h.iso.hom ≫ f) D.toAmbient_overBase.symm
    _ = (h.iso.hom ≫ D.toAmbient) ≫ X.structMap :=
        (Category.assoc h.iso.hom D.toAmbient X.structMap).symm
    _ = C.toAmbient ≫ X.structMap :=
        congrArg (fun f => f ≫ X.structMap) h.hom_toAmbient
    _ = C.carrier.structMap :=
        C.toAmbient_overBase

end IsoOverAmbient

end SourceImageSubscheme

namespace SourceIrreducibleComponent

abbrev toSourceImageSubscheme {X : Geometry.SmSchemeOver k}
    (component : SourceIrreducibleComponent X) : SourceImageSubscheme (k := k) X :=
  SourceImageSubscheme.ofSourceIrreducibleComponent component

@[simp] theorem toSourceImageSubscheme_carrier {X : Geometry.SmSchemeOver k}
    (component : SourceIrreducibleComponent X) :
    component.toSourceImageSubscheme.carrier =
      { scheme := component.carrier.scheme
        structMap := component.carrier.structMap } := rfl

@[simp] theorem toSourceImageSubscheme_toAmbient {X : Geometry.SmSchemeOver k}
    (component : SourceIrreducibleComponent X) :
    component.toSourceImageSubscheme.toAmbient = component.toAmbient := rfl

@[simp] theorem toSourceImageSubscheme_structMap {X : Geometry.SmSchemeOver k}
    (component : SourceIrreducibleComponent X) :
    component.toSourceImageSubscheme.carrier.structMap = component.carrier.structMap := rfl

end SourceIrreducibleComponent

/-- Fiber product of a plain source image over `Spec k` with a smooth target. -/
abbrev sourceOverBaseProduct (S : SchemeOverBase k) (Y : Geometry.SmSchemeOver k) : Scheme :=
  pullback S.structMap Y.structMap

abbrev sourceOverBaseProduct.fst (S : SchemeOverBase k) (Y : Geometry.SmSchemeOver k) :
    sourceOverBaseProduct (k := k) S Y ⟶ S.scheme :=
  pullback.fst S.structMap Y.structMap

abbrev sourceOverBaseProduct.snd (S : SchemeOverBase k) (Y : Geometry.SmSchemeOver k) :
    sourceOverBaseProduct (k := k) S Y ⟶ Y.scheme :=
  pullback.snd S.structMap Y.structMap

/-- The defining square of `S ×_k Y`: the two projections have the same map
to `Spec k`. -/
theorem sourceOverBaseProduct_condition
    (S : SchemeOverBase k) (Y : Geometry.SmSchemeOver k) :
    sourceOverBaseProduct.fst (k := k) S Y ≫ S.structMap =
      sourceOverBaseProduct.snd (k := k) S Y ≫ Y.structMap :=
  pullback.condition (f := S.structMap) (g := Y.structMap)

namespace SourceImageSubscheme.IsoOverAmbient

noncomputable def overBaseProductIso {X : Geometry.SmSchemeOver k}
    {Y : Geometry.SmSchemeOver k}
    {C D : SourceImageSubscheme (k := k) X}
    (h : SourceImageSubscheme.IsoOverAmbient C D) :
    sourceOverBaseProduct (k := k) C.carrier Y ≅ sourceOverBaseProduct (k := k) D.carrier Y := by
  refine asIso <|
    pullback.map C.carrier.structMap Y.structMap D.carrier.structMap Y.structMap
      h.iso.hom (𝟙 Y.scheme) (𝟙 (Spec (CommRingCat.of k))) ?_ ?_
  · exact h.hom_structMap.symm
  · exact Eq.trans (Category.id_comp Y.structMap) (Category.comp_id Y.structMap).symm

theorem overBaseProductIso_hom_fst_raw {X : Geometry.SmSchemeOver k}
    {Y : Geometry.SmSchemeOver k}
    {C D : SourceImageSubscheme (k := k) X}
    (h : SourceImageSubscheme.IsoOverAmbient C D) :
    (h.overBaseProductIso (Y := Y)).hom ≫ sourceOverBaseProduct.fst (k := k) D.carrier Y =
      sourceOverBaseProduct.fst (k := k) C.carrier Y ≫ h.iso.hom := by
  change
    pullback.map C.carrier.structMap Y.structMap D.carrier.structMap Y.structMap
        h.iso.hom (𝟙 Y.scheme) (𝟙 (Spec (CommRingCat.of k))) _ _ ≫
      sourceOverBaseProduct.fst (k := k) D.carrier Y =
    sourceOverBaseProduct.fst (k := k) C.carrier Y ≫ h.iso.hom
  exact pullback.map_fst

@[simp] theorem overBaseProductIso_hom_fst {X : Geometry.SmSchemeOver k}
    {Y : Geometry.SmSchemeOver k}
    {C D : SourceImageSubscheme (k := k) X}
    (h : SourceImageSubscheme.IsoOverAmbient C D) :
    (h.overBaseProductIso (Y := Y)).hom ≫ sourceOverBaseProduct.fst (k := k) D.carrier Y =
      sourceOverBaseProduct.fst (k := k) C.carrier Y ≫ h.iso.hom :=
  h.overBaseProductIso_hom_fst_raw (Y := Y)

theorem overBaseProductIso_hom_snd_raw {X : Geometry.SmSchemeOver k}
    {Y : Geometry.SmSchemeOver k}
    {C D : SourceImageSubscheme (k := k) X}
    (h : SourceImageSubscheme.IsoOverAmbient C D) :
    (h.overBaseProductIso (Y := Y)).hom ≫ sourceOverBaseProduct.snd (k := k) D.carrier Y =
      sourceOverBaseProduct.snd (k := k) C.carrier Y := by
  change
    pullback.map C.carrier.structMap Y.structMap D.carrier.structMap Y.structMap
        h.iso.hom (𝟙 Y.scheme) (𝟙 (Spec (CommRingCat.of k))) _ _ ≫
      sourceOverBaseProduct.snd (k := k) D.carrier Y =
    sourceOverBaseProduct.snd (k := k) C.carrier Y
  exact pullback.map_snd

@[simp] theorem overBaseProductIso_hom_snd {X : Geometry.SmSchemeOver k}
    {Y : Geometry.SmSchemeOver k}
    {C D : SourceImageSubscheme (k := k) X}
    (h : SourceImageSubscheme.IsoOverAmbient C D) :
    (h.overBaseProductIso (Y := Y)).hom ≫ sourceOverBaseProduct.snd (k := k) D.carrier Y =
      sourceOverBaseProduct.snd (k := k) C.carrier Y :=
  h.overBaseProductIso_hom_snd_raw (Y := Y)

structure CompatibleOverBaseProductIso {X : Geometry.SmSchemeOver k}
    {Y : Geometry.SmSchemeOver k}
    (C D : SourceImageSubscheme (k := k) X) where
  sourceIso : SourceImageSubscheme.IsoOverAmbient C D
  iso : sourceOverBaseProduct (k := k) C.carrier Y ≅ sourceOverBaseProduct (k := k) D.carrier Y
  hom_fst :
    iso.hom ≫ sourceOverBaseProduct.fst (k := k) D.carrier Y =
      sourceOverBaseProduct.fst (k := k) C.carrier Y ≫ sourceIso.iso.hom
  hom_snd :
    iso.hom ≫ sourceOverBaseProduct.snd (k := k) D.carrier Y =
      sourceOverBaseProduct.snd (k := k) C.carrier Y

namespace CompatibleOverBaseProductIso

theorem symm_hom_fst {X : Geometry.SmSchemeOver k} {Y : Geometry.SmSchemeOver k}
    {C D : SourceImageSubscheme (k := k) X}
    (h : CompatibleOverBaseProductIso (Y := Y) C D) :
    h.iso.inv ≫ sourceOverBaseProduct.fst (k := k) C.carrier Y =
      sourceOverBaseProduct.fst (k := k) D.carrier Y ≫ h.sourceIso.iso.inv := by
  have hcomp :
      h.iso.hom ≫
          (sourceOverBaseProduct.fst (k := k) D.carrier Y ≫ h.sourceIso.iso.inv) =
        sourceOverBaseProduct.fst (k := k) C.carrier Y := by
    calc
      h.iso.hom ≫ (sourceOverBaseProduct.fst (k := k) D.carrier Y ≫ h.sourceIso.iso.inv) =
          (h.iso.hom ≫ sourceOverBaseProduct.fst (k := k) D.carrier Y) ≫
            h.sourceIso.iso.inv := by
              exact (Category.assoc _ _ _).symm
      _ = (sourceOverBaseProduct.fst (k := k) C.carrier Y ≫ h.sourceIso.iso.hom) ≫
            h.sourceIso.iso.inv := by
              exact congrArg (fun f => f ≫ h.sourceIso.iso.inv) h.hom_fst
      _ = sourceOverBaseProduct.fst (k := k) C.carrier Y := by
              calc
                (sourceOverBaseProduct.fst (k := k) C.carrier Y ≫ h.sourceIso.iso.hom) ≫
                    h.sourceIso.iso.inv =
                    sourceOverBaseProduct.fst (k := k) C.carrier Y ≫
                      (h.sourceIso.iso.hom ≫ h.sourceIso.iso.inv) := by
                        exact Category.assoc _ _ _
                _ = sourceOverBaseProduct.fst (k := k) C.carrier Y ≫ 𝟙 _ := by
                      exact congrArg (fun f => sourceOverBaseProduct.fst (k := k) C.carrier Y ≫ f)
                        h.sourceIso.iso.hom_inv_id
                _ = sourceOverBaseProduct.fst (k := k) C.carrier Y := by
                      exact Category.comp_id _
  have hleft :
      sourceOverBaseProduct.fst (k := k) D.carrier Y ≫ h.sourceIso.iso.inv =
        h.iso.inv ≫ sourceOverBaseProduct.fst (k := k) C.carrier Y := by
    have htmp := congrArg (fun f => h.iso.inv ≫ f) hcomp
    calc
      sourceOverBaseProduct.fst (k := k) D.carrier Y ≫ h.sourceIso.iso.inv =
          (h.iso.inv ≫ h.iso.hom) ≫
            (sourceOverBaseProduct.fst (k := k) D.carrier Y ≫ h.sourceIso.iso.inv) := by
              exact Eq.symm (Category.assoc _ _ _)
      _ = h.iso.inv ≫
            (h.iso.hom ≫ (sourceOverBaseProduct.fst (k := k) D.carrier Y ≫
              h.sourceIso.iso.inv)) := by
              exact Category.assoc _ _ _
      _ = h.iso.inv ≫ sourceOverBaseProduct.fst (k := k) C.carrier Y := by
              exact congrArg (fun f => h.iso.inv ≫ f) hcomp
  exact hleft.symm

theorem symm_hom_snd {X : Geometry.SmSchemeOver k} {Y : Geometry.SmSchemeOver k}
    {C D : SourceImageSubscheme (k := k) X}
    (h : CompatibleOverBaseProductIso (Y := Y) C D) :
    h.iso.inv ≫ sourceOverBaseProduct.snd (k := k) C.carrier Y =
      sourceOverBaseProduct.snd (k := k) D.carrier Y := by
  calc
    h.iso.inv ≫ sourceOverBaseProduct.snd (k := k) C.carrier Y =
        h.iso.inv ≫ (sourceOverBaseProduct.snd (k := k) D.carrier Y) := by
          exact congrArg (fun f => h.iso.inv ≫ f) h.hom_snd.symm
    _ = sourceOverBaseProduct.snd (k := k) D.carrier Y := by
          exact Category.id_comp _

theorem trans_hom_fst {X : Geometry.SmSchemeOver k} {Y : Geometry.SmSchemeOver k}
    {C D E : SourceImageSubscheme (k := k) X}
    (hCD : CompatibleOverBaseProductIso (Y := Y) C D)
    (hDE : CompatibleOverBaseProductIso (Y := Y) D E) :
    (hCD.iso ≪≫ hDE.iso).hom ≫ sourceOverBaseProduct.fst (k := k) E.carrier Y =
      sourceOverBaseProduct.fst (k := k) C.carrier Y ≫
        (hCD.sourceIso.iso ≪≫ hDE.sourceIso.iso).hom := by
  calc
    (hCD.iso ≪≫ hDE.iso).hom ≫ sourceOverBaseProduct.fst (k := k) E.carrier Y =
        hCD.iso.hom ≫ (hDE.iso.hom ≫ sourceOverBaseProduct.fst (k := k) E.carrier Y) := by
            rfl
    _ = hCD.iso.hom ≫
          (sourceOverBaseProduct.fst (k := k) D.carrier Y ≫ hDE.sourceIso.iso.hom) := by
          exact congrArg (fun f => hCD.iso.hom ≫ f) hDE.hom_fst
    _ = (hCD.iso.hom ≫ sourceOverBaseProduct.fst (k := k) D.carrier Y) ≫
          hDE.sourceIso.iso.hom := by
          exact Category.assoc _ _ _
    _ = (sourceOverBaseProduct.fst (k := k) C.carrier Y ≫ hCD.sourceIso.iso.hom) ≫
          hDE.sourceIso.iso.hom := by
          exact congrArg (fun f => f ≫ hDE.sourceIso.iso.hom) hCD.hom_fst
    _ = sourceOverBaseProduct.fst (k := k) C.carrier Y ≫
          (hCD.sourceIso.iso ≪≫ hDE.sourceIso.iso).hom := by
          rfl

theorem trans_hom_snd {X : Geometry.SmSchemeOver k} {Y : Geometry.SmSchemeOver k}
    {C D E : SourceImageSubscheme (k := k) X}
    (hCD : CompatibleOverBaseProductIso (Y := Y) C D)
    (hDE : CompatibleOverBaseProductIso (Y := Y) D E) :
    (hCD.iso ≪≫ hDE.iso).hom ≫ sourceOverBaseProduct.snd (k := k) E.carrier Y =
      sourceOverBaseProduct.snd (k := k) C.carrier Y := by
  calc
    (hCD.iso ≪≫ hDE.iso).hom ≫ sourceOverBaseProduct.snd (k := k) E.carrier Y =
        hCD.iso.hom ≫ (hDE.iso.hom ≫ sourceOverBaseProduct.snd (k := k) E.carrier Y) := by
            rfl
    _ = hCD.iso.hom ≫ sourceOverBaseProduct.snd (k := k) D.carrier Y := by
          exact congrArg (fun f => hCD.iso.hom ≫ f) hDE.hom_snd
    _ = sourceOverBaseProduct.snd (k := k) C.carrier Y := by
          exact hCD.hom_snd

def refl {X : Geometry.SmSchemeOver k} {Y : Geometry.SmSchemeOver k}
    (C : SourceImageSubscheme (k := k) X) : CompatibleOverBaseProductIso (Y := Y) C C where
  sourceIso := SourceImageSubscheme.IsoOverAmbient.refl C
  iso := Iso.refl _
  hom_fst := Category.id_comp _
  hom_snd := Category.id_comp (sourceOverBaseProduct.snd (k := k) C.carrier Y)

def symm {X : Geometry.SmSchemeOver k} {Y : Geometry.SmSchemeOver k}
    {C D : SourceImageSubscheme (k := k) X}
    (h : CompatibleOverBaseProductIso (Y := Y) C D) :
    CompatibleOverBaseProductIso (Y := Y) D C where
  sourceIso := h.sourceIso.symm
  iso := h.iso.symm
  hom_fst := h.symm_hom_fst
  hom_snd := h.symm_hom_snd

def trans {X : Geometry.SmSchemeOver k} {Y : Geometry.SmSchemeOver k}
    {C D E : SourceImageSubscheme (k := k) X}
    (hCD : CompatibleOverBaseProductIso (Y := Y) C D)
    (hDE : CompatibleOverBaseProductIso (Y := Y) D E) :
    CompatibleOverBaseProductIso (Y := Y) C E where
  sourceIso := hCD.sourceIso.trans hDE.sourceIso
  iso := hCD.iso ≪≫ hDE.iso
  hom_fst := hCD.trans_hom_fst hDE
  hom_snd := hCD.trans_hom_snd hDE

def ofIsoOverAmbient {X : Geometry.SmSchemeOver k} {Y : Geometry.SmSchemeOver k}
    {C D : SourceImageSubscheme (k := k) X}
    (h : SourceImageSubscheme.IsoOverAmbient C D) :
    CompatibleOverBaseProductIso (Y := Y) C D where
  sourceIso := h
  iso := h.overBaseProductIso (Y := Y)
  hom_fst := h.overBaseProductIso_hom_fst (Y := Y)
  hom_snd := h.overBaseProductIso_hom_snd (Y := Y)

end CompatibleOverBaseProductIso

end SourceImageSubscheme.IsoOverAmbient

structure PrimeFiniteCorrespondenceSupport
    (X Y : Geometry.SmSchemeOver k) where
  sourceImage : SourceImageSubscheme (k := k) X
  support : Scheme
  isIntegral : IsIntegral support
  finiteOverSourceComponent : support ⟶ sourceImage.carrier.scheme
  finite_toSourceComponent : IsFinite finiteOverSourceComponent
  surjective_toSourceComponent : Function.Surjective finiteOverSourceComponent.base
  toTarget : support ⟶ Y.scheme
  inclusion : support ⟶ sourceOverBaseProduct (k := k) sourceImage.carrier Y
  inclusion_fst : inclusion ≫ sourceOverBaseProduct.fst (k := k) sourceImage.carrier Y =
    finiteOverSourceComponent
  inclusion_snd : inclusion ≫ sourceOverBaseProduct.snd (k := k) sourceImage.carrier Y =
    toTarget
  isClosedImmersion : IsClosedImmersion inclusion

abbrev RepresentedPrimeSupport (X Y : Geometry.SmSchemeOver k) : Type (u + 1) :=
  PrimeFiniteCorrespondenceSupport X Y

namespace PrimeFiniteCorrespondenceSupport

abbrev sourceComponent {X Y : Geometry.SmSchemeOver k}
    (Z : PrimeFiniteCorrespondenceSupport (k := k) X Y) : SourceImageSubscheme (k := k) X :=
  Z.sourceImage

abbrev toSourceImage {X Y : Geometry.SmSchemeOver k}
    (Z : PrimeFiniteCorrespondenceSupport (k := k) X Y) :
    Z.support ⟶ Z.sourceImage.carrier.scheme :=
  Z.finiteOverSourceComponent

abbrev toSourceComponent {X Y : Geometry.SmSchemeOver k}
    (Z : PrimeFiniteCorrespondenceSupport (k := k) X Y) :
    Z.support ⟶ Z.sourceImage.carrier.scheme :=
  Z.toSourceImage

abbrev toTargetScheme {X Y : Geometry.SmSchemeOver k}
    (Z : PrimeFiniteCorrespondenceSupport (k := k) X Y) : Z.support ⟶ Y.scheme :=
  Z.toTarget

abbrev toAmbientSource {X Y : Geometry.SmSchemeOver k}
    (Z : PrimeFiniteCorrespondenceSupport (k := k) X Y) : Z.support ⟶ X.scheme :=
  Z.toSourceImage ≫ Z.sourceImage.toAmbient

abbrev compositionFiberProduct {X Y Z : Geometry.SmSchemeOver k}
    (P : RepresentedPrimeSupport X Y) (Q : RepresentedPrimeSupport Y Z) : Scheme :=
  pullback P.toTargetScheme Q.toAmbientSource

abbrev compositionFiberFst {X Y Z : Geometry.SmSchemeOver k}
    (P : RepresentedPrimeSupport X Y) (Q : RepresentedPrimeSupport Y Z) :
    compositionFiberProduct P Q ⟶ P.support :=
  pullback.fst P.toTargetScheme Q.toAmbientSource

abbrev compositionFiberSnd {X Y Z : Geometry.SmSchemeOver k}
    (P : RepresentedPrimeSupport X Y) (Q : RepresentedPrimeSupport Y Z) :
    compositionFiberProduct P Q ⟶ Q.support :=
  pullback.snd P.toTargetScheme Q.toAmbientSource

@[simp] theorem compositionFiber_condition {X Y Z : Geometry.SmSchemeOver k}
    (P : RepresentedPrimeSupport X Y) (Q : RepresentedPrimeSupport Y Z) :
    compositionFiberFst P Q ≫ P.toTargetScheme =
      compositionFiberSnd P Q ≫ Q.toAmbientSource := by
  exact pullback.condition (f := P.toTargetScheme) (g := Q.toAmbientSource)

@[simp] theorem toSourceComponent_overBase {X Y : Geometry.SmSchemeOver k}
    (Z : PrimeFiniteCorrespondenceSupport (k := k) X Y) :
    Z.toSourceComponent ≫ Z.sourceImage.carrier.structMap =
      Z.toTargetScheme ≫ Y.structMap := by
  calc
    Z.toSourceComponent ≫ Z.sourceImage.carrier.structMap =
        Z.inclusion ≫ sourceOverBaseProduct.fst (k := k) Z.sourceImage.carrier Y ≫
          Z.sourceImage.carrier.structMap := by
            exact congrArg (fun f => f ≫ Z.sourceImage.carrier.structMap) Z.inclusion_fst.symm
    _ = Z.inclusion ≫
          (sourceOverBaseProduct.fst (k := k) Z.sourceImage.carrier Y ≫
            Z.sourceImage.carrier.structMap) := by
            exact (Category.assoc _ _ _).symm
    _ = Z.inclusion ≫
          (sourceOverBaseProduct.snd (k := k) Z.sourceImage.carrier Y ≫ Y.structMap) := by
            exact congrArg (fun f => Z.inclusion ≫ f)
              (sourceOverBaseProduct_condition (k := k) Z.sourceImage.carrier Y)
    _ = (Z.inclusion ≫ sourceOverBaseProduct.snd (k := k) Z.sourceImage.carrier Y) ≫
          Y.structMap := by
            exact (Category.assoc _ _ _).symm
    _ = Z.toTargetScheme ≫ Y.structMap := by
            exact congrArg (fun f => f ≫ Y.structMap) Z.inclusion_snd

@[simp] theorem toAmbientSource_overBase {X Y : Geometry.SmSchemeOver k}
    (Z : PrimeFiniteCorrespondenceSupport (k := k) X Y) :
    Z.toAmbientSource ≫ X.structMap = Z.toTargetScheme ≫ Y.structMap := by
  calc
    Z.toAmbientSource ≫ X.structMap =
        (Z.toSourceComponent ≫ Z.sourceImage.toAmbient) ≫ X.structMap :=
          rfl
    _ = Z.toSourceComponent ≫ (Z.sourceImage.toAmbient ≫ X.structMap) :=
          Category.assoc Z.toSourceComponent Z.sourceImage.toAmbient X.structMap
    _ = Z.toSourceComponent ≫ Z.sourceImage.carrier.structMap :=
          congrArg (fun f => Z.toSourceComponent ≫ f) Z.sourceImage.toAmbient_overBase
    _ = Z.toTargetScheme ≫ Y.structMap :=
          Z.toSourceComponent_overBase

/-- The two maps used to send `P ×_Y Q` to `source(P) ×_k Z`
have the same structure map to `Spec k`. -/
theorem compositionToAmbientProduct_lift_condition {X Y Z : Geometry.SmSchemeOver k}
    (P : RepresentedPrimeSupport X Y) (Q : RepresentedPrimeSupport Y Z) :
    compositionFiberFst P Q ≫ P.toSourceComponent ≫ P.sourceImage.carrier.structMap =
      compositionFiberSnd P Q ≫ Q.toTargetScheme ≫ Z.structMap := by
  have source_component_condition :
      compositionFiberFst P Q ≫ P.toSourceComponent ≫ P.sourceImage.carrier.structMap =
        compositionFiberFst P Q ≫ P.toTargetScheme ≫ Y.structMap := by
    exact congrArg (fun f => compositionFiberFst P Q ≫ f) P.toSourceComponent_overBase
  have fiber_condition :
      compositionFiberFst P Q ≫ P.toTargetScheme ≫ Y.structMap =
        compositionFiberSnd P Q ≫ Q.toAmbientSource ≫ Y.structMap :=
    congrArg (fun f => f ≫ Y.structMap) (compositionFiber_condition P Q)
  have target_condition :
      compositionFiberSnd P Q ≫ Q.toAmbientSource ≫ Y.structMap =
        compositionFiberSnd P Q ≫ Q.toTargetScheme ≫ Z.structMap := by
    exact congrArg (fun f => compositionFiberSnd P Q ≫ f) Q.toAmbientSource_overBase
  calc
    compositionFiberFst P Q ≫ P.toSourceComponent ≫ P.sourceImage.carrier.structMap =
        compositionFiberFst P Q ≫ P.toTargetScheme ≫ Y.structMap :=
          source_component_condition
    _ = compositionFiberSnd P Q ≫ Q.toAmbientSource ≫ Y.structMap :=
          fiber_condition
    _ = compositionFiberSnd P Q ≫ Q.toTargetScheme ≫ Z.structMap :=
          target_condition

abbrev compositionToAmbientProduct {X Y Z : Geometry.SmSchemeOver k}
    (P : RepresentedPrimeSupport X Y) (Q : RepresentedPrimeSupport Y Z) :
    compositionFiberProduct P Q ⟶ sourceOverBaseProduct (k := k) P.sourceImage.carrier Z :=
  pullback.lift
    (compositionFiberFst P Q ≫ P.toSourceComponent)
    (compositionFiberSnd P Q ≫ Q.toTargetScheme)
    (compositionToAmbientProduct_lift_condition P Q)

@[simp] theorem compositionToAmbientProduct_fst {X Y Z : Geometry.SmSchemeOver k}
    (P : RepresentedPrimeSupport X Y) (Q : RepresentedPrimeSupport Y Z) :
    compositionToAmbientProduct P Q ≫ sourceOverBaseProduct.fst (k := k) P.sourceImage.carrier Z =
      compositionFiberFst P Q ≫ P.toSourceComponent := by
  exact pullback.lift_fst _ _ _

@[simp] theorem compositionToAmbientProduct_snd {X Y Z : Geometry.SmSchemeOver k}
    (P : RepresentedPrimeSupport X Y) (Q : RepresentedPrimeSupport Y Z) :
    compositionToAmbientProduct P Q ≫ sourceOverBaseProduct.snd (k := k) P.sourceImage.carrier Z =
      compositionFiberSnd P Q ≫ Q.toTargetScheme := by
  exact pullback.lift_snd _ _ _

abbrev leftAssociatedCompositionFiberProduct {W X Y Z : Geometry.SmSchemeOver k}
    (P : RepresentedPrimeSupport W X) (Q : RepresentedPrimeSupport X Y)
    (R : RepresentedPrimeSupport Y Z) : Scheme :=
  pullback (compositionFiberSnd P Q ≫ Q.toTargetScheme) R.toAmbientSource

abbrev rightAssociatedCompositionFiberProduct {W X Y Z : Geometry.SmSchemeOver k}
    (P : RepresentedPrimeSupport W X) (Q : RepresentedPrimeSupport X Y)
    (R : RepresentedPrimeSupport Y Z) : Scheme :=
  pullback P.toTargetScheme (compositionFiberFst Q R ≫ Q.toAmbientSource)

/-- The two maps used to send the left-associated fiber product to
`source(P) ×_k Z` have the same structure map to `Spec k`. -/
theorem leftAssociatedCompositionToAmbientProduct_lift_condition
    {W X Y Z : Geometry.SmSchemeOver k}
    (P : RepresentedPrimeSupport W X) (Q : RepresentedPrimeSupport X Y)
    (R : RepresentedPrimeSupport Y Z) :
    pullback.fst (compositionFiberSnd P Q ≫ Q.toTargetScheme) R.toAmbientSource ≫
        compositionFiberFst P Q ≫ P.toSourceComponent ≫ P.sourceImage.carrier.structMap =
      pullback.snd (compositionFiberSnd P Q ≫ Q.toTargetScheme) R.toAmbientSource ≫
        R.toTargetScheme ≫ Z.structMap := by
  let leftFst : leftAssociatedCompositionFiberProduct P Q R ⟶ compositionFiberProduct P Q :=
    pullback.fst (compositionFiberSnd P Q ≫ Q.toTargetScheme) R.toAmbientSource
  let leftSnd : leftAssociatedCompositionFiberProduct P Q R ⟶ R.support :=
    pullback.snd (compositionFiberSnd P Q ≫ Q.toTargetScheme) R.toAmbientSource
  have source_component_condition :
      leftFst ≫ compositionFiberFst P Q ≫ P.toSourceComponent ≫
          P.sourceImage.carrier.structMap =
        leftFst ≫ compositionFiberFst P Q ≫ P.toTargetScheme ≫ X.structMap := by
    exact congrArg
      (fun f => leftFst ≫ compositionFiberFst P Q ≫ f) P.toSourceComponent_overBase
  have first_fiber_condition :
      leftFst ≫ compositionFiberFst P Q ≫ P.toTargetScheme ≫ X.structMap =
        leftFst ≫ compositionFiberSnd P Q ≫ Q.toAmbientSource ≫ X.structMap :=
    congrArg (fun f => f ≫ X.structMap)
      (congrArg (fun f => leftFst ≫ f) (compositionFiber_condition P Q))
  have middle_condition :
      leftFst ≫ compositionFiberSnd P Q ≫ Q.toAmbientSource ≫ X.structMap =
        leftFst ≫ compositionFiberSnd P Q ≫ Q.toTargetScheme ≫ Y.structMap := by
    exact congrArg
      (fun f => leftFst ≫ compositionFiberSnd P Q ≫ f) Q.toAmbientSource_overBase
  have second_fiber_condition :
      leftFst ≫ compositionFiberSnd P Q ≫ Q.toTargetScheme ≫ Y.structMap =
        leftSnd ≫ R.toAmbientSource ≫ Y.structMap := by
    exact congrArg (fun f => f ≫ Y.structMap)
      (pullback.condition (f := compositionFiberSnd P Q ≫ Q.toTargetScheme)
        (g := R.toAmbientSource))
  have target_condition :
      leftSnd ≫ R.toAmbientSource ≫ Y.structMap =
        leftSnd ≫ R.toTargetScheme ≫ Z.structMap := by
    exact congrArg (fun f => leftSnd ≫ f) R.toAmbientSource_overBase
  calc
    leftFst ≫ compositionFiberFst P Q ≫ P.toSourceComponent ≫
        P.sourceImage.carrier.structMap =
        leftFst ≫ compositionFiberFst P Q ≫ P.toTargetScheme ≫ X.structMap :=
          source_component_condition
    _ = leftFst ≫ compositionFiberSnd P Q ≫ Q.toAmbientSource ≫ X.structMap :=
          first_fiber_condition
    _ = leftFst ≫ compositionFiberSnd P Q ≫ Q.toTargetScheme ≫ Y.structMap :=
          middle_condition
    _ = leftSnd ≫ R.toAmbientSource ≫ Y.structMap :=
          second_fiber_condition
    _ = leftSnd ≫ R.toTargetScheme ≫ Z.structMap :=
          target_condition

abbrev leftAssociatedCompositionToAmbientProduct {W X Y Z : Geometry.SmSchemeOver k}
    (P : RepresentedPrimeSupport W X) (Q : RepresentedPrimeSupport X Y)
    (R : RepresentedPrimeSupport Y Z) :
    leftAssociatedCompositionFiberProduct P Q R ⟶ sourceOverBaseProduct (k := k) P.sourceImage.carrier Z := by
  let leftFst : leftAssociatedCompositionFiberProduct P Q R ⟶ compositionFiberProduct P Q :=
    pullback.fst (compositionFiberSnd P Q ≫ Q.toTargetScheme) R.toAmbientSource
  let leftSnd : leftAssociatedCompositionFiberProduct P Q R ⟶ R.support :=
    pullback.snd (compositionFiberSnd P Q ≫ Q.toTargetScheme) R.toAmbientSource
  exact pullback.lift
    (leftFst ≫ compositionFiberFst P Q ≫ P.toSourceComponent)
    (leftSnd ≫ R.toTargetScheme)
    (leftAssociatedCompositionToAmbientProduct_lift_condition P Q R)

@[simp] theorem leftAssociatedCompositionToAmbientProduct_fst
    {W X Y Z : Geometry.SmSchemeOver k}
    (P : RepresentedPrimeSupport W X) (Q : RepresentedPrimeSupport X Y)
    (R : RepresentedPrimeSupport Y Z) :
    leftAssociatedCompositionToAmbientProduct P Q R ≫
        sourceOverBaseProduct.fst (k := k) P.sourceImage.carrier Z =
      pullback.fst (compositionFiberSnd P Q ≫ Q.toTargetScheme) R.toAmbientSource ≫
        compositionFiberFst P Q ≫ P.toSourceComponent := by
  exact pullback.lift_fst _ _ _

@[simp] theorem leftAssociatedCompositionToAmbientProduct_snd
    {W X Y Z : Geometry.SmSchemeOver k}
    (P : RepresentedPrimeSupport W X) (Q : RepresentedPrimeSupport X Y)
    (R : RepresentedPrimeSupport Y Z) :
    leftAssociatedCompositionToAmbientProduct P Q R ≫
        sourceOverBaseProduct.snd (k := k) P.sourceImage.carrier Z =
      pullback.snd (compositionFiberSnd P Q ≫ Q.toTargetScheme) R.toAmbientSource ≫
        R.toTargetScheme := by
  exact pullback.lift_snd _ _ _

/-- The two maps used to send the right-associated fiber product to
`source(P) ×_k Z` have the same structure map to `Spec k`. -/
theorem rightAssociatedCompositionToAmbientProduct_lift_condition
    {W X Y Z : Geometry.SmSchemeOver k}
    (P : RepresentedPrimeSupport W X) (Q : RepresentedPrimeSupport X Y)
    (R : RepresentedPrimeSupport Y Z) :
    pullback.fst P.toTargetScheme (compositionFiberFst Q R ≫ Q.toAmbientSource) ≫
        P.toSourceComponent ≫ P.sourceImage.carrier.structMap =
      pullback.snd P.toTargetScheme (compositionFiberFst Q R ≫ Q.toAmbientSource) ≫
        compositionFiberSnd Q R ≫ R.toTargetScheme ≫ Z.structMap := by
  let rightFst : rightAssociatedCompositionFiberProduct P Q R ⟶ P.support :=
    pullback.fst P.toTargetScheme (compositionFiberFst Q R ≫ Q.toAmbientSource)
  let rightSnd : rightAssociatedCompositionFiberProduct P Q R ⟶ compositionFiberProduct Q R :=
    pullback.snd P.toTargetScheme (compositionFiberFst Q R ≫ Q.toAmbientSource)
  have source_component_condition :
      rightFst ≫ P.toSourceComponent ≫ P.sourceImage.carrier.structMap =
        rightFst ≫ P.toTargetScheme ≫ X.structMap := by
    exact congrArg (fun f => rightFst ≫ f) P.toSourceComponent_overBase
  have outer_fiber_condition :
      rightFst ≫ P.toTargetScheme ≫ X.structMap =
        rightSnd ≫ compositionFiberFst Q R ≫ Q.toAmbientSource ≫ X.structMap := by
    exact congrArg (fun f => f ≫ X.structMap)
      (pullback.condition (f := P.toTargetScheme)
        (g := compositionFiberFst Q R ≫ Q.toAmbientSource))
  have middle_condition :
      rightSnd ≫ compositionFiberFst Q R ≫ Q.toAmbientSource ≫ X.structMap =
        rightSnd ≫ compositionFiberFst Q R ≫ Q.toTargetScheme ≫ Y.structMap := by
    exact congrArg
      (fun f => rightSnd ≫ compositionFiberFst Q R ≫ f) Q.toAmbientSource_overBase
  have inner_fiber_condition :
      rightSnd ≫ compositionFiberFst Q R ≫ Q.toTargetScheme ≫ Y.structMap =
        rightSnd ≫ compositionFiberSnd Q R ≫ R.toAmbientSource ≫ Y.structMap :=
    congrArg (fun f => f ≫ Y.structMap)
      (congrArg (fun f => rightSnd ≫ f) (compositionFiber_condition Q R))
  have target_condition :
      rightSnd ≫ compositionFiberSnd Q R ≫ R.toAmbientSource ≫ Y.structMap =
        rightSnd ≫ compositionFiberSnd Q R ≫ R.toTargetScheme ≫ Z.structMap := by
    exact congrArg
      (fun f => rightSnd ≫ compositionFiberSnd Q R ≫ f) R.toAmbientSource_overBase
  calc
    rightFst ≫ P.toSourceComponent ≫ P.sourceImage.carrier.structMap =
        rightFst ≫ P.toTargetScheme ≫ X.structMap :=
          source_component_condition
    _ = rightSnd ≫ compositionFiberFst Q R ≫ Q.toAmbientSource ≫ X.structMap :=
          outer_fiber_condition
    _ = rightSnd ≫ compositionFiberFst Q R ≫ Q.toTargetScheme ≫ Y.structMap :=
          middle_condition
    _ = rightSnd ≫ compositionFiberSnd Q R ≫ R.toAmbientSource ≫ Y.structMap :=
          inner_fiber_condition
    _ = rightSnd ≫ compositionFiberSnd Q R ≫ R.toTargetScheme ≫ Z.structMap :=
          target_condition

abbrev rightAssociatedCompositionToAmbientProduct {W X Y Z : Geometry.SmSchemeOver k}
    (P : RepresentedPrimeSupport W X) (Q : RepresentedPrimeSupport X Y)
    (R : RepresentedPrimeSupport Y Z) :
    rightAssociatedCompositionFiberProduct P Q R ⟶ sourceOverBaseProduct (k := k) P.sourceImage.carrier Z := by
  let rightFst : rightAssociatedCompositionFiberProduct P Q R ⟶ P.support :=
    pullback.fst P.toTargetScheme (compositionFiberFst Q R ≫ Q.toAmbientSource)
  let rightSnd : rightAssociatedCompositionFiberProduct P Q R ⟶ compositionFiberProduct Q R :=
    pullback.snd P.toTargetScheme (compositionFiberFst Q R ≫ Q.toAmbientSource)
  exact pullback.lift
    (rightFst ≫ P.toSourceComponent)
    (rightSnd ≫ compositionFiberSnd Q R ≫ R.toTargetScheme)
    (rightAssociatedCompositionToAmbientProduct_lift_condition P Q R)

@[simp] theorem rightAssociatedCompositionToAmbientProduct_fst
    {W X Y Z : Geometry.SmSchemeOver k}
    (P : RepresentedPrimeSupport W X) (Q : RepresentedPrimeSupport X Y)
    (R : RepresentedPrimeSupport Y Z) :
    rightAssociatedCompositionToAmbientProduct P Q R ≫
        sourceOverBaseProduct.fst (k := k) P.sourceImage.carrier Z =
      pullback.fst P.toTargetScheme (compositionFiberFst Q R ≫ Q.toAmbientSource) ≫
        P.toSourceComponent := by
  exact pullback.lift_fst _ _ _

@[simp] theorem rightAssociatedCompositionToAmbientProduct_snd
    {W X Y Z : Geometry.SmSchemeOver k}
    (P : RepresentedPrimeSupport W X) (Q : RepresentedPrimeSupport X Y)
    (R : RepresentedPrimeSupport Y Z) :
    rightAssociatedCompositionToAmbientProduct P Q R ≫
        sourceOverBaseProduct.snd (k := k) P.sourceImage.carrier Z =
      pullback.snd P.toTargetScheme (compositionFiberFst Q R ≫ Q.toAmbientSource) ≫
        compositionFiberSnd Q R ≫ R.toTargetScheme := by
  exact pullback.lift_snd _ _ _

abbrev inducedMap {X Y : Geometry.SmSchemeOver k}
    (Z : PrimeFiniteCorrespondenceSupport X Y) :
    Z.support ⟶ sourceOverBaseProduct (k := k) Z.sourceImage.carrier Y :=
  Z.inclusion

end PrimeFiniteCorrespondenceSupport

end -- noncomputable section

end Boundary
