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
  hom_toAmbient := by simp

def symm {X : Geometry.SmSchemeOver k}
    {C D : SourceImageSubscheme (k := k) X} (h : IsoOverAmbient C D) :
    IsoOverAmbient D C where
  iso := h.iso.symm
  hom_toAmbient := by
    calc
      h.iso.inv ≫ C.toAmbient = h.iso.inv ≫ (h.iso.hom ≫ D.toAmbient) := by
        rw [h.hom_toAmbient]
      _ = D.toAmbient := by simp [Category.assoc]

def trans {X : Geometry.SmSchemeOver k}
    {C D E : SourceImageSubscheme (k := k) X}
    (hCD : IsoOverAmbient C D) (hDE : IsoOverAmbient D E) :
    IsoOverAmbient C E where
  iso := hCD.iso ≪≫ hDE.iso
  hom_toAmbient := by
    calc
      (hCD.iso ≪≫ hDE.iso).hom ≫ E.toAmbient = hCD.iso.hom ≫ (hDE.iso.hom ≫ E.toAmbient) := by
        simp [Category.assoc]
      _ = hCD.iso.hom ≫ D.toAmbient := by rw [hDE.hom_toAmbient]
      _ = C.toAmbient := by rw [hCD.hom_toAmbient]

theorem hom_structMap {X : Geometry.SmSchemeOver k}
    {C D : SourceImageSubscheme (k := k) X} (h : IsoOverAmbient C D) :
    h.iso.hom ≫ D.carrier.structMap = C.carrier.structMap := by
  calc
    h.iso.hom ≫ D.carrier.structMap = h.iso.hom ≫ (D.toAmbient ≫ X.structMap) := by
      rw [D.toAmbient_overBase]
    _ = (h.iso.hom ≫ D.toAmbient) ≫ X.structMap := by simp [Category.assoc]
    _ = C.toAmbient ≫ X.structMap := by rw [h.hom_toAmbient]
    _ = C.carrier.structMap := C.toAmbient_overBase

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

namespace SourceImageSubscheme.IsoOverAmbient

noncomputable def overBaseProductIso {X : Geometry.SmSchemeOver k}
    {Y : Geometry.SmSchemeOver k}
    {C D : SourceImageSubscheme (k := k) X}
    (h : SourceImageSubscheme.IsoOverAmbient C D) :
    sourceOverBaseProduct (k := k) C.carrier Y ≅ sourceOverBaseProduct (k := k) D.carrier Y := by
  refine asIso <|
    pullback.map C.carrier.structMap Y.structMap D.carrier.structMap Y.structMap
      h.iso.hom (𝟙 Y.scheme) (𝟙 (Spec (CommRingCat.of k))) ?_ ?_
  · simpa using h.hom_structMap.symm
  · simp

@[simp] theorem overBaseProductIso_hom_fst {X : Geometry.SmSchemeOver k}
    {Y : Geometry.SmSchemeOver k}
    {C D : SourceImageSubscheme (k := k) X}
    (h : SourceImageSubscheme.IsoOverAmbient C D) :
    (h.overBaseProductIso (Y := Y)).hom ≫ sourceOverBaseProduct.fst (k := k) D.carrier Y =
      sourceOverBaseProduct.fst (k := k) C.carrier Y ≫ h.iso.hom := by
  simp [SourceImageSubscheme.IsoOverAmbient.overBaseProductIso, Category.assoc]

@[simp] theorem overBaseProductIso_hom_snd {X : Geometry.SmSchemeOver k}
    {Y : Geometry.SmSchemeOver k}
    {C D : SourceImageSubscheme (k := k) X}
    (h : SourceImageSubscheme.IsoOverAmbient C D) :
    (h.overBaseProductIso (Y := Y)).hom ≫ sourceOverBaseProduct.snd (k := k) D.carrier Y =
      sourceOverBaseProduct.snd (k := k) C.carrier Y := by
  simp [SourceImageSubscheme.IsoOverAmbient.overBaseProductIso, Category.assoc]

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

def refl {X : Geometry.SmSchemeOver k} {Y : Geometry.SmSchemeOver k}
    (C : SourceImageSubscheme (k := k) X) : CompatibleOverBaseProductIso (Y := Y) C C where
  sourceIso := SourceImageSubscheme.IsoOverAmbient.refl C
  iso := Iso.refl _
  hom_fst := by simp [SourceImageSubscheme.IsoOverAmbient.refl]
  hom_snd := by simp [SourceImageSubscheme.IsoOverAmbient.refl]

def symm {X : Geometry.SmSchemeOver k} {Y : Geometry.SmSchemeOver k}
    {C D : SourceImageSubscheme (k := k) X}
    (h : CompatibleOverBaseProductIso (Y := Y) C D) :
    CompatibleOverBaseProductIso (Y := Y) D C where
  sourceIso := h.sourceIso.symm
  iso := h.iso.symm
  hom_fst := by
    have hleft :
        h.iso.inv ≫ sourceOverBaseProduct.fst (k := k) C.carrier Y ≫ h.sourceIso.iso.hom =
          sourceOverBaseProduct.fst (k := k) D.carrier Y := by
      simpa [Category.assoc] using (congrArg (fun f => h.iso.inv ≫ f) h.hom_fst).symm
    have hright :
        h.iso.inv ≫ sourceOverBaseProduct.fst (k := k) C.carrier Y =
          sourceOverBaseProduct.fst (k := k) D.carrier Y ≫ h.sourceIso.iso.inv := by
      simpa [Category.assoc] using
        congrArg (fun f => f ≫ h.sourceIso.iso.inv) hleft
    simpa [Category.assoc] using hright
  hom_snd := by
    simpa [Category.assoc] using (congrArg (fun f => h.iso.inv ≫ f) h.hom_snd).symm

def trans {X : Geometry.SmSchemeOver k} {Y : Geometry.SmSchemeOver k}
    {C D E : SourceImageSubscheme (k := k) X}
    (hCD : CompatibleOverBaseProductIso (Y := Y) C D)
    (hDE : CompatibleOverBaseProductIso (Y := Y) D E) :
    CompatibleOverBaseProductIso (Y := Y) C E where
  sourceIso := hCD.sourceIso.trans hDE.sourceIso
  iso := hCD.iso ≪≫ hDE.iso
  hom_fst := by
    calc
      (hCD.iso ≪≫ hDE.iso).hom ≫ sourceOverBaseProduct.fst (k := k) E.carrier Y
          = hCD.iso.hom ≫ (hDE.iso.hom ≫ sourceOverBaseProduct.fst (k := k) E.carrier Y) := by
              simp [Category.assoc]
      _ = hCD.iso.hom ≫
            (sourceOverBaseProduct.fst (k := k) D.carrier Y ≫ hDE.sourceIso.iso.hom) := by
            rw [hDE.hom_fst]
      _ = (hCD.iso.hom ≫ sourceOverBaseProduct.fst (k := k) D.carrier Y) ≫
            hDE.sourceIso.iso.hom := by
            simp [Category.assoc]
      _ = (sourceOverBaseProduct.fst (k := k) C.carrier Y ≫ hCD.sourceIso.iso.hom) ≫
            hDE.sourceIso.iso.hom := by
            rw [hCD.hom_fst]
      _ = sourceOverBaseProduct.fst (k := k) C.carrier Y ≫
            (hCD.sourceIso.iso ≪≫ hDE.sourceIso.iso).hom := by
            simp [Category.assoc]
  hom_snd := by
    calc
      (hCD.iso ≪≫ hDE.iso).hom ≫ sourceOverBaseProduct.snd (k := k) E.carrier Y
          = hCD.iso.hom ≫ (hDE.iso.hom ≫ sourceOverBaseProduct.snd (k := k) E.carrier Y) := by
              simp [Category.assoc]
      _ = hCD.iso.hom ≫ sourceOverBaseProduct.snd (k := k) D.carrier Y := by
            rw [hDE.hom_snd]
      _ = sourceOverBaseProduct.snd (k := k) C.carrier Y := by
            rw [hCD.hom_snd]

def ofIsoOverAmbient {X : Geometry.SmSchemeOver k} {Y : Geometry.SmSchemeOver k}
    {C D : SourceImageSubscheme (k := k) X}
    (h : SourceImageSubscheme.IsoOverAmbient C D) :
    CompatibleOverBaseProductIso (Y := Y) C D where
  sourceIso := h
  iso := h.overBaseProductIso (Y := Y)
  hom_fst := by simpa using h.overBaseProductIso_hom_fst (Y := Y)
  hom_snd := by simpa using h.overBaseProductIso_hom_snd (Y := Y)

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
  simpa [compositionFiberProduct, compositionFiberFst, compositionFiberSnd] using
    pullback.condition (f := P.toTargetScheme) (g := Q.toAmbientSource)

@[simp] theorem toSourceComponent_overBase {X Y : Geometry.SmSchemeOver k}
    (Z : PrimeFiniteCorrespondenceSupport (k := k) X Y) :
    Z.toSourceComponent ≫ Z.sourceImage.carrier.structMap =
      Z.toTargetScheme ≫ Y.structMap := by
  have hfst := congrArg
    (fun f => f ≫ Z.sourceImage.carrier.structMap) Z.inclusion_fst
  have hsnd := congrArg (fun f => f ≫ Y.structMap) Z.inclusion_snd
  calc
    Z.toSourceComponent ≫ Z.sourceImage.carrier.structMap
        = Z.inclusion ≫ sourceOverBaseProduct.fst (k := k) Z.sourceImage.carrier Y ≫
            Z.sourceImage.carrier.structMap := by
              simpa [PrimeFiniteCorrespondenceSupport.toSourceComponent,
                PrimeFiniteCorrespondenceSupport.toSourceImage,
                Category.assoc] using hfst.symm
    _ = Z.inclusion ≫ sourceOverBaseProduct.snd (k := k) Z.sourceImage.carrier Y ≫ Y.structMap := by
          simp [sourceOverBaseProduct, Category.assoc, pullback.condition]
    _ = Z.toTargetScheme ≫ Y.structMap := by
          simpa [PrimeFiniteCorrespondenceSupport.toTargetScheme, Category.assoc] using hsnd

@[simp] theorem toAmbientSource_overBase {X Y : Geometry.SmSchemeOver k}
    (Z : PrimeFiniteCorrespondenceSupport (k := k) X Y) :
    Z.toAmbientSource ≫ X.structMap = Z.toTargetScheme ≫ Y.structMap := by
  simp [PrimeFiniteCorrespondenceSupport.toAmbientSource, Category.assoc,
    Z.toSourceComponent_overBase, Z.sourceImage.toAmbient_overBase]

abbrev compositionToAmbientProduct {X Y Z : Geometry.SmSchemeOver k}
    (P : RepresentedPrimeSupport X Y) (Q : RepresentedPrimeSupport Y Z) :
    compositionFiberProduct P Q ⟶ sourceOverBaseProduct (k := k) P.sourceImage.carrier Z :=
  pullback.lift
    (compositionFiberFst P Q ≫ P.toSourceComponent)
    (compositionFiberSnd P Q ≫ Q.toTargetScheme)
    (by
      have hP := congrArg
        (fun f => compositionFiberFst P Q ≫ f) P.toSourceComponent_overBase
      have hPQ' :
          compositionFiberFst P Q ≫ P.toTargetScheme ≫ Y.structMap =
            compositionFiberSnd P Q ≫ Q.toAmbientSource ≫ Y.structMap :=
        congrArg (fun f => f ≫ Y.structMap) (compositionFiber_condition P Q)
      have hQ := congrArg
        (fun f => compositionFiberSnd P Q ≫ f) Q.toAmbientSource_overBase
      calc
        compositionFiberFst P Q ≫ P.toSourceComponent ≫ P.sourceImage.carrier.structMap
            = compositionFiberFst P Q ≫ P.toTargetScheme ≫ Y.structMap := by
                simpa [Category.assoc] using hP
        _ = compositionFiberSnd P Q ≫ Q.toAmbientSource ≫ Y.structMap := by
              exact hPQ'
        _ = compositionFiberSnd P Q ≫ Q.toTargetScheme ≫ Z.structMap := by
              simpa [Category.assoc] using hQ)

@[simp] theorem compositionToAmbientProduct_fst {X Y Z : Geometry.SmSchemeOver k}
    (P : RepresentedPrimeSupport X Y) (Q : RepresentedPrimeSupport Y Z) :
    compositionToAmbientProduct P Q ≫ sourceOverBaseProduct.fst (k := k) P.sourceImage.carrier Z =
      compositionFiberFst P Q ≫ P.toSourceComponent := by
  simp [compositionToAmbientProduct]

@[simp] theorem compositionToAmbientProduct_snd {X Y Z : Geometry.SmSchemeOver k}
    (P : RepresentedPrimeSupport X Y) (Q : RepresentedPrimeSupport Y Z) :
    compositionToAmbientProduct P Q ≫ sourceOverBaseProduct.snd (k := k) P.sourceImage.carrier Z =
      compositionFiberSnd P Q ≫ Q.toTargetScheme := by
  simp [compositionToAmbientProduct]

abbrev leftAssociatedCompositionFiberProduct {W X Y Z : Geometry.SmSchemeOver k}
    (P : RepresentedPrimeSupport W X) (Q : RepresentedPrimeSupport X Y)
    (R : RepresentedPrimeSupport Y Z) : Scheme :=
  pullback (compositionFiberSnd P Q ≫ Q.toTargetScheme) R.toAmbientSource

abbrev rightAssociatedCompositionFiberProduct {W X Y Z : Geometry.SmSchemeOver k}
    (P : RepresentedPrimeSupport W X) (Q : RepresentedPrimeSupport X Y)
    (R : RepresentedPrimeSupport Y Z) : Scheme :=
  pullback P.toTargetScheme (compositionFiberFst Q R ≫ Q.toAmbientSource)

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
    (by
      have hP := congrArg
        (fun f => leftFst ≫ compositionFiberFst P Q ≫ f) P.toSourceComponent_overBase
      have hPQ :
          leftFst ≫ compositionFiberFst P Q ≫ P.toTargetScheme ≫ X.structMap =
            leftFst ≫ compositionFiberSnd P Q ≫ Q.toAmbientSource ≫ X.structMap := by
        exact congrArg (fun f => f ≫ X.structMap)
          (congrArg (fun f => leftFst ≫ f) (compositionFiber_condition P Q))
      have hQ := congrArg
        (fun f => leftFst ≫ compositionFiberSnd P Q ≫ f) Q.toAmbientSource_overBase
      have hleft :
          leftFst ≫ compositionFiberSnd P Q ≫ Q.toTargetScheme ≫ Y.structMap =
            leftSnd ≫ R.toAmbientSource ≫ Y.structMap := by
        simpa [leftFst, leftSnd, Category.assoc] using
          congrArg (fun f => f ≫ Y.structMap)
            (pullback.condition (f := compositionFiberSnd P Q ≫ Q.toTargetScheme)
              (g := R.toAmbientSource))
      have hR := congrArg (fun f => leftSnd ≫ f) R.toAmbientSource_overBase
      calc
        leftFst ≫ compositionFiberFst P Q ≫ P.toSourceComponent ≫
            P.sourceImage.carrier.structMap
            = leftFst ≫ compositionFiberFst P Q ≫ P.toTargetScheme ≫ X.structMap := by
                simpa [Category.assoc] using hP
        _ = leftFst ≫ compositionFiberSnd P Q ≫ Q.toAmbientSource ≫ X.structMap := by
              simpa [Category.assoc] using hPQ
        _ = leftFst ≫ compositionFiberSnd P Q ≫ Q.toTargetScheme ≫ Y.structMap := by
              simpa [Category.assoc] using hQ
        _ = leftSnd ≫ R.toAmbientSource ≫ Y.structMap := by
              simpa [Category.assoc] using hleft
        _ = leftSnd ≫ R.toTargetScheme ≫ Z.structMap := by
              simpa [Category.assoc] using hR)

@[simp] theorem leftAssociatedCompositionToAmbientProduct_fst
    {W X Y Z : Geometry.SmSchemeOver k}
    (P : RepresentedPrimeSupport W X) (Q : RepresentedPrimeSupport X Y)
    (R : RepresentedPrimeSupport Y Z) :
    leftAssociatedCompositionToAmbientProduct P Q R ≫
        sourceOverBaseProduct.fst (k := k) P.sourceImage.carrier Z =
      pullback.fst (compositionFiberSnd P Q ≫ Q.toTargetScheme) R.toAmbientSource ≫
        compositionFiberFst P Q ≫ P.toSourceComponent := by
  simp [leftAssociatedCompositionToAmbientProduct]

@[simp] theorem leftAssociatedCompositionToAmbientProduct_snd
    {W X Y Z : Geometry.SmSchemeOver k}
    (P : RepresentedPrimeSupport W X) (Q : RepresentedPrimeSupport X Y)
    (R : RepresentedPrimeSupport Y Z) :
    leftAssociatedCompositionToAmbientProduct P Q R ≫
        sourceOverBaseProduct.snd (k := k) P.sourceImage.carrier Z =
      pullback.snd (compositionFiberSnd P Q ≫ Q.toTargetScheme) R.toAmbientSource ≫
        R.toTargetScheme := by
  simp [leftAssociatedCompositionToAmbientProduct]

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
    (by
      have hP := congrArg (fun f => rightFst ≫ f) P.toSourceComponent_overBase
      have hright :
          rightFst ≫ P.toTargetScheme ≫ X.structMap =
            rightSnd ≫ compositionFiberFst Q R ≫ Q.toAmbientSource ≫ X.structMap := by
        simpa [rightFst, rightSnd, Category.assoc] using
          congrArg (fun f => f ≫ X.structMap)
            (pullback.condition (f := P.toTargetScheme)
              (g := compositionFiberFst Q R ≫ Q.toAmbientSource))
      have hQ := congrArg
        (fun f => rightSnd ≫ compositionFiberFst Q R ≫ f) Q.toAmbientSource_overBase
      have hQR :
          rightSnd ≫ compositionFiberFst Q R ≫ Q.toTargetScheme ≫ Y.structMap =
            rightSnd ≫ compositionFiberSnd Q R ≫ R.toAmbientSource ≫ Y.structMap := by
        exact congrArg (fun f => f ≫ Y.structMap)
          (congrArg (fun f => rightSnd ≫ f) (compositionFiber_condition Q R))
      have hR := congrArg
        (fun f => rightSnd ≫ compositionFiberSnd Q R ≫ f) R.toAmbientSource_overBase
      calc
        rightFst ≫ P.toSourceComponent ≫ P.sourceImage.carrier.structMap
            = rightFst ≫ P.toTargetScheme ≫ X.structMap := by
                simpa [Category.assoc] using hP
        _ = rightSnd ≫ compositionFiberFst Q R ≫ Q.toAmbientSource ≫ X.structMap := by
              simpa [Category.assoc] using hright
        _ = rightSnd ≫ compositionFiberFst Q R ≫ Q.toTargetScheme ≫ Y.structMap := by
              simpa [Category.assoc] using hQ
        _ = rightSnd ≫ compositionFiberSnd Q R ≫ R.toAmbientSource ≫ Y.structMap := by
              simpa [Category.assoc] using hQR
        _ = rightSnd ≫ compositionFiberSnd Q R ≫ R.toTargetScheme ≫ Z.structMap := by
              simpa [Category.assoc] using hR)

@[simp] theorem rightAssociatedCompositionToAmbientProduct_fst
    {W X Y Z : Geometry.SmSchemeOver k}
    (P : RepresentedPrimeSupport W X) (Q : RepresentedPrimeSupport X Y)
    (R : RepresentedPrimeSupport Y Z) :
    rightAssociatedCompositionToAmbientProduct P Q R ≫
        sourceOverBaseProduct.fst (k := k) P.sourceImage.carrier Z =
      pullback.fst P.toTargetScheme (compositionFiberFst Q R ≫ Q.toAmbientSource) ≫
        P.toSourceComponent := by
  simp [rightAssociatedCompositionToAmbientProduct]

@[simp] theorem rightAssociatedCompositionToAmbientProduct_snd
    {W X Y Z : Geometry.SmSchemeOver k}
    (P : RepresentedPrimeSupport W X) (Q : RepresentedPrimeSupport X Y)
    (R : RepresentedPrimeSupport Y Z) :
    rightAssociatedCompositionToAmbientProduct P Q R ≫
        sourceOverBaseProduct.snd (k := k) P.sourceImage.carrier Z =
      pullback.snd P.toTargetScheme (compositionFiberFst Q R ≫ Q.toAmbientSource) ≫
        compositionFiberSnd Q R ≫ R.toTargetScheme := by
  simp [rightAssociatedCompositionToAmbientProduct]

def compositionFiberProductAssocIso {W X Y Z : Geometry.SmSchemeOver k}
    (P : RepresentedPrimeSupport W X) (Q : RepresentedPrimeSupport X Y)
    (R : RepresentedPrimeSupport Y Z) :
    leftAssociatedCompositionFiberProduct P Q R ≅
      rightAssociatedCompositionFiberProduct P Q R := by
  classical
  let leftFst : leftAssociatedCompositionFiberProduct P Q R ⟶ compositionFiberProduct P Q :=
    pullback.fst (compositionFiberSnd P Q ≫ Q.toTargetScheme) R.toAmbientSource
  let leftSnd : leftAssociatedCompositionFiberProduct P Q R ⟶ R.support :=
    pullback.snd (compositionFiberSnd P Q ≫ Q.toTargetScheme) R.toAmbientSource
  let rightFst : rightAssociatedCompositionFiberProduct P Q R ⟶ P.support :=
    pullback.fst P.toTargetScheme (compositionFiberFst Q R ≫ Q.toAmbientSource)
  let rightSnd : rightAssociatedCompositionFiberProduct P Q R ⟶ compositionFiberProduct Q R :=
    pullback.snd P.toTargetScheme (compositionFiberFst Q R ≫ Q.toAmbientSource)
  let leftToQR : leftAssociatedCompositionFiberProduct P Q R ⟶ compositionFiberProduct Q R :=
    pullback.lift (leftFst ≫ compositionFiberSnd P Q) leftSnd (by
      simpa [leftFst, leftSnd, Category.assoc] using
        pullback.condition (f := compositionFiberSnd P Q ≫ Q.toTargetScheme)
          (g := R.toAmbientSource))
  let hom : leftAssociatedCompositionFiberProduct P Q R ⟶
      rightAssociatedCompositionFiberProduct P Q R :=
    pullback.lift (leftFst ≫ compositionFiberFst P Q) leftToQR (by
      calc
        leftFst ≫ compositionFiberFst P Q ≫ P.toTargetScheme
            = leftFst ≫ compositionFiberSnd P Q ≫ Q.toAmbientSource := by
                simpa [Category.assoc] using
                  congrArg (fun f => leftFst ≫ f) (compositionFiber_condition P Q)
        _ = leftToQR ≫ compositionFiberFst Q R ≫ Q.toAmbientSource := by
              simp [leftToQR, Category.assoc])
  let rightToPQ : rightAssociatedCompositionFiberProduct P Q R ⟶ compositionFiberProduct P Q :=
    pullback.lift rightFst (rightSnd ≫ compositionFiberFst Q R) (by
      simpa [rightFst, rightSnd, Category.assoc] using
        pullback.condition (f := P.toTargetScheme)
          (g := compositionFiberFst Q R ≫ Q.toAmbientSource))
  let inv : rightAssociatedCompositionFiberProduct P Q R ⟶
      leftAssociatedCompositionFiberProduct P Q R :=
    pullback.lift rightToPQ (rightSnd ≫ compositionFiberSnd Q R) (by
      calc
        rightToPQ ≫ compositionFiberSnd P Q ≫ Q.toTargetScheme
            = rightSnd ≫ compositionFiberFst Q R ≫ Q.toTargetScheme := by
                simp [rightToPQ, Category.assoc]
        _ = rightSnd ≫ compositionFiberSnd Q R ≫ R.toAmbientSource := by
              simpa [Category.assoc] using
                congrArg (fun f => rightSnd ≫ f) (compositionFiber_condition Q R))
  refine
    { hom := hom
      inv := inv
      hom_inv_id := ?_
      inv_hom_id := ?_ }
  · apply pullback.hom_ext
    · apply pullback.hom_ext
      · simp [hom, inv, leftFst, rightFst, rightToPQ, Category.assoc]
      · simp [hom, inv, leftFst, rightSnd, rightToPQ, leftToQR, Category.assoc]
    · simp [hom, inv, leftSnd, rightSnd, leftToQR, Category.assoc]
  · apply pullback.hom_ext
    · simp [hom, inv, leftFst, rightFst, rightToPQ, Category.assoc]
    · apply pullback.hom_ext
      · simp [hom, inv, leftFst, leftSnd, rightSnd, rightToPQ, leftToQR, Category.assoc]
      · simp [hom, inv, leftSnd, rightSnd, leftToQR, Category.assoc]

@[simp] theorem compositionFiberProductAssocIso_hom_comp_rightAssociatedCompositionToAmbientProduct
    {W X Y Z : Geometry.SmSchemeOver k}
    (P : RepresentedPrimeSupport W X) (Q : RepresentedPrimeSupport X Y)
    (R : RepresentedPrimeSupport Y Z) :
    (compositionFiberProductAssocIso P Q R).hom ≫
      rightAssociatedCompositionToAmbientProduct P Q R =
      leftAssociatedCompositionToAmbientProduct P Q R := by
  apply pullback.hom_ext
  · simp [compositionFiberProductAssocIso, leftAssociatedCompositionToAmbientProduct,
      rightAssociatedCompositionToAmbientProduct, Category.assoc]
  · simp [compositionFiberProductAssocIso, leftAssociatedCompositionToAmbientProduct,
      rightAssociatedCompositionToAmbientProduct, Category.assoc]

abbrev inducedMap {X Y : Geometry.SmSchemeOver k}
    (Z : PrimeFiniteCorrespondenceSupport X Y) :
    Z.support ⟶ sourceOverBaseProduct (k := k) Z.sourceImage.carrier Y :=
  Z.inclusion

end PrimeFiniteCorrespondenceSupport

end -- noncomputable section

end Boundary
