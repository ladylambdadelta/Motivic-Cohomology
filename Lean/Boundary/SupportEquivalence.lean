import Boundary.PrimeSupport

/-!
# Prime-Support Equivalence and Geometric Classes

This file packages the isomorphism-over-product relation on represented prime
supports and the resulting quotient-level geometric prime-support classes.
-/

universe u

variable {k : Type u} [Field k] [PerfectField k]

open AlgebraicGeometry CategoryTheory Limits

namespace Boundary

noncomputable section

namespace PrimeFiniteCorrespondenceSupport

/-- An explicit isomorphism-over-product relation on represented prime
supports.

Two represented prime supports are related when their represented source
images are isomorphic over the ambient source scheme and there is an
isomorphism of support schemes compatible with the embeddings into the induced
isomorphic fiber products. -/
def SupportIsoOverProduct {X Y : Geometry.SmSchemeOver k}
    (P Q : PrimeFiniteCorrespondenceSupport X Y) :=
  ∃ (compatible_source_component :
        SourceImageSubscheme.IsoOverAmbient.CompatibleOverBaseProductIso
          (Y := Y) P.sourceComponent Q.sourceComponent)
    (iso : P.support ≅ Q.support),
      P.inclusion ≫ compatible_source_component.iso.hom =
        iso.hom ≫ Q.inclusion

/-- Candidate geometric equivalence relation on represented prime supports. -/
abbrev PrimeSupportEquivalent {X Y : Geometry.SmSchemeOver k}
  (P Q : PrimeFiniteCorrespondenceSupport X Y) :=
  SupportIsoOverProduct P Q

/-- Reflexivity of the isomorphism-over-product relation. -/
theorem supportIsoOverProduct_refl {X Y : Geometry.SmSchemeOver k}
    (P : PrimeFiniteCorrespondenceSupport X Y) : SupportIsoOverProduct P P := by
  refine ⟨SourceImageSubscheme.IsoOverAmbient.CompatibleOverBaseProductIso.refl
      (Y := Y) P.sourceComponent,
    Iso.refl P.support, ?_⟩
  simp [SourceImageSubscheme.IsoOverAmbient.CompatibleOverBaseProductIso.refl]

theorem SupportIsoOverProduct.toSourceComponent_hom
    {X Y : Geometry.SmSchemeOver k}
    {P Q : PrimeFiniteCorrespondenceSupport X Y}
    (hPQ : SupportIsoOverProduct P Q) :
    P.toSourceComponent ≫ (Classical.choose hPQ).sourceIso.iso.hom =
      (Classical.choose (Classical.choose_spec hPQ)).hom ≫ Q.toSourceComponent := by
  classical
  let hcomp := Classical.choose hPQ
  let hrest := Classical.choose_spec hPQ
  let iso := Classical.choose hrest
  let hcomm := Classical.choose_spec hrest
  change P.toSourceComponent ≫ hcomp.sourceIso.iso.hom =
    iso.hom ≫ Q.toSourceComponent
  calc
    P.toSourceComponent ≫ hcomp.sourceIso.iso.hom =
        P.inclusion ≫ sourceOverBaseProduct.fst (k := k) P.sourceComponent.carrier Y ≫
          hcomp.sourceIso.iso.hom := by
          simpa [PrimeFiniteCorrespondenceSupport.toSourceComponent,
            Category.assoc] using
            congrArg (fun f => f ≫ hcomp.sourceIso.iso.hom) P.inclusion_fst.symm
    _ = P.inclusion ≫ hcomp.iso.hom ≫
          sourceOverBaseProduct.fst (k := k) Q.sourceComponent.carrier Y := by
          simpa [Category.assoc] using
            congrArg (fun f => P.inclusion ≫ f) hcomp.hom_fst.symm
    _ = iso.hom ≫ Q.inclusion ≫
          sourceOverBaseProduct.fst (k := k) Q.sourceComponent.carrier Y := by
          simpa [Category.assoc] using
            congrArg
              (fun f => f ≫ sourceOverBaseProduct.fst (k := k) Q.sourceComponent.carrier Y)
              hcomm
    _ = iso.hom ≫ Q.toSourceComponent := by
          simpa [PrimeFiniteCorrespondenceSupport.toSourceComponent,
            Category.assoc] using
            congrArg (fun f => iso.hom ≫ f) Q.inclusion_fst

theorem SupportIsoOverProduct.hom_toAmbientSource
    {X Y : Geometry.SmSchemeOver k}
    {P Q : PrimeFiniteCorrespondenceSupport X Y}
    (hPQ : SupportIsoOverProduct P Q) :
    (Classical.choose (Classical.choose_spec hPQ)).hom ≫ Q.toAmbientSource =
      P.toAmbientSource := by
  classical
  let hcomp := Classical.choose hPQ
  let hrest := Classical.choose_spec hPQ
  let iso := Classical.choose hrest
  have hsource := SupportIsoOverProduct.toSourceComponent_hom (P := P) (Q := Q) hPQ
  change iso.hom ≫ Q.toAmbientSource = P.toAmbientSource
  calc
    iso.hom ≫ Q.toAmbientSource =
        iso.hom ≫ Q.toSourceComponent ≫ Q.sourceComponent.toAmbient := by
        simp [PrimeFiniteCorrespondenceSupport.toAmbientSource, Category.assoc]
    _ = P.toSourceComponent ≫ hcomp.sourceIso.iso.hom ≫ Q.sourceComponent.toAmbient := by
        simpa [Category.assoc] using
          congrArg (fun f => f ≫ Q.sourceComponent.toAmbient) hsource.symm
    _ = P.toSourceComponent ≫ P.sourceComponent.toAmbient := by
        simpa [Category.assoc] using
          congrArg (fun f => P.toSourceComponent ≫ f) hcomp.sourceIso.hom_toAmbient
    _ = P.toAmbientSource := by
        simp [PrimeFiniteCorrespondenceSupport.toAmbientSource]

theorem SupportIsoOverProduct.hom_toTargetScheme
    {X Y : Geometry.SmSchemeOver k}
    {P Q : PrimeFiniteCorrespondenceSupport X Y}
    (hPQ : SupportIsoOverProduct P Q) :
    (Classical.choose (Classical.choose_spec hPQ)).hom ≫ Q.toTargetScheme =
      P.toTargetScheme := by
  classical
  let hcomp := Classical.choose hPQ
  let hrest := Classical.choose_spec hPQ
  let iso := Classical.choose hrest
  let hcomm := Classical.choose_spec hrest
  change iso.hom ≫ Q.toTargetScheme = P.toTargetScheme
  calc
    iso.hom ≫ Q.toTargetScheme =
        iso.hom ≫ Q.inclusion ≫
          sourceOverBaseProduct.snd (k := k) Q.sourceComponent.carrier Y := by
          simpa [PrimeFiniteCorrespondenceSupport.toTargetScheme,
            Category.assoc] using
            congrArg (fun f => iso.hom ≫ f) Q.inclusion_snd.symm
    _ = P.inclusion ≫ hcomp.iso.hom ≫
          sourceOverBaseProduct.snd (k := k) Q.sourceComponent.carrier Y := by
          simpa [Category.assoc] using
            congrArg
              (fun f => f ≫ sourceOverBaseProduct.snd (k := k) Q.sourceComponent.carrier Y)
              hcomm.symm
    _ = P.inclusion ≫
          sourceOverBaseProduct.snd (k := k) P.sourceComponent.carrier Y := by
          simpa [Category.assoc] using
            congrArg (fun f => P.inclusion ≫ f) hcomp.hom_snd
    _ = P.toTargetScheme := by
          simpa [PrimeFiniteCorrespondenceSupport.toTargetScheme,
            Category.assoc] using P.inclusion_snd

theorem supportIsoOverProduct_toSourceComponent_hom
    {X Y : Geometry.SmSchemeOver k}
    {P Q : PrimeFiniteCorrespondenceSupport X Y}
    (hPQ : SupportIsoOverProduct P Q) :
    P.toSourceComponent ≫ (Classical.choose hPQ).sourceIso.iso.hom =
      (Classical.choose (Classical.choose_spec hPQ)).hom ≫ Q.toSourceComponent :=
  SupportIsoOverProduct.toSourceComponent_hom hPQ

theorem supportIsoOverProduct_hom_toAmbientSource
    {X Y : Geometry.SmSchemeOver k}
    {P Q : PrimeFiniteCorrespondenceSupport X Y}
    (hPQ : SupportIsoOverProduct P Q) :
    (Classical.choose (Classical.choose_spec hPQ)).hom ≫ Q.toAmbientSource =
      P.toAmbientSource :=
  SupportIsoOverProduct.hom_toAmbientSource hPQ

theorem supportIsoOverProduct_hom_toTargetScheme
    {X Y : Geometry.SmSchemeOver k}
    {P Q : PrimeFiniteCorrespondenceSupport X Y}
    (hPQ : SupportIsoOverProduct P Q) :
    (Classical.choose (Classical.choose_spec hPQ)).hom ≫ Q.toTargetScheme =
      P.toTargetScheme :=
  SupportIsoOverProduct.hom_toTargetScheme hPQ

theorem supportIsoOverProduct_comp_hom_toAmbientSource
    {X Y : Geometry.SmSchemeOver k}
    {P Q : PrimeFiniteCorrespondenceSupport X Y}
    (hPQ : SupportIsoOverProduct P Q)
    {W : Scheme.{u}} (f : W ⟶ P.support) :
    f ≫ (Classical.choose (Classical.choose_spec hPQ)).hom ≫ Q.toAmbientSource =
      f ≫ P.toAmbientSource := by
  simpa [Category.assoc] using
    congrArg (fun g => f ≫ g) (supportIsoOverProduct_hom_toAmbientSource hPQ)

theorem supportIsoOverProduct_comp_hom_toTargetScheme
    {X Y : Geometry.SmSchemeOver k}
    {P Q : PrimeFiniteCorrespondenceSupport X Y}
    (hPQ : SupportIsoOverProduct P Q)
    {W : Scheme.{u}} (f : W ⟶ P.support) :
    f ≫ (Classical.choose (Classical.choose_spec hPQ)).hom ≫ Q.toTargetScheme =
      f ≫ P.toTargetScheme := by
  simpa [Category.assoc] using
    congrArg (fun g => f ≫ g) (supportIsoOverProduct_hom_toTargetScheme hPQ)

theorem supportIsoOverProduct_hom_toTargetScheme_structMap
    {X Y : Geometry.SmSchemeOver k}
    {P Q : PrimeFiniteCorrespondenceSupport X Y}
    (hPQ : SupportIsoOverProduct P Q) :
    (Classical.choose (Classical.choose_spec hPQ)).hom ≫ Q.toTargetScheme ≫ Y.structMap =
      P.toTargetScheme ≫ Y.structMap := by
  simpa [Category.assoc] using
    congrArg (fun f => f ≫ Y.structMap) (supportIsoOverProduct_hom_toTargetScheme hPQ)

theorem supportIsoOverProduct_hom_toAmbientSource_structMap
    {X Y : Geometry.SmSchemeOver k}
    {P Q : PrimeFiniteCorrespondenceSupport X Y}
    (hPQ : SupportIsoOverProduct P Q) :
    (Classical.choose (Classical.choose_spec hPQ)).hom ≫ Q.toAmbientSource ≫ X.structMap =
      P.toAmbientSource ≫ X.structMap := by
  simpa [Category.assoc] using
    congrArg (fun f => f ≫ X.structMap) (supportIsoOverProduct_hom_toAmbientSource hPQ)

/-- Symmetry of the isomorphism-over-product relation. -/
theorem supportIsoOverProduct_symm {X Y : Geometry.SmSchemeOver k}
    {P Q : PrimeFiniteCorrespondenceSupport X Y}
    (hPQ : SupportIsoOverProduct P Q) : SupportIsoOverProduct Q P := by
  rcases hPQ with ⟨hcomp, iso, hcomm⟩
  refine ⟨SourceImageSubscheme.IsoOverAmbient.CompatibleOverBaseProductIso.symm hcomp,
    iso.symm, ?_⟩
  have hleft : iso.inv ≫ P.inclusion ≫ hcomp.iso.hom = Q.inclusion := by
    simpa [Category.assoc] using congrArg (fun f => iso.inv ≫ f) hcomm
  have hright : iso.inv ≫ P.inclusion = Q.inclusion ≫ hcomp.iso.inv := by
    simpa [Category.assoc] using
      congrArg (fun f => f ≫ hcomp.iso.inv) hleft
  simpa [SourceImageSubscheme.IsoOverAmbient.CompatibleOverBaseProductIso.symm,
    Category.assoc] using hright.symm

/-- Transitivity of the isomorphism-over-product relation. -/
theorem supportIsoOverProduct_trans {X Y : Geometry.SmSchemeOver k}
    {P Q R : PrimeFiniteCorrespondenceSupport X Y}
    (hPQ : SupportIsoOverProduct P Q) (hQR : SupportIsoOverProduct Q R) :
    SupportIsoOverProduct P R := by
  rcases hPQ with ⟨hcompPQ, isoPQ, hcommPQ⟩
  rcases hQR with ⟨hcompQR, isoQR, hcommQR⟩
  refine ⟨SourceImageSubscheme.IsoOverAmbient.CompatibleOverBaseProductIso.trans
      hcompPQ hcompQR,
    isoPQ ≪≫ isoQR, ?_⟩
  calc
    P.inclusion ≫ (hcompPQ.iso ≪≫ hcompQR.iso).hom
        = P.inclusion ≫ hcompPQ.iso.hom ≫ hcompQR.iso.hom := by
              simp [Category.assoc]
    _ = (isoPQ.hom ≫ Q.inclusion) ≫ hcompQR.iso.hom := by
          simpa [Category.assoc] using
            congrArg (fun f => f ≫ hcompQR.iso.hom) hcommPQ
    _ = isoPQ.hom ≫ (Q.inclusion ≫ hcompQR.iso.hom) := by
          simp [Category.assoc]
    _ = isoPQ.hom ≫ (isoQR.hom ≫ R.inclusion) := by rw [hcommQR]
    _ = (isoPQ ≪≫ isoQR).hom ≫ R.inclusion := by simp [Category.assoc]

/-- The setoid identifying represented prime supports that are isomorphic over
the same source-image fiber product. -/
def primeSupportEquivalentSetoid (X Y : Geometry.SmSchemeOver k) :
    Setoid (PrimeFiniteCorrespondenceSupport X Y) where
  r := PrimeSupportEquivalent
  iseqv := by
    refine ⟨?_, ?_, ?_⟩
    · intro P
      exact supportIsoOverProduct_refl P
    · intro P Q h
      exact supportIsoOverProduct_symm h
    · intro P Q R h₁ h₂
      exact supportIsoOverProduct_trans h₁ h₂

end PrimeFiniteCorrespondenceSupport

/-- Geometric prime finite correspondences: represented prime supports modulo
the isomorphism-over-product relation. -/
abbrev PrimeFiniteCorrespondenceGeom
    (X Y : Geometry.SmSchemeOver k) : Type (u + 1) :=
  Quotient (PrimeFiniteCorrespondenceSupport.primeSupportEquivalentSetoid X Y)

namespace PrimeFiniteCorrespondenceGeom

/-- The geometric class of a represented prime support. -/
def ofRepresented {X Y : Geometry.SmSchemeOver k}
    (P : PrimeFiniteCorrespondenceSupport X Y) : PrimeFiniteCorrespondenceGeom X Y :=
  Quotient.mk _ P

/-- Equivalent represented prime supports define the same geometric prime
support. -/
theorem eq_of_primeSupportEquivalent {X Y : Geometry.SmSchemeOver k}
    {P Q : RepresentedPrimeSupport X Y}
    (h : PrimeFiniteCorrespondenceSupport.PrimeSupportEquivalent P Q) :
    ofRepresented P = ofRepresented Q :=
  Quotient.sound h

end PrimeFiniteCorrespondenceGeom

end -- noncomputable section

end Boundary
