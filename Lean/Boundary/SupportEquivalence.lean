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
          (Y := Y) P.sourceImage Q.sourceImage)
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
      (Y := Y) P.sourceImage,
    Iso.refl P.support, ?_⟩
  rfl

theorem SupportIsoOverProduct.toSourceComponent_hom
    {X Y : Geometry.SmSchemeOver k}
    {P Q : PrimeFiniteCorrespondenceSupport X Y}
    (hPQ : SupportIsoOverProduct P Q) :
    P.finiteOverSourceComponent ≫ (Classical.choose hPQ).sourceIso.iso.hom =
      (Classical.choose (Classical.choose_spec hPQ)).hom ≫ Q.finiteOverSourceComponent := by
  classical
  let hcomp := Classical.choose hPQ
  let hrest := Classical.choose_spec hPQ
  let iso := Classical.choose hrest
  let hcomm := Classical.choose_spec hrest
  change P.inclusion ≫ hcomp.iso.hom = iso.hom ≫ Q.inclusion at hcomm
  change P.finiteOverSourceComponent ≫ hcomp.sourceIso.iso.hom =
    iso.hom ≫ Q.finiteOverSourceComponent
  calc
    P.finiteOverSourceComponent ≫ hcomp.sourceIso.iso.hom =
        P.inclusion ≫ sourceOverBaseProduct.fst (k := k) P.sourceImage.carrier Y ≫
          hcomp.sourceIso.iso.hom := by
          exact congrArg (fun f => f ≫ hcomp.sourceIso.iso.hom) P.inclusion_fst.symm
    _ = P.inclusion ≫ hcomp.iso.hom ≫
          sourceOverBaseProduct.fst (k := k) Q.sourceImage.carrier Y := by
          rw [← hcomp.hom_fst]
    _ = iso.hom ≫ Q.inclusion ≫
          sourceOverBaseProduct.fst (k := k) Q.sourceImage.carrier Y := by
          exact congrArg
            (fun f => f ≫ sourceOverBaseProduct.fst (k := k) Q.sourceImage.carrier Y)
            hcomm
    _ = iso.hom ≫ Q.finiteOverSourceComponent := by
          rw [Q.inclusion_fst]

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
  change P.finiteOverSourceComponent ≫ hcomp.sourceIso.iso.hom =
    iso.hom ≫ Q.finiteOverSourceComponent at hsource
  change iso.hom ≫ Q.toAmbientSource = P.toAmbientSource
  calc
    iso.hom ≫ Q.toAmbientSource =
        iso.hom ≫ Q.finiteOverSourceComponent ≫ Q.sourceImage.toAmbient := by
        rfl
    _ = P.finiteOverSourceComponent ≫ hcomp.sourceIso.iso.hom ≫ Q.sourceImage.toAmbient := by
        exact congrArg (fun f => f ≫ Q.sourceImage.toAmbient) hsource.symm
    _ = P.finiteOverSourceComponent ≫ P.sourceImage.toAmbient := by
        rw [hcomp.sourceIso.hom_toAmbient]
    _ = P.toAmbientSource := by
        rfl

theorem SupportIsoOverProduct.hom_toTargetScheme
    {X Y : Geometry.SmSchemeOver k}
    {P Q : PrimeFiniteCorrespondenceSupport X Y}
    (hPQ : SupportIsoOverProduct P Q) :
    (Classical.choose (Classical.choose_spec hPQ)).hom ≫ Q.toTarget =
      P.toTarget := by
  classical
  let hcomp := Classical.choose hPQ
  let hrest := Classical.choose_spec hPQ
  let iso := Classical.choose hrest
  let hcomm := Classical.choose_spec hrest
  change P.inclusion ≫ hcomp.iso.hom = iso.hom ≫ Q.inclusion at hcomm
  change iso.hom ≫ Q.toTarget = P.toTarget
  calc
    iso.hom ≫ Q.toTarget =
        iso.hom ≫ Q.inclusion ≫
          sourceOverBaseProduct.snd (k := k) Q.sourceImage.carrier Y := by
          exact congrArg (fun f => iso.hom ≫ f) Q.inclusion_snd.symm
    _ = P.inclusion ≫ hcomp.iso.hom ≫
          sourceOverBaseProduct.snd (k := k) Q.sourceImage.carrier Y := by
          exact congrArg
            (fun f => f ≫ sourceOverBaseProduct.snd (k := k) Q.sourceImage.carrier Y)
            hcomm.symm
    _ = P.inclusion ≫
          sourceOverBaseProduct.snd (k := k) P.sourceImage.carrier Y := by
          rw [hcomp.hom_snd]
    _ = P.toTarget := by
          exact P.inclusion_snd

theorem supportIsoOverProduct_toSourceComponent_hom
    {X Y : Geometry.SmSchemeOver k}
    {P Q : PrimeFiniteCorrespondenceSupport X Y}
    (hPQ : SupportIsoOverProduct P Q) :
    P.finiteOverSourceComponent ≫ (Classical.choose hPQ).sourceIso.iso.hom =
      (Classical.choose (Classical.choose_spec hPQ)).hom ≫ Q.finiteOverSourceComponent :=
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
    (Classical.choose (Classical.choose_spec hPQ)).hom ≫ Q.toTarget =
      P.toTarget :=
  SupportIsoOverProduct.hom_toTargetScheme hPQ

theorem supportIsoOverProduct_comp_hom_toAmbientSource
    {X Y : Geometry.SmSchemeOver k}
    {P Q : PrimeFiniteCorrespondenceSupport X Y}
    (hPQ : SupportIsoOverProduct P Q)
    {W : Scheme.{u}} (f : W ⟶ P.support) :
    f ≫ (Classical.choose (Classical.choose_spec hPQ)).hom ≫ Q.toAmbientSource =
      f ≫ P.toAmbientSource := by
  rw [supportIsoOverProduct_hom_toAmbientSource hPQ]

theorem supportIsoOverProduct_comp_hom_toTargetScheme
    {X Y : Geometry.SmSchemeOver k}
    {P Q : PrimeFiniteCorrespondenceSupport X Y}
    (hPQ : SupportIsoOverProduct P Q)
    {W : Scheme.{u}} (f : W ⟶ P.support) :
    f ≫ (Classical.choose (Classical.choose_spec hPQ)).hom ≫ Q.toTarget =
      f ≫ P.toTarget := by
  rw [supportIsoOverProduct_hom_toTargetScheme hPQ]

theorem supportIsoOverProduct_hom_toTargetScheme_structMap
    {X Y : Geometry.SmSchemeOver k}
    {P Q : PrimeFiniteCorrespondenceSupport X Y}
    (hPQ : SupportIsoOverProduct P Q) :
    (Classical.choose (Classical.choose_spec hPQ)).hom ≫ Q.toTarget ≫ Y.structMap =
      P.toTarget ≫ Y.structMap := by
  rw [← Category.assoc, supportIsoOverProduct_hom_toTargetScheme hPQ]

theorem supportIsoOverProduct_hom_toAmbientSource_structMap
    {X Y : Geometry.SmSchemeOver k}
    {P Q : PrimeFiniteCorrespondenceSupport X Y}
    (hPQ : SupportIsoOverProduct P Q) :
    (Classical.choose (Classical.choose_spec hPQ)).hom ≫ Q.toAmbientSource ≫ X.structMap =
      P.toAmbientSource ≫ X.structMap := by
  change
    ((Classical.choose (Classical.choose_spec hPQ)).hom ≫ Q.toAmbientSource) ≫ X.structMap =
      P.toAmbientSource ≫ X.structMap
  exact congrArg (fun f => f ≫ X.structMap)
    (supportIsoOverProduct_hom_toAmbientSource hPQ)

/-- Symmetry of the isomorphism-over-product relation. -/
theorem supportIsoOverProduct_symm {X Y : Geometry.SmSchemeOver k}
    {P Q : PrimeFiniteCorrespondenceSupport X Y}
    (hPQ : SupportIsoOverProduct P Q) : SupportIsoOverProduct Q P := by
  rcases hPQ with ⟨hcomp, iso, hcomm⟩
  refine ⟨SourceImageSubscheme.IsoOverAmbient.CompatibleOverBaseProductIso.symm hcomp,
    iso.symm, ?_⟩
  have hleft : iso.inv ≫ P.inclusion ≫ hcomp.iso.hom = Q.inclusion := by
    rw [hcomm]
    rw [← Category.assoc, Iso.inv_hom_id, Category.id_comp]
  have hright : iso.inv ≫ P.inclusion = Q.inclusion ≫ hcomp.iso.inv := by
    rw [← hleft]
    calc
      iso.inv ≫ P.inclusion =
          (iso.inv ≫ P.inclusion) ≫ 𝟙 _ := by
            rw [Category.comp_id]
      _ = (iso.inv ≫ P.inclusion) ≫ hcomp.iso.hom ≫ hcomp.iso.inv := by
            rw [Iso.hom_inv_id]
      _ = (iso.inv ≫ P.inclusion ≫ hcomp.iso.hom) ≫ hcomp.iso.inv := by
            rfl
  change Q.inclusion ≫ hcomp.iso.inv = iso.inv ≫ P.inclusion
  exact hright.symm

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
              rfl
    _ = (isoPQ.hom ≫ Q.inclusion) ≫ hcompQR.iso.hom := by
          exact congrArg (fun f => f ≫ hcompQR.iso.hom) hcommPQ
    _ = isoPQ.hom ≫ (Q.inclusion ≫ hcompQR.iso.hom) := by
          rw [Category.assoc]
    _ = isoPQ.hom ≫ (isoQR.hom ≫ R.inclusion) := by rw [hcommQR]
    _ = (isoPQ ≪≫ isoQR).hom ≫ R.inclusion := by rfl

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
