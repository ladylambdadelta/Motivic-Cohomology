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

/-- Source-component compatibility extracted from explicit support-isomorphism
witnesses. -/
theorem supportIsoOverProduct_toSourceComponent_hom_of_witness
    {X Y : Geometry.SmSchemeOver k}
    {P Q : PrimeFiniteCorrespondenceSupport X Y}
    (compatibleSource :
      SourceImageSubscheme.IsoOverAmbient.CompatibleOverBaseProductIso
        (Y := Y) P.sourceImage Q.sourceImage)
    (supportIso : P.support ≅ Q.support)
    (support_comm :
      P.inclusion ≫ compatibleSource.iso.hom =
        supportIso.hom ≫ Q.inclusion) :
    P.finiteOverSourceComponent ≫ compatibleSource.sourceIso.iso.hom =
      supportIso.hom ≫ Q.finiteOverSourceComponent :=
  calc
    P.finiteOverSourceComponent ≫ compatibleSource.sourceIso.iso.hom =
        P.inclusion ≫ sourceOverBaseProduct.fst (k := k) P.sourceImage.carrier Y ≫
          compatibleSource.sourceIso.iso.hom :=
          congrArg (fun f => f ≫ compatibleSource.sourceIso.iso.hom) P.inclusion_fst.symm
    _ = P.inclusion ≫
          (compatibleSource.iso.hom ≫ sourceOverBaseProduct.fst (k := k) Q.sourceImage.carrier Y) :=
          Eq.symm (Category.assoc _ _ _)
    _ = P.inclusion ≫
          (sourceOverBaseProduct.fst (k := k) P.sourceImage.carrier Y ≫
            compatibleSource.sourceIso.iso.hom) := by
          exact congrArg (fun f => P.inclusion ≫ f) compatibleSource.hom_fst.symm
    _ = supportIso.hom ≫ Q.inclusion ≫
          sourceOverBaseProduct.fst (k := k) Q.sourceImage.carrier Y :=
          congrArg
            (fun f => f ≫ sourceOverBaseProduct.fst (k := k) Q.sourceImage.carrier Y)
            support_comm
    _ = supportIso.hom ≫ Q.finiteOverSourceComponent :=
          congrArg (fun f => supportIso.hom ≫ f) Q.inclusion_fst

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
  exact
    supportIsoOverProduct_toSourceComponent_hom_of_witness
      (P := P) (Q := Q) hcomp iso hcomm

/-- An explicit support isomorphism over the source-product preserves the
ambient source map. -/
theorem supportIsoOverProduct_hom_toAmbientSource_of_witness
    {X Y : Geometry.SmSchemeOver k}
    {P Q : PrimeFiniteCorrespondenceSupport X Y}
    (compatibleSource :
      SourceImageSubscheme.IsoOverAmbient.CompatibleOverBaseProductIso
        (Y := Y) P.sourceImage Q.sourceImage)
    (supportIso : P.support ≅ Q.support)
    (support_comm :
      P.inclusion ≫ compatibleSource.iso.hom =
        supportIso.hom ≫ Q.inclusion) :
    supportIso.hom ≫ Q.toAmbientSource = P.toAmbientSource :=
  let sourceComponentCompatibility :
      P.finiteOverSourceComponent ≫ compatibleSource.sourceIso.iso.hom =
        supportIso.hom ≫ Q.finiteOverSourceComponent :=
    supportIsoOverProduct_toSourceComponent_hom_of_witness
      (P := P) (Q := Q) compatibleSource supportIso support_comm
  calc
    supportIso.hom ≫ Q.toAmbientSource =
        supportIso.hom ≫ Q.finiteOverSourceComponent ≫ Q.sourceImage.toAmbient :=
          rfl
    _ = P.finiteOverSourceComponent ≫ compatibleSource.sourceIso.iso.hom ≫
          Q.sourceImage.toAmbient :=
          congrArg (fun f => f ≫ Q.sourceImage.toAmbient)
            sourceComponentCompatibility.symm
    _ = P.finiteOverSourceComponent ≫ P.sourceImage.toAmbient :=
          congrArg (fun f => P.finiteOverSourceComponent ≫ f)
            compatibleSource.sourceIso.hom_toAmbient
    _ = P.toAmbientSource :=
          rfl

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
  let hcomm := Classical.choose_spec hrest
  exact
    supportIsoOverProduct_hom_toAmbientSource_of_witness
      (P := P) (Q := Q) hcomp iso hcomm

/-- An explicit support isomorphism over the source-product preserves the
target map. -/
theorem supportIsoOverProduct_hom_toTargetScheme_of_witness
    {X Y : Geometry.SmSchemeOver k}
    {P Q : PrimeFiniteCorrespondenceSupport X Y}
    (compatibleSource :
      SourceImageSubscheme.IsoOverAmbient.CompatibleOverBaseProductIso
        (Y := Y) P.sourceImage Q.sourceImage)
    (supportIso : P.support ≅ Q.support)
    (support_comm :
      P.inclusion ≫ compatibleSource.iso.hom =
        supportIso.hom ≫ Q.inclusion) :
    supportIso.hom ≫ Q.toTarget = P.toTarget :=
  calc
    supportIso.hom ≫ Q.toTarget =
        supportIso.hom ≫ Q.inclusion ≫
          sourceOverBaseProduct.snd (k := k) Q.sourceImage.carrier Y :=
          congrArg (fun f => supportIso.hom ≫ f) Q.inclusion_snd.symm
    _ = P.inclusion ≫ compatibleSource.iso.hom ≫
          sourceOverBaseProduct.snd (k := k) Q.sourceImage.carrier Y :=
          congrArg
            (fun f => f ≫ sourceOverBaseProduct.snd (k := k) Q.sourceImage.carrier Y)
            support_comm.symm
    _ = P.inclusion ≫ sourceOverBaseProduct.snd (k := k) P.sourceImage.carrier Y :=
          congrArg (fun f => P.inclusion ≫ f) compatibleSource.hom_snd
    _ = P.toTarget :=
          P.inclusion_snd

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
  exact
    supportIsoOverProduct_hom_toTargetScheme_of_witness
      (P := P) (Q := Q) hcomp iso hcomm

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
  exact congrArg (fun g => f ≫ g) (supportIsoOverProduct_hom_toAmbientSource hPQ)

theorem supportIsoOverProduct_comp_hom_toTargetScheme
    {X Y : Geometry.SmSchemeOver k}
    {P Q : PrimeFiniteCorrespondenceSupport X Y}
    (hPQ : SupportIsoOverProduct P Q)
    {W : Scheme.{u}} (f : W ⟶ P.support) :
    f ≫ (Classical.choose (Classical.choose_spec hPQ)).hom ≫ Q.toTarget =
      f ≫ P.toTarget := by
  exact congrArg (fun g => f ≫ g) (supportIsoOverProduct_hom_toTargetScheme hPQ)

theorem supportIsoOverProduct_hom_toTargetScheme_structMap
    {X Y : Geometry.SmSchemeOver k}
    {P Q : PrimeFiniteCorrespondenceSupport X Y}
    (hPQ : SupportIsoOverProduct P Q) :
    (Classical.choose (Classical.choose_spec hPQ)).hom ≫ Q.toTarget ≫ Y.structMap =
      P.toTarget ≫ Y.structMap := by
  exact congrArg (fun g => g ≫ Y.structMap) (supportIsoOverProduct_hom_toTargetScheme hPQ)

theorem supportIsoOverProduct_hom_toAmbientSource_structMap
    {X Y : Geometry.SmSchemeOver k}
    {P Q : PrimeFiniteCorrespondenceSupport X Y}
    (hPQ : SupportIsoOverProduct P Q) :
    (Classical.choose (Classical.choose_spec hPQ)).hom ≫ Q.toAmbientSource ≫ X.structMap =
      P.toAmbientSource ≫ X.structMap := by
  exact congrArg (fun f => f ≫ X.structMap)
    (supportIsoOverProduct_hom_toAmbientSource hPQ)

/-- The inverse support isomorphism satisfies the support-embedding
compatibility needed for symmetry of `SupportIsoOverProduct`. -/
theorem supportIsoOverProduct_symm_comm_of_witness
    {X Y : Geometry.SmSchemeOver k}
    {P Q : PrimeFiniteCorrespondenceSupport X Y}
    (compatibleSource :
      SourceImageSubscheme.IsoOverAmbient.CompatibleOverBaseProductIso
        (Y := Y) P.sourceImage Q.sourceImage)
    (supportIso : P.support ≅ Q.support)
    (support_comm :
      P.inclusion ≫ compatibleSource.iso.hom =
        supportIso.hom ≫ Q.inclusion) :
    Q.inclusion ≫ compatibleSource.iso.inv =
      supportIso.inv ≫ P.inclusion := by
  have inverse_left_support_comm :
      supportIso.inv ≫ P.inclusion ≫ compatibleSource.iso.hom =
        Q.inclusion := by
    calc
      supportIso.inv ≫ P.inclusion ≫ compatibleSource.iso.hom =
          supportIso.inv ≫ (P.inclusion ≫ compatibleSource.iso.hom) := by
            exact Eq.symm (Category.assoc _ _ _)
      _ = supportIso.inv ≫ (supportIso.hom ≫ Q.inclusion) := by
            exact congrArg (fun f => supportIso.inv ≫ f) support_comm
      _ = (supportIso.inv ≫ supportIso.hom) ≫ Q.inclusion := by
            exact (Category.assoc supportIso.inv supportIso.hom Q.inclusion).symm
      _ = Q.inclusion := by
            calc
              (supportIso.inv ≫ supportIso.hom) ≫ Q.inclusion =
                  𝟙 _ ≫ Q.inclusion := by
                    exact congrArg (fun f => f ≫ Q.inclusion) supportIso.inv_hom_id
              _ = Q.inclusion := by
                    exact Category.id_comp Q.inclusion
  have inverse_right_support_comm :
      supportIso.inv ≫ P.inclusion =
        Q.inclusion ≫ compatibleSource.iso.inv := by
    calc
      supportIso.inv ≫ P.inclusion =
          (supportIso.inv ≫ P.inclusion) ≫ 𝟙 _ := by
            exact (Category.comp_id (supportIso.inv ≫ P.inclusion)).symm
      _ = (supportIso.inv ≫ P.inclusion) ≫
            compatibleSource.iso.hom ≫ compatibleSource.iso.inv := by
            exact
              congrArg (fun f => (supportIso.inv ≫ P.inclusion) ≫ f)
                compatibleSource.iso.hom_inv_id.symm
      _ = (supportIso.inv ≫ P.inclusion ≫ compatibleSource.iso.hom) ≫
            compatibleSource.iso.inv := by
            exact Category.assoc _ _ _
      _ = Q.inclusion ≫ compatibleSource.iso.inv := by
            exact congrArg (fun f => f ≫ compatibleSource.iso.inv)
              inverse_left_support_comm
  exact inverse_right_support_comm.symm

/-- Symmetry of the isomorphism-over-product relation. -/
theorem supportIsoOverProduct_symm {X Y : Geometry.SmSchemeOver k}
    {P Q : PrimeFiniteCorrespondenceSupport X Y}
    (hPQ : SupportIsoOverProduct P Q) : SupportIsoOverProduct Q P := by
  rcases hPQ with ⟨hcomp, iso, hcomm⟩
  refine ⟨SourceImageSubscheme.IsoOverAmbient.CompatibleOverBaseProductIso.symm hcomp,
    iso.symm, ?_⟩
  exact supportIsoOverProduct_symm_comm_of_witness hcomp iso hcomm

/-- Commutativity of the composite support isomorphism used for transitivity
of `SupportIsoOverProduct`. -/
theorem supportIsoOverProduct_trans_comm_of_witness
    {X Y : Geometry.SmSchemeOver k}
    {P Q R : PrimeFiniteCorrespondenceSupport X Y}
    (compatiblePQ :
      SourceImageSubscheme.IsoOverAmbient.CompatibleOverBaseProductIso
        (Y := Y) P.sourceImage Q.sourceImage)
    (compatibleQR :
      SourceImageSubscheme.IsoOverAmbient.CompatibleOverBaseProductIso
        (Y := Y) Q.sourceImage R.sourceImage)
    (supportIsoPQ : P.support ≅ Q.support)
    (supportIsoQR : Q.support ≅ R.support)
    (support_comm_PQ :
      P.inclusion ≫ compatiblePQ.iso.hom =
        supportIsoPQ.hom ≫ Q.inclusion)
    (support_comm_QR :
      Q.inclusion ≫ compatibleQR.iso.hom =
        supportIsoQR.hom ≫ R.inclusion) :
    P.inclusion ≫ (compatiblePQ.iso ≪≫ compatibleQR.iso).hom =
      (supportIsoPQ ≪≫ supportIsoQR).hom ≫ R.inclusion :=
  calc
    P.inclusion ≫ (compatiblePQ.iso ≪≫ compatibleQR.iso).hom =
        P.inclusion ≫ compatiblePQ.iso.hom ≫ compatibleQR.iso.hom :=
          rfl
    _ = (supportIsoPQ.hom ≫ Q.inclusion) ≫ compatibleQR.iso.hom :=
          congrArg (fun f => f ≫ compatibleQR.iso.hom) support_comm_PQ
    _ = supportIsoPQ.hom ≫ (Q.inclusion ≫ compatibleQR.iso.hom) :=
          Category.assoc supportIsoPQ.hom Q.inclusion compatibleQR.iso.hom
    _ = supportIsoPQ.hom ≫ (supportIsoQR.hom ≫ R.inclusion) :=
          congrArg (fun f => supportIsoPQ.hom ≫ f) support_comm_QR
    _ = (supportIsoPQ ≪≫ supportIsoQR).hom ≫ R.inclusion :=
          rfl

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
  exact
    supportIsoOverProduct_trans_comm_of_witness
      hcompPQ hcompQR isoPQ isoQR hcommPQ hcommQR

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
