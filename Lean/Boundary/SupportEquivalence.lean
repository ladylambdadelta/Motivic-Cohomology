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
components are isomorphic over the ambient source scheme and there is an
isomorphism of support schemes compatible with the embeddings into the induced
isomorphic fiber products. -/
def SupportIsoOverProduct {X Y : Geometry.SmSchemeOver k}
    (P Q : PrimeFiniteCorrespondenceSupport X Y) : Prop :=
  ∃ (compatible_source_component :
        SourceIrreducibleComponent.IsoOverAmbient.CompatibleOverBaseProductIso
          (Y := Y) P.sourceComponent Q.sourceComponent)
    (iso : P.support ≅ Q.support),
      P.inclusion ≫ compatible_source_component.iso.hom =
        iso.hom ≫ Q.inclusion

/-- Candidate geometric equivalence relation on represented prime supports. -/
abbrev PrimeSupportEquivalent {X Y : Geometry.SmSchemeOver k}
    (P Q : PrimeFiniteCorrespondenceSupport X Y) : Prop :=
  SupportIsoOverProduct P Q

/-- Reflexivity of the isomorphism-over-product relation. -/
theorem supportIsoOverProduct_refl {X Y : Geometry.SmSchemeOver k}
    (P : PrimeFiniteCorrespondenceSupport X Y) : SupportIsoOverProduct P P := by
  refine ⟨SourceIrreducibleComponent.IsoOverAmbient.CompatibleOverBaseProductIso.refl
      (Y := Y) P.sourceComponent,
    Iso.refl P.support, ?_⟩
  simp [SourceIrreducibleComponent.IsoOverAmbient.CompatibleOverBaseProductIso.refl]

/-- Symmetry of the isomorphism-over-product relation. -/
theorem supportIsoOverProduct_symm {X Y : Geometry.SmSchemeOver k}
    {P Q : PrimeFiniteCorrespondenceSupport X Y}
    (hPQ : SupportIsoOverProduct P Q) : SupportIsoOverProduct Q P := by
  rcases hPQ with ⟨hcomp, iso, hcomm⟩
  refine ⟨SourceIrreducibleComponent.IsoOverAmbient.CompatibleOverBaseProductIso.symm hcomp,
    iso.symm, ?_⟩
  have hleft : iso.inv ≫ P.inclusion ≫ hcomp.iso.hom = Q.inclusion := by
    simpa [Category.assoc] using congrArg (fun f => iso.inv ≫ f) hcomm
  have hright : iso.inv ≫ P.inclusion = Q.inclusion ≫ hcomp.iso.inv := by
    simpa [Category.assoc] using
      congrArg (fun f => f ≫ hcomp.iso.inv) hleft
  simpa [SourceIrreducibleComponent.IsoOverAmbient.CompatibleOverBaseProductIso.symm,
    Category.assoc] using hright.symm

/-- Transitivity of the isomorphism-over-product relation. -/
theorem supportIsoOverProduct_trans {X Y : Geometry.SmSchemeOver k}
    {P Q R : PrimeFiniteCorrespondenceSupport X Y}
    (hPQ : SupportIsoOverProduct P Q) (hQR : SupportIsoOverProduct Q R) :
    SupportIsoOverProduct P R := by
  rcases hPQ with ⟨hcompPQ, isoPQ, hcommPQ⟩
  rcases hQR with ⟨hcompQR, isoQR, hcommQR⟩
  refine ⟨SourceIrreducibleComponent.IsoOverAmbient.CompatibleOverBaseProductIso.trans
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
the same source-component fiber product. -/
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
