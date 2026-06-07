import Boundary.CorrespondenceSums

/-!
# Diagonal Prime Supports

This file packages the diagonal represented-prime support on a chosen source
irreducible component and the resulting quotient-level diagonal classes.
-/

universe u

variable {k : Type u} [Field k] [PerfectField k]

open AlgebraicGeometry CategoryTheory Limits

namespace Boundary

noncomputable section

namespace SourceImageSubscheme

/-- The diagonal graph of an integral closed source image inside
`sourceImage ×_k X`, viewed as a represented prime support from `X` to itself.

This is the root diagonal class compatible with the source-image basis for
represented prime supports. -/
def diagonalRepresentedPrimeSupport {X : Geometry.SmSchemeOver k}
    (sourceImage : SourceImageSubscheme (k := k) X) :
    RepresentedPrimeSupport X X where
  sourceImage := sourceImage
  support := sourceImage.carrier.scheme
  isIntegral := sourceImage.isIntegral
  finiteOverSourceComponent := 𝟙 sourceImage.carrier.scheme
  finite_toSourceComponent := by infer_instance
  surjective_toSourceComponent := by
    intro x
    exact ⟨x, rfl⟩
  toTarget := sourceImage.toAmbient
  inclusion := pullback.lift (𝟙 sourceImage.carrier.scheme) sourceImage.toAmbient (by
    exact sourceImage.toAmbient_overBase.symm)
  inclusion_fst := by
    simp [sourceOverBaseProduct]
  inclusion_snd := by
    simp [sourceOverBaseProduct]
  isClosedImmersion := by
    let graphIso :
        pullback (sourceImage.toAmbient ≫ X.structMap) X.structMap ≅
          sourceOverBaseProduct sourceImage.carrier X :=
      pullback.congrHom sourceImage.toAmbient_overBase rfl
    let desired : sourceImage.carrier.scheme ⟶ sourceOverBaseProduct sourceImage.carrier X :=
      pullback.lift (𝟙 sourceImage.carrier.scheme) sourceImage.toAmbient (by
        exact sourceImage.toAmbient_overBase.symm)
    let graphMap : sourceImage.carrier.scheme ⟶
        pullback (sourceImage.toAmbient ≫ X.structMap) X.structMap :=
      pullback.lift (𝟙 sourceImage.carrier.scheme) sourceImage.toAmbient
        (Category.id_comp (sourceImage.toAmbient ≫ X.structMap))
    let e : Arrow.mk desired ≅ Arrow.mk graphMap :=
      Arrow.isoMk (Iso.refl _) graphIso.symm (by
        apply pullback.hom_ext
        · simp [desired, graphMap, graphIso, sourceOverBaseProduct,
            sourceImage.toAmbient_overBase]
        · simp [desired, graphMap, graphIso, sourceOverBaseProduct,
            sourceImage.toAmbient_overBase])
    letI : IsSeparated X.structMap := X.separated
    exact (MorphismProperty.arrow_mk_iso_iff (P := @IsClosedImmersion) e).2 inferInstance

@[simp] theorem diagonalRepresentedPrimeSupport_sourceComponent
    {X : Geometry.SmSchemeOver k}
    (sourceImage : SourceImageSubscheme (k := k) X) :
    (diagonalRepresentedPrimeSupport sourceImage).sourceComponent = sourceImage := rfl

@[simp] theorem diagonalRepresentedPrimeSupport_toSourceImage
    {X : Geometry.SmSchemeOver k}
    (sourceImage : SourceImageSubscheme (k := k) X) :
    (diagonalRepresentedPrimeSupport sourceImage).toSourceImage =
      𝟙 sourceImage.carrier.scheme := rfl

@[simp] theorem diagonalRepresentedPrimeSupport_inclusion_fst
    {X : Geometry.SmSchemeOver k}
    (sourceImage : SourceImageSubscheme (k := k) X) :
    (diagonalRepresentedPrimeSupport sourceImage).inclusion ≫
        sourceOverBaseProduct.fst (k := k) sourceImage.carrier X =
      𝟙 sourceImage.carrier.scheme := by
  exact (diagonalRepresentedPrimeSupport sourceImage).inclusion_fst

@[simp] theorem diagonalRepresentedPrimeSupport_inclusion_snd
    {X : Geometry.SmSchemeOver k}
    (sourceImage : SourceImageSubscheme (k := k) X) :
    (diagonalRepresentedPrimeSupport sourceImage).inclusion ≫
        sourceOverBaseProduct.snd (k := k) sourceImage.carrier X =
      sourceImage.toAmbient := by
  exact (diagonalRepresentedPrimeSupport sourceImage).inclusion_snd

@[simp] theorem diagonalRepresentedPrimeSupport_inclusion_fst_sourceComponent
    {X : Geometry.SmSchemeOver k}
    (sourceImage : SourceImageSubscheme (k := k) X) :
    (diagonalRepresentedPrimeSupport sourceImage).inclusion ≫
        Limits.pullback.fst
          (diagonalRepresentedPrimeSupport sourceImage).sourceComponent.carrier.structMap
          X.structMap =
      𝟙 sourceImage.carrier.scheme := by
  exact diagonalRepresentedPrimeSupport_inclusion_fst sourceImage

@[simp] theorem diagonalRepresentedPrimeSupport_inclusion_snd_sourceComponent
    {X : Geometry.SmSchemeOver k}
    (sourceImage : SourceImageSubscheme (k := k) X) :
    (diagonalRepresentedPrimeSupport sourceImage).inclusion ≫
        Limits.pullback.snd
          (diagonalRepresentedPrimeSupport sourceImage).sourceComponent.carrier.structMap
          X.structMap =
      sourceImage.toAmbient := by
  exact diagonalRepresentedPrimeSupport_inclusion_snd sourceImage

/-- The quotient class of the diagonal graph over a source image. -/
def diagonalPrimeGeom {X : Geometry.SmSchemeOver k}
    (sourceImage : SourceImageSubscheme (k := k) X) :
    PrimeFiniteCorrespondenceGeom X X :=
  PrimeFiniteCorrespondenceGeom.ofRepresented
    (diagonalRepresentedPrimeSupport sourceImage)

/-- The singleton finite correspondence supported on the diagonal graph of a
source image. -/
def diagonalFiniteCorrespondence {X : Geometry.SmSchemeOver k}
    (sourceImage : SourceImageSubscheme (k := k) X) :
    FiniteCorrespondence X X :=
  Finsupp.single (diagonalPrimeGeom sourceImage) 1

/-- A represented prime support whose support maps isomorphically to its
source image and whose target map is the ambient source map is equivalent to
the diagonal represented support over that source image. -/
theorem primeSupportEquivalent_diagonal_of_isIso_toSourceImage_of_target_eq
    {X : Geometry.SmSchemeOver k}
    (P : RepresentedPrimeSupport X X)
    [IsIso P.finiteOverSourceComponent]
    (hTarget : P.toTarget = P.toAmbientSource) :
    PrimeFiniteCorrespondenceSupport.PrimeSupportEquivalent P
      (diagonalRepresentedPrimeSupport P.sourceImage) := by
  let compat :=
    SourceImageSubscheme.IsoOverAmbient.CompatibleOverBaseProductIso.refl
      (Y := X) P.sourceImage
  refine ⟨compat, asIso P.finiteOverSourceComponent, ?_⟩
  change P.inclusion ≫ compat.iso.hom =
    (asIso P.finiteOverSourceComponent).hom ≫
      (diagonalRepresentedPrimeSupport P.sourceImage).inclusion
  apply pullback.hom_ext
  · calc
      (P.inclusion ≫ compat.iso.hom) ≫
          sourceOverBaseProduct.fst (k := k) P.sourceImage.carrier X =
        P.inclusion ≫ sourceOverBaseProduct.fst (k := k) P.sourceImage.carrier X := by
          simp [compat,
            SourceImageSubscheme.IsoOverAmbient.CompatibleOverBaseProductIso.refl,
            Category.assoc]
      _ = P.finiteOverSourceComponent := P.inclusion_fst
      _ = ((asIso P.finiteOverSourceComponent).hom ≫
            (diagonalRepresentedPrimeSupport P.sourceImage).inclusion) ≫
          sourceOverBaseProduct.fst (k := k) P.sourceImage.carrier X := by
          simp [PrimeFiniteCorrespondenceSupport.toSourceImage, Category.assoc]
  · calc
      (P.inclusion ≫ compat.iso.hom) ≫
          sourceOverBaseProduct.snd (k := k) P.sourceImage.carrier X =
        P.inclusion ≫ sourceOverBaseProduct.snd (k := k) P.sourceImage.carrier X := by
          simp [compat,
            SourceImageSubscheme.IsoOverAmbient.CompatibleOverBaseProductIso.refl,
            Category.assoc]
      _ = P.toTarget := P.inclusion_snd
      _ = P.toAmbientSource := hTarget
      _ = P.finiteOverSourceComponent ≫ P.sourceImage.toAmbient := rfl
      _ = ((asIso P.finiteOverSourceComponent).hom ≫
            (diagonalRepresentedPrimeSupport P.sourceImage).inclusion) ≫
          sourceOverBaseProduct.snd (k := k) P.sourceImage.carrier X := by
          simp [PrimeFiniteCorrespondenceSupport.toSourceImage,
            PrimeFiniteCorrespondenceSupport.toAmbientSource, Category.assoc]

/-- Singleton finite-correspondence form of
`primeSupportEquivalent_diagonal_of_isIso_toSourceImage_of_target_eq`. -/
theorem single_eq_diagonal_of_isIso_toSourceImage_of_target_eq
    {X : Geometry.SmSchemeOver k}
    (P : RepresentedPrimeSupport X X)
    [IsIso P.finiteOverSourceComponent]
    (hTarget : P.toTarget = P.toAmbientSource) :
    Finsupp.single (PrimeFiniteCorrespondenceGeom.ofRepresented P) 1 =
      diagonalFiniteCorrespondence P.sourceImage := by
  change Finsupp.single (PrimeFiniteCorrespondenceGeom.ofRepresented P) (1 : ℤ) =
    Finsupp.single
      (PrimeFiniteCorrespondenceGeom.ofRepresented
        (diagonalRepresentedPrimeSupport P.sourceImage)) (1 : ℤ)
  rw [PrimeFiniteCorrespondenceGeom.eq_of_primeSupportEquivalent
    (primeSupportEquivalent_diagonal_of_isIso_toSourceImage_of_target_eq P hTarget)]

end SourceImageSubscheme

namespace PrimeFiniteCorrespondenceSupport

/-- The diagonal represented prime support on the actual source image of `P`. -/
abbrev sourceDiagonal {X Y : Geometry.SmSchemeOver k}
    (P : RepresentedPrimeSupport X Y) :
    RepresentedPrimeSupport X X :=
  SourceImageSubscheme.diagonalRepresentedPrimeSupport P.sourceImage

/-- The quotient diagonal class on the actual source image of `P`. -/
abbrev sourceDiagonalGeom {X Y : Geometry.SmSchemeOver k}
    (P : RepresentedPrimeSupport X Y) :
    PrimeFiniteCorrespondenceGeom X X :=
  SourceImageSubscheme.diagonalPrimeGeom P.sourceImage

/-- The singleton diagonal correspondence on the actual source image of `P`. -/
abbrev sourceDiagonalFiniteCorrespondence {X Y : Geometry.SmSchemeOver k}
    (P : RepresentedPrimeSupport X Y) :
    FiniteCorrespondence X X :=
  SourceImageSubscheme.diagonalFiniteCorrespondence P.sourceImage

end PrimeFiniteCorrespondenceSupport

namespace SourceIrreducibleComponent

/-- The diagonal graph of a chosen source irreducible component inside
`component ×_k X`, viewed as a represented prime support from `X` to itself.

The current prime-support basis is indexed by a single source irreducible
component, so this is the honest diagonal class available without yet summing
over all components of a reducible source. -/
def diagonalRepresentedPrimeSupport {X : Geometry.SmSchemeOver k}
    (component : SourceIrreducibleComponent X) :
    RepresentedPrimeSupport X X :=
  SourceImageSubscheme.diagonalRepresentedPrimeSupport component.toSourceImageSubscheme

@[simp] theorem diagonalRepresentedPrimeSupport_sourceComponent
    {X : Geometry.SmSchemeOver k}
    (component : SourceIrreducibleComponent X) :
    (diagonalRepresentedPrimeSupport component).sourceComponent =
      component.toSourceImageSubscheme := rfl

@[simp] theorem diagonalRepresentedPrimeSupport_toSourceImage
    {X : Geometry.SmSchemeOver k}
    (component : SourceIrreducibleComponent X) :
    (diagonalRepresentedPrimeSupport component).toSourceImage =
      𝟙 component.carrier.scheme := rfl

@[simp] theorem diagonalRepresentedPrimeSupport_inclusion_fst
    {X : Geometry.SmSchemeOver k}
    (component : SourceIrreducibleComponent X) :
    (diagonalRepresentedPrimeSupport component).inclusion ≫
        sourceOverBaseProduct.fst (k := k) component.toSourceImageSubscheme.carrier X =
      𝟙 component.carrier.scheme := by
  exact SourceImageSubscheme.diagonalRepresentedPrimeSupport_inclusion_fst
    component.toSourceImageSubscheme

@[simp] theorem diagonalRepresentedPrimeSupport_inclusion_snd
    {X : Geometry.SmSchemeOver k}
    (component : SourceIrreducibleComponent X) :
    (diagonalRepresentedPrimeSupport component).inclusion ≫
        sourceOverBaseProduct.snd (k := k) component.toSourceImageSubscheme.carrier X =
      component.toAmbient := by
  exact SourceImageSubscheme.diagonalRepresentedPrimeSupport_inclusion_snd
    component.toSourceImageSubscheme

@[simp] theorem diagonalRepresentedPrimeSupport_inclusion_fst_sourceComponent
    {X : Geometry.SmSchemeOver k}
    (component : SourceIrreducibleComponent X) :
    (diagonalRepresentedPrimeSupport component).inclusion ≫
        Limits.pullback.fst
          (diagonalRepresentedPrimeSupport component).sourceComponent.carrier.structMap
          X.structMap =
      𝟙 component.carrier.scheme := by
  exact SourceImageSubscheme.diagonalRepresentedPrimeSupport_inclusion_fst_sourceComponent
    component.toSourceImageSubscheme

@[simp] theorem diagonalRepresentedPrimeSupport_inclusion_snd_sourceComponent
    {X : Geometry.SmSchemeOver k}
    (component : SourceIrreducibleComponent X) :
    (diagonalRepresentedPrimeSupport component).inclusion ≫
        Limits.pullback.snd
          (diagonalRepresentedPrimeSupport component).sourceComponent.carrier.structMap
          X.structMap =
      component.toAmbient := by
  exact SourceImageSubscheme.diagonalRepresentedPrimeSupport_inclusion_snd_sourceComponent
    component.toSourceImageSubscheme

/-- The quotient class of the diagonal graph over a chosen source component. -/
def diagonalPrimeGeom {X : Geometry.SmSchemeOver k}
    (component : SourceIrreducibleComponent X) :
    PrimeFiniteCorrespondenceGeom X X :=
  SourceImageSubscheme.diagonalPrimeGeom component.toSourceImageSubscheme

/-- The singleton finite correspondence supported on the diagonal graph of a
chosen source irreducible component. -/
def diagonalFiniteCorrespondence {X : Geometry.SmSchemeOver k}
    (component : SourceIrreducibleComponent X) :
    FiniteCorrespondence X X :=
  SourceImageSubscheme.diagonalFiniteCorrespondence component.toSourceImageSubscheme

/-- Any represented prime support equivalent to the diagonal graph over a chosen
source component defines the same singleton quotient-indexed correspondence. -/
theorem single_eq_diagonal_of_primeSupportEquivalent {X : Geometry.SmSchemeOver k}
    (component : SourceIrreducibleComponent X)
    {P : RepresentedPrimeSupport X X}
    (h : PrimeFiniteCorrespondenceSupport.PrimeSupportEquivalent P
      (diagonalRepresentedPrimeSupport component)) :
    Finsupp.single (PrimeFiniteCorrespondenceGeom.ofRepresented P) 1 =
      diagonalFiniteCorrespondence component := by
  change Finsupp.single (PrimeFiniteCorrespondenceGeom.ofRepresented P) (1 : ℤ) =
    Finsupp.single
      (PrimeFiniteCorrespondenceGeom.ofRepresented
        (diagonalRepresentedPrimeSupport component)) (1 : ℤ)
  rw [PrimeFiniteCorrespondenceGeom.eq_of_primeSupportEquivalent h]

/-- Diagonal represented supports over source components that are isomorphic
over the ambient source define equivalent prime supports. -/
theorem diagonal_primeSupportEquivalent_of_isoOverAmbient
    {X : Geometry.SmSchemeOver k} {C D : SourceIrreducibleComponent X}
    (h : SourceIrreducibleComponent.IsoOverAmbient C D) :
    PrimeFiniteCorrespondenceSupport.PrimeSupportEquivalent
      (diagonalRepresentedPrimeSupport C)
      (diagonalRepresentedPrimeSupport D) := by
  let sourceIso : SourceImageSubscheme.IsoOverAmbient
      C.toSourceImageSubscheme D.toSourceImageSubscheme :=
    { iso := h.iso
      hom_toAmbient := h.hom_toAmbient }
  let compat :=
    SourceImageSubscheme.IsoOverAmbient.CompatibleOverBaseProductIso.ofIsoOverAmbient
      (Y := X) sourceIso
  refine ⟨compat, h.iso, ?_⟩
  change (diagonalRepresentedPrimeSupport C).inclusion ≫ compat.iso.hom =
    h.iso.hom ≫ (diagonalRepresentedPrimeSupport D).inclusion
  apply pullback.hom_ext
  · calc
      (diagonalRepresentedPrimeSupport C).inclusion ≫ compat.iso.hom ≫
          sourceOverBaseProduct.fst (k := k) D.toSourceImageSubscheme.carrier X
          = (diagonalRepresentedPrimeSupport C).inclusion ≫
              sourceOverBaseProduct.fst (k := k) C.toSourceImageSubscheme.carrier X ≫ h.iso.hom := by
                simpa [compat,
                  SourceImageSubscheme.IsoOverAmbient.CompatibleOverBaseProductIso.ofIsoOverAmbient,
                  Category.assoc] using
                  congrArg (fun f => (diagonalRepresentedPrimeSupport C).inclusion ≫ f)
                    (SourceImageSubscheme.IsoOverAmbient.overBaseProductIso_hom_fst
                      (Y := X) sourceIso)
      _ = (diagonalRepresentedPrimeSupport C).finiteOverSourceComponent ≫ h.iso.hom := by
            simpa [Category.assoc] using
              congrArg (fun f => f ≫ h.iso.hom)
                (diagonalRepresentedPrimeSupport C).inclusion_fst
      _ = h.iso.hom := by
            change 𝟙 C.carrier.scheme ≫ h.iso.hom = h.iso.hom
            simp
      _ = h.iso.hom ≫ (diagonalRepresentedPrimeSupport D).finiteOverSourceComponent := by
            change h.iso.hom = h.iso.hom ≫ 𝟙 D.carrier.scheme
            simp
      _ = h.iso.hom ≫ (diagonalRepresentedPrimeSupport D).inclusion ≫
        sourceOverBaseProduct.fst (k := k) D.toSourceImageSubscheme.carrier X := by
            simpa [Category.assoc] using
              congrArg (fun f => h.iso.hom ≫ f)
                (diagonalRepresentedPrimeSupport D).inclusion_fst.symm
  · calc
      (diagonalRepresentedPrimeSupport C).inclusion ≫ compat.iso.hom ≫
          sourceOverBaseProduct.snd (k := k) D.toSourceImageSubscheme.carrier X
          = (diagonalRepresentedPrimeSupport C).inclusion ≫
          sourceOverBaseProduct.snd (k := k) C.toSourceImageSubscheme.carrier X := by
                have hsnd :=
                  SourceImageSubscheme.IsoOverAmbient.overBaseProductIso_hom_snd
                    (Y := X) sourceIso
                simpa [compat,
                  SourceImageSubscheme.IsoOverAmbient.CompatibleOverBaseProductIso.ofIsoOverAmbient,
                  Category.assoc] using
                  congrArg (fun f => (diagonalRepresentedPrimeSupport C).inclusion ≫ f)
                    hsnd
      _ = (diagonalRepresentedPrimeSupport C).toTarget := by
            exact (diagonalRepresentedPrimeSupport C).inclusion_snd
      _ = C.toAmbient := by
            change C.toSourceImageSubscheme.toAmbient = C.toAmbient
            rfl
      _ = h.iso.hom ≫ D.toAmbient := by rw [h.hom_toAmbient]
      _ = h.iso.hom ≫ (diagonalRepresentedPrimeSupport D).toTarget := by
            change h.iso.hom ≫ D.toAmbient =
              h.iso.hom ≫ D.toSourceImageSubscheme.toAmbient
            rfl
      _ = h.iso.hom ≫ (diagonalRepresentedPrimeSupport D).inclusion ≫
        sourceOverBaseProduct.snd (k := k) D.toSourceImageSubscheme.carrier X := by
            simpa [Category.assoc] using
              congrArg (fun f => h.iso.hom ≫ f)
                (diagonalRepresentedPrimeSupport D).inclusion_snd.symm

/-- The diagonal geometric class depends only on the source-component class over
the ambient source. -/
theorem diagonalPrimeGeom_eq_of_isoOverAmbient
    {X : Geometry.SmSchemeOver k} {C D : SourceIrreducibleComponent X}
    (h : SourceIrreducibleComponent.IsoOverAmbient C D) :
    diagonalPrimeGeom C = diagonalPrimeGeom D := by
  exact PrimeFiniteCorrespondenceGeom.eq_of_primeSupportEquivalent
    (diagonal_primeSupportEquivalent_of_isoOverAmbient h)

/-- For diagonal represented prime supports, geometric equivalence already
remembers the source-component isomorphism over the ambient source. -/
def isoOverAmbient_of_diagonal_primeSupportEquivalent
    {X : Geometry.SmSchemeOver k} {C D : SourceIrreducibleComponent X}
    (h : PrimeFiniteCorrespondenceSupport.PrimeSupportEquivalent
      (diagonalRepresentedPrimeSupport C)
      (diagonalRepresentedPrimeSupport D)) :
    SourceIrreducibleComponent.IsoOverAmbient C D := by
  have h' :
      ∃ (compatibleSourceComponent :
          SourceImageSubscheme.IsoOverAmbient.CompatibleOverBaseProductIso
            (Y := X) C.toSourceImageSubscheme D.toSourceImageSubscheme)
        (supportIso : C.carrier.scheme ≅ D.carrier.scheme),
        (diagonalRepresentedPrimeSupport C).inclusion ≫ compatibleSourceComponent.iso.hom =
          supportIso.hom ≫ (diagonalRepresentedPrimeSupport D).inclusion := by
    simpa [PrimeFiniteCorrespondenceSupport.PrimeSupportEquivalent,
      PrimeFiniteCorrespondenceSupport.SupportIsoOverProduct,
      diagonalRepresentedPrimeSupport] using h
  let compatibleSourceComponent := Classical.choose h'
  exact
    { iso := compatibleSourceComponent.sourceIso.iso
      hom_toAmbient := compatibleSourceComponent.sourceIso.hom_toAmbient }

/-- Equality of diagonal geometric classes forces the corresponding source
components to be isomorphic over the ambient source. -/
def isoOverAmbient_of_diagonalPrimeGeom_eq
    {X : Geometry.SmSchemeOver k} {C D : SourceIrreducibleComponent X}
    (h : diagonalPrimeGeom C = diagonalPrimeGeom D) :
    SourceIrreducibleComponent.IsoOverAmbient C D := by
  exact isoOverAmbient_of_diagonal_primeSupportEquivalent (Quotient.exact h)

/-- The singleton diagonal finite correspondence depends only on the
source-component class over the ambient source. -/
theorem diagonalFiniteCorrespondence_eq_of_isoOverAmbient
    {X : Geometry.SmSchemeOver k} {C D : SourceIrreducibleComponent X}
    (h : SourceIrreducibleComponent.IsoOverAmbient C D) :
    diagonalFiniteCorrespondence C = diagonalFiniteCorrespondence D := by
  change Finsupp.single (diagonalPrimeGeom C) (1 : ℤ) =
    Finsupp.single (diagonalPrimeGeom D) (1 : ℤ)
  rw [diagonalPrimeGeom_eq_of_isoOverAmbient h]

end SourceIrreducibleComponent

end

end Boundary
