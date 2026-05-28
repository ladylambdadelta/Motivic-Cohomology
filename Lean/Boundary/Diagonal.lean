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

namespace SourceIrreducibleComponent

/-- The diagonal graph of a chosen source irreducible component inside
`component ×_k X`, viewed as a represented prime support from `X` to itself.

The current prime-support basis is indexed by a single source irreducible
component, so this is the honest diagonal class available without yet summing
over all components of a reducible source. -/
def diagonalRepresentedPrimeSupport {X : Geometry.SmSchemeOver k}
    (component : SourceIrreducibleComponent X) :
    RepresentedPrimeSupport X X where
  sourceComponent := component
  support := component.carrier.scheme
  isIntegral := component.isIntegral
  finiteOverSourceComponent := 𝟙 component.carrier.scheme
  finite_toSourceComponent := by infer_instance
  surjective_toSourceComponent := by
    intro x
    exact ⟨x, rfl⟩
  toTarget := component.toAmbient
  inclusion := pullback.lift (𝟙 component.carrier.scheme) component.toAmbient (by
    simpa using component.toAmbient_overBase.symm)
  inclusion_fst := by
    simp [overBaseProduct]
  inclusion_snd := by
    simp [overBaseProduct]
  isClosedImmersion := by
    let graphIso :
        pullback (component.toAmbient ≫ X.structMap) X.structMap ≅
          overBaseProduct component.carrier X :=
      pullback.congrHom component.toAmbient_overBase rfl
    let desired : component.carrier.scheme ⟶ overBaseProduct component.carrier X :=
      pullback.lift (𝟙 component.carrier.scheme) component.toAmbient (by
        simpa using component.toAmbient_overBase.symm)
    let graphMap : component.carrier.scheme ⟶
        pullback (component.toAmbient ≫ X.structMap) X.structMap :=
      pullback.lift (𝟙 component.carrier.scheme) component.toAmbient
        (Category.id_comp (component.toAmbient ≫ X.structMap))
    let e : Arrow.mk desired ≅ Arrow.mk graphMap :=
      Arrow.isoMk (Iso.refl _) graphIso.symm (by
        apply pullback.hom_ext
        · simp [desired, graphMap, graphIso, overBaseProduct, component.toAmbient_overBase]
        · simp [desired, graphMap, graphIso, overBaseProduct, component.toAmbient_overBase])
    letI : IsSeparated X.structMap := X.separated
    exact (MorphismProperty.arrow_mk_iso_iff (P := @IsClosedImmersion) e).2 inferInstance

/-- The quotient class of the diagonal graph over a chosen source component. -/
def diagonalPrimeGeom {X : Geometry.SmSchemeOver k}
    (component : SourceIrreducibleComponent X) :
    PrimeFiniteCorrespondenceGeom X X :=
  PrimeFiniteCorrespondenceGeom.ofRepresented
    (diagonalRepresentedPrimeSupport component)

/-- The singleton finite correspondence supported on the diagonal graph of a
chosen source irreducible component. -/
def diagonalFiniteCorrespondence {X : Geometry.SmSchemeOver k}
    (component : SourceIrreducibleComponent X) :
    FiniteCorrespondence X X :=
  Finsupp.single (diagonalPrimeGeom component) 1

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
  let compat :=
    SourceIrreducibleComponent.IsoOverAmbient.CompatibleOverBaseProductIso.ofIsoOverAmbient
      (Y := X) h
  refine ⟨compat, h.iso, ?_⟩
  change (diagonalRepresentedPrimeSupport C).inclusion ≫ compat.iso.hom =
    h.iso.hom ≫ (diagonalRepresentedPrimeSupport D).inclusion
  apply pullback.hom_ext
  · calc
      (diagonalRepresentedPrimeSupport C).inclusion ≫ compat.iso.hom ≫ overBaseProduct.fst D.carrier X
          = (diagonalRepresentedPrimeSupport C).inclusion ≫
              overBaseProduct.fst C.carrier X ≫ h.iso.hom := by
                simpa [compat,
                  SourceIrreducibleComponent.IsoOverAmbient.CompatibleOverBaseProductIso.ofIsoOverAmbient,
                  Category.assoc] using
                  congrArg (fun f => (diagonalRepresentedPrimeSupport C).inclusion ≫ f)
                    (SourceIrreducibleComponent.IsoOverAmbient.overBaseProductIso_hom_fst h)
      _ = (diagonalRepresentedPrimeSupport C).finiteOverSourceComponent ≫ h.iso.hom := by
            simpa [Category.assoc] using
              congrArg (fun f => f ≫ h.iso.hom)
                (diagonalRepresentedPrimeSupport C).inclusion_fst
      _ = h.iso.hom := by
            simp [diagonalRepresentedPrimeSupport]
      _ = h.iso.hom ≫ (diagonalRepresentedPrimeSupport D).finiteOverSourceComponent := by
            simp [diagonalRepresentedPrimeSupport]
      _ = h.iso.hom ≫ (diagonalRepresentedPrimeSupport D).inclusion ≫ overBaseProduct.fst D.carrier X := by
            simpa [Category.assoc] using
              congrArg (fun f => h.iso.hom ≫ f)
                (diagonalRepresentedPrimeSupport D).inclusion_fst.symm
  · calc
      (diagonalRepresentedPrimeSupport C).inclusion ≫ compat.iso.hom ≫ overBaseProduct.snd D.carrier X
          = (diagonalRepresentedPrimeSupport C).inclusion ≫ overBaseProduct.snd C.carrier X := by
                simpa [compat,
                  SourceIrreducibleComponent.IsoOverAmbient.CompatibleOverBaseProductIso.ofIsoOverAmbient,
                  Category.assoc] using
                  congrArg (fun f => (diagonalRepresentedPrimeSupport C).inclusion ≫ f)
                    (SourceIrreducibleComponent.IsoOverAmbient.overBaseProductIso_hom_snd h)
      _ = (diagonalRepresentedPrimeSupport C).toTarget := by
            exact (diagonalRepresentedPrimeSupport C).inclusion_snd
      _ = C.toAmbient := by simp [diagonalRepresentedPrimeSupport]
      _ = h.iso.hom ≫ D.toAmbient := by rw [h.hom_toAmbient]
      _ = h.iso.hom ≫ (diagonalRepresentedPrimeSupport D).toTarget := by
            simp [diagonalRepresentedPrimeSupport]
      _ = h.iso.hom ≫ (diagonalRepresentedPrimeSupport D).inclusion ≫ overBaseProduct.snd D.carrier X := by
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
          SourceIrreducibleComponent.IsoOverAmbient.CompatibleOverBaseProductIso
            (Y := X) C D)
        (_iso : C.carrier.scheme ≅ D.carrier.scheme),
        (diagonalRepresentedPrimeSupport C).inclusion ≫ compatibleSourceComponent.iso.hom =
          _iso.hom ≫ (diagonalRepresentedPrimeSupport D).inclusion := by
    simpa [PrimeFiniteCorrespondenceSupport.PrimeSupportEquivalent,
      PrimeFiniteCorrespondenceSupport.SupportIsoOverProduct,
      diagonalRepresentedPrimeSupport] using h
  let compatibleSourceComponent := Classical.choose h'
  exact compatibleSourceComponent.sourceIso

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
