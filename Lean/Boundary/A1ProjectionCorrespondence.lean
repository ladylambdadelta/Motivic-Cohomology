import Boundary.A1AffineLine
/-!
This file was split out of `Boundary.A1Geometry`; declarations remain in
namespace `Boundary` under their mathematical owner layer.
-/

universe u

open CategoryTheory
open CategoryTheory.Limits
open Opposite
open Polynomial
open AlgebraicGeometry
open AlgebraicGeometry.Scheme
open Geometry

namespace Boundary

noncomputable section

variable {k : Type u} [Field k] [PerfectField k]
def projectionTransferToBaseGraphData (X : Geometry.SmSchemeOver k) :
    Geometry.MorphismGraphTransferObligationQ (projectionToBase X) :=
  Geometry.morphismGraphTransferObligation (projectionToBase X)

/-- The graph projection for `X ×_k A1_k ⟶ X` is finite. -/
theorem projectionToBase_graphProjectionFinite (X : Geometry.SmSchemeOver k) :
    IsFinite
      (Geometry.ordinaryMorphismGraphMap (projectionToBase X) ≫
        overBaseProduct.fst (productWithA1 X) X) := by
  exact Geometry.ordinaryMorphismGraphProjectionFinite (projectionToBase X)

/-- The componentwise graph of the projection `X ×_k A1_k ⟶ X` as a represented
prime support. -/
def projectionToBase_graphPrimeSupport (X : Geometry.SmSchemeOver k)
    (component : SourceIrreducibleComponent (productWithA1 X)) :
    PrimeFiniteCorrespondenceSupport (productWithA1 X) X :=
  Geometry.ordinaryMorphismGraphPrimeSupport component (projectionToBase X)

/-- The quotient geometric class of the componentwise graph of
`X ×_k A1_k ⟶ X`. -/
def projectionToBase_graphPrimeGeom (X : Geometry.SmSchemeOver k)
    (component : SourceIrreducibleComponent (productWithA1 X)) :
    PrimeFiniteCorrespondenceGeom (productWithA1 X) X :=
  PrimeFiniteCorrespondenceGeom.ofRepresented
    (projectionToBase_graphPrimeSupport X component)

/-- Componentwise graph prime supports for source components that are
isomorphic over the ambient source define equivalent represented supports. -/
theorem projectionToBase_graphPrimeSupportEquivalent_of_isoOverAmbient
    (X : Geometry.SmSchemeOver k)
    {C D : SourceIrreducibleComponent (productWithA1 X)}
    (h : SourceIrreducibleComponent.IsoOverAmbient C D) :
    PrimeFiniteCorrespondenceSupport.PrimeSupportEquivalent
      (projectionToBase_graphPrimeSupport X C)
      (projectionToBase_graphPrimeSupport X D) := by
  let sourceIso : SourceImageSubscheme.IsoOverAmbient
      C.toSourceImageSubscheme D.toSourceImageSubscheme :=
    { iso := h.iso
      hom_toAmbient := h.hom_toAmbient }
  let compat :=
    SourceImageSubscheme.IsoOverAmbient.CompatibleOverBaseProductIso.ofIsoOverAmbient
      (Y := X) sourceIso
  refine ⟨compat, h.iso, ?_⟩
  change (projectionToBase_graphPrimeSupport X C).inclusion ≫ compat.iso.hom =
    h.iso.hom ≫ (projectionToBase_graphPrimeSupport X D).inclusion
  apply Limits.pullback.hom_ext
  · calc
      (projectionToBase_graphPrimeSupport X C).inclusion ≫ compat.iso.hom ≫
          sourceOverBaseProduct.fst (k := k) D.toSourceImageSubscheme.carrier X
          = (projectionToBase_graphPrimeSupport X C).inclusion ≫
              sourceOverBaseProduct.fst (k := k) C.toSourceImageSubscheme.carrier X ≫ h.iso.hom := by
                simpa [compat,
                  SourceImageSubscheme.IsoOverAmbient.CompatibleOverBaseProductIso.ofIsoOverAmbient,
                  Category.assoc] using
                  congrArg (fun f => (projectionToBase_graphPrimeSupport X C).inclusion ≫ f)
                    (SourceImageSubscheme.IsoOverAmbient.overBaseProductIso_hom_fst
                      (Y := X) sourceIso)
      _ = (projectionToBase_graphPrimeSupport X C).finiteOverSourceComponent ≫ h.iso.hom := by
            simpa [Category.assoc] using
              congrArg (fun f => f ≫ h.iso.hom)
                (projectionToBase_graphPrimeSupport X C).inclusion_fst
      _ = h.iso.hom := by
            change ((Geometry.ordinaryMorphismGraphMap
              (Geometry.ordinaryMorphismOnSourceComponent C (projectionToBase X)) ≫
                sourceOverBaseProduct.fst (k := k) C.toSourceImageSubscheme.carrier X) ≫
                  h.iso.hom = h.iso.hom)
            simpa [Category.assoc] using
              congrArg (fun f => f ≫ h.iso.hom)
                (Geometry.ordinaryMorphismGraphMap_fst
                  (Geometry.ordinaryMorphismOnSourceComponent C (projectionToBase X)))
      _ = h.iso.hom ≫ (projectionToBase_graphPrimeSupport X D).finiteOverSourceComponent := by
            change h.iso.hom = h.iso.hom ≫
              (Geometry.ordinaryMorphismGraphMap
                (Geometry.ordinaryMorphismOnSourceComponent D (projectionToBase X)) ≫
                  sourceOverBaseProduct.fst (k := k) D.toSourceImageSubscheme.carrier X)
            simpa [Category.assoc] using
              congrArg (fun f => h.iso.hom ≫ f)
                (Geometry.ordinaryMorphismGraphMap_fst
                  (Geometry.ordinaryMorphismOnSourceComponent D (projectionToBase X))).symm
      _ = h.iso.hom ≫ (projectionToBase_graphPrimeSupport X D).inclusion ≫
            sourceOverBaseProduct.fst (k := k) D.toSourceImageSubscheme.carrier X := by
            simpa [Category.assoc] using
              congrArg (fun f => h.iso.hom ≫ f)
                (projectionToBase_graphPrimeSupport X D).inclusion_fst.symm
  · calc
      (projectionToBase_graphPrimeSupport X C).inclusion ≫ compat.iso.hom ≫
          sourceOverBaseProduct.snd (k := k) D.toSourceImageSubscheme.carrier X
          = (projectionToBase_graphPrimeSupport X C).inclusion ≫
              sourceOverBaseProduct.snd (k := k) C.toSourceImageSubscheme.carrier X := by
                simpa [compat,
                  SourceImageSubscheme.IsoOverAmbient.CompatibleOverBaseProductIso.ofIsoOverAmbient,
                  Category.assoc] using
                  congrArg (fun f => (projectionToBase_graphPrimeSupport X C).inclusion ≫ f)
                    (SourceImageSubscheme.IsoOverAmbient.overBaseProductIso_hom_snd
                      (Y := X) sourceIso)
      _ = (projectionToBase_graphPrimeSupport X C).toTarget := by
            exact (projectionToBase_graphPrimeSupport X C).inclusion_snd
      _ = C.toAmbient ≫ (projectionToBase X).hom := by
        rfl
      _ = (h.iso.hom ≫ D.toAmbient) ≫ (projectionToBase X).hom := by
        rw [← h.hom_toAmbient]
      _ = h.iso.hom ≫ D.toAmbient ≫ (projectionToBase X).hom := by
        simp [Category.assoc]
      _ = h.iso.hom ≫ (projectionToBase_graphPrimeSupport X D).toTarget := by
        rfl
      _ = h.iso.hom ≫ (projectionToBase_graphPrimeSupport X D).inclusion ≫
            sourceOverBaseProduct.snd (k := k) D.toSourceImageSubscheme.carrier X := by
            simpa [Category.assoc] using
              congrArg (fun f => h.iso.hom ≫ f)
                (projectionToBase_graphPrimeSupport X D).inclusion_snd.symm

/-- The graph geometric class depends only on the source-component class over
the ambient source. -/
theorem projectionToBase_graphPrimeGeom_eq_of_isoOverAmbient
    (X : Geometry.SmSchemeOver k)
    {C D : SourceIrreducibleComponent (productWithA1 X)}
    (h : SourceIrreducibleComponent.IsoOverAmbient C D) :
    projectionToBase_graphPrimeGeom X C = projectionToBase_graphPrimeGeom X D := by
  exact PrimeFiniteCorrespondenceGeom.eq_of_primeSupportEquivalent
    (projectionToBase_graphPrimeSupportEquivalent_of_isoOverAmbient X h)

/-- Equivalent componentwise graph prime supports already remember the source
component isomorphism over the ambient source. -/
def isoOverAmbient_of_projectionToBase_graphPrimeSupportEquivalent
    (X : Geometry.SmSchemeOver k)
    {C D : SourceIrreducibleComponent (productWithA1 X)}
    (h : PrimeFiniteCorrespondenceSupport.PrimeSupportEquivalent
      (projectionToBase_graphPrimeSupport X C)
      (projectionToBase_graphPrimeSupport X D)) :
    SourceIrreducibleComponent.IsoOverAmbient C D := by
  have h' :
      ∃ (compatibleSourceComponent :
          SourceImageSubscheme.IsoOverAmbient.CompatibleOverBaseProductIso
            (Y := X) C.toSourceImageSubscheme D.toSourceImageSubscheme)
        (_iso : C.carrier.scheme ≅ D.carrier.scheme),
        (projectionToBase_graphPrimeSupport X C).inclusion ≫ compatibleSourceComponent.iso.hom =
          _iso.hom ≫ (projectionToBase_graphPrimeSupport X D).inclusion := by
    simpa [PrimeFiniteCorrespondenceSupport.PrimeSupportEquivalent,
      PrimeFiniteCorrespondenceSupport.SupportIsoOverProduct] using h
  exact
    { iso := (Classical.choose h').sourceIso.iso
      hom_toAmbient := (Classical.choose h').sourceIso.hom_toAmbient }

/-- Equality of componentwise graph geometric classes forces the corresponding
source components to be isomorphic over the ambient source. -/
def isoOverAmbient_of_projectionToBase_graphPrimeGeom_eq
    (X : Geometry.SmSchemeOver k)
    {C D : SourceIrreducibleComponent (productWithA1 X)}
    (h : projectionToBase_graphPrimeGeom X C = projectionToBase_graphPrimeGeom X D) :
    SourceIrreducibleComponent.IsoOverAmbient C D := by
  exact isoOverAmbient_of_projectionToBase_graphPrimeSupportEquivalent X (Quotient.exact h)

/-- The singleton presentation attached to the componentwise graph prime support
for `X ×_k A1_k ⟶ X`. -/
def projectionToBase_componentCorrespondencePresentation (X : Geometry.SmSchemeOver k)
    (component : SourceIrreducibleComponent (productWithA1 X)) :
    FiniteCorrespondencePresentation (productWithA1 X) X :=
  FiniteCorrespondencePresentation.ofPrimeSupport
    (projectionToBase_graphPrimeSupport X component)

/-- The singleton finite correspondence attached to the componentwise graph
prime support for `X ×_k A1_k ⟶ X`. -/
def projectionToBase_componentCorrespondence (X : Geometry.SmSchemeOver k)
    (component : SourceIrreducibleComponent (productWithA1 X)) :
    FiniteCorrespondence (productWithA1 X) X :=
  FiniteCorrespondence.ofPrimeSupport (projectionToBase_graphPrimeSupport X component)

/-- The componentwise singleton finite correspondence depends only on the
source-component class over the ambient source. -/
theorem projectionToBase_componentCorrespondence_eq_of_isoOverAmbient
    (X : Geometry.SmSchemeOver k)
    {C D : SourceIrreducibleComponent (productWithA1 X)}
    (h : SourceIrreducibleComponent.IsoOverAmbient C D) :
    projectionToBase_componentCorrespondence X C =
      projectionToBase_componentCorrespondence X D := by
  change Finsupp.single (projectionToBase_graphPrimeGeom X C) (1 : ℤ) =
    Finsupp.single (projectionToBase_graphPrimeGeom X D) (1 : ℤ)
  rw [projectionToBase_graphPrimeGeom_eq_of_isoOverAmbient X h]

/-- The finite correspondence obtained by summing the componentwise singleton
graph correspondences over a chosen finite irreducible-component decomposition
of `X ×_k A1_k`. -/
def projectionToBase_finiteCorrespondenceOfDecomposition (X : Geometry.SmSchemeOver k)
    (decomp : FiniteIrreducibleComponentDecomposition (productWithA1 X)) :
    FiniteCorrespondence (productWithA1 X) X :=
  ∑ component in decomp.components, projectionToBase_componentCorrespondence X component

/-- The set of geometric graph classes contributed by a certified finite
irreducible-component decomposition of `X ×_k A1_k`. -/
def projectionToBase_graphPrimeClassesOfDecomposition (X : Geometry.SmSchemeOver k)
    (decomp : FiniteIrreducibleComponentDecomposition (productWithA1 X)) :
    Finset (PrimeFiniteCorrespondenceGeom (productWithA1 X) X) := by
  classical
  exact decomp.components.image (projectionToBase_graphPrimeGeom X)

/-- The decomposition-sum projection correspondence can be rewritten as a sum
over the induced geometric graph classes. -/
theorem projectionToBase_finiteCorrespondenceOfDecomposition_eq_sum_graphPrimeGeoms
    (X : Geometry.SmSchemeOver k)
    (decomp : FiniteIrreducibleComponentDecomposition (productWithA1 X)) :
    projectionToBase_finiteCorrespondenceOfDecomposition X decomp =
      ∑ graphClass in projectionToBase_graphPrimeClassesOfDecomposition X decomp,
        Finsupp.single graphClass 1 := by
  classical
  rw [projectionToBase_finiteCorrespondenceOfDecomposition,
    projectionToBase_graphPrimeClassesOfDecomposition]
  symm
  refine Finset.sum_image ?_
  intro C hC D hD hEq
  have hiso : SourceIrreducibleComponent.IsoOverAmbient C D :=
    isoOverAmbient_of_projectionToBase_graphPrimeGeom_eq X hEq
  exact decomp.no_equivalent_duplicates hC hD hiso

/-- Any two certified decompositions of `X ×_k A1_k` determine the same set of
componentwise graph geometric classes for the projection to `X`. -/
theorem projectionToBase_graphPrimeClasses_eq (X : Geometry.SmSchemeOver k)
    (D₁ D₂ : FiniteIrreducibleComponentDecomposition (productWithA1 X)) :
    projectionToBase_graphPrimeClassesOfDecomposition X D₁ =
      projectionToBase_graphPrimeClassesOfDecomposition X D₂ := by
  classical
  rw [projectionToBase_graphPrimeClassesOfDecomposition,
    projectionToBase_graphPrimeClassesOfDecomposition]
  apply Finset.ext
  intro graphClass
  constructor
  · intro hmem
    rcases Finset.mem_image.mp hmem with ⟨component, hcomponent, hgraph⟩
    rcases D₂.exhaustive component with ⟨listed, hiso⟩
    exact Finset.mem_image.mpr ⟨listed.1, listed.2, by
      rw [← projectionToBase_graphPrimeGeom_eq_of_isoOverAmbient X hiso]
      exact hgraph⟩
  · intro hmem
    rcases Finset.mem_image.mp hmem with ⟨component, hcomponent, hgraph⟩
    rcases D₁.exhaustive component with ⟨listed, hiso⟩
    exact Finset.mem_image.mpr ⟨listed.1, listed.2, by
      rw [← projectionToBase_graphPrimeGeom_eq_of_isoOverAmbient X hiso]
      exact hgraph⟩

/-- The decomposition-sum projection correspondence is independent of the
chosen finite irreducible-component decomposition. -/
theorem projectionToBase_finiteCorrespondence_independent
    (X : Geometry.SmSchemeOver k)
    (D₁ D₂ : FiniteIrreducibleComponentDecomposition (productWithA1 X)) :
    projectionToBase_finiteCorrespondenceOfDecomposition X D₁ =
      projectionToBase_finiteCorrespondenceOfDecomposition X D₂ := by
  simpa [projectionToBase_finiteCorrespondenceOfDecomposition,
    projectionToBase_componentCorrespondence, projectionToBase_graphPrimeSupport,
    Geometry.ordinaryMorphismGraph_finiteCorrespondenceOfDecomposition,
    Geometry.ordinaryMorphismGraph_componentCorrespondence] using
    Geometry.ordinaryMorphismGraph_finiteCorrespondence_independent
      (projectionToBase X) D₁ D₂

/-- The rationalized decomposition-sum correspondence for the projection
`X ×_k A1_k ⟶ X`, viewed in the existing `SmCorQ` Hom type. -/
def projectionToBase_rationalCorrespondenceOfDecomposition
    (category : SmCorQ (k := k)) (X : Geometry.SmSchemeOver k)
    (decomp : FiniteIrreducibleComponentDecomposition (productWithA1 X)) :
    SmCorQ.Hom category (productWithA1 X) X :=
  FiniteCorrespondence.toRational
    (projectionToBase_finiteCorrespondenceOfDecomposition X decomp)

/-- The rationalized projection correspondence is independent of the chosen
finite irreducible-component decomposition. -/
theorem projectionToBase_rationalCorrespondence_independent
    (category : SmCorQ (k := k)) (X : Geometry.SmSchemeOver k)
    (D₁ D₂ : FiniteIrreducibleComponentDecomposition (productWithA1 X)) :
    projectionToBase_rationalCorrespondenceOfDecomposition category X D₁ =
      projectionToBase_rationalCorrespondenceOfDecomposition category X D₂ := by
  simpa [projectionToBase_rationalCorrespondenceOfDecomposition,
    projectionToBase_finiteCorrespondenceOfDecomposition,
    projectionToBase_componentCorrespondence, projectionToBase_graphPrimeSupport,
    Geometry.ordinaryMorphismGraph_rationalCorrespondenceOfDecomposition,
    Geometry.ordinaryMorphismGraph_finiteCorrespondenceOfDecomposition,
    Geometry.ordinaryMorphismGraph_componentCorrespondence] using
    Geometry.ordinaryMorphismGraph_rationalCorrespondence_independent
      category (projectionToBase X) D₁ D₂

/-- The representable `A1`-projection localization morphism induced by a chosen
finite irreducible-component decomposition of `X ×_k A1_k`. Its direction is
the variance-correct one for `QtrMap`: from the representable of the cylinder
to the representable of the base. -/
def projectionToBase_QtrMapOfDecomposition
    (category : SmCorQ (k := k)) (X : Geometry.SmSchemeOver k)
    (decomp : FiniteIrreducibleComponentDecomposition (productWithA1 X)) :
    Qtr (category := category) (productWithA1 X) ⟶ Qtr (category := category) X :=
  QtrMap (category := category)
    (projectionToBase_rationalCorrespondenceOfDecomposition category X decomp)

/-- The representable `A1`-projection localization morphism is independent of
the chosen finite irreducible-component decomposition of `X ×_k A1_k`. -/
theorem projectionToBase_QtrMap_independent
    (category : SmCorQ (k := k)) (X : Geometry.SmSchemeOver k)
    (D₁ D₂ : FiniteIrreducibleComponentDecomposition (productWithA1 X)) :
    projectionToBase_QtrMapOfDecomposition category X D₁ =
      projectionToBase_QtrMapOfDecomposition category X D₂ := by
  unfold projectionToBase_QtrMapOfDecomposition
  exact congrArg (QtrMap (category := category))
    (projectionToBase_rationalCorrespondence_independent category X D₁ D₂)

/-- The decomposition-indexed map induced on a presheaf with transfers by the
rationalized projection correspondence `X ×_k A1_k ⟶ X`. -/
def projectionToBase_PSTMapOfDecomposition
    {category : SmCorQ (k := k)}
    (F : PST category) (X : Geometry.SmSchemeOver k)
    (D : FiniteIrreducibleComponentDecomposition (productWithA1 X)) := by
  letI := SmCorQCat category
  exact F.map (Quiver.Hom.op
    (projectionToBase_rationalCorrespondenceOfDecomposition category X D))

/-- The decomposition-indexed PST map induced by the projection correspondence
is independent of the chosen finite irreducible-component decomposition. -/
theorem projectionToBase_PSTMap_independent
    {category : SmCorQ (k := k)}
    (F : PST category) (X : Geometry.SmSchemeOver k)
    (D₁ D₂ : FiniteIrreducibleComponentDecomposition (productWithA1 X)) :
    projectionToBase_PSTMapOfDecomposition F X D₁ =
      projectionToBase_PSTMapOfDecomposition F X D₂ := by
  letI := SmCorQCat category
  exact congrArg F.map <|
    congrArg Quiver.Hom.op
      (projectionToBase_rationalCorrespondence_independent category X D₁ D₂)

/-- The `LinearPST` Yoneda bridge sends precomposition by the representable
`A1`-projection generator to the induced value map on the presheaf. -/
theorem QtrLinear_yoneda_representableA1Projection
    {category : SmCorQ (k := k)}
    (F : LinearPST category) (X : Geometry.SmSchemeOver k)
    (D : FiniteIrreducibleComponentDecomposition (productWithA1 X))
    (η : (QtrLinear (category := category) X).toPST ⟶ F.toPST) :
    QtrLinear_yoneda F (productWithA1 X)
        ((projectionToBase_QtrMapOfDecomposition category X D) ≫ η) =
      projectionToBase_PSTMapOfDecomposition F.toPST X D
        (QtrLinear_yoneda F X η) := by
  simpa [projectionToBase_QtrMapOfDecomposition,
    projectionToBase_PSTMapOfDecomposition] using
    QtrLinear_yoneda_naturality (F := F)
      (α := projectionToBase_rationalCorrespondenceOfDecomposition category X D) η

end

end Boundary
