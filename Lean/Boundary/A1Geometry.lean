import Boundary.A1Invariance
import Boundary.ComponentGeometry
import Boundary.CorrespondenceSums
import Boundary.NisnevichDescent
import Boundary.NisnevichTopology
import Boundary.PolynomialSmoothness
import Boundary.SmOver
import Geometry.Correspondences.Graph
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
import Mathlib.AlgebraicGeometry.Morphisms.Separated
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.CategoryTheory.FullSubcategory
import Mathlib.CategoryTheory.Localization.Bousfield
import Mathlib.RingTheory.RingHom.Locally
import Mathlib.RingTheory.FinitePresentation
import Mathlib.RingTheory.FiniteType

/-!
# Affine-Line Geometry Over A Perfect Field

This module packages the honest algebraic-geometry data around the affine line
over `k` that is already available in the current environment.
-/

universe u

open AlgebraicGeometry CategoryTheory

namespace Boundary

noncomputable section

variable {k : Type u} [Field k] [PerfectField k]

/-- The affine-line scheme over `k`, presented as `Spec(k[t])`. -/
abbrev affineLineSchemeOver (k : Type u) [Field k] [PerfectField k] : Scheme.{u} :=
  Spec (CommRingCat.of (Polynomial k))

/-- The structural morphism `Spec(k[t]) ⟶ Spec(k)` induced by `Polynomial.C`. -/
abbrev affineLineStructMap (k : Type u) [Field k] [PerfectField k] :
    affineLineSchemeOver k ⟶ Spec (CommRingCat.of k) :=
  Spec.map (CommRingCat.ofHom (Polynomial.C : k →+* Polynomial k))

theorem affineLineSeparated (k : Type u) [Field k] [PerfectField k] :
    IsSeparated (affineLineStructMap k) := by
  infer_instance

theorem affineLineQuasiCompact (k : Type u) [Field k] [PerfectField k] :
    QuasiCompact (affineLineStructMap k) := by
  infer_instance

theorem affineLineLocallyOfFiniteType (k : Type u) [Field k] [PerfectField k] :
    LocallyOfFiniteType (affineLineStructMap k) := by
  rw [HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)]
  change RingHom.FiniteType (Polynomial.C : k →+* Polynomial k)
  letI : Algebra k (Polynomial k) := (Polynomial.C).toAlgebra
  rw [RingHom.FiniteType]
  rw [polynomial_C_toAlgebra_eq]
  exact Algebra.FiniteType.polynomial k

theorem affineLineFiniteType (k : Type u) [Field k] [PerfectField k] :
    Geometry.IsOfFiniteType (affineLineStructMap k) := by
  exact ⟨affineLineQuasiCompact k, affineLineLocallyOfFiniteType k⟩

theorem polynomialAffineLine_isSmooth (k : Type u) [Field k] [PerfectField k] :
    IsSmooth (affineLineStructMap k) := by
  rw [HasRingHomProperty.Spec_iff (P := @IsSmooth)]
  exact RingHom.locally_of RingHom.isStandardSmooth_respectsIso
    (Polynomial.C : k →+* Polynomial k) (polynomial_C_isStandardSmooth k)

/-- The affine line as an object of `Sm/k`. -/
def A1_k :
    Geometry.SmSchemeOver k where
  scheme := affineLineSchemeOver k
  structMap := affineLineStructMap k
  smooth := polynomialAffineLine_isSmooth k
  separated := affineLineSeparated k
  finiteType := affineLineFiniteType k

/-- The smooth fiber product `X ×_k A1_k` over `Spec k`. -/
def productWithA1 (X : Geometry.SmSchemeOver k) : Geometry.SmSchemeOver k := by
  let A1 := A1_k (k := k)
  refine
    { scheme := overBaseProduct X A1
      structMap := overBaseProduct.fst X A1 ≫ X.structMap
      smooth := ?_
      separated := ?_
      finiteType := ?_ }
  · letI : MorphismProperty.IsStableUnderBaseChange @IsSmooth :=
      isSmooth_isStableUnderBaseChange
    letI : IsSmooth (overBaseProduct.fst X A1) :=
      MorphismProperty.pullback_fst X.structMap A1.structMap A1.smooth
    letI : IsSmooth X.structMap := X.smooth
    infer_instance
  · letI : IsSeparated (overBaseProduct.fst X A1) :=
      MorphismProperty.pullback_fst X.structMap A1.structMap A1.separated
    letI : IsSeparated X.structMap := X.separated
    infer_instance
  · letI : QuasiCompact A1.structMap := Geometry.SmSchemeOver.quasiCompact_structMap A1
    letI : LocallyOfFiniteType A1.structMap := Geometry.SmSchemeOver.locallyOfFiniteType_structMap A1
    letI : QuasiCompact X.structMap := Geometry.SmSchemeOver.quasiCompact_structMap X
    letI : LocallyOfFiniteType X.structMap := Geometry.SmSchemeOver.locallyOfFiniteType_structMap X
    letI : QuasiCompact (overBaseProduct.fst X A1) :=
      MorphismProperty.pullback_fst X.structMap A1.structMap
        (Geometry.SmSchemeOver.quasiCompact_structMap A1)
    letI : LocallyOfFiniteType (overBaseProduct.fst X A1) :=
      MorphismProperty.pullback_fst X.structMap A1.structMap
        (Geometry.SmSchemeOver.locallyOfFiniteType_structMap A1)
    exact ⟨inferInstance, inferInstance⟩

/-- The projection `X ×_k A1_k ⟶ X` in `Sm/k`. -/
def projectionToBase (X : Geometry.SmSchemeOver k) : productWithA1 X ⟶ X where
  hom := overBaseProduct.fst X (A1_k (k := k))
  over := rfl

/-- The graph-correspondence obligation for the projection `X ×_k A1_k ⟶ X`.
This is the current concrete transfer datum exposed by the existing geometry
graph machinery. -/
def projectionTransferToBaseGraphObligation (X : Geometry.SmSchemeOver k) :
    Geometry.MorphismGraphTransferObligationQ (projectionToBase X) :=
  Geometry.morphismGraphTransferObligation (projectionToBase X)

/-- The graph projection for `X ×_k A1_k ⟶ X` is finite. -/
theorem projectionToBase_graphProjectionFinite (X : Geometry.SmSchemeOver k) :
    IsFinite
      (Geometry.ordinaryMorphismGraphMap (projectionToBase X) ≫
        overBaseProduct.fst (productWithA1 X) X) := by
  simpa using Geometry.ordinaryMorphismGraphProjectionFinite (projectionToBase X)

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
  let compat :=
    SourceIrreducibleComponent.IsoOverAmbient.CompatibleOverBaseProductIso.ofIsoOverAmbient
      (Y := X) h
  refine ⟨compat, h.iso, ?_⟩
  change (projectionToBase_graphPrimeSupport X C).inclusion ≫ compat.iso.hom =
    h.iso.hom ≫ (projectionToBase_graphPrimeSupport X D).inclusion
  apply Limits.pullback.hom_ext
  · calc
      (projectionToBase_graphPrimeSupport X C).inclusion ≫ compat.iso.hom ≫
          overBaseProduct.fst D.carrier X
          = (projectionToBase_graphPrimeSupport X C).inclusion ≫
              overBaseProduct.fst C.carrier X ≫ h.iso.hom := by
                simpa [compat,
                  SourceIrreducibleComponent.IsoOverAmbient.CompatibleOverBaseProductIso.ofIsoOverAmbient,
                  Category.assoc] using
                  congrArg (fun f => (projectionToBase_graphPrimeSupport X C).inclusion ≫ f)
                    (SourceIrreducibleComponent.IsoOverAmbient.overBaseProductIso_hom_fst
                      (Y := X) h)
      _ = (projectionToBase_graphPrimeSupport X C).finiteOverSourceComponent ≫ h.iso.hom := by
            simpa [Category.assoc] using
              congrArg (fun f => f ≫ h.iso.hom)
                (projectionToBase_graphPrimeSupport X C).inclusion_fst
      _ = h.iso.hom := by
            change ((Geometry.ordinaryMorphismGraphMap
              (Geometry.ordinaryMorphismOnSourceComponent C (projectionToBase X)) ≫
                overBaseProduct.fst C.carrier X) ≫ h.iso.hom = h.iso.hom)
            simpa [Category.assoc] using
              congrArg (fun f => f ≫ h.iso.hom)
                (Geometry.ordinaryMorphismGraphMap_fst
                  (Geometry.ordinaryMorphismOnSourceComponent C (projectionToBase X)))
      _ = h.iso.hom ≫ (projectionToBase_graphPrimeSupport X D).finiteOverSourceComponent := by
            change h.iso.hom = h.iso.hom ≫
              (Geometry.ordinaryMorphismGraphMap
                (Geometry.ordinaryMorphismOnSourceComponent D (projectionToBase X)) ≫
                  overBaseProduct.fst D.carrier X)
            simpa [Category.assoc] using
              congrArg (fun f => h.iso.hom ≫ f)
                (Geometry.ordinaryMorphismGraphMap_fst
                  (Geometry.ordinaryMorphismOnSourceComponent D (projectionToBase X))).symm
      _ = h.iso.hom ≫ (projectionToBase_graphPrimeSupport X D).inclusion ≫
            overBaseProduct.fst D.carrier X := by
            simpa [Category.assoc] using
              congrArg (fun f => h.iso.hom ≫ f)
                (projectionToBase_graphPrimeSupport X D).inclusion_fst.symm
  · calc
      (projectionToBase_graphPrimeSupport X C).inclusion ≫ compat.iso.hom ≫
          overBaseProduct.snd D.carrier X
          = (projectionToBase_graphPrimeSupport X C).inclusion ≫
              overBaseProduct.snd C.carrier X := by
                simpa [compat,
                  SourceIrreducibleComponent.IsoOverAmbient.CompatibleOverBaseProductIso.ofIsoOverAmbient,
                  Category.assoc] using
                  congrArg (fun f => (projectionToBase_graphPrimeSupport X C).inclusion ≫ f)
                    (SourceIrreducibleComponent.IsoOverAmbient.overBaseProductIso_hom_snd
                      (Y := X) h)
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
            overBaseProduct.snd D.carrier X := by
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
          SourceIrreducibleComponent.IsoOverAmbient.CompatibleOverBaseProductIso
            (Y := X) C D)
        (_iso : C.carrier.scheme ≅ D.carrier.scheme),
        (projectionToBase_graphPrimeSupport X C).inclusion ≫ compatibleSourceComponent.iso.hom =
          _iso.hom ≫ (projectionToBase_graphPrimeSupport X D).inclusion := by
    simpa [PrimeFiniteCorrespondenceSupport.PrimeSupportEquivalent,
      PrimeFiniteCorrespondenceSupport.SupportIsoOverProduct] using h
  exact (Classical.choose h').sourceIso

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
    (D : FiniteIrreducibleComponentDecomposition (productWithA1 X)) :
    letI := SmCorQCat category
    ∀ (η : (QtrLinear (category := category) X).toPST ⟶ F.toPST),
      QtrLinear_yoneda F (productWithA1 X)
        ((projectionToBase_QtrMapOfDecomposition category X D) ≫ η) =
          projectionToBase_PSTMapOfDecomposition F.toPST X D
            (QtrLinear_yoneda F X η) := by
  letI := SmCorQCat category
  intro η
  simpa [projectionToBase_QtrMapOfDecomposition,
    projectionToBase_PSTMapOfDecomposition] using
    (QtrLinear_yoneda_naturality (F := F)
      (α := projectionToBase_rationalCorrespondenceOfDecomposition category X D) η)

/-- A presheaf with transfers is `A1`-local when every decomposition-indexed
projection map `X ×_k A1_k ⟶ X` induces an isomorphism. -/
def IsA1Local {category : SmCorQ (k := k)}
    (F : PST category) : Prop := by
  letI := SmCorQCat category
  exact ∀ (X : Geometry.SmSchemeOver k)
    (D : FiniteIrreducibleComponentDecomposition (productWithA1 X)),
      CategoryTheory.IsIso (projectionToBase_PSTMapOfDecomposition F X D)

namespace IsA1Local

/-- The `A1`-locality condition for the projection map is independent of the
chosen finite irreducible-component decomposition. -/
theorem decomposition_independent
    {category : SmCorQ (k := k)}
    {F : PST category} {X : Geometry.SmSchemeOver k}
    {D₁ D₂ : FiniteIrreducibleComponentDecomposition (productWithA1 X)}
    (h : CategoryTheory.IsIso (projectionToBase_PSTMapOfDecomposition F X D₁)) :
    CategoryTheory.IsIso (projectionToBase_PSTMapOfDecomposition F X D₂) := by
  rw [← projectionToBase_PSTMap_independent F X D₁ D₂]
  exact h

/-- Every `A1`-local presheaf with transfers inverts the representable
`A1`-projection generator on values. This is exactly the map appearing in the
definition of `IsA1Local`, induced by the same projection correspondence as
`projectionToBase_QtrMapOfDecomposition`. -/
theorem inverts_representableA1Projection
    {category : SmCorQ (k := k)} {F : PST category}
    (hF : IsA1Local F)
    (X : Geometry.SmSchemeOver k)
    (D : FiniteIrreducibleComponentDecomposition (productWithA1 X)) :
    CategoryTheory.IsIso (projectionToBase_PSTMapOfDecomposition F X D) :=
  hF X D

/-- If a presheaf with transfers inverts every representable `A1`-projection
generator on values, then it is `A1`-local. -/
theorem of_inverts_representableA1Projection
    {category : SmCorQ (k := k)} {F : PST category}
    (hF : ∀ (X : Geometry.SmSchemeOver k)
      (D : FiniteIrreducibleComponentDecomposition (productWithA1 X)),
        CategoryTheory.IsIso (projectionToBase_PSTMapOfDecomposition F X D)) :
    IsA1Local F :=
  hF

/-- A presheaf with transfers is `A1`-local exactly when it inverts every
representable `A1`-projection generator on values. -/
theorem isA1Local_iff_inverts_representableA1Projection
    {category : SmCorQ (k := k)} {F : PST category} :
    IsA1Local F ↔
      ∀ (X : Geometry.SmSchemeOver k)
        (D : FiniteIrreducibleComponentDecomposition (productWithA1 X)),
          CategoryTheory.IsIso (projectionToBase_PSTMapOfDecomposition F X D) := by
  constructor
  · exact inverts_representableA1Projection
  · exact of_inverts_representableA1Projection

end IsA1Local

/-- For a bundled linear presheaf with transfers, `A1`-locality is equivalent
to inverting the representable `A1`-projection generator on the current
Yoneda-carried morphism type. -/
theorem IsA1Local_iff_QtrLinear_inverts_A1Projection
    {category : SmCorQ (k := k)}
    (F : LinearPST category) :
    IsA1Local F.toPST ↔
      ∀ (X : Geometry.SmSchemeOver k)
        (D : FiniteIrreducibleComponentDecomposition (productWithA1 X)),
        Function.Bijective
          (fun η : (QtrLinear (category := category) X).toPST ⟶ F.toPST =>
            (projectionToBase_QtrMapOfDecomposition category X D) ≫ η) := by
  letI := SmCorQCat category
  constructor
  · intro hF X D
    let p := projectionToBase_PSTMapOfDecomposition F.toPST X D
    have hpIso : CategoryTheory.IsIso p :=
      (IsA1Local.isA1Local_iff_inverts_representableA1Projection
        (F := F.toPST)).mp hF X D
    let ep : F.toPST.obj (Opposite.op X) ≃ₗ[ℚ] F.toPST.obj (Opposite.op (productWithA1 X)) :=
      (asIso p).toLinearEquiv
    have hpBij : Function.Bijective p := by
      simpa using ep.bijective
    refine ⟨?_, ?_⟩
    · intro η₁ η₂ hη
      apply (QtrLinear_yoneda F X).injective
      have h₁ := QtrLinear_yoneda_representableA1Projection (F := F) X D η₁
      have h₂ := QtrLinear_yoneda_representableA1Projection (F := F) X D η₂
      apply hpBij.1
      calc
        p (QtrLinear_yoneda F X η₁)
          = QtrLinear_yoneda F (productWithA1 X)
              ((projectionToBase_QtrMapOfDecomposition category X D) ≫ η₁) := by
                symm
                exact h₁
        _ = QtrLinear_yoneda F (productWithA1 X)
              ((projectionToBase_QtrMapOfDecomposition category X D) ≫ η₂) := by
                simpa using congrArg (QtrLinear_yoneda F (productWithA1 X)) hη
        _ = p (QtrLinear_yoneda F X η₂) := h₂
    · intro θ
      rcases hpBij.2 (QtrLinear_yoneda F (productWithA1 X) θ) with ⟨x, hx⟩
      refine ⟨(QtrLinear_yoneda F X).invFun x, ?_⟩
      apply (QtrLinear_yoneda F (productWithA1 X)).injective
      calc
        QtrLinear_yoneda F (productWithA1 X)
            ((projectionToBase_QtrMapOfDecomposition category X D) ≫
              (QtrLinear_yoneda F X).invFun x)
          = p (QtrLinear_yoneda F X ((QtrLinear_yoneda F X).invFun x)) :=
              QtrLinear_yoneda_representableA1Projection
                (F := F) X D ((QtrLinear_yoneda F X).invFun x)
        _ = p x := by
              exact congrArg p ((QtrLinear_yoneda F X).right_inv x)
        _ = QtrLinear_yoneda F (productWithA1 X) θ := hx
  · intro hF
    rw [IsA1Local.isA1Local_iff_inverts_representableA1Projection]
    intro X D
    let p := projectionToBase_PSTMapOfDecomposition F.toPST X D
    have hpre := hF X D
    have hpBij : Function.Bijective p := by
      refine ⟨?_, ?_⟩
      · intro x₁ x₂ hx
        let η₁ : (QtrLinear (category := category) X).toPST ⟶ F.toPST :=
          (QtrLinear_yoneda F X).invFun x₁
        let η₂ : (QtrLinear (category := category) X).toPST ⟶ F.toPST :=
          (QtrLinear_yoneda F X).invFun x₂
        have hpreEq :
            (projectionToBase_QtrMapOfDecomposition category X D) ≫ η₁ =
              (projectionToBase_QtrMapOfDecomposition category X D) ≫ η₂ := by
          apply (QtrLinear_yoneda F (productWithA1 X)).injective
          calc
            QtrLinear_yoneda F (productWithA1 X)
                ((projectionToBase_QtrMapOfDecomposition category X D) ≫ η₁)
              = p x₁ := by
                  calc
                    QtrLinear_yoneda F (productWithA1 X)
                        ((projectionToBase_QtrMapOfDecomposition category X D) ≫ η₁)
                      = p (QtrLinear_yoneda F X η₁) :=
                          QtrLinear_yoneda_representableA1Projection (F := F) X D η₁
                    _ = p x₁ := by
                          exact congrArg p (by simpa [η₁] using (QtrLinear_yoneda F X).right_inv x₁)
            _ = p x₂ := hx
            _ = QtrLinear_yoneda F (productWithA1 X)
                ((projectionToBase_QtrMapOfDecomposition category X D) ≫ η₂) := by
                  calc
                    p x₂ = p (QtrLinear_yoneda F X η₂) := by
                      exact congrArg p (by simpa [η₂] using ((QtrLinear_yoneda F X).right_inv x₂).symm)
                    _ = QtrLinear_yoneda F (productWithA1 X)
                        ((projectionToBase_QtrMapOfDecomposition category X D) ≫ η₂) :=
                          (QtrLinear_yoneda_representableA1Projection (F := F) X D η₂).symm
        have hη : η₁ = η₂ := hpre.1 hpreEq
        have hx' := congrArg (QtrLinear_yoneda F X) hη
        simpa [η₁, η₂] using hx'
      · intro y
        let θ : (QtrLinear (category := category) (productWithA1 X)).toPST ⟶ F.toPST :=
          (QtrLinear_yoneda F (productWithA1 X)).invFun y
        rcases hpre.2 θ with ⟨η, hη⟩
        refine ⟨QtrLinear_yoneda F X η, ?_⟩
        calc
          p (QtrLinear_yoneda F X η)
            = QtrLinear_yoneda F (productWithA1 X)
                ((projectionToBase_QtrMapOfDecomposition category X D) ≫ η) := by
                  symm
                  exact QtrLinear_yoneda_representableA1Projection (F := F) X D η
          _ = QtrLinear_yoneda F (productWithA1 X) θ := by
                simpa using congrArg (QtrLinear_yoneda F (productWithA1 X)) hη
          _ = y := (QtrLinear_yoneda F (productWithA1 X)).right_inv y
    exact
      (LinearEquiv.toModuleIso'
        (LinearEquiv.ofBijective p hpBij)).isIso_hom

/-- Bundled `A1`-local presheaves with transfers. -/
abbrev A1LocalPST (category : SmCorQ (k := k)) :=
  { F : PST category // IsA1Local F }

namespace A1LocalPST

/-- Forget the `A1`-locality proof and view a bundled object as a presheaf with
transfers. -/
abbrev toPST {category : SmCorQ (k := k)}
    (F : A1LocalPST category) : PST category :=
  F.1

/-- A bundled `A1`-local presheaf with transfers carries its locality proof. -/
theorem isA1Local {category : SmCorQ (k := k)}
    (F : A1LocalPST category) : IsA1Local F.toPST :=
  F.2

end A1LocalPST

/-- A presheaf with transfers is both `A1`-local and Nisnevich-local. -/
def IsA1NisLocal {category : SmCorQ (k := k)}
    (F : PST category) : Prop :=
  IsA1Local F ∧ IsNisnevichLocal F

namespace IsA1NisLocal

/-- A combined `A1`+Nisnevich-local presheaf is `A1`-local. -/
theorem isA1Local {category : SmCorQ (k := k)} {F : PST category}
    (hF : IsA1NisLocal F) : IsA1Local F :=
  hF.1

/-- A combined `A1`+Nisnevich-local presheaf is Nisnevich-local. -/
theorem isNisnevichLocal {category : SmCorQ (k := k)} {F : PST category}
    (hF : IsA1NisLocal F) : IsNisnevichLocal F :=
  hF.2

/-- If a presheaf with transfers is both `A1`-local and Nisnevich-local, then
it is combined `A1`+Nisnevich-local. -/
theorem of_localities {category : SmCorQ (k := k)} {F : PST category}
    (hA1 : IsA1Local F) (hNis : IsNisnevichLocal F) : IsA1NisLocal F :=
  ⟨hA1, hNis⟩

/-- A presheaf with transfers is combined `A1`+Nisnevich-local exactly when it
is both `A1`-local and Nisnevich-local. -/
theorem iff_localities {category : SmCorQ (k := k)} {F : PST category} :
    IsA1NisLocal F ↔ IsA1Local F ∧ IsNisnevichLocal F :=
  Iff.rfl

end IsA1NisLocal

/-- For a bundled linear presheaf with transfers, combined `A1` and Nisnevich
locality is equivalent to the conjunction of the two Yoneda-form local
conditions already established separately. -/
theorem IsA1NisLocal_iff_QtrLinear_local
    {category : SmCorQ (k := k)}
    (F : LinearPST category) :
    IsA1NisLocal F.toPST ↔
      (∀ (X : Geometry.SmSchemeOver k)
        (D : FiniteIrreducibleComponentDecomposition (productWithA1 X)),
        Function.Bijective
          (fun η : (QtrLinear (category := category) X).toPST ⟶ F.toPST =>
            (projectionToBase_QtrMapOfDecomposition category X D) ≫ η)) ∧
      (∀ square : NisnevichDistinguishedSquareDataQ category,
        ∀ (ηopen : (QtrLinear (category := category) square.openPiece).toPST ⟶ F.toPST)
          (ηpatch : (QtrLinear (category := category) square.patchPiece).toPST ⟶ F.toPST),
          (QtrMap (category := category) square.overlapToOpenTransfer) ≫ ηopen =
            (QtrMap (category := category) square.overlapToPatchTransfer) ≫ ηpatch →
          ∃! ηbase : (QtrLinear (category := category) square.base).toPST ⟶ F.toPST,
            (QtrMap (category := category) square.openToBaseTransfer) ≫ ηbase = ηopen ∧
              (QtrMap (category := category) square.patchToBaseTransfer) ≫ ηbase = ηpatch) := by
  rw [IsA1NisLocal.iff_localities,
    IsA1Local_iff_QtrLinear_inverts_A1Projection,
    IsNisnevichLocal_iff_QtrLinear_satisfies_descent]

/-- Canonical-route Nisnevich locality for presheaves with transfers on
`canonicalSmCorQ`. This is just the existing squarewise descent condition,
specialized to the canonical rational correspondence category attached to the
chosen composition package. -/
def IsCanonicalNisnevichLocal
    (composition : Boundary.CanonicalCompositionData (k := k))
    (F : PST (Boundary.canonicalCategory composition)) : Prop :=
  IsNisnevichLocal F

/-- On the canonical route, Nisnevich locality is exactly the usual unique
gluing condition for canonical distinguished-square descent generators. -/
theorem IsCanonicalNisnevichLocal_iff_QtrLinear_satisfies_descent
    (composition : Boundary.CanonicalCompositionData (k := k))
    (F : LinearPST (Boundary.canonicalCategory composition)) :
    IsCanonicalNisnevichLocal composition F.toPST ↔
      ∀ square : NisnevichDistinguishedSquareDataQ (Boundary.canonicalCategory composition),
        ∀ (ηopen : (QtrLinear (category := Boundary.canonicalCategory composition)
            square.openPiece).toPST ⟶ F.toPST)
          (ηpatch : (QtrLinear (category := Boundary.canonicalCategory composition)
            square.patchPiece).toPST ⟶ F.toPST),
          (QtrMap (category := Boundary.canonicalCategory composition)
              square.overlapToOpenTransfer) ≫ ηopen =
            (QtrMap (category := Boundary.canonicalCategory composition)
              square.overlapToPatchTransfer) ≫ ηpatch →
          ∃! ηbase : (QtrLinear (category := Boundary.canonicalCategory composition)
              square.base).toPST ⟶ F.toPST,
            (QtrMap (category := Boundary.canonicalCategory composition)
                square.openToBaseTransfer) ≫ ηbase = ηopen ∧
              (QtrMap (category := Boundary.canonicalCategory composition)
                square.patchToBaseTransfer) ≫ ηbase = ηpatch :=
  IsNisnevichLocal_iff_QtrLinear_satisfies_descent F

/-- Canonical-route `A1`-locality for presheaves with transfers on
`canonicalSmCorQ`. This is the existing `A1`-locality predicate specialized to
the canonical rational correspondence category determined by `composition`. -/
def IsCanonicalA1Local
    (composition : Boundary.CanonicalCompositionData (k := k))
    (F : PST (Boundary.canonicalCategory composition)) : Prop :=
  IsA1Local F

/-- Canonical-route combined `A1`+Nisnevich locality on `canonicalSmCorQ`. -/
def IsCanonicalA1NisLocal
    (composition : Boundary.CanonicalCompositionData (k := k))
    (F : PST (Boundary.canonicalCategory composition)) : Prop :=
  IsCanonicalA1Local composition F ∧ IsCanonicalNisnevichLocal composition F

namespace IsCanonicalA1NisLocal

/-- A canonical `A1`+Nisnevich-local presheaf is canonically `A1`-local. -/
theorem isA1Local
    {composition : Boundary.CanonicalCompositionData (k := k)}
    {F : PST (Boundary.canonicalCategory composition)}
    (hF : IsCanonicalA1NisLocal composition F) :
    IsCanonicalA1Local composition F :=
  hF.1

/-- A canonical `A1`+Nisnevich-local presheaf is canonically Nisnevich-local. -/
theorem isNisnevichLocal
    {composition : Boundary.CanonicalCompositionData (k := k)}
    {F : PST (Boundary.canonicalCategory composition)}
    (hF : IsCanonicalA1NisLocal composition F) :
    IsCanonicalNisnevichLocal composition F :=
  hF.2

/-- Canonical combined locality is exactly the conjunction of the canonical
`A1`- and Nisnevich-locality predicates. -/
theorem iff_localities
    {composition : Boundary.CanonicalCompositionData (k := k)}
    {F : PST (Boundary.canonicalCategory composition)} :
    IsCanonicalA1NisLocal composition F ↔
      IsCanonicalA1Local composition F ∧
        IsCanonicalNisnevichLocal composition F :=
  Iff.rfl

end IsCanonicalA1NisLocal

/-- On the canonical route, combined `A1`+Nisnevich locality is equivalent to
the conjunction of the canonical `A1`-projection and distinguished-square
descent conditions on the honest `QtrLinear` surface. -/
theorem IsCanonicalA1NisLocal_iff_QtrLinear_local
    (composition : Boundary.CanonicalCompositionData (k := k))
    (F : LinearPST (Boundary.canonicalCategory composition)) :
    IsCanonicalA1NisLocal composition F.toPST ↔
      (∀ (X : Geometry.SmSchemeOver k)
        (D : FiniteIrreducibleComponentDecomposition (productWithA1 X)),
        Function.Bijective
          (fun η : (QtrLinear (category := Boundary.canonicalCategory composition) X).toPST ⟶
              F.toPST =>
            (projectionToBase_QtrMapOfDecomposition
              (Boundary.canonicalCategory composition) X D) ≫ η)) ∧
      (∀ square : NisnevichDistinguishedSquareDataQ (Boundary.canonicalCategory composition),
        ∀ (ηopen : (QtrLinear (category := Boundary.canonicalCategory composition)
            square.openPiece).toPST ⟶ F.toPST)
          (ηpatch : (QtrLinear (category := Boundary.canonicalCategory composition)
            square.patchPiece).toPST ⟶ F.toPST),
          (QtrMap (category := Boundary.canonicalCategory composition)
              square.overlapToOpenTransfer) ≫ ηopen =
            (QtrMap (category := Boundary.canonicalCategory composition)
              square.overlapToPatchTransfer) ≫ ηpatch →
          ∃! ηbase : (QtrLinear (category := Boundary.canonicalCategory composition)
              square.base).toPST ⟶ F.toPST,
            (QtrMap (category := Boundary.canonicalCategory composition)
                square.openToBaseTransfer) ≫ ηbase = ηopen ∧
              (QtrMap (category := Boundary.canonicalCategory composition)
                square.patchToBaseTransfer) ≫ ηbase = ηpatch) := by
  change IsA1NisLocal F.toPST ↔
      (∀ (X : Geometry.SmSchemeOver k)
        (D : FiniteIrreducibleComponentDecomposition (productWithA1 X)),
        Function.Bijective
          (fun η : (QtrLinear (category := Boundary.canonicalCategory composition) X).toPST ⟶
              F.toPST =>
            (projectionToBase_QtrMapOfDecomposition
              (Boundary.canonicalCategory composition) X D) ≫ η)) ∧
      (∀ square : NisnevichDistinguishedSquareDataQ (Boundary.canonicalCategory composition),
        ∀ (ηopen : (QtrLinear (category := Boundary.canonicalCategory composition)
            square.openPiece).toPST ⟶ F.toPST)
          (ηpatch : (QtrLinear (category := Boundary.canonicalCategory composition)
            square.patchPiece).toPST ⟶ F.toPST),
          (QtrMap (category := Boundary.canonicalCategory composition)
              square.overlapToOpenTransfer) ≫ ηopen =
            (QtrMap (category := Boundary.canonicalCategory composition)
              square.overlapToPatchTransfer) ≫ ηpatch →
          ∃! ηbase : (QtrLinear (category := Boundary.canonicalCategory composition)
              square.base).toPST ⟶ F.toPST,
            (QtrMap (category := Boundary.canonicalCategory composition)
                square.openToBaseTransfer) ≫ ηbase = ηopen ∧
              (QtrMap (category := Boundary.canonicalCategory composition)
                square.patchToBaseTransfer) ≫ ηbase = ηpatch)
  exact IsA1NisLocal_iff_QtrLinear_local F

/-- A bundled linear presheaf with transfers is `A1`+Nisnevich-local when its
underlying presheaf with transfers is both `A1`-local and Nisnevich-local. -/
def IsLinearA1NisLocal {category : SmCorQ (k := k)}
    (F : LinearPST category) : Prop :=
  IsA1NisLocal F.toPST

/-- Bundled `A1`+Nisnevich-local presheaves with transfers inside the honest
`LinearPST` surface. -/
abbrev LinearA1NisLocalPST (category : SmCorQ (k := k)) :=
  { F : LinearPST category // IsLinearA1NisLocal F }

namespace LinearA1NisLocalPST

/-- Forget the locality proof and view a bundled object as a linear presheaf
with transfers. -/
abbrev toLinearPST {category : SmCorQ (k := k)}
    (F : LinearA1NisLocalPST category) : LinearPST category :=
  F.1

instance {category : SmCorQ (k := k)} : Category (LinearA1NisLocalPST category) := by
  exact InducedCategory.category LinearA1NisLocalPST.toLinearPST

/-- Forget the linearity and locality proofs and view a bundled object as an
ordinary presheaf with transfers. -/
abbrev toPST {category : SmCorQ (k := k)}
    (F : LinearA1NisLocalPST category) : PST category :=
  F.toLinearPST.toPST

/-- A bundled linear `A1`+Nisnevich-local presheaf carries its combined
locality proof. -/
theorem isA1NisLocal {category : SmCorQ (k := k)}
    (F : LinearA1NisLocalPST category) : IsA1NisLocal F.toPST :=
  F.2

/-- A bundled linear `A1`+Nisnevich-local presheaf is `A1`-local. -/
theorem isA1Local {category : SmCorQ (k := k)}
    (F : LinearA1NisLocalPST category) : IsA1Local F.toPST :=
  F.2.1

/-- A bundled linear `A1`+Nisnevich-local presheaf is Nisnevich-local. -/
theorem isNisnevichLocal {category : SmCorQ (k := k)}
    (F : LinearA1NisLocalPST category) : IsNisnevichLocal F.toPST :=
  F.2.2

/-- The inclusion of `A1`+Nisnevich-local linear presheaves with transfers into
all linear presheaves with transfers.

This is a fully faithful embedding; its left adjoint (A¹/Nis sheafification)
is the Step 2 mathematical blocker. -/
def inclusion (category : SmCorQ (k := k)) :
    LinearA1NisLocalPST category ⥤ LinearPST category :=
  inducedFunctor LinearA1NisLocalPST.toLinearPST

@[simp] theorem inclusion_obj {category : SmCorQ (k := k)}
    (F : LinearA1NisLocalPST category) :
    (inclusion category).obj F = F.toLinearPST :=
  rfl

@[simp] theorem inclusion_map {category : SmCorQ (k := k)}
    {F G : LinearA1NisLocalPST category} (f : F ⟶ G) :
    (inclusion category).map f = f :=
  rfl

instance inclusion_full {category : SmCorQ (k := k)} :
    (inclusion category).Full := by
  change (inducedFunctor LinearA1NisLocalPST.toLinearPST).Full
  infer_instance

instance inclusion_faithful {category : SmCorQ (k := k)} :
    (inclusion category).Faithful := by
  change (inducedFunctor LinearA1NisLocalPST.toLinearPST).Faithful
  infer_instance

end LinearA1NisLocalPST

/-- A morphism of bundled linear presheaves with transfers is an `A1`+Nisnevich
local equivalence when every bundled local object sees precomposition with it
as a bijection on morphism sets. -/
def IsA1NisLocalEquivalence
    {category : SmCorQ (k := k)}
    {F G : LinearPST category}
    (φ : F ⟶ G) : Prop :=
  ∀ (L : LinearA1NisLocalPST category),
    Function.Bijective (fun η : G ⟶ L.toLinearPST => φ ≫ η)

namespace IsA1NisLocalEquivalence

theorem id
    {category : SmCorQ (k := k)}
    (F : LinearPST category) :
    IsA1NisLocalEquivalence (𝟙 F) := by
  intro L
  constructor
  · intro η₁ η₂ hη
    simpa using hη
  · intro η
    refine ⟨η, ?_⟩
    simp

theorem comp
    {category : SmCorQ (k := k)}
    {F G H : LinearPST category}
    {φ : F ⟶ G} {ψ : G ⟶ H}
    (hφ : IsA1NisLocalEquivalence φ)
    (hψ : IsA1NisLocalEquivalence ψ) :
    IsA1NisLocalEquivalence (φ ≫ ψ) := by
  intro L
  let bφ : Function.Bijective (fun η : G ⟶ L.toLinearPST => φ ≫ η) := hφ L
  let bψ : Function.Bijective (fun η : H ⟶ L.toLinearPST => ψ ≫ η) := hψ L
  constructor
  · intro η₁ η₂ hη
    apply bψ.1
    apply bφ.1
    simpa [Category.assoc] using hη
  · intro η
    rcases bφ.2 η with ⟨θ, hθ⟩
    rcases bψ.2 θ with ⟨μ, hμ⟩
    refine ⟨μ, ?_⟩
    calc
      (φ ≫ ψ) ≫ μ = φ ≫ (ψ ≫ μ) := by simp [Category.assoc]
      _ = φ ≫ θ := by simpa using congrArg (fun t => φ ≫ t) hμ
      _ = η := hθ

theorem of_comp_left
    {category : SmCorQ (k := k)}
    {F G H : LinearPST category}
    {φ : F ⟶ G} {ψ : G ⟶ H}
    (hψ : IsA1NisLocalEquivalence ψ)
    (hcomp : IsA1NisLocalEquivalence (φ ≫ ψ)) :
    IsA1NisLocalEquivalence φ := by
  intro L
  let bφ : Function.Bijective (fun η : G ⟶ L.toLinearPST => φ ≫ η) := by
    refine ⟨?_, ?_⟩
    · intro η₁ η₂ hη
      rcases (hψ L).2 η₁ with ⟨μ₁, hμ₁⟩
      rcases (hψ L).2 η₂ with ⟨μ₂, hμ₂⟩
      have hcompEq : (φ ≫ ψ) ≫ μ₁ = (φ ≫ ψ) ≫ μ₂ := by
        calc
          (φ ≫ ψ) ≫ μ₁ = φ ≫ η₁ := by
            simpa [Category.assoc] using congrArg (fun t => φ ≫ t) hμ₁
          _ = φ ≫ η₂ := hη
          _ = (φ ≫ ψ) ≫ μ₂ := by
            simpa [Category.assoc] using congrArg (fun t => φ ≫ t) hμ₂.symm
      have hμμ : μ₁ = μ₂ := (hcomp L).1 hcompEq
      calc
        η₁ = ψ ≫ μ₁ := hμ₁.symm
        _ = ψ ≫ μ₂ := by simpa using congrArg (fun t => ψ ≫ t) hμμ
        _ = η₂ := hμ₂
    · intro η
      rcases (hcomp L).2 η with ⟨μ, hμ⟩
      refine ⟨ψ ≫ μ, ?_⟩
      simpa [Category.assoc] using hμ
  exact bφ

theorem of_comp_right
    {category : SmCorQ (k := k)}
    {F G H : LinearPST category}
    {φ : F ⟶ G} {ψ : G ⟶ H}
    (hφ : IsA1NisLocalEquivalence φ)
    (hcomp : IsA1NisLocalEquivalence (φ ≫ ψ)) :
    IsA1NisLocalEquivalence ψ := by
  intro L
  let bψ : Function.Bijective (fun η : H ⟶ L.toLinearPST => ψ ≫ η) := by
    refine ⟨?_, ?_⟩
    · intro η₁ η₂ hη
      have hcompEq : (φ ≫ ψ) ≫ η₁ = (φ ≫ ψ) ≫ η₂ := by
        simpa [Category.assoc] using congrArg (fun t => φ ≫ t) hη
      exact (hcomp L).1 hcompEq
    · intro η
      rcases (hcomp L).2 (φ ≫ η) with ⟨μ, hμ⟩
      refine ⟨μ, ?_⟩
      apply (hφ L).1
      simpa [Category.assoc] using hμ
  exact bψ

theorem of_isIso
    {category : SmCorQ (k := k)}
    {F G : LinearPST category}
    (φ : F ⟶ G)
    [CategoryTheory.IsIso φ] :
    IsA1NisLocalEquivalence φ := by
  intro L
  constructor
  · intro η₁ η₂ hη
    calc
      η₁ = inv φ ≫ (φ ≫ η₁) := by simp [Category.assoc]
      _ = inv φ ≫ (φ ≫ η₂) := by
        simpa using congrArg (fun t => inv φ ≫ t) hη
      _ = η₂ := by simp [Category.assoc]
  · intro η
    refine ⟨inv φ ≫ η, ?_⟩
    simp [Category.assoc]

/-- If `φ : F ⟶ G` admits a left inverse `r : G ⟶ F` (i.e., `φ ≫ r = 𝟙 F`)
that is itself a local equivalence, then `φ` is a local equivalence.

A split mono with a local-equivalence retraction is a local equivalence
because composition with a fixed local equivalence preserves the class
(two-out-of-three via `of_comp_left`). -/
theorem of_hasLeftInverse
    {category : SmCorQ (k := k)}
    {F G : LinearPST category}
    {φ : F ⟶ G}
    (r : G ⟶ F)
    (hsplit : φ ≫ r = 𝟙 F)
    (hr : IsA1NisLocalEquivalence r) :
    IsA1NisLocalEquivalence φ :=
  of_comp_left hr (hsplit ▸ id F)

/-- If `φ : F ⟶ G` admits a right inverse `r : G ⟶ F` (i.e., `r ≫ φ = 𝟙 G`)
that is itself a local equivalence, then `φ` is a local equivalence.

A split epi with a local-equivalence section is a local equivalence
because composition with a fixed local equivalence preserves the class
(two-out-of-three via `of_comp_right`). -/
theorem of_hasRightInverse
    {category : SmCorQ (k := k)}
    {F G : LinearPST category}
    {φ : F ⟶ G}
    (r : G ⟶ F)
    (hsplit : r ≫ φ = 𝟙 G)
    (hr : IsA1NisLocalEquivalence r) :
    IsA1NisLocalEquivalence φ :=
  of_comp_right hr (hsplit ▸ id G)

/-- Every local object inverts a local equivalence: precomposition with a local
equivalence `φ : F ⟶ G` induces a bijection `(G ⟶ L) → (F ⟶ L)` for any
`L : LinearA1NisLocalPST`.

This is the point-wise statement that `φ ∈ W_loc` means `Hom(G, L) ≅ Hom(F, L)`
for all local `L`, which later feeds the universal-property formulation. -/
theorem inverted_by_local_object
    {category : SmCorQ (k := k)}
    {F G : LinearPST category}
    {φ : F ⟶ G}
    (hφ : IsA1NisLocalEquivalence φ)
    (L : LinearA1NisLocalPST category) :
    Function.Bijective (fun η : G ⟶ L.toLinearPST => φ ≫ η) :=
  hφ L

/-- The local-equivalence predicate is *exactly* the test against local objects:
`φ` is a local equivalence iff every `L : LinearA1NisLocalPST` inverts `φ`.

This is the definition unfolded as a biconditional. -/
theorem iff_inverted_by_local_objects
    {category : SmCorQ (k := k)}
    {F G : LinearPST category}
    (φ : F ⟶ G) :
    IsA1NisLocalEquivalence φ ↔
      ∀ L : LinearA1NisLocalPST category,
        Function.Bijective (fun η : G ⟶ L.toLinearPST => φ ≫ η) :=
  Iff.rfl

end IsA1NisLocalEquivalence

/-- The Nisnevich descent generator is an `A1`+Nisnevich-local equivalence. -/
theorem nisnevichDescentGenerator_isA1NisLocalEquivalence
    {category : SmCorQ (k := k)}
    (square : NisnevichDistinguishedSquareDataQ category) :
    IsA1NisLocalEquivalence
    (F := square.descentCompatiblePairObjectLinear)
      (G := QtrLinear (category := category) square.base)
    (square.nisnevichDescentGeneratorMapLinear) := by
  intro L
  let hDescent := ((IsA1NisLocal_iff_QtrLinear_local L.toLinearPST).mp L.isA1NisLocal).2
  constructor
  · intro η₁ η₂ hcomp
    let η₁P : (QtrLinear (category := category) square.base).toPST ⟶ L.toPST := η₁
    let η₂P : (QtrLinear (category := category) square.base).toPST ⟶ L.toPST := η₂
    let ηopen₁ : (QtrLinear (category := category) square.openPiece).toPST ⟶ L.toPST :=
      (QtrMap (category := category) square.openToBaseTransfer) ≫ η₁P
    let ηpatch₁ : (QtrLinear (category := category) square.patchPiece).toPST ⟶ L.toPST :=
      (QtrMap (category := category) square.patchToBaseTransfer) ≫ η₁P
    let ηopen₂ : (QtrLinear (category := category) square.openPiece).toPST ⟶ L.toPST :=
      (QtrMap (category := category) square.openToBaseTransfer) ≫ η₂P
    let ηpatch₂ : (QtrLinear (category := category) square.patchPiece).toPST ⟶ L.toPST :=
      (QtrMap (category := category) square.patchToBaseTransfer) ≫ η₂P
    have hcompat₁ :
        (QtrMap (category := category) square.overlapToOpenTransfer) ≫ ηopen₁ =
          (QtrMap (category := category) square.overlapToPatchTransfer) ≫ ηpatch₁ := by
      simpa [ηopen₁, ηpatch₁, Category.assoc] using
        (NisnevichDistinguishedSquareDataQ.baseSection_overlap_compatible
          (square := square) (F := L.toPST) (ηbase := η₁P))
    rcases hDescent square ηopen₁ ηpatch₁ hcompat₁ with ⟨ηbase, hbase, huniq⟩
    have hcompP :
        square.nisnevichDescentGeneratorMapLinear ≫ η₁P =
          square.nisnevichDescentGeneratorMapLinear ≫ η₂P := by
      simpa [η₁P, η₂P] using hcomp
    have hopenEq : ηopen₁ = ηopen₂ := by
      calc
        ηopen₁ = (QtrMap (category := category) square.openToBaseTransfer) ≫ η₁P := by
            rfl
        _ = (square.descentTargetOpenInclusion ≫
              square.descentCompatiblePairQuotientMap ≫
              square.nisnevichDescentGeneratorMapLinear) ≫ η₁P := by
            simpa [NisnevichDistinguishedSquareDataQ.descentTargetOpenInclusion_comp_quotient_comp_generatorLinear
              (square := square)]
        _ = (square.descentTargetOpenInclusion ≫
              square.descentCompatiblePairQuotientMap ≫
              square.nisnevichDescentGeneratorMapLinear) ≫ η₂P := by
            simpa [Category.assoc] using
              congrArg
                (fun t => (square.descentTargetOpenInclusion ≫
                    square.descentCompatiblePairQuotientMap) ≫ t)
                hcompP
        _ = (QtrMap (category := category) square.openToBaseTransfer) ≫ η₂P := by
            simpa [NisnevichDistinguishedSquareDataQ.descentTargetOpenInclusion_comp_quotient_comp_generatorLinear
              (square := square)]
        _ = ηopen₂ := by rfl
    have hpatchEq : ηpatch₁ = ηpatch₂ := by
      calc
        ηpatch₁ = (QtrMap (category := category) square.patchToBaseTransfer) ≫ η₁P := by
            rfl
        _ = (square.descentTargetPatchInclusion ≫
              square.descentCompatiblePairQuotientMap ≫
              square.nisnevichDescentGeneratorMapLinear) ≫ η₁P := by
            simpa [NisnevichDistinguishedSquareDataQ.descentTargetPatchInclusion_comp_quotient_comp_generatorLinear
              (square := square)]
        _ = (square.descentTargetPatchInclusion ≫
              square.descentCompatiblePairQuotientMap ≫
              square.nisnevichDescentGeneratorMapLinear) ≫ η₂P := by
            simpa [Category.assoc] using
              congrArg
                (fun t => (square.descentTargetPatchInclusion ≫
                    square.descentCompatiblePairQuotientMap) ≫ t)
                hcompP
        _ = (QtrMap (category := category) square.patchToBaseTransfer) ≫ η₂P := by
            simpa [NisnevichDistinguishedSquareDataQ.descentTargetPatchInclusion_comp_quotient_comp_generatorLinear
              (square := square)]
        _ = ηpatch₂ := by rfl
    have hη₁ : η₁P = ηbase := by
      apply huniq
      constructor <;> rfl
    have hη₂ : η₂P = ηbase := by
      apply huniq
      constructor
      · simpa [ηopen₂] using hopenEq.symm
      · simpa [ηpatch₂] using hpatchEq.symm
    simpa [η₁P, η₂P] using hη₁.trans hη₂.symm
  · intro η
    let ηopen : (QtrLinear (category := category) square.openPiece).toPST ⟶ L.toPST :=
      square.descentTargetOpenInclusion ≫
        square.descentCompatiblePairQuotientMap ≫ η
    let ηpatch : (QtrLinear (category := category) square.patchPiece).toPST ⟶ L.toPST :=
      square.descentTargetPatchInclusion ≫
        square.descentCompatiblePairQuotientMap ≫ η
    have hcompat :
        (QtrMap (category := category) square.overlapToOpenTransfer) ≫ ηopen =
          (QtrMap (category := category) square.overlapToPatchTransfer) ≫ ηpatch := by
      simpa [ηopen, ηpatch, Category.assoc] using
        (NisnevichDistinguishedSquareDataQ.descentCompatiblePairObject_overlap_compat
          (square := square) (L := L.toLinearPST) η)
    rcases hDescent square ηopen ηpatch hcompat with ⟨ηbase, hbase, _⟩
    have hηlegs :
        square.descentTargetOpenInclusion ≫
            square.descentCompatiblePairQuotientMap ≫ η = ηopen ∧
          square.descentTargetPatchInclusion ≫
            square.descentCompatiblePairQuotientMap ≫ η = ηpatch := by
      constructor <;> rfl
    have hgenlegs :
        square.descentTargetOpenInclusion ≫
            square.descentCompatiblePairQuotientMap ≫
            (square.nisnevichDescentGeneratorMapLinear ≫ ηbase) = ηopen ∧
          square.descentTargetPatchInclusion ≫
            square.descentCompatiblePairQuotientMap ≫
            (square.nisnevichDescentGeneratorMapLinear ≫ ηbase) = ηpatch := by
      constructor
      · calc
          square.descentTargetOpenInclusion ≫
              square.descentCompatiblePairQuotientMap ≫
              (square.nisnevichDescentGeneratorMapLinear ≫ ηbase)
            = (square.descentTargetOpenInclusion ≫
                square.descentCompatiblePairQuotientMap ≫
                square.nisnevichDescentGeneratorMapLinear) ≫ ηbase := by
                  simp [Category.assoc]
        _ = (QtrMap (category := category) square.openToBaseTransfer) ≫ ηbase := by
              simpa [NisnevichDistinguishedSquareDataQ.descentTargetOpenInclusion_comp_quotient_comp_generatorLinear
                (square := square)]
        _ = ηopen := by simpa [ηopen] using hbase.1
      · calc
          square.descentTargetPatchInclusion ≫
              square.descentCompatiblePairQuotientMap ≫
              (square.nisnevichDescentGeneratorMapLinear ≫ ηbase)
            = (square.descentTargetPatchInclusion ≫
                square.descentCompatiblePairQuotientMap ≫
                square.nisnevichDescentGeneratorMapLinear) ≫ ηbase := by
                  simp [Category.assoc]
        _ = (QtrMap (category := category) square.patchToBaseTransfer) ≫ ηbase := by
              simpa [NisnevichDistinguishedSquareDataQ.descentTargetPatchInclusion_comp_quotient_comp_generatorLinear
                (square := square)]
        _ = ηpatch := by simpa [ηpatch] using hbase.2
    rcases (NisnevichDistinguishedSquareDataQ.descentCompatiblePair_desc
      (square := square) (L := L.toLinearPST) (ηU := ηopen) (ηV := ηpatch) hcompat) with
      ⟨ξ, hξ, hξuniq⟩
    have hηeq : η = ξ := hξuniq η hηlegs
    have hgeneq : square.nisnevichDescentGeneratorMapLinear ≫ ηbase = ξ :=
      hξuniq (square.nisnevichDescentGeneratorMapLinear ≫ ηbase)
        hgenlegs
    refine ⟨ηbase, ?_⟩
    calc
      square.nisnevichDescentGeneratorMapLinear ≫ ηbase = ξ := hgeneq
      _ = η := hηeq.symm

/-- The representable `A1`-projection generator is an `A1`+Nisnevich-local
equivalence on the honest `LinearPST` surface. -/
theorem representableA1Projection_isA1NisLocalEquivalence
    {category : SmCorQ (k := k)}
    (X : Geometry.SmSchemeOver k)
    (D : FiniteIrreducibleComponentDecomposition (productWithA1 X)) :
    IsA1NisLocalEquivalence
      (F := QtrLinear (category := category) (productWithA1 X))
      (G := QtrLinear (category := category) X)
      (show QtrLinear (category := category) (productWithA1 X) ⟶
          QtrLinear (category := category) X from
        projectionToBase_QtrMapOfDecomposition category X D) := by
  intro L
  simpa using
    ((IsA1NisLocal_iff_QtrLinear_local L.toLinearPST).mp L.isA1NisLocal).1 X D

/-- Both basic geometric generator families land in `IsA1NisLocalEquivalence`.

These are the two fundamental generator maps from which the motivic
localization is built:

* **A¹ projection generators**: `Q_tr(X × A¹) → Q_tr(X)`.
* **Nisnevich descent generators**: `Comp(U,V;W) → Q_tr(X)` arising from a
  Nisnevich distinguished square.

Neither the localization functor nor motives are defined here; this is purely
the statement that the generators already constructed satisfy the
local-equivalence predicate. -/
theorem basicGenerators_areA1NisLocalEquivalences
    {category : SmCorQ (k := k)} :
    (∀ (X : Geometry.SmSchemeOver k)
       (D : FiniteIrreducibleComponentDecomposition (productWithA1 X)),
        IsA1NisLocalEquivalence
          (F := QtrLinear (category := category) (productWithA1 X))
          (G := QtrLinear (category := category) X)
          (projectionToBase_QtrMapOfDecomposition category X D)) ∧
    (∀ (square : NisnevichDistinguishedSquareDataQ category),
        IsA1NisLocalEquivalence
          (F := square.descentCompatiblePairObjectLinear)
          (G := QtrLinear (category := category) square.base)
          square.nisnevichDescentGeneratorMapLinear) :=
  ⟨fun X D => representableA1Projection_isA1NisLocalEquivalence X D,
   fun square => nisnevichDescentGenerator_isA1NisLocalEquivalence square⟩

/-- Canonical-route bundled linear presheaves with transfers that are both
`A1`-local and Nisnevich-local. -/
abbrev CanonicalA1NisLocalPST
    (composition : Boundary.CanonicalCompositionData (k := k)) :=
  LinearA1NisLocalPST (Boundary.canonicalCategory composition)

/-- Canonical-route local equivalences on `LinearPST (canonicalSmCorQ)`. -/
def IsCanonicalA1NisLocalEquivalence
    (composition : Boundary.CanonicalCompositionData (k := k))
    {F G : LinearPST (Boundary.canonicalCategory composition)}
    (φ : F ⟶ G) : Prop :=
  IsA1NisLocalEquivalence φ

/-- The representable `A1`-projection generator is a canonical
`A1`+Nisnevich-local equivalence. -/
theorem representableA1Projection_isCanonicalA1NisLocalEquivalence
    (composition : Boundary.CanonicalCompositionData (k := k))
    (X : Geometry.SmSchemeOver k)
    (D : FiniteIrreducibleComponentDecomposition (productWithA1 X)) :
    IsCanonicalA1NisLocalEquivalence composition
      (F := QtrLinear (category := Boundary.canonicalCategory composition) (productWithA1 X))
      (G := QtrLinear (category := Boundary.canonicalCategory composition) X)
      (show QtrLinear (category := Boundary.canonicalCategory composition) (productWithA1 X) ⟶
          QtrLinear (category := Boundary.canonicalCategory composition) X from
        projectionToBase_QtrMapOfDecomposition
          (Boundary.canonicalCategory composition) X D) :=
  representableA1Projection_isA1NisLocalEquivalence
    (category := Boundary.canonicalCategory composition) X D

/-- The canonical Nisnevich descent generator is a canonical `A1`+Nisnevich-local
equivalence. -/
theorem canonicalNisnevichDescentGenerator_isCanonicalA1NisLocalEquivalence
    (composition : Boundary.CanonicalCompositionData (k := k))
    (square : NisnevichDistinguishedSquareDataQ (Boundary.canonicalCategory composition)) :
    IsCanonicalA1NisLocalEquivalence composition
      (F := square.descentCompatiblePairObjectLinear)
      (G := QtrLinear (category := Boundary.canonicalCategory composition) square.base)
      square.nisnevichDescentGeneratorMapLinear :=
  nisnevichDescentGenerator_isA1NisLocalEquivalence
    (category := Boundary.canonicalCategory composition) square

/-- On the canonical route, both basic generator families land in the canonical
`A1`+Nisnevich local-equivalence class. -/
theorem canonicalBasicGenerators_areA1NisLocalEquivalences
    (composition : Boundary.CanonicalCompositionData (k := k)) :
    (∀ (X : Geometry.SmSchemeOver k)
       (D : FiniteIrreducibleComponentDecomposition (productWithA1 X)),
        IsCanonicalA1NisLocalEquivalence composition
          (F := QtrLinear (category := Boundary.canonicalCategory composition) (productWithA1 X))
          (G := QtrLinear (category := Boundary.canonicalCategory composition) X)
          (projectionToBase_QtrMapOfDecomposition
            (Boundary.canonicalCategory composition) X D)) ∧
    (∀ (square : NisnevichDistinguishedSquareDataQ (Boundary.canonicalCategory composition)),
        IsCanonicalA1NisLocalEquivalence composition
          (F := square.descentCompatiblePairObjectLinear)
          (G := QtrLinear (category := Boundary.canonicalCategory composition) square.base)
          square.nisnevichDescentGeneratorMapLinear) :=
  ⟨fun X D => representableA1Projection_isCanonicalA1NisLocalEquivalence composition X D,
   fun square => canonicalNisnevichDescentGenerator_isCanonicalA1NisLocalEquivalence
     composition square⟩

/-- Primitive canonical-route `A1` and Nisnevich generators over
`canonicalSmCorQ`. -/
inductive CanonicalA1NisGenerator
    (composition : Boundary.CanonicalCompositionData (k := k)) where
  | a1Projection (X : Geometry.SmSchemeOver k)
      (D : FiniteIrreducibleComponentDecomposition (productWithA1 X))
  | nisnevichDescent
      (square : NisnevichDistinguishedSquareDataQ
        (Boundary.canonicalCategory composition))

/-- The canonical generator presentation for the `A1` projections and
Nisnevich descent maps over `canonicalSmCorQ`. -/
def canonicalA1NisGenerators
    (composition : Boundary.CanonicalCompositionData (k := k)) :
    LocalizingMorphismPresentationQ (Boundary.canonicalCategory composition) where
  Generator := CanonicalA1NisGenerator composition
  data := fun
    | .a1Projection X D =>
        ⟨Qtr (category := Boundary.canonicalCategory composition) (productWithA1 X),
          Qtr (category := Boundary.canonicalCategory composition) X,
          projectionToBase_QtrMapOfDecomposition
            (Boundary.canonicalCategory composition) X D⟩
    | .nisnevichDescent square =>
        ⟨square.descentCompatiblePairObject,
          Qtr (category := Boundary.canonicalCategory composition) square.base,
          square.nisnevichDescentGeneratorMapCanonical⟩

/-- The canonical `W_{A1,Nis}` local-equivalence predicate on
`LinearPST (canonicalSmCorQ)`, expressed through the Bousfield-`W` class of the
bundled canonical local objects. -/
def canonicalA1NisLocalEquivalences
    (composition : Boundary.CanonicalCompositionData (k := k))
    {F G : LinearPST (Boundary.canonicalCategory composition)}
    (φ : F ⟶ G) : Prop :=
  Localization.LeftBousfield.W
    (· ∈ Set.range
      (LinearA1NisLocalPST.inclusion (Boundary.canonicalCategory composition)).obj) φ

/-- The generated canonical weak-equivalence class
`W_{A1,Nis}^{can} = \langle X × A1 → X, \text{Nis descent} \rangle`. -/
def canonicalA1NisWeakEquivalences
    (composition : Boundary.CanonicalCompositionData (k := k))
    {F G : PST (Boundary.canonicalCategory composition)}
    (φ : F ⟶ G) : Prop :=
  Nonempty (GeneratedWeakEquivalenceQ (canonicalA1NisGenerators composition) φ)

/-- The saturated canonical weak-equivalence class generated by the primitive
`A1` projections and Nisnevich descent maps.

On the canonical route this saturation is taken semantically, via the same
left-Bousfield `W`-construction used for the honest localization object.  Thus
`canonicalA1NisSaturatedWeakEquivalences` is the public saturated class, while
`canonicalA1NisWeakEquivalences` remains the proof-relevant raw syntax of
generator composites. -/
def canonicalA1NisSaturatedWeakEquivalences
    (composition : Boundary.CanonicalCompositionData (k := k))
    {F G : LinearPST (Boundary.canonicalCategory composition)}
    (φ : F ⟶ G) : Prop :=
  canonicalA1NisLocalEquivalences composition φ

private def canonicalA1NisLocalEquivalencesProperty
    (composition : Boundary.CanonicalCompositionData (k := k)) :
    MorphismProperty (LinearPST (Boundary.canonicalCategory composition)) :=
  fun _ _ φ => canonicalA1NisLocalEquivalences composition φ

private def canonicalA1NisWeakEquivalencesProperty
    (composition : Boundary.CanonicalCompositionData (k := k)) :
    MorphismProperty (LinearPST (Boundary.canonicalCategory composition)) :=
  fun F G φ =>
    canonicalA1NisWeakEquivalences composition (F := F.toPST) (G := G.toPST) φ

private def canonicalA1NisSaturatedWeakEquivalencesProperty
    (composition : Boundary.CanonicalCompositionData (k := k)) :
    MorphismProperty (LinearPST (Boundary.canonicalCategory composition)) :=
  fun _ _ φ => canonicalA1NisSaturatedWeakEquivalences composition φ

/-- The honest canonical `A1`/Nisnevich localization of
`LinearPST (canonicalSmCorQ)`, formed by Mathlib's localization construction at
the canonical local-equivalence class. -/
abbrev canonicalA1NisLocalization
    (composition : Boundary.CanonicalCompositionData (k := k)) :=
  (canonicalA1NisLocalEquivalencesProperty composition).Localization

/-- The canonical localization functor
`LinearPST (canonicalSmCorQ) ⥤ canonicalA1NisLocalization`. -/
def canonicalA1NisLocalizationFunctor
    (composition : Boundary.CanonicalCompositionData (k := k)) :
    LinearPST (Boundary.canonicalCategory composition) ⥤
      canonicalA1NisLocalization composition :=
  (canonicalA1NisLocalEquivalencesProperty composition).Q

instance canonicalA1NisLocalizationFunctor_isLocalization
    (composition : Boundary.CanonicalCompositionData (k := k)) :
    (canonicalA1NisLocalizationFunctor composition).IsLocalization
      (canonicalA1NisLocalEquivalencesProperty composition) := by
  dsimp [canonicalA1NisLocalizationFunctor, canonicalA1NisLocalization]
  infer_instance

theorem canonicalA1NisLocalEquivalences_iff
    (composition : Boundary.CanonicalCompositionData (k := k))
    {F G : LinearPST (Boundary.canonicalCategory composition)}
    (φ : F ⟶ G) :
    canonicalA1NisLocalEquivalences composition φ ↔
      IsCanonicalA1NisLocalEquivalence composition φ := by
  constructor
  · intro hφ L
    exact hφ ((LinearA1NisLocalPST.inclusion
      (Boundary.canonicalCategory composition)).obj L) ⟨L, rfl⟩
  · intro hφ Z ⟨L, hL⟩
    rw [← hL]
    exact hφ L

/-- Universal property of the canonical `A1`/Nisnevich localization: for every
target category `D`, precomposition with the canonical localization functor is
an equivalence from functors out of the localization to functors that invert
the canonical local-equivalence class. -/
def canonicalA1NisLocalization_universalProperty
    (composition : Boundary.CanonicalCompositionData (k := k))
    (D : Type*) [Category D] :
    (canonicalA1NisLocalization composition ⥤ D) ≌
      (canonicalA1NisLocalEquivalencesProperty composition).FunctorsInverting D :=
  CategoryTheory.Localization.functorEquivalence
    (canonicalA1NisLocalizationFunctor composition)
    (canonicalA1NisLocalEquivalencesProperty composition)
    D

private theorem generatedWeakEquivalence_invertedByCanonicalLocal
    (composition : Boundary.CanonicalCompositionData (k := k))
    {F G : PST (Boundary.canonicalCategory composition)}
    {φ : F ⟶ G}
    (hφ : GeneratedWeakEquivalenceQ (canonicalA1NisGenerators composition) φ) :
    ∀ (L : CanonicalA1NisLocalPST composition),
      Function.Bijective (fun η : G ⟶ L.toPST => φ ≫ η) := by
  induction hφ with
  | ofGenerator g =>
      cases g with
      | a1Projection X D =>
          intro L
          have hloc :
              canonicalA1NisLocalEquivalences composition
                (F := QtrLinear (category := Boundary.canonicalCategory composition) (productWithA1 X))
                (G := QtrLinear (category := Boundary.canonicalCategory composition) X)
                (show QtrLinear (category := Boundary.canonicalCategory composition) (productWithA1 X) ⟶
                    QtrLinear (category := Boundary.canonicalCategory composition) X from
                  projectionToBase_QtrMapOfDecomposition
                    (Boundary.canonicalCategory composition) X D) := by
            rw [canonicalA1NisLocalEquivalences_iff]
            exact representableA1Projection_isCanonicalA1NisLocalEquivalence composition X D
          simpa using hloc
            ((LinearA1NisLocalPST.inclusion (Boundary.canonicalCategory composition)).obj L)
            ⟨L, rfl⟩
      | nisnevichDescent square =>
          intro L
          have hloc :
              canonicalA1NisLocalEquivalences composition
                (F := square.descentCompatiblePairObjectLinear)
                (G := QtrLinear (category := Boundary.canonicalCategory composition) square.base)
                square.nisnevichDescentGeneratorMapLinear := by
            rw [canonicalA1NisLocalEquivalences_iff]
            exact canonicalNisnevichDescentGenerator_isCanonicalA1NisLocalEquivalence
              composition square
          simpa [NisnevichDistinguishedSquareDataQ.nisnevichDescentGeneratorMapLinear,
            NisnevichDistinguishedSquareDataQ.nisnevichDescentGeneratorMapCanonical] using
            hloc ((LinearA1NisLocalPST.inclusion (Boundary.canonicalCategory composition)).obj L)
              ⟨L, rfl⟩
  | id X =>
      intro L
      constructor
      · intro η₁ η₂ hη
        simpa using hη
      · intro η
        refine ⟨η, ?_⟩
        simp
  | comp hf hg ihf ihg =>
      intro L
      rename_i X Y Z f g
      let bf := ihf L
      let bg := ihg L
      constructor
      · intro η₁ η₂ hη
        apply bg.1
        apply bf.1
        simpa [Category.assoc] using hη
      · intro η
        rcases bf.2 η with ⟨θ, hθ⟩
        rcases bg.2 θ with ⟨μ, hμ⟩
        refine ⟨μ, ?_⟩
        calc
          (fun η => (f ≫ g) ≫ η) μ = f ≫ ((fun η => g ≫ η) μ) := by
            simp [Category.assoc]
          _ = f ≫ θ := by rw [hμ]
          _ = η := hθ

/-- Every generator-built canonical weak equivalence between linear presheaves
is already a canonical local equivalence. -/
theorem canonicalA1NisWeakEquivalences_le_localEquivalences
    (composition : Boundary.CanonicalCompositionData (k := k)) :
    ∀ {F G : LinearPST (Boundary.canonicalCategory composition)} (φ : F ⟶ G),
      canonicalA1NisWeakEquivalences composition (F := F.toPST) (G := G.toPST) φ →
        canonicalA1NisLocalEquivalences composition φ := by
  intro F G φ hφ
  rcases hφ with ⟨hφ⟩
  intro Z hZ
  rcases hZ with ⟨L, rfl⟩
  simpa using generatedWeakEquivalence_invertedByCanonicalLocal composition hφ L

/-- The raw generator-built class sits inside the saturated canonical class. -/
theorem canonicalA1NisWeakEquivalences_le_saturated
    (composition : Boundary.CanonicalCompositionData (k := k)) :
    ∀ {F G : LinearPST (Boundary.canonicalCategory composition)} (φ : F ⟶ G),
      canonicalA1NisWeakEquivalences composition (F := F.toPST) (G := G.toPST) φ →
        canonicalA1NisSaturatedWeakEquivalences composition φ := by
  intro F G φ hφ
  exact canonicalA1NisWeakEquivalences_le_localEquivalences composition φ hφ

/-- The saturated canonical generated class is already a local-equivalence
class on the canonical route. -/
theorem canonicalA1NisSaturatedWeakEquivalences_le_localEquivalences
    (composition : Boundary.CanonicalCompositionData (k := k)) :
    ∀ {F G : LinearPST (Boundary.canonicalCategory composition)} (φ : F ⟶ G),
      canonicalA1NisSaturatedWeakEquivalences composition φ →
        canonicalA1NisLocalEquivalences composition φ := by
  intro F G φ hφ
  exact hφ

/-- Conversely, the canonical local-equivalence class is exactly the saturated
generated class. -/
theorem canonicalA1NisLocalEquivalences_le_saturatedWeakEquivalences
    (composition : Boundary.CanonicalCompositionData (k := k)) :
    ∀ {F G : LinearPST (Boundary.canonicalCategory composition)} (φ : F ⟶ G),
      canonicalA1NisLocalEquivalences composition φ →
        canonicalA1NisSaturatedWeakEquivalences composition φ := by
  intro F G φ hφ
  exact hφ

/-- The saturated generated class and the canonical local-equivalence class
coincide on the canonical route. -/
theorem canonicalA1NisSaturatedWeakEquivalences_eq_localEquivalences
    (composition : Boundary.CanonicalCompositionData (k := k)) :
    ∀ {F G : LinearPST (Boundary.canonicalCategory composition)} (φ : F ⟶ G),
      canonicalA1NisSaturatedWeakEquivalences composition φ ↔
        canonicalA1NisLocalEquivalences composition φ := by
  intro F G φ
  constructor
  · exact canonicalA1NisSaturatedWeakEquivalences_le_localEquivalences composition φ
  · exact canonicalA1NisLocalEquivalences_le_saturatedWeakEquivalences composition φ

/-- Exact remaining reverse comparison obligation: the current generated class
contains only identities, compositions, and primitive generators, while the
local-equivalence class used for the actual localization is already saturated by
Mathlib's localization API.  Any proof of this proposition must therefore show
that the generated class is sufficiently saturated on the canonical route. -/
def canonicalA1NisLocalEquivalences_le_generatedWeakEquivalences
    (composition : Boundary.CanonicalCompositionData (k := k)) : Prop :=
  ∀ {F G : LinearPST (Boundary.canonicalCategory composition)} (φ : F ⟶ G),
    canonicalA1NisLocalEquivalences composition φ →
      canonicalA1NisWeakEquivalences composition (F := F.toPST) (G := G.toPST) φ

/-- If the reverse saturation obligation is discharged, the generator-built and
local-equivalence presentations coincide on the canonical route. -/
theorem canonicalA1NisWeakEquivalences_eq_localEquivalences
    (composition : Boundary.CanonicalCompositionData (k := k))
    (hrev : canonicalA1NisLocalEquivalences_le_generatedWeakEquivalences composition) :
    ∀ {F G : LinearPST (Boundary.canonicalCategory composition)} (φ : F ⟶ G),
      canonicalA1NisWeakEquivalences composition (F := F.toPST) (G := G.toPST) φ ↔
        canonicalA1NisLocalEquivalences composition φ := by
  intro F G φ
  constructor
  · exact canonicalA1NisWeakEquivalences_le_localEquivalences composition φ
  · exact hrev φ

/-- If the reverse inclusion is discharged, the universal property of the
canonical localization can be restated using the generator-built weak
equivalence class. -/
def canonicalA1NisLocalization_universalProperty_generated
    (composition : Boundary.CanonicalCompositionData (k := k))
    (hrev : canonicalA1NisLocalEquivalences_le_generatedWeakEquivalences composition)
    (D : Type*) [Category D] :
    (canonicalA1NisLocalization composition ⥤ D) ≌
      (canonicalA1NisWeakEquivalencesProperty composition).FunctorsInverting D := by
  let hgen_le_hloc : canonicalA1NisWeakEquivalencesProperty composition ≤
      canonicalA1NisLocalEquivalencesProperty composition := by
    intro F G φ hφ
    exact canonicalA1NisWeakEquivalences_le_localEquivalences composition φ hφ
  let hloc_le_hgen : canonicalA1NisLocalEquivalencesProperty composition ≤
      canonicalA1NisWeakEquivalencesProperty composition := by
    intro F G φ hφ
    exact hrev φ hφ
  let transport :
      (canonicalA1NisLocalEquivalencesProperty composition).FunctorsInverting D ≌
        (canonicalA1NisWeakEquivalencesProperty composition).FunctorsInverting D := by
    refine
      { functor :=
          { obj := fun F =>
              MorphismProperty.FunctorsInverting.mk F.1
                (MorphismProperty.IsInvertedBy.of_le _ _ F.1 F.2 hgen_le_hloc)
            map := fun η => η }
        inverse :=
          { obj := fun F =>
              MorphismProperty.FunctorsInverting.mk F.1
                (MorphismProperty.IsInvertedBy.of_le _ _ F.1 F.2 hloc_le_hgen)
            map := fun η => η }
        unitIso := NatIso.ofComponents (fun F => Iso.refl F) (fun η => by
          ext X
          change η.app X ≫ 𝟙 _ = 𝟙 _ ≫ η.app X
          simpa using ((Category.comp_id (η.app X)).trans (Category.id_comp (η.app X)).symm))
        counitIso := NatIso.ofComponents (fun F => Iso.refl F) (fun η => by
          ext X
          change η.app X ≫ 𝟙 _ = 𝟙 _ ≫ η.app X
          simpa using ((Category.comp_id (η.app X)).trans (Category.id_comp (η.app X)).symm))
        functor_unitIso_comp := by
          intro F
          ext X
          change 𝟙 _ ≫ 𝟙 _ = 𝟙 _
          simp }
  let uprop :
      (canonicalA1NisLocalization composition ⥤ D) ≌
        (canonicalA1NisLocalEquivalencesProperty composition).FunctorsInverting D :=
    canonicalA1NisLocalization_universalProperty composition D
  exact uprop.trans transport

/-- Unconditional universal property of the canonical localization restated
using the saturated generated class. -/
def canonicalA1NisLocalization_universalProperty_saturatedGenerated
    (composition : Boundary.CanonicalCompositionData (k := k))
    (D : Type*) [Category D] :
    (canonicalA1NisLocalization composition ⥤ D) ≌
      (canonicalA1NisSaturatedWeakEquivalencesProperty composition).FunctorsInverting D :=
  canonicalA1NisLocalization_universalProperty composition D

/-- The primitive canonical `A1` and Nisnevich generator maps are members of
the generated weak-equivalence class `W_{A1,Nis}^{can}`. -/
theorem canonicalA1NisGenerators_generate_canonicalA1NisWeakEquivalences
    (composition : Boundary.CanonicalCompositionData (k := k)) :
    (∀ (X : Geometry.SmSchemeOver k)
       (D : FiniteIrreducibleComponentDecomposition (productWithA1 X)),
        canonicalA1NisWeakEquivalences composition
          (projectionToBase_QtrMapOfDecomposition
            (Boundary.canonicalCategory composition) X D)) ∧
    (∀ (square : NisnevichDistinguishedSquareDataQ (Boundary.canonicalCategory composition)),
        canonicalA1NisWeakEquivalences composition
          square.nisnevichDescentGeneratorMapCanonical) := by
  constructor
  · intro X D
    change canonicalA1NisWeakEquivalences composition
      ((canonicalA1NisGenerators composition).map
        (CanonicalA1NisGenerator.a1Projection X D))
    exact ⟨GeneratedWeakEquivalenceQ.ofGenerator
      (presentation := canonicalA1NisGenerators composition)
      (CanonicalA1NisGenerator.a1Projection X D)⟩
  · intro square
    change canonicalA1NisWeakEquivalences composition
      ((canonicalA1NisGenerators composition).map
        (CanonicalA1NisGenerator.nisnevichDescent square))
    exact ⟨GeneratedWeakEquivalenceQ.ofGenerator
      (presentation := canonicalA1NisGenerators composition)
      (CanonicalA1NisGenerator.nisnevichDescent square)⟩

/-- The primitive canonical `A1` and Nisnevich generators already lie in the
canonical local-equivalence class seen by canonical local objects. -/
theorem canonicalA1NisGenerators_areCanonicalLocalEquivalences
    (composition : Boundary.CanonicalCompositionData (k := k)) :
    (∀ (X : Geometry.SmSchemeOver k)
       (D : FiniteIrreducibleComponentDecomposition (productWithA1 X)),
        canonicalA1NisLocalEquivalences composition
          (F := QtrLinear (category := Boundary.canonicalCategory composition) (productWithA1 X))
          (G := QtrLinear (category := Boundary.canonicalCategory composition) X)
          (show QtrLinear (category := Boundary.canonicalCategory composition) (productWithA1 X) ⟶
              QtrLinear (category := Boundary.canonicalCategory composition) X from
            projectionToBase_QtrMapOfDecomposition
              (Boundary.canonicalCategory composition) X D)) ∧
    (∀ (square : NisnevichDistinguishedSquareDataQ (Boundary.canonicalCategory composition)),
        canonicalA1NisLocalEquivalences composition
          (F := square.descentCompatiblePairObjectLinear)
          (G := QtrLinear (category := Boundary.canonicalCategory composition) square.base)
          square.nisnevichDescentGeneratorMapLinear) := by
  constructor
  · intro X D
    rw [canonicalA1NisLocalEquivalences_iff]
    exact representableA1Projection_isCanonicalA1NisLocalEquivalence composition X D
  · intro square
    rw [canonicalA1NisLocalEquivalences_iff]
    exact canonicalNisnevichDescentGenerator_isCanonicalA1NisLocalEquivalence
      composition square

/-- The primitive canonical `A1` and Nisnevich generators already lie in the
public saturated weak-equivalence class on the canonical route. -/
theorem canonicalA1NisGenerators_areSaturatedWeakEquivalences
    (composition : Boundary.CanonicalCompositionData (k := k)) :
    (∀ (X : Geometry.SmSchemeOver k)
       (D : FiniteIrreducibleComponentDecomposition (productWithA1 X)),
        canonicalA1NisSaturatedWeakEquivalences composition
          (F := QtrLinear (category := Boundary.canonicalCategory composition) (productWithA1 X))
          (G := QtrLinear (category := Boundary.canonicalCategory composition) X)
          (show QtrLinear (category := Boundary.canonicalCategory composition) (productWithA1 X) ⟶
              QtrLinear (category := Boundary.canonicalCategory composition) X from
            projectionToBase_QtrMapOfDecomposition
              (Boundary.canonicalCategory composition) X D)) ∧
    (∀ (square : NisnevichDistinguishedSquareDataQ (Boundary.canonicalCategory composition)),
        canonicalA1NisSaturatedWeakEquivalences composition
          (F := square.descentCompatiblePairObjectLinear)
          (G := QtrLinear (category := Boundary.canonicalCategory composition) square.base)
          square.nisnevichDescentGeneratorMapLinear) := by
  simpa [canonicalA1NisSaturatedWeakEquivalences_eq_localEquivalences]
    using canonicalA1NisGenerators_areCanonicalLocalEquivalences composition

/-- Alignment: `IsA1NisLocalEquivalence` is exactly
`Localization.LeftBousfield.W` for objects in the essential image of
`LinearA1NisLocalPST.inclusion`.

This is the bridge between our predicate definition and Mathlib's Bousfield
localization API.  It makes `Localization.LeftBousfield.isLocalization`
applicable directly once a sheafification adjunction is provided. -/
theorem isA1NisLocalEquivalence_iff_bousfieldW
    {category : SmCorQ (k := k)}
    {F G : LinearPST category}
    (φ : F ⟶ G) :
    IsA1NisLocalEquivalence φ ↔
      Localization.LeftBousfield.W
        (· ∈ Set.range (LinearA1NisLocalPST.inclusion category).obj) φ := by
  constructor
  · intro hφ Z ⟨L, hL⟩
    rw [← hL]
    exact hφ L
  · intro hφ L
    exact hφ ((LinearA1NisLocalPST.inclusion category).obj L) ⟨L, rfl⟩

/-- **Conditional localization theorem**: given any sheafification functor
`L : LinearPST category ⥤ LinearA1NisLocalPST category` equipped with an
adjunction `L ⊣ LinearA1NisLocalPST.inclusion`, the functor `L` is a
localization of `LinearPST` at `LeftBousfield.W` (equivalently, at
`IsA1NisLocalEquivalence` by `isA1NisLocalEquivalence_iff_bousfieldW`).

The proof is immediate from `Localization.LeftBousfield.isLocalization`,
using the already-proved `inclusion_full` and `inclusion_faithful` instances.

**This theorem does not claim that such an adjunction exists.**  Constructing
the A¹/Nis sheafification functor — the left adjoint to the inclusion — is the
remaining Step 2 mathematical blocker.  Once that adjunction is supplied,
the localization theorem is complete. -/
theorem a1NisLocalization_of_adj
    {category : SmCorQ (k := k)}
    (L : LinearPST category ⥤ LinearA1NisLocalPST category)
    (adj : L ⊣ LinearA1NisLocalPST.inclusion category) :
    L.IsLocalization
      (Localization.LeftBousfield.W
        (· ∈ Set.range (LinearA1NisLocalPST.inclusion category).obj)) :=
  Localization.LeftBousfield.isLocalization adj

/-- Bundled presheaves with transfers satisfying both `A1` and Nisnevich
locality. -/
def A1NisLocalPST (category : SmCorQ (k := k)) :=
  { F : PST category // IsA1NisLocal F }

namespace A1NisLocalPST

/-- Forget the locality proofs and view a bundled object as a presheaf with
transfers. -/
abbrev toPST {category : SmCorQ (k := k)}
    (F : A1NisLocalPST category) : PST category :=
  F.1

instance {category : SmCorQ (k := k)} : Coe (A1NisLocalPST category) (PST category) where
  coe F := F.toPST

instance {category : SmCorQ (k := k)} : Category (A1NisLocalPST category) := by
  letI := SmCorQCat category
  exact InducedCategory.category A1NisLocalPST.toPST

/-- Morphisms in `A1NisLocalPST` are exactly ordinary `PST` morphisms between
the underlying presheaves. -/
@[simp] theorem Hom_def {category : SmCorQ (k := k)}
    (F G : A1NisLocalPST category) :
    (F ⟶ G) = (F.toPST ⟶ G.toPST) :=
  rfl

/-- The forgetful functor from bundled `A1`+Nisnevich-local presheaves with
transfers to ordinary presheaves with transfers. -/
def forgetToPST {category : SmCorQ (k := k)} : A1NisLocalPST category ⥤ PST category := by
  letI := SmCorQCat category
  exact inducedFunctor A1NisLocalPST.toPST

@[simp] theorem forgetToPST_obj {category : SmCorQ (k := k)}
    (F : A1NisLocalPST category) :
    (forgetToPST (category := category)).obj F = F.toPST :=
  rfl

@[simp] theorem forgetToPST_map {category : SmCorQ (k := k)}
    {F G : A1NisLocalPST category} (f : F ⟶ G) :
    (forgetToPST (category := category)).map f = f :=
  rfl

instance forgetToPST_full {category : SmCorQ (k := k)} :
    (forgetToPST (category := category)).Full := by
  letI := SmCorQCat category
  change (inducedFunctor A1NisLocalPST.toPST).Full
  infer_instance

instance forgetToPST_faithful {category : SmCorQ (k := k)} :
    (forgetToPST (category := category)).Faithful := by
  letI := SmCorQCat category
  change (inducedFunctor A1NisLocalPST.toPST).Faithful
  infer_instance

/-- An ordinary presheaf with transfers is `A1`+Nisnevich-local exactly when it
lies in the image of the forgetful functor from bundled local objects. -/
theorem exists_obj_forgetToPST_iff {category : SmCorQ (k := k)}
    (F : PST category) :
    (∃ G : A1NisLocalPST category, (forgetToPST (category := category)).obj G = F) ↔
      IsA1NisLocal F := by
  constructor
  · rintro ⟨G, hG⟩
    simpa [forgetToPST] using hG ▸ G.2
  · intro hF
    exact ⟨⟨F, hF⟩, rfl⟩

/-- An ordinary presheaf with transfers underlies a bundled object of
`A1NisLocalPST` exactly when it is both `A1`-local and Nisnevich-local. -/
theorem exists_obj_forgetToPST_iff_localities {category : SmCorQ (k := k)}
    (F : PST category) :
    (∃ G : A1NisLocalPST category, (forgetToPST (category := category)).obj G = F) ↔
      IsA1Local F ∧ IsNisnevichLocal F := by
  rw [exists_obj_forgetToPST_iff, IsA1NisLocal.iff_localities]

/-- A bundled `A1`+Nisnevich-local presheaf carries its `A1`-locality proof. -/
theorem isA1Local {category : SmCorQ (k := k)}
    (F : A1NisLocalPST category) : IsA1Local F.toPST :=
  F.2.1

/-- A bundled `A1`+Nisnevich-local presheaf carries its Nisnevich-locality
proof. -/
theorem isNisnevichLocal {category : SmCorQ (k := k)}
    (F : A1NisLocalPST category) : IsNisnevichLocal F.toPST :=
  F.2.2

end A1NisLocalPST

end

end Boundary
