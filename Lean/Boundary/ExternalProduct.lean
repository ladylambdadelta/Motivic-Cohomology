import Boundary.CompositionCategory
import Boundary.PrimeSupport
import Boundary.ComponentGeometry
import Boundary.SupportEquivalence

/-!
# External Products of Finite Correspondences

This file corrects the prime-level target of external products.

For represented prime supports `P : X1 ⟶ Y1` and `Q : X2 ⟶ Y2`, the raw
product support lives over the full source product
`(X1 x_k X2) x_k (Y1 x_k Y2)`. Decomposing that raw support by irreducible
components then produces a finite sum of represented prime supports on the
product source and product target.

Accordingly, the prime-level external product lands in finite correspondences,
not in represented prime supports.
-/

universe u

variable {k : Type u} [Field k] [PerfectField k]

open AlgebraicGeometry CategoryTheory Limits

namespace Boundary

noncomputable section

/-- One irreducible component of a scheme, realized as an integral closed
subscheme together with the fact that its image is a topological irreducible
component. This is the raw-scheme analogue of `SourceIrreducibleComponent`.
-/
structure IrreducibleComponentAsIntClosedSubscheme (X : Scheme.{u}) where
  carrier : IntClosedSubscheme X
  isIrreducibleComponent :
    Set.range carrier.inclusion.base ∈ irreducibleComponents X

/-- A finite decomposition of an arbitrary scheme by integral closed
subschemes whose images are genuine irreducible components. Unlike
`FiniteIrreducibleComponentDecomposition`, this works for plain schemes rather
than only for smooth schemes over the base field. -/
structure FiniteIntegralClosedComponentDecomposition (X : Scheme.{u}) where
  index : Type u
  fintypeIndex : Fintype index
  decidableEqIndex : DecidableEq index
  component : index → IrreducibleComponentAsIntClosedSubscheme X
  covers :
    ∀ x : X.carrier,
      ∃ i : index, x ∈ Set.range ((component i).carrier.inclusion.base)
  irredundant : Function.Injective component

namespace FiniteIntegralClosedComponentDecomposition

variable {X : Scheme.{u}}

instance (decomposition : FiniteIntegralClosedComponentDecomposition X) :
    Fintype decomposition.index := decomposition.fintypeIndex

instance (decomposition : FiniteIntegralClosedComponentDecomposition X) :
    DecidableEq decomposition.index := decomposition.decidableEqIndex

end FiniteIntegralClosedComponentDecomposition

private theorem mem_irreducibleComponents_image_of_homeomorph
    {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]
    (e : X ≃ₜ Y)
    {s : Set X}
    (hs : s ∈ irreducibleComponents X) :
    e '' s ∈ irreducibleComponents Y := by
  rw [irreducibleComponents_eq_maximals_closed] at hs ⊢
  refine ⟨?_, ?_⟩
  · exact ⟨e.isClosedMap s hs.1.1, hs.1.2.image e e.continuous.continuousOn⟩
  · intro t ht hsubset
    have hpre_closed_irred : IsClosed (e.symm '' t) ∧ IsIrreducible (e.symm '' t) := by
      exact ⟨e.symm.isClosedMap t ht.1, ht.2.image e.symm e.symm.continuous.continuousOn⟩
    have hs_subset_pre : s ⊆ e.symm '' t := by
      intro x hx
      exact ⟨e x, hsubset ⟨x, hx, rfl⟩, by simp⟩
    have hpre_subset : e.symm '' t ⊆ s := hs.2 hpre_closed_irred hs_subset_pre
    have hpre_eq : e.symm '' t = s := Set.Subset.antisymm hpre_subset hs_subset_pre
    intro y hy
    have hy_pre : e.symm y ∈ e.symm '' t := ⟨y, hy, rfl⟩
    have hy_source : e.symm y ∈ s := by
      simpa [hpre_eq] using hy_pre
    exact ⟨e.symm y, hy_source, by simp⟩

namespace IntClosedSubscheme

/-- Transport an integral closed subscheme across an ambient scheme
isomorphism by composing its closed immersion with the isomorphism. -/
def transport {X Y : Scheme.{u}} (e : X ≅ Y) (Z : IntClosedSubscheme X) :
    IntClosedSubscheme Y where
  scheme := Z.scheme
  inclusion := Z.inclusion ≫ e.hom
  isClosedImm := by
    letI : IsClosedImmersion Z.inclusion := Z.isClosedImm
    infer_instance
  isIntegral := Z.isIntegral

@[simp] theorem transport_symm_transport
    {X Y : Scheme.{u}} (e : X ≅ Y) (Z : IntClosedSubscheme X) :
    transport e.symm (transport e Z) = Z := by
  cases Z
  simp [transport, Category.assoc]

theorem transport_injective {X Y : Scheme.{u}} (e : X ≅ Y) :
    Function.Injective (transport e) := by
  intro Z Z' h
  have h' := congrArg (transport e.symm) h
  simpa using h'

@[simp] theorem range_transport_inclusion
    {X Y : Scheme.{u}} (e : X ≅ Y) (Z : IntClosedSubscheme X) :
    Set.range (transport e Z).inclusion.base =
      e.hom.homeomorph '' Set.range Z.inclusion.base := by
  ext y
  constructor
  · rintro ⟨z, rfl⟩
    exact ⟨Z.inclusion.base z, ⟨z, rfl⟩, rfl⟩
  · rintro ⟨x, ⟨z, rfl⟩, hxy⟩
    refine ⟨z, ?_⟩
    simpa [transport, Category.assoc] using hxy

end IntClosedSubscheme

namespace IrreducibleComponentAsIntClosedSubscheme

/-- Transport an irreducible-component realization across an ambient scheme
isomorphism. -/
def transport {X Y : Scheme.{u}} (e : X ≅ Y)
    (component : IrreducibleComponentAsIntClosedSubscheme X) :
    IrreducibleComponentAsIntClosedSubscheme Y where
  carrier := Boundary.IntClosedSubscheme.transport e component.carrier
  isIrreducibleComponent := by
    rw [Boundary.IntClosedSubscheme.range_transport_inclusion]
    exact mem_irreducibleComponents_image_of_homeomorph e.hom.homeomorph
      component.isIrreducibleComponent

@[simp] theorem transport_symm_transport
    {X Y : Scheme.{u}} (e : X ≅ Y)
    (component : IrreducibleComponentAsIntClosedSubscheme X) :
    transport e.symm (transport e component) = component := by
  cases component
  simp [transport]

theorem transport_injective {X Y : Scheme.{u}} (e : X ≅ Y) :
    Function.Injective (transport e) := by
  intro component₁ component₂ h
  have h' := congrArg (transport e.symm) h
  simpa using h'

end IrreducibleComponentAsIntClosedSubscheme

namespace FiniteIntegralClosedComponentDecomposition

/-- Transport a finite irreducible-component decomposition across an ambient
scheme isomorphism. The index set and component schemes are preserved; only the
ambient inclusions are transported. -/
def transport {X Y : Scheme.{u}} (e : X ≅ Y)
    (decomposition : FiniteIntegralClosedComponentDecomposition X) :
    FiniteIntegralClosedComponentDecomposition Y where
  index := decomposition.index
  fintypeIndex := decomposition.fintypeIndex
  decidableEqIndex := decomposition.decidableEqIndex
  component := fun i =>
    Boundary.IrreducibleComponentAsIntClosedSubscheme.transport e (decomposition.component i)
  covers := by
    intro y
    let x : X := e.inv.base y
    rcases decomposition.covers x with ⟨i, ⟨z, hz⟩⟩
    refine ⟨i, ⟨z, ?_⟩⟩
    change e.hom.base ((decomposition.component i).carrier.inclusion.base z) = y
    simpa [x, hz]
  irredundant := by
    intro i j hij
    exact decomposition.irredundant
      (IrreducibleComponentAsIntClosedSubscheme.transport_injective e hij)

end FiniteIntegralClosedComponentDecomposition

/-- Raw product-support data before choosing prime source components.

Unlike `PrimeFiniteCorrespondenceSupport`, this structure does not pick a
source irreducible component. It only records a closed support over the full
product source together with its map to the full product target. The passage to
prime pieces is handled by `ProductFiniteCorrespondenceImageDecomposition`. -/
structure ProductFiniteCorrespondenceSupport
    (X1 Y1 X2 Y2 : Geometry.SmSchemeOver k) where
  support : Scheme
  finiteOverProductSource : support ⟶ (overBaseProductObject X1 X2).scheme
  finite_toProductSource : IsFinite finiteOverProductSource
  toProductTarget : support ⟶ (overBaseProductObject Y1 Y2).scheme
  overBase :
    finiteOverProductSource ≫ (overBaseProductObject X1 X2).structMap =
      toProductTarget ≫ (overBaseProductObject Y1 Y2).structMap

namespace ProductFiniteCorrespondenceSupport

abbrev toProductSource
    {X1 Y1 X2 Y2 : Geometry.SmSchemeOver k}
    (S : ProductFiniteCorrespondenceSupport X1 Y1 X2 Y2) :
    S.support ⟶ (overBaseProductObject X1 X2).scheme :=
  S.finiteOverProductSource

@[simp] theorem toProductSource_overBase
    {X1 Y1 X2 Y2 : Geometry.SmSchemeOver k}
    (S : ProductFiniteCorrespondenceSupport X1 Y1 X2 Y2) :
    S.toProductSource ≫ (overBaseProductObject X1 X2).structMap =
      S.toProductTarget ≫ (overBaseProductObject Y1 Y2).structMap :=
  S.overBase

end ProductFiniteCorrespondenceSupport

namespace PrimeFiniteCorrespondenceSupport

/-- The raw product support scheme `P.support ×_k Q.support`. -/
abbrev externalProductSupportScheme
    {X1 Y1 X2 Y2 : Geometry.SmSchemeOver k}
    (P : RepresentedPrimeSupport X1 Y1)
    (Q : RepresentedPrimeSupport X2 Y2) : Scheme :=
  pullback (P.toAmbientSource ≫ X1.structMap) (Q.toAmbientSource ≫ X2.structMap)

/-- The canonical map `P.support ×_k Q.support → X1 ×_k X2`. -/
abbrev externalProductToProductSource
    {X1 Y1 X2 Y2 : Geometry.SmSchemeOver k}
    (P : RepresentedPrimeSupport X1 Y1)
    (Q : RepresentedPrimeSupport X2 Y2) :
    externalProductSupportScheme P Q ⟶ (overBaseProductObject X1 X2).scheme :=
  pullback.map (P.toAmbientSource ≫ X1.structMap) (Q.toAmbientSource ≫ X2.structMap)
    X1.structMap X2.structMap P.toAmbientSource Q.toAmbientSource (𝟙 _)
    (by simp [Category.assoc])
    (by simp [Category.assoc])

/-- The canonical map `P.support ×_k Q.support → Y1 ×_k Y2`. -/
abbrev externalProductToProductTarget
    {X1 Y1 X2 Y2 : Geometry.SmSchemeOver k}
    (P : RepresentedPrimeSupport X1 Y1)
    (Q : RepresentedPrimeSupport X2 Y2) :
    externalProductSupportScheme P Q ⟶ (overBaseProductObject Y1 Y2).scheme :=
  pullback.map (P.toAmbientSource ≫ X1.structMap) (Q.toAmbientSource ≫ X2.structMap)
    Y1.structMap Y2.structMap P.toTargetScheme Q.toTargetScheme (𝟙 _)
    (by simpa [Category.assoc] using P.toAmbientSource_overBase)
    (by simpa [Category.assoc] using Q.toAmbientSource_overBase)

/-- The actual raw product support attached to two represented prime supports.

This is the support-level external product before choosing irreducible pieces of
`P.support ×_k Q.support`. -/
def externalProductSupport
    {X1 Y1 X2 Y2 : Geometry.SmSchemeOver k}
    (P : RepresentedPrimeSupport X1 Y1)
    (Q : RepresentedPrimeSupport X2 Y2) :
    ProductFiniteCorrespondenceSupport X1 Y1 X2 Y2 where
  support := externalProductSupportScheme P Q
  finiteOverProductSource := externalProductToProductSource P Q
  finite_toProductSource := by
    letI : IsFinite P.finiteOverSourceComponent := P.finite_toSourceComponent
    letI : IsFinite Q.finiteOverSourceComponent := Q.finite_toSourceComponent
    letI : IsClosedImmersion P.sourceComponent.toAmbient :=
      P.sourceComponent.isClosedImmersion
    letI : IsClosedImmersion Q.sourceComponent.toAmbient :=
      Q.sourceComponent.isClosedImmersion
    letI : IsFinite P.sourceComponent.toAmbient := by infer_instance
    letI : IsFinite Q.sourceComponent.toAmbient := by infer_instance
    letI : IsFinite P.toAmbientSource := by
      dsimp [PrimeFiniteCorrespondenceSupport.toAmbientSource]
      infer_instance
    letI : IsFinite Q.toAmbientSource := by
      dsimp [PrimeFiniteCorrespondenceSupport.toAmbientSource]
      infer_instance
    simpa [externalProductToProductSource] using
      (MorphismProperty.pullback_map (P := @IsFinite)
        (f := P.toAmbientSource ≫ X1.structMap)
        (g := Q.toAmbientSource ≫ X2.structMap)
        (f' := X1.structMap)
        (g' := X2.structMap)
        (i₁ := P.toAmbientSource)
        (i₂ := Q.toAmbientSource)
        (h₁ := (inferInstance : IsFinite P.toAmbientSource))
        (h₂ := (inferInstance : IsFinite Q.toAmbientSource))
        (e₁ := rfl) (e₂ := rfl))
  toProductTarget := externalProductToProductTarget P Q
  overBase := by
    calc
      externalProductToProductSource P Q ≫ (overBaseProductObject X1 X2).structMap
          = pullback.fst (P.toAmbientSource ≫ X1.structMap) (Q.toAmbientSource ≫ X2.structMap) ≫
              P.toAmbientSource ≫ X1.structMap := by
                simp [externalProductToProductSource, overBaseProductObject, Category.assoc]
      _ = pullback.fst (P.toAmbientSource ≫ X1.structMap) (Q.toAmbientSource ≫ X2.structMap) ≫
            P.toTargetScheme ≫ Y1.structMap := by
              simpa [Category.assoc] using
                congrArg
                  (fun f =>
                    pullback.fst (P.toAmbientSource ≫ X1.structMap)
                      (Q.toAmbientSource ≫ X2.structMap) ≫ f)
                  P.toAmbientSource_overBase
      _ = externalProductToProductTarget P Q ≫ (overBaseProductObject Y1 Y2).structMap := by
            simp [externalProductToProductTarget, overBaseProductObject, Category.assoc]

@[simp] theorem diagonalRepresentedPrimeSupport_toTarget_structMap
    {X : Geometry.SmSchemeOver k}
    (source : SourceIrreducibleComponent X) :
    (SourceIrreducibleComponent.diagonalRepresentedPrimeSupport (k := k) source).toTarget ≫
        X.structMap =
      SourceIrreducibleComponent.toAmbient source ≫ X.structMap := by
  calc
    (SourceIrreducibleComponent.diagonalRepresentedPrimeSupport (k := k) source).toTarget ≫
        X.structMap =
        source.toSourceImageSubscheme.toAmbient ≫ X.structMap := by
          simp [SourceIrreducibleComponent.diagonalRepresentedPrimeSupport,
            SourceImageSubscheme.diagonalRepresentedPrimeSupport]
    _ = SourceIrreducibleComponent.toAmbient source ≫ X.structMap := by
          rw [SourceIrreducibleComponent.toSourceImageSubscheme_toAmbient]

theorem diagonalRepresentedPrimeSupport_toAmbientSource_structMap
    {X : Geometry.SmSchemeOver k}
    (source : SourceIrreducibleComponent X) :
    (SourceIrreducibleComponent.diagonalRepresentedPrimeSupport (k := k) source).toAmbientSource ≫
        X.structMap =
      SourceIrreducibleComponent.toAmbient source ≫ X.structMap := by
  calc
    (SourceIrreducibleComponent.diagonalRepresentedPrimeSupport (k := k) source).toAmbientSource ≫
        X.structMap =
        (SourceIrreducibleComponent.diagonalRepresentedPrimeSupport (k := k) source).toTargetScheme ≫
          X.structMap := by
          simpa using
            (PrimeFiniteCorrespondenceSupport.toAmbientSource_overBase
              (Z := SourceIrreducibleComponent.diagonalRepresentedPrimeSupport (k := k) source))
    _ = SourceIrreducibleComponent.toAmbient source ≫ X.structMap := by
          simpa [PrimeFiniteCorrespondenceSupport.toTargetScheme] using
            diagonalRepresentedPrimeSupport_toTarget_structMap (k := k) source

@[simp] theorem diagonal_externalProduct_eq_diagonal_product
    {X1 X2 : Geometry.SmSchemeOver k}
    (source1 : SourceIrreducibleComponent X1)
    (source2 : SourceIrreducibleComponent X2) :
    externalProductSupportScheme
      (SourceIrreducibleComponent.diagonalRepresentedPrimeSupport (k := k) source1)
      (SourceIrreducibleComponent.diagonalRepresentedPrimeSupport (k := k) source2)
      = pullback
        (SourceIrreducibleComponent.toAmbient source1 ≫ X1.structMap)
        (SourceIrreducibleComponent.toAmbient source2 ≫ X2.structMap) := by
  simpa [externalProductSupportScheme] using
    congrArg₂ (fun f g => pullback f g)
      (diagonalRepresentedPrimeSupport_toAmbientSource_structMap (k := k) source1)
      (diagonalRepresentedPrimeSupport_toAmbientSource_structMap (k := k) source2)

/-- Bridge form of diagonal-product integrality: the external-product diagonal
support and the pullback source diagonal support are definitionally the same
scheme, so integrality transfers transparently between these presentations. -/
theorem product_of_integral_diagonal_source_is_integral
    {X1 X2 : Geometry.SmSchemeOver k}
  (source1 : SourceIrreducibleComponent X1)
  (source2 : SourceIrreducibleComponent X2) :
    IsIntegral
        (externalProductSupportScheme
    (SourceIrreducibleComponent.diagonalRepresentedPrimeSupport (k := k) source1)
    (SourceIrreducibleComponent.diagonalRepresentedPrimeSupport (k := k) source2))
      ↔ IsIntegral (pullback
        (SourceIrreducibleComponent.toAmbient source1 ≫ X1.structMap)
        (SourceIrreducibleComponent.toAmbient source2 ≫ X2.structMap)) := by
  simpa [diagonal_externalProduct_eq_diagonal_product (k := k) source1 source2]

/-- Support-level diagonal-product identification: the raw support of the
external product of diagonal represented primes is the pullback of the two
source-image structure morphisms. -/
noncomputable def product_diagonal_support_iso
    {X1 X2 : Geometry.SmSchemeOver k}
    (source1 : SourceIrreducibleComponent X1)
    (source2 : SourceIrreducibleComponent X2) :
    externalProductSupportScheme
      (SourceIrreducibleComponent.diagonalRepresentedPrimeSupport (k := k) source1)
      (SourceIrreducibleComponent.diagonalRepresentedPrimeSupport (k := k) source2)
      ≅ pullback
        (SourceIrreducibleComponent.toAmbient source1 ≫ X1.structMap)
        (SourceIrreducibleComponent.toAmbient source2 ≫ X2.structMap) := by
  simpa [diagonal_externalProduct_eq_diagonal_product (k := k) source1 source2]
    using Iso.refl (pullback
      (SourceIrreducibleComponent.toAmbient source1 ≫ X1.structMap)
      (SourceIrreducibleComponent.toAmbient source2 ≫ X2.structMap))

abbrev product_diagonal_source_map
    {X1 X2 : Geometry.SmSchemeOver k}
    (source1 : SourceIrreducibleComponent X1)
    (source2 : SourceIrreducibleComponent X2) :=
  externalProductToProductSource
    (SourceIrreducibleComponent.diagonalRepresentedPrimeSupport (k := k) source1)
    (SourceIrreducibleComponent.diagonalRepresentedPrimeSupport (k := k) source2)

@[simp] theorem diagonal_externalProductToProductSource
    {X1 X2 : Geometry.SmSchemeOver k}
    (source1 : SourceIrreducibleComponent X1)
    (source2 : SourceIrreducibleComponent X2) :
    externalProductToProductSource
      (SourceIrreducibleComponent.diagonalRepresentedPrimeSupport (k := k) source1)
      (SourceIrreducibleComponent.diagonalRepresentedPrimeSupport (k := k) source2)
      = product_diagonal_source_map (k := k) source1 source2 := by
  rfl

/-- Source-map compatibility for product diagonals: after identifying the raw
support with the pullback of source-image structure maps, the external-product
source map is exactly induced by the ambient source-image inclusions. -/
theorem product_diagonal_map_eq_diagonal_product_map
    {X1 X2 : Geometry.SmSchemeOver k}
    (source1 : SourceIrreducibleComponent X1)
    (source2 : SourceIrreducibleComponent X2) :
    externalProductToProductSource
      (SourceIrreducibleComponent.diagonalRepresentedPrimeSupport (k := k) source1)
      (SourceIrreducibleComponent.diagonalRepresentedPrimeSupport (k := k) source2)
      = product_diagonal_source_map (k := k) source1 source2 :=
  diagonal_externalProductToProductSource (k := k) source1 source2

/-- Source-image bridge theorem for product diagonals: under the support
identification, the external-product source map is exactly the canonical
diagonal source-image map of the product object. -/
theorem product_diagonal_sourceImage_is_diagonal_sourceImage
    {X1 X2 : Geometry.SmSchemeOver k}
    (source1 : SourceIrreducibleComponent X1)
    (source2 : SourceIrreducibleComponent X2) :
    externalProductToProductSource
      (SourceIrreducibleComponent.diagonalRepresentedPrimeSupport (k := k) source1)
      (SourceIrreducibleComponent.diagonalRepresentedPrimeSupport (k := k) source2)
      = product_diagonal_source_map (k := k) source1 source2 :=
  product_diagonal_map_eq_diagonal_product_map (k := k) source1 source2

theorem diagonal_product_sourceImage_eq
    {X1 X2 : Geometry.SmSchemeOver k}
    (source1 : SourceIrreducibleComponent X1)
    (source2 : SourceIrreducibleComponent X2) :
    externalProductToProductSource
      (SourceIrreducibleComponent.diagonalRepresentedPrimeSupport (k := k) source1)
      (SourceIrreducibleComponent.diagonalRepresentedPrimeSupport (k := k) source2)
      = product_diagonal_source_map (k := k) source1 source2 :=
  product_diagonal_sourceImage_is_diagonal_sourceImage (k := k) source1 source2

theorem sourceComponent_product_diagonal
    {X1 X2 : Geometry.SmSchemeOver k}
    (source1 : SourceIrreducibleComponent X1)
    (source2 : SourceIrreducibleComponent X2) :
    externalProductToProductSource
      (SourceIrreducibleComponent.diagonalRepresentedPrimeSupport (k := k) source1)
      (SourceIrreducibleComponent.diagonalRepresentedPrimeSupport (k := k) source2)
      = product_diagonal_source_map (k := k) source1 source2 :=
  diagonal_product_sourceImage_eq (k := k) source1 source2

abbrev product_diagonal_target_map
    {X1 X2 : Geometry.SmSchemeOver k}
    (source1 : SourceIrreducibleComponent X1)
    (source2 : SourceIrreducibleComponent X2) :=
  externalProductToProductTarget
    (SourceIrreducibleComponent.diagonalRepresentedPrimeSupport (k := k) source1)
    (SourceIrreducibleComponent.diagonalRepresentedPrimeSupport (k := k) source2)

  theorem diagonal_product_sourceComponent_eq
      {X1 X2 : Geometry.SmSchemeOver k}
      (source1 : SourceIrreducibleComponent X1)
      (source2 : SourceIrreducibleComponent X2) :
      externalProductToProductTarget
          (SourceIrreducibleComponent.diagonalRepresentedPrimeSupport (k := k) source1)
          (SourceIrreducibleComponent.diagonalRepresentedPrimeSupport (k := k) source2)
        = product_diagonal_target_map (k := k) source1 source2 := by
    rfl

@[simp] theorem diagonal_externalProductToProductTarget
    {X1 X2 : Geometry.SmSchemeOver k}
    (source1 : SourceIrreducibleComponent X1)
    (source2 : SourceIrreducibleComponent X2) :
    externalProductToProductTarget
        (SourceIrreducibleComponent.diagonalRepresentedPrimeSupport (k := k) source1)
        (SourceIrreducibleComponent.diagonalRepresentedPrimeSupport (k := k) source2)
      = product_diagonal_target_map (k := k) source1 source2 := by
  rfl

/-- For diagonal prime supports, the raw external-product map to the product
target is the same morphism as the raw external-product map to the product
source, after the source and target products are definitionally the same
object. This is the support-level normal form behind the tensor identity
theorem. -/
theorem diagonal_externalProductToProductTarget_eq_toProductSource
    {X1 X2 : Geometry.SmSchemeOver k}
    (source1 : SourceIrreducibleComponent X1)
    (source2 : SourceIrreducibleComponent X2) :
    externalProductToProductTarget
        (SourceIrreducibleComponent.diagonalRepresentedPrimeSupport (k := k) source1)
        (SourceIrreducibleComponent.diagonalRepresentedPrimeSupport (k := k) source2)
      =
    externalProductToProductSource
        (SourceIrreducibleComponent.diagonalRepresentedPrimeSupport (k := k) source1)
        (SourceIrreducibleComponent.diagonalRepresentedPrimeSupport (k := k) source2) := by
  let P := SourceIrreducibleComponent.diagonalRepresentedPrimeSupport (k := k) source1
  let Q := SourceIrreducibleComponent.diagonalRepresentedPrimeSupport (k := k) source2
  change externalProductToProductTarget P Q = externalProductToProductSource P Q
  have hTarget₁ :
      P.toTargetScheme = P.toAmbientSource := by
    rfl
  have hTarget₂ :
      Q.toTargetScheme = Q.toAmbientSource := by
    rfl
  apply pullback.hom_ext
  · simpa [externalProductToProductTarget, externalProductToProductSource,
      P, Q, PrimeFiniteCorrespondenceSupport.toAmbientSource,
      PrimeFiniteCorrespondenceSupport.toSourceImage, Category.assoc] using
      congrArg
        (fun f =>
          pullback.fst (P.toAmbientSource ≫ X1.structMap)
            (Q.toAmbientSource ≫ X2.structMap) ≫ f)
        hTarget₁
  · simpa [externalProductToProductTarget, externalProductToProductSource,
      P, Q, PrimeFiniteCorrespondenceSupport.toAmbientSource,
      PrimeFiniteCorrespondenceSupport.toSourceImage, Category.assoc] using
      congrArg
        (fun f =>
          pullback.snd (P.toAmbientSource ≫ X1.structMap)
            (Q.toAmbientSource ≫ X2.structMap) ≫ f)
        hTarget₂

/-- Product-support version of
`diagonal_externalProductToProductTarget_eq_toProductSource`. -/
theorem diagonal_externalProductSupport_toProductTarget_eq_toProductSource
    {X1 X2 : Geometry.SmSchemeOver k}
    (source1 : SourceIrreducibleComponent X1)
    (source2 : SourceIrreducibleComponent X2) :
    (externalProductSupport
        (SourceIrreducibleComponent.diagonalRepresentedPrimeSupport (k := k) source1)
        (SourceIrreducibleComponent.diagonalRepresentedPrimeSupport (k := k) source2)).toProductTarget =
    (externalProductSupport
        (SourceIrreducibleComponent.diagonalRepresentedPrimeSupport (k := k) source1)
        (SourceIrreducibleComponent.diagonalRepresentedPrimeSupport (k := k) source2)).toProductSource := by
  exact diagonal_externalProductToProductTarget_eq_toProductSource
    (k := k) source1 source2

end PrimeFiniteCorrespondenceSupport

namespace FiniteIrreducibleComponentDecomposition

/-- The identity correspondence on a product is unchanged if its diagonal
decomposition is replaced by the product decomposition constructed from
diagonal decompositions on the two factors. -/
theorem identityFiniteCorrespondence_eq_product_decomposition
    {X Y : Geometry.SmSchemeOver k}
    (DX : FiniteIrreducibleComponentDecomposition X)
    (DY : FiniteIrreducibleComponentDecomposition Y)
    (stableDX :
      (listed : { listed : SourceIrreducibleComponent X // listed ∈ DX.components }) →
        ProductStableSourceComponent X)
    (hstableDX : ∀ listed, (stableDX listed).component = listed.1)
    (DXY : FiniteIrreducibleComponentDecomposition (overBaseProductObject X Y)) :
    DXY.identityFiniteCorrespondence =
      (finiteProductSourceIrreducibleComponentDecomposition
        DX DY stableDX hstableDX).identityFiniteCorrespondence := by
  exact identityFiniteCorrespondence_independent DXY
    (finiteProductSourceIrreducibleComponentDecomposition DX DY stableDX hstableDX)

end FiniteIrreducibleComponentDecomposition

/-- Boundary-level alias for prime-support equivalence. Keeping this alias here
prevents later external-product code from depending on the internal namespace
where the equivalence relation is implemented. -/
abbrev PrimeSupportEquivalent {X Y : Geometry.SmSchemeOver k}
    (P Q : RepresentedPrimeSupport X Y) : Prop :=
  PrimeFiniteCorrespondenceSupport.PrimeSupportEquivalent P Q

namespace PrimeFiniteCorrespondenceSupport

/-- Induced isomorphism of raw external-product supports on the left under a
prime-support equivalence `P ≃ P'`. -/
noncomputable def leftExternalProductSupportIso
    {X1 Y1 X2 Y2 : Geometry.SmSchemeOver k}
    {P P' : RepresentedPrimeSupport X1 Y1}
 (h : PrimeSupportEquivalent P P')
    (Q : RepresentedPrimeSupport X2 Y2) :
    externalProductSupportScheme P Q ≅ externalProductSupportScheme P' Q := by
  let hrest := Classical.choose_spec h
  let iso := Classical.choose hrest
  refine asIso <|
    pullback.map
      (P.toAmbientSource ≫ X1.structMap)
      (Q.toAmbientSource ≫ X2.structMap)
      (P'.toAmbientSource ≫ X1.structMap)
      (Q.toAmbientSource ≫ X2.structMap)
      iso.hom (𝟙 _) (𝟙 _) ?_ ?_
  · simpa [Category.assoc] using
      (_root_.Boundary.PrimeFiniteCorrespondenceSupport.supportIsoOverProduct_hom_toAmbientSource_structMap
        (P := P) (Q := P') h).symm
  · simp

theorem leftExternalProductSupportIso_hom_toProductSource
    {X1 Y1 X2 Y2 : Geometry.SmSchemeOver k}
    {P P' : RepresentedPrimeSupport X1 Y1}
    (h : PrimeSupportEquivalent P P')
    (Q : RepresentedPrimeSupport X2 Y2) :
    (leftExternalProductSupportIso h Q).hom ≫ externalProductToProductSource P' Q =
      externalProductToProductSource P Q := by
  apply pullback.hom_ext
  · simpa [leftExternalProductSupportIso, externalProductToProductSource,
      Category.assoc] using
      _root_.Boundary.PrimeFiniteCorrespondenceSupport.supportIsoOverProduct_comp_hom_toAmbientSource h
        (pullback.fst (P.toAmbientSource ≫ X1.structMap)
          (Q.toAmbientSource ≫ X2.structMap))
  · simp [leftExternalProductSupportIso, externalProductToProductSource, Category.assoc]

theorem leftExternalProductSupportIso_hom_toProductTarget
    {X1 Y1 X2 Y2 : Geometry.SmSchemeOver k}
    {P P' : RepresentedPrimeSupport X1 Y1}
    (h : PrimeSupportEquivalent P P')
    (Q : RepresentedPrimeSupport X2 Y2) :
    (leftExternalProductSupportIso h Q).hom ≫ externalProductToProductTarget P' Q =
      externalProductToProductTarget P Q := by
  apply pullback.hom_ext
  · simpa [leftExternalProductSupportIso, externalProductToProductTarget,
      Category.assoc] using
      _root_.Boundary.PrimeFiniteCorrespondenceSupport.supportIsoOverProduct_comp_hom_toTargetScheme h
        (pullback.fst (P.toAmbientSource ≫ X1.structMap)
          (Q.toAmbientSource ≫ X2.structMap))
  · simp [leftExternalProductSupportIso, externalProductToProductTarget, Category.assoc]

theorem leftExternalProductSupportIso_transport_factorization
    {X1 Y1 X2 Y2 : Geometry.SmSchemeOver k}
    {P P' : RepresentedPrimeSupport X1 Y1}
    (h : PrimeSupportEquivalent P P')
    (Q : RepresentedPrimeSupport X2 Y2)
    (Z : IntClosedSubscheme (externalProductSupportScheme P Q)) :
    Z.inclusion ≫ (externalProductSupport P Q).toProductSource =
      (Boundary.IntClosedSubscheme.transport (leftExternalProductSupportIso h Q) Z).inclusion ≫
        (externalProductSupport P' Q).toProductSource := by
  have hmap := leftExternalProductSupportIso_hom_toProductSource h Q
  calc
    Z.inclusion ≫ (externalProductSupport P Q).toProductSource =
        Z.inclusion ≫
          ((leftExternalProductSupportIso h Q).hom ≫
            (externalProductSupport P' Q).toProductSource) := by
          simpa [ProductFiniteCorrespondenceSupport.toProductSource] using
            (congrArg (fun f => Z.inclusion ≫ f) hmap.symm)
    _ = (Boundary.IntClosedSubscheme.transport (leftExternalProductSupportIso h Q) Z).inclusion ≫
          (externalProductSupport P' Q).toProductSource := by
          simp [Boundary.IntClosedSubscheme.transport, Category.assoc]

theorem leftExternalProductSupportIso_transport_target_factorization
    {X1 Y1 X2 Y2 : Geometry.SmSchemeOver k}
    {P P' : RepresentedPrimeSupport X1 Y1}
    (h : PrimeSupportEquivalent P P')
    (Q : RepresentedPrimeSupport X2 Y2)
    (Z : IntClosedSubscheme (externalProductSupportScheme P Q)) :
    Z.inclusion ≫ (externalProductSupport P Q).toProductTarget =
      (Boundary.IntClosedSubscheme.transport (leftExternalProductSupportIso h Q) Z).inclusion ≫
        (externalProductSupport P' Q).toProductTarget := by
  have hmap := leftExternalProductSupportIso_hom_toProductTarget h Q
  calc
    Z.inclusion ≫ (externalProductSupport P Q).toProductTarget =
        Z.inclusion ≫
          ((leftExternalProductSupportIso h Q).hom ≫
            (externalProductSupport P' Q).toProductTarget) := by
          simpa [ProductFiniteCorrespondenceSupport.toProductTarget] using
            (congrArg (fun f => Z.inclusion ≫ f) hmap.symm)
    _ = (Boundary.IntClosedSubscheme.transport (leftExternalProductSupportIso h Q) Z).inclusion ≫
          (externalProductSupport P' Q).toProductTarget := by
          simp [Boundary.IntClosedSubscheme.transport, Category.assoc]

/-- Induced isomorphism of raw external-product supports on the right under a
prime-support equivalence `Q ≃ Q'`. -/
noncomputable def rightExternalProductSupportIso
    {X1 Y1 X2 Y2 : Geometry.SmSchemeOver k}
 (P : RepresentedPrimeSupport X1 Y1)
    {Q Q' : RepresentedPrimeSupport X2 Y2}
    (h : PrimeSupportEquivalent Q Q') :
    externalProductSupportScheme P Q ≅ externalProductSupportScheme P Q' := by
  let hrest := Classical.choose_spec h
  let iso := Classical.choose hrest
  refine asIso <|
    pullback.map
      (P.toAmbientSource ≫ X1.structMap)
      (Q.toAmbientSource ≫ X2.structMap)
      (P.toAmbientSource ≫ X1.structMap)
      (Q'.toAmbientSource ≫ X2.structMap)
      (𝟙 _) iso.hom (𝟙 _) ?_ ?_
  · simp
  · simpa [Category.assoc] using
      (_root_.Boundary.PrimeFiniteCorrespondenceSupport.supportIsoOverProduct_hom_toAmbientSource_structMap
        (P := Q) (Q := Q') h).symm

theorem rightExternalProductSupportIso_hom_toProductSource
    {X1 Y1 X2 Y2 : Geometry.SmSchemeOver k}
    (P : RepresentedPrimeSupport X1 Y1)
    {Q Q' : RepresentedPrimeSupport X2 Y2}
    (h : PrimeSupportEquivalent Q Q') :
    (rightExternalProductSupportIso P h).hom ≫ externalProductToProductSource P Q' =
      externalProductToProductSource P Q := by
  apply pullback.hom_ext
  · simp [rightExternalProductSupportIso, externalProductToProductSource, Category.assoc]
  · simpa [rightExternalProductSupportIso, externalProductToProductSource,
      Category.assoc] using
      _root_.Boundary.PrimeFiniteCorrespondenceSupport.supportIsoOverProduct_comp_hom_toAmbientSource h
        (pullback.snd (P.toAmbientSource ≫ X1.structMap)
          (Q.toAmbientSource ≫ X2.structMap))

theorem rightExternalProductSupportIso_hom_toProductTarget
    {X1 Y1 X2 Y2 : Geometry.SmSchemeOver k}
    (P : RepresentedPrimeSupport X1 Y1)
    {Q Q' : RepresentedPrimeSupport X2 Y2}
    (h : PrimeSupportEquivalent Q Q') :
    (rightExternalProductSupportIso P h).hom ≫ externalProductToProductTarget P Q' =
      externalProductToProductTarget P Q := by
  apply pullback.hom_ext
  · simp [rightExternalProductSupportIso, externalProductToProductTarget, Category.assoc]
  · simpa [rightExternalProductSupportIso, externalProductToProductTarget,
      Category.assoc] using
      _root_.Boundary.PrimeFiniteCorrespondenceSupport.supportIsoOverProduct_comp_hom_toTargetScheme h
        (pullback.snd (P.toAmbientSource ≫ X1.structMap)
          (Q.toAmbientSource ≫ X2.structMap))

theorem rightExternalProductSupportIso_transport_factorization
    {X1 Y1 X2 Y2 : Geometry.SmSchemeOver k}
    (P : RepresentedPrimeSupport X1 Y1)
    {Q Q' : RepresentedPrimeSupport X2 Y2}
    (h : PrimeSupportEquivalent Q Q')
    (Z : IntClosedSubscheme (externalProductSupportScheme P Q)) :
    Z.inclusion ≫ (externalProductSupport P Q).toProductSource =
      (Boundary.IntClosedSubscheme.transport (rightExternalProductSupportIso P h) Z).inclusion ≫
        (externalProductSupport P Q').toProductSource := by
  have hmap := rightExternalProductSupportIso_hom_toProductSource P h
  calc
    Z.inclusion ≫ (externalProductSupport P Q).toProductSource =
        Z.inclusion ≫
          ((rightExternalProductSupportIso P h).hom ≫
            (externalProductSupport P Q').toProductSource) := by
          simpa [ProductFiniteCorrespondenceSupport.toProductSource] using
            (congrArg (fun f => Z.inclusion ≫ f) hmap.symm)
    _ = (Boundary.IntClosedSubscheme.transport (rightExternalProductSupportIso P h) Z).inclusion ≫
          (externalProductSupport P Q').toProductSource := by
          simp [Boundary.IntClosedSubscheme.transport, Category.assoc]

theorem rightExternalProductSupportIso_transport_target_factorization
    {X1 Y1 X2 Y2 : Geometry.SmSchemeOver k}
    (P : RepresentedPrimeSupport X1 Y1)
    {Q Q' : RepresentedPrimeSupport X2 Y2}
    (h : PrimeSupportEquivalent Q Q')
    (Z : IntClosedSubscheme (externalProductSupportScheme P Q)) :
    Z.inclusion ≫ (externalProductSupport P Q).toProductTarget =
      (Boundary.IntClosedSubscheme.transport (rightExternalProductSupportIso P h) Z).inclusion ≫
        (externalProductSupport P Q').toProductTarget := by
  have hmap := rightExternalProductSupportIso_hom_toProductTarget P h
  calc
    Z.inclusion ≫ (externalProductSupport P Q).toProductTarget =
        Z.inclusion ≫
          ((rightExternalProductSupportIso P h).hom ≫
            (externalProductSupport P Q').toProductTarget) := by
          simpa [ProductFiniteCorrespondenceSupport.toProductTarget] using
            (congrArg (fun f => Z.inclusion ≫ f) hmap.symm)
    _ = (Boundary.IntClosedSubscheme.transport (rightExternalProductSupportIso P h) Z).inclusion ≫
          (externalProductSupport P Q').toProductTarget := by
          simp [Boundary.IntClosedSubscheme.transport, Category.assoc]

end PrimeFiniteCorrespondenceSupport

namespace ExternalProductRawComponentData

/-- Canonical map from a listed raw external-product component to the full
product source `X1 ×_k X2`. -/
abbrev rawComponentToProductSource
    {X1 Y1 X2 Y2 : Geometry.SmSchemeOver k}
    (P : RepresentedPrimeSupport X1 Y1)
    (Q : RepresentedPrimeSupport X2 Y2)
    (sourceDecomposition :
      FiniteIntegralClosedComponentDecomposition
        (PrimeFiniteCorrespondenceSupport.externalProductSupportScheme P Q))
    (sourceSubscheme :
      IntClosedSubscheme
        (PrimeFiniteCorrespondenceSupport.externalProductSupportScheme P Q)) :
    sourceSubscheme.scheme ⟶ (overBaseProductObject X1 X2).scheme :=
  sourceSubscheme.inclusion ≫ PrimeFiniteCorrespondenceSupport.externalProductToProductSource P Q

/-- Canonical target map from a listed raw external-product component to the
full product target `Y1 ×_k Y2`. -/
abbrev rawComponentToProductTarget
    {X1 Y1 X2 Y2 : Geometry.SmSchemeOver k}
    (P : RepresentedPrimeSupport X1 Y1)
    (Q : RepresentedPrimeSupport X2 Y2)
    (sourceDecomposition :
      FiniteIntegralClosedComponentDecomposition
        (PrimeFiniteCorrespondenceSupport.externalProductSupportScheme P Q))
    (sourceSubscheme :
      IntClosedSubscheme
        (PrimeFiniteCorrespondenceSupport.externalProductSupportScheme P Q)) :
    sourceSubscheme.scheme ⟶ (overBaseProductObject Y1 Y2).scheme :=
  sourceSubscheme.inclusion ≫ PrimeFiniteCorrespondenceSupport.externalProductToProductTarget P Q

/-- Honest image-based prime-piece data for one irreducible component of the
raw product support `P.support ×_k Q.support`.

This records the actual integral closed source image inside `X1 ×_k X2`
without introducing any auxiliary choice of ambient irreducible component.
This is the mathematically correct local target for
external-product components. -/
structure ExternalProductSourceImageData
    {X1 Y1 X2 Y2 : Geometry.SmSchemeOver k}
    (P : RepresentedPrimeSupport X1 Y1)
    (Q : RepresentedPrimeSupport X2 Y2)
    (sourceDecomposition :
      FiniteIntegralClosedComponentDecomposition
        (PrimeFiniteCorrespondenceSupport.externalProductSupportScheme P Q))
    (sourceSubscheme :
      IntClosedSubscheme
        (PrimeFiniteCorrespondenceSupport.externalProductSupportScheme P Q)) where
  multiplicity : ℕ
  sourceImage : IntClosedSubscheme ((overBaseProductObject X1 X2).scheme)
  toSourceImage : sourceSubscheme.scheme ⟶ sourceImage.scheme
  finite_toSourceImage : IsFinite toSourceImage
  surjective_toSourceImage : Function.Surjective toSourceImage.base
  sourceImage_factorization :
    toSourceImage ≫ sourceImage.inclusion =
      rawComponentToProductSource P Q sourceDecomposition sourceSubscheme
  toProductTarget : sourceSubscheme.scheme ⟶ (overBaseProductObject Y1 Y2).scheme
  target_factorization :
    toProductTarget =
      rawComponentToProductTarget P Q sourceDecomposition sourceSubscheme
  inclusion :
    sourceSubscheme.scheme ⟶
      pullback (sourceImage.inclusion ≫ (overBaseProductObject X1 X2).structMap)
        ((overBaseProductObject Y1 Y2).structMap)
  inclusion_fst :
    inclusion ≫
        pullback.fst
          (sourceImage.inclusion ≫ (overBaseProductObject X1 X2).structMap)
          ((overBaseProductObject Y1 Y2).structMap) =
      toSourceImage
  inclusion_snd :
    inclusion ≫
        pullback.snd
          (sourceImage.inclusion ≫ (overBaseProductObject X1 X2).structMap)
          ((overBaseProductObject Y1 Y2).structMap) =
      toProductTarget
  isClosedImmersion : IsClosedImmersion inclusion

end ExternalProductRawComponentData

/-- Boundary-level alias for raw component image data used by product
decompositions. -/
abbrev ExternalProductSourceImageData
    {X1 Y1 X2 Y2 : Geometry.SmSchemeOver k}
    (P : RepresentedPrimeSupport X1 Y1)
    (Q : RepresentedPrimeSupport X2 Y2)
    (sourceDecomposition :
      FiniteIntegralClosedComponentDecomposition
        (PrimeFiniteCorrespondenceSupport.externalProductSupportScheme P Q))
    (sourceSubscheme :
      IntClosedSubscheme
        (PrimeFiniteCorrespondenceSupport.externalProductSupportScheme P Q)) :=
  ExternalProductRawComponentData.ExternalProductSourceImageData
    P Q sourceDecomposition sourceSubscheme

/-- Honest decomposition data turning one raw product support into a finite sum
of image-based external-product pieces.

Each listed piece records the actual scheme-theoretic source image in
`X1 ×_k X2`, rather than any auxiliary choice of ambient irreducible
component. -/
structure ProductFiniteCorrespondenceImageDecomposition
    {X1 Y1 X2 Y2 : Geometry.SmSchemeOver k}
    (supportData : ProductFiniteCorrespondenceSupport X1 Y1 X2 Y2) where
  components : FiniteIntegralClosedComponentDecomposition supportData.support
  multiplicity : components.index → ℕ
  sourceImage :
    components.index → IntClosedSubscheme ((overBaseProductObject X1 X2).scheme)
  toSourceImage :
    (i : components.index) →
      (components.component i).carrier.scheme ⟶ (sourceImage i).scheme
  finite_toSourceImage :
    (i : components.index) → IsFinite (toSourceImage i)
  surjective_toSourceImage :
    (i : components.index) → Function.Surjective (toSourceImage i).base
  sourceImage_factorization :
    (i : components.index) →
      toSourceImage i ≫ (sourceImage i).inclusion =
        (components.component i).carrier.inclusion ≫
          supportData.toProductSource
  toProductTarget :
    (i : components.index) →
      (components.component i).carrier.scheme ⟶ (overBaseProductObject Y1 Y2).scheme
  target_factorization :
    (i : components.index) →
      toProductTarget i =
        (components.component i).carrier.inclusion ≫ supportData.toProductTarget
  inclusion :
    (i : components.index) →
      (components.component i).carrier.scheme ⟶
        pullback
          ((sourceImage i).inclusion ≫ (overBaseProductObject X1 X2).structMap)
          ((overBaseProductObject Y1 Y2).structMap)
  inclusion_fst :
    (i : components.index) →
      inclusion i ≫
          pullback.fst
            ((sourceImage i).inclusion ≫ (overBaseProductObject X1 X2).structMap)
            ((overBaseProductObject Y1 Y2).structMap) =
        toSourceImage i
  inclusion_snd :
    (i : components.index) →
      inclusion i ≫
          pullback.snd
            ((sourceImage i).inclusion ≫ (overBaseProductObject X1 X2).structMap)
            ((overBaseProductObject Y1 Y2).structMap) =
        toProductTarget i
  isClosedImmersion :
    (i : components.index) → IsClosedImmersion (inclusion i)

namespace ProductFiniteCorrespondenceImageDecomposition

/-- Assemble an honest image-based decomposition from explicit image data over
the listed raw components of a chosen product-support decomposition. -/
def ofComponentData
    {X1 Y1 X2 Y2 : Geometry.SmSchemeOver k}
    (P : RepresentedPrimeSupport X1 Y1)
    (Q : RepresentedPrimeSupport X2 Y2)
    (sourceDecomposition :
      FiniteIntegralClosedComponentDecomposition
        (PrimeFiniteCorrespondenceSupport.externalProductSupportScheme P Q))
    (componentData :
      (i : sourceDecomposition.index) →
        ExternalProductSourceImageData P Q sourceDecomposition
          ((sourceDecomposition.component i).carrier)) :
    ProductFiniteCorrespondenceImageDecomposition
      (PrimeFiniteCorrespondenceSupport.externalProductSupport P Q) where
  components := sourceDecomposition
  multiplicity := fun i => (componentData i).multiplicity
  sourceImage := fun i => (componentData i).sourceImage
  toSourceImage := fun i => (componentData i).toSourceImage
  finite_toSourceImage := fun i => (componentData i).finite_toSourceImage
  surjective_toSourceImage := fun i => (componentData i).surjective_toSourceImage
  sourceImage_factorization := fun i => (componentData i).sourceImage_factorization
  toProductTarget := fun i => (componentData i).toProductTarget
  target_factorization := fun i => (componentData i).target_factorization
  inclusion := fun i => (componentData i).inclusion
  inclusion_fst := fun i => (componentData i).inclusion_fst
  inclusion_snd := fun i => (componentData i).inclusion_snd
  isClosedImmersion := fun i => (componentData i).isClosedImmersion

/-- One listed image-based decomposition piece as a represented prime support
on the full product source and target. -/
def toRepresentedPrimeSupport
    {X1 Y1 X2 Y2 : Geometry.SmSchemeOver k}
    {supportData : ProductFiniteCorrespondenceSupport X1 Y1 X2 Y2}
    (decomposition : ProductFiniteCorrespondenceImageDecomposition supportData)
    (i : decomposition.components.index) :
    RepresentedPrimeSupport (overBaseProductObject X1 X2) (overBaseProductObject Y1 Y2) where
  sourceImage :=
    { carrier :=
        { scheme := (decomposition.sourceImage i).scheme
          structMap :=
            (decomposition.sourceImage i).inclusion ≫
              (overBaseProductObject X1 X2).structMap }
      toAmbient := (decomposition.sourceImage i).inclusion
      toAmbient_overBase := rfl
      isClosedImmersion := (decomposition.sourceImage i).isClosedImm
      isIntegral := (decomposition.sourceImage i).isIntegral }
  support := (decomposition.components.component i).carrier.scheme
  isIntegral := (decomposition.components.component i).carrier.isIntegral
  finiteOverSourceComponent := decomposition.toSourceImage i
  finite_toSourceComponent := decomposition.finite_toSourceImage i
  surjective_toSourceComponent := decomposition.surjective_toSourceImage i
  toTarget := decomposition.toProductTarget i
  inclusion := decomposition.inclusion i
  inclusion_fst := decomposition.inclusion_fst i
  inclusion_snd := decomposition.inclusion_snd i
  isClosedImmersion := decomposition.isClosedImmersion i

/-- If the raw product support has equal maps to product source and product
target, then each represented image piece has target map equal to its ambient
source map. This is the local diagonal normal form for decomposed product
supports. -/
theorem toRepresentedPrimeSupport_toTarget_eq_toAmbientSource_of_target_eq_source
    {X1 X2 : Geometry.SmSchemeOver k}
    {supportData : ProductFiniteCorrespondenceSupport X1 X1 X2 X2}
    (decomposition : ProductFiniteCorrespondenceImageDecomposition supportData)
    (hTarget :
      supportData.toProductTarget = supportData.toProductSource)
    (i : decomposition.components.index) :
    (decomposition.toRepresentedPrimeSupport i).toTargetScheme =
      (decomposition.toRepresentedPrimeSupport i).toAmbientSource := by
  calc
    (decomposition.toRepresentedPrimeSupport i).toTargetScheme =
        decomposition.toProductTarget i := by
        rfl
    _ = (decomposition.components.component i).carrier.inclusion ≫
          supportData.toProductTarget := by
        exact decomposition.target_factorization i
    _ = (decomposition.components.component i).carrier.inclusion ≫
          supportData.toProductSource := by
        rw [hTarget]
    _ = decomposition.toSourceImage i ≫ (decomposition.sourceImage i).inclusion := by
        exact (decomposition.sourceImage_factorization i).symm
    _ = (decomposition.toRepresentedPrimeSupport i).toAmbientSource := by
        rfl

/-- One listed image-based decomposition piece as a weighted represented prime
support. -/
def toWeightedPrimeFiniteCorrespondenceSupport
    {X1 Y1 X2 Y2 : Geometry.SmSchemeOver k}
    {supportData : ProductFiniteCorrespondenceSupport X1 Y1 X2 Y2}
    (decomposition : ProductFiniteCorrespondenceImageDecomposition supportData)
    (i : decomposition.components.index) :
    WeightedPrimeFiniteCorrespondenceSupport
      (overBaseProductObject X1 X2) (overBaseProductObject Y1 Y2) where
  multiplicity := decomposition.multiplicity i
  prime := decomposition.toRepresentedPrimeSupport i

/-- Weighted finite-correspondence form of the local diagonal normal form.
If the raw support has equal source and target maps, a decomposed piece maps
isomorphically to its source image, and its multiplicity is one, then that
piece is exactly the diagonal singleton on its source image. -/
theorem ofWeighted_toRepresentedPrimeSupport_eq_diagonal_of_target_eq_source
    {X1 X2 : Geometry.SmSchemeOver k}
    {supportData : ProductFiniteCorrespondenceSupport X1 X1 X2 X2}
    (decomposition : ProductFiniteCorrespondenceImageDecomposition supportData)
    (hTarget :
      supportData.toProductTarget = supportData.toProductSource)
    (i : decomposition.components.index)
    [IsIso (decomposition.toSourceImage i)]
    (hmult : decomposition.multiplicity i = 1) :
    FiniteCorrespondence.ofWeightedPrimeSupport
        (decomposition.toWeightedPrimeFiniteCorrespondenceSupport i) =
      SourceImageSubscheme.diagonalFiniteCorrespondence
        (decomposition.toRepresentedPrimeSupport i).sourceComponent := by
  have hPieceTarget :
      (decomposition.toRepresentedPrimeSupport i).toTargetScheme =
        (decomposition.toRepresentedPrimeSupport i).toAmbientSource :=
    decomposition.toRepresentedPrimeSupport_toTarget_eq_toAmbientSource_of_target_eq_source
      hTarget i
  change
    Finsupp.single
        (PrimeFiniteCorrespondenceGeom.ofRepresented
          (decomposition.toRepresentedPrimeSupport i))
        ((decomposition.multiplicity i : ℕ) : ℤ) =
      SourceImageSubscheme.diagonalFiniteCorrespondence
        (decomposition.toRepresentedPrimeSupport i).sourceComponent
  rw [hmult]
  letI : IsIso (decomposition.toRepresentedPrimeSupport i).toSourceImage := by
    change IsIso (decomposition.toSourceImage i)
    infer_instance
  exact
    _root_.Boundary.SourceImageSubscheme.single_eq_diagonal_of_isIso_toSourceImage_of_target_eq
      (decomposition.toRepresentedPrimeSupport i) hPieceTarget

/-- The finite correspondence presentation obtained by summing the decomposed
image-based prime pieces of the raw product support. -/
def toPresentation
    {X1 Y1 X2 Y2 : Geometry.SmSchemeOver k}
    {supportData : ProductFiniteCorrespondenceSupport X1 Y1 X2 Y2}
    (decomposition : ProductFiniteCorrespondenceImageDecomposition supportData) :
    FiniteCorrespondencePresentation
      (overBaseProductObject X1 X2) (overBaseProductObject Y1 Y2) := by
  classical
  letI := decomposition.components.fintypeIndex
  letI := decomposition.components.decidableEqIndex
  exact Finset.univ.sum fun i =>
    FiniteCorrespondencePresentation.ofWeightedPrimeSupport
      (decomposition.toWeightedPrimeFiniteCorrespondenceSupport i)

/-- The geometric finite correspondence obtained from the decomposed raw
product support. -/
def toFiniteCorrespondence
    {X1 Y1 X2 Y2 : Geometry.SmSchemeOver k}
    {supportData : ProductFiniteCorrespondenceSupport X1 Y1 X2 Y2}
    (decomposition : ProductFiniteCorrespondenceImageDecomposition supportData) :
    FiniteCorrespondence
        (overBaseProductObject X1 X2) (overBaseProductObject Y1 Y2) :=
    FiniteCorrespondencePresentation.toGeom (decomposition.toPresentation)

/-- Sum-level diagonal normal form for an image decomposition of a raw support
whose target map equals its source map. The remaining hypotheses are precisely
the geometric facts that each listed piece maps isomorphically to its source
image and appears with multiplicity one. -/
theorem toFiniteCorrespondence_eq_sum_diagonal_of_target_eq_source
    {X1 X2 : Geometry.SmSchemeOver k}
    {supportData : ProductFiniteCorrespondenceSupport X1 X1 X2 X2}
    (decomposition : ProductFiniteCorrespondenceImageDecomposition supportData)
    (hTarget :
      supportData.toProductTarget = supportData.toProductSource)
    (hIso : ∀ i : decomposition.components.index,
      IsIso (decomposition.toSourceImage i))
    (hmult : ∀ i : decomposition.components.index,
      decomposition.multiplicity i = 1) :
    decomposition.toFiniteCorrespondence =
      ∑ i : decomposition.components.index,
        SourceImageSubscheme.diagonalFiniteCorrespondence
          (decomposition.toRepresentedPrimeSupport i).sourceComponent := by
  classical
  letI := decomposition.components.fintypeIndex
  letI := decomposition.components.decidableEqIndex
  have hToGeom_sum :
      ∀ s : Finset decomposition.components.index,
        FiniteCorrespondencePresentation.toGeom
            (∑ i in s,
              FiniteCorrespondencePresentation.ofWeightedPrimeSupport
                (decomposition.toWeightedPrimeFiniteCorrespondenceSupport i)) =
          ∑ i in s,
            FiniteCorrespondencePresentation.toGeom
              (FiniteCorrespondencePresentation.ofWeightedPrimeSupport
                (decomposition.toWeightedPrimeFiniteCorrespondenceSupport i)) := by
    intro s
    refine Finset.induction_on s ?_ ?_
    · simp [FiniteCorrespondencePresentation.toGeom_zero]
    · intro i s his ih
      simp [Finset.sum_insert, his, FiniteCorrespondencePresentation.toGeom_add, ih]
  rw [ProductFiniteCorrespondenceImageDecomposition.toFiniteCorrespondence,
    ProductFiniteCorrespondenceImageDecomposition.toPresentation]
  rw [hToGeom_sum Finset.univ]
  apply Finset.sum_congr rfl
  intro i _hi
  letI : IsIso (decomposition.toSourceImage i) := hIso i
  simpa [FiniteCorrespondencePresentation.ofWeightedPrimeSupport,
    FiniteCorrespondencePresentation.toGeom] using
      decomposition.ofWeighted_toRepresentedPrimeSupport_eq_diagonal_of_target_eq_source
        hTarget i (hmult i)

/-- Specialization of the sum-level diagonal normal form to the raw external
product of two diagonal represented supports. -/
theorem diagonal_externalProduct_decomposition_toFiniteCorrespondence_eq_sum_diagonal
    {X1 X2 : Geometry.SmSchemeOver k}
    (source1 : SourceIrreducibleComponent X1)
    (source2 : SourceIrreducibleComponent X2)
    (decomposition :
      ProductFiniteCorrespondenceImageDecomposition
        (PrimeFiniteCorrespondenceSupport.externalProductSupport
          (SourceIrreducibleComponent.diagonalRepresentedPrimeSupport (k := k) source1)
          (SourceIrreducibleComponent.diagonalRepresentedPrimeSupport (k := k) source2)))
    (hIso : ∀ i : decomposition.components.index,
      IsIso (decomposition.toSourceImage i))
    (hmult : ∀ i : decomposition.components.index,
      decomposition.multiplicity i = 1) :
    decomposition.toFiniteCorrespondence =
      ∑ i : decomposition.components.index,
        SourceImageSubscheme.diagonalFiniteCorrespondence
          (decomposition.toRepresentedPrimeSupport i).sourceComponent := by
  exact
    decomposition.toFiniteCorrespondence_eq_sum_diagonal_of_target_eq_source
      (PrimeFiniteCorrespondenceSupport.diagonal_externalProductSupport_toProductTarget_eq_toProductSource
        (k := k) source1 source2)
      hIso hmult

/-- Transport an image-based raw-support decomposition across a left
prime-support equivalence `P ≃ P'`. -/
def transportLeft
    {X1 Y1 X2 Y2 : Geometry.SmSchemeOver k}
    {P P' : RepresentedPrimeSupport X1 Y1}
    (h : PrimeSupportEquivalent P P')
    (Q : RepresentedPrimeSupport X2 Y2)
    (decomposition :
      ProductFiniteCorrespondenceImageDecomposition
        (PrimeFiniteCorrespondenceSupport.externalProductSupport P Q)) :
    ProductFiniteCorrespondenceImageDecomposition
      (PrimeFiniteCorrespondenceSupport.externalProductSupport P' Q) where
  components :=
    FiniteIntegralClosedComponentDecomposition.transport
      (PrimeFiniteCorrespondenceSupport.leftExternalProductSupportIso h Q)
      decomposition.components
  multiplicity := decomposition.multiplicity
  sourceImage := decomposition.sourceImage
  toSourceImage := decomposition.toSourceImage
  finite_toSourceImage := decomposition.finite_toSourceImage
  surjective_toSourceImage := decomposition.surjective_toSourceImage
  sourceImage_factorization := by
    intro i
    calc
      decomposition.toSourceImage i ≫ (decomposition.sourceImage i).inclusion =
          (decomposition.components.component i).carrier.inclusion ≫
            (PrimeFiniteCorrespondenceSupport.externalProductSupport P Q).toProductSource := by
            exact decomposition.sourceImage_factorization i
      _ = ((FiniteIntegralClosedComponentDecomposition.transport
            (PrimeFiniteCorrespondenceSupport.leftExternalProductSupportIso h Q)
            decomposition.components).component i).carrier.inclusion ≫
            (PrimeFiniteCorrespondenceSupport.externalProductSupport P' Q).toProductSource := by
            exact
              PrimeFiniteCorrespondenceSupport.leftExternalProductSupportIso_transport_factorization
                h Q (decomposition.components.component i).carrier
  toProductTarget := decomposition.toProductTarget
  target_factorization := by
    intro i
    calc
      decomposition.toProductTarget i =
          (decomposition.components.component i).carrier.inclusion ≫
            (PrimeFiniteCorrespondenceSupport.externalProductSupport P Q).toProductTarget := by
            exact decomposition.target_factorization i
      _ = ((FiniteIntegralClosedComponentDecomposition.transport
            (PrimeFiniteCorrespondenceSupport.leftExternalProductSupportIso h Q)
            decomposition.components).component i).carrier.inclusion ≫
            (PrimeFiniteCorrespondenceSupport.externalProductSupport P' Q).toProductTarget := by
            exact
              PrimeFiniteCorrespondenceSupport.leftExternalProductSupportIso_transport_target_factorization
                h Q (decomposition.components.component i).carrier
  inclusion := decomposition.inclusion
  inclusion_fst := decomposition.inclusion_fst
  inclusion_snd := decomposition.inclusion_snd
  isClosedImmersion := decomposition.isClosedImmersion

/-- Transport an image-based raw-support decomposition across a right
prime-support equivalence `Q ≃ Q'`. -/
def transportRight
    {X1 Y1 X2 Y2 : Geometry.SmSchemeOver k}
    (P : RepresentedPrimeSupport X1 Y1)
    {Q Q' : RepresentedPrimeSupport X2 Y2}
    (h : PrimeSupportEquivalent Q Q')
    (decomposition :
      ProductFiniteCorrespondenceImageDecomposition
        (PrimeFiniteCorrespondenceSupport.externalProductSupport P Q)) :
    ProductFiniteCorrespondenceImageDecomposition
      (PrimeFiniteCorrespondenceSupport.externalProductSupport P Q') where
  components :=
    FiniteIntegralClosedComponentDecomposition.transport
      (PrimeFiniteCorrespondenceSupport.rightExternalProductSupportIso P h)
      decomposition.components
  multiplicity := decomposition.multiplicity
  sourceImage := decomposition.sourceImage
  toSourceImage := decomposition.toSourceImage
  finite_toSourceImage := decomposition.finite_toSourceImage
  surjective_toSourceImage := decomposition.surjective_toSourceImage
  sourceImage_factorization := by
    intro i
    calc
      decomposition.toSourceImage i ≫ (decomposition.sourceImage i).inclusion =
          (decomposition.components.component i).carrier.inclusion ≫
            (PrimeFiniteCorrespondenceSupport.externalProductSupport P Q).toProductSource := by
            exact decomposition.sourceImage_factorization i
      _ = ((FiniteIntegralClosedComponentDecomposition.transport
            (PrimeFiniteCorrespondenceSupport.rightExternalProductSupportIso P h)
            decomposition.components).component i).carrier.inclusion ≫
            (PrimeFiniteCorrespondenceSupport.externalProductSupport P Q').toProductSource := by
            exact
              PrimeFiniteCorrespondenceSupport.rightExternalProductSupportIso_transport_factorization
                P h (decomposition.components.component i).carrier
  toProductTarget := decomposition.toProductTarget
  target_factorization := by
    intro i
    calc
      decomposition.toProductTarget i =
          (decomposition.components.component i).carrier.inclusion ≫
            (PrimeFiniteCorrespondenceSupport.externalProductSupport P Q).toProductTarget := by
            exact decomposition.target_factorization i
      _ = ((FiniteIntegralClosedComponentDecomposition.transport
            (PrimeFiniteCorrespondenceSupport.rightExternalProductSupportIso P h)
            decomposition.components).component i).carrier.inclusion ≫
            (PrimeFiniteCorrespondenceSupport.externalProductSupport P Q').toProductTarget := by
            exact
              PrimeFiniteCorrespondenceSupport.rightExternalProductSupportIso_transport_target_factorization
                P h (decomposition.components.component i).carrier
  inclusion := decomposition.inclusion
  inclusion_fst := decomposition.inclusion_fst
  inclusion_snd := decomposition.inclusion_snd
  isClosedImmersion := decomposition.isClosedImmersion

@[simp] theorem toWeightedPrimeFiniteCorrespondenceSupport_transportLeft
    {X1 Y1 X2 Y2 : Geometry.SmSchemeOver k}
    {P P' : RepresentedPrimeSupport X1 Y1}
    (h : PrimeSupportEquivalent P P')
    (Q : RepresentedPrimeSupport X2 Y2)
    (decomposition :
      ProductFiniteCorrespondenceImageDecomposition
        (PrimeFiniteCorrespondenceSupport.externalProductSupport P Q))
    (i : decomposition.components.index) :
    (transportLeft h Q decomposition).toWeightedPrimeFiniteCorrespondenceSupport i =
      decomposition.toWeightedPrimeFiniteCorrespondenceSupport i := rfl

@[simp] theorem toWeightedPrimeFiniteCorrespondenceSupport_transportRight
    {X1 Y1 X2 Y2 : Geometry.SmSchemeOver k}
    (P : RepresentedPrimeSupport X1 Y1)
    {Q Q' : RepresentedPrimeSupport X2 Y2}
    (h : PrimeSupportEquivalent Q Q')
    (decomposition :
      ProductFiniteCorrespondenceImageDecomposition
        (PrimeFiniteCorrespondenceSupport.externalProductSupport P Q))
    (i : decomposition.components.index) :
    (transportRight P h decomposition).toWeightedPrimeFiniteCorrespondenceSupport i =
      decomposition.toWeightedPrimeFiniteCorrespondenceSupport i := rfl

theorem toPresentation_transportLeft_eq
    {X1 Y1 X2 Y2 : Geometry.SmSchemeOver k}
    {P P' : RepresentedPrimeSupport X1 Y1}
    (h : PrimeSupportEquivalent P P')
    (Q : RepresentedPrimeSupport X2 Y2)
    (decomposition :
      ProductFiniteCorrespondenceImageDecomposition
        (PrimeFiniteCorrespondenceSupport.externalProductSupport P Q)) :
    (transportLeft h Q decomposition).toPresentation = decomposition.toPresentation := by
  classical
  simp [toPresentation]
  change
    (∑ i : decomposition.components.index,
      FiniteCorrespondencePresentation.ofWeightedPrimeSupport
        (decomposition.toWeightedPrimeFiniteCorrespondenceSupport i)) =
    ∑ i : decomposition.components.index,
      FiniteCorrespondencePresentation.ofWeightedPrimeSupport
        (decomposition.toWeightedPrimeFiniteCorrespondenceSupport i)
  rfl

theorem toPresentation_transportRight_eq
    {X1 Y1 X2 Y2 : Geometry.SmSchemeOver k}
    (P : RepresentedPrimeSupport X1 Y1)
    {Q Q' : RepresentedPrimeSupport X2 Y2}
    (h : PrimeSupportEquivalent Q Q')
    (decomposition :
      ProductFiniteCorrespondenceImageDecomposition
        (PrimeFiniteCorrespondenceSupport.externalProductSupport P Q)) :
    (transportRight P h decomposition).toPresentation = decomposition.toPresentation := by
  classical
  simp [toPresentation]
  change
    (∑ i : decomposition.components.index,
      FiniteCorrespondencePresentation.ofWeightedPrimeSupport
        (decomposition.toWeightedPrimeFiniteCorrespondenceSupport i)) =
    ∑ i : decomposition.components.index,
      FiniteCorrespondencePresentation.ofWeightedPrimeSupport
        (decomposition.toWeightedPrimeFiniteCorrespondenceSupport i)
  rfl

end ProductFiniteCorrespondenceImageDecomposition

namespace FiniteCorrespondencePresentation

@[simp] theorem toGeom_ofWeightedPrimeSupport_eq_of_primeSupportEquivalent
    {X Y : Geometry.SmSchemeOver k}
    {P Q : RepresentedPrimeSupport X Y}
    (h : PrimeSupportEquivalent P Q)
    (m : ℕ) :
    toGeom
      (ofWeightedPrimeSupport
        { multiplicity := m, prime := P }) =
      toGeom
        (ofWeightedPrimeSupport
          { multiplicity := m, prime := Q }) := by
  simp [ofWeightedPrimeSupport, toGeom]
  rw [PrimeFiniteCorrespondenceGeom.eq_of_primeSupportEquivalent h]

/-- Pointwise prime-support equivalence on a common finite index family yields
the same geometric finite correspondence after summing the weighted prime
pieces. This is the external-product sum-level bridge needed for left/right
quotient compatibility once componentwise transport is provided. -/
theorem toGeom_sum_weightedPrimeSupport_eq_of_pointwise_primeSupportEquivalent
    {X Y : Geometry.SmSchemeOver k}
    {ι : Type u} [Fintype ι] [DecidableEq ι]
    (left right : ι → WeightedPrimeFiniteCorrespondenceSupport X Y)
    (hmult : ∀ i, (left i).multiplicity = (right i).multiplicity)
    (heq : ∀ i, PrimeSupportEquivalent (left i).prime (right i).prime) :
    toGeom (Finset.univ.sum fun i => ofWeightedPrimeSupport (left i)) =
      toGeom (Finset.univ.sum fun i => ofWeightedPrimeSupport (right i)) := by
  classical
  refine Finset.induction_on Finset.univ ?base ?step
  · simp
  · intro i s his hs
    have hs' :
        toGeom (∑ j in s, ofWeightedPrimeSupport (left j)) =
          toGeom (∑ j in s, ofWeightedPrimeSupport (right j)) := by
      exact hs
    simp [Finset.sum_insert, his, toGeom_add, hs', hmult i,
      toGeom_ofWeightedPrimeSupport_eq_of_primeSupportEquivalent (heq i)]

end FiniteCorrespondencePresentation

namespace ProductFiniteCorrespondenceImageDecomposition

theorem toGeom_toPresentation_transportLeft_eq
    {X1 Y1 X2 Y2 : Geometry.SmSchemeOver k}
    {P P' : RepresentedPrimeSupport X1 Y1}
    (h : PrimeSupportEquivalent P P')
    (Q : RepresentedPrimeSupport X2 Y2)
    (decomposition :
      ProductFiniteCorrespondenceImageDecomposition
        (PrimeFiniteCorrespondenceSupport.externalProductSupport P Q)) :
      FiniteCorrespondencePresentation.toGeom (decomposition.toPresentation) =
      FiniteCorrespondencePresentation.toGeom
        ((transportLeft h Q decomposition).toPresentation) := by
  exact congrArg FiniteCorrespondencePresentation.toGeom
    (ProductFiniteCorrespondenceImageDecomposition.toPresentation_transportLeft_eq
      h Q decomposition).symm

theorem toGeom_toPresentation_transportRight_eq
    {X1 Y1 X2 Y2 : Geometry.SmSchemeOver k}
    (P : RepresentedPrimeSupport X1 Y1)
    {Q Q' : RepresentedPrimeSupport X2 Y2}
    (h : PrimeSupportEquivalent Q Q')
    (decomposition :
      ProductFiniteCorrespondenceImageDecomposition
        (PrimeFiniteCorrespondenceSupport.externalProductSupport P Q)) :
      FiniteCorrespondencePresentation.toGeom (decomposition.toPresentation) =
      FiniteCorrespondencePresentation.toGeom
        ((transportRight P h decomposition).toPresentation) := by
  exact congrArg FiniteCorrespondencePresentation.toGeom
    (ProductFiniteCorrespondenceImageDecomposition.toPresentation_transportRight_eq
      P h decomposition).symm

end ProductFiniteCorrespondenceImageDecomposition

/-- Honest represented-prime external product data.

For a represented prime pair `(P, Q)`, the raw product support is first built
at the support level. It is then decomposed into actual prime pieces on the
product source. Compatibility with `PrimeSupportEquivalent` ensures descent to
geometric prime-support classes. -/
structure RepresentedPrimeFiniteCorrespondenceExternalProduct where
  productSupport :
    {X1 Y1 X2 Y2 : Geometry.SmSchemeOver k} →
      RepresentedPrimeSupport X1 Y1 →
      RepresentedPrimeSupport X2 Y2 →
      ProductFiniteCorrespondenceSupport X1 Y1 X2 Y2
  decompose :
    {X1 Y1 X2 Y2 : Geometry.SmSchemeOver k} →
      (P : RepresentedPrimeSupport X1 Y1) →
      (Q : RepresentedPrimeSupport X2 Y2) →
      ProductFiniteCorrespondenceImageDecomposition (productSupport P Q)
  respects_left :
    ∀ {X1 Y1 X2 Y2 : Geometry.SmSchemeOver k}
      {P P' : RepresentedPrimeSupport X1 Y1}
      (_h : PrimeSupportEquivalent P P')
      (Q : RepresentedPrimeSupport X2 Y2),
        FiniteCorrespondencePresentation.toGeom ((decompose P Q).toPresentation) =
          FiniteCorrespondencePresentation.toGeom ((decompose P' Q).toPresentation)
  respects_right :
    ∀ {X1 Y1 X2 Y2 : Geometry.SmSchemeOver k}
      (P : RepresentedPrimeSupport X1 Y1)
      {Q Q' : RepresentedPrimeSupport X2 Y2}
      (_h : PrimeSupportEquivalent Q Q'),
        FiniteCorrespondencePresentation.toGeom ((decompose P Q).toPresentation) =
          FiniteCorrespondencePresentation.toGeom ((decompose P Q').toPresentation)

namespace RepresentedPrimeFiniteCorrespondenceExternalProduct

/-- Build the concrete represented-prime external-product datum from the actual
raw product-support geometry plus explicit decomposition input.

The geometric content is split exactly where the current codebase can support
it honestly:

* `PrimeFiniteCorrespondenceSupport.externalProductSupport` constructs the raw
  support `P.support ×_k Q.support` with its maps to the product source and
  target;
* `decompose` supplies the chosen irreducible-component decomposition of that
  raw support into prime pieces on the product source.

Compatibility with `PrimeSupportEquivalent` is kept explicit as part of the
input data needed to descend to geometric prime-support classes. -/
def representedPrimeExternalProduct
    (decompose :
      {X1 Y1 X2 Y2 : Geometry.SmSchemeOver k} →
        (P : RepresentedPrimeSupport X1 Y1) →
        (Q : RepresentedPrimeSupport X2 Y2) →
        ProductFiniteCorrespondenceImageDecomposition
          (PrimeFiniteCorrespondenceSupport.externalProductSupport P Q))
    (respects_left :
      ∀ {X1 Y1 X2 Y2 : Geometry.SmSchemeOver k}
        {P P' : RepresentedPrimeSupport X1 Y1}
        (_h : PrimeSupportEquivalent P P')
        (Q : RepresentedPrimeSupport X2 Y2),
          FiniteCorrespondencePresentation.toGeom ((decompose P Q).toPresentation) =
            FiniteCorrespondencePresentation.toGeom ((decompose P' Q).toPresentation))
    (respects_right :
      ∀ {X1 Y1 X2 Y2 : Geometry.SmSchemeOver k}
        (P : RepresentedPrimeSupport X1 Y1)
        {Q Q' : RepresentedPrimeSupport X2 Y2}
        (_h : PrimeSupportEquivalent Q Q'),
          FiniteCorrespondencePresentation.toGeom ((decompose P Q).toPresentation) =
            FiniteCorrespondencePresentation.toGeom ((decompose P Q').toPresentation)) :
    RepresentedPrimeFiniteCorrespondenceExternalProduct (k := k) where
  productSupport := PrimeFiniteCorrespondenceSupport.externalProductSupport
  decompose := decompose
  respects_left := respects_left
  respects_right := respects_right

/-- Build the represented-prime external-product datum from a decomposition
family that is coherent under transport across `PrimeSupportEquivalent` on the
left and right. This is the direct quotient-descent constructor: the coherence
assumptions identify `decompose P' Q` and `decompose P Q'` with the transported
decompositions, and the compatibility proofs are then discharged by the raw
support transport lemmas above. -/
def representedPrimeExternalProductOfTransport
    (decompose :
      {X1 Y1 X2 Y2 : Geometry.SmSchemeOver k} →
        (P : RepresentedPrimeSupport X1 Y1) →
        (Q : RepresentedPrimeSupport X2 Y2) →
        ProductFiniteCorrespondenceImageDecomposition
          (PrimeFiniteCorrespondenceSupport.externalProductSupport P Q))
    (left_transport :
      ∀ {X1 Y1 X2 Y2 : Geometry.SmSchemeOver k}
        {P P' : RepresentedPrimeSupport X1 Y1}
        (h : PrimeSupportEquivalent P P')
        (Q : RepresentedPrimeSupport X2 Y2),
          decompose P' Q =
            ProductFiniteCorrespondenceImageDecomposition.transportLeft h Q (decompose P Q))
    (right_transport :
      ∀ {X1 Y1 X2 Y2 : Geometry.SmSchemeOver k}
        (P : RepresentedPrimeSupport X1 Y1)
        {Q Q' : RepresentedPrimeSupport X2 Y2}
        (h : PrimeSupportEquivalent Q Q'),
          decompose P Q' =
            ProductFiniteCorrespondenceImageDecomposition.transportRight P h (decompose P Q)) :
    RepresentedPrimeFiniteCorrespondenceExternalProduct (k := k) :=
  representedPrimeExternalProduct (k := k) decompose
    (by
      intro X1 Y1 X2 Y2 P P' h Q
      have hleft :
          decompose P' Q =
            ProductFiniteCorrespondenceImageDecomposition.transportLeft h Q (decompose P Q) :=
        left_transport h Q
      change FiniteCorrespondencePresentation.toGeom ((decompose P Q).toPresentation) =
        FiniteCorrespondencePresentation.toGeom ((decompose P' Q).toPresentation)
      rw [hleft]
      exact ProductFiniteCorrespondenceImageDecomposition.toGeom_toPresentation_transportLeft_eq
        h Q (decompose P Q))
    (by
      intro X1 Y1 X2 Y2 P Q Q' h
      have hright :
          decompose P Q' =
            ProductFiniteCorrespondenceImageDecomposition.transportRight P h (decompose P Q) :=
        right_transport P h
      change FiniteCorrespondencePresentation.toGeom ((decompose P Q).toPresentation) =
        FiniteCorrespondencePresentation.toGeom ((decompose P Q').toPresentation)
      rw [hright]
      exact ProductFiniteCorrespondenceImageDecomposition.toGeom_toPresentation_transportRight_eq
        P h (decompose P Q))

/-- A transport-coherent family of raw external-product decompositions.

This is the exact frozen input needed to descend the represented-prime
external product to finite correspondences. -/
structure ExternalProductDecompositionFamily where
  decompose :
    {X1 Y1 X2 Y2 : Geometry.SmSchemeOver k} →
      (P : RepresentedPrimeSupport X1 Y1) →
      (Q : RepresentedPrimeSupport X2 Y2) →
      ProductFiniteCorrespondenceImageDecomposition
        (PrimeFiniteCorrespondenceSupport.externalProductSupport P Q)
  left_transport :
    ∀ {X1 Y1 X2 Y2 : Geometry.SmSchemeOver k}
      {P P' : RepresentedPrimeSupport X1 Y1}
      (h : PrimeSupportEquivalent P P')
      (Q : RepresentedPrimeSupport X2 Y2),
        decompose P' Q =
          ProductFiniteCorrespondenceImageDecomposition.transportLeft h Q (decompose P Q)
  right_transport :
    ∀ {X1 Y1 X2 Y2 : Geometry.SmSchemeOver k}
      (P : RepresentedPrimeSupport X1 Y1)
      {Q Q' : RepresentedPrimeSupport X2 Y2}
      (h : PrimeSupportEquivalent Q Q'),
        decompose P Q' =
          ProductFiniteCorrespondenceImageDecomposition.transportRight P h (decompose P Q)

namespace ExternalProductDecompositionFamily

/-- The represented-prime external-product datum induced by a transport-
coherent decomposition family. -/
def data
    (family : ExternalProductDecompositionFamily (k := k)) :
    RepresentedPrimeFiniteCorrespondenceExternalProduct (k := k) :=
  representedPrimeExternalProductOfTransport (k := k)
    family.decompose family.left_transport family.right_transport

@[simp] theorem data_extRepresented
    (family : ExternalProductDecompositionFamily (k := k))
    {X1 Y1 X2 Y2 : Geometry.SmSchemeOver k}
    (P : RepresentedPrimeSupport X1 Y1)
    (Q : RepresentedPrimeSupport X2 Y2) :
  (family.data.decompose P Q).toPresentation = (family.decompose P Q).toPresentation := rfl

end ExternalProductDecompositionFamily

def extRepresented
    (data : RepresentedPrimeFiniteCorrespondenceExternalProduct (k := k))
    {X1 Y1 X2 Y2 : Geometry.SmSchemeOver k}
    (P : RepresentedPrimeSupport X1 Y1)
    (Q : RepresentedPrimeSupport X2 Y2) :
    FiniteCorrespondencePresentation
      (overBaseProductObject X1 X2) (overBaseProductObject Y1 Y2) :=
  (data.decompose P Q).toPresentation

@[simp] theorem representedPrimeExternalProduct_productSupport
    (decompose :
      {X1 Y1 X2 Y2 : Geometry.SmSchemeOver k} →
        (P : RepresentedPrimeSupport X1 Y1) →
        (Q : RepresentedPrimeSupport X2 Y2) →
        ProductFiniteCorrespondenceImageDecomposition
          (PrimeFiniteCorrespondenceSupport.externalProductSupport P Q))
    (respects_left :
      ∀ {X1 Y1 X2 Y2 : Geometry.SmSchemeOver k}
        {P P' : RepresentedPrimeSupport X1 Y1}
        (_h : PrimeSupportEquivalent P P')
        (Q : RepresentedPrimeSupport X2 Y2),
          FiniteCorrespondencePresentation.toGeom ((decompose P Q).toPresentation) =
            FiniteCorrespondencePresentation.toGeom ((decompose P' Q).toPresentation))
    (respects_right :
      ∀ {X1 Y1 X2 Y2 : Geometry.SmSchemeOver k}
        (P : RepresentedPrimeSupport X1 Y1)
        {Q Q' : RepresentedPrimeSupport X2 Y2}
        (_h : PrimeSupportEquivalent Q Q'),
          FiniteCorrespondencePresentation.toGeom ((decompose P Q).toPresentation) =
            FiniteCorrespondencePresentation.toGeom ((decompose P Q').toPresentation))
    {X1 Y1 X2 Y2 : Geometry.SmSchemeOver k}
    (P : RepresentedPrimeSupport X1 Y1)
    (Q : RepresentedPrimeSupport X2 Y2) :
    (representedPrimeExternalProduct (k := k) decompose respects_left respects_right).productSupport P Q =
      PrimeFiniteCorrespondenceSupport.externalProductSupport P Q := rfl

@[simp] theorem representedPrimeExternalProduct_extRepresented
    (decompose :
      {X1 Y1 X2 Y2 : Geometry.SmSchemeOver k} →
        (P : RepresentedPrimeSupport X1 Y1) →
        (Q : RepresentedPrimeSupport X2 Y2) →
        ProductFiniteCorrespondenceImageDecomposition
          (PrimeFiniteCorrespondenceSupport.externalProductSupport P Q))
    (respects_left :
      ∀ {X1 Y1 X2 Y2 : Geometry.SmSchemeOver k}
        {P P' : RepresentedPrimeSupport X1 Y1}
        (_h : PrimeSupportEquivalent P P')
        (Q : RepresentedPrimeSupport X2 Y2),
          FiniteCorrespondencePresentation.toGeom ((decompose P Q).toPresentation) =
            FiniteCorrespondencePresentation.toGeom ((decompose P' Q).toPresentation))
    (respects_right :
      ∀ {X1 Y1 X2 Y2 : Geometry.SmSchemeOver k}
        (P : RepresentedPrimeSupport X1 Y1)
        {Q Q' : RepresentedPrimeSupport X2 Y2}
        (_h : PrimeSupportEquivalent Q Q'),
          FiniteCorrespondencePresentation.toGeom ((decompose P Q).toPresentation) =
            FiniteCorrespondencePresentation.toGeom ((decompose P Q').toPresentation))
    {X1 Y1 X2 Y2 : Geometry.SmSchemeOver k}
    (P : RepresentedPrimeSupport X1 Y1)
    (Q : RepresentedPrimeSupport X2 Y2) :
    (representedPrimeExternalProduct (k := k) decompose respects_left respects_right).extRepresented P Q =
      (decompose P Q).toPresentation := rfl

/-- Descended external product on geometric prime-support classes. -/
def extPrime
    (data : RepresentedPrimeFiniteCorrespondenceExternalProduct (k := k))
    {X1 Y1 X2 Y2 : Geometry.SmSchemeOver k}
    (left : PrimeFiniteCorrespondenceGeom X1 Y1)
    (right : PrimeFiniteCorrespondenceGeom X2 Y2) :
    FiniteCorrespondence
      (overBaseProductObject X1 X2) (overBaseProductObject Y1 Y2) := by
  classical
  refine Quotient.liftOn left
    (fun P =>
      Quotient.liftOn right
        (fun Q => FiniteCorrespondencePresentation.toGeom (data.extRepresented P Q))
        (by
          intro Q Q' hQQ'
          exact data.respects_right P hQQ')) ?_
  intro P P' hPP'
  refine Quotient.inductionOn right ?_
  intro Q
  exact data.respects_left hPP' Q

@[simp] theorem extPrime_ofRepresented
    (data : RepresentedPrimeFiniteCorrespondenceExternalProduct (k := k))
    {X1 Y1 X2 Y2 : Geometry.SmSchemeOver k}
    (P : RepresentedPrimeSupport X1 Y1)
    (Q : RepresentedPrimeSupport X2 Y2) :
    data.extPrime (PrimeFiniteCorrespondenceGeom.ofRepresented P)
        (PrimeFiniteCorrespondenceGeom.ofRepresented Q) =
      FiniteCorrespondencePresentation.toGeom (data.extRepresented P Q) :=
  rfl

namespace ExternalProductDecompositionFamily

@[simp] theorem data_extPrime_ofRepresented
    (family : ExternalProductDecompositionFamily (k := k))
    {X1 Y1 X2 Y2 : Geometry.SmSchemeOver k}
    (P : RepresentedPrimeSupport X1 Y1)
    (Q : RepresentedPrimeSupport X2 Y2) :
    family.data.extPrime
        (PrimeFiniteCorrespondenceGeom.ofRepresented P)
        (PrimeFiniteCorrespondenceGeom.ofRepresented Q) =
      FiniteCorrespondencePresentation.toGeom ((family.decompose P Q).toPresentation) := by
  calc
    family.data.extPrime
        (PrimeFiniteCorrespondenceGeom.ofRepresented P)
        (PrimeFiniteCorrespondenceGeom.ofRepresented Q) =
      FiniteCorrespondencePresentation.toGeom (family.data.extRepresented P Q) :=
        RepresentedPrimeFiniteCorrespondenceExternalProduct.extPrime_ofRepresented
          family.data P Q
    _ = FiniteCorrespondencePresentation.toGeom ((family.decompose P Q).toPresentation) :=
        congrArg FiniteCorrespondencePresentation.toGeom
          (ExternalProductDecompositionFamily.data_extRepresented family P Q)

end ExternalProductDecompositionFamily

/-- Bilinear extension of prime external product to arbitrary finite
correspondences. -/
def ext
    (data : RepresentedPrimeFiniteCorrespondenceExternalProduct (k := k))
    {X1 Y1 X2 Y2 : Geometry.SmSchemeOver k}
    (left : FiniteCorrespondence X1 Y1)
    (right : FiniteCorrespondence X2 Y2) :
    FiniteCorrespondence
      (overBaseProductObject X1 X2) (overBaseProductObject Y1 Y2) :=
  left.sum fun leftPrime leftCoeff =>
    right.sum fun rightPrime rightCoeff =>
      (leftCoeff * rightCoeff) • data.extPrime leftPrime rightPrime

@[simp] theorem ext_zero_left
    (data : RepresentedPrimeFiniteCorrespondenceExternalProduct (k := k))
    {X1 Y1 X2 Y2 : Geometry.SmSchemeOver k}
    (right : FiniteCorrespondence X2 Y2) :
    data.ext (0 : FiniteCorrespondence X1 Y1) right = 0 := by
  rw [ext]
  simp

@[simp] theorem ext_zero_right
    (data : RepresentedPrimeFiniteCorrespondenceExternalProduct (k := k))
    {X1 Y1 X2 Y2 : Geometry.SmSchemeOver k}
    (left : FiniteCorrespondence X1 Y1) :
    data.ext left (0 : FiniteCorrespondence X2 Y2) = 0 := by
  rw [ext]
  simp

@[simp] theorem ext_single_left
    (data : RepresentedPrimeFiniteCorrespondenceExternalProduct (k := k))
    {X1 Y1 X2 Y2 : Geometry.SmSchemeOver k}
    (leftPrime : PrimeFiniteCorrespondenceGeom X1 Y1)
    (leftCoeff : ℤ)
    (right : FiniteCorrespondence X2 Y2) :
    data.ext (Finsupp.single leftPrime leftCoeff) right =
      right.sum fun rightPrime rightCoeff =>
        (leftCoeff * rightCoeff) • data.extPrime leftPrime rightPrime := by
  classical
  rw [ext]
  simp

@[simp] theorem ext_single_right
    (data : RepresentedPrimeFiniteCorrespondenceExternalProduct (k := k))
    {X1 Y1 X2 Y2 : Geometry.SmSchemeOver k}
    (left : FiniteCorrespondence X1 Y1)
    (rightPrime : PrimeFiniteCorrespondenceGeom X2 Y2)
    (rightCoeff : ℤ) :
    data.ext left (Finsupp.single rightPrime rightCoeff) =
      left.sum fun leftPrime leftCoeff =>
        (leftCoeff * rightCoeff) • data.extPrime leftPrime rightPrime := by
  classical
  rw [ext]
  simp

@[simp] theorem ext_single_single
    (data : RepresentedPrimeFiniteCorrespondenceExternalProduct (k := k))
    {X1 Y1 X2 Y2 : Geometry.SmSchemeOver k}
    (leftPrime : PrimeFiniteCorrespondenceGeom X1 Y1)
    (rightPrime : PrimeFiniteCorrespondenceGeom X2 Y2)
    (leftCoeff rightCoeff : ℤ) :
    data.ext (Finsupp.single leftPrime leftCoeff)
        (Finsupp.single rightPrime rightCoeff) =
      (leftCoeff * rightCoeff) • data.extPrime leftPrime rightPrime := by
  classical
  rw [ext]
  simp

theorem ext_add_left
    (data : RepresentedPrimeFiniteCorrespondenceExternalProduct (k := k))
    {X1 Y1 X2 Y2 : Geometry.SmSchemeOver k}
    (left1 left2 : FiniteCorrespondence X1 Y1)
    (right : FiniteCorrespondence X2 Y2) :
    data.ext (left1 + left2) right = data.ext left1 right + data.ext left2 right := by
  classical
  rw [ext, ext, ext, Finsupp.sum_add_index'] <;>
    simp [add_mul, add_smul, zero_mul]

theorem ext_add_right
    (data : RepresentedPrimeFiniteCorrespondenceExternalProduct (k := k))
    {X1 Y1 X2 Y2 : Geometry.SmSchemeOver k}
    (left : FiniteCorrespondence X1 Y1)
    (right1 right2 : FiniteCorrespondence X2 Y2) :
    data.ext left (right1 + right2) = data.ext left right1 + data.ext left right2 := by
  classical
  rw [ext, ext, ext, ← Finsupp.sum_add]
  congr
  ext leftPrime leftCoeff
  rw [Finsupp.sum_add_index'] <;> simp [mul_add, add_smul, zero_mul]

theorem ext_smul_left
    (data : RepresentedPrimeFiniteCorrespondenceExternalProduct (k := k))
    {X1 Y1 X2 Y2 : Geometry.SmSchemeOver k}
    (coeff : ℤ)
    (left : FiniteCorrespondence X1 Y1)
    (right : FiniteCorrespondence X2 Y2) :
    data.ext (coeff • left) right = coeff • data.ext left right := by
  apply Finsupp.induction_linear left
  · simp
  · intro left1 left2 ih1 ih2
    rw [smul_add, ext_add_left, ih1, ih2, ext_add_left]
    exact (smul_add coeff (data.ext left1 right) (data.ext left2 right)).symm
  · intro leftPrime leftCoeff
    classical
    simp [ext_single_left]
    rw [Finsupp.smul_sum]
    refine Finset.sum_congr rfl ?_
    intro rightPrime _hmem
    simp [mul_assoc, mul_left_comm, mul_comm, smul_smul]

theorem ext_smul_right
    (data : RepresentedPrimeFiniteCorrespondenceExternalProduct (k := k))
    {X1 Y1 X2 Y2 : Geometry.SmSchemeOver k}
    (coeff : ℤ)
    (left : FiniteCorrespondence X1 Y1)
    (right : FiniteCorrespondence X2 Y2) :
    data.ext left (coeff • right) = coeff • data.ext left right := by
  apply Finsupp.induction_linear right
  · simp
  · intro right1 right2 ih1 ih2
    rw [smul_add, ext_add_right, ih1, ih2, ext_add_right]
    exact (smul_add coeff (data.ext left right1) (data.ext left right2)).symm
  · intro rightPrime rightCoeff
    classical
    simp [ext_single_right]
    rw [Finsupp.smul_sum]
    refine Finset.sum_congr rfl ?_
    intro leftPrime _hmem
    simp [mul_assoc, mul_left_comm, mul_comm, smul_smul]

@[simp] theorem representedPrimeExternalProduct_ext_zero_left
    (decompose :
      {X1 Y1 X2 Y2 : Geometry.SmSchemeOver k} →
        (P : RepresentedPrimeSupport X1 Y1) →
        (Q : RepresentedPrimeSupport X2 Y2) →
        ProductFiniteCorrespondenceImageDecomposition
          (PrimeFiniteCorrespondenceSupport.externalProductSupport P Q))
    (respects_left :
      ∀ {X1 Y1 X2 Y2 : Geometry.SmSchemeOver k}
        {P P' : RepresentedPrimeSupport X1 Y1}
        (_h : PrimeSupportEquivalent P P')
        (Q : RepresentedPrimeSupport X2 Y2),
          FiniteCorrespondencePresentation.toGeom ((decompose P Q).toPresentation) =
            FiniteCorrespondencePresentation.toGeom ((decompose P' Q).toPresentation))
    (respects_right :
      ∀ {X1 Y1 X2 Y2 : Geometry.SmSchemeOver k}
        (P : RepresentedPrimeSupport X1 Y1)
        {Q Q' : RepresentedPrimeSupport X2 Y2}
        (_h : PrimeSupportEquivalent Q Q'),
          FiniteCorrespondencePresentation.toGeom ((decompose P Q).toPresentation) =
            FiniteCorrespondencePresentation.toGeom ((decompose P Q').toPresentation))
    {X1 Y1 X2 Y2 : Geometry.SmSchemeOver k}
    (right : FiniteCorrespondence X2 Y2) :
    (representedPrimeExternalProduct (k := k) decompose respects_left respects_right).ext
        (0 : FiniteCorrespondence X1 Y1) right = 0 :=
  ext_zero_left _ right

theorem representedPrimeExternalProduct_ext_add_left
    (decompose :
      {X1 Y1 X2 Y2 : Geometry.SmSchemeOver k} →
        (P : RepresentedPrimeSupport X1 Y1) →
        (Q : RepresentedPrimeSupport X2 Y2) →
        ProductFiniteCorrespondenceImageDecomposition
          (PrimeFiniteCorrespondenceSupport.externalProductSupport P Q))
    (respects_left :
      ∀ {X1 Y1 X2 Y2 : Geometry.SmSchemeOver k}
        {P P' : RepresentedPrimeSupport X1 Y1}
        (_h : PrimeSupportEquivalent P P')
        (Q : RepresentedPrimeSupport X2 Y2),
          FiniteCorrespondencePresentation.toGeom ((decompose P Q).toPresentation) =
            FiniteCorrespondencePresentation.toGeom ((decompose P' Q).toPresentation))
    (respects_right :
      ∀ {X1 Y1 X2 Y2 : Geometry.SmSchemeOver k}
        (P : RepresentedPrimeSupport X1 Y1)
        {Q Q' : RepresentedPrimeSupport X2 Y2}
        (_h : PrimeSupportEquivalent Q Q'),
          FiniteCorrespondencePresentation.toGeom ((decompose P Q).toPresentation) =
            FiniteCorrespondencePresentation.toGeom ((decompose P Q').toPresentation))
    {X1 Y1 X2 Y2 : Geometry.SmSchemeOver k}
    (left1 left2 : FiniteCorrespondence X1 Y1)
    (right : FiniteCorrespondence X2 Y2) :
    (representedPrimeExternalProduct (k := k) decompose respects_left respects_right).ext
        (left1 + left2) right =
      (representedPrimeExternalProduct (k := k) decompose respects_left respects_right).ext left1 right +
      (representedPrimeExternalProduct (k := k) decompose respects_left respects_right).ext left2 right :=
  ext_add_left _ left1 left2 right

theorem representedPrimeExternalProduct_ext_add_right
    (decompose :
      {X1 Y1 X2 Y2 : Geometry.SmSchemeOver k} →
        (P : RepresentedPrimeSupport X1 Y1) →
        (Q : RepresentedPrimeSupport X2 Y2) →
        ProductFiniteCorrespondenceImageDecomposition
          (PrimeFiniteCorrespondenceSupport.externalProductSupport P Q))
    (respects_left :
      ∀ {X1 Y1 X2 Y2 : Geometry.SmSchemeOver k}
        {P P' : RepresentedPrimeSupport X1 Y1}
        (_h : PrimeSupportEquivalent P P')
        (Q : RepresentedPrimeSupport X2 Y2),
          FiniteCorrespondencePresentation.toGeom ((decompose P Q).toPresentation) =
            FiniteCorrespondencePresentation.toGeom ((decompose P' Q).toPresentation))
    (respects_right :
      ∀ {X1 Y1 X2 Y2 : Geometry.SmSchemeOver k}
        (P : RepresentedPrimeSupport X1 Y1)
        {Q Q' : RepresentedPrimeSupport X2 Y2}
        (_h : PrimeSupportEquivalent Q Q'),
          FiniteCorrespondencePresentation.toGeom ((decompose P Q).toPresentation) =
            FiniteCorrespondencePresentation.toGeom ((decompose P Q').toPresentation))
    {X1 Y1 X2 Y2 : Geometry.SmSchemeOver k}
    (left : FiniteCorrespondence X1 Y1)
    (right1 right2 : FiniteCorrespondence X2 Y2) :
    (representedPrimeExternalProduct (k := k) decompose respects_left respects_right).ext
        left (right1 + right2) =
      (representedPrimeExternalProduct (k := k) decompose respects_left respects_right).ext left right1 +
      (representedPrimeExternalProduct (k := k) decompose respects_left respects_right).ext left right2 :=
  ext_add_right _ left right1 right2

theorem representedPrimeExternalProduct_ext_smul_left
    (decompose :
      {X1 Y1 X2 Y2 : Geometry.SmSchemeOver k} →
        (P : RepresentedPrimeSupport X1 Y1) →
        (Q : RepresentedPrimeSupport X2 Y2) →
        ProductFiniteCorrespondenceImageDecomposition
          (PrimeFiniteCorrespondenceSupport.externalProductSupport P Q))
    (respects_left :
      ∀ {X1 Y1 X2 Y2 : Geometry.SmSchemeOver k}
        {P P' : RepresentedPrimeSupport X1 Y1}
        (_h : PrimeSupportEquivalent P P')
        (Q : RepresentedPrimeSupport X2 Y2),
          FiniteCorrespondencePresentation.toGeom ((decompose P Q).toPresentation) =
            FiniteCorrespondencePresentation.toGeom ((decompose P' Q).toPresentation))
    (respects_right :
      ∀ {X1 Y1 X2 Y2 : Geometry.SmSchemeOver k}
        (P : RepresentedPrimeSupport X1 Y1)
        {Q Q' : RepresentedPrimeSupport X2 Y2}
        (_h : PrimeSupportEquivalent Q Q'),
          FiniteCorrespondencePresentation.toGeom ((decompose P Q).toPresentation) =
            FiniteCorrespondencePresentation.toGeom ((decompose P Q').toPresentation))
    {X1 Y1 X2 Y2 : Geometry.SmSchemeOver k}
    (coeff : ℤ)
    (left : FiniteCorrespondence X1 Y1)
    (right : FiniteCorrespondence X2 Y2) :
    (representedPrimeExternalProduct (k := k) decompose respects_left respects_right).ext
        (coeff • left) right =
      coeff • (representedPrimeExternalProduct (k := k) decompose respects_left respects_right).ext left right :=
  ext_smul_left _ coeff left right

theorem representedPrimeExternalProduct_ext_smul_right
    (decompose :
      {X1 Y1 X2 Y2 : Geometry.SmSchemeOver k} →
        (P : RepresentedPrimeSupport X1 Y1) →
        (Q : RepresentedPrimeSupport X2 Y2) →
        ProductFiniteCorrespondenceImageDecomposition
          (PrimeFiniteCorrespondenceSupport.externalProductSupport P Q))
    (respects_left :
      ∀ {X1 Y1 X2 Y2 : Geometry.SmSchemeOver k}
        {P P' : RepresentedPrimeSupport X1 Y1}
        (_h : PrimeSupportEquivalent P P')
        (Q : RepresentedPrimeSupport X2 Y2),
          FiniteCorrespondencePresentation.toGeom ((decompose P Q).toPresentation) =
            FiniteCorrespondencePresentation.toGeom ((decompose P' Q).toPresentation))
    (respects_right :
      ∀ {X1 Y1 X2 Y2 : Geometry.SmSchemeOver k}
        (P : RepresentedPrimeSupport X1 Y1)
        {Q Q' : RepresentedPrimeSupport X2 Y2}
        (_h : PrimeSupportEquivalent Q Q'),
          FiniteCorrespondencePresentation.toGeom ((decompose P Q).toPresentation) =
            FiniteCorrespondencePresentation.toGeom ((decompose P Q').toPresentation))
    {X1 Y1 X2 Y2 : Geometry.SmSchemeOver k}
    (coeff : ℤ)
    (left : FiniteCorrespondence X1 Y1)
    (right : FiniteCorrespondence X2 Y2) :
    (representedPrimeExternalProduct (k := k) decompose respects_left respects_right).ext
        left (coeff • right) =
      coeff • (representedPrimeExternalProduct (k := k) decompose respects_left respects_right).ext left right :=
  ext_smul_right _ coeff left right

end RepresentedPrimeFiniteCorrespondenceExternalProduct

namespace FiniteCorrespondence

/-- Generic algebra over a supplied transport-coherent decomposition family.

This remains available for internal proof combinators, but it is not the
public canonical tensor route. -/
def externalProductWithFamily
    (family :
      RepresentedPrimeFiniteCorrespondenceExternalProduct.ExternalProductDecompositionFamily
        (k := k))
    {X1 Y1 X2 Y2 : Geometry.SmSchemeOver k}
    (left : FiniteCorrespondence X1 Y1)
    (right : FiniteCorrespondence X2 Y2) :
    FiniteCorrespondence
      (overBaseProductObject X1 X2) (overBaseProductObject Y1 Y2) :=
  family.data.ext left right

@[simp] theorem externalProductWithFamily_zero_left
    (family :
      RepresentedPrimeFiniteCorrespondenceExternalProduct.ExternalProductDecompositionFamily
        (k := k))
    {X1 Y1 X2 Y2 : Geometry.SmSchemeOver k}
    (right : FiniteCorrespondence X2 Y2) :
    externalProductWithFamily family (0 : FiniteCorrespondence X1 Y1) right = 0 := by
  exact
    RepresentedPrimeFiniteCorrespondenceExternalProduct.ext_zero_left family.data right

@[simp] theorem externalProductWithFamily_zero_right
    (family :
      RepresentedPrimeFiniteCorrespondenceExternalProduct.ExternalProductDecompositionFamily
        (k := k))
    {X1 Y1 X2 Y2 : Geometry.SmSchemeOver k}
    (left : FiniteCorrespondence X1 Y1) :
    externalProductWithFamily family left (0 : FiniteCorrespondence X2 Y2) = 0 := by
  exact
    RepresentedPrimeFiniteCorrespondenceExternalProduct.ext_zero_right family.data left

theorem externalProductWithFamily_add_left
    (family :
      RepresentedPrimeFiniteCorrespondenceExternalProduct.ExternalProductDecompositionFamily
        (k := k))
    {X1 Y1 X2 Y2 : Geometry.SmSchemeOver k}
    (left1 left2 : FiniteCorrespondence X1 Y1)
    (right : FiniteCorrespondence X2 Y2) :
    externalProductWithFamily family (left1 + left2) right =
      externalProductWithFamily family left1 right + externalProductWithFamily family left2 right := by
  exact
    RepresentedPrimeFiniteCorrespondenceExternalProduct.ext_add_left family.data left1 left2 right

theorem externalProductWithFamily_add_right
    (family :
      RepresentedPrimeFiniteCorrespondenceExternalProduct.ExternalProductDecompositionFamily
        (k := k))
    {X1 Y1 X2 Y2 : Geometry.SmSchemeOver k}
    (left : FiniteCorrespondence X1 Y1)
    (right1 right2 : FiniteCorrespondence X2 Y2) :
    externalProductWithFamily family left (right1 + right2) =
      externalProductWithFamily family left right1 + externalProductWithFamily family left right2 := by
  exact
    RepresentedPrimeFiniteCorrespondenceExternalProduct.ext_add_right family.data left right1 right2

theorem externalProductWithFamily_sum_left
    (family :
      RepresentedPrimeFiniteCorrespondenceExternalProduct.ExternalProductDecompositionFamily
        (k := k))
    {ι : Type*}
    (s : Finset ι)
    {X1 Y1 X2 Y2 : Geometry.SmSchemeOver k}
    (left : ι → FiniteCorrespondence X1 Y1)
    (right : FiniteCorrespondence X2 Y2) :
    externalProductWithFamily family (∑ i in s, left i) right =
      ∑ i in s, externalProductWithFamily family (left i) right := by
  classical
  refine Finset.induction_on s ?_ ?_
  · rw [Finset.sum_empty, Finset.sum_empty, externalProductWithFamily_zero_left]
  · intro i s hi ih
    rw [Finset.sum_insert hi, Finset.sum_insert hi,
      externalProductWithFamily_add_left, ih]

theorem externalProductWithFamily_sum_right
    (family :
      RepresentedPrimeFiniteCorrespondenceExternalProduct.ExternalProductDecompositionFamily
        (k := k))
    {ι : Type*}
    (s : Finset ι)
    {X1 Y1 X2 Y2 : Geometry.SmSchemeOver k}
    (left : FiniteCorrespondence X1 Y1)
    (right : ι → FiniteCorrespondence X2 Y2) :
    externalProductWithFamily family left (∑ i in s, right i) =
      ∑ i in s, externalProductWithFamily family left (right i) := by
  classical
  refine Finset.induction_on s ?_ ?_
  · rw [Finset.sum_empty, Finset.sum_empty, externalProductWithFamily_zero_right]
  · intro i s hi ih
    rw [Finset.sum_insert hi, Finset.sum_insert hi,
      externalProductWithFamily_add_right, ih]

theorem externalProductWithFamily_smul_left
    (family :
      RepresentedPrimeFiniteCorrespondenceExternalProduct.ExternalProductDecompositionFamily
        (k := k))
    {X1 Y1 X2 Y2 : Geometry.SmSchemeOver k}
    (coeff : ℤ)
    (left : FiniteCorrespondence X1 Y1)
    (right : FiniteCorrespondence X2 Y2) :
    externalProductWithFamily family (coeff • left) right =
      coeff • externalProductWithFamily family left right := by
  exact
    RepresentedPrimeFiniteCorrespondenceExternalProduct.ext_smul_left family.data coeff left right

theorem externalProductWithFamily_smul_right
    (family :
      RepresentedPrimeFiniteCorrespondenceExternalProduct.ExternalProductDecompositionFamily
        (k := k))
    {X1 Y1 X2 Y2 : Geometry.SmSchemeOver k}
    (coeff : ℤ)
    (left : FiniteCorrespondence X1 Y1)
    (right : FiniteCorrespondence X2 Y2) :
    externalProductWithFamily family left (coeff • right) =
      coeff • externalProductWithFamily family left right := by
  exact
    RepresentedPrimeFiniteCorrespondenceExternalProduct.ext_smul_right family.data coeff left right

@[simp] theorem externalProductWithFamily_single_single
    (family :
      RepresentedPrimeFiniteCorrespondenceExternalProduct.ExternalProductDecompositionFamily
        (k := k))
    {X1 Y1 X2 Y2 : Geometry.SmSchemeOver k}
    (leftPrime : PrimeFiniteCorrespondenceGeom X1 Y1)
    (rightPrime : PrimeFiniteCorrespondenceGeom X2 Y2)
    (leftCoeff rightCoeff : ℤ) :
    externalProductWithFamily family
        (Finsupp.single leftPrime leftCoeff)
        (Finsupp.single rightPrime rightCoeff) =
      (leftCoeff * rightCoeff) •
        family.data.extPrime leftPrime rightPrime := by
  exact
    RepresentedPrimeFiniteCorrespondenceExternalProduct.ext_single_single
      family.data leftPrime rightPrime leftCoeff rightCoeff

@[simp] theorem externalProductWithFamily_single_single_one
    (family :
      RepresentedPrimeFiniteCorrespondenceExternalProduct.ExternalProductDecompositionFamily
        (k := k))
    {X1 Y1 X2 Y2 : Geometry.SmSchemeOver k}
    (leftPrime : PrimeFiniteCorrespondenceGeom X1 Y1)
    (rightPrime : PrimeFiniteCorrespondenceGeom X2 Y2) :
    externalProductWithFamily family
        (Finsupp.single leftPrime 1)
        (Finsupp.single rightPrime 1) =
      family.data.extPrime leftPrime rightPrime := by
  simpa using
    externalProductWithFamily_single_single
      (family := family) leftPrime rightPrime (leftCoeff := 1) (rightCoeff := 1)

theorem externalProductWithFamily_single_single_eq_smul_one
    (family :
      RepresentedPrimeFiniteCorrespondenceExternalProduct.ExternalProductDecompositionFamily
        (k := k))
    {X1 Y1 X2 Y2 : Geometry.SmSchemeOver k}
    (leftPrime : PrimeFiniteCorrespondenceGeom X1 Y1)
    (rightPrime : PrimeFiniteCorrespondenceGeom X2 Y2)
    (leftCoeff rightCoeff : ℤ) :
    externalProductWithFamily family
        (Finsupp.single leftPrime leftCoeff)
        (Finsupp.single rightPrime rightCoeff) =
      (leftCoeff * rightCoeff) •
        externalProductWithFamily family
          (Finsupp.single leftPrime 1) (Finsupp.single rightPrime 1) := by
  rw [externalProductWithFamily_single_single,
    externalProductWithFamily_single_single_one]

@[simp] theorem externalProductWithFamily_single_single_ofRepresented_one
    (family :
      RepresentedPrimeFiniteCorrespondenceExternalProduct.ExternalProductDecompositionFamily
        (k := k))
    {X1 Y1 X2 Y2 : Geometry.SmSchemeOver k}
    (P : RepresentedPrimeSupport X1 Y1)
    (Q : RepresentedPrimeSupport X2 Y2) :
    externalProductWithFamily family
        (Finsupp.single (PrimeFiniteCorrespondenceGeom.ofRepresented P) 1)
        (Finsupp.single (PrimeFiniteCorrespondenceGeom.ofRepresented Q) 1) =
      FiniteCorrespondencePresentation.toGeom ((family.decompose P Q).toPresentation) := by
  simpa using
    congrArg id
      (RepresentedPrimeFiniteCorrespondenceExternalProduct.ExternalProductDecompositionFamily.data_extPrime_ofRepresented
        (family := family) P Q)

/-- Singleton diagonal external products reduce to the diagonal sum of the
actual image components of the chosen raw diagonal product decomposition,
provided those concrete components map isomorphically to their source images
and occur with multiplicity one. -/
theorem externalProductWithFamily_diagonal_single_single_eq_sum_diagonal
    (family :
      RepresentedPrimeFiniteCorrespondenceExternalProduct.ExternalProductDecompositionFamily
        (k := k))
    {X Y : Geometry.SmSchemeOver k}
    (sourceX : SourceIrreducibleComponent X)
    (sourceY : SourceIrreducibleComponent Y)
    (hIso :
      ∀ i :
        (family.decompose
          (SourceIrreducibleComponent.diagonalRepresentedPrimeSupport (k := k) sourceX)
          (SourceIrreducibleComponent.diagonalRepresentedPrimeSupport (k := k) sourceY)).components.index,
        IsIso
          ((family.decompose
            (SourceIrreducibleComponent.diagonalRepresentedPrimeSupport (k := k) sourceX)
            (SourceIrreducibleComponent.diagonalRepresentedPrimeSupport (k := k) sourceY)).toSourceImage i))
    (hmult :
      ∀ i :
        (family.decompose
          (SourceIrreducibleComponent.diagonalRepresentedPrimeSupport (k := k) sourceX)
          (SourceIrreducibleComponent.diagonalRepresentedPrimeSupport (k := k) sourceY)).components.index,
        (family.decompose
          (SourceIrreducibleComponent.diagonalRepresentedPrimeSupport (k := k) sourceX)
          (SourceIrreducibleComponent.diagonalRepresentedPrimeSupport (k := k) sourceY)).multiplicity i = 1) :
    externalProductWithFamily family
        (SourceIrreducibleComponent.diagonalFiniteCorrespondence sourceX)
        (SourceIrreducibleComponent.diagonalFiniteCorrespondence sourceY) =
      ∑ i :
        (family.decompose
          (SourceIrreducibleComponent.diagonalRepresentedPrimeSupport (k := k) sourceX)
          (SourceIrreducibleComponent.diagonalRepresentedPrimeSupport (k := k) sourceY)).components.index,
        SourceImageSubscheme.diagonalFiniteCorrespondence
          ((family.decompose
            (SourceIrreducibleComponent.diagonalRepresentedPrimeSupport (k := k) sourceX)
            (SourceIrreducibleComponent.diagonalRepresentedPrimeSupport (k := k) sourceY)).toRepresentedPrimeSupport i).sourceComponent := by
  classical
  let P := SourceIrreducibleComponent.diagonalRepresentedPrimeSupport (k := k) sourceX
  let Q := SourceIrreducibleComponent.diagonalRepresentedPrimeSupport (k := k) sourceY
  let decomposition := family.decompose P Q
  calc
    externalProductWithFamily family
        (SourceIrreducibleComponent.diagonalFiniteCorrespondence sourceX)
        (SourceIrreducibleComponent.diagonalFiniteCorrespondence sourceY)
        =
      externalProductWithFamily family
        (Finsupp.single (SourceIrreducibleComponent.diagonalPrimeGeom sourceX) 1)
        (Finsupp.single (SourceIrreducibleComponent.diagonalPrimeGeom sourceY) 1) := by
        rfl
    _ = FiniteCorrespondencePresentation.toGeom decomposition.toPresentation := by
        simpa [P, Q, decomposition,
          SourceIrreducibleComponent.diagonalPrimeGeom] using
          externalProductWithFamily_single_single_ofRepresented_one
            (family := family) P Q
    _ = decomposition.toFiniteCorrespondence := by
        rfl
    _ = ∑ i : decomposition.components.index,
        SourceImageSubscheme.diagonalFiniteCorrespondence
          (decomposition.toRepresentedPrimeSupport i).sourceComponent := by
        exact
          _root_.Boundary.ProductFiniteCorrespondenceImageDecomposition.diagonal_externalProduct_decomposition_toFiniteCorrespondence_eq_sum_diagonal
            sourceX sourceY decomposition
            (by
              intro i
              exact hIso i)
            (by
              intro i
              exact hmult i)

/-- The identity-by-identity external product is a sum of diagonal pieces from
the actual raw diagonal product decompositions. This is the bilinear lift of
`externalProductWithFamily_diagonal_single_single_eq_sum_diagonal`; it keeps
the remaining geometry localized to the concrete diagonal decompositions. -/
theorem externalProductWithFamily_identity_identity_eq_sum_diagonal_decompositions
    (family :
      RepresentedPrimeFiniteCorrespondenceExternalProduct.ExternalProductDecompositionFamily
        (k := k))
    {X Y : Geometry.SmSchemeOver k}
    (DX : FiniteIrreducibleComponentDecomposition X)
    (DY : FiniteIrreducibleComponentDecomposition Y)
    (hIso :
      ∀ (sourceX : { sourceX : SourceIrreducibleComponent X // sourceX ∈ DX.components })
        (sourceY : { sourceY : SourceIrreducibleComponent Y // sourceY ∈ DY.components })
        (i :
          (family.decompose
            (SourceIrreducibleComponent.diagonalRepresentedPrimeSupport (k := k) sourceX.1)
            (SourceIrreducibleComponent.diagonalRepresentedPrimeSupport (k := k) sourceY.1)).components.index),
          IsIso
            ((family.decompose
              (SourceIrreducibleComponent.diagonalRepresentedPrimeSupport (k := k) sourceX.1)
              (SourceIrreducibleComponent.diagonalRepresentedPrimeSupport (k := k) sourceY.1)).toSourceImage i))
    (hmult :
      ∀ (sourceX : { sourceX : SourceIrreducibleComponent X // sourceX ∈ DX.components })
        (sourceY : { sourceY : SourceIrreducibleComponent Y // sourceY ∈ DY.components })
        (i :
          (family.decompose
            (SourceIrreducibleComponent.diagonalRepresentedPrimeSupport (k := k) sourceX.1)
            (SourceIrreducibleComponent.diagonalRepresentedPrimeSupport (k := k) sourceY.1)).components.index),
          (family.decompose
            (SourceIrreducibleComponent.diagonalRepresentedPrimeSupport (k := k) sourceX.1)
            (SourceIrreducibleComponent.diagonalRepresentedPrimeSupport (k := k) sourceY.1)).multiplicity i = 1) :
    externalProductWithFamily family
        DX.identityFiniteCorrespondence DY.identityFiniteCorrespondence =
      ∑ sourceX : { sourceX : SourceIrreducibleComponent X // sourceX ∈ DX.components },
        ∑ sourceY : { sourceY : SourceIrreducibleComponent Y // sourceY ∈ DY.components },
          ∑ i :
            (family.decompose
              (SourceIrreducibleComponent.diagonalRepresentedPrimeSupport (k := k) sourceX.1)
              (SourceIrreducibleComponent.diagonalRepresentedPrimeSupport (k := k) sourceY.1)).components.index,
            SourceImageSubscheme.diagonalFiniteCorrespondence
              ((family.decompose
                (SourceIrreducibleComponent.diagonalRepresentedPrimeSupport (k := k) sourceX.1)
                (SourceIrreducibleComponent.diagonalRepresentedPrimeSupport (k := k) sourceY.1)).toRepresentedPrimeSupport i).sourceComponent := by
  classical
  rw [FiniteIrreducibleComponentDecomposition.identityFiniteCorrespondence_eq_sum_components,
    FiniteIrreducibleComponentDecomposition.identityFiniteCorrespondence_eq_sum_components]
  rw [← Finset.sum_attach]
  rw [externalProductWithFamily_sum_left]
  apply Finset.sum_congr rfl
  intro sourceX _hsourceX
  rw [← Finset.sum_attach]
  rw [externalProductWithFamily_sum_right]
  apply Finset.sum_congr rfl
  intro sourceY _hsourceY
  exact
    externalProductWithFamily_diagonal_single_single_eq_sum_diagonal
      (family := family) sourceX.1 sourceY.1
      (by
        intro i
        exact hIso sourceX sourceY i)
      (by
        intro i
        exact hmult sourceX sourceY i)

/-- If the diagonal pieces produced by the raw identity-product
decompositions are identified bijectively with the listed components of a
certified product decomposition, then the external product of the two identity
finite correspondences is the canonical identity finite correspondence on the
product.

The only remaining input is the geometric bijection between actual decomposed
diagonal pieces and the certified product components; the algebraic
coefficient comparison is owned here. -/
theorem externalProductWithFamily_identity_identity_eq_identityFiniteCorrespondence_of_equiv_diagonal_decompositions
    (family :
      RepresentedPrimeFiniteCorrespondenceExternalProduct.ExternalProductDecompositionFamily
        (k := k))
    {X Y : Geometry.SmSchemeOver k}
    (DX : FiniteIrreducibleComponentDecomposition X)
    (DY : FiniteIrreducibleComponentDecomposition Y)
    (DProduct : FiniteIrreducibleComponentDecomposition (overBaseProductObject X Y))
    (hIso :
      ∀ (sourceX : { sourceX : SourceIrreducibleComponent X // sourceX ∈ DX.components })
        (sourceY : { sourceY : SourceIrreducibleComponent Y // sourceY ∈ DY.components })
        (i :
          (family.decompose
            (SourceIrreducibleComponent.diagonalRepresentedPrimeSupport (k := k) sourceX.1)
            (SourceIrreducibleComponent.diagonalRepresentedPrimeSupport (k := k) sourceY.1)).components.index),
          IsIso
            ((family.decompose
              (SourceIrreducibleComponent.diagonalRepresentedPrimeSupport (k := k) sourceX.1)
              (SourceIrreducibleComponent.diagonalRepresentedPrimeSupport (k := k) sourceY.1)).toSourceImage i))
    (hmult :
      ∀ (sourceX : { sourceX : SourceIrreducibleComponent X // sourceX ∈ DX.components })
        (sourceY : { sourceY : SourceIrreducibleComponent Y // sourceY ∈ DY.components })
        (i :
          (family.decompose
            (SourceIrreducibleComponent.diagonalRepresentedPrimeSupport (k := k) sourceX.1)
            (SourceIrreducibleComponent.diagonalRepresentedPrimeSupport (k := k) sourceY.1)).components.index),
          (family.decompose
            (SourceIrreducibleComponent.diagonalRepresentedPrimeSupport (k := k) sourceX.1)
            (SourceIrreducibleComponent.diagonalRepresentedPrimeSupport (k := k) sourceY.1)).multiplicity i = 1)
    (listedEquiv :
      (Σ sourceX : { sourceX : SourceIrreducibleComponent X // sourceX ∈ DX.components },
        Σ sourceY : { sourceY : SourceIrreducibleComponent Y // sourceY ∈ DY.components },
          (family.decompose
            (SourceIrreducibleComponent.diagonalRepresentedPrimeSupport (k := k) sourceX.1)
            (SourceIrreducibleComponent.diagonalRepresentedPrimeSupport (k := k) sourceY.1)).components.index)
        ≃ { listed : SourceIrreducibleComponent (overBaseProductObject X Y) //
            listed ∈ DProduct.components })
    (hcomponent :
      ∀ idx :
        (Σ sourceX : { sourceX : SourceIrreducibleComponent X // sourceX ∈ DX.components },
          Σ sourceY : { sourceY : SourceIrreducibleComponent Y // sourceY ∈ DY.components },
            (family.decompose
              (SourceIrreducibleComponent.diagonalRepresentedPrimeSupport (k := k) sourceX.1)
              (SourceIrreducibleComponent.diagonalRepresentedPrimeSupport (k := k) sourceY.1)).components.index),
        (let P :=
          SourceIrreducibleComponent.diagonalRepresentedPrimeSupport (k := k) idx.1.1
        let Q :=
          SourceIrreducibleComponent.diagonalRepresentedPrimeSupport (k := k) idx.2.1.1
        let decomposition := family.decompose P Q
        SourceImageSubscheme.diagonalFiniteCorrespondence
          (decomposition.toRepresentedPrimeSupport idx.2.2).sourceComponent) =
          SourceIrreducibleComponent.diagonalFiniteCorrespondence (listedEquiv idx).1) :
    externalProductWithFamily family
        DX.identityFiniteCorrespondence DY.identityFiniteCorrespondence =
      DProduct.identityFiniteCorrespondence := by
  classical
  let sourceImage :
      (Σ sourceX : { sourceX : SourceIrreducibleComponent X // sourceX ∈ DX.components },
        Σ sourceY : { sourceY : SourceIrreducibleComponent Y // sourceY ∈ DY.components },
          (family.decompose
            (SourceIrreducibleComponent.diagonalRepresentedPrimeSupport (k := k) sourceX.1)
            (SourceIrreducibleComponent.diagonalRepresentedPrimeSupport (k := k) sourceY.1)).components.index) →
        SourceImageSubscheme (k := k) (overBaseProductObject X Y) :=
    fun idx =>
      let P :=
        SourceIrreducibleComponent.diagonalRepresentedPrimeSupport (k := k) idx.1.1
      let Q :=
        SourceIrreducibleComponent.diagonalRepresentedPrimeSupport (k := k) idx.2.1.1
      let decomposition := family.decompose P Q
      (decomposition.toRepresentedPrimeSupport idx.2.2).sourceComponent
  letI : Fintype
      (Σ sourceX : { sourceX : SourceIrreducibleComponent X // sourceX ∈ DX.components },
        Σ sourceY : { sourceY : SourceIrreducibleComponent Y // sourceY ∈ DY.components },
          (family.decompose
            (SourceIrreducibleComponent.diagonalRepresentedPrimeSupport (k := k) sourceX.1)
            (SourceIrreducibleComponent.diagonalRepresentedPrimeSupport (k := k) sourceY.1)).components.index) :=
    Fintype.ofEquiv
      { listed : SourceIrreducibleComponent (overBaseProductObject X Y) //
          listed ∈ DProduct.components } listedEquiv.symm
  have hFormal :
      (∑ idx :
        (Σ sourceX : { sourceX : SourceIrreducibleComponent X // sourceX ∈ DX.components },
          Σ sourceY : { sourceY : SourceIrreducibleComponent Y // sourceY ∈ DY.components },
            (family.decompose
              (SourceIrreducibleComponent.diagonalRepresentedPrimeSupport (k := k) sourceX.1)
              (SourceIrreducibleComponent.diagonalRepresentedPrimeSupport (k := k) sourceY.1)).components.index),
        SourceImageSubscheme.diagonalFiniteCorrespondence (sourceImage idx)) =
        DProduct.identityFiniteCorrespondence := by
    exact
      _root_.Boundary.FiniteIrreducibleComponentDecomposition.sum_diagonal_eq_identityFiniteCorrespondence_of_equiv_components
        (decomposition := DProduct)
        (sourceImage := sourceImage)
        (listedEquiv := listedEquiv)
        hcomponent
  rw [externalProductWithFamily_identity_identity_eq_sum_diagonal_decompositions
    (family := family) DX DY hIso hmult]
  change
    (∑ sourceX : { sourceX : SourceIrreducibleComponent X // sourceX ∈ DX.components },
      ∑ sourceY : { sourceY : SourceIrreducibleComponent Y // sourceY ∈ DY.components },
        ∑ i :
          (family.decompose
            (SourceIrreducibleComponent.diagonalRepresentedPrimeSupport (k := k) sourceX.1)
            (SourceIrreducibleComponent.diagonalRepresentedPrimeSupport (k := k) sourceY.1)).components.index,
          SourceImageSubscheme.diagonalFiniteCorrespondence
            (sourceImage ⟨sourceX, sourceY, i⟩)) =
      DProduct.identityFiniteCorrespondence
  simpa [sourceImage, Finset.univ_sigma_univ, Finset.sum_sigma] using hFormal

/-- Bilinear lift for external-product/compose interchange.

To prove full interchange on finite correspondences, it is enough to prove it
on singleton generators. -/
theorem externalProductWithFamily_comp_interchange_of_singletons
    (family :
      RepresentedPrimeFiniteCorrespondenceExternalProduct.ExternalProductDecompositionFamily
        (k := k))
    (compData : FiniteCorrespondenceCompositionData (k := k))
    (hSingle :
      ∀ {W1 X1 Y1 W2 X2 Y2 : Geometry.SmSchemeOver k}
        (f : PrimeFiniteCorrespondenceGeom W1 X1)
        (fCoeff : ℤ)
        (g : PrimeFiniteCorrespondenceGeom X1 Y1)
        (gCoeff : ℤ)
        (f' : PrimeFiniteCorrespondenceGeom W2 X2)
        (fCoeff' : ℤ)
        (g' : PrimeFiniteCorrespondenceGeom X2 Y2)
        (gCoeff' : ℤ),
          externalProductWithFamily family
              (FiniteCorrespondenceCompositionData.comp compData
                (Finsupp.single f fCoeff) (Finsupp.single g gCoeff))
              (FiniteCorrespondenceCompositionData.comp compData
                (Finsupp.single f' fCoeff') (Finsupp.single g' gCoeff'))
            =
              FiniteCorrespondenceCompositionData.comp compData
                (externalProductWithFamily family
                  (Finsupp.single f fCoeff) (Finsupp.single f' fCoeff'))
                (externalProductWithFamily family
                  (Finsupp.single g gCoeff) (Finsupp.single g' gCoeff')))
    {W1 X1 Y1 W2 X2 Y2 : Geometry.SmSchemeOver k}
    (f : FiniteCorrespondence W1 X1)
    (g : FiniteCorrespondence X1 Y1)
    (f' : FiniteCorrespondence W2 X2)
    (g' : FiniteCorrespondence X2 Y2) :
    externalProductWithFamily family
        (FiniteCorrespondenceCompositionData.comp compData f g)
        (FiniteCorrespondenceCompositionData.comp compData f' g')
      =
        FiniteCorrespondenceCompositionData.comp compData
          (externalProductWithFamily family f f')
          (externalProductWithFamily family g g') := by
  apply Finsupp.induction_linear f
  · simp
  · intro f1 f2 ih1 ih2
    rw [FiniteCorrespondenceCompositionData.comp_add_left,
      externalProductWithFamily_add_left,
      ih1, ih2,
      externalProductWithFamily_add_left,
      FiniteCorrespondenceCompositionData.comp_add_left]
  · intro fPrime fCoeff
    apply Finsupp.induction_linear g
    · simp
    · intro g1 g2 ihg1 ihg2
      rw [FiniteCorrespondenceCompositionData.comp_add_right,
          externalProductWithFamily_add_left,
          ihg1, ihg2,
          externalProductWithFamily_add_left,
          FiniteCorrespondenceCompositionData.comp_add_right]
    · intro gPrime gCoeff
      apply Finsupp.induction_linear f'
      · simp
      · intro f1' f2' ihf1' ihf2'
        rw [FiniteCorrespondenceCompositionData.comp_add_left,
            externalProductWithFamily_add_right,
            ihf1', ihf2',
            externalProductWithFamily_add_right,
            FiniteCorrespondenceCompositionData.comp_add_left]
      · intro fPrime' fCoeff'
        apply Finsupp.induction_linear g'
        · simp
        · intro g1' g2' ihg1' ihg2'
          rw [FiniteCorrespondenceCompositionData.comp_add_right,
            externalProductWithFamily_add_right,
            ihg1', ihg2',
            externalProductWithFamily_add_right,
            FiniteCorrespondenceCompositionData.comp_add_right]
        · intro gPrime' gCoeff'
          exact hSingle fPrime fCoeff gPrime gCoeff fPrime' fCoeff' gPrime' gCoeff'

/-- Prime-level external-product/compose interchange implies full interchange
on finite correspondences. -/
theorem externalProductWithFamily_comp_interchange_of_primes
    (family :
      RepresentedPrimeFiniteCorrespondenceExternalProduct.ExternalProductDecompositionFamily
        (k := k))
    (compData : FiniteCorrespondenceCompositionData (k := k))
    (hPrime :
      ∀ {W1 X1 Y1 W2 X2 Y2 : Geometry.SmSchemeOver k}
        (f : PrimeFiniteCorrespondenceGeom W1 X1)
        (g : PrimeFiniteCorrespondenceGeom X1 Y1)
        (f' : PrimeFiniteCorrespondenceGeom W2 X2)
        (g' : PrimeFiniteCorrespondenceGeom X2 Y2),
          externalProductWithFamily family
              (FiniteCorrespondenceCompositionData.compPrime compData f g)
              (FiniteCorrespondenceCompositionData.compPrime compData f' g')
            =
              FiniteCorrespondenceCompositionData.comp compData
                (externalProductWithFamily family (Finsupp.single f 1) (Finsupp.single f' 1))
                (externalProductWithFamily family (Finsupp.single g 1) (Finsupp.single g' 1)))
    {W1 X1 Y1 W2 X2 Y2 : Geometry.SmSchemeOver k}
    (f : FiniteCorrespondence W1 X1)
    (g : FiniteCorrespondence X1 Y1)
    (f' : FiniteCorrespondence W2 X2)
    (g' : FiniteCorrespondence X2 Y2) :
    externalProductWithFamily family
        (FiniteCorrespondenceCompositionData.comp compData f g)
        (FiniteCorrespondenceCompositionData.comp compData f' g')
      =
        FiniteCorrespondenceCompositionData.comp compData
          (externalProductWithFamily family f f')
          (externalProductWithFamily family g g') := by
  refine externalProductWithFamily_comp_interchange_of_singletons family compData ?_ f g f' g'
  intro W1 X1 Y1 W2 X2 Y2 fPrime fCoeff gPrime gCoeff fPrime' fCoeff' gPrime' gCoeff'
  calc
    externalProductWithFamily family
        (FiniteCorrespondenceCompositionData.comp compData
          (Finsupp.single fPrime fCoeff) (Finsupp.single gPrime gCoeff))
        (FiniteCorrespondenceCompositionData.comp compData
          (Finsupp.single fPrime' fCoeff') (Finsupp.single gPrime' gCoeff'))
      = externalProductWithFamily family
          ((fCoeff * gCoeff) •
            FiniteCorrespondenceCompositionData.compPrime compData fPrime gPrime)
          ((fCoeff' * gCoeff') •
            FiniteCorrespondenceCompositionData.compPrime compData fPrime' gPrime') := by
              rw [FiniteCorrespondenceCompositionData.comp_single_single,
                FiniteCorrespondenceCompositionData.comp_single_single]
      _ = ((fCoeff * gCoeff) * (fCoeff' * gCoeff')) •
            externalProductWithFamily family
              (FiniteCorrespondenceCompositionData.compPrime compData fPrime gPrime)
              (FiniteCorrespondenceCompositionData.compPrime compData fPrime' gPrime') := by
                rw [externalProductWithFamily_smul_left,
                  externalProductWithFamily_smul_right, smul_smul]
      _ = ((fCoeff * gCoeff) * (fCoeff' * gCoeff')) •
          FiniteCorrespondenceCompositionData.comp compData
            (externalProductWithFamily family (Finsupp.single fPrime 1) (Finsupp.single fPrime' 1))
            (externalProductWithFamily family (Finsupp.single gPrime 1) (Finsupp.single gPrime' 1)) := by
              rw [hPrime fPrime gPrime fPrime' gPrime']
      _ = FiniteCorrespondenceCompositionData.comp compData
          ((fCoeff * fCoeff') •
            (externalProductWithFamily family (Finsupp.single fPrime 1) (Finsupp.single fPrime' 1)))
          ((gCoeff * gCoeff') •
            (externalProductWithFamily family (Finsupp.single gPrime 1) (Finsupp.single gPrime' 1))) := by
            rw [show ((fCoeff * gCoeff) * (fCoeff' * gCoeff')) =
                (fCoeff * fCoeff') * (gCoeff * gCoeff') by ring]
            rw [← smul_smul]
            rw [← FiniteCorrespondenceCompositionData.comp_smul_right]
            rw [← FiniteCorrespondenceCompositionData.comp_smul_left]
      _ = FiniteCorrespondenceCompositionData.comp compData
          (externalProductWithFamily family (Finsupp.single fPrime fCoeff) (Finsupp.single fPrime' fCoeff'))
          ((gCoeff * gCoeff') •
            (externalProductWithFamily family (Finsupp.single gPrime 1) (Finsupp.single gPrime' 1))) := by
              rw [← externalProductWithFamily_single_single_eq_smul_one]
      _ = FiniteCorrespondenceCompositionData.comp compData
          (externalProductWithFamily family (Finsupp.single fPrime fCoeff) (Finsupp.single fPrime' fCoeff'))
          (externalProductWithFamily family (Finsupp.single gPrime gCoeff) (Finsupp.single gPrime' gCoeff')) := by
              rw [← externalProductWithFamily_single_single_eq_smul_one]

/-- Canonical coherent external-product family used by the public finite-
correspondence external product. -/
class CanonicalExternalProductFamily where
  family :
    RepresentedPrimeFiniteCorrespondenceExternalProduct.ExternalProductDecompositionFamily
      (k := k)

namespace CanonicalExternalProductFamily

end CanonicalExternalProductFamily

/-- Export package for the finite-correspondence external product used as the
input to effective tensor descent.

This is intentionally below the geometric/support construction and above the
effective-motive descent layer. It packages the canonical decomposition family
and exposes only algebraic facts already proved in this file; it does not claim
that the external product has descended through A1/Nis/effective localization. -/
structure EffectiveTensorDescentExternalProductPackage where
  family :
    RepresentedPrimeFiniteCorrespondenceExternalProduct.ExternalProductDecompositionFamily
      (k := k)

namespace EffectiveTensorDescentExternalProductPackage

instance (package : EffectiveTensorDescentExternalProductPackage (k := k)) :
    CanonicalExternalProductFamily (k := k) where
  family := package.family

def product
    (package : EffectiveTensorDescentExternalProductPackage (k := k))
    {X1 Y1 X2 Y2 : Geometry.SmSchemeOver k}
    (left : FiniteCorrespondence X1 Y1)
    (right : FiniteCorrespondence X2 Y2) :
    FiniteCorrespondence (overBaseProductObject X1 X2) (overBaseProductObject Y1 Y2) :=
  externalProductWithFamily package.family left right

theorem product_add_left
    (package : EffectiveTensorDescentExternalProductPackage (k := k))
    {X1 Y1 X2 Y2 : Geometry.SmSchemeOver k}
    (left1 left2 : FiniteCorrespondence X1 Y1)
    (right : FiniteCorrespondence X2 Y2) :
    package.product (left1 + left2) right =
      package.product left1 right + package.product left2 right := by
  exact externalProductWithFamily_add_left
    (family := package.family) left1 left2 right

theorem product_add_right
    (package : EffectiveTensorDescentExternalProductPackage (k := k))
    {X1 Y1 X2 Y2 : Geometry.SmSchemeOver k}
    (left : FiniteCorrespondence X1 Y1)
    (right1 right2 : FiniteCorrespondence X2 Y2) :
    package.product left (right1 + right2) =
      package.product left right1 + package.product left right2 := by
  exact externalProductWithFamily_add_right
    (family := package.family) left right1 right2

theorem product_smul_left
    (package : EffectiveTensorDescentExternalProductPackage (k := k))
    {X1 Y1 X2 Y2 : Geometry.SmSchemeOver k}
    (coeff : ℤ)
    (left : FiniteCorrespondence X1 Y1)
    (right : FiniteCorrespondence X2 Y2) :
    package.product (coeff • left) right =
      coeff • package.product left right := by
  exact externalProductWithFamily_smul_left
    (family := package.family) coeff left right

theorem product_smul_right
    (package : EffectiveTensorDescentExternalProductPackage (k := k))
    {X1 Y1 X2 Y2 : Geometry.SmSchemeOver k}
    (coeff : ℤ)
    (left : FiniteCorrespondence X1 Y1)
    (right : FiniteCorrespondence X2 Y2) :
    package.product left (coeff • right) =
      coeff • package.product left right := by
  exact externalProductWithFamily_smul_right
    (family := package.family) coeff left right

theorem product_single_single
    (package : EffectiveTensorDescentExternalProductPackage (k := k))
    {X1 Y1 X2 Y2 : Geometry.SmSchemeOver k}
    (leftPrime : PrimeFiniteCorrespondenceGeom X1 Y1)
    (rightPrime : PrimeFiniteCorrespondenceGeom X2 Y2)
    (leftCoeff rightCoeff : ℤ) :
    package.product
        (Finsupp.single leftPrime leftCoeff)
        (Finsupp.single rightPrime rightCoeff) =
      (leftCoeff * rightCoeff) •
        package.family.data.extPrime leftPrime rightPrime := by
  exact externalProductWithFamily_single_single
    (family := package.family) leftPrime rightPrime leftCoeff rightCoeff

theorem product_single_single_one
    (package : EffectiveTensorDescentExternalProductPackage (k := k))
    {X1 Y1 X2 Y2 : Geometry.SmSchemeOver k}
    (leftPrime : PrimeFiniteCorrespondenceGeom X1 Y1)
    (rightPrime : PrimeFiniteCorrespondenceGeom X2 Y2) :
    package.product
        (Finsupp.single leftPrime 1)
        (Finsupp.single rightPrime 1) =
      package.family.data.extPrime leftPrime rightPrime := by
  simpa using
    product_single_single
      (package := package) leftPrime rightPrime (leftCoeff := 1) (rightCoeff := 1)

theorem product_comp_interchange_of_primes
    (package : EffectiveTensorDescentExternalProductPackage (k := k))
    (compData : FiniteCorrespondenceCompositionData (k := k))
    (hPrime :
      ∀ {W1 X1 Y1 W2 X2 Y2 : Geometry.SmSchemeOver k}
        (f : PrimeFiniteCorrespondenceGeom W1 X1)
        (g : PrimeFiniteCorrespondenceGeom X1 Y1)
        (f' : PrimeFiniteCorrespondenceGeom W2 X2)
        (g' : PrimeFiniteCorrespondenceGeom X2 Y2),
          package.product
              (FiniteCorrespondenceCompositionData.compPrime compData f g)
              (FiniteCorrespondenceCompositionData.compPrime compData f' g')
            =
              FiniteCorrespondenceCompositionData.comp compData
                (package.product (Finsupp.single f 1) (Finsupp.single f' 1))
                (package.product (Finsupp.single g 1) (Finsupp.single g' 1)))
    {W1 X1 Y1 W2 X2 Y2 : Geometry.SmSchemeOver k}
    (f : FiniteCorrespondence W1 X1)
    (g : FiniteCorrespondence X1 Y1)
    (f' : FiniteCorrespondence W2 X2)
    (g' : FiniteCorrespondence X2 Y2) :
    package.product
        (FiniteCorrespondenceCompositionData.comp compData f g)
        (FiniteCorrespondenceCompositionData.comp compData f' g')
      =
        FiniteCorrespondenceCompositionData.comp compData
          (package.product f f')
          (package.product g g') := by
  simpa [product] using
    externalProductWithFamily_comp_interchange_of_primes
      (family := package.family) compData hPrime f g f' g'

end EffectiveTensorDescentExternalProductPackage

/-- Public external product on finite correspondences, routed only through the
canonical coherent family. -/
def externalProduct
    [CanonicalExternalProductFamily (k := k)]
    {X1 Y1 X2 Y2 : Geometry.SmSchemeOver k}
    (left : FiniteCorrespondence X1 Y1)
    (right : FiniteCorrespondence X2 Y2) :
    FiniteCorrespondence
      (overBaseProductObject X1 X2) (overBaseProductObject Y1 Y2) :=
  externalProductWithFamily (CanonicalExternalProductFamily.family (k := k)) left right

@[simp] theorem externalProduct_zero_left
    [CanonicalExternalProductFamily (k := k)]
    {X1 Y1 X2 Y2 : Geometry.SmSchemeOver k}
    (right : FiniteCorrespondence X2 Y2) :
    externalProduct (k := k) (0 : FiniteCorrespondence X1 Y1) right = 0 := by
  exact
    externalProductWithFamily_zero_left
      (k := k)
      (family := CanonicalExternalProductFamily.family (k := k))
      right

@[simp] theorem externalProduct_zero_right
    [CanonicalExternalProductFamily (k := k)]
    {X1 Y1 X2 Y2 : Geometry.SmSchemeOver k}
    (left : FiniteCorrespondence X1 Y1) :
    externalProduct (k := k) left (0 : FiniteCorrespondence X2 Y2) = 0 := by
  exact
    externalProductWithFamily_zero_right
      (k := k)
      (family := CanonicalExternalProductFamily.family (k := k))
      left

theorem externalProduct_add_left
    [CanonicalExternalProductFamily (k := k)]
    {X1 Y1 X2 Y2 : Geometry.SmSchemeOver k}
    (left1 left2 : FiniteCorrespondence X1 Y1)
    (right : FiniteCorrespondence X2 Y2) :
    externalProduct (k := k) (left1 + left2) right =
      externalProduct (k := k) left1 right + externalProduct (k := k) left2 right := by
  exact
    externalProductWithFamily_add_left
      (k := k)
      (family := CanonicalExternalProductFamily.family (k := k))
      left1 left2 right

theorem externalProduct_add_right
    [CanonicalExternalProductFamily (k := k)]
    {X1 Y1 X2 Y2 : Geometry.SmSchemeOver k}
    (left : FiniteCorrespondence X1 Y1)
    (right1 right2 : FiniteCorrespondence X2 Y2) :
    externalProduct (k := k) left (right1 + right2) =
      externalProduct (k := k) left right1 + externalProduct (k := k) left right2 := by
  exact
    externalProductWithFamily_add_right
      (k := k)
      (family := CanonicalExternalProductFamily.family (k := k))
      left right1 right2

theorem externalProduct_smul_left
    [CanonicalExternalProductFamily (k := k)]
    {X1 Y1 X2 Y2 : Geometry.SmSchemeOver k}
    (coeff : ℤ)
    (left : FiniteCorrespondence X1 Y1)
    (right : FiniteCorrespondence X2 Y2) :
    externalProduct (k := k) (coeff • left) right =
      coeff • externalProduct (k := k) left right := by
  exact
    externalProductWithFamily_smul_left
      (k := k)
      (family := CanonicalExternalProductFamily.family (k := k))
      coeff left right

theorem externalProduct_smul_right
    [CanonicalExternalProductFamily (k := k)]
    {X1 Y1 X2 Y2 : Geometry.SmSchemeOver k}
    (coeff : ℤ)
    (left : FiniteCorrespondence X1 Y1)
    (right : FiniteCorrespondence X2 Y2) :
    externalProduct (k := k) left (coeff • right) =
      coeff • externalProduct (k := k) left right := by
  exact
    externalProductWithFamily_smul_right
      (k := k)
      (family := CanonicalExternalProductFamily.family (k := k))
      coeff left right

@[simp] theorem externalProduct_single_single
    [CanonicalExternalProductFamily (k := k)]
    {X1 Y1 X2 Y2 : Geometry.SmSchemeOver k}
    (leftPrime : PrimeFiniteCorrespondenceGeom X1 Y1)
    (rightPrime : PrimeFiniteCorrespondenceGeom X2 Y2)
    (leftCoeff rightCoeff : ℤ) :
    externalProduct (k := k)
        (Finsupp.single leftPrime leftCoeff)
        (Finsupp.single rightPrime rightCoeff) =
      (leftCoeff * rightCoeff) •
        (CanonicalExternalProductFamily.family (k := k)).data.extPrime leftPrime rightPrime := by
  exact
    externalProductWithFamily_single_single
      (k := k)
      (family := CanonicalExternalProductFamily.family (k := k))
      leftPrime rightPrime leftCoeff rightCoeff

@[simp] theorem externalProduct_single_single_one
    [CanonicalExternalProductFamily (k := k)]
    {X1 Y1 X2 Y2 : Geometry.SmSchemeOver k}
    (leftPrime : PrimeFiniteCorrespondenceGeom X1 Y1)
    (rightPrime : PrimeFiniteCorrespondenceGeom X2 Y2) :
    externalProduct (k := k)
        (Finsupp.single leftPrime 1)
        (Finsupp.single rightPrime 1) =
      (CanonicalExternalProductFamily.family (k := k)).data.extPrime leftPrime rightPrime := by
  exact
    externalProductWithFamily_single_single_one
      (k := k)
      (family := CanonicalExternalProductFamily.family (k := k))
      leftPrime rightPrime

/-- Bilinear lift for external-product/compose interchange on the canonical
public external product. -/
theorem externalProduct_comp_interchange_of_singletons
    [CanonicalExternalProductFamily (k := k)]
    (compData : FiniteCorrespondenceCompositionData (k := k))
    (hSingle :
      ∀ {W1 X1 Y1 W2 X2 Y2 : Geometry.SmSchemeOver k}
        (f : PrimeFiniteCorrespondenceGeom W1 X1)
        (fCoeff : ℤ)
        (g : PrimeFiniteCorrespondenceGeom X1 Y1)
        (gCoeff : ℤ)
        (f' : PrimeFiniteCorrespondenceGeom W2 X2)
        (fCoeff' : ℤ)
        (g' : PrimeFiniteCorrespondenceGeom X2 Y2)
        (gCoeff' : ℤ),
          externalProduct (k := k)
              (FiniteCorrespondenceCompositionData.comp compData
                (Finsupp.single f fCoeff) (Finsupp.single g gCoeff))
              (FiniteCorrespondenceCompositionData.comp compData
                (Finsupp.single f' fCoeff') (Finsupp.single g' gCoeff'))
            =
              FiniteCorrespondenceCompositionData.comp compData
                (externalProduct (k := k)
                  (Finsupp.single f fCoeff) (Finsupp.single f' fCoeff'))
                (externalProduct (k := k)
                  (Finsupp.single g gCoeff) (Finsupp.single g' gCoeff')))
    {W1 X1 Y1 W2 X2 Y2 : Geometry.SmSchemeOver k}
    (f : FiniteCorrespondence W1 X1)
    (g : FiniteCorrespondence X1 Y1)
    (f' : FiniteCorrespondence W2 X2)
    (g' : FiniteCorrespondence X2 Y2) :
    externalProduct (k := k)
        (FiniteCorrespondenceCompositionData.comp compData f g)
        (FiniteCorrespondenceCompositionData.comp compData f' g')
      =
        FiniteCorrespondenceCompositionData.comp compData
          (externalProduct (k := k) f f')
          (externalProduct (k := k) g g') := by
  exact
    externalProductWithFamily_comp_interchange_of_singletons
      (k := k)
      (family := CanonicalExternalProductFamily.family (k := k))
      compData hSingle f g f' g'

/-- Prime-level external-product/compose interchange implies full interchange
for the canonical public external product. -/
theorem externalProduct_comp_interchange_of_primes
    [CanonicalExternalProductFamily (k := k)]
    (compData : FiniteCorrespondenceCompositionData (k := k))
    (hPrime :
      ∀ {W1 X1 Y1 W2 X2 Y2 : Geometry.SmSchemeOver k}
        (f : PrimeFiniteCorrespondenceGeom W1 X1)
        (g : PrimeFiniteCorrespondenceGeom X1 Y1)
        (f' : PrimeFiniteCorrespondenceGeom W2 X2)
        (g' : PrimeFiniteCorrespondenceGeom X2 Y2),
          externalProduct (k := k)
              (FiniteCorrespondenceCompositionData.compPrime compData f g)
              (FiniteCorrespondenceCompositionData.compPrime compData f' g')
            =
              FiniteCorrespondenceCompositionData.comp compData
                (externalProduct (k := k) (Finsupp.single f 1) (Finsupp.single f' 1))
                (externalProduct (k := k) (Finsupp.single g 1) (Finsupp.single g' 1)))
    {W1 X1 Y1 W2 X2 Y2 : Geometry.SmSchemeOver k}
    (f : FiniteCorrespondence W1 X1)
    (g : FiniteCorrespondence X1 Y1)
    (f' : FiniteCorrespondence W2 X2)
    (g' : FiniteCorrespondence X2 Y2) :
    externalProduct (k := k)
        (FiniteCorrespondenceCompositionData.comp compData f g)
        (FiniteCorrespondenceCompositionData.comp compData f' g')
      =
        FiniteCorrespondenceCompositionData.comp compData
          (externalProduct (k := k) f f')
          (externalProduct (k := k) g g') := by
  exact
    externalProductWithFamily_comp_interchange_of_primes
      (k := k)
      (family := CanonicalExternalProductFamily.family (k := k))
      compData hPrime f g f' g'

/-- Canonical consumer-facing name for external-product/compose interchange.
This is an alias of `externalProduct_comp_interchange_of_primes`. -/
theorem externalProduct_comp_interchange
    [CanonicalExternalProductFamily (k := k)]
    (compData : FiniteCorrespondenceCompositionData (k := k))
    (hPrime :
      ∀ {W1 X1 Y1 W2 X2 Y2 : Geometry.SmSchemeOver k}
        (f : PrimeFiniteCorrespondenceGeom W1 X1)
        (g : PrimeFiniteCorrespondenceGeom X1 Y1)
        (f' : PrimeFiniteCorrespondenceGeom W2 X2)
        (g' : PrimeFiniteCorrespondenceGeom X2 Y2),
          externalProduct (k := k)
              (FiniteCorrespondenceCompositionData.compPrime compData f g)
              (FiniteCorrespondenceCompositionData.compPrime compData f' g')
            =
              FiniteCorrespondenceCompositionData.comp compData
                (externalProduct (k := k) (Finsupp.single f 1) (Finsupp.single f' 1))
                (externalProduct (k := k) (Finsupp.single g 1) (Finsupp.single g' 1)))
    {W1 X1 Y1 W2 X2 Y2 : Geometry.SmSchemeOver k}
    (f : FiniteCorrespondence W1 X1)
    (g : FiniteCorrespondence X1 Y1)
    (f' : FiniteCorrespondence W2 X2)
    (g' : FiniteCorrespondence X2 Y2) :
    externalProduct (k := k)
        (FiniteCorrespondenceCompositionData.comp compData f g)
        (FiniteCorrespondenceCompositionData.comp compData f' g')
      =
        FiniteCorrespondenceCompositionData.comp compData
          (externalProduct (k := k) f f')
          (externalProduct (k := k) g g') :=
  externalProduct_comp_interchange_of_primes
    (k := k) compData hPrime f g f' g'

end FiniteCorrespondence

end

end Boundary
