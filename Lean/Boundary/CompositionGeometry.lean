import Boundary.DiagonalDecomposition
import Boundary.ImageComponentGeometry
import Geometry.Cycles.Operations

/-!
# Represented-Prime Composition Geometry

This file packages the support-fiber-product image layer and the finite-family
geometry used to build represented-prime composition data.
-/

universe u

variable {k : Type u} [Field k] [PerfectField k]

open AlgebraicGeometry CategoryTheory Limits

namespace Boundary

open PrimeFiniteCorrespondenceSupport

noncomputable section

/-- A factorization of the canonical map from the support fiber product
`P.support ×_Y Q.support` to `sourceComponent(P) ×_k Z` through its intended
scheme-theoretic image. -/
structure SupportFiberProductImageFactorization
    {X Y Z : Geometry.SmSchemeOver k}
    (P : RepresentedPrimeSupport X Y) (Q : RepresentedPrimeSupport Y Z) where
  image : Scheme
  toImage : compositionFiberProduct P Q ⟶ image
  imageToAmbientProduct : image ⟶ overBaseProduct P.sourceComponent.carrier Z
  factorization : toImage ≫ imageToAmbientProduct = compositionToAmbientProduct P Q
  imageClosedImmersion : IsClosedImmersion imageToAmbientProduct

/-- A factorization of the canonical map from the left-associated triple support
fiber product `(P.support ×_X Q.support) ×_Y R.support` to
`sourceComponent(P) ×_k Z` through an intended scheme-theoretic image. -/
structure LeftAssociatedSupportFiberProductImageFactorization
    {W X Y Z : Geometry.SmSchemeOver k}
    (P : RepresentedPrimeSupport W X) (Q : RepresentedPrimeSupport X Y)
    (R : RepresentedPrimeSupport Y Z) where
  image : Scheme
  toImage : leftAssociatedCompositionFiberProduct P Q R ⟶ image
  imageToAmbientProduct : image ⟶ overBaseProduct P.sourceComponent.carrier Z
  factorization :
    toImage ≫ imageToAmbientProduct = leftAssociatedCompositionToAmbientProduct P Q R
  imageClosedImmersion : IsClosedImmersion imageToAmbientProduct

/-- A factorization of the canonical map from the right-associated triple
support fiber product `P.support ×_X (Q.support ×_Y R.support)` to
`sourceComponent(P) ×_k Z` through an intended scheme-theoretic image. -/
structure RightAssociatedSupportFiberProductImageFactorization
    {W X Y Z : Geometry.SmSchemeOver k}
    (P : RepresentedPrimeSupport W X) (Q : RepresentedPrimeSupport X Y)
    (R : RepresentedPrimeSupport Y Z) where
  image : Scheme
  toImage : rightAssociatedCompositionFiberProduct P Q R ⟶ image
  imageToAmbientProduct : image ⟶ overBaseProduct P.sourceComponent.carrier Z
  factorization :
    toImage ≫ imageToAmbientProduct = rightAssociatedCompositionToAmbientProduct P Q R
  imageClosedImmersion : IsClosedImmersion imageToAmbientProduct

namespace SupportFiberProductImageFactorization

/-- Forget the support-fiber-product-specific packaging and view the image data
as a generic closed-image factorization. -/
def toClosedImageFactorization
    {X Y Z : Geometry.SmSchemeOver k}
    {P : RepresentedPrimeSupport X Y} {Q : RepresentedPrimeSupport Y Z}
    (imageData : SupportFiberProductImageFactorization P Q) :
    ClosedImageFactorization (compositionToAmbientProduct P Q) where
  image := imageData.image
  toImage := imageData.toImage
  imageToTarget := imageData.imageToAmbientProduct
  factorization := imageData.factorization
  imageClosedImmersion := imageData.imageClosedImmersion

end SupportFiberProductImageFactorization

namespace LeftAssociatedSupportFiberProductImageFactorization

/-- Forget the left-associated support-fiber-product-specific packaging and
view the image data as a generic closed-image factorization. -/
def toClosedImageFactorization
    {W X Y Z : Geometry.SmSchemeOver k}
    {P : RepresentedPrimeSupport W X} {Q : RepresentedPrimeSupport X Y}
    {R : RepresentedPrimeSupport Y Z}
    (imageData : LeftAssociatedSupportFiberProductImageFactorization P Q R) :
    ClosedImageFactorization (leftAssociatedCompositionToAmbientProduct P Q R) where
  image := imageData.image
  toImage := imageData.toImage
  imageToTarget := imageData.imageToAmbientProduct
  factorization := imageData.factorization
  imageClosedImmersion := imageData.imageClosedImmersion

end LeftAssociatedSupportFiberProductImageFactorization

namespace RightAssociatedSupportFiberProductImageFactorization

/-- Forget the right-associated support-fiber-product-specific packaging and
view the image data as a generic closed-image factorization. -/
def toClosedImageFactorization
    {W X Y Z : Geometry.SmSchemeOver k}
    {P : RepresentedPrimeSupport W X} {Q : RepresentedPrimeSupport X Y}
    {R : RepresentedPrimeSupport Y Z}
    (imageData : RightAssociatedSupportFiberProductImageFactorization P Q R) :
    ClosedImageFactorization (rightAssociatedCompositionToAmbientProduct P Q R) where
  image := imageData.image
  toImage := imageData.toImage
  imageToTarget := imageData.imageToAmbientProduct
  factorization := imageData.factorization
  imageClosedImmersion := imageData.imageClosedImmersion

end RightAssociatedSupportFiberProductImageFactorization

namespace LeftAssociatedSupportFiberProductImageFactorization

/-- Transport a left-associated triple image factorization across the canonical
associativity isomorphism of triple support fiber products. -/
def toRightAssociated
    {W X Y Z : Geometry.SmSchemeOver k}
    {P : RepresentedPrimeSupport W X} {Q : RepresentedPrimeSupport X Y}
    {R : RepresentedPrimeSupport Y Z}
    (factorization : LeftAssociatedSupportFiberProductImageFactorization P Q R) :
    RightAssociatedSupportFiberProductImageFactorization P Q R where
  image := factorization.image
  toImage := (compositionFiberProductAssocIso P Q R).inv ≫ factorization.toImage
  imageToAmbientProduct := factorization.imageToAmbientProduct
  factorization := by
    calc
      (compositionFiberProductAssocIso P Q R).inv ≫ factorization.toImage ≫
          factorization.imageToAmbientProduct
          = (compositionFiberProductAssocIso P Q R).inv ≫
              leftAssociatedCompositionToAmbientProduct P Q R := by
                  rw [factorization.factorization]
      _ = rightAssociatedCompositionToAmbientProduct P Q R := by
            calc
              (compositionFiberProductAssocIso P Q R).inv ≫
                  leftAssociatedCompositionToAmbientProduct P Q R
                  = (compositionFiberProductAssocIso P Q R).inv ≫
                      ((compositionFiberProductAssocIso P Q R).hom ≫
                        rightAssociatedCompositionToAmbientProduct P Q R) := by
                          rw [compositionFiberProductAssocIso_hom_comp_rightAssociatedCompositionToAmbientProduct
                            P Q R]
              _ = rightAssociatedCompositionToAmbientProduct P Q R := by
                    simpa [Category.assoc] using
                      (Iso.inv_hom_id_assoc (compositionFiberProductAssocIso P Q R)
                        (rightAssociatedCompositionToAmbientProduct P Q R))
  imageClosedImmersion := factorization.imageClosedImmersion

@[simp] theorem toRightAssociated_image
    {W X Y Z : Geometry.SmSchemeOver k}
    {P : RepresentedPrimeSupport W X} {Q : RepresentedPrimeSupport X Y}
    {R : RepresentedPrimeSupport Y Z}
    (factorization : LeftAssociatedSupportFiberProductImageFactorization P Q R) :
    factorization.toRightAssociated.image = factorization.image := rfl

@[simp] theorem toRightAssociated_imageToAmbientProduct
    {W X Y Z : Geometry.SmSchemeOver k}
    {P : RepresentedPrimeSupport W X} {Q : RepresentedPrimeSupport X Y}
    {R : RepresentedPrimeSupport Y Z}
    (factorization : LeftAssociatedSupportFiberProductImageFactorization P Q R) :
    factorization.toRightAssociated.imageToAmbientProduct = factorization.imageToAmbientProduct := rfl

end LeftAssociatedSupportFiberProductImageFactorization

/-- One integral component of the image of the left-associated triple support
fiber-product map to `sourceComponent(P) ×_k Z`. -/
structure LeftAssociatedSupportFiberProductImageComponent
    {W X Y Z : Geometry.SmSchemeOver k}
    {P : RepresentedPrimeSupport W X} {Q : RepresentedPrimeSupport X Y}
    {R : RepresentedPrimeSupport Y Z}
    (imageData : LeftAssociatedSupportFiberProductImageFactorization P Q R) where
  lengthCoeff : ℕ
  support : Scheme
  isIntegral : IsIntegral support
  toImage : support ⟶ imageData.image
  toImageClosedImmersion : IsClosedImmersion toImage
  toCompositionFiberProduct : support ⟶ leftAssociatedCompositionFiberProduct P Q R
  toImage_factorization :
    toCompositionFiberProduct ≫ imageData.toImage = toImage
  finiteOverSourceComponent : support ⟶ P.sourceComponent.carrier.scheme
  finite_toSourceComponent : IsFinite finiteOverSourceComponent
  surjective_toSourceComponent : Function.Surjective finiteOverSourceComponent.base
  toTarget : support ⟶ Z.scheme
  inclusion : support ⟶ overBaseProduct P.sourceComponent.carrier Z
  inclusion_factorization : toImage ≫ imageData.imageToAmbientProduct = inclusion
  inclusion_fst : inclusion ≫ overBaseProduct.fst P.sourceComponent.carrier Z =
    finiteOverSourceComponent
  inclusion_snd : inclusion ≫ overBaseProduct.snd P.sourceComponent.carrier Z =
    toTarget
  isClosedImmersion : IsClosedImmersion inclusion

/-- One integral component of the image of the right-associated triple support
fiber-product map to `sourceComponent(P) ×_k Z`. -/
structure RightAssociatedSupportFiberProductImageComponent
    {W X Y Z : Geometry.SmSchemeOver k}
    {P : RepresentedPrimeSupport W X} {Q : RepresentedPrimeSupport X Y}
    {R : RepresentedPrimeSupport Y Z}
    (imageData : RightAssociatedSupportFiberProductImageFactorization P Q R) where
  lengthCoeff : ℕ
  support : Scheme
  isIntegral : IsIntegral support
  toImage : support ⟶ imageData.image
  toImageClosedImmersion : IsClosedImmersion toImage
  toCompositionFiberProduct : support ⟶ rightAssociatedCompositionFiberProduct P Q R
  toImage_factorization :
    toCompositionFiberProduct ≫ imageData.toImage = toImage
  finiteOverSourceComponent : support ⟶ P.sourceComponent.carrier.scheme
  finite_toSourceComponent : IsFinite finiteOverSourceComponent
  surjective_toSourceComponent : Function.Surjective finiteOverSourceComponent.base
  toTarget : support ⟶ Z.scheme
  inclusion : support ⟶ overBaseProduct P.sourceComponent.carrier Z
  inclusion_factorization : toImage ≫ imageData.imageToAmbientProduct = inclusion
  inclusion_fst : inclusion ≫ overBaseProduct.fst P.sourceComponent.carrier Z =
    finiteOverSourceComponent
  inclusion_snd : inclusion ≫ overBaseProduct.snd P.sourceComponent.carrier Z =
    toTarget
  isClosedImmersion : IsClosedImmersion inclusion

namespace LeftAssociatedSupportFiberProductImageComponent

/-- View one left-associated triple image component as a weighted integral
closed subscheme of the scheme-theoretic image. -/
def toWeightedIntClosedSubscheme
    {W X Y Z : Geometry.SmSchemeOver k}
    {P : RepresentedPrimeSupport W X} {Q : RepresentedPrimeSupport X Y}
    {R : RepresentedPrimeSupport Y Z}
    {imageData : LeftAssociatedSupportFiberProductImageFactorization P Q R}
    (component : LeftAssociatedSupportFiberProductImageComponent imageData) :
    WeightedIntClosedSubscheme imageData.image where
  multiplicity := component.lengthCoeff
  support :=
    { scheme := component.support
      inclusion := component.toImage
      isClosedImm := component.toImageClosedImmersion
      isIntegral := component.isIntegral }

end LeftAssociatedSupportFiberProductImageComponent

namespace RightAssociatedSupportFiberProductImageComponent

/-- View one right-associated triple image component as a weighted integral
closed subscheme of the scheme-theoretic image. -/
def toWeightedIntClosedSubscheme
    {W X Y Z : Geometry.SmSchemeOver k}
    {P : RepresentedPrimeSupport W X} {Q : RepresentedPrimeSupport X Y}
    {R : RepresentedPrimeSupport Y Z}
    {imageData : RightAssociatedSupportFiberProductImageFactorization P Q R}
    (component : RightAssociatedSupportFiberProductImageComponent imageData) :
    WeightedIntClosedSubscheme imageData.image where
  multiplicity := component.lengthCoeff
  support :=
    { scheme := component.support
      inclusion := component.toImage
      isClosedImm := component.toImageClosedImmersion
      isIntegral := component.isIntegral }

end RightAssociatedSupportFiberProductImageComponent

namespace LeftAssociatedSupportFiberProductImageComponent

/-- Transport a left-associated triple image component across the support
associator, reusing the same support and ambient inclusion. -/
def toRightAssociated
    {W X Y Z : Geometry.SmSchemeOver k}
    {P : RepresentedPrimeSupport W X} {Q : RepresentedPrimeSupport X Y}
    {R : RepresentedPrimeSupport Y Z}
    {imageData : LeftAssociatedSupportFiberProductImageFactorization P Q R}
    (component : LeftAssociatedSupportFiberProductImageComponent imageData) :
    RightAssociatedSupportFiberProductImageComponent imageData.toRightAssociated where
  lengthCoeff := component.lengthCoeff
  support := component.support
  isIntegral := component.isIntegral
  toImage := component.toImage
  toImageClosedImmersion := component.toImageClosedImmersion
  toCompositionFiberProduct :=
    component.toCompositionFiberProduct ≫ (compositionFiberProductAssocIso P Q R).hom
  toImage_factorization := by
    calc
      component.toCompositionFiberProduct ≫ (compositionFiberProductAssocIso P Q R).hom ≫
          imageData.toRightAssociated.toImage
          = component.toCompositionFiberProduct ≫ imageData.toImage := by
              simp [LeftAssociatedSupportFiberProductImageFactorization.toRightAssociated,
                Category.assoc]
      _ = component.toImage := component.toImage_factorization
  finiteOverSourceComponent := component.finiteOverSourceComponent
  finite_toSourceComponent := component.finite_toSourceComponent
  surjective_toSourceComponent := component.surjective_toSourceComponent
  toTarget := component.toTarget
  inclusion := component.inclusion
  inclusion_factorization := by
    simpa [LeftAssociatedSupportFiberProductImageFactorization.toRightAssociated] using
      component.inclusion_factorization
  inclusion_fst := component.inclusion_fst
  inclusion_snd := component.inclusion_snd
  isClosedImmersion := component.isClosedImmersion

  @[simp] theorem toRightAssociated_lengthCoeff
    {W X Y Z : Geometry.SmSchemeOver k}
    {P : RepresentedPrimeSupport W X} {Q : RepresentedPrimeSupport X Y}
    {R : RepresentedPrimeSupport Y Z}
    {imageData : LeftAssociatedSupportFiberProductImageFactorization P Q R}
    (component : LeftAssociatedSupportFiberProductImageComponent imageData) :
    component.toRightAssociated.lengthCoeff = component.lengthCoeff := rfl

  @[simp] theorem toRightAssociated_support
    {W X Y Z : Geometry.SmSchemeOver k}
    {P : RepresentedPrimeSupport W X} {Q : RepresentedPrimeSupport X Y}
    {R : RepresentedPrimeSupport Y Z}
    {imageData : LeftAssociatedSupportFiberProductImageFactorization P Q R}
    (component : LeftAssociatedSupportFiberProductImageComponent imageData) :
    component.toRightAssociated.support = component.support := rfl

  @[simp] theorem toRightAssociated_inclusion
    {W X Y Z : Geometry.SmSchemeOver k}
    {P : RepresentedPrimeSupport W X} {Q : RepresentedPrimeSupport X Y}
    {R : RepresentedPrimeSupport Y Z}
    {imageData : LeftAssociatedSupportFiberProductImageFactorization P Q R}
    (component : LeftAssociatedSupportFiberProductImageComponent imageData) :
    component.toRightAssociated.inclusion = component.inclusion := rfl

  @[simp] theorem toRightAssociated_finiteOverSourceComponent
    {W X Y Z : Geometry.SmSchemeOver k}
    {P : RepresentedPrimeSupport W X} {Q : RepresentedPrimeSupport X Y}
    {R : RepresentedPrimeSupport Y Z}
    {imageData : LeftAssociatedSupportFiberProductImageFactorization P Q R}
    (component : LeftAssociatedSupportFiberProductImageComponent imageData) :
    component.toRightAssociated.finiteOverSourceComponent =
      component.finiteOverSourceComponent := rfl

end LeftAssociatedSupportFiberProductImageComponent

namespace LeftAssociatedSupportFiberProductImageComponent

/-- The outer represented prime support in `W ⟶ Z` carried by a left-associated
triple image component. -/
def toRepresentedPrimeSupport
    {W X Y Z : Geometry.SmSchemeOver k}
    {P : RepresentedPrimeSupport W X} {Q : RepresentedPrimeSupport X Y}
    {R : RepresentedPrimeSupport Y Z}
    {imageData : LeftAssociatedSupportFiberProductImageFactorization P Q R}
    (component : LeftAssociatedSupportFiberProductImageComponent imageData) :
    RepresentedPrimeSupport W Z where
  sourceComponent := P.sourceComponent
  support := component.support
  isIntegral := component.isIntegral
  finiteOverSourceComponent := component.finiteOverSourceComponent
  finite_toSourceComponent := component.finite_toSourceComponent
  surjective_toSourceComponent := component.surjective_toSourceComponent
  toTarget := component.toTarget
  inclusion := component.inclusion
  inclusion_fst := component.inclusion_fst
  inclusion_snd := component.inclusion_snd
  isClosedImmersion := component.isClosedImmersion

/-- The outer weighted prime support in `W ⟶ Z` carried by a left-associated
triple image component. -/
def toWeightedPrimeFiniteCorrespondenceSupport
    {W X Y Z : Geometry.SmSchemeOver k}
    {P : RepresentedPrimeSupport W X} {Q : RepresentedPrimeSupport X Y}
    {R : RepresentedPrimeSupport Y Z}
    {imageData : LeftAssociatedSupportFiberProductImageFactorization P Q R}
    (component : LeftAssociatedSupportFiberProductImageComponent imageData) :
    WeightedPrimeFiniteCorrespondenceSupport W Z where
  multiplicity := component.lengthCoeff
  prime := component.toRepresentedPrimeSupport

end LeftAssociatedSupportFiberProductImageComponent

/-- A finite integral decomposition of the image of the left-associated triple
support-fiber-product map. -/
structure LeftAssociatedSupportFiberProductImageDecomposition
    {W X Y Z : Geometry.SmSchemeOver k}
    (P : RepresentedPrimeSupport W X) (Q : RepresentedPrimeSupport X Y)
    (R : RepresentedPrimeSupport Y Z) where
  imageData : LeftAssociatedSupportFiberProductImageFactorization P Q R
  index : Type u
  fintype_index : Fintype index
  decidableEq_index : DecidableEq index
  component : index → LeftAssociatedSupportFiberProductImageComponent imageData

/-- A finite integral decomposition of the image of the right-associated triple
support-fiber-product map. -/
structure RightAssociatedSupportFiberProductImageDecomposition
    {W X Y Z : Geometry.SmSchemeOver k}
    (P : RepresentedPrimeSupport W X) (Q : RepresentedPrimeSupport X Y)
    (R : RepresentedPrimeSupport Y Z) where
  imageData : RightAssociatedSupportFiberProductImageFactorization P Q R
  index : Type u
  fintype_index : Fintype index
  decidableEq_index : DecidableEq index
  component : index → RightAssociatedSupportFiberProductImageComponent imageData

namespace LeftAssociatedSupportFiberProductImageDecomposition

/-- Forget the left-associated support-fiber-product-specific packaging and view
the image decomposition as a generic finite weighted family on the image. -/
def toFiniteWeightedIntegralImageFamily
    {W X Y Z : Geometry.SmSchemeOver k}
    {P : RepresentedPrimeSupport W X} {Q : RepresentedPrimeSupport X Y}
    {R : RepresentedPrimeSupport Y Z}
    (decomposition : LeftAssociatedSupportFiberProductImageDecomposition P Q R) :
    FiniteWeightedIntegralImageFamily (leftAssociatedCompositionToAmbientProduct P Q R) where
  factorization := decomposition.imageData.toClosedImageFactorization
  family :=
    { index := decomposition.index
      fintype_index := decomposition.fintype_index
      decidableEq_index := decomposition.decidableEq_index
      component := fun i => (decomposition.component i).toWeightedIntClosedSubscheme }

@[simp] theorem toFiniteWeightedIntegralImageFamily_componentInTarget_inclusion
    {W X Y Z : Geometry.SmSchemeOver k}
    {P : RepresentedPrimeSupport W X} {Q : RepresentedPrimeSupport X Y}
    {R : RepresentedPrimeSupport Y Z}
    (decomposition : LeftAssociatedSupportFiberProductImageDecomposition P Q R)
    (i : decomposition.index) :
    (decomposition.toFiniteWeightedIntegralImageFamily.componentInTarget i).support.inclusion =
      (decomposition.component i).inclusion := by
  simpa [FiniteWeightedIntegralImageFamily.componentInTarget,
    LeftAssociatedSupportFiberProductImageDecomposition.toFiniteWeightedIntegralImageFamily,
    LeftAssociatedSupportFiberProductImageComponent.toWeightedIntClosedSubscheme] using
    (decomposition.component i).inclusion_factorization

end LeftAssociatedSupportFiberProductImageDecomposition

namespace RightAssociatedSupportFiberProductImageDecomposition

/-- Forget the right-associated support-fiber-product-specific packaging and
view the image decomposition as a generic finite weighted family on the image. -/
def toFiniteWeightedIntegralImageFamily
    {W X Y Z : Geometry.SmSchemeOver k}
    {P : RepresentedPrimeSupport W X} {Q : RepresentedPrimeSupport X Y}
    {R : RepresentedPrimeSupport Y Z}
    (decomposition : RightAssociatedSupportFiberProductImageDecomposition P Q R) :
    FiniteWeightedIntegralImageFamily (rightAssociatedCompositionToAmbientProduct P Q R) where
  factorization := decomposition.imageData.toClosedImageFactorization
  family :=
    { index := decomposition.index
      fintype_index := decomposition.fintype_index
      decidableEq_index := decomposition.decidableEq_index
      component := fun i => (decomposition.component i).toWeightedIntClosedSubscheme }

@[simp] theorem toFiniteWeightedIntegralImageFamily_componentInTarget_inclusion
    {W X Y Z : Geometry.SmSchemeOver k}
    {P : RepresentedPrimeSupport W X} {Q : RepresentedPrimeSupport X Y}
    {R : RepresentedPrimeSupport Y Z}
    (decomposition : RightAssociatedSupportFiberProductImageDecomposition P Q R)
    (i : decomposition.index) :
    (decomposition.toFiniteWeightedIntegralImageFamily.componentInTarget i).support.inclusion =
      (decomposition.component i).inclusion := by
  simpa [FiniteWeightedIntegralImageFamily.componentInTarget,
    RightAssociatedSupportFiberProductImageDecomposition.toFiniteWeightedIntegralImageFamily,
    RightAssociatedSupportFiberProductImageComponent.toWeightedIntClosedSubscheme] using
    (decomposition.component i).inclusion_factorization

end RightAssociatedSupportFiberProductImageDecomposition

namespace RightAssociatedSupportFiberProductImageComponent

/-- The outer represented prime support in `W ⟶ Z` carried by a right-associated
triple image component. -/
def toRepresentedPrimeSupport
    {W X Y Z : Geometry.SmSchemeOver k}
    {P : RepresentedPrimeSupport W X} {Q : RepresentedPrimeSupport X Y}
    {R : RepresentedPrimeSupport Y Z}
    {imageData : RightAssociatedSupportFiberProductImageFactorization P Q R}
    (component : RightAssociatedSupportFiberProductImageComponent imageData) :
    RepresentedPrimeSupport W Z where
  sourceComponent := P.sourceComponent
  support := component.support
  isIntegral := component.isIntegral
  finiteOverSourceComponent := component.finiteOverSourceComponent
  finite_toSourceComponent := component.finite_toSourceComponent
  surjective_toSourceComponent := component.surjective_toSourceComponent
  toTarget := component.toTarget
  inclusion := component.inclusion
  inclusion_fst := component.inclusion_fst
  inclusion_snd := component.inclusion_snd
  isClosedImmersion := component.isClosedImmersion

/-- The outer weighted prime support in `W ⟶ Z` carried by a right-associated
triple image component. -/
def toWeightedPrimeFiniteCorrespondenceSupport
    {W X Y Z : Geometry.SmSchemeOver k}
    {P : RepresentedPrimeSupport W X} {Q : RepresentedPrimeSupport X Y}
    {R : RepresentedPrimeSupport Y Z}
    {imageData : RightAssociatedSupportFiberProductImageFactorization P Q R}
    (component : RightAssociatedSupportFiberProductImageComponent imageData) :
    WeightedPrimeFiniteCorrespondenceSupport W Z where
  multiplicity := component.lengthCoeff
  prime := component.toRepresentedPrimeSupport

end RightAssociatedSupportFiberProductImageComponent

namespace LeftAssociatedSupportFiberProductImageComponent

@[simp] theorem toRightAssociated_toRepresentedPrimeSupport
    {W X Y Z : Geometry.SmSchemeOver k}
    {P : RepresentedPrimeSupport W X} {Q : RepresentedPrimeSupport X Y}
    {R : RepresentedPrimeSupport Y Z}
    {imageData : LeftAssociatedSupportFiberProductImageFactorization P Q R}
    (component : LeftAssociatedSupportFiberProductImageComponent imageData) :
    component.toRightAssociated.toRepresentedPrimeSupport =
      component.toRepresentedPrimeSupport := rfl

@[simp] theorem toRightAssociated_toWeightedPrimeFiniteCorrespondenceSupport
    {W X Y Z : Geometry.SmSchemeOver k}
    {P : RepresentedPrimeSupport W X} {Q : RepresentedPrimeSupport X Y}
    {R : RepresentedPrimeSupport Y Z}
    {imageData : LeftAssociatedSupportFiberProductImageFactorization P Q R}
    (component : LeftAssociatedSupportFiberProductImageComponent imageData) :
    component.toRightAssociated.toWeightedPrimeFiniteCorrespondenceSupport =
      component.toWeightedPrimeFiniteCorrespondenceSupport := rfl

end LeftAssociatedSupportFiberProductImageComponent

namespace LeftAssociatedSupportFiberProductImageDecomposition

/-- The outer finite correspondence presentation induced by a left-associated
triple image decomposition. -/
def toPresentation
    {W X Y Z : Geometry.SmSchemeOver k}
    {P : RepresentedPrimeSupport W X} {Q : RepresentedPrimeSupport X Y}
    {R : RepresentedPrimeSupport Y Z}
    (decomposition : LeftAssociatedSupportFiberProductImageDecomposition P Q R) :
    FiniteCorrespondencePresentation W Z := by
  classical
  letI := decomposition.fintype_index
  letI := decomposition.decidableEq_index
  exact Finset.univ.sum fun i =>
    FiniteCorrespondencePresentation.ofWeightedPrimeSupport
      ((decomposition.component i).toWeightedPrimeFiniteCorrespondenceSupport)

/-- Transport a left-associated triple image decomposition across the support
associator. -/
def toRightAssociated
    {W X Y Z : Geometry.SmSchemeOver k}
    {P : RepresentedPrimeSupport W X} {Q : RepresentedPrimeSupport X Y}
    {R : RepresentedPrimeSupport Y Z}
    (decomposition : LeftAssociatedSupportFiberProductImageDecomposition P Q R) :
    RightAssociatedSupportFiberProductImageDecomposition P Q R where
  imageData := decomposition.imageData.toRightAssociated
  index := decomposition.index
  fintype_index := decomposition.fintype_index
  decidableEq_index := decomposition.decidableEq_index
  component := fun i => (decomposition.component i).toRightAssociated

@[simp] theorem toRightAssociated_index
    {W X Y Z : Geometry.SmSchemeOver k}
    {P : RepresentedPrimeSupport W X} {Q : RepresentedPrimeSupport X Y}
    {R : RepresentedPrimeSupport Y Z}
    (decomposition : LeftAssociatedSupportFiberProductImageDecomposition P Q R) :
    decomposition.toRightAssociated.index = decomposition.index := rfl

@[simp] theorem toRightAssociated_component
  {W X Y Z : Geometry.SmSchemeOver k}
  {P : RepresentedPrimeSupport W X} {Q : RepresentedPrimeSupport X Y}
  {R : RepresentedPrimeSupport Y Z}
  (decomposition : LeftAssociatedSupportFiberProductImageDecomposition P Q R)
  (i : decomposition.index) :
  decomposition.toRightAssociated.component i =
    (decomposition.component i).toRightAssociated := rfl

end LeftAssociatedSupportFiberProductImageDecomposition

namespace RightAssociatedSupportFiberProductImageDecomposition

/-- The outer finite correspondence presentation induced by a right-associated
triple image decomposition. -/
def toPresentation
    {W X Y Z : Geometry.SmSchemeOver k}
    {P : RepresentedPrimeSupport W X} {Q : RepresentedPrimeSupport X Y}
    {R : RepresentedPrimeSupport Y Z}
    (decomposition : RightAssociatedSupportFiberProductImageDecomposition P Q R) :
    FiniteCorrespondencePresentation W Z := by
  classical
  letI := decomposition.fintype_index
  letI := decomposition.decidableEq_index
  exact Finset.univ.sum fun i =>
    FiniteCorrespondencePresentation.ofWeightedPrimeSupport
      ((decomposition.component i).toWeightedPrimeFiniteCorrespondenceSupport)

end RightAssociatedSupportFiberProductImageDecomposition

namespace LeftAssociatedSupportFiberProductImageDecomposition

@[simp] theorem toRightAssociated_toPresentation
    {W X Y Z : Geometry.SmSchemeOver k}
    {P : RepresentedPrimeSupport W X} {Q : RepresentedPrimeSupport X Y}
    {R : RepresentedPrimeSupport Y Z}
    (decomposition : LeftAssociatedSupportFiberProductImageDecomposition P Q R) :
    decomposition.toRightAssociated.toPresentation = decomposition.toPresentation := by
  classical
  unfold RightAssociatedSupportFiberProductImageDecomposition.toPresentation
  unfold LeftAssociatedSupportFiberProductImageDecomposition.toPresentation
  refine Finset.sum_congr rfl ?_
  intro i hi
  simp

end LeftAssociatedSupportFiberProductImageDecomposition

/-- One integral component of the scheme-theoretic image of the canonical map
from `P.support ×_Y Q.support` to `sourceComponent(P) ×_k Z`, equipped with its
length/multiplicity coefficient. -/
structure SupportFiberProductImageComponent
    {X Y Z : Geometry.SmSchemeOver k}
    {P : RepresentedPrimeSupport X Y} {Q : RepresentedPrimeSupport Y Z}
    (imageData : SupportFiberProductImageFactorization P Q) where
  lengthCoeff : ℕ
  support : Scheme
  isIntegral : IsIntegral support
  toImage : support ⟶ imageData.image
  toImageClosedImmersion : IsClosedImmersion toImage
  toCompositionFiberProduct : support ⟶ compositionFiberProduct P Q
  toImage_factorization :
    toCompositionFiberProduct ≫ imageData.toImage = toImage
  finiteOverSourceComponent : support ⟶ P.sourceComponent.carrier.scheme
  finite_toSourceComponent : IsFinite finiteOverSourceComponent
  surjective_toSourceComponent : Function.Surjective finiteOverSourceComponent.base
  toTarget : support ⟶ Z.scheme
  inclusion : support ⟶ overBaseProduct P.sourceComponent.carrier Z
  inclusion_factorization : toImage ≫ imageData.imageToAmbientProduct = inclusion
  inclusion_fst : inclusion ≫ overBaseProduct.fst P.sourceComponent.carrier Z =
    finiteOverSourceComponent
  inclusion_snd : inclusion ≫ overBaseProduct.snd P.sourceComponent.carrier Z =
    toTarget
  isClosedImmersion : IsClosedImmersion inclusion
  toCompositionFiberProduct_fst :
    toCompositionFiberProduct ≫ compositionFiberFst P Q ≫ P.toSourceComponent =
      finiteOverSourceComponent
  toCompositionFiberProduct_snd :
    toCompositionFiberProduct ≫ compositionFiberSnd P Q ≫ Q.toTargetScheme =
      toTarget

/-- A finite integral decomposition of the scheme-theoretic image of the
canonical support-fiber-product map, together with the associated length
coefficients. -/
structure SupportFiberProductImageDecomposition
    {X Y Z : Geometry.SmSchemeOver k}
    (P : RepresentedPrimeSupport X Y) (Q : RepresentedPrimeSupport Y Z) where
  imageData : SupportFiberProductImageFactorization P Q
  index : Type u
  fintype_index : Fintype index
  decidableEq_index : DecidableEq index
  component : index → SupportFiberProductImageComponent imageData

/-- View one support-fiber-product image component as a weighted integral
closed subscheme of the scheme-theoretic image. -/
def supportFiberProductImageComponentToWeightedIntClosedSubscheme
    {X Y Z : Geometry.SmSchemeOver k}
    {P : RepresentedPrimeSupport X Y} {Q : RepresentedPrimeSupport Y Z}
    {imageData : SupportFiberProductImageFactorization P Q}
    (component : SupportFiberProductImageComponent imageData) :
    WeightedIntClosedSubscheme imageData.image where
  multiplicity := component.lengthCoeff
  support :=
    { scheme := component.support
      inclusion := component.toImage
      isClosedImm := component.toImageClosedImmersion
      isIntegral := component.isIntegral }

/-- Forget the support-fiber-product-specific packaging and view the binary
image decomposition as a generic finite weighted family on the image. -/
def supportFiberProductImageDecompositionToFiniteWeightedIntegralImageFamily
    {X Y Z : Geometry.SmSchemeOver k}
    {P : RepresentedPrimeSupport X Y} {Q : RepresentedPrimeSupport Y Z}
    (decomposition : SupportFiberProductImageDecomposition P Q) :
    FiniteWeightedIntegralImageFamily (compositionToAmbientProduct P Q) where
  factorization := decomposition.imageData.toClosedImageFactorization
  family :=
    { index := decomposition.index
      fintype_index := decomposition.fintype_index
      decidableEq_index := decomposition.decidableEq_index
      component := fun i => supportFiberProductImageComponentToWeightedIntClosedSubscheme
        (decomposition.component i) }

@[simp] theorem supportFiberProductImageDecompositionToFiniteWeightedIntegralImageFamily_componentInTarget_inclusion
    {X Y Z : Geometry.SmSchemeOver k}
    {P : RepresentedPrimeSupport X Y} {Q : RepresentedPrimeSupport Y Z}
    (decomposition : SupportFiberProductImageDecomposition P Q)
    (i : decomposition.index) :
    ((supportFiberProductImageDecompositionToFiniteWeightedIntegralImageFamily
        decomposition).componentInTarget i).support.inclusion =
      (decomposition.component i).inclusion := by
  simpa [FiniteWeightedIntegralImageFamily.componentInTarget,
    supportFiberProductImageDecompositionToFiniteWeightedIntegralImageFamily,
    supportFiberProductImageComponentToWeightedIntClosedSubscheme] using
    (decomposition.component i).inclusion_factorization

/-- One integral component contributing to the composition of represented prime
supports `P : X ⟶ Y` and `Q : Y ⟶ Z`. It lies over the support fiber product
`P.support ×_Y Q.support` and induces a represented prime support from `X` to
`Z` over the source component of `P`. -/
structure RepresentedPrimeCompositionPiece
    {X Y Z : Geometry.SmSchemeOver k}
    (P : RepresentedPrimeSupport X Y) (Q : RepresentedPrimeSupport Y Z) where
  multiplicity : ℕ
  support : Scheme
  isIntegral : IsIntegral support
  finiteOverSourceComponent : support ⟶ P.sourceComponent.carrier.scheme
  finite_toSourceComponent : IsFinite finiteOverSourceComponent
  surjective_toSourceComponent : Function.Surjective finiteOverSourceComponent.base
  toTarget : support ⟶ Z.scheme
  inclusion : support ⟶ overBaseProduct P.sourceComponent.carrier Z
  inclusion_fst : inclusion ≫ overBaseProduct.fst P.sourceComponent.carrier Z =
    finiteOverSourceComponent
  inclusion_snd : inclusion ≫ overBaseProduct.snd P.sourceComponent.carrier Z =
    toTarget
  isClosedImmersion : IsClosedImmersion inclusion
  toCompositionFiberProduct : support ⟶ compositionFiberProduct P Q
  toCompositionFiberProduct_fst :
    toCompositionFiberProduct ≫ compositionFiberFst P Q ≫ P.toSourceComponent =
      finiteOverSourceComponent
  toCompositionFiberProduct_snd :
    toCompositionFiberProduct ≫ compositionFiberSnd P Q ≫ Q.toTargetScheme =
      toTarget

/-- A finite family of integral closed subschemes of an arbitrary scheme. This
is the source-side decomposition layer before target-image multiplicities are
attached. -/
structure FiniteIntegralClosedFamily (X : Scheme.{u}) where
  index : Type u
  fintype_index : Fintype index
  decidableEq_index : DecidableEq index
  component : index → IntClosedSubscheme X

/-- Source-lifted data for one composed image piece.

This stores the honest triple `(R, D_R, [k(R):k(D_R)])`:

* `sourceSubscheme` is the source-side integral closed piece
  `R ⊂ P.support ×_Y Q.support`,
* `targetSubscheme` is the target image piece
  `D_R ⊂ sourceComponent(P) ×_k Z`,
* `genericLengthData` packages the function-field extension from `R` to `D_R`,
  and `multiplicity` is required to agree with the resulting canonical
  multiplicity.

The existing `SupportFiberProductImageComponent` is recovered by forgetting the
explicit source piece. -/
structure SupportFiberProductLiftedImageComponentData
    {X Y Z : Geometry.SmSchemeOver k}
    {P : RepresentedPrimeSupport X Y} {Q : RepresentedPrimeSupport Y Z}
    (imageData : SupportFiberProductImageFactorization P Q) where
  sourceSubscheme : IntClosedSubscheme (compositionFiberProduct P Q)
  targetSubscheme : IntClosedSubscheme (overBaseProduct P.sourceComponent.carrier Z)
  genericLengthData :
    _root_.FiniteMapImageFunctionFieldData
      (compositionToAmbientProduct P Q)
      sourceSubscheme
      targetSubscheme
  multiplicity : ℕ
  multiplicity_eq_genericLength :
    multiplicity =
      _root_.finiteMapImageMultiplicity (compositionToAmbientProduct P Q) genericLengthData
  liftedTargetToCompositionFiberProduct :
    targetSubscheme.scheme ⟶ compositionFiberProduct P Q
  finiteOverSourceComponent : targetSubscheme.scheme ⟶ P.sourceComponent.carrier.scheme
  finite_toSourceComponent : IsFinite finiteOverSourceComponent
  surjective_toSourceComponent : Function.Surjective finiteOverSourceComponent.base
  toTarget : targetSubscheme.scheme ⟶ Z.scheme
  targetSubscheme_inclusion_fst :
    targetSubscheme.inclusion ≫ overBaseProduct.fst P.sourceComponent.carrier Z =
      finiteOverSourceComponent
  targetSubscheme_inclusion_snd :
    targetSubscheme.inclusion ≫ overBaseProduct.snd P.sourceComponent.carrier Z =
      toTarget
  liftedTarget_fst :
    liftedTargetToCompositionFiberProduct ≫ compositionFiberFst P Q ≫ P.toSourceComponent =
      finiteOverSourceComponent
  liftedTarget_snd :
    liftedTargetToCompositionFiberProduct ≫ compositionFiberSnd P Q ≫ Q.toTargetScheme =
      toTarget
  sourceToTarget : sourceSubscheme.scheme ⟶ targetSubscheme.scheme
  sourceToTarget_factorization :
    sourceSubscheme.inclusion ≫ compositionToAmbientProduct P Q =
      sourceToTarget ≫ targetSubscheme.inclusion
  toImage : targetSubscheme.scheme ⟶ imageData.image
  toImageClosedImmersion : IsClosedImmersion toImage
  toImage_factorization :
    liftedTargetToCompositionFiberProduct ≫ imageData.toImage = toImage
  inclusion_factorization :
    toImage ≫ imageData.imageToAmbientProduct = targetSubscheme.inclusion

namespace SupportFiberProductLiftedImageComponentData

@[simp] theorem multiplicity_eq_finiteMapImageMultiplicity
    {X Y Z : Geometry.SmSchemeOver k}
    {P : RepresentedPrimeSupport X Y} {Q : RepresentedPrimeSupport Y Z}
    {imageData : SupportFiberProductImageFactorization P Q}
    (data : SupportFiberProductLiftedImageComponentData imageData) :
    data.multiplicity =
      _root_.finiteMapImageMultiplicity (compositionToAmbientProduct P Q) data.genericLengthData :=
  data.multiplicity_eq_genericLength

/-- Turn source-lifted image-component data into the binary image-component
packaging used by the represented-prime composition API. -/
def toSupportFiberProductImageComponent
    {X Y Z : Geometry.SmSchemeOver k}
    {P : RepresentedPrimeSupport X Y} {Q : RepresentedPrimeSupport Y Z}
    {imageData : SupportFiberProductImageFactorization P Q}
    (data : SupportFiberProductLiftedImageComponentData imageData) :
    SupportFiberProductImageComponent imageData where
  lengthCoeff := data.multiplicity
  support := data.targetSubscheme.scheme
  isIntegral := data.targetSubscheme.isIntegral
  toImage := data.toImage
  toImageClosedImmersion := data.toImageClosedImmersion
  toCompositionFiberProduct := data.liftedTargetToCompositionFiberProduct
  toImage_factorization := data.toImage_factorization
  finiteOverSourceComponent := data.finiteOverSourceComponent
  finite_toSourceComponent := data.finite_toSourceComponent
  surjective_toSourceComponent := data.surjective_toSourceComponent
  toTarget := data.toTarget
  inclusion := data.targetSubscheme.inclusion
  inclusion_factorization := data.inclusion_factorization
  inclusion_fst := data.targetSubscheme_inclusion_fst
  inclusion_snd := data.targetSubscheme_inclusion_snd
  isClosedImmersion := data.targetSubscheme.isClosedImm
  toCompositionFiberProduct_fst := data.liftedTarget_fst
  toCompositionFiberProduct_snd := data.liftedTarget_snd

end SupportFiberProductLiftedImageComponentData

/-- Finite source-lifted image data for the support-fiber-product map.

This is the exact bridge between a target-side finite pushforward family and a
`SupportFiberProductImageDecomposition`: once each weighted image component is
equipped with its lift back into the support fiber product and its factorization
through the chosen scheme-theoretic image, the decomposition is obtained by
repackaging. -/
structure SupportFiberProductLiftedImageDecompositionData
    {X Y Z : Geometry.SmSchemeOver k}
    (P : RepresentedPrimeSupport X Y) (Q : RepresentedPrimeSupport Y Z) where
  imageData : SupportFiberProductImageFactorization P Q
  index : Type u
  fintype_index : Fintype index
  decidableEq_index : DecidableEq index
  component : index → SupportFiberProductLiftedImageComponentData imageData

namespace SupportFiberProductLiftedImageDecompositionData

/-- The finite family of source integral closed pieces underlying a lifted
support-fiber-product decomposition. -/
def sourceComponentFamily
    {X Y Z : Geometry.SmSchemeOver k}
    {P : RepresentedPrimeSupport X Y} {Q : RepresentedPrimeSupport Y Z}
    (data : SupportFiberProductLiftedImageDecompositionData P Q) :
    FiniteIntegralClosedFamily (compositionFiberProduct P Q) where
  index := data.index
  fintype_index := data.fintype_index
  decidableEq_index := data.decidableEq_index
  component := fun i => (data.component i).sourceSubscheme

/-- Repackage finite source-lifted image data as the binary image decomposition
required by the represented-prime composition layer. -/
def toSupportFiberProductImageDecomposition
    {X Y Z : Geometry.SmSchemeOver k}
    {P : RepresentedPrimeSupport X Y} {Q : RepresentedPrimeSupport Y Z}
    (data : SupportFiberProductLiftedImageDecompositionData P Q) :
    SupportFiberProductImageDecomposition P Q where
  imageData := data.imageData
  index := data.index
  fintype_index := data.fintype_index
  decidableEq_index := data.decidableEq_index
  component := fun i => (data.component i).toSupportFiberProductImageComponent

end SupportFiberProductLiftedImageDecompositionData

namespace RepresentedPrimeCompositionPiece

/-- The represented prime support induced by one composed piece. -/
def toRepresentedPrimeSupport {X Y Z : Geometry.SmSchemeOver k}
    {P : RepresentedPrimeSupport X Y} {Q : RepresentedPrimeSupport Y Z}
    (piece : RepresentedPrimeCompositionPiece P Q) :
    RepresentedPrimeSupport X Z where
  sourceComponent := P.sourceComponent
  support := piece.support
  isIntegral := piece.isIntegral
  finiteOverSourceComponent := piece.finiteOverSourceComponent
  finite_toSourceComponent := piece.finite_toSourceComponent
  surjective_toSourceComponent := piece.surjective_toSourceComponent
  toTarget := piece.toTarget
  inclusion := piece.inclusion
  inclusion_fst := piece.inclusion_fst
  inclusion_snd := piece.inclusion_snd
  isClosedImmersion := piece.isClosedImmersion

/-- The weighted prime support induced by one composed piece. -/
def toWeightedPrimeFiniteCorrespondenceSupport {X Y Z : Geometry.SmSchemeOver k}
    {P : RepresentedPrimeSupport X Y} {Q : RepresentedPrimeSupport Y Z}
    (piece : RepresentedPrimeCompositionPiece P Q) :
    WeightedPrimeFiniteCorrespondenceSupport X Z where
  multiplicity := piece.multiplicity
  prime := piece.toRepresentedPrimeSupport

end RepresentedPrimeCompositionPiece

/-- A finite family of integral pieces computing the composition of two
represented prime supports. -/
structure RepresentedPrimeCompositionDatum
    {X Y Z : Geometry.SmSchemeOver k}
    (P : RepresentedPrimeSupport X Y) (Q : RepresentedPrimeSupport Y Z) where
  index : Type u
  fintype_index : Fintype index
  decidableEq_index : DecidableEq index
  piece : index → RepresentedPrimeCompositionPiece P Q

namespace RepresentedPrimeCompositionDatum

/-- The finite correspondence presentation carried by a geometric composition
datum. -/
def toPresentation {X Y Z : Geometry.SmSchemeOver k}
    {P : RepresentedPrimeSupport X Y} {Q : RepresentedPrimeSupport Y Z}
    (datum : RepresentedPrimeCompositionDatum P Q) :
    FiniteCorrespondencePresentation X Z := by
  classical
  letI := datum.fintype_index
  letI := datum.decidableEq_index
  exact Finset.univ.sum fun i =>
    FiniteCorrespondencePresentation.ofWeightedPrimeSupport
      ((datum.piece i).toWeightedPrimeFiniteCorrespondenceSupport)

@[simp] theorem toPresentation_eq_zero_of_isEmpty {X Y Z : Geometry.SmSchemeOver k}
    {P : RepresentedPrimeSupport X Y} {Q : RepresentedPrimeSupport Y Z}
    (datum : RepresentedPrimeCompositionDatum P Q) [IsEmpty datum.index] :
    datum.toPresentation = 0 := by
  classical
  simp [RepresentedPrimeCompositionDatum.toPresentation]

end RepresentedPrimeCompositionDatum

namespace SupportFiberProductImageComponent

/-- The outer represented prime support in `X ⟶ Z` carried by a binary image
component. -/
def toRepresentedPrimeSupport
    {X Y Z : Geometry.SmSchemeOver k}
    {P : RepresentedPrimeSupport X Y} {Q : RepresentedPrimeSupport Y Z}
    {imageData : SupportFiberProductImageFactorization P Q}
    (component : SupportFiberProductImageComponent imageData) :
    RepresentedPrimeSupport X Z where
  sourceComponent := P.sourceComponent
  support := component.support
  isIntegral := component.isIntegral
  finiteOverSourceComponent := component.finiteOverSourceComponent
  finite_toSourceComponent := component.finite_toSourceComponent
  surjective_toSourceComponent := component.surjective_toSourceComponent
  toTarget := component.toTarget
  inclusion := component.inclusion
  inclusion_fst := component.inclusion_fst
  inclusion_snd := component.inclusion_snd
  isClosedImmersion := component.isClosedImmersion

/-- The outer weighted prime support in `X ⟶ Z` carried by a binary image
component. -/
def toWeightedPrimeFiniteCorrespondenceSupport
    {X Y Z : Geometry.SmSchemeOver k}
    {P : RepresentedPrimeSupport X Y} {Q : RepresentedPrimeSupport Y Z}
    {imageData : SupportFiberProductImageFactorization P Q}
    (component : SupportFiberProductImageComponent imageData) :
    WeightedPrimeFiniteCorrespondenceSupport X Z where
  multiplicity := component.lengthCoeff
  prime := component.toRepresentedPrimeSupport

/-- An image component determines a represented-prime composition piece by
composing its closed immersion into the scheme-theoretic image with the image
map into `sourceComponent(P) ×_k Z`. -/
def toRepresentedPrimeCompositionPiece
    {X Y Z : Geometry.SmSchemeOver k}
    {P : RepresentedPrimeSupport X Y} {Q : RepresentedPrimeSupport Y Z}
    {imageData : SupportFiberProductImageFactorization P Q}
    (component : SupportFiberProductImageComponent imageData) :
    RepresentedPrimeCompositionPiece P Q where
  multiplicity := component.lengthCoeff
  support := component.support
  isIntegral := component.isIntegral
  finiteOverSourceComponent := component.finiteOverSourceComponent
  finite_toSourceComponent := component.finite_toSourceComponent
  surjective_toSourceComponent := component.surjective_toSourceComponent
  toTarget := component.toTarget
  inclusion := component.inclusion
  inclusion_fst := component.inclusion_fst
  inclusion_snd := component.inclusion_snd
  isClosedImmersion := component.isClosedImmersion
  toCompositionFiberProduct := component.toCompositionFiberProduct
  toCompositionFiberProduct_fst := component.toCompositionFiberProduct_fst
  toCompositionFiberProduct_snd := component.toCompositionFiberProduct_snd

@[simp] theorem toRepresentedPrimeCompositionPiece_toRepresentedPrimeSupport
    {X Y Z : Geometry.SmSchemeOver k}
    {P : RepresentedPrimeSupport X Y} {Q : RepresentedPrimeSupport Y Z}
    {imageData : SupportFiberProductImageFactorization P Q}
    (component : SupportFiberProductImageComponent imageData) :
    component.toRepresentedPrimeCompositionPiece.toRepresentedPrimeSupport =
      component.toRepresentedPrimeSupport := rfl

@[simp] theorem toRepresentedPrimeCompositionPiece_toWeightedPrimeFiniteCorrespondenceSupport
    {X Y Z : Geometry.SmSchemeOver k}
    {P : RepresentedPrimeSupport X Y} {Q : RepresentedPrimeSupport Y Z}
    {imageData : SupportFiberProductImageFactorization P Q}
    (component : SupportFiberProductImageComponent imageData) :
    component.toRepresentedPrimeCompositionPiece.toWeightedPrimeFiniteCorrespondenceSupport =
      component.toWeightedPrimeFiniteCorrespondenceSupport := rfl

end SupportFiberProductImageComponent

namespace SupportFiberProductImageDecomposition

/-- The outer finite correspondence presentation induced directly by a binary
support-fiber-product image decomposition. -/
def toPresentation
    {X Y Z : Geometry.SmSchemeOver k}
    {P : RepresentedPrimeSupport X Y} {Q : RepresentedPrimeSupport Y Z}
    (decomposition : SupportFiberProductImageDecomposition P Q) :
    FiniteCorrespondencePresentation X Z := by
  classical
  letI := decomposition.fintype_index
  letI := decomposition.decidableEq_index
  exact Finset.univ.sum fun i =>
    FiniteCorrespondencePresentation.ofWeightedPrimeSupport
      ((decomposition.component i).toWeightedPrimeFiniteCorrespondenceSupport)

/-- Convert a support-fiber-product image decomposition into the finite family
of represented-prime composition pieces used by the composition API. -/
def toRepresentedPrimeCompositionDatum
    {X Y Z : Geometry.SmSchemeOver k}
    {P : RepresentedPrimeSupport X Y} {Q : RepresentedPrimeSupport Y Z}
    (decomposition : SupportFiberProductImageDecomposition P Q) :
    RepresentedPrimeCompositionDatum P Q where
  index := decomposition.index
  fintype_index := decomposition.fintype_index
  decidableEq_index := decomposition.decidableEq_index
  piece := fun i =>
    (decomposition.component i).toRepresentedPrimeCompositionPiece

@[simp] theorem toPresentation_eq_toRepresentedPrimeCompositionDatum_toPresentation
    {X Y Z : Geometry.SmSchemeOver k}
    {P : RepresentedPrimeSupport X Y} {Q : RepresentedPrimeSupport Y Z}
    (decomposition : SupportFiberProductImageDecomposition P Q) :
    decomposition.toPresentation =
      decomposition.toRepresentedPrimeCompositionDatum.toPresentation := by
  classical
  unfold SupportFiberProductImageDecomposition.toPresentation
  unfold SupportFiberProductImageDecomposition.toRepresentedPrimeCompositionDatum
  unfold RepresentedPrimeCompositionDatum.toPresentation
  refine Finset.sum_congr rfl ?_
  intro i hi
  simp

@[simp] theorem toRepresentedPrimeCompositionDatum_piece_multiplicity
    {X Y Z : Geometry.SmSchemeOver k}
    {P : RepresentedPrimeSupport X Y} {Q : RepresentedPrimeSupport Y Z}
    (decomposition : SupportFiberProductImageDecomposition P Q)
    (i : decomposition.index) :
    (decomposition.toRepresentedPrimeCompositionDatum.piece i).multiplicity =
      ((supportFiberProductImageDecompositionToFiniteWeightedIntegralImageFamily
        decomposition).componentInTarget i).multiplicity := by
  rfl

@[simp] theorem toRepresentedPrimeCompositionDatum_piece_inclusion
    {X Y Z : Geometry.SmSchemeOver k}
    {P : RepresentedPrimeSupport X Y} {Q : RepresentedPrimeSupport Y Z}
    (decomposition : SupportFiberProductImageDecomposition P Q)
    (i : decomposition.index) :
    (decomposition.toRepresentedPrimeCompositionDatum.piece i).inclusion =
      ((supportFiberProductImageDecompositionToFiniteWeightedIntegralImageFamily
        decomposition).componentInTarget i).support.inclusion := by
  simp [SupportFiberProductImageDecomposition.toRepresentedPrimeCompositionDatum,
    SupportFiberProductImageComponent.toRepresentedPrimeCompositionPiece,
    supportFiberProductImageDecompositionToFiniteWeightedIntegralImageFamily_componentInTarget_inclusion]

/-- If the underlying support fiber product is empty, then any image
decomposition indexed over it must itself have empty index. -/
theorem isEmpty_index_of_isEmpty_compositionFiberProduct
    {X Y Z : Geometry.SmSchemeOver k}
    {P : RepresentedPrimeSupport X Y} {Q : RepresentedPrimeSupport Y Z}
    (decomposition : SupportFiberProductImageDecomposition P Q)
    [IsEmpty (compositionFiberProduct P Q)] :
    IsEmpty decomposition.index := by
  refine ⟨fun i => ?_⟩
  let component := decomposition.component i
  have hsource_nonempty : (Set.range P.sourceComponent.toAmbient.base).Nonempty := by
    exact P.sourceComponent.range_mem_irreducibleComponents.1.nonempty
  rcases hsource_nonempty with ⟨_, xSource, rfl⟩
  let x : component.support := Classical.choose (component.surjective_toSourceComponent xSource)
  exact isEmptyElim (component.toCompositionFiberProduct.base x)

end SupportFiberProductImageDecomposition

namespace RepresentedPrimeCompositionDatum

/-- Build composition data directly from a finite integral decomposition of the
scheme-theoretic image of the canonical support-fiber-product map. -/
def ofSupportFiberProductImageDecomposition
    {X Y Z : Geometry.SmSchemeOver k}
    {P : RepresentedPrimeSupport X Y} {Q : RepresentedPrimeSupport Y Z}
    (decomposition : SupportFiberProductImageDecomposition P Q) :
    RepresentedPrimeCompositionDatum P Q :=
  decomposition.toRepresentedPrimeCompositionDatum

@[simp] theorem ofSupportFiberProductImageDecomposition_toPresentation
    {X Y Z : Geometry.SmSchemeOver k}
    {P : RepresentedPrimeSupport X Y} {Q : RepresentedPrimeSupport Y Z}
    (decomposition : SupportFiberProductImageDecomposition P Q) :
    (RepresentedPrimeCompositionDatum.ofSupportFiberProductImageDecomposition
      decomposition).toPresentation = decomposition.toPresentation := by
  simpa [RepresentedPrimeCompositionDatum.ofSupportFiberProductImageDecomposition] using
    decomposition.toPresentation_eq_toRepresentedPrimeCompositionDatum_toPresentation.symm

@[simp] theorem ofSupportFiberProductImageDecomposition_toPresentation_eq_zero_of_isEmpty
    {X Y Z : Geometry.SmSchemeOver k}
    {P : RepresentedPrimeSupport X Y} {Q : RepresentedPrimeSupport Y Z}
    (decomposition : SupportFiberProductImageDecomposition P Q)
    [IsEmpty decomposition.index] :
    (RepresentedPrimeCompositionDatum.ofSupportFiberProductImageDecomposition
      decomposition).toPresentation = 0 := by
  letI : IsEmpty decomposition.toRepresentedPrimeCompositionDatum.index := by
    dsimp [SupportFiberProductImageDecomposition.toRepresentedPrimeCompositionDatum]
    infer_instance
  change decomposition.toRepresentedPrimeCompositionDatum.toPresentation = 0
  exact RepresentedPrimeCompositionDatum.toPresentation_eq_zero_of_isEmpty
    (datum := decomposition.toRepresentedPrimeCompositionDatum)

/-- The canonical left-identity piece for composing the diagonal support on the
source component of `P` with `P` itself. This is the geometric singleton coming
from the canonical pullback isomorphism
`sourceComponent(P) ×_X P.support ≅ P.support`. -/
def diagonalLeftIdentityPiece {X Y : Geometry.SmSchemeOver k}
    (P : RepresentedPrimeSupport X Y) :
    RepresentedPrimeCompositionPiece
      (SourceIrreducibleComponent.diagonalRepresentedPrimeSupport P.sourceComponent) P where
  multiplicity := 1
  support := P.support
  isIntegral := P.isIntegral
  finiteOverSourceComponent := P.finiteOverSourceComponent
  finite_toSourceComponent := P.finite_toSourceComponent
  surjective_toSourceComponent := P.surjective_toSourceComponent
  toTarget := P.toTarget
  inclusion := P.inclusion
  inclusion_fst := P.inclusion_fst
  inclusion_snd := P.inclusion_snd
  isClosedImmersion := P.isClosedImmersion
  toCompositionFiberProduct :=
    pullback.lift P.toSourceComponent (𝟙 P.support) (by
      simp [PrimeFiniteCorrespondenceSupport.toAmbientSource,
        SourceIrreducibleComponent.diagonalRepresentedPrimeSupport])
  toCompositionFiberProduct_fst := by
    calc
      pullback.lift P.toSourceComponent (𝟙 P.support) (by
          simp [PrimeFiniteCorrespondenceSupport.toAmbientSource,
            SourceIrreducibleComponent.diagonalRepresentedPrimeSupport]) ≫
          compositionFiberFst
            (SourceIrreducibleComponent.diagonalRepresentedPrimeSupport P.sourceComponent) P ≫
          (SourceIrreducibleComponent.diagonalRepresentedPrimeSupport
            P.sourceComponent).toSourceComponent
          = P.toSourceComponent ≫
              (SourceIrreducibleComponent.diagonalRepresentedPrimeSupport
                P.sourceComponent).toSourceComponent := by
                  simp [compositionFiberFst, compositionFiberProduct]
      _ = P.finiteOverSourceComponent := by
            simp [PrimeFiniteCorrespondenceSupport.toSourceComponent,
              SourceIrreducibleComponent.diagonalRepresentedPrimeSupport,
              Category.assoc]
  toCompositionFiberProduct_snd := by
    simp [compositionFiberSnd, compositionFiberProduct]

/-- The singleton datum implementing left identity on represented prime
supports. -/
def diagonalLeftIdentityDatum {X Y : Geometry.SmSchemeOver k}
    (P : RepresentedPrimeSupport X Y) :
    RepresentedPrimeCompositionDatum
      (SourceIrreducibleComponent.diagonalRepresentedPrimeSupport P.sourceComponent) P where
  index := PUnit
  fintype_index := inferInstance
  decidableEq_index := inferInstance
  piece := fun _ => diagonalLeftIdentityPiece P

@[simp] theorem diagonalLeftIdentityDatum_toPresentation {X Y : Geometry.SmSchemeOver k}
    (P : RepresentedPrimeSupport X Y) :
    (diagonalLeftIdentityDatum P).toPresentation =
      FiniteCorrespondencePresentation.ofPrimeSupport P := by
  cases P
  simp [diagonalLeftIdentityDatum, diagonalLeftIdentityPiece,
    RepresentedPrimeCompositionDatum.toPresentation,
    FiniteCorrespondencePresentation.ofPrimeSupport,
    FiniteCorrespondencePresentation.ofWeightedPrimeSupport,
    RepresentedPrimeCompositionPiece.toWeightedPrimeFiniteCorrespondenceSupport,
    RepresentedPrimeCompositionPiece.toRepresentedPrimeSupport,
    SourceIrreducibleComponent.diagonalRepresentedPrimeSupport]

@[simp] theorem diagonalLeftIdentityDatum_toGeomSingle {X Y : Geometry.SmSchemeOver k}
    (P : RepresentedPrimeSupport X Y) :
    FiniteCorrespondencePresentation.toGeom ((diagonalLeftIdentityDatum P).toPresentation) =
      Finsupp.single (PrimeFiniteCorrespondenceGeom.ofRepresented P) 1 := by
  rw [diagonalLeftIdentityDatum_toPresentation]
  exact FiniteCorrespondencePresentation.toGeom_single P

/-- Canonical pullback isomorphism witnessing left identity on represented
prime supports at the support-fiber-product level. -/
def diagonalLeftIdentityFiberIso {X Y : Geometry.SmSchemeOver k}
    (P : RepresentedPrimeSupport X Y) :
    compositionFiberProduct
        (SourceIrreducibleComponent.diagonalRepresentedPrimeSupport P.sourceComponent) P ≅
      P.support := by
  classical
  let diag := SourceIrreducibleComponent.diagonalRepresentedPrimeSupport P.sourceComponent
  let inv : P.support ⟶ compositionFiberProduct diag P :=
    pullback.lift P.toSourceComponent (𝟙 P.support) (by
      simp [diag, PrimeFiniteCorrespondenceSupport.toAmbientSource,
        SourceIrreducibleComponent.diagonalRepresentedPrimeSupport, Category.assoc])
  refine
    { hom := compositionFiberSnd diag P
      inv := inv
      hom_inv_id := ?_
      inv_hom_id := ?_ }
  · apply pullback.hom_ext
    · haveI : Mono P.sourceComponent.toAmbient := by
        haveI : IsOpenImmersion P.sourceComponent.toAmbient := by
          change IsOpenImmersion P.sourceComponent.immersion
          exact P.sourceComponent.isOpenImmersion
        infer_instance
      have hcond :
          compositionFiberFst diag P ≫ P.sourceComponent.toAmbient =
            compositionFiberSnd diag P ≫ P.toAmbientSource := by
        change compositionFiberFst diag P ≫ diag.toTargetScheme =
            compositionFiberSnd diag P ≫ P.toAmbientSource
        exact compositionFiber_condition diag P
      apply (cancel_mono P.sourceComponent.toAmbient).1
      calc
        compositionFiberSnd diag P ≫ inv ≫ compositionFiberFst diag P ≫ P.sourceComponent.toAmbient
            = compositionFiberSnd diag P ≫ P.toSourceComponent ≫ P.sourceComponent.toAmbient := by
                simp [inv, Category.assoc]
        _ = compositionFiberSnd diag P ≫ P.toAmbientSource := by
              simp [PrimeFiniteCorrespondenceSupport.toAmbientSource, Category.assoc]
        _ = compositionFiberFst diag P ≫ P.sourceComponent.toAmbient := by
              exact hcond.symm
    · simp [inv, Category.assoc]
  · simp [inv, Category.assoc]

/-- The scheme-theoretic-image factorization for `Δ_X ×_X P`, transported
across the canonical fiber-product isomorphism `Δ_X ×_X P ≅ P`. -/
def diagonalLeftIdentityImageFactorization {X Y : Geometry.SmSchemeOver k}
    (P : RepresentedPrimeSupport X Y) :
    SupportFiberProductImageFactorization
      (SourceIrreducibleComponent.diagonalRepresentedPrimeSupport P.sourceComponent) P where
  image := P.support
  toImage := compositionFiberSnd _ P
  imageToAmbientProduct := P.inclusion
  factorization := by
    apply pullback.hom_ext
    · haveI : Mono P.sourceComponent.toAmbient := by
        haveI : IsOpenImmersion P.sourceComponent.toAmbient := by
          change IsOpenImmersion P.sourceComponent.immersion
          exact P.sourceComponent.isOpenImmersion
        infer_instance
      have hfst := congrArg
        (fun f =>
          compositionFiberSnd
              (SourceIrreducibleComponent.diagonalRepresentedPrimeSupport P.sourceComponent) P ≫
            f ≫ P.sourceComponent.toAmbient)
        P.inclusion_fst
      have hcond :
          compositionFiberFst
              (SourceIrreducibleComponent.diagonalRepresentedPrimeSupport P.sourceComponent) P ≫
            P.sourceComponent.toAmbient =
              compositionFiberSnd
                (SourceIrreducibleComponent.diagonalRepresentedPrimeSupport P.sourceComponent) P ≫
              P.toAmbientSource := by
        change compositionFiberFst
            (SourceIrreducibleComponent.diagonalRepresentedPrimeSupport P.sourceComponent) P ≫
              (SourceIrreducibleComponent.diagonalRepresentedPrimeSupport P.sourceComponent).toTargetScheme =
            compositionFiberSnd
              (SourceIrreducibleComponent.diagonalRepresentedPrimeSupport P.sourceComponent) P ≫
              P.toAmbientSource
        exact compositionFiber_condition _ P
      apply (cancel_mono P.sourceComponent.toAmbient).1
      calc
        compositionFiberSnd
            (SourceIrreducibleComponent.diagonalRepresentedPrimeSupport P.sourceComponent) P ≫
            P.inclusion ≫ overBaseProduct.fst P.sourceComponent.carrier Y ≫
            P.sourceComponent.toAmbient
            = compositionFiberSnd
                (SourceIrreducibleComponent.diagonalRepresentedPrimeSupport P.sourceComponent) P ≫
                P.toSourceComponent ≫ P.sourceComponent.toAmbient := by
                  simpa [Category.assoc] using hfst
        _ = compositionFiberSnd
              (SourceIrreducibleComponent.diagonalRepresentedPrimeSupport P.sourceComponent) P ≫
              P.toAmbientSource := by
                simp [PrimeFiniteCorrespondenceSupport.toAmbientSource, Category.assoc]
        _ = compositionFiberFst
              (SourceIrreducibleComponent.diagonalRepresentedPrimeSupport P.sourceComponent) P ≫
              P.sourceComponent.toAmbient := by
                exact hcond.symm
        _ = compositionToAmbientProduct
              (SourceIrreducibleComponent.diagonalRepresentedPrimeSupport P.sourceComponent) P ≫
              overBaseProduct.fst P.sourceComponent.carrier Y ≫ P.sourceComponent.toAmbient := by
                simp [compositionToAmbientProduct_fst,
                  PrimeFiniteCorrespondenceSupport.toSourceComponent,
                  SourceIrreducibleComponent.diagonalRepresentedPrimeSupport, Category.assoc]
    · simpa [compositionToAmbientProduct_snd, Category.assoc] using
        congrArg
          (fun f =>
            compositionFiberSnd
                (SourceIrreducibleComponent.diagonalRepresentedPrimeSupport P.sourceComponent) P ≫ f)
          P.inclusion_snd
  imageClosedImmersion := P.isClosedImmersion

/-- The unique integral image component for `Δ_X ×_X P`, with multiplicity `1`,
transported back to the support fiber product using the canonical isomorphism
`Δ_X ×_X P ≅ P`. -/
def diagonalLeftIdentityImageComponent {X Y : Geometry.SmSchemeOver k}
    (P : RepresentedPrimeSupport X Y) :
    SupportFiberProductImageComponent (diagonalLeftIdentityImageFactorization P) where
  lengthCoeff := 1
  support := P.support
  isIntegral := P.isIntegral
  toImage := 𝟙 P.support
  toImageClosedImmersion := by infer_instance
  toCompositionFiberProduct := (diagonalLeftIdentityFiberIso P).inv
  toImage_factorization := by
    change (diagonalLeftIdentityFiberIso P).inv ≫ (diagonalLeftIdentityFiberIso P).hom = 𝟙 P.support
    exact (diagonalLeftIdentityFiberIso P).inv_hom_id
  finiteOverSourceComponent := P.finiteOverSourceComponent
  finite_toSourceComponent := P.finite_toSourceComponent
  surjective_toSourceComponent := P.surjective_toSourceComponent
  toTarget := P.toTarget
  inclusion := P.inclusion
  inclusion_factorization := by
    simp [diagonalLeftIdentityImageFactorization]
  inclusion_fst := P.inclusion_fst
  inclusion_snd := P.inclusion_snd
  isClosedImmersion := P.isClosedImmersion
  toCompositionFiberProduct_fst := by
    change (diagonalLeftIdentityFiberIso P).inv ≫
        compositionFiberFst
          (SourceIrreducibleComponent.diagonalRepresentedPrimeSupport P.sourceComponent) P ≫
        (SourceIrreducibleComponent.diagonalRepresentedPrimeSupport P.sourceComponent).toSourceComponent =
      P.finiteOverSourceComponent
    simp [diagonalLeftIdentityFiberIso, compositionFiberFst, compositionFiberProduct,
      PrimeFiniteCorrespondenceSupport.toSourceComponent,
      SourceIrreducibleComponent.diagonalRepresentedPrimeSupport, Category.assoc]
  toCompositionFiberProduct_snd := by
    change (diagonalLeftIdentityFiberIso P).inv ≫
        compositionFiberSnd
          (SourceIrreducibleComponent.diagonalRepresentedPrimeSupport P.sourceComponent) P ≫
        P.toTargetScheme = P.toTarget
    simp [diagonalLeftIdentityFiberIso, compositionFiberSnd, compositionFiberProduct]

/-- The one-component image decomposition realising `Δ_X ∘ P = P` at the
represented-prime level. -/
def diagonalLeftIdentityImageDecomposition {X Y : Geometry.SmSchemeOver k}
    (P : RepresentedPrimeSupport X Y) :
    SupportFiberProductImageDecomposition
      (SourceIrreducibleComponent.diagonalRepresentedPrimeSupport P.sourceComponent) P where
  imageData := diagonalLeftIdentityImageFactorization P
  index := PUnit
  fintype_index := inferInstance
  decidableEq_index := inferInstance
  component := fun _ => diagonalLeftIdentityImageComponent P

@[simp] theorem diagonalLeftIdentityImageDecomposition_toDatum
    {X Y : Geometry.SmSchemeOver k} (P : RepresentedPrimeSupport X Y) :
    RepresentedPrimeCompositionDatum.ofSupportFiberProductImageDecomposition
        (diagonalLeftIdentityImageDecomposition P) =
      diagonalLeftIdentityDatum P := by
  cases P
  rfl

@[simp] theorem diagonalLeftIdentityImageDecomposition_toPresentation
    {X Y : Geometry.SmSchemeOver k} (P : RepresentedPrimeSupport X Y) :
    (RepresentedPrimeCompositionDatum.ofSupportFiberProductImageDecomposition
        (diagonalLeftIdentityImageDecomposition P)).toPresentation =
      FiniteCorrespondencePresentation.ofPrimeSupport P := by
  rw [diagonalLeftIdentityImageDecomposition_toDatum,
    diagonalLeftIdentityDatum_toPresentation]

@[simp] theorem diagonalLeftIdentityImageDecomposition_toGeomSingle
    {X Y : Geometry.SmSchemeOver k} (P : RepresentedPrimeSupport X Y) :
    FiniteCorrespondencePresentation.toGeom
        ((RepresentedPrimeCompositionDatum.ofSupportFiberProductImageDecomposition
          (diagonalLeftIdentityImageDecomposition P)).toPresentation) =
      Finsupp.single (PrimeFiniteCorrespondenceGeom.ofRepresented P) 1 := by
  rw [diagonalLeftIdentityImageDecomposition_toDatum,
    diagonalLeftIdentityDatum_toGeomSingle]

/-- Canonical pullback isomorphism witnessing right identity on represented
prime supports once the target map of `P` is factored through a chosen source
component of the target scheme. -/
def diagonalRightIdentityFiberIso {X Y : Geometry.SmSchemeOver k}
    (P : RepresentedPrimeSupport X Y)
    (component : SourceIrreducibleComponent Y)
    (toComponent : P.support ⟶ component.carrier.scheme)
    (htoComponent : toComponent ≫ component.toAmbient = P.toTargetScheme) :
    compositionFiberProduct P (SourceIrreducibleComponent.diagonalRepresentedPrimeSupport component) ≅
      P.support := by
  classical
  let diag := SourceIrreducibleComponent.diagonalRepresentedPrimeSupport component
  let inv : P.support ⟶ compositionFiberProduct P diag :=
    pullback.lift (𝟙 P.support) toComponent (by
      simpa [diag, PrimeFiniteCorrespondenceSupport.toAmbientSource, Category.assoc] using
        htoComponent.symm)
  refine
    { hom := compositionFiberFst P diag
      inv := inv
      hom_inv_id := ?_
      inv_hom_id := ?_ }
  · apply pullback.hom_ext
    · simp [inv, compositionFiberFst, compositionFiberProduct]
    · haveI : Mono component.toAmbient := by
        haveI : IsOpenImmersion component.toAmbient := by
          change IsOpenImmersion component.immersion
          exact component.isOpenImmersion
        infer_instance
      have hcond :
          compositionFiberFst P diag ≫ P.toTargetScheme =
            compositionFiberSnd P diag ≫ component.toAmbient := by
        change compositionFiberFst P diag ≫ P.toTargetScheme =
            compositionFiberSnd P diag ≫ diag.toAmbientSource
        exact compositionFiber_condition P diag
      apply (cancel_mono component.toAmbient).1
      calc
        compositionFiberFst P diag ≫ inv ≫ compositionFiberSnd P diag ≫ component.toAmbient
            = compositionFiberFst P diag ≫ toComponent ≫ component.toAmbient := by
                simp [inv, Category.assoc]
        _ = compositionFiberFst P diag ≫ P.toTargetScheme := by
              simpa [Category.assoc] using
                congrArg (fun f => compositionFiberFst P diag ≫ f) htoComponent
        _ = compositionFiberSnd P diag ≫ component.toAmbient := hcond
  · simp [inv, Category.assoc]

/-- The scheme-theoretic-image factorization for `P ×_Y Δ_component`,
transported across the canonical fiber-product isomorphism `P ×_Y Δ ≅ P`. -/
def diagonalRightIdentityImageFactorization {X Y : Geometry.SmSchemeOver k}
    (P : RepresentedPrimeSupport X Y)
    (component : SourceIrreducibleComponent Y)
    (toComponent : P.support ⟶ component.carrier.scheme)
  (_htoComponent : toComponent ≫ component.toAmbient = P.toTargetScheme) :
    SupportFiberProductImageFactorization P
      (SourceIrreducibleComponent.diagonalRepresentedPrimeSupport component) where
  image := P.support
  toImage := compositionFiberFst P _
  imageToAmbientProduct := P.inclusion
  factorization := by
    let diag := SourceIrreducibleComponent.diagonalRepresentedPrimeSupport component
    apply pullback.hom_ext
    · simpa [compositionToAmbientProduct_fst, Category.assoc] using
        congrArg (fun f => compositionFiberFst P diag ≫ f) P.inclusion_fst
    · have hcond :
          compositionFiberFst P diag ≫ P.toTargetScheme =
            compositionFiberSnd P diag ≫ component.toAmbient := by
        change compositionFiberFst P diag ≫ P.toTargetScheme =
            compositionFiberSnd P diag ≫ diag.toAmbientSource
        exact compositionFiber_condition P diag
      calc
        compositionFiberFst P diag ≫ P.inclusion ≫ overBaseProduct.snd P.sourceComponent.carrier Y
            = compositionFiberFst P diag ≫ P.toTargetScheme := by
                simpa [Category.assoc] using
                  congrArg (fun f => compositionFiberFst P diag ≫ f) P.inclusion_snd
        _ = compositionFiberSnd P diag ≫ component.toAmbient := hcond
        _ = compositionFiberSnd P diag ≫ diag.toTargetScheme := by
              simp [diag, PrimeFiniteCorrespondenceSupport.toTargetScheme,
                SourceIrreducibleComponent.diagonalRepresentedPrimeSupport]
        _ = compositionToAmbientProduct P diag ≫ overBaseProduct.snd P.sourceComponent.carrier Y := by
              simp [compositionToAmbientProduct_snd,
                PrimeFiniteCorrespondenceSupport.toTargetScheme,
                SourceIrreducibleComponent.diagonalRepresentedPrimeSupport, Category.assoc]
  imageClosedImmersion := P.isClosedImmersion

/-- The unique integral image component for `P ×_Y Δ_component`, with
multiplicity `1`, transported back to the support fiber product using the
canonical isomorphism `P ×_Y Δ ≅ P`. -/
def diagonalRightIdentityImageComponent {X Y : Geometry.SmSchemeOver k}
    (P : RepresentedPrimeSupport X Y)
    (component : SourceIrreducibleComponent Y)
    (toComponent : P.support ⟶ component.carrier.scheme)
    (htoComponent : toComponent ≫ component.toAmbient = P.toTargetScheme) :
    SupportFiberProductImageComponent
      (diagonalRightIdentityImageFactorization P component toComponent htoComponent) where
  lengthCoeff := 1
  support := P.support
  isIntegral := P.isIntegral
  toImage := 𝟙 P.support
  toImageClosedImmersion := by infer_instance
  toCompositionFiberProduct :=
    (diagonalRightIdentityFiberIso P component toComponent htoComponent).inv
  toImage_factorization := by
    change (diagonalRightIdentityFiberIso P component toComponent htoComponent).inv ≫
        (diagonalRightIdentityFiberIso P component toComponent htoComponent).hom = 𝟙 P.support
    exact (diagonalRightIdentityFiberIso P component toComponent htoComponent).inv_hom_id
  finiteOverSourceComponent := P.finiteOverSourceComponent
  finite_toSourceComponent := P.finite_toSourceComponent
  surjective_toSourceComponent := P.surjective_toSourceComponent
  toTarget := P.toTarget
  inclusion := P.inclusion
  inclusion_factorization := by
    simp [diagonalRightIdentityImageFactorization]
  inclusion_fst := P.inclusion_fst
  inclusion_snd := P.inclusion_snd
  isClosedImmersion := P.isClosedImmersion
  toCompositionFiberProduct_fst := by
    simp [diagonalRightIdentityFiberIso, compositionFiberFst, compositionFiberProduct]
  toCompositionFiberProduct_snd := by
    let diag := SourceIrreducibleComponent.diagonalRepresentedPrimeSupport component
    calc
      (diagonalRightIdentityFiberIso P component toComponent htoComponent).inv ≫
          compositionFiberSnd P diag ≫ diag.toTargetScheme
          = toComponent ≫ component.toAmbient := by
              simp [diagonalRightIdentityFiberIso, diag, compositionFiberSnd,
                compositionFiberProduct, PrimeFiniteCorrespondenceSupport.toTargetScheme,
                SourceIrreducibleComponent.diagonalRepresentedPrimeSupport, Category.assoc]
      _ = P.toTargetScheme := htoComponent
      _ = P.toTarget := rfl

/-- The one-component image decomposition realising `P ∘ Δ_component = P` once
the target map of `P` is factored through the chosen component. -/
def diagonalRightIdentityImageDecomposition {X Y : Geometry.SmSchemeOver k}
    (P : RepresentedPrimeSupport X Y)
    (component : SourceIrreducibleComponent Y)
    (toComponent : P.support ⟶ component.carrier.scheme)
    (htoComponent : toComponent ≫ component.toAmbient = P.toTargetScheme) :
    SupportFiberProductImageDecomposition P
      (SourceIrreducibleComponent.diagonalRepresentedPrimeSupport component) where
  imageData := diagonalRightIdentityImageFactorization P component toComponent htoComponent
  index := PUnit
  fintype_index := inferInstance
  decidableEq_index := inferInstance
  component := fun _ => diagonalRightIdentityImageComponent P component toComponent htoComponent

@[simp] theorem diagonalRightIdentityImageDecomposition_toPresentation
    {X Y : Geometry.SmSchemeOver k} (P : RepresentedPrimeSupport X Y)
    (component : SourceIrreducibleComponent Y)
    (toComponent : P.support ⟶ component.carrier.scheme)
    (htoComponent : toComponent ≫ component.toAmbient = P.toTargetScheme) :
    (RepresentedPrimeCompositionDatum.ofSupportFiberProductImageDecomposition
        (diagonalRightIdentityImageDecomposition P component toComponent htoComponent)).toPresentation =
      FiniteCorrespondencePresentation.ofPrimeSupport P := by
  cases P
  simp [diagonalRightIdentityImageDecomposition,
    diagonalRightIdentityImageComponent,
    RepresentedPrimeCompositionDatum.ofSupportFiberProductImageDecomposition,
    SupportFiberProductImageDecomposition.toRepresentedPrimeCompositionDatum,
    RepresentedPrimeCompositionDatum.toPresentation,
    FiniteCorrespondencePresentation.ofPrimeSupport,
    FiniteCorrespondencePresentation.ofWeightedPrimeSupport,
    SupportFiberProductImageComponent.toRepresentedPrimeCompositionPiece,
    RepresentedPrimeCompositionPiece.toWeightedPrimeFiniteCorrespondenceSupport,
    RepresentedPrimeCompositionPiece.toRepresentedPrimeSupport]

@[simp] theorem diagonalRightIdentityImageDecomposition_toGeomSingle
    {X Y : Geometry.SmSchemeOver k} (P : RepresentedPrimeSupport X Y)
    (component : SourceIrreducibleComponent Y)
    (toComponent : P.support ⟶ component.carrier.scheme)
    (htoComponent : toComponent ≫ component.toAmbient = P.toTargetScheme) :
    FiniteCorrespondencePresentation.toGeom
        ((RepresentedPrimeCompositionDatum.ofSupportFiberProductImageDecomposition
          (diagonalRightIdentityImageDecomposition P component toComponent htoComponent)).toPresentation) =
      Finsupp.single (PrimeFiniteCorrespondenceGeom.ofRepresented P) 1 := by
  rw [diagonalRightIdentityImageDecomposition_toPresentation]
  exact FiniteCorrespondencePresentation.toGeom_single P

end RepresentedPrimeCompositionDatum

end

end Boundary
