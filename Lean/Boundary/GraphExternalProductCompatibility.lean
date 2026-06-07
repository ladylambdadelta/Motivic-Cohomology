import Boundary.GraphExternalProductSingletonDecomposition
import Boundary.ExternalProduct
import Boundary.GraphProductSupportIso
import Boundary.ComponentGeometry
import Boundary.NisnevichPullbackTransfer
import Geometry.Correspondences.Graph

universe u

open AlgebraicGeometry CategoryTheory Limits

namespace Boundary

noncomputable section

variable {k : Type u} [Field k] [PerfectField k]

/-- After transporting the raw support of `graph(f) ⊠ Δ` to the canonical
product source component, its target map has the first product projection
expected for the graph of `f × id`. -/
theorem graphExternalProduct_id_right_projection_fst
    {X Y Z : Geometry.SmSchemeOver k}
    (C : ProductStableSourceComponent X)
    (D : SourceIrreducibleComponent Z)
    (f : SmOverHom X Y) :
    (graphExternalProductSupportIso_id_right C D f).inv ≫
        PrimeFiniteCorrespondenceSupport.externalProductToProductTarget
          (Geometry.ordinaryMorphismGraphPrimeSupport C.component f)
          (SourceIrreducibleComponent.diagonalRepresentedPrimeSupport D) ≫
          overBaseProduct.fst Y Z =
      (productSourceIrreducibleComponent C D).toAmbient ≫
        overBaseProduct.fst X Z ≫ f.hom := by
  calc
    (graphExternalProductSupportIso_id_right C D f).inv ≫
        PrimeFiniteCorrespondenceSupport.externalProductToProductTarget
          (Geometry.ordinaryMorphismGraphPrimeSupport C.component f)
          (SourceIrreducibleComponent.diagonalRepresentedPrimeSupport D) ≫
          overBaseProduct.fst Y Z =
      (graphExternalProductSupportIso_id_right C D f).inv ≫
        pullback.fst
          ((Geometry.ordinaryMorphismGraphPrimeSupport C.component f).toAmbientSource ≫ X.structMap)
          ((SourceIrreducibleComponent.diagonalRepresentedPrimeSupport D).toAmbientSource ≫
            Z.structMap) ≫ C.component.toAmbient ≫ f.hom := by
        simp [PrimeFiniteCorrespondenceSupport.externalProductToProductTarget,
          Geometry.ordinaryMorphismGraphPrimeSupport_toTargetScheme, Category.assoc]
    _ = overBaseProduct.fst C.component.carrier D.carrier ≫ C.component.toAmbient ≫
          f.hom := by
        change
          ((graphExternalProductSupportIso_id_right C D f).inv ≫
              pullback.fst
                ((Geometry.ordinaryMorphismGraphPrimeSupport C.component f).toAmbientSource ≫
                  X.structMap)
                ((SourceIrreducibleComponent.diagonalRepresentedPrimeSupport D).toAmbientSource ≫
                  Z.structMap)) ≫ C.component.toAmbient ≫ f.hom =
            overBaseProduct.fst C.component.carrier D.carrier ≫ C.component.toAmbient ≫ f.hom
        exact congrArg (fun h => h ≫ C.component.toAmbient ≫ f.hom)
          (graphExternalProductSupportIso_id_right_inv_fst C D f)
    _ = (productSourceIrreducibleComponent C D).toAmbient ≫
          overBaseProduct.fst X Z ≫ f.hom := by
        change
          (overBaseProduct.fst C.component.carrier D.carrier ≫ C.component.toAmbient) ≫ f.hom =
            ((productSourceIrreducibleComponent C D).toAmbient ≫
              overBaseProduct.fst X Z) ≫ f.hom
        exact congrArg (fun h => h ≫ f.hom)
          (productSourceIrreducibleComponent_fst_image C D).symm

/-- After transporting the raw support of `graph(f) ⊠ Δ`, its target map has
the second product projection expected for the graph of `f × id`. -/
theorem graphExternalProduct_id_right_projection_snd
    {X Y Z : Geometry.SmSchemeOver k}
    (C : ProductStableSourceComponent X)
    (D : SourceIrreducibleComponent Z)
    (f : SmOverHom X Y) :
    (graphExternalProductSupportIso_id_right C D f).inv ≫
        PrimeFiniteCorrespondenceSupport.externalProductToProductTarget
          (Geometry.ordinaryMorphismGraphPrimeSupport C.component f)
          (SourceIrreducibleComponent.diagonalRepresentedPrimeSupport D) ≫
          overBaseProduct.snd Y Z =
      (productSourceIrreducibleComponent C D).toAmbient ≫
        overBaseProduct.snd X Z := by
  calc
    (graphExternalProductSupportIso_id_right C D f).inv ≫
        PrimeFiniteCorrespondenceSupport.externalProductToProductTarget
          (Geometry.ordinaryMorphismGraphPrimeSupport C.component f)
          (SourceIrreducibleComponent.diagonalRepresentedPrimeSupport D) ≫
          overBaseProduct.snd Y Z =
      (graphExternalProductSupportIso_id_right C D f).inv ≫
        pullback.snd
          ((Geometry.ordinaryMorphismGraphPrimeSupport C.component f).toAmbientSource ≫ X.structMap)
          ((SourceIrreducibleComponent.diagonalRepresentedPrimeSupport D).toAmbientSource ≫
            Z.structMap) ≫
          (SourceIrreducibleComponent.diagonalRepresentedPrimeSupport D).toTargetScheme := by
        simp [PrimeFiniteCorrespondenceSupport.externalProductToProductTarget, Category.assoc]
    _ = overBaseProduct.snd C.component.carrier D.carrier ≫
          (SourceIrreducibleComponent.diagonalRepresentedPrimeSupport D).toTargetScheme := by
        change
          ((graphExternalProductSupportIso_id_right C D f).inv ≫
              pullback.snd
                ((Geometry.ordinaryMorphismGraphPrimeSupport C.component f).toAmbientSource ≫
                  X.structMap)
                ((SourceIrreducibleComponent.diagonalRepresentedPrimeSupport D).toAmbientSource ≫
                  Z.structMap)) ≫
                (SourceIrreducibleComponent.diagonalRepresentedPrimeSupport D).toTargetScheme =
            overBaseProduct.snd C.component.carrier D.carrier ≫
              (SourceIrreducibleComponent.diagonalRepresentedPrimeSupport D).toTargetScheme
        exact congrArg
          (fun h => h ≫
            (SourceIrreducibleComponent.diagonalRepresentedPrimeSupport D).toTargetScheme)
          (graphExternalProductSupportIso_id_right_inv_snd C D f)
    _ = overBaseProduct.snd C.component.carrier D.carrier ≫ D.toAmbient := by
        simp [PrimeFiniteCorrespondenceSupport.toTargetScheme,
          SourceIrreducibleComponent.diagonalRepresentedPrimeSupport,
          SourceImageSubscheme.diagonalRepresentedPrimeSupport]
    _ = (productSourceIrreducibleComponent C D).toAmbient ≫
          overBaseProduct.snd X Z := by
        rw [productSourceIrreducibleComponent_snd_image]

/-- Transported external-product target map for `graph(f) ⊠ Δ`. -/
theorem graphExternalProductToProductTarget_id_right
    {X Y Z : Geometry.SmSchemeOver k}
    (C : ProductStableSourceComponent X)
    (D : SourceIrreducibleComponent Z)
    (f : SmOverHom X Y) :
    (graphExternalProductSupportIso_id_right C D f).inv ≫
      PrimeFiniteCorrespondenceSupport.externalProductToProductTarget
        (Geometry.ordinaryMorphismGraphPrimeSupport C.component f)
        (SourceIrreducibleComponent.diagonalRepresentedPrimeSupport D) =
      (productSourceIrreducibleComponent C D).toAmbient ≫
        (overBaseProductMap f (𝟙 Z)).hom := by
  apply pullback.hom_ext
  · calc
      ((graphExternalProductSupportIso_id_right C D f).inv ≫
          PrimeFiniteCorrespondenceSupport.externalProductToProductTarget
            (Geometry.ordinaryMorphismGraphPrimeSupport C.component f)
            (SourceIrreducibleComponent.diagonalRepresentedPrimeSupport D)) ≫
            pullback.fst Y.structMap Z.structMap =
        (graphExternalProductSupportIso_id_right C D f).inv ≫
          PrimeFiniteCorrespondenceSupport.externalProductToProductTarget
            (Geometry.ordinaryMorphismGraphPrimeSupport C.component f)
            (SourceIrreducibleComponent.diagonalRepresentedPrimeSupport D) ≫
            overBaseProduct.fst Y Z := by
          rfl
      _ = (productSourceIrreducibleComponent C D).toAmbient ≫
            overBaseProduct.fst X Z ≫ f.hom := by
          exact graphExternalProduct_id_right_projection_fst C D f
      _ = ((productSourceIrreducibleComponent C D).toAmbient ≫
            (overBaseProductMap f (𝟙 Z)).hom) ≫
            pullback.fst Y.structMap Z.structMap := by
          simp [overBaseProductMap, Category.assoc]
  · calc
      ((graphExternalProductSupportIso_id_right C D f).inv ≫
          PrimeFiniteCorrespondenceSupport.externalProductToProductTarget
            (Geometry.ordinaryMorphismGraphPrimeSupport C.component f)
            (SourceIrreducibleComponent.diagonalRepresentedPrimeSupport D)) ≫
            pullback.snd Y.structMap Z.structMap =
        (graphExternalProductSupportIso_id_right C D f).inv ≫
          PrimeFiniteCorrespondenceSupport.externalProductToProductTarget
            (Geometry.ordinaryMorphismGraphPrimeSupport C.component f)
            (SourceIrreducibleComponent.diagonalRepresentedPrimeSupport D) ≫
            overBaseProduct.snd Y Z := by
          rfl
      _ = (productSourceIrreducibleComponent C D).toAmbient ≫
            overBaseProduct.snd X Z := by
          exact graphExternalProduct_id_right_projection_snd C D f
      _ = ((productSourceIrreducibleComponent C D).toAmbient ≫
            (overBaseProductMap f (𝟙 Z)).hom) ≫
            pullback.snd Y.structMap Z.structMap := by
          calc
            (productSourceIrreducibleComponent C D).toAmbient ≫
                overBaseProduct.snd X Z =
              overBaseProduct.snd C.component.carrier D.carrier ≫ D.toAmbient := by
                rw [productSourceIrreducibleComponent_snd_image]
            _ = ((productSourceIrreducibleComponent C D).toAmbient ≫
                  (overBaseProductMap f (𝟙 Z)).hom) ≫
                  pullback.snd Y.structMap Z.structMap := by
                rw [overBaseProductMap, overBaseProduct.snd, Category.assoc]

/-- External product of a graph with a diagonal, represented on the canonical
product source component. -/
abbrev graphExternalProductPrimeSupport_id_right
    {X Y Z : Geometry.SmSchemeOver k}
    (C : ProductStableSourceComponent X)
    (D : SourceIrreducibleComponent Z)
    (f : SmOverHom X Y) :
    RepresentedPrimeSupport
      (overBaseProductObject X Z) (overBaseProductObject Y Z) :=
  Geometry.ordinaryMorphismGraphPrimeSupport
    (productSourceIrreducibleComponent C D)
    (overBaseProductMap f (𝟙 Z))

/-- Prime-support compatibility for graphs under product with the identity on
the right. -/
theorem ordinaryMorphismGraphPrimeSupport_overBaseProductMap_id_right_equiv
    {X Y Z : Geometry.SmSchemeOver k}
    (C : ProductStableSourceComponent X)
    (D : SourceIrreducibleComponent Z)
    (f : SmOverHom X Y) :
    PrimeFiniteCorrespondenceSupport.PrimeSupportEquivalent
      (Geometry.ordinaryMorphismGraphPrimeSupport
        (productSourceIrreducibleComponent C D)
        (overBaseProductMap f (𝟙 Z)))
      (graphExternalProductPrimeSupport_id_right C D f) :=
  PrimeFiniteCorrespondenceSupport.supportIsoOverProduct_refl _

/-- Singleton graph correspondence for `f × id` agrees with the represented
external-product prime support on the product source component. -/
theorem graphCorrespondence_overBaseProductMap_id_right_eq_externalProduct
    {X Y Z : Geometry.SmSchemeOver k}
    (C : ProductStableSourceComponent X)
    (D : SourceIrreducibleComponent Z)
    (f : SmOverHom X Y) :
    Geometry.ordinaryMorphismGraph_componentCorrespondence
      (productSourceIrreducibleComponent C D)
      (overBaseProductMap f (𝟙 Z)) =
      FiniteCorrespondence.ofPrimeSupport
        (graphExternalProductPrimeSupport_id_right C D f) := by
  rfl

/-- Algebraic singleton form: the represented external-product graph support
is the componentwise graph correspondence for `f × id`. -/
theorem graphExternalProduct_id_right_eq
    {X Y Z : Geometry.SmSchemeOver k}
    (C : ProductStableSourceComponent X)
    (D : SourceIrreducibleComponent Z)
    (f : SmOverHom X Y) :
      FiniteCorrespondence.ofPrimeSupport
        (graphExternalProductPrimeSupport_id_right C D f) =
      Geometry.ordinaryMorphismGraph_componentCorrespondence
        (productSourceIrreducibleComponent C D)
        (overBaseProductMap f (𝟙 Z)) := by
  exact (graphCorrespondence_overBaseProductMap_id_right_eq_externalProduct C D f).symm

theorem graphExternalProduct_id_right_singletonDecomposition_toFiniteCorrespondence
    {X Y Z : Geometry.SmSchemeOver k}
    (C : ProductStableSourceComponent X)
    (D : SourceIrreducibleComponent Z)
    (f : SmOverHom X Y) :
    (GraphExternalProductSingleton.graphExternalProduct_id_right_imageDecomposition_singleton
        C D f).toFiniteCorrespondence =
      FiniteCorrespondence.ofPrimeSupport
        ((GraphExternalProductSingleton.graphExternalProduct_id_right_imageDecomposition_singleton
          C D f).toRepresentedPrimeSupport (ULift.up ())) := by
  classical
  simp [
    ProductFiniteCorrespondenceImageDecomposition.toFiniteCorrespondence,
    ProductFiniteCorrespondenceImageDecomposition.toPresentation,
    ProductFiniteCorrespondenceImageDecomposition.toWeightedPrimeFiniteCorrespondenceSupport,
    ProductFiniteCorrespondenceImageDecomposition.toRepresentedPrimeSupport,
    GraphExternalProductSingleton.graphExternalProduct_id_right_imageDecomposition_singleton,
    GraphExternalProductSingleton.singletonRawSupportDecomposition,
    FiniteCorrespondencePresentation.ofWeightedPrimeSupport,
    FiniteCorrespondencePresentation.toGeom,
    FiniteCorrespondence.ofPrimeSupport
  ]

/-- After transporting the raw support of `Δ ⊠ graph(g)` to the canonical
product source component, its target map has the first product projection
expected for the graph of `id × g`. -/
theorem graphExternalProduct_id_left_projection_fst
    {X Y Z : Geometry.SmSchemeOver k}
    (C : ProductStableSourceComponent X)
    (D : SourceIrreducibleComponent Y)
    (g : SmOverHom Y Z) :
    (graphExternalProductSupportIso_id_left C D g).inv ≫
        PrimeFiniteCorrespondenceSupport.externalProductToProductTarget
          (SourceIrreducibleComponent.diagonalRepresentedPrimeSupport C.component)
          (Geometry.ordinaryMorphismGraphPrimeSupport D g) ≫
          overBaseProduct.fst X Z =
      (productSourceIrreducibleComponent C D).toAmbient ≫
        overBaseProduct.fst X Y := by
  calc
    (graphExternalProductSupportIso_id_left C D g).inv ≫
        PrimeFiniteCorrespondenceSupport.externalProductToProductTarget
          (SourceIrreducibleComponent.diagonalRepresentedPrimeSupport C.component)
          (Geometry.ordinaryMorphismGraphPrimeSupport D g) ≫
          overBaseProduct.fst X Z =
      (graphExternalProductSupportIso_id_left C D g).inv ≫
        pullback.fst
          ((SourceIrreducibleComponent.diagonalRepresentedPrimeSupport C.component).toAmbientSource ≫
            X.structMap)
          ((Geometry.ordinaryMorphismGraphPrimeSupport D g).toAmbientSource ≫ Y.structMap) ≫
          (SourceIrreducibleComponent.diagonalRepresentedPrimeSupport C.component).toTargetScheme := by
        simp [PrimeFiniteCorrespondenceSupport.externalProductToProductTarget, Category.assoc]
    _ = overBaseProduct.fst C.component.carrier D.carrier ≫
          (SourceIrreducibleComponent.diagonalRepresentedPrimeSupport C.component).toTargetScheme := by
        change
          ((graphExternalProductSupportIso_id_left C D g).inv ≫
              pullback.fst
                ((SourceIrreducibleComponent.diagonalRepresentedPrimeSupport C.component).toAmbientSource ≫
                  X.structMap)
                ((Geometry.ordinaryMorphismGraphPrimeSupport D g).toAmbientSource ≫
                  Y.structMap)) ≫
                (SourceIrreducibleComponent.diagonalRepresentedPrimeSupport C.component).toTargetScheme =
            overBaseProduct.fst C.component.carrier D.carrier ≫
              (SourceIrreducibleComponent.diagonalRepresentedPrimeSupport C.component).toTargetScheme
        exact congrArg
          (fun h => h ≫
            (SourceIrreducibleComponent.diagonalRepresentedPrimeSupport C.component).toTargetScheme)
          (graphExternalProductSupportIso_id_left_inv_fst C D g)
    _ = overBaseProduct.fst C.component.carrier D.carrier ≫ C.component.toAmbient := by
        simp [PrimeFiniteCorrespondenceSupport.toTargetScheme,
          SourceIrreducibleComponent.diagonalRepresentedPrimeSupport,
          SourceImageSubscheme.diagonalRepresentedPrimeSupport]
    _ = (productSourceIrreducibleComponent C D).toAmbient ≫
          overBaseProduct.fst X Y := by
        rw [productSourceIrreducibleComponent_fst_image]

/-- After transporting the raw support of `Δ ⊠ graph(g)`, its target map has
the second product projection expected for the graph of `id × g`. -/
theorem graphExternalProduct_id_left_projection_snd
    {X Y Z : Geometry.SmSchemeOver k}
    (C : ProductStableSourceComponent X)
    (D : SourceIrreducibleComponent Y)
    (g : SmOverHom Y Z) :
    (graphExternalProductSupportIso_id_left C D g).inv ≫
        PrimeFiniteCorrespondenceSupport.externalProductToProductTarget
          (SourceIrreducibleComponent.diagonalRepresentedPrimeSupport C.component)
          (Geometry.ordinaryMorphismGraphPrimeSupport D g) ≫
          overBaseProduct.snd X Z =
      (productSourceIrreducibleComponent C D).toAmbient ≫
        overBaseProduct.snd X Y ≫ g.hom := by
  calc
    (graphExternalProductSupportIso_id_left C D g).inv ≫
        PrimeFiniteCorrespondenceSupport.externalProductToProductTarget
          (SourceIrreducibleComponent.diagonalRepresentedPrimeSupport C.component)
          (Geometry.ordinaryMorphismGraphPrimeSupport D g) ≫
          overBaseProduct.snd X Z =
      (graphExternalProductSupportIso_id_left C D g).inv ≫
        pullback.snd
          ((SourceIrreducibleComponent.diagonalRepresentedPrimeSupport C.component).toAmbientSource ≫
            X.structMap)
          ((Geometry.ordinaryMorphismGraphPrimeSupport D g).toAmbientSource ≫ Y.structMap) ≫
          D.toAmbient ≫ g.hom := by
        simp [PrimeFiniteCorrespondenceSupport.externalProductToProductTarget,
          Geometry.ordinaryMorphismGraphPrimeSupport_toTargetScheme, Category.assoc]
    _ = overBaseProduct.snd C.component.carrier D.carrier ≫ D.toAmbient ≫
          g.hom := by
        change
          ((graphExternalProductSupportIso_id_left C D g).inv ≫
              pullback.snd
                ((SourceIrreducibleComponent.diagonalRepresentedPrimeSupport C.component).toAmbientSource ≫
                  X.structMap)
                ((Geometry.ordinaryMorphismGraphPrimeSupport D g).toAmbientSource ≫
                  Y.structMap)) ≫ D.toAmbient ≫ g.hom =
            overBaseProduct.snd C.component.carrier D.carrier ≫ D.toAmbient ≫ g.hom
        exact congrArg (fun h => h ≫ D.toAmbient ≫ g.hom)
          (graphExternalProductSupportIso_id_left_inv_snd C D g)
    _ = (productSourceIrreducibleComponent C D).toAmbient ≫
          overBaseProduct.snd X Y ≫ g.hom := by
        change
          (overBaseProduct.snd C.component.carrier D.carrier ≫ D.toAmbient) ≫ g.hom =
            ((productSourceIrreducibleComponent C D).toAmbient ≫
              overBaseProduct.snd X Y) ≫ g.hom
        exact congrArg (fun h => h ≫ g.hom)
          (productSourceIrreducibleComponent_snd_image C D).symm

/-- Transported external-product target map for `Δ ⊠ graph(g)`. -/
theorem graphExternalProductToProductTarget_id_left
    {X Y Z : Geometry.SmSchemeOver k}
    (C : ProductStableSourceComponent X)
    (D : SourceIrreducibleComponent Y)
    (g : SmOverHom Y Z) :
    (graphExternalProductSupportIso_id_left C D g).inv ≫
      PrimeFiniteCorrespondenceSupport.externalProductToProductTarget
        (SourceIrreducibleComponent.diagonalRepresentedPrimeSupport C.component)
        (Geometry.ordinaryMorphismGraphPrimeSupport D g) =
      (productSourceIrreducibleComponent C D).toAmbient ≫
        (overBaseProductMap (𝟙 X) g).hom := by
  apply pullback.hom_ext
  · calc
      ((graphExternalProductSupportIso_id_left C D g).inv ≫
          PrimeFiniteCorrespondenceSupport.externalProductToProductTarget
            (SourceIrreducibleComponent.diagonalRepresentedPrimeSupport C.component)
            (Geometry.ordinaryMorphismGraphPrimeSupport D g)) ≫
            pullback.fst X.structMap Z.structMap =
        (graphExternalProductSupportIso_id_left C D g).inv ≫
          PrimeFiniteCorrespondenceSupport.externalProductToProductTarget
            (SourceIrreducibleComponent.diagonalRepresentedPrimeSupport C.component)
            (Geometry.ordinaryMorphismGraphPrimeSupport D g) ≫
            overBaseProduct.fst X Z := by
          rfl
      _ = (productSourceIrreducibleComponent C D).toAmbient ≫
            overBaseProduct.fst X Y := by
          exact graphExternalProduct_id_left_projection_fst C D g
      _ = ((productSourceIrreducibleComponent C D).toAmbient ≫
            (overBaseProductMap (𝟙 X) g).hom) ≫
            pullback.fst X.structMap Z.structMap := by
          calc
            (productSourceIrreducibleComponent C D).toAmbient ≫
                overBaseProduct.fst X Y =
              overBaseProduct.fst C.component.carrier D.carrier ≫ C.component.toAmbient := by
                rw [productSourceIrreducibleComponent_fst_image]
            _ = ((productSourceIrreducibleComponent C D).toAmbient ≫
                  (overBaseProductMap (𝟙 X) g).hom) ≫
                  pullback.fst X.structMap Z.structMap := by
                rw [overBaseProductMap, overBaseProduct.fst, Category.assoc]
  · calc
      ((graphExternalProductSupportIso_id_left C D g).inv ≫
          PrimeFiniteCorrespondenceSupport.externalProductToProductTarget
            (SourceIrreducibleComponent.diagonalRepresentedPrimeSupport C.component)
            (Geometry.ordinaryMorphismGraphPrimeSupport D g)) ≫
            pullback.snd X.structMap Z.structMap =
        (graphExternalProductSupportIso_id_left C D g).inv ≫
          PrimeFiniteCorrespondenceSupport.externalProductToProductTarget
            (SourceIrreducibleComponent.diagonalRepresentedPrimeSupport C.component)
            (Geometry.ordinaryMorphismGraphPrimeSupport D g) ≫
            overBaseProduct.snd X Z := by
          rfl
      _ = (productSourceIrreducibleComponent C D).toAmbient ≫
            overBaseProduct.snd X Y ≫ g.hom := by
          exact graphExternalProduct_id_left_projection_snd C D g
      _ = ((productSourceIrreducibleComponent C D).toAmbient ≫
            (overBaseProductMap (𝟙 X) g).hom) ≫
            pullback.snd X.structMap Z.structMap := by
          simp [overBaseProductMap, Category.assoc]

/-- External product of a diagonal with a graph, represented on the canonical
product source component. -/
abbrev graphExternalProductPrimeSupport_id_left
    {X Y Z : Geometry.SmSchemeOver k}
    (C : ProductStableSourceComponent X)
    (D : SourceIrreducibleComponent Y)
    (g : SmOverHom Y Z) :
    RepresentedPrimeSupport
      (overBaseProductObject X Y) (overBaseProductObject X Z) :=
  Geometry.ordinaryMorphismGraphPrimeSupport
    (productSourceIrreducibleComponent C D)
    (overBaseProductMap (𝟙 X) g)

/-- Prime-support compatibility for graphs under product with the identity on
the left. -/
theorem ordinaryMorphismGraphPrimeSupport_overBaseProductMap_id_left_equiv
    {X Y Z : Geometry.SmSchemeOver k}
    (C : ProductStableSourceComponent X)
    (D : SourceIrreducibleComponent Y)
    (g : SmOverHom Y Z) :
    PrimeFiniteCorrespondenceSupport.PrimeSupportEquivalent
      (Geometry.ordinaryMorphismGraphPrimeSupport
        (productSourceIrreducibleComponent C D)
        (overBaseProductMap (𝟙 X) g))
      (graphExternalProductPrimeSupport_id_left C D g) :=
  PrimeFiniteCorrespondenceSupport.supportIsoOverProduct_refl _

/-- Singleton graph correspondence for `id × g` agrees with the represented
external-product prime support on the product source component. -/
theorem graphCorrespondence_overBaseProductMap_id_left_eq_externalProduct
    {X Y Z : Geometry.SmSchemeOver k}
    (C : ProductStableSourceComponent X)
    (D : SourceIrreducibleComponent Y)
    (g : SmOverHom Y Z) :
    Geometry.ordinaryMorphismGraph_componentCorrespondence
      (productSourceIrreducibleComponent C D)
      (overBaseProductMap (𝟙 X) g) =
      FiniteCorrespondence.ofPrimeSupport
        (graphExternalProductPrimeSupport_id_left C D g) := by
  rfl

/-- Algebraic singleton form: the represented external-product graph support
is the componentwise graph correspondence for `id × g`. -/
theorem graphExternalProduct_id_left_eq
    {X Y Z : Geometry.SmSchemeOver k}
    (C : ProductStableSourceComponent X)
    (D : SourceIrreducibleComponent Y)
    (g : SmOverHom Y Z) :
    FiniteCorrespondence.ofPrimeSupport
        (graphExternalProductPrimeSupport_id_left C D g) =
      Geometry.ordinaryMorphismGraph_componentCorrespondence
        (productSourceIrreducibleComponent C D)
        (overBaseProductMap (𝟙 X) g) := by
  exact (graphCorrespondence_overBaseProductMap_id_left_eq_externalProduct C D g).symm

/-- The product-source component indexed by listed source components is
injective.  This is the public noncollision theorem used when rewriting
`Finset.sum_image` over product components. -/
theorem productSourceIrreducibleComponent_pair_injective
    {X Y : Geometry.SmSchemeOver k}
    (DX : FiniteIrreducibleComponentDecomposition X)
    (DY : FiniteIrreducibleComponentDecomposition Y)
    (stableDX :
      (listed : { listed : SourceIrreducibleComponent X // listed ∈ DX.components }) →
        ProductStableSourceComponent X)
    (hstableDX : ∀ listed, (stableDX listed).component = listed.1) :
    Function.Injective
      (fun p : { x // x ∈ DX.components } × { x // x ∈ DY.components } =>
        productSourceIrreducibleComponent (stableDX p.1) p.2.1) := by
  intro p q hpq
  rcases p with ⟨p₁, p₂⟩
  rcases q with ⟨q₁, q₂⟩
  have hiso :
      SourceIrreducibleComponent.IsoOverAmbient
        (productSourceIrreducibleComponent (stableDX p₁) p₂.1)
        (productSourceIrreducibleComponent (stableDX q₁) q₂.1) := by
    simpa [hpq] using
      (SourceIrreducibleComponent.IsoOverAmbient.refl
        (productSourceIrreducibleComponent (stableDX p₁) p₂.1))
  rcases _root_.Boundary.productSourceIrreducibleComponent_unique DX DY stableDX hstableDX hiso with
    ⟨hp, hq⟩
  exact Prod.ext hp hq

/-- Distinct listed component pairs give distinct product-source components. -/
theorem productSourceIrreducibleComponent_pair_ne_of_ne
    {X Y : Geometry.SmSchemeOver k}
    (DX : FiniteIrreducibleComponentDecomposition X)
    (DY : FiniteIrreducibleComponentDecomposition Y)
    (stableDX :
      (listed : { listed : SourceIrreducibleComponent X // listed ∈ DX.components }) →
        ProductStableSourceComponent X)
    (hstableDX : ∀ listed, (stableDX listed).component = listed.1)
    {p q : { x // x ∈ DX.components } × { x // x ∈ DY.components }}
    (h : p ≠ q) :
    productSourceIrreducibleComponent (stableDX p.1) p.2.1 ≠
      productSourceIrreducibleComponent (stableDX q.1) q.2.1 := by
  intro hpq
  exact h (productSourceIrreducibleComponent_pair_injective DX DY stableDX hstableDX hpq)

/-- Concrete equivalence between listed factor-component pairs and the listed
components of the certified product decomposition. -/
noncomputable def productSourceIrreducibleComponent_listedEquiv
    {X Y : Geometry.SmSchemeOver k}
    (DX : FiniteIrreducibleComponentDecomposition X)
    (DY : FiniteIrreducibleComponentDecomposition Y)
    (stableDX :
      (listed : { listed : SourceIrreducibleComponent X // listed ∈ DX.components }) →
        ProductStableSourceComponent X)
    (hstableDX : ∀ listed, (stableDX listed).component = listed.1) :
    ({ x // x ∈ DX.components } × { y // y ∈ DY.components }) ≃
      { listed : SourceIrreducibleComponent (overBaseProductObject X Y) //
        listed ∈
          (_root_.Boundary.finiteProductSourceIrreducibleComponentDecomposition
            DX DY stableDX hstableDX).components } := by
  classical
  let listedPairs :
      Finset ({ x // x ∈ DX.components } × { y // y ∈ DY.components }) :=
    DX.components.attach.product DY.components.attach
  let componentMap :
      ({ x // x ∈ DX.components } × { y // y ∈ DY.components }) →
        SourceIrreducibleComponent (overBaseProductObject X Y) :=
    fun p => productSourceIrreducibleComponent (stableDX p.1) p.2.1
  have hcomp :
      (_root_.Boundary.finiteProductSourceIrreducibleComponentDecomposition
        DX DY stableDX hstableDX).components =
        listedPairs.image componentMap := by
    rfl
  have hinj : Function.Injective componentMap :=
    productSourceIrreducibleComponent_pair_injective DX DY stableDX hstableDX
  refine
    { toFun := fun p =>
        ⟨componentMap p, ?_⟩
      invFun := fun listed =>
        Classical.choose ?_
      left_inv := ?_
      right_inv := ?_ }
  · rw [hcomp]
    refine Finset.mem_image.mpr ?_
    refine ⟨p, ?_, rfl⟩
    exact Finset.mem_product.mpr ⟨Finset.mem_attach _ _, Finset.mem_attach _ _⟩
  · have hmem : listed.1 ∈ listedPairs.image componentMap := by
      simpa [hcomp] using listed.2
    exact Finset.mem_image.mp hmem
  · intro p
    let witness :
        ∃ a ∈ listedPairs, componentMap a =
          (⟨componentMap p, by
            rw [hcomp]
            refine Finset.mem_image.mpr ?_
            refine ⟨p, ?_, rfl⟩
            exact Finset.mem_product.mpr
              ⟨Finset.mem_attach _ _, Finset.mem_attach _ _⟩⟩ :
            { listed : SourceIrreducibleComponent (overBaseProductObject X Y) //
              listed ∈
                (_root_.Boundary.finiteProductSourceIrreducibleComponentDecomposition
                  DX DY stableDX hstableDX).components }).1 := by
      rw [hcomp]
      exact Finset.mem_image.mp
        (by
          refine Finset.mem_image.mpr ?_
          refine ⟨p, ?_, rfl⟩
          exact Finset.mem_product.mpr
            ⟨Finset.mem_attach _ _, Finset.mem_attach _ _⟩)
    have hchosen := Classical.choose_spec witness
    exact hinj hchosen.2
  · intro listed
    let witness :
        ∃ a ∈ listedPairs, componentMap a = listed.1 := by
      have hmem : listed.1 ∈ listedPairs.image componentMap := by
        simpa [hcomp] using listed.2
      exact Finset.mem_image.mp hmem
    have hchosen := Classical.choose_spec witness
    apply Subtype.ext
    exact hchosen.2

/-- Concrete equivalence between the raw singleton diagonal pieces of
`id × id` and the listed components of the certified product decomposition. -/
noncomputable def identityExternalProduct_rawDiagonalPieces_equiv_productComponents
    {X Y : Geometry.SmSchemeOver k}
    (DX : FiniteIrreducibleComponentDecomposition X)
    (DY : FiniteIrreducibleComponentDecomposition Y)
    (stableDX :
      (listed : { listed : SourceIrreducibleComponent X // listed ∈ DX.components }) →
        ProductStableSourceComponent X)
    (hstableDX : ∀ listed, (stableDX listed).component = listed.1) :
    (Σ sourceX : { sourceX : SourceIrreducibleComponent X // sourceX ∈ DX.components },
      Σ sourceY : { sourceY : SourceIrreducibleComponent Y // sourceY ∈ DY.components },
        (GraphExternalProductSingleton.graphExternalProduct_id_right_imageDecomposition_singleton
          (stableDX sourceX) sourceY.1 (𝟙 X)).components.index)
      ≃ { listed : SourceIrreducibleComponent (overBaseProductObject X Y) //
          listed ∈
            (_root_.Boundary.finiteProductSourceIrreducibleComponentDecomposition
              DX DY stableDX hstableDX).components } := by
  classical
  let pairEquiv :=
    productSourceIrreducibleComponent_listedEquiv DX DY stableDX hstableDX
  refine
    { toFun := fun idx => pairEquiv ⟨idx.1, idx.2.1⟩
      invFun := fun listed =>
        let p := pairEquiv.symm listed
        ⟨p.1, p.2,
          (ULift.up () :
            (GraphExternalProductSingleton.graphExternalProduct_id_right_imageDecomposition_singleton
              (stableDX p.1) p.2.1 (𝟙 X)).components.index)⟩
      left_inv := ?_
      right_inv := ?_ }
  · intro idx
    cases idx with
    | mk sourceX rest =>
    cases rest with
    | mk sourceY i =>
    cases i with
    | up down =>
    cases down
    simp [pairEquiv]
  · intro listed
    simp [pairEquiv]

/-- The raw singleton diagonal piece indexed by a listed factor pair gives the
same diagonal finite correspondence as the corresponding listed component of
the certified product decomposition. -/
theorem identityExternalProduct_rawDiagonalPiece_diagonal_eq_productComponent
    {X Y : Geometry.SmSchemeOver k}
    (DX : FiniteIrreducibleComponentDecomposition X)
    (DY : FiniteIrreducibleComponentDecomposition Y)
    (stableDX :
      (listed : { listed : SourceIrreducibleComponent X // listed ∈ DX.components }) →
        ProductStableSourceComponent X)
    (hstableDX : ∀ listed, (stableDX listed).component = listed.1)
    (idx :
      Σ sourceX : { sourceX : SourceIrreducibleComponent X // sourceX ∈ DX.components },
        Σ sourceY : { sourceY : SourceIrreducibleComponent Y // sourceY ∈ DY.components },
          (GraphExternalProductSingleton.graphExternalProduct_id_right_imageDecomposition_singleton
            (stableDX sourceX) sourceY.1 (𝟙 X)).components.index) :
    SourceImageSubscheme.diagonalFiniteCorrespondence
        ((GraphExternalProductSingleton.graphExternalProduct_id_right_imageDecomposition_singleton
          (stableDX idx.1) idx.2.1.1 (𝟙 X)).toRepresentedPrimeSupport idx.2.2).sourceComponent =
      SourceIrreducibleComponent.diagonalFiniteCorrespondence
        ((identityExternalProduct_rawDiagonalPieces_equiv_productComponents
          DX DY stableDX hstableDX idx).1) := by
  cases idx with
  | mk sourceX rest =>
  cases rest with
  | mk sourceY i =>
  cases i with
  | up down =>
  cases down
  simp [
    identityExternalProduct_rawDiagonalPieces_equiv_productComponents,
    productSourceIrreducibleComponent_listedEquiv,
    GraphExternalProductSingleton.graphExternalProduct_id_right_imageDecomposition_singleton,
    ProductFiniteCorrespondenceImageDecomposition.toRepresentedPrimeSupport,
    GraphExternalProductSingleton.rightSourceImage_diagonalFiniteCorrespondence
  ]

/-- The concrete singleton raw diagonal pieces for `id × id` sum to the
canonical identity finite correspondence of the product decomposition. -/
theorem identityExternalProduct_singletonDiagonalSum_eq_identityFiniteCorrespondence
    {X Y : Geometry.SmSchemeOver k}
    (DX : FiniteIrreducibleComponentDecomposition X)
    (DY : FiniteIrreducibleComponentDecomposition Y)
    (stableDX :
      (listed : { listed : SourceIrreducibleComponent X // listed ∈ DX.components }) →
        ProductStableSourceComponent X)
    (hstableDX : ∀ listed, (stableDX listed).component = listed.1) :
    (∑ sourceX in DX.components.attach,
      ∑ sourceY in DY.components.attach,
        ∑ i :
          (GraphExternalProductSingleton.graphExternalProduct_id_right_imageDecomposition_singleton
            (stableDX sourceX) sourceY.1 (𝟙 X)).components.index,
          SourceImageSubscheme.diagonalFiniteCorrespondence
            ((GraphExternalProductSingleton.graphExternalProduct_id_right_imageDecomposition_singleton
              (stableDX sourceX) sourceY.1 (𝟙 X)).toRepresentedPrimeSupport i).sourceComponent) =
      (_root_.Boundary.finiteProductSourceIrreducibleComponentDecomposition
        DX DY stableDX hstableDX).identityFiniteCorrespondence := by
  classical
  let rawEquiv :=
    identityExternalProduct_rawDiagonalPieces_equiv_productComponents DX DY stableDX hstableDX
  let sourceImage :
      (Σ sourceX : { sourceX : SourceIrreducibleComponent X // sourceX ∈ DX.components },
        Σ sourceY : { sourceY : SourceIrreducibleComponent Y // sourceY ∈ DY.components },
          (GraphExternalProductSingleton.graphExternalProduct_id_right_imageDecomposition_singleton
            (stableDX sourceX) sourceY.1 (𝟙 X)).components.index) →
        SourceImageSubscheme (k := k) (overBaseProductObject X Y) :=
    fun idx =>
      ((GraphExternalProductSingleton.graphExternalProduct_id_right_imageDecomposition_singleton
        (stableDX idx.1) idx.2.1.1 (𝟙 X)).toRepresentedPrimeSupport idx.2.2).sourceComponent
  have hFormal :
      (∑ idx :
        (Σ sourceX : { sourceX : SourceIrreducibleComponent X // sourceX ∈ DX.components },
          Σ sourceY : { sourceY : SourceIrreducibleComponent Y // sourceY ∈ DY.components },
            (GraphExternalProductSingleton.graphExternalProduct_id_right_imageDecomposition_singleton
              (stableDX sourceX) sourceY.1 (𝟙 X)).components.index),
        SourceImageSubscheme.diagonalFiniteCorrespondence (sourceImage idx)) =
        (_root_.Boundary.finiteProductSourceIrreducibleComponentDecomposition
          DX DY stableDX hstableDX).identityFiniteCorrespondence := by
    exact
      FiniteIrreducibleComponentDecomposition.sum_diagonal_eq_identityFiniteCorrespondence_of_equiv_components
        (_root_.Boundary.finiteProductSourceIrreducibleComponentDecomposition
          DX DY stableDX hstableDX)
        sourceImage rawEquiv
        (identityExternalProduct_rawDiagonalPiece_diagonal_eq_productComponent
          DX DY stableDX hstableDX)
  change
    (∑ sourceX in DX.components.attach,
      ∑ sourceY in DY.components.attach,
        ∑ i :
          (GraphExternalProductSingleton.graphExternalProduct_id_right_imageDecomposition_singleton
            (stableDX sourceX) sourceY.1 (𝟙 X)).components.index,
          SourceImageSubscheme.diagonalFiniteCorrespondence
            (sourceImage ⟨sourceX, sourceY, i⟩)) =
      (_root_.Boundary.finiteProductSourceIrreducibleComponentDecomposition
        DX DY stableDX hstableDX).identityFiniteCorrespondence
  simpa [sourceImage] using hFormal

/-- Graph-compatible identity external product over an arbitrary certified
product decomposition. This is the owner-level support/decomposition theorem
that the monoidal layer actually needs: once the raw diagonal pieces for
`id × id` are identified bijectively with the listed components of some
certified decomposition of `X ×_k Y`, the external product of the two identity
finite correspondences is the canonical identity finite correspondence of that
decomposition.

The remaining work for the fully unconditional tensor identity theorem is
therefore exactly the geometric construction of `listedEquiv` and
`hcomponent` for the actual product-support decomposition, not any further
algebra in `SmCorQ`. -/
theorem externalProduct_identity_identity_eq_identityFiniteCorrespondence_of_decomposition
    (family : FiniteCorrespondence.GraphIdentityCompatibleExternalProductFamily (k := k))
    {X Y : Geometry.SmSchemeOver k}
    (DX : FiniteIrreducibleComponentDecomposition X)
    (DY : FiniteIrreducibleComponentDecomposition Y)
    (DProduct : FiniteIrreducibleComponentDecomposition (overBaseProductObject X Y))
    (hIso :
      ∀ (sourceX : { sourceX : SourceIrreducibleComponent X // sourceX ∈ DX.components })
        (sourceY : { sourceY : SourceIrreducibleComponent Y // sourceY ∈ DY.components })
        (i :
          (family.family.decompose
            (SourceIrreducibleComponent.diagonalRepresentedPrimeSupport (k := k) sourceX.1)
            (SourceIrreducibleComponent.diagonalRepresentedPrimeSupport (k := k) sourceY.1)).components.index),
          IsIso
            ((family.family.decompose
              (SourceIrreducibleComponent.diagonalRepresentedPrimeSupport (k := k) sourceX.1)
              (SourceIrreducibleComponent.diagonalRepresentedPrimeSupport (k := k) sourceY.1)).toSourceImage i))
    (hmult :
      ∀ (sourceX : { sourceX : SourceIrreducibleComponent X // sourceX ∈ DX.components })
        (sourceY : { sourceY : SourceIrreducibleComponent Y // sourceY ∈ DY.components })
        (i :
          (family.family.decompose
            (SourceIrreducibleComponent.diagonalRepresentedPrimeSupport (k := k) sourceX.1)
            (SourceIrreducibleComponent.diagonalRepresentedPrimeSupport (k := k) sourceY.1)).components.index),
          (family.family.decompose
            (SourceIrreducibleComponent.diagonalRepresentedPrimeSupport (k := k) sourceX.1)
            (SourceIrreducibleComponent.diagonalRepresentedPrimeSupport (k := k) sourceY.1)).multiplicity i = 1)
    (listedEquiv :
      (Σ sourceX : { sourceX : SourceIrreducibleComponent X // sourceX ∈ DX.components },
        Σ sourceY : { sourceY : SourceIrreducibleComponent Y // sourceY ∈ DY.components },
          (family.family.decompose
            (SourceIrreducibleComponent.diagonalRepresentedPrimeSupport (k := k) sourceX.1)
            (SourceIrreducibleComponent.diagonalRepresentedPrimeSupport (k := k) sourceY.1)).components.index)
        ≃ { listed : SourceIrreducibleComponent (overBaseProductObject X Y) //
            listed ∈ DProduct.components })
    (hcomponent :
      ∀ idx :
        (Σ sourceX : { sourceX : SourceIrreducibleComponent X // sourceX ∈ DX.components },
          Σ sourceY : { sourceY : SourceIrreducibleComponent Y // sourceY ∈ DY.components },
            (family.family.decompose
              (SourceIrreducibleComponent.diagonalRepresentedPrimeSupport (k := k) sourceX.1)
              (SourceIrreducibleComponent.diagonalRepresentedPrimeSupport (k := k) sourceY.1)).components.index),
        (let P :=
          SourceIrreducibleComponent.diagonalRepresentedPrimeSupport (k := k) idx.1.1
        let Q :=
          SourceIrreducibleComponent.diagonalRepresentedPrimeSupport (k := k) idx.2.1.1
        let decomposition := family.family.decompose P Q
        SourceImageSubscheme.diagonalFiniteCorrespondence
          (decomposition.toRepresentedPrimeSupport idx.2.2).sourceComponent) =
          SourceIrreducibleComponent.diagonalFiniteCorrespondence (listedEquiv idx).1) :
    FiniteCorrespondence.externalProductWithFamily family.family
        DX.identityFiniteCorrespondence DY.identityFiniteCorrespondence =
      DProduct.identityFiniteCorrespondence := by
  exact
    FiniteCorrespondence
      .externalProductWithFamily_identity_identity_eq_identityFiniteCorrespondence_of_equiv_diagonal_decompositions
      family.family DX DY DProduct hIso hmult listedEquiv hcomponent

/-- The componentwise graph/external-product singleton for `id × id` is the
diagonal singleton on the corresponding product source component. -/
theorem graphExternalProduct_id_right_prime_eq_diagonal
    {X Y : Geometry.SmSchemeOver k}
    (C : ProductStableSourceComponent X)
    (D : SourceIrreducibleComponent Y) :
    FiniteCorrespondence.ofPrimeSupport
        (graphExternalProductPrimeSupport_id_right C D (𝟙 X)) =
      SourceIrreducibleComponent.diagonalFiniteCorrespondence
        (productSourceIrreducibleComponent C D) := by
  calc
    FiniteCorrespondence.ofPrimeSupport
        (graphExternalProductPrimeSupport_id_right C D (𝟙 X)) =
      Geometry.ordinaryMorphismGraph_componentCorrespondence
        (productSourceIrreducibleComponent C D)
        (overBaseProductMap (𝟙 X) (𝟙 Y)) := by
        exact graphExternalProduct_id_right_eq C D (𝟙 X)
    _ = Geometry.ordinaryMorphismGraph_componentCorrespondence
        (productSourceIrreducibleComponent C D)
        (𝟙 (overBaseProductObject X Y)) := by
        rw [overBaseProductMap_id]
    _ = SourceIrreducibleComponent.diagonalFiniteCorrespondence
        (productSourceIrreducibleComponent C D) := by
        exact SmCorQ.graphComponentCorrespondence_id
          (productSourceIrreducibleComponent C D)

/-- The graph finite correspondence of `f × id` over the canonical product
decomposition is the sum of the componentwise external-product graph singletons
indexed by the listed factor components. -/
theorem graphFiniteCorrespondence_overBaseProductMap_id_right_eq_sum
    {X Y Z : Geometry.SmSchemeOver k}
    (DX : FiniteIrreducibleComponentDecomposition X)
    (DZ : FiniteIrreducibleComponentDecomposition Z)
    (stableDX :
      (listed : { listed : SourceIrreducibleComponent X // listed ∈ DX.components }) →
        ProductStableSourceComponent X)
    (hstableDX : ∀ listed, (stableDX listed).component = listed.1)
    (f : SmOverHom X Y) :
    Geometry.ordinaryMorphismGraph_finiteCorrespondenceOfDecomposition
        (overBaseProductMap f (𝟙 Z))
        (_root_.Boundary.finiteProductSourceIrreducibleComponentDecomposition DX DZ stableDX hstableDX) =
      ∑ p in DX.components.attach.product DZ.components.attach,
        FiniteCorrespondence.ofPrimeSupport
          (graphExternalProductPrimeSupport_id_right (stableDX p.1) p.2.1 f) := by
  classical
  let listedPairs :
      Finset ({ x // x ∈ DX.components } × { x // x ∈ DZ.components }) :=
    DX.components.attach.product DZ.components.attach
  let componentMap :
      ({ x // x ∈ DX.components } × { x // x ∈ DZ.components }) →
        SourceIrreducibleComponent (overBaseProductObject X Z) :=
    fun p => productSourceIrreducibleComponent (stableDX p.1) p.2.1
  have hcomp :
      (_root_.Boundary.finiteProductSourceIrreducibleComponentDecomposition DX DZ stableDX hstableDX).components =
        listedPairs.image componentMap := by
    rfl
  rw [Geometry.ordinaryMorphismGraph_finiteCorrespondenceOfDecomposition, hcomp]
  rw [Finset.sum_image]
  · refine Finset.sum_congr rfl ?_
    intro p hp
    simpa [componentMap] using
      graphCorrespondence_overBaseProductMap_id_right_eq_externalProduct
        (stableDX p.1) p.2.1 f
  · intro x hx y hy hxy
    exact productSourceIrreducibleComponent_pair_injective DX DZ stableDX hstableDX hxy

/-- Rational graph transfer form of the right identity external-product graph
compatibility. -/
theorem graphTransfer_overBaseProductMap_id_right
    (category : SmCorQ (k := k))
    {X Y Z : Geometry.SmSchemeOver k}
    (DX : FiniteIrreducibleComponentDecomposition X)
    (DZ : FiniteIrreducibleComponentDecomposition Z)
    (stableDX :
      (listed : { listed : SourceIrreducibleComponent X // listed ∈ DX.components }) →
        ProductStableSourceComponent X)
    (hstableDX : ∀ listed, (stableDX listed).component = listed.1)
    (f : SmOverHom X Y) :
    SmCorQ.graphTransfer category
        (overBaseProductMap f (𝟙 Z))
        (_root_.Boundary.finiteProductSourceIrreducibleComponentDecomposition DX DZ stableDX hstableDX) =
      FiniteCorrespondence.toRational
        (∑ p in DX.components.attach.product DZ.components.attach,
          FiniteCorrespondence.ofPrimeSupport
            (graphExternalProductPrimeSupport_id_right (stableDX p.1) p.2.1 f)) := by
  change
    FiniteCorrespondence.toRational
      (Geometry.ordinaryMorphismGraph_finiteCorrespondenceOfDecomposition
        (overBaseProductMap f (𝟙 Z))
        (_root_.Boundary.finiteProductSourceIrreducibleComponentDecomposition DX DZ stableDX hstableDX)) =
      FiniteCorrespondence.toRational
        (∑ p in DX.components.attach.product DZ.components.attach,
          FiniteCorrespondence.ofPrimeSupport
            (graphExternalProductPrimeSupport_id_right (stableDX p.1) p.2.1 f))
  exact congrArg FiniteCorrespondence.toRational
    (graphFiniteCorrespondence_overBaseProductMap_id_right_eq_sum DX DZ stableDX hstableDX f)

/-- The graph finite correspondence of `id × g` over the canonical product
decomposition is the sum of the componentwise external-product graph singletons
indexed by the listed factor components. -/
theorem graphFiniteCorrespondence_overBaseProductMap_id_left_eq_sum
    {X Y Z : Geometry.SmSchemeOver k}
    (DX : FiniteIrreducibleComponentDecomposition X)
    (DY : FiniteIrreducibleComponentDecomposition Y)
    (stableDX :
      (listed : { listed : SourceIrreducibleComponent X // listed ∈ DX.components }) →
        ProductStableSourceComponent X)
    (hstableDX : ∀ listed, (stableDX listed).component = listed.1)
    (g : SmOverHom Y Z) :
    Geometry.ordinaryMorphismGraph_finiteCorrespondenceOfDecomposition
        (overBaseProductMap (𝟙 X) g)
        (_root_.Boundary.finiteProductSourceIrreducibleComponentDecomposition DX DY stableDX hstableDX) =
      ∑ p in DX.components.attach.product DY.components.attach,
        FiniteCorrespondence.ofPrimeSupport
          (graphExternalProductPrimeSupport_id_left (stableDX p.1) p.2.1 g) := by
  classical
  let listedPairs :
      Finset ({ x // x ∈ DX.components } × { x // x ∈ DY.components }) :=
    DX.components.attach.product DY.components.attach
  let componentMap :
      ({ x // x ∈ DX.components } × { x // x ∈ DY.components }) →
        SourceIrreducibleComponent (overBaseProductObject X Y) :=
    fun p => productSourceIrreducibleComponent (stableDX p.1) p.2.1
  have hcomp :
      (_root_.Boundary.finiteProductSourceIrreducibleComponentDecomposition DX DY stableDX hstableDX).components =
        listedPairs.image componentMap := by
    rfl
  rw [Geometry.ordinaryMorphismGraph_finiteCorrespondenceOfDecomposition, hcomp]
  rw [Finset.sum_image]
  · refine Finset.sum_congr rfl ?_
    intro p hp
    simpa [componentMap] using
      graphCorrespondence_overBaseProductMap_id_left_eq_externalProduct
        (stableDX p.1) p.2.1 g
  · intro x hx y hy hxy
    exact productSourceIrreducibleComponent_pair_injective DX DY stableDX hstableDX hxy

/-- Rational graph transfer form of the left identity external-product graph
compatibility. -/
theorem graphTransfer_overBaseProductMap_id_left
    (category : SmCorQ (k := k))
    {X Y Z : Geometry.SmSchemeOver k}
    (DX : FiniteIrreducibleComponentDecomposition X)
    (DY : FiniteIrreducibleComponentDecomposition Y)
    (stableDX :
      (listed : { listed : SourceIrreducibleComponent X // listed ∈ DX.components }) →
        ProductStableSourceComponent X)
    (hstableDX : ∀ listed, (stableDX listed).component = listed.1)
    (g : SmOverHom Y Z) :
    SmCorQ.graphTransfer category
        (overBaseProductMap (𝟙 X) g)
        (_root_.Boundary.finiteProductSourceIrreducibleComponentDecomposition DX DY stableDX hstableDX) =
      FiniteCorrespondence.toRational
        (∑ p in DX.components.attach.product DY.components.attach,
          FiniteCorrespondence.ofPrimeSupport
            (graphExternalProductPrimeSupport_id_left (stableDX p.1) p.2.1 g)) := by
  change
    FiniteCorrespondence.toRational
      (Geometry.ordinaryMorphismGraph_finiteCorrespondenceOfDecomposition
        (overBaseProductMap (𝟙 X) g)
        (_root_.Boundary.finiteProductSourceIrreducibleComponentDecomposition DX DY stableDX hstableDX)) =
      FiniteCorrespondence.toRational
        (∑ p in DX.components.attach.product DY.components.attach,
          FiniteCorrespondence.ofPrimeSupport
            (graphExternalProductPrimeSupport_id_left (stableDX p.1) p.2.1 g))
  exact congrArg FiniteCorrespondence.toRational
    (graphFiniteCorrespondence_overBaseProductMap_id_left_eq_sum DX DY stableDX hstableDX g)

namespace FiniteCorrespondence

/-- External-product owners whose chosen decomposition family computes graph
products with diagonal identities by the singleton decompositions constructed
in this file's upstream graph-support layer. -/
structure GraphIdentityCompatibleExternalProductFamily extends
    CanonicalExternalProductFamily (k := k) where
  externalProduct_graph_id_right :
    ∀ {X Y Z : Geometry.SmSchemeOver k}
      (C : ProductStableSourceComponent X)
      (D : SourceIrreducibleComponent Z)
      (f : SmOverHom X Y),
        externalProductWithFamily toCanonicalExternalProductFamily.family
          (FiniteCorrespondence.ofPrimeSupport
            (Geometry.ordinaryMorphismGraphPrimeSupport C.component f))
          (SourceIrreducibleComponent.diagonalFiniteCorrespondence D) =
        FiniteCorrespondence.ofPrimeSupport
          (graphExternalProductPrimeSupport_id_right C D f)
  externalProduct_graph_id_left :
    ∀ {X Y Z : Geometry.SmSchemeOver k}
      (C : ProductStableSourceComponent X)
      (D : SourceIrreducibleComponent Y)
      (g : SmOverHom Y Z),
        externalProductWithFamily toCanonicalExternalProductFamily.family
          (SourceIrreducibleComponent.diagonalFiniteCorrespondence C.component)
          (FiniteCorrespondence.ofPrimeSupport
            (Geometry.ordinaryMorphismGraphPrimeSupport D g)) =
        FiniteCorrespondence.ofPrimeSupport
          (graphExternalProductPrimeSupport_id_left C D g)

/-- Tensor-compatible external-product owner.

The identity fields are proved against the graph/diagonal singleton
construction in this file. The interchange field is the correspondence-level
compatibility needed for functorial tensor products:
compose first in each factor and then externally multiply, or externally
multiply source and target correspondences and then compose. This is the
owner-level package consumed by presentation and motive layers; downstream
code should use its exported theorems rather than carrying prime-level
interchange hypotheses. -/
structure TensorCompatibleExternalProductFamily extends
    GraphIdentityCompatibleExternalProductFamily (k := k) where
  externalProduct_compPrime_interchange :
    ∀ {W1 X1 Y1 W2 X2 Y2 : Geometry.SmSchemeOver k}
      (compData : FiniteCorrespondenceCompositionData (k := k))
      (f : PrimeFiniteCorrespondenceGeom W1 X1)
      (g : PrimeFiniteCorrespondenceGeom X1 Y1)
      (f' : PrimeFiniteCorrespondenceGeom W2 X2)
      (g' : PrimeFiniteCorrespondenceGeom X2 Y2),
        externalProductWithFamily toGraphIdentityCompatibleExternalProductFamily.family
            (FiniteCorrespondenceCompositionData.compPrime compData f g)
            (FiniteCorrespondenceCompositionData.compPrime compData f' g')
          =
            FiniteCorrespondenceCompositionData.comp compData
              (externalProductWithFamily toGraphIdentityCompatibleExternalProductFamily.family
                (Finsupp.single f 1) (Finsupp.single f' 1))
              (externalProductWithFamily toGraphIdentityCompatibleExternalProductFamily.family
                (Finsupp.single g 1) (Finsupp.single g' 1))

namespace GraphIdentityCompatibleExternalProductFamily

instance (family : GraphIdentityCompatibleExternalProductFamily (k := k)) :
    CanonicalExternalProductFamily (k := k) :=
  family.toCanonicalExternalProductFamily

theorem externalProduct_identity_right_eq_sum
    (family : GraphIdentityCompatibleExternalProductFamily (k := k))
    {X Z : Geometry.SmSchemeOver k}
    (DX : FiniteIrreducibleComponentDecomposition X)
    (DZ : FiniteIrreducibleComponentDecomposition Z)
    (stableDX :
      (listed : { listed : SourceIrreducibleComponent X // listed ∈ DX.components }) →
        ProductStableSourceComponent X)
    (hstableDX : ∀ listed, (stableDX listed).component = listed.1) :
    externalProductWithFamily family.family
        DX.identityFiniteCorrespondence DZ.identityFiniteCorrespondence =
      ∑ p in DX.components.attach.product DZ.components.attach,
        FiniteCorrespondence.ofPrimeSupport
          (graphExternalProductPrimeSupport_id_right
            (stableDX p.1) p.2.1 (𝟙 X)) := by
  classical
  rw [FiniteIrreducibleComponentDecomposition.identityFiniteCorrespondence_eq_sum_components,
    FiniteIrreducibleComponentDecomposition.identityFiniteCorrespondence_eq_sum_components]
  rw [externalProductWithFamily_sum_left]
  simp only [externalProductWithFamily_sum_right]
  rw [← Finset.sum_product']
  rw [Finset.sum_product]
  conv_rhs =>
    change ∑ p in DX.components.attach ×ˢ DZ.components.attach,
      FiniteCorrespondence.ofPrimeSupport
        (graphExternalProductPrimeSupport_id_right (stableDX p.1) p.2.1 (𝟙 X))
    rw [Finset.sum_product]
  rw [← Finset.sum_attach]
  apply Finset.sum_congr rfl
  intro x _hx
  rw [← Finset.sum_attach]
  apply Finset.sum_congr rfl
  intro z _hz
  rw [← SmCorQ.graphComponentCorrespondence_id x.1]
  rw [← hstableDX x]
  simpa [Geometry.ordinaryMorphismGraph_componentCorrespondence] using
    family.externalProduct_graph_id_right (stableDX x) z.1 (𝟙 X)

theorem externalProduct_identity_left_eq_sum
    (family : GraphIdentityCompatibleExternalProductFamily (k := k))
    {X Y : Geometry.SmSchemeOver k}
    (DX : FiniteIrreducibleComponentDecomposition X)
    (DY : FiniteIrreducibleComponentDecomposition Y)
    (stableDX :
      (listed : { listed : SourceIrreducibleComponent X // listed ∈ DX.components }) →
        ProductStableSourceComponent X)
    (hstableDX : ∀ listed, (stableDX listed).component = listed.1) :
    externalProductWithFamily family.family
        DX.identityFiniteCorrespondence DY.identityFiniteCorrespondence =
      ∑ p in DX.components.attach.product DY.components.attach,
        FiniteCorrespondence.ofPrimeSupport
          (graphExternalProductPrimeSupport_id_left
            (stableDX p.1) p.2.1 (𝟙 Y)) := by
  classical
  rw [FiniteIrreducibleComponentDecomposition.identityFiniteCorrespondence_eq_sum_components,
    FiniteIrreducibleComponentDecomposition.identityFiniteCorrespondence_eq_sum_components]
  rw [externalProductWithFamily_sum_left]
  simp only [externalProductWithFamily_sum_right]
  rw [← Finset.sum_product']
  rw [Finset.sum_product]
  conv_rhs =>
    change ∑ p in DX.components.attach ×ˢ DY.components.attach,
      FiniteCorrespondence.ofPrimeSupport
        (graphExternalProductPrimeSupport_id_left (stableDX p.1) p.2.1 (𝟙 Y))
    rw [Finset.sum_product]
  rw [← Finset.sum_attach]
  apply Finset.sum_congr rfl
  intro x _hx
  rw [← Finset.sum_attach]
  apply Finset.sum_congr rfl
  intro y _hy
  rw [← SmCorQ.graphComponentCorrespondence_id y.1]
  rw [← hstableDX x]
  simpa [Geometry.ordinaryMorphismGraph_componentCorrespondence] using
    family.externalProduct_graph_id_left (stableDX x) y.1 (𝟙 Y)

end GraphIdentityCompatibleExternalProductFamily

namespace GraphIdentityCompatibleExternalProductFamily

/-- Integral owner theorem: a graph-compatible external-product family sends
the two diagonal identity correspondences to the component-sum identity on the
certified product decomposition. -/
theorem externalProduct_identity_identity_eq_identityFiniteCorrespondence
    (family : GraphIdentityCompatibleExternalProductFamily (k := k))
    {X Y : Geometry.SmSchemeOver k}
    (DX : FiniteIrreducibleComponentDecomposition X)
    (DY : FiniteIrreducibleComponentDecomposition Y)
    (stableDX :
      (listed : { listed : SourceIrreducibleComponent X // listed ∈ DX.components }) →
        ProductStableSourceComponent X)
    (hstableDX : ∀ listed, (stableDX listed).component = listed.1) :
    externalProductWithFamily family.family
        DX.identityFiniteCorrespondence DY.identityFiniteCorrespondence =
      (_root_.Boundary.finiteProductSourceIrreducibleComponentDecomposition
        DX DY stableDX hstableDX).identityFiniteCorrespondence := by
  classical
  rw [externalProduct_identity_right_eq_sum family DX DY stableDX hstableDX]
  rw [FiniteIrreducibleComponentDecomposition.identityFiniteCorrespondence_eq_sum_components]
  let listedPairs :
      Finset ({ x // x ∈ DX.components } × { y // y ∈ DY.components }) :=
    DX.components.attach.product DY.components.attach
  let componentMap :
      ({ x // x ∈ DX.components } × { y // y ∈ DY.components }) →
        SourceIrreducibleComponent (overBaseProductObject X Y) :=
    fun p => productSourceIrreducibleComponent (stableDX p.1) p.2.1
  have hcomp :
      (_root_.Boundary.finiteProductSourceIrreducibleComponentDecomposition
        DX DY stableDX hstableDX).components =
        listedPairs.image componentMap := by
    rfl
  rw [hcomp, Finset.sum_image]
  · refine Finset.sum_congr rfl ?_
    intro p hp
    exact graphExternalProduct_id_right_prime_eq_diagonal (stableDX p.1) p.2.1
  · intro p hp q hq hpq
    exact productSourceIrreducibleComponent_pair_injective DX DY stableDX hstableDX hpq

end GraphIdentityCompatibleExternalProductFamily

namespace TensorCompatibleExternalProductFamily

instance (family : TensorCompatibleExternalProductFamily (k := k)) :
    GraphIdentityCompatibleExternalProductFamily (k := k) :=
  family.toGraphIdentityCompatibleExternalProductFamily

instance (family : TensorCompatibleExternalProductFamily (k := k)) :
    CanonicalExternalProductFamily (k := k) :=
  family.toGraphIdentityCompatibleExternalProductFamily.toCanonicalExternalProductFamily

end TensorCompatibleExternalProductFamily

end FiniteCorrespondence

/-- Specializing the graph/external-product right endpoint to `id × id`
recovers the rational identity correspondence on the product. -/
theorem graphExternalProduct_id_right_sum_eq_identity
    (category : SmCorQ (k := k))
    {X Z : Geometry.SmSchemeOver k}
    (DX : FiniteIrreducibleComponentDecomposition X)
    (DZ : FiniteIrreducibleComponentDecomposition Z)
    (stableDX :
      (listed : { listed : SourceIrreducibleComponent X // listed ∈ DX.components }) →
        ProductStableSourceComponent X)
    (hstableDX : ∀ listed, (stableDX listed).component = listed.1) :
    FiniteCorrespondence.toRational
        (∑ p in DX.components.attach.product DZ.components.attach,
          FiniteCorrespondence.ofPrimeSupport
            (graphExternalProductPrimeSupport_id_right
              (stableDX p.1) p.2.1 (𝟙 X))) =
      FiniteCorrespondence.toRational
        ((_root_.Boundary.finiteProductSourceIrreducibleComponentDecomposition
          DX DZ stableDX hstableDX).identityFiniteCorrespondence) := by
  calc
    FiniteCorrespondence.toRational
        (∑ p in DX.components.attach.product DZ.components.attach,
          FiniteCorrespondence.ofPrimeSupport
            (graphExternalProductPrimeSupport_id_right
              (stableDX p.1) p.2.1 (𝟙 X))) =
      SmCorQ.graphTransfer category
        (overBaseProductMap (𝟙 X) (𝟙 Z))
        (_root_.Boundary.finiteProductSourceIrreducibleComponentDecomposition
          DX DZ stableDX hstableDX) := by
        exact (graphTransfer_overBaseProductMap_id_right
          category DX DZ stableDX hstableDX (𝟙 X)).symm
    _ = SmCorQ.graphTransfer category
        (𝟙 (overBaseProductObject X Z))
        (_root_.Boundary.finiteProductSourceIrreducibleComponentDecomposition
          DX DZ stableDX hstableDX) := by
        rw [overBaseProductMap_id]
    _ = FiniteCorrespondence.toRational
        ((_root_.Boundary.finiteProductSourceIrreducibleComponentDecomposition
          DX DZ stableDX hstableDX).identityFiniteCorrespondence) := by
        exact SmCorQ.graphTransfer_id_eq_toRational_identity
          (category := category)
          (_root_.Boundary.finiteProductSourceIrreducibleComponentDecomposition
            DX DZ stableDX hstableDX)

/-- The left-handed graph/external-product endpoint has the same identity
specialization. -/
theorem graphExternalProduct_id_left_sum_eq_identity
    (category : SmCorQ (k := k))
    {X Y : Geometry.SmSchemeOver k}
    (DX : FiniteIrreducibleComponentDecomposition X)
    (DY : FiniteIrreducibleComponentDecomposition Y)
    (stableDX :
      (listed : { listed : SourceIrreducibleComponent X // listed ∈ DX.components }) →
        ProductStableSourceComponent X)
    (hstableDX : ∀ listed, (stableDX listed).component = listed.1) :
    FiniteCorrespondence.toRational
        (∑ p in DX.components.attach.product DY.components.attach,
          FiniteCorrespondence.ofPrimeSupport
            (graphExternalProductPrimeSupport_id_left
              (stableDX p.1) p.2.1 (𝟙 Y))) =
      FiniteCorrespondence.toRational
        ((_root_.Boundary.finiteProductSourceIrreducibleComponentDecomposition
          DX DY stableDX hstableDX).identityFiniteCorrespondence) := by
  calc
    FiniteCorrespondence.toRational
        (∑ p in DX.components.attach.product DY.components.attach,
          FiniteCorrespondence.ofPrimeSupport
            (graphExternalProductPrimeSupport_id_left
              (stableDX p.1) p.2.1 (𝟙 Y))) =
      SmCorQ.graphTransfer category
        (overBaseProductMap (𝟙 X) (𝟙 Y))
        (_root_.Boundary.finiteProductSourceIrreducibleComponentDecomposition
          DX DY stableDX hstableDX) := by
        exact (graphTransfer_overBaseProductMap_id_left
          category DX DY stableDX hstableDX (𝟙 Y)).symm
    _ = SmCorQ.graphTransfer category
        (𝟙 (overBaseProductObject X Y))
        (_root_.Boundary.finiteProductSourceIrreducibleComponentDecomposition
          DX DY stableDX hstableDX) := by
        rw [overBaseProductMap_id]
    _ = FiniteCorrespondence.toRational
        ((_root_.Boundary.finiteProductSourceIrreducibleComponentDecomposition
          DX DY stableDX hstableDX).identityFiniteCorrespondence) := by
        exact SmCorQ.graphTransfer_id_eq_toRational_identity
          (category := category)
          (_root_.Boundary.finiteProductSourceIrreducibleComponentDecomposition
            DX DY stableDX hstableDX)

namespace FiniteCorrespondence.GraphIdentityCompatibleExternalProductFamily

/-- A graph-compatible external-product family sends a graph correspondence
external-tensored with a diagonal identity to the componentwise graph of
`f × id`, expressed over the product-source decomposition. -/
theorem externalProduct_graphTransfer_id_right_eq_sum
    (family : FiniteCorrespondence.GraphIdentityCompatibleExternalProductFamily (k := k))
    {X Y Z : Geometry.SmSchemeOver k}
    (DX : FiniteIrreducibleComponentDecomposition X)
    (DZ : FiniteIrreducibleComponentDecomposition Z)
    (stableDX :
      (listed : { listed : SourceIrreducibleComponent X // listed ∈ DX.components }) →
        ProductStableSourceComponent X)
    (hstableDX : ∀ listed, (stableDX listed).component = listed.1)
    (f : SmOverHom X Y) :
    FiniteCorrespondence.externalProductWithFamily family.family
        (Geometry.ordinaryMorphismGraph_finiteCorrespondenceOfDecomposition f DX)
        DZ.identityFiniteCorrespondence =
      ∑ p in DX.components.attach.product DZ.components.attach,
        FiniteCorrespondence.ofPrimeSupport
          (graphExternalProductPrimeSupport_id_right (stableDX p.1) p.2.1 f) := by
  classical
  rw [Geometry.ordinaryMorphismGraph_finiteCorrespondenceOfDecomposition,
    FiniteIrreducibleComponentDecomposition.identityFiniteCorrespondence_eq_sum_components]
  rw [externalProductWithFamily_sum_left]
  simp only [externalProductWithFamily_sum_right]
  rw [← Finset.sum_product']
  rw [Finset.sum_product]
  conv_rhs =>
    change ∑ p in DX.components.attach ×ˢ DZ.components.attach,
      FiniteCorrespondence.ofPrimeSupport
        (graphExternalProductPrimeSupport_id_right (stableDX p.1) p.2.1 f)
    rw [Finset.sum_product]
  rw [← Finset.sum_attach]
  apply Finset.sum_congr rfl
  intro x _hx
  rw [← Finset.sum_attach]
  apply Finset.sum_congr rfl
  intro z _hz
  rw [← hstableDX x]
  simpa [Geometry.ordinaryMorphismGraph_componentCorrespondence] using
    family.externalProduct_graph_id_right
      (stableDX x) z.1 f

/-- Left-handed graph-transfer/identity external-product sum formula. -/
theorem externalProduct_id_left_graphTransfer_eq_sum
    (family : FiniteCorrespondence.GraphIdentityCompatibleExternalProductFamily (k := k))
    {X Y Z : Geometry.SmSchemeOver k}
    (DX : FiniteIrreducibleComponentDecomposition X)
    (DY : FiniteIrreducibleComponentDecomposition Y)
    (stableDX :
      (listed : { listed : SourceIrreducibleComponent X // listed ∈ DX.components }) →
        ProductStableSourceComponent X)
    (hstableDX : ∀ listed, (stableDX listed).component = listed.1)
    (g : SmOverHom Y Z) :
    FiniteCorrespondence.externalProductWithFamily family.family
        DX.identityFiniteCorrespondence
        (Geometry.ordinaryMorphismGraph_finiteCorrespondenceOfDecomposition g DY) =
      ∑ p in DX.components.attach.product DY.components.attach,
        FiniteCorrespondence.ofPrimeSupport
          (graphExternalProductPrimeSupport_id_left (stableDX p.1) p.2.1 g) := by
  classical
  rw [FiniteIrreducibleComponentDecomposition.identityFiniteCorrespondence_eq_sum_components,
    Geometry.ordinaryMorphismGraph_finiteCorrespondenceOfDecomposition]
  rw [externalProductWithFamily_sum_left]
  simp only [externalProductWithFamily_sum_right]
  rw [← Finset.sum_product']
  rw [Finset.sum_product]
  conv_rhs =>
    change ∑ p in DX.components.attach ×ˢ DY.components.attach,
      FiniteCorrespondence.ofPrimeSupport
        (graphExternalProductPrimeSupport_id_left (stableDX p.1) p.2.1 g)
    rw [Finset.sum_product]
  rw [← Finset.sum_attach]
  apply Finset.sum_congr rfl
  intro x _hx
  rw [← Finset.sum_attach]
  apply Finset.sum_congr rfl
  intro y _hy
  rw [← hstableDX x]
  simpa [Geometry.ordinaryMorphismGraph_componentCorrespondence] using
    family.externalProduct_graph_id_left
      (stableDX x) y.1 g

/-- For a graph-compatible external-product owner, the external product of the
two diagonal identity correspondences is the product identity after extending
coefficients to `ℚ`. -/
theorem externalProduct_id_right
    (family : FiniteCorrespondence.GraphIdentityCompatibleExternalProductFamily (k := k))
    (category : SmCorQ (k := k))
    {X Z : Geometry.SmSchemeOver k}
    (DX : FiniteIrreducibleComponentDecomposition X)
    (DZ : FiniteIrreducibleComponentDecomposition Z)
    (stableDX :
      (listed : { listed : SourceIrreducibleComponent X // listed ∈ DX.components }) →
        ProductStableSourceComponent X)
    (hstableDX : ∀ listed, (stableDX listed).component = listed.1) :
    FiniteCorrespondence.toRational
        (FiniteCorrespondence.externalProductWithFamily family.family
          DX.identityFiniteCorrespondence DZ.identityFiniteCorrespondence) =
      FiniteCorrespondence.toRational
        ((_root_.Boundary.finiteProductSourceIrreducibleComponentDecomposition
          DX DZ stableDX hstableDX).identityFiniteCorrespondence) := by
  rw [externalProduct_identity_right_eq_sum family DX DZ stableDX hstableDX]
  exact graphExternalProduct_id_right_sum_eq_identity
    category DX DZ stableDX hstableDX

/-- Left-handed form of `externalProduct_id_right`. -/
theorem externalProduct_id_left
    (family : FiniteCorrespondence.GraphIdentityCompatibleExternalProductFamily (k := k))
    (category : SmCorQ (k := k))
    {X Y : Geometry.SmSchemeOver k}
    (DX : FiniteIrreducibleComponentDecomposition X)
    (DY : FiniteIrreducibleComponentDecomposition Y)
    (stableDX :
      (listed : { listed : SourceIrreducibleComponent X // listed ∈ DX.components }) →
        ProductStableSourceComponent X)
    (hstableDX : ∀ listed, (stableDX listed).component = listed.1) :
    FiniteCorrespondence.toRational
        (FiniteCorrespondence.externalProductWithFamily family.family
          DX.identityFiniteCorrespondence DY.identityFiniteCorrespondence) =
      FiniteCorrespondence.toRational
        ((_root_.Boundary.finiteProductSourceIrreducibleComponentDecomposition
          DX DY stableDX hstableDX).identityFiniteCorrespondence) := by
  rw [externalProduct_identity_left_eq_sum family DX DY stableDX hstableDX]
  exact graphExternalProduct_id_left_sum_eq_identity
    category DX DY stableDX hstableDX

/-- Tensoring the graph transfer of `f` on the right by an identity
correspondence gives the graph transfer of `f × id`, for the product
decomposition owned by the component-geometry layer. -/
theorem externalProduct_graphTransfer_id_right
    (family : FiniteCorrespondence.GraphIdentityCompatibleExternalProductFamily (k := k))
    (category : SmCorQ (k := k))
    {X Y Z : Geometry.SmSchemeOver k}
    (DX : FiniteIrreducibleComponentDecomposition X)
    (DZ : FiniteIrreducibleComponentDecomposition Z)
    (stableDX :
      (listed : { listed : SourceIrreducibleComponent X // listed ∈ DX.components }) →
        ProductStableSourceComponent X)
    (hstableDX : ∀ listed, (stableDX listed).component = listed.1)
    (f : SmOverHom X Y) :
    FiniteCorrespondence.toRational
        (FiniteCorrespondence.externalProductWithFamily family.family
          (Geometry.ordinaryMorphismGraph_finiteCorrespondenceOfDecomposition f DX)
          DZ.identityFiniteCorrespondence) =
      SmCorQ.graphTransfer category
        (overBaseProductMap f (𝟙 Z))
        (_root_.Boundary.finiteProductSourceIrreducibleComponentDecomposition
          DX DZ stableDX hstableDX) := by
  calc
    FiniteCorrespondence.toRational
        (FiniteCorrespondence.externalProductWithFamily family.family
          (Geometry.ordinaryMorphismGraph_finiteCorrespondenceOfDecomposition f DX)
          DZ.identityFiniteCorrespondence)
      = FiniteCorrespondence.toRational
          (∑ p in DX.components.attach.product DZ.components.attach,
            FiniteCorrespondence.ofPrimeSupport
              (graphExternalProductPrimeSupport_id_right (stableDX p.1) p.2.1 f)) := by
          exact congrArg FiniteCorrespondence.toRational
            (externalProduct_graphTransfer_id_right_eq_sum
              family DX DZ stableDX hstableDX f)
    _ = SmCorQ.graphTransfer category
        (overBaseProductMap f (𝟙 Z))
        (_root_.Boundary.finiteProductSourceIrreducibleComponentDecomposition
          DX DZ stableDX hstableDX) := by
          exact (graphTransfer_overBaseProductMap_id_right
            category DX DZ stableDX hstableDX f).symm

/-- Tensoring the graph transfer of `f` on the right by an identity
correspondence may target any certified decomposition of the product object,
since graph transfer is independent of the chosen source decomposition. -/
theorem externalProduct_graphTransfer_id_right_of_product_decomposition
    (family : FiniteCorrespondence.GraphIdentityCompatibleExternalProductFamily (k := k))
    (category : SmCorQ (k := k))
    {X Y Z : Geometry.SmSchemeOver k}
    (DX : FiniteIrreducibleComponentDecomposition X)
    (DZ : FiniteIrreducibleComponentDecomposition Z)
    (stableDX :
      (listed : { listed : SourceIrreducibleComponent X // listed ∈ DX.components }) →
        ProductStableSourceComponent X)
    (hstableDX : ∀ listed, (stableDX listed).component = listed.1)
    (DProduct : FiniteIrreducibleComponentDecomposition (overBaseProductObject X Z))
    (f : SmOverHom X Y) :
    FiniteCorrespondence.toRational
        (FiniteCorrespondence.externalProductWithFamily family.family
          (Geometry.ordinaryMorphismGraph_finiteCorrespondenceOfDecomposition f DX)
          DZ.identityFiniteCorrespondence) =
      SmCorQ.graphTransfer category
        (overBaseProductMap f (𝟙 Z))
        DProduct := by
  calc
    FiniteCorrespondence.toRational
        (FiniteCorrespondence.externalProductWithFamily family.family
          (Geometry.ordinaryMorphismGraph_finiteCorrespondenceOfDecomposition f DX)
          DZ.identityFiniteCorrespondence) =
      SmCorQ.graphTransfer category
        (overBaseProductMap f (𝟙 Z))
        (_root_.Boundary.finiteProductSourceIrreducibleComponentDecomposition
          DX DZ stableDX hstableDX) := by
        exact externalProduct_graphTransfer_id_right family category DX DZ stableDX hstableDX f
    _ = SmCorQ.graphTransfer category
        (overBaseProductMap f (𝟙 Z))
        DProduct := by
        exact SmCorQ.graphTransfer_independent category
          (overBaseProductMap f (𝟙 Z))
          (_root_.Boundary.finiteProductSourceIrreducibleComponentDecomposition
            DX DZ stableDX hstableDX)
          DProduct

/-- Left-handed graph-transfer tensor identity. -/
theorem externalProduct_id_left_graphTransfer
    (family : FiniteCorrespondence.GraphIdentityCompatibleExternalProductFamily (k := k))
    (category : SmCorQ (k := k))
    {X Y Z : Geometry.SmSchemeOver k}
    (DX : FiniteIrreducibleComponentDecomposition X)
    (DY : FiniteIrreducibleComponentDecomposition Y)
    (stableDX :
      (listed : { listed : SourceIrreducibleComponent X // listed ∈ DX.components }) →
        ProductStableSourceComponent X)
    (hstableDX : ∀ listed, (stableDX listed).component = listed.1)
    (g : SmOverHom Y Z) :
    FiniteCorrespondence.toRational
        (FiniteCorrespondence.externalProductWithFamily family.family
          DX.identityFiniteCorrespondence
          (Geometry.ordinaryMorphismGraph_finiteCorrespondenceOfDecomposition g DY)) =
      SmCorQ.graphTransfer category
        (overBaseProductMap (𝟙 X) g)
        (_root_.Boundary.finiteProductSourceIrreducibleComponentDecomposition
          DX DY stableDX hstableDX) := by
  calc
    FiniteCorrespondence.toRational
        (FiniteCorrespondence.externalProductWithFamily family.family
          DX.identityFiniteCorrespondence
          (Geometry.ordinaryMorphismGraph_finiteCorrespondenceOfDecomposition g DY))
      = FiniteCorrespondence.toRational
          (∑ p in DX.components.attach.product DY.components.attach,
            FiniteCorrespondence.ofPrimeSupport
              (graphExternalProductPrimeSupport_id_left (stableDX p.1) p.2.1 g)) := by
          exact congrArg FiniteCorrespondence.toRational
            (externalProduct_id_left_graphTransfer_eq_sum
              family DX DY stableDX hstableDX g)
    _ = SmCorQ.graphTransfer category
        (overBaseProductMap (𝟙 X) g)
        (_root_.Boundary.finiteProductSourceIrreducibleComponentDecomposition
          DX DY stableDX hstableDX) := by
          exact (graphTransfer_overBaseProductMap_id_left
            category DX DY stableDX hstableDX g).symm

/-- Tensoring an identity correspondence on the left by the graph transfer of
`g` may target any certified decomposition of the product object, since graph
transfer is independent of the chosen source decomposition. -/
theorem externalProduct_id_left_graphTransfer_of_product_decomposition
    (family : FiniteCorrespondence.GraphIdentityCompatibleExternalProductFamily (k := k))
    (category : SmCorQ (k := k))
    {X Y Z : Geometry.SmSchemeOver k}
    (DX : FiniteIrreducibleComponentDecomposition X)
    (DY : FiniteIrreducibleComponentDecomposition Y)
    (stableDX :
      (listed : { listed : SourceIrreducibleComponent X // listed ∈ DX.components }) →
        ProductStableSourceComponent X)
    (hstableDX : ∀ listed, (stableDX listed).component = listed.1)
    (DProduct : FiniteIrreducibleComponentDecomposition (overBaseProductObject X Y))
    (g : SmOverHom Y Z) :
    FiniteCorrespondence.toRational
        (FiniteCorrespondence.externalProductWithFamily family.family
          DX.identityFiniteCorrespondence
          (Geometry.ordinaryMorphismGraph_finiteCorrespondenceOfDecomposition g DY)) =
      SmCorQ.graphTransfer category
        (overBaseProductMap (𝟙 X) g)
        DProduct := by
  calc
    FiniteCorrespondence.toRational
        (FiniteCorrespondence.externalProductWithFamily family.family
          DX.identityFiniteCorrespondence
          (Geometry.ordinaryMorphismGraph_finiteCorrespondenceOfDecomposition g DY)) =
      SmCorQ.graphTransfer category
        (overBaseProductMap (𝟙 X) g)
        (_root_.Boundary.finiteProductSourceIrreducibleComponentDecomposition
          DX DY stableDX hstableDX) := by
        exact externalProduct_id_left_graphTransfer family category DX DY stableDX hstableDX g
    _ = SmCorQ.graphTransfer category
        (overBaseProductMap (𝟙 X) g)
        DProduct := by
        exact SmCorQ.graphTransfer_independent category
          (overBaseProductMap (𝟙 X) g)
          (_root_.Boundary.finiteProductSourceIrreducibleComponentDecomposition
            DX DY stableDX hstableDX)
          DProduct

/-- Clean correspondence-level identity theorem for a graph-compatible
external-product owner under locally irreducible product-model geometry. -/
theorem externalProduct_identity_identity_eq_identityFiniteCorrespondence_of_locallyIrreducible
    (family : FiniteCorrespondence.GraphIdentityCompatibleExternalProductFamily (k := k))
    {X Y : Geometry.SmSchemeOver k}
    (DX : FiniteIrreducibleComponentDecomposition X)
    (DY : FiniteIrreducibleComponentDecomposition Y)
    (DProduct : FiniteIrreducibleComponentDecomposition (overBaseProductObject X Y))
    (hLoc :
      ∀ (sourceX : { sourceX : SourceIrreducibleComponent X // sourceX ∈ DX.components })
        (sourceY : { sourceY : SourceIrreducibleComponent Y // sourceY ∈ DY.components }),
        Geometry.Topology.LocallyIrreducibleSpace
          (product_diagonal_smoothObject (k := k) sourceX.1 sourceY.1).scheme)
    (hIntegral :
      ∀ (sourceX : { sourceX : SourceIrreducibleComponent X // sourceX ∈ DX.components })
        (sourceY : { sourceY : SourceIrreducibleComponent Y // sourceY ∈ DY.components }),
        ∀ C :
          { C : Set (product_diagonal_smoothObject (k := k) sourceX.1 sourceY.1).scheme //
              C ∈ irreducibleComponents
                (product_diagonal_smoothObject (k := k) sourceX.1 sourceY.1).scheme },
          IsIntegral
            (Scheme.Opens.toScheme
              (⟨C.1,
                Geometry.Topology.isOpen_irreducibleComponent_of_locallyIrreducible
                  C.2 (hLoc sourceX sourceY)⟩ :
                (product_diagonal_smoothObject (k := k) sourceX.1 sourceY.1).scheme.Opens))) :
    FiniteCorrespondence.externalProductWithFamily family.family
        DX.identityFiniteCorrespondence DY.identityFiniteCorrespondence =
      DProduct.identityFiniteCorrespondence := by
  exact
    FiniteCorrespondence
      .externalProductWithFamily_identity_identity_eq_identityFiniteCorrespondence_of_locallyIrreducible
      (k := k) family.family DX DY DProduct
      (fun sourceX sourceY i =>
        product_diagonal_supportComponentData_toSourceImage_isIso
          (k := k) sourceX.1 sourceY.1
          (FiniteIntegralClosedComponentDecomposition.ofIrreducibleComponentRealization
            (X := pullback
              (SourceIrreducibleComponent.toAmbient sourceX.1 ≫ X.structMap)
              (SourceIrreducibleComponent.toAmbient sourceY.1 ≫ Y.structMap))
            AlgebraicGeometry.finite_irreducibleComponents_of_isNoetherian
            (PrimeFiniteCorrespondenceSupport
              .product_diagonal_smoothObjectRealizationOfLocallyIrreducible
              (k := k) sourceX.1 sourceY.1
              (hLoc sourceX sourceY) (hIntegral sourceX sourceY)))
          i)
      (fun sourceX sourceY i =>
        product_diagonal_supportComponentData_multiplicity
          (k := k) sourceX.1 sourceY.1
          (FiniteIntegralClosedComponentDecomposition.ofIrreducibleComponentRealization
            (X := pullback
              (SourceIrreducibleComponent.toAmbient sourceX.1 ≫ X.structMap)
              (SourceIrreducibleComponent.toAmbient sourceY.1 ≫ Y.structMap))
            AlgebraicGeometry.finite_irreducibleComponents_of_isNoetherian
            (PrimeFiniteCorrespondenceSupport
              .product_diagonal_smoothObjectRealizationOfLocallyIrreducible
              (k := k) sourceX.1 sourceY.1
              (hLoc sourceX sourceY) (hIntegral sourceX sourceY)))
          i)
      hLoc hIntegral

/-- Clean correspondence-level identity theorem for a graph-compatible
external-product owner under reduced locally irreducible product-model
geometry. -/
theorem externalProduct_identity_identity_eq_identityFiniteCorrespondence_of_reducedLocallyIrreducible
    (family : FiniteCorrespondence.GraphIdentityCompatibleExternalProductFamily (k := k))
    {X Y : Geometry.SmSchemeOver k}
    (DX : FiniteIrreducibleComponentDecomposition X)
    (DY : FiniteIrreducibleComponentDecomposition Y)
    (DProduct : FiniteIrreducibleComponentDecomposition (overBaseProductObject X Y))
    (hLoc :
      ∀ (sourceX : { sourceX : SourceIrreducibleComponent X // sourceX ∈ DX.components })
        (sourceY : { sourceY : SourceIrreducibleComponent Y // sourceY ∈ DY.components }),
        Geometry.Topology.LocallyIrreducibleSpace
          (product_diagonal_smoothObject (k := k) sourceX.1 sourceY.1).scheme)
    (hReduced :
      ∀ (sourceX : { sourceX : SourceIrreducibleComponent X // sourceX ∈ DX.components })
        (sourceY : { sourceY : SourceIrreducibleComponent Y // sourceY ∈ DY.components }),
        IsReduced
          (product_diagonal_smoothObject (k := k) sourceX.1 sourceY.1).scheme) :
    FiniteCorrespondence.externalProductWithFamily family.family
        DX.identityFiniteCorrespondence DY.identityFiniteCorrespondence =
      DProduct.identityFiniteCorrespondence := by
  exact
    externalProduct_identity_identity_eq_identityFiniteCorrespondence_of_locallyIrreducible
      family DX DY DProduct hLoc
      (fun sourceX sourceY C => by
        letI := hReduced sourceX sourceY
        exact
          irreducibleComponentOpen_isIntegral_of_isReduced_locallyIrreducible
            (product_diagonal_smoothObject (k := k) sourceX.1 sourceY.1).scheme
            (hLoc sourceX sourceY) C)

/-- Clean correspondence-level identity theorem for a graph-compatible
external-product owner under the alternative bottom geometry route
`IsReduced + irreducible components open` on each product model. -/
theorem externalProduct_identity_identity_eq_identityFiniteCorrespondence_of_reducedComponentsOpen
    (family : FiniteCorrespondence.GraphIdentityCompatibleExternalProductFamily (k := k))
    {X Y : Geometry.SmSchemeOver k}
    (DX : FiniteIrreducibleComponentDecomposition X)
    (DY : FiniteIrreducibleComponentDecomposition Y)
    (DProduct : FiniteIrreducibleComponentDecomposition (overBaseProductObject X Y))
    (hOpen :
      ∀ (sourceX : { sourceX : SourceIrreducibleComponent X // sourceX ∈ DX.components })
        (sourceY : { sourceY : SourceIrreducibleComponent Y // sourceY ∈ DY.components }),
        ∀ C :
          { C : Set (product_diagonal_smoothObject (k := k) sourceX.1 sourceY.1).scheme //
              C ∈ irreducibleComponents
                (product_diagonal_smoothObject (k := k) sourceX.1 sourceY.1).scheme },
          IsOpen C.1)
    (hReduced :
      ∀ (sourceX : { sourceX : SourceIrreducibleComponent X // sourceX ∈ DX.components })
        (sourceY : { sourceY : SourceIrreducibleComponent Y // sourceY ∈ DY.components }),
        IsReduced
          (product_diagonal_smoothObject (k := k) sourceX.1 sourceY.1).scheme) :
    FiniteCorrespondence.externalProductWithFamily family.family
        DX.identityFiniteCorrespondence DY.identityFiniteCorrespondence =
      DProduct.identityFiniteCorrespondence := by
  exact
    FiniteCorrespondence
      .externalProductWithFamily_identity_identity_eq_identityFiniteCorrespondence_of_reduced_componentsOpen
      (k := k) family.family DX DY DProduct
      (fun sourceX sourceY i =>
        product_diagonal_supportComponentData_toSourceImage_isIso
          (k := k) sourceX.1 sourceY.1
          (FiniteIntegralClosedComponentDecomposition.ofIrreducibleComponentRealization
            (X := pullback
              (SourceIrreducibleComponent.toAmbient sourceX.1 ≫ X.structMap)
              (SourceIrreducibleComponent.toAmbient sourceY.1 ≫ Y.structMap))
            AlgebraicGeometry.finite_irreducibleComponents_of_isNoetherian
            (PrimeFiniteCorrespondenceSupport
              .product_diagonal_smoothObjectRealizationOfReducedComponentsOpen
              (k := k) sourceX.1 sourceY.1
              (hOpen sourceX sourceY)))
          i)
      (fun sourceX sourceY i =>
        product_diagonal_supportComponentData_multiplicity
          (k := k) sourceX.1 sourceY.1
          (FiniteIntegralClosedComponentDecomposition.ofIrreducibleComponentRealization
            (X := pullback
              (SourceIrreducibleComponent.toAmbient sourceX.1 ≫ X.structMap)
              (SourceIrreducibleComponent.toAmbient sourceY.1 ≫ Y.structMap))
            AlgebraicGeometry.finite_irreducibleComponents_of_isNoetherian
            (PrimeFiniteCorrespondenceSupport
              .product_diagonal_smoothObjectRealizationOfReducedComponentsOpen
              (k := k) sourceX.1 sourceY.1
              (hOpen sourceX sourceY)))
          i)
      hOpen hReduced

/-- Rational right-identity theorem under locally irreducible product-model
geometry. -/
theorem externalProduct_id_right_of_locallyIrreducible
    (family : FiniteCorrespondence.GraphIdentityCompatibleExternalProductFamily (k := k))
    {X Y : Geometry.SmSchemeOver k}
    (DX : FiniteIrreducibleComponentDecomposition X)
    (DY : FiniteIrreducibleComponentDecomposition Y)
    (DProduct : FiniteIrreducibleComponentDecomposition (overBaseProductObject X Y))
    (hLoc :
      ∀ (sourceX : { sourceX : SourceIrreducibleComponent X // sourceX ∈ DX.components })
        (sourceY : { sourceY : SourceIrreducibleComponent Y // sourceY ∈ DY.components }),
        Geometry.Topology.LocallyIrreducibleSpace
          (product_diagonal_smoothObject (k := k) sourceX.1 sourceY.1).scheme)
    (hIntegral :
      ∀ (sourceX : { sourceX : SourceIrreducibleComponent X // sourceX ∈ DX.components })
        (sourceY : { sourceY : SourceIrreducibleComponent Y // sourceY ∈ DY.components }),
        ∀ C :
          { C : Set (product_diagonal_smoothObject (k := k) sourceX.1 sourceY.1).scheme //
              C ∈ irreducibleComponents
                (product_diagonal_smoothObject (k := k) sourceX.1 sourceY.1).scheme },
          IsIntegral
            (Scheme.Opens.toScheme
              (⟨C.1,
                Geometry.Topology.isOpen_irreducibleComponent_of_locallyIrreducible
                  C.2 (hLoc sourceX sourceY)⟩ :
                (product_diagonal_smoothObject (k := k) sourceX.1 sourceY.1).scheme.Opens))) :
    FiniteCorrespondence.toRational
        (FiniteCorrespondence.externalProductWithFamily family.family
          DX.identityFiniteCorrespondence DY.identityFiniteCorrespondence) =
      FiniteCorrespondence.toRational DProduct.identityFiniteCorrespondence :=
  congrArg FiniteCorrespondence.toRational
    (externalProduct_identity_identity_eq_identityFiniteCorrespondence_of_locallyIrreducible
      family DX DY DProduct hLoc hIntegral)

/-- Rational right-identity theorem under reduced locally irreducible
product-model geometry. -/
theorem externalProduct_id_right_of_reducedLocallyIrreducible
    (family : FiniteCorrespondence.GraphIdentityCompatibleExternalProductFamily (k := k))
    {X Y : Geometry.SmSchemeOver k}
    (DX : FiniteIrreducibleComponentDecomposition X)
    (DY : FiniteIrreducibleComponentDecomposition Y)
    (DProduct : FiniteIrreducibleComponentDecomposition (overBaseProductObject X Y))
    (hLoc :
      ∀ (sourceX : { sourceX : SourceIrreducibleComponent X // sourceX ∈ DX.components })
        (sourceY : { sourceY : SourceIrreducibleComponent Y // sourceY ∈ DY.components }),
        Geometry.Topology.LocallyIrreducibleSpace
          (product_diagonal_smoothObject (k := k) sourceX.1 sourceY.1).scheme)
    (hReduced :
      ∀ (sourceX : { sourceX : SourceIrreducibleComponent X // sourceX ∈ DX.components })
        (sourceY : { sourceY : SourceIrreducibleComponent Y // sourceY ∈ DY.components }),
        IsReduced
          (product_diagonal_smoothObject (k := k) sourceX.1 sourceY.1).scheme) :
    FiniteCorrespondence.toRational
        (FiniteCorrespondence.externalProductWithFamily family.family
          DX.identityFiniteCorrespondence DY.identityFiniteCorrespondence) =
      FiniteCorrespondence.toRational DProduct.identityFiniteCorrespondence :=
  congrArg FiniteCorrespondence.toRational
    (externalProduct_identity_identity_eq_identityFiniteCorrespondence_of_reducedLocallyIrreducible
      family DX DY DProduct hLoc hReduced)

/-- Rational right-identity theorem under the alternative bottom geometry
route `IsReduced + irreducible components open` on each product model. -/
theorem externalProduct_id_right_of_reducedComponentsOpen
    (family : FiniteCorrespondence.GraphIdentityCompatibleExternalProductFamily (k := k))
    {X Y : Geometry.SmSchemeOver k}
    (DX : FiniteIrreducibleComponentDecomposition X)
    (DY : FiniteIrreducibleComponentDecomposition Y)
    (DProduct : FiniteIrreducibleComponentDecomposition (overBaseProductObject X Y))
    (hOpen :
      ∀ (sourceX : { sourceX : SourceIrreducibleComponent X // sourceX ∈ DX.components })
        (sourceY : { sourceY : SourceIrreducibleComponent Y // sourceY ∈ DY.components }),
        ∀ C :
          { C : Set (product_diagonal_smoothObject (k := k) sourceX.1 sourceY.1).scheme //
              C ∈ irreducibleComponents
                (product_diagonal_smoothObject (k := k) sourceX.1 sourceY.1).scheme },
          IsOpen C.1)
    (hReduced :
      ∀ (sourceX : { sourceX : SourceIrreducibleComponent X // sourceX ∈ DX.components })
        (sourceY : { sourceY : SourceIrreducibleComponent Y // sourceY ∈ DY.components }),
        IsReduced
          (product_diagonal_smoothObject (k := k) sourceX.1 sourceY.1).scheme) :
    FiniteCorrespondence.toRational
        (FiniteCorrespondence.externalProductWithFamily family.family
          DX.identityFiniteCorrespondence DY.identityFiniteCorrespondence) =
      FiniteCorrespondence.toRational DProduct.identityFiniteCorrespondence :=
  congrArg FiniteCorrespondence.toRational
    (externalProduct_identity_identity_eq_identityFiniteCorrespondence_of_reducedComponentsOpen
      family DX DY DProduct hOpen hReduced)

/-- Rational right-identity theorem under the route
`components open + relative-dimension-zero standard-smooth affine charts`
on each product model. -/
theorem externalProduct_id_right_of_standardSmoothOfRelativeDimensionZeroComponentsOpen
    (family : FiniteCorrespondence.GraphIdentityCompatibleExternalProductFamily (k := k))
    {X Y : Geometry.SmSchemeOver k}
    (DX : FiniteIrreducibleComponentDecomposition X)
    (DY : FiniteIrreducibleComponentDecomposition Y)
    (DProduct : FiniteIrreducibleComponentDecomposition (overBaseProductObject X Y))
    (hOpen :
      ∀ (sourceX : { sourceX : SourceIrreducibleComponent X // sourceX ∈ DX.components })
        (sourceY : { sourceY : SourceIrreducibleComponent Y // sourceY ∈ DY.components }),
        ∀ C :
          { C : Set (product_diagonal_smoothObject (k := k) sourceX.1 sourceY.1).scheme //
              C ∈ irreducibleComponents
                (product_diagonal_smoothObject (k := k) sourceX.1 sourceY.1).scheme },
          IsOpen C.1)
    (hStd0 :
      ∀ (sourceX : { sourceX : SourceIrreducibleComponent X // sourceX ∈ DX.components })
        (sourceY : { sourceY : SourceIrreducibleComponent Y // sourceY ∈ DY.components })
        (x : (product_diagonal_smoothObject (k := k) sourceX.1 sourceY.1).scheme),
        ∃ U :
          (product_diagonal_smoothObject (k := k) sourceX.1 sourceY.1).scheme.affineOpens,
          x ∈ U.1 ∧
          Algebra.IsStandardSmoothOfRelativeDimension 0 k
            (Γ((product_diagonal_smoothObject (k := k) sourceX.1 sourceY.1).scheme, U))) :
    FiniteCorrespondence.toRational
        (FiniteCorrespondence.externalProductWithFamily family.family
          DX.identityFiniteCorrespondence DY.identityFiniteCorrespondence) =
      FiniteCorrespondence.toRational DProduct.identityFiniteCorrespondence :=
  congrArg FiniteCorrespondence.toRational
    (FiniteCorrespondence
      .externalProductWithFamily_identity_identity_eq_identityFiniteCorrespondence_of_standardSmoothOfRelativeDimensionZero_componentsOpen
      (k := k) family.family DX DY DProduct
      (fun sourceX sourceY i =>
        product_diagonal_supportComponentData_toSourceImage_isIso
          (k := k) sourceX.1 sourceY.1
          (FiniteIntegralClosedComponentDecomposition.ofIrreducibleComponentRealization
            (X := pullback
              (SourceIrreducibleComponent.toAmbient sourceX.1 ≫ X.structMap)
              (SourceIrreducibleComponent.toAmbient sourceY.1 ≫ Y.structMap))
            AlgebraicGeometry.finite_irreducibleComponents_of_isNoetherian
            (PrimeFiniteCorrespondenceSupport
              .product_diagonal_smoothObjectRealizationOfReducedComponentsOpen
              (k := k) sourceX.1 sourceY.1
              (hOpen sourceX sourceY)))
          i)
      (fun sourceX sourceY i =>
        product_diagonal_supportComponentData_multiplicity
          (k := k) sourceX.1 sourceY.1
          (FiniteIntegralClosedComponentDecomposition.ofIrreducibleComponentRealization
            (X := pullback
              (SourceIrreducibleComponent.toAmbient sourceX.1 ≫ X.structMap)
              (SourceIrreducibleComponent.toAmbient sourceY.1 ≫ Y.structMap))
            AlgebraicGeometry.finite_irreducibleComponents_of_isNoetherian
            (PrimeFiniteCorrespondenceSupport
              .product_diagonal_smoothObjectRealizationOfReducedComponentsOpen
              (k := k) sourceX.1 sourceY.1
              (hOpen sourceX sourceY)))
          i)
      hOpen hStd0)

/-- Rational right-identity theorem under the route
`reduced locally irreducible + relative-dimension-zero standard-smooth affine charts`
on each product model. -/
theorem externalProduct_id_right_of_standardSmoothOfRelativeDimensionZeroReducedLocallyIrreducible
    (family : FiniteCorrespondence.GraphIdentityCompatibleExternalProductFamily (k := k))
    {X Y : Geometry.SmSchemeOver k}
    (DX : FiniteIrreducibleComponentDecomposition X)
    (DY : FiniteIrreducibleComponentDecomposition Y)
    (DProduct : FiniteIrreducibleComponentDecomposition (overBaseProductObject X Y))
    (hStd0 :
      ∀ (sourceX : { sourceX : SourceIrreducibleComponent X // sourceX ∈ DX.components })
        (sourceY : { sourceY : SourceIrreducibleComponent Y // sourceY ∈ DY.components })
        (x : (product_diagonal_smoothObject (k := k) sourceX.1 sourceY.1).scheme),
        ∃ U :
          (product_diagonal_smoothObject (k := k) sourceX.1 sourceY.1).scheme.affineOpens,
          x ∈ U.1 ∧
          Algebra.IsStandardSmoothOfRelativeDimension 0 k
            (Γ((product_diagonal_smoothObject (k := k) sourceX.1 sourceY.1).scheme, U))) :
    FiniteCorrespondence.toRational
        (FiniteCorrespondence.externalProductWithFamily family.family
          DX.identityFiniteCorrespondence DY.identityFiniteCorrespondence) =
      FiniteCorrespondence.toRational DProduct.identityFiniteCorrespondence :=
  congrArg FiniteCorrespondence.toRational
    (FiniteCorrespondence
      .externalProductWithFamily_identity_identity_eq_identityFiniteCorrespondence_of_standardSmoothOfRelativeDimensionZero_reducedLocallyIrreducible
      (k := k) family.family DX DY DProduct
      (fun sourceX sourceY i =>
        product_diagonal_supportComponentData_toSourceImage_isIso
          (k := k) sourceX.1 sourceY.1
          (FiniteIntegralClosedComponentDecomposition.ofIrreducibleComponentRealization
            (X := pullback
              (SourceIrreducibleComponent.toAmbient sourceX.1 ≫ X.structMap)
              (SourceIrreducibleComponent.toAmbient sourceY.1 ≫ Y.structMap))
            AlgebraicGeometry.finite_irreducibleComponents_of_isNoetherian
            (PrimeFiniteCorrespondenceSupport
              .product_diagonal_smoothObjectRealizationOfReducedLocallyIrreducible
              (k := k) sourceX.1 sourceY.1
              (product_diagonal_smoothObject_locallyIrreducible_of_standardSmoothOfRelativeDimensionZeroAffine
                (k := k) sourceX.1 sourceY.1 (hStd0 sourceX sourceY))
              (product_diagonal_smoothObject_isReduced_of_standardSmoothOfRelativeDimensionZeroAffine
                (k := k) sourceX.1 sourceY.1 (hStd0 sourceX sourceY))))
          i)
      (fun sourceX sourceY i =>
        product_diagonal_supportComponentData_multiplicity
          (k := k) sourceX.1 sourceY.1
          (FiniteIntegralClosedComponentDecomposition.ofIrreducibleComponentRealization
            (X := pullback
              (SourceIrreducibleComponent.toAmbient sourceX.1 ≫ X.structMap)
              (SourceIrreducibleComponent.toAmbient sourceY.1 ≫ Y.structMap))
            AlgebraicGeometry.finite_irreducibleComponents_of_isNoetherian
            (PrimeFiniteCorrespondenceSupport
              .product_diagonal_smoothObjectRealizationOfReducedLocallyIrreducible
              (k := k) sourceX.1 sourceY.1
              (product_diagonal_smoothObject_locallyIrreducible_of_standardSmoothOfRelativeDimensionZeroAffine
                (k := k) sourceX.1 sourceY.1 (hStd0 sourceX sourceY))
              (product_diagonal_smoothObject_isReduced_of_standardSmoothOfRelativeDimensionZeroAffine
                (k := k) sourceX.1 sourceY.1 (hStd0 sourceX sourceY))))
          i)
      hStd0)

end FiniteCorrespondence.GraphIdentityCompatibleExternalProductFamily

namespace FiniteCorrespondence

namespace TensorCompatibleExternalProductFamily

/-- Full correspondence-level external-product/compose interchange exported
from the tensor-compatible owner package. -/
theorem externalProduct_comp_interchange
    (family : TensorCompatibleExternalProductFamily (k := k))
    (compData : FiniteCorrespondenceCompositionData (k := k))
    {W1 X1 Y1 W2 X2 Y2 : Geometry.SmSchemeOver k}
    (f : FiniteCorrespondence W1 X1)
    (g : FiniteCorrespondence X1 Y1)
    (f' : FiniteCorrespondence W2 X2)
    (g' : FiniteCorrespondence X2 Y2) :
    externalProductWithFamily family.family
        (FiniteCorrespondenceCompositionData.comp compData f g)
        (FiniteCorrespondenceCompositionData.comp compData f' g')
      =
        FiniteCorrespondenceCompositionData.comp compData
          (externalProductWithFamily family.family f f')
          (externalProductWithFamily family.family g g') := by
  exact externalProductWithFamily_comp_interchange_of_primes
    (family := family.family) compData
    (fun f g f' g' =>
      family.externalProduct_compPrime_interchange compData f g f' g')
    f g f' g'

end TensorCompatibleExternalProductFamily

/-- Public owner theorem: a graph-compatible external-product family sends
diagonal identities to the product diagonal identity after rationalization. -/
theorem externalProductWithFamily_identity_identity_eq_identityFiniteCorrespondence
    (family : GraphIdentityCompatibleExternalProductFamily (k := k))
    {X Y : Geometry.SmSchemeOver k}
    (DX : FiniteIrreducibleComponentDecomposition X)
    (DY : FiniteIrreducibleComponentDecomposition Y)
    (stableDX :
      (listed : { listed : SourceIrreducibleComponent X // listed ∈ DX.components }) →
        ProductStableSourceComponent X)
    (hstableDX : ∀ listed, (stableDX listed).component = listed.1) :
    externalProductWithFamily family.family
        DX.identityFiniteCorrespondence DY.identityFiniteCorrespondence =
      (_root_.Boundary.finiteProductSourceIrreducibleComponentDecomposition
        DX DY stableDX hstableDX).identityFiniteCorrespondence :=
  GraphIdentityCompatibleExternalProductFamily
    .externalProduct_identity_identity_eq_identityFiniteCorrespondence
    family DX DY stableDX hstableDX

/-- Public owner theorem: a graph-compatible external-product family sends
diagonal identities to the product diagonal identity after rationalization. -/
theorem externalProduct_id_right
    (family : GraphIdentityCompatibleExternalProductFamily (k := k))
    (category : SmCorQ (k := k))
    {X Z : Geometry.SmSchemeOver k}
    (DX : FiniteIrreducibleComponentDecomposition X)
    (DZ : FiniteIrreducibleComponentDecomposition Z)
    (stableDX :
      (listed : { listed : SourceIrreducibleComponent X // listed ∈ DX.components }) →
        ProductStableSourceComponent X)
    (hstableDX : ∀ listed, (stableDX listed).component = listed.1) :
    FiniteCorrespondence.toRational
        (externalProductWithFamily family.family
          DX.identityFiniteCorrespondence DZ.identityFiniteCorrespondence) =
      FiniteCorrespondence.toRational
        ((_root_.Boundary.finiteProductSourceIrreducibleComponentDecomposition
          DX DZ stableDX hstableDX).identityFiniteCorrespondence) :=
  congrArg FiniteCorrespondence.toRational
    (externalProductWithFamily_identity_identity_eq_identityFiniteCorrespondence
      family DX DZ stableDX hstableDX)

/-- The right identity theorem may target any certified decomposition of the
product object. The proof is the owner identity theorem for the product
listing, followed by independence of the diagonal identity correspondence from
the chosen finite irreducible-component decomposition. -/
theorem externalProduct_id_right_of_product_decomposition
    (family : GraphIdentityCompatibleExternalProductFamily (k := k))
    (category : SmCorQ (k := k))
    {X Z : Geometry.SmSchemeOver k}
    (DX : FiniteIrreducibleComponentDecomposition X)
    (DZ : FiniteIrreducibleComponentDecomposition Z)
    (stableDX :
      (listed : { listed : SourceIrreducibleComponent X // listed ∈ DX.components }) →
        ProductStableSourceComponent X)
    (hstableDX : ∀ listed, (stableDX listed).component = listed.1)
    (DProduct :
      FiniteIrreducibleComponentDecomposition (overBaseProductObject X Z)) :
    FiniteCorrespondence.toRational
        (externalProductWithFamily family.family
          DX.identityFiniteCorrespondence DZ.identityFiniteCorrespondence) =
      FiniteCorrespondence.toRational DProduct.identityFiniteCorrespondence := by
  calc
    FiniteCorrespondence.toRational
        (externalProductWithFamily family.family
          DX.identityFiniteCorrespondence DZ.identityFiniteCorrespondence) =
      FiniteCorrespondence.toRational
        ((_root_.Boundary.finiteProductSourceIrreducibleComponentDecomposition
          DX DZ stableDX hstableDX).identityFiniteCorrespondence) := by
        exact externalProduct_id_right family category DX DZ stableDX hstableDX
    _ = FiniteCorrespondence.toRational DProduct.identityFiniteCorrespondence := by
        exact congrArg FiniteCorrespondence.toRational
          (FiniteIrreducibleComponentDecomposition.identityFiniteCorrespondence_independent
            (_root_.Boundary.finiteProductSourceIrreducibleComponentDecomposition
              DX DZ stableDX hstableDX)
            DProduct)

/-- Public owner theorem: a graph-compatible external-product family sends
diagonal identities to the product diagonal identity under locally irreducible
product-model geometry. -/
theorem externalProductWithFamily_identity_identity_eq_identityFiniteCorrespondence_of_locallyIrreducible
    (family : GraphIdentityCompatibleExternalProductFamily (k := k))
    {X Y : Geometry.SmSchemeOver k}
    (DX : FiniteIrreducibleComponentDecomposition X)
    (DY : FiniteIrreducibleComponentDecomposition Y)
    (DProduct : FiniteIrreducibleComponentDecomposition (overBaseProductObject X Y))
    (hLoc :
      ∀ (sourceX : { sourceX : SourceIrreducibleComponent X // sourceX ∈ DX.components })
        (sourceY : { sourceY : SourceIrreducibleComponent Y // sourceY ∈ DY.components }),
        Geometry.Topology.LocallyIrreducibleSpace
          (product_diagonal_smoothObject (k := k) sourceX.1 sourceY.1).scheme)
    (hIntegral :
      ∀ (sourceX : { sourceX : SourceIrreducibleComponent X // sourceX ∈ DX.components })
        (sourceY : { sourceY : SourceIrreducibleComponent Y // sourceY ∈ DY.components }),
        ∀ C :
          { C : Set (product_diagonal_smoothObject (k := k) sourceX.1 sourceY.1).scheme //
              C ∈ irreducibleComponents
                (product_diagonal_smoothObject (k := k) sourceX.1 sourceY.1).scheme },
          IsIntegral
            (Scheme.Opens.toScheme
              (⟨C.1,
                Geometry.Topology.isOpen_irreducibleComponent_of_locallyIrreducible
                  C.2 (hLoc sourceX sourceY)⟩ :
                (product_diagonal_smoothObject (k := k) sourceX.1 sourceY.1).scheme.Opens))) :
    externalProductWithFamily family.family
        DX.identityFiniteCorrespondence DY.identityFiniteCorrespondence =
      DProduct.identityFiniteCorrespondence :=
  GraphIdentityCompatibleExternalProductFamily
    .externalProduct_identity_identity_eq_identityFiniteCorrespondence_of_locallyIrreducible
    family DX DY DProduct hLoc hIntegral

/-- Public owner theorem: a graph-compatible external-product family sends
diagonal identities to the product diagonal identity under reduced locally
irreducible product-model geometry. -/
theorem externalProductWithFamily_identity_identity_eq_identityFiniteCorrespondence_of_reducedLocallyIrreducible
    (family : GraphIdentityCompatibleExternalProductFamily (k := k))
    {X Y : Geometry.SmSchemeOver k}
    (DX : FiniteIrreducibleComponentDecomposition X)
    (DY : FiniteIrreducibleComponentDecomposition Y)
    (DProduct : FiniteIrreducibleComponentDecomposition (overBaseProductObject X Y))
    (hLoc :
      ∀ (sourceX : { sourceX : SourceIrreducibleComponent X // sourceX ∈ DX.components })
        (sourceY : { sourceY : SourceIrreducibleComponent Y // sourceY ∈ DY.components }),
        Geometry.Topology.LocallyIrreducibleSpace
          (product_diagonal_smoothObject (k := k) sourceX.1 sourceY.1).scheme)
    (hReduced :
      ∀ (sourceX : { sourceX : SourceIrreducibleComponent X // sourceX ∈ DX.components })
        (sourceY : { sourceY : SourceIrreducibleComponent Y // sourceY ∈ DY.components }),
        IsReduced
          (product_diagonal_smoothObject (k := k) sourceX.1 sourceY.1).scheme) :
    externalProductWithFamily family.family
        DX.identityFiniteCorrespondence DY.identityFiniteCorrespondence =
      DProduct.identityFiniteCorrespondence :=
  GraphIdentityCompatibleExternalProductFamily
    .externalProduct_identity_identity_eq_identityFiniteCorrespondence_of_reducedLocallyIrreducible
    family DX DY DProduct hLoc hReduced

/-- Public owner theorem: a graph-compatible external-product family sends
diagonal identities to the product diagonal identity under the alternative
bottom geometry route `IsReduced + irreducible components open`. -/
theorem externalProductWithFamily_identity_identity_eq_identityFiniteCorrespondence_of_reducedComponentsOpen
    (family : GraphIdentityCompatibleExternalProductFamily (k := k))
    {X Y : Geometry.SmSchemeOver k}
    (DX : FiniteIrreducibleComponentDecomposition X)
    (DY : FiniteIrreducibleComponentDecomposition Y)
    (DProduct : FiniteIrreducibleComponentDecomposition (overBaseProductObject X Y))
    (hOpen :
      ∀ (sourceX : { sourceX : SourceIrreducibleComponent X // sourceX ∈ DX.components })
        (sourceY : { sourceY : SourceIrreducibleComponent Y // sourceY ∈ DY.components }),
        ∀ C :
          { C : Set (product_diagonal_smoothObject (k := k) sourceX.1 sourceY.1).scheme //
              C ∈ irreducibleComponents
                (product_diagonal_smoothObject (k := k) sourceX.1 sourceY.1).scheme },
          IsOpen C.1)
    (hReduced :
      ∀ (sourceX : { sourceX : SourceIrreducibleComponent X // sourceX ∈ DX.components })
        (sourceY : { sourceY : SourceIrreducibleComponent Y // sourceY ∈ DY.components }),
        IsReduced
          (product_diagonal_smoothObject (k := k) sourceX.1 sourceY.1).scheme) :
    externalProductWithFamily family.family
        DX.identityFiniteCorrespondence DY.identityFiniteCorrespondence =
      DProduct.identityFiniteCorrespondence :=
  GraphIdentityCompatibleExternalProductFamily
    .externalProduct_identity_identity_eq_identityFiniteCorrespondence_of_reducedComponentsOpen
    family DX DY DProduct hOpen hReduced

/-- Public owner theorem: a graph-compatible external-product family sends
diagonal identities to the product diagonal identity under the route
`components open + relative-dimension-zero standard-smooth affine charts`
on each product model. -/
theorem externalProductWithFamily_identity_identity_eq_identityFiniteCorrespondence_of_standardSmoothOfRelativeDimensionZeroComponentsOpen
    (family : GraphIdentityCompatibleExternalProductFamily (k := k))
    {X Y : Geometry.SmSchemeOver k}
    (DX : FiniteIrreducibleComponentDecomposition X)
    (DY : FiniteIrreducibleComponentDecomposition Y)
    (DProduct : FiniteIrreducibleComponentDecomposition (overBaseProductObject X Y))
    (hOpen :
      ∀ (sourceX : { sourceX : SourceIrreducibleComponent X // sourceX ∈ DX.components })
        (sourceY : { sourceY : SourceIrreducibleComponent Y // sourceY ∈ DY.components }),
        ∀ C :
          { C : Set (product_diagonal_smoothObject (k := k) sourceX.1 sourceY.1).scheme //
              C ∈ irreducibleComponents
                (product_diagonal_smoothObject (k := k) sourceX.1 sourceY.1).scheme },
          IsOpen C.1)
    (hStd0 :
      ∀ (sourceX : { sourceX : SourceIrreducibleComponent X // sourceX ∈ DX.components })
        (sourceY : { sourceY : SourceIrreducibleComponent Y // sourceY ∈ DY.components })
        (x : (product_diagonal_smoothObject (k := k) sourceX.1 sourceY.1).scheme),
        ∃ U :
          (product_diagonal_smoothObject (k := k) sourceX.1 sourceY.1).scheme.affineOpens,
          x ∈ U.1 ∧
          Algebra.IsStandardSmoothOfRelativeDimension 0 k
            (Γ((product_diagonal_smoothObject (k := k) sourceX.1 sourceY.1).scheme, U))) :
    externalProductWithFamily family.family
        DX.identityFiniteCorrespondence DY.identityFiniteCorrespondence =
      DProduct.identityFiniteCorrespondence :=
  GraphIdentityCompatibleExternalProductFamily
    .externalProduct_identity_identity_eq_identityFiniteCorrespondence_of_standardSmoothOfRelativeDimensionZero_componentsOpen
    family DX DY DProduct hOpen hStd0

/-- Public owner theorem: a graph-compatible external-product family sends
diagonal identities to the product diagonal identity under the route
`reduced locally irreducible + relative-dimension-zero standard-smooth affine charts`
on each product model. -/
theorem externalProductWithFamily_identity_identity_eq_identityFiniteCorrespondence_of_standardSmoothOfRelativeDimensionZeroReducedLocallyIrreducible
    (family : GraphIdentityCompatibleExternalProductFamily (k := k))
    {X Y : Geometry.SmSchemeOver k}
    (DX : FiniteIrreducibleComponentDecomposition X)
    (DY : FiniteIrreducibleComponentDecomposition Y)
    (DProduct : FiniteIrreducibleComponentDecomposition (overBaseProductObject X Y))
    (hStd0 :
      ∀ (sourceX : { sourceX : SourceIrreducibleComponent X // sourceX ∈ DX.components })
        (sourceY : { sourceY : SourceIrreducibleComponent Y // sourceY ∈ DY.components })
        (x : (product_diagonal_smoothObject (k := k) sourceX.1 sourceY.1).scheme),
        ∃ U :
          (product_diagonal_smoothObject (k := k) sourceX.1 sourceY.1).scheme.affineOpens,
          x ∈ U.1 ∧
          Algebra.IsStandardSmoothOfRelativeDimension 0 k
            (Γ((product_diagonal_smoothObject (k := k) sourceX.1 sourceY.1).scheme, U))) :
    externalProductWithFamily family.family
        DX.identityFiniteCorrespondence DY.identityFiniteCorrespondence =
      DProduct.identityFiniteCorrespondence :=
  GraphIdentityCompatibleExternalProductFamily
    .externalProduct_identity_identity_eq_identityFiniteCorrespondence_of_standardSmoothOfRelativeDimensionZeroReducedLocallyIrreducible
    family DX DY DProduct hStd0

/-- Rational right identity theorem under locally irreducible product-model
geometry. -/
theorem externalProduct_id_right_of_locallyIrreducible
    (family : GraphIdentityCompatibleExternalProductFamily (k := k))
    (category : SmCorQ (k := k))
    {X Z : Geometry.SmSchemeOver k}
    (DX : FiniteIrreducibleComponentDecomposition X)
    (DZ : FiniteIrreducibleComponentDecomposition Z)
    (DProduct : FiniteIrreducibleComponentDecomposition (overBaseProductObject X Z))
    (hLoc :
      ∀ (sourceX : { sourceX : SourceIrreducibleComponent X // sourceX ∈ DX.components })
        (sourceZ : { sourceY : SourceIrreducibleComponent Z // sourceY ∈ DZ.components }),
        Geometry.Topology.LocallyIrreducibleSpace
          (product_diagonal_smoothObject (k := k) sourceX.1 sourceZ.1).scheme)
    (hIntegral :
      ∀ (sourceX : { sourceX : SourceIrreducibleComponent X // sourceX ∈ DX.components })
        (sourceZ : { sourceY : SourceIrreducibleComponent Z // sourceY ∈ DZ.components }),
        ∀ C :
          { C : Set (product_diagonal_smoothObject (k := k) sourceX.1 sourceZ.1).scheme //
              C ∈ irreducibleComponents
                (product_diagonal_smoothObject (k := k) sourceX.1 sourceZ.1).scheme },
          IsIntegral
            (Scheme.Opens.toScheme
              (⟨C.1,
                Geometry.Topology.isOpen_irreducibleComponent_of_locallyIrreducible
                  C.2 (hLoc sourceX sourceZ)⟩ :
                (product_diagonal_smoothObject (k := k) sourceX.1 sourceZ.1).scheme.Opens))) :
    FiniteCorrespondence.toRational
        (externalProductWithFamily family.family
          DX.identityFiniteCorrespondence DZ.identityFiniteCorrespondence) =
      FiniteCorrespondence.toRational DProduct.identityFiniteCorrespondence :=
  GraphIdentityCompatibleExternalProductFamily.externalProduct_id_right_of_locallyIrreducible
    family DX DZ DProduct hLoc hIntegral

/-- Rational right identity theorem under reduced locally irreducible
product-model geometry. -/
theorem externalProduct_id_right_of_reducedLocallyIrreducible
    (family : GraphIdentityCompatibleExternalProductFamily (k := k))
    (category : SmCorQ (k := k))
    {X Z : Geometry.SmSchemeOver k}
    (DX : FiniteIrreducibleComponentDecomposition X)
    (DZ : FiniteIrreducibleComponentDecomposition Z)
    (DProduct : FiniteIrreducibleComponentDecomposition (overBaseProductObject X Z))
    (hLoc :
      ∀ (sourceX : { sourceX : SourceIrreducibleComponent X // sourceX ∈ DX.components })
        (sourceZ : { sourceY : SourceIrreducibleComponent Z // sourceY ∈ DZ.components }),
        Geometry.Topology.LocallyIrreducibleSpace
          (product_diagonal_smoothObject (k := k) sourceX.1 sourceZ.1).scheme)
    (hReduced :
      ∀ (sourceX : { sourceX : SourceIrreducibleComponent X // sourceX ∈ DX.components })
        (sourceZ : { sourceY : SourceIrreducibleComponent Z // sourceY ∈ DZ.components }),
        IsReduced
          (product_diagonal_smoothObject (k := k) sourceX.1 sourceZ.1).scheme) :
    FiniteCorrespondence.toRational
        (externalProductWithFamily family.family
          DX.identityFiniteCorrespondence DZ.identityFiniteCorrespondence) =
      FiniteCorrespondence.toRational DProduct.identityFiniteCorrespondence :=
  GraphIdentityCompatibleExternalProductFamily.externalProduct_id_right_of_reducedLocallyIrreducible
    family DX DZ DProduct hLoc hReduced

/-- Rational right identity theorem under the alternative bottom geometry
route `IsReduced + irreducible components open`. -/
theorem externalProduct_id_right_of_reducedComponentsOpen
    (family : GraphIdentityCompatibleExternalProductFamily (k := k))
    (category : SmCorQ (k := k))
    {X Z : Geometry.SmSchemeOver k}
    (DX : FiniteIrreducibleComponentDecomposition X)
    (DZ : FiniteIrreducibleComponentDecomposition Z)
    (DProduct : FiniteIrreducibleComponentDecomposition (overBaseProductObject X Z))
    (hOpen :
      ∀ (sourceX : { sourceX : SourceIrreducibleComponent X // sourceX ∈ DX.components })
        (sourceZ : { sourceY : SourceIrreducibleComponent Z // sourceY ∈ DZ.components }),
        ∀ C :
          { C : Set (product_diagonal_smoothObject (k := k) sourceX.1 sourceZ.1).scheme //
              C ∈ irreducibleComponents
                (product_diagonal_smoothObject (k := k) sourceX.1 sourceZ.1).scheme },
          IsOpen C.1)
    (hReduced :
      ∀ (sourceX : { sourceX : SourceIrreducibleComponent X // sourceX ∈ DX.components })
        (sourceZ : { sourceY : SourceIrreducibleComponent Z // sourceY ∈ DZ.components }),
        IsReduced
          (product_diagonal_smoothObject (k := k) sourceX.1 sourceZ.1).scheme) :
    FiniteCorrespondence.toRational
        (externalProductWithFamily family.family
          DX.identityFiniteCorrespondence DZ.identityFiniteCorrespondence) =
      FiniteCorrespondence.toRational DProduct.identityFiniteCorrespondence :=
  GraphIdentityCompatibleExternalProductFamily.externalProduct_id_right_of_reducedComponentsOpen
    family DX DZ DProduct hOpen hReduced

/-- Rational right identity theorem under the route
`components open + relative-dimension-zero standard-smooth affine charts`
on each product model. -/
theorem externalProduct_id_right_of_standardSmoothOfRelativeDimensionZeroComponentsOpen
    (family : GraphIdentityCompatibleExternalProductFamily (k := k))
    (category : SmCorQ (k := k))
    {X Z : Geometry.SmSchemeOver k}
    (DX : FiniteIrreducibleComponentDecomposition X)
    (DZ : FiniteIrreducibleComponentDecomposition Z)
    (DProduct : FiniteIrreducibleComponentDecomposition (overBaseProductObject X Z))
    (hOpen :
      ∀ (sourceX : { sourceX : SourceIrreducibleComponent X // sourceX ∈ DX.components })
        (sourceZ : { sourceY : SourceIrreducibleComponent Z // sourceY ∈ DZ.components }),
        ∀ C :
          { C : Set (product_diagonal_smoothObject (k := k) sourceX.1 sourceZ.1).scheme //
              C ∈ irreducibleComponents
                (product_diagonal_smoothObject (k := k) sourceX.1 sourceZ.1).scheme },
          IsOpen C.1)
    (hStd0 :
      ∀ (sourceX : { sourceX : SourceIrreducibleComponent X // sourceX ∈ DX.components })
        (sourceZ : { sourceY : SourceIrreducibleComponent Z // sourceY ∈ DZ.components })
        (x : (product_diagonal_smoothObject (k := k) sourceX.1 sourceZ.1).scheme),
        ∃ U :
          (product_diagonal_smoothObject (k := k) sourceX.1 sourceZ.1).scheme.affineOpens,
          x ∈ U.1 ∧
          Algebra.IsStandardSmoothOfRelativeDimension 0 k
            (Γ((product_diagonal_smoothObject (k := k) sourceX.1 sourceZ.1).scheme, U))) :
    FiniteCorrespondence.toRational
        (externalProductWithFamily family.family
          DX.identityFiniteCorrespondence DZ.identityFiniteCorrespondence) =
      FiniteCorrespondence.toRational DProduct.identityFiniteCorrespondence :=
  GraphIdentityCompatibleExternalProductFamily
    .externalProduct_id_right_of_standardSmoothOfRelativeDimensionZeroComponentsOpen
    family DX DZ DProduct hOpen hStd0

/-- Rational right identity theorem under the route
`reduced locally irreducible + relative-dimension-zero standard-smooth affine charts`
on each product model. -/
theorem externalProduct_id_right_of_standardSmoothOfRelativeDimensionZeroReducedLocallyIrreducible
    (family : GraphIdentityCompatibleExternalProductFamily (k := k))
    (category : SmCorQ (k := k))
    {X Z : Geometry.SmSchemeOver k}
    (DX : FiniteIrreducibleComponentDecomposition X)
    (DZ : FiniteIrreducibleComponentDecomposition Z)
    (DProduct : FiniteIrreducibleComponentDecomposition (overBaseProductObject X Z))
    (hStd0 :
      ∀ (sourceX : { sourceX : SourceIrreducibleComponent X // sourceX ∈ DX.components })
        (sourceZ : { sourceY : SourceIrreducibleComponent Z // sourceY ∈ DZ.components })
        (x : (product_diagonal_smoothObject (k := k) sourceX.1 sourceZ.1).scheme),
        ∃ U :
          (product_diagonal_smoothObject (k := k) sourceX.1 sourceZ.1).scheme.affineOpens,
          x ∈ U.1 ∧
          Algebra.IsStandardSmoothOfRelativeDimension 0 k
            (Γ((product_diagonal_smoothObject (k := k) sourceX.1 sourceZ.1).scheme, U))) :
    FiniteCorrespondence.toRational
        (externalProductWithFamily family.family
          DX.identityFiniteCorrespondence DZ.identityFiniteCorrespondence) =
      FiniteCorrespondence.toRational DProduct.identityFiniteCorrespondence :=
  GraphIdentityCompatibleExternalProductFamily
    .externalProduct_id_right_of_standardSmoothOfRelativeDimensionZeroReducedLocallyIrreducible
    family DX DZ DProduct hStd0

/-- Public owner theorem, left-handed form of `externalProduct_id_right`. -/
theorem externalProduct_id_left
    (family : GraphIdentityCompatibleExternalProductFamily (k := k))
    (category : SmCorQ (k := k))
    {X Y : Geometry.SmSchemeOver k}
    (DX : FiniteIrreducibleComponentDecomposition X)
    (DY : FiniteIrreducibleComponentDecomposition Y)
    (stableDX :
      (listed : { listed : SourceIrreducibleComponent X // listed ∈ DX.components }) →
        ProductStableSourceComponent X)
    (hstableDX : ∀ listed, (stableDX listed).component = listed.1) :
    FiniteCorrespondence.toRational
        (externalProductWithFamily family.family
          DX.identityFiniteCorrespondence DY.identityFiniteCorrespondence) =
      FiniteCorrespondence.toRational
        ((_root_.Boundary.finiteProductSourceIrreducibleComponentDecomposition
          DX DY stableDX hstableDX).identityFiniteCorrespondence) :=
  GraphIdentityCompatibleExternalProductFamily.externalProduct_id_left
    family category DX DY stableDX hstableDX

/-- Public owner theorem, left-handed form of
`externalProduct_id_right_of_locallyIrreducible`. -/
theorem externalProduct_id_left_of_locallyIrreducible
    (family : GraphIdentityCompatibleExternalProductFamily (k := k))
    (category : SmCorQ (k := k))
    {X Y : Geometry.SmSchemeOver k}
    (DX : FiniteIrreducibleComponentDecomposition X)
    (DY : FiniteIrreducibleComponentDecomposition Y)
    (DProduct : FiniteIrreducibleComponentDecomposition (overBaseProductObject X Y))
    (hLoc :
      ∀ (sourceX : { sourceX : SourceIrreducibleComponent X // sourceX ∈ DX.components })
        (sourceY : { sourceY : SourceIrreducibleComponent Y // sourceY ∈ DY.components }),
        Geometry.Topology.LocallyIrreducibleSpace
          (product_diagonal_smoothObject (k := k) sourceX.1 sourceY.1).scheme)
    (hIntegral :
      ∀ (sourceX : { sourceX : SourceIrreducibleComponent X // sourceX ∈ DX.components })
        (sourceY : { sourceY : SourceIrreducibleComponent Y // sourceY ∈ DY.components }),
        ∀ C :
          { C : Set (product_diagonal_smoothObject (k := k) sourceX.1 sourceY.1).scheme //
              C ∈ irreducibleComponents
                (product_diagonal_smoothObject (k := k) sourceX.1 sourceY.1).scheme },
          IsIntegral
            (Scheme.Opens.toScheme
              (⟨C.1,
                Geometry.Topology.isOpen_irreducibleComponent_of_locallyIrreducible
                  C.2 (hLoc sourceX sourceY)⟩ :
                (product_diagonal_smoothObject (k := k) sourceX.1 sourceY.1).scheme.Opens))) :
    FiniteCorrespondence.toRational
        (externalProductWithFamily family.family
          DX.identityFiniteCorrespondence DY.identityFiniteCorrespondence) =
      FiniteCorrespondence.toRational DProduct.identityFiniteCorrespondence :=
  externalProduct_id_right_of_locallyIrreducible
    family category DX DY DProduct hLoc hIntegral

/-- Public owner theorem, left-handed form of
`externalProduct_id_right_of_reducedLocallyIrreducible`. -/
theorem externalProduct_id_left_of_reducedLocallyIrreducible
    (family : GraphIdentityCompatibleExternalProductFamily (k := k))
    (category : SmCorQ (k := k))
    {X Y : Geometry.SmSchemeOver k}
    (DX : FiniteIrreducibleComponentDecomposition X)
    (DY : FiniteIrreducibleComponentDecomposition Y)
    (DProduct : FiniteIrreducibleComponentDecomposition (overBaseProductObject X Y))
    (hLoc :
      ∀ (sourceX : { sourceX : SourceIrreducibleComponent X // sourceX ∈ DX.components })
        (sourceY : { sourceY : SourceIrreducibleComponent Y // sourceY ∈ DY.components }),
        Geometry.Topology.LocallyIrreducibleSpace
          (product_diagonal_smoothObject (k := k) sourceX.1 sourceY.1).scheme)
    (hReduced :
      ∀ (sourceX : { sourceX : SourceIrreducibleComponent X // sourceX ∈ DX.components })
        (sourceY : { sourceY : SourceIrreducibleComponent Y // sourceY ∈ DY.components }),
        IsReduced
          (product_diagonal_smoothObject (k := k) sourceX.1 sourceY.1).scheme) :
    FiniteCorrespondence.toRational
        (externalProductWithFamily family.family
          DX.identityFiniteCorrespondence DY.identityFiniteCorrespondence) =
      FiniteCorrespondence.toRational DProduct.identityFiniteCorrespondence :=
  externalProduct_id_right_of_reducedLocallyIrreducible
    family category DX DY DProduct hLoc hReduced

/-- Public owner theorem, left-handed form of
`externalProduct_id_right_of_reducedComponentsOpen`. -/
theorem externalProduct_id_left_of_reducedComponentsOpen
    (family : GraphIdentityCompatibleExternalProductFamily (k := k))
    (category : SmCorQ (k := k))
    {X Y : Geometry.SmSchemeOver k}
    (DX : FiniteIrreducibleComponentDecomposition X)
    (DY : FiniteIrreducibleComponentDecomposition Y)
    (DProduct : FiniteIrreducibleComponentDecomposition (overBaseProductObject X Y))
    (hOpen :
      ∀ (sourceX : { sourceX : SourceIrreducibleComponent X // sourceX ∈ DX.components })
        (sourceY : { sourceY : SourceIrreducibleComponent Y // sourceY ∈ DY.components }),
        ∀ C :
          { C : Set (product_diagonal_smoothObject (k := k) sourceX.1 sourceY.1).scheme //
              C ∈ irreducibleComponents
                (product_diagonal_smoothObject (k := k) sourceX.1 sourceY.1).scheme },
          IsOpen C.1)
    (hReduced :
      ∀ (sourceX : { sourceX : SourceIrreducibleComponent X // sourceX ∈ DX.components })
        (sourceY : { sourceY : SourceIrreducibleComponent Y // sourceY ∈ DY.components }),
        IsReduced
          (product_diagonal_smoothObject (k := k) sourceX.1 sourceY.1).scheme) :
    FiniteCorrespondence.toRational
        (externalProductWithFamily family.family
          DX.identityFiniteCorrespondence DY.identityFiniteCorrespondence) =
      FiniteCorrespondence.toRational DProduct.identityFiniteCorrespondence :=
  externalProduct_id_right_of_reducedComponentsOpen
    family category DX DY DProduct hOpen hReduced

/-- Public owner theorem, left-handed form of
`externalProduct_id_right_of_standardSmoothOfRelativeDimensionZeroComponentsOpen`. -/
theorem externalProduct_id_left_of_standardSmoothOfRelativeDimensionZeroComponentsOpen
    (family : GraphIdentityCompatibleExternalProductFamily (k := k))
    (category : SmCorQ (k := k))
    {X Y : Geometry.SmSchemeOver k}
    (DX : FiniteIrreducibleComponentDecomposition X)
    (DY : FiniteIrreducibleComponentDecomposition Y)
    (DProduct : FiniteIrreducibleComponentDecomposition (overBaseProductObject X Y))
    (hOpen :
      ∀ (sourceX : { sourceX : SourceIrreducibleComponent X // sourceX ∈ DX.components })
        (sourceY : { sourceY : SourceIrreducibleComponent Y // sourceY ∈ DY.components }),
        ∀ C :
          { C : Set (product_diagonal_smoothObject (k := k) sourceX.1 sourceY.1).scheme //
              C ∈ irreducibleComponents
                (product_diagonal_smoothObject (k := k) sourceX.1 sourceY.1).scheme },
          IsOpen C.1)
    (hStd0 :
      ∀ (sourceX : { sourceX : SourceIrreducibleComponent X // sourceX ∈ DX.components })
        (sourceY : { sourceY : SourceIrreducibleComponent Y // sourceY ∈ DY.components })
        (x : (product_diagonal_smoothObject (k := k) sourceX.1 sourceY.1).scheme),
        ∃ U :
          (product_diagonal_smoothObject (k := k) sourceX.1 sourceY.1).scheme.affineOpens,
          x ∈ U.1 ∧
          Algebra.IsStandardSmoothOfRelativeDimension 0 k
            (Γ((product_diagonal_smoothObject (k := k) sourceX.1 sourceY.1).scheme, U))) :
    FiniteCorrespondence.toRational
        (externalProductWithFamily family.family
          DX.identityFiniteCorrespondence DY.identityFiniteCorrespondence) =
      FiniteCorrespondence.toRational DProduct.identityFiniteCorrespondence :=
  externalProduct_id_right_of_standardSmoothOfRelativeDimensionZeroComponentsOpen
    family category DX DY DProduct hOpen hStd0

/-- Public owner theorem, left-handed form of
`externalProduct_id_right_of_standardSmoothOfRelativeDimensionZeroReducedLocallyIrreducible`. -/
theorem externalProduct_id_left_of_standardSmoothOfRelativeDimensionZeroReducedLocallyIrreducible
    (family : GraphIdentityCompatibleExternalProductFamily (k := k))
    (category : SmCorQ (k := k))
    {X Y : Geometry.SmSchemeOver k}
    (DX : FiniteIrreducibleComponentDecomposition X)
    (DY : FiniteIrreducibleComponentDecomposition Y)
    (DProduct : FiniteIrreducibleComponentDecomposition (overBaseProductObject X Y))
    (hStd0 :
      ∀ (sourceX : { sourceX : SourceIrreducibleComponent X // sourceX ∈ DX.components })
        (sourceY : { sourceY : SourceIrreducibleComponent Y // sourceY ∈ DY.components })
        (x : (product_diagonal_smoothObject (k := k) sourceX.1 sourceY.1).scheme),
        ∃ U :
          (product_diagonal_smoothObject (k := k) sourceX.1 sourceY.1).scheme.affineOpens,
          x ∈ U.1 ∧
          Algebra.IsStandardSmoothOfRelativeDimension 0 k
            (Γ((product_diagonal_smoothObject (k := k) sourceX.1 sourceY.1).scheme, U))) :
    FiniteCorrespondence.toRational
        (externalProductWithFamily family.family
          DX.identityFiniteCorrespondence DY.identityFiniteCorrespondence) =
      FiniteCorrespondence.toRational DProduct.identityFiniteCorrespondence :=
  externalProduct_id_right_of_standardSmoothOfRelativeDimensionZeroReducedLocallyIrreducible
    family category DX DY DProduct hStd0

/-- Left-handed arbitrary-product-decomposition form of
`externalProduct_id_right_of_product_decomposition`. -/
theorem externalProduct_id_left_of_product_decomposition
    (family : GraphIdentityCompatibleExternalProductFamily (k := k))
    (category : SmCorQ (k := k))
    {X Y : Geometry.SmSchemeOver k}
    (DX : FiniteIrreducibleComponentDecomposition X)
    (DY : FiniteIrreducibleComponentDecomposition Y)
    (stableDX :
      (listed : { listed : SourceIrreducibleComponent X // listed ∈ DX.components }) →
        ProductStableSourceComponent X)
    (hstableDX : ∀ listed, (stableDX listed).component = listed.1)
    (DProduct :
      FiniteIrreducibleComponentDecomposition (overBaseProductObject X Y)) :
    FiniteCorrespondence.toRational
        (externalProductWithFamily family.family
          DX.identityFiniteCorrespondence DY.identityFiniteCorrespondence) =
      FiniteCorrespondence.toRational DProduct.identityFiniteCorrespondence := by
  calc
    FiniteCorrespondence.toRational
        (externalProductWithFamily family.family
          DX.identityFiniteCorrespondence DY.identityFiniteCorrespondence) =
      FiniteCorrespondence.toRational
        ((_root_.Boundary.finiteProductSourceIrreducibleComponentDecomposition
          DX DY stableDX hstableDX).identityFiniteCorrespondence) := by
        exact externalProduct_id_left family category DX DY stableDX hstableDX
    _ = FiniteCorrespondence.toRational DProduct.identityFiniteCorrespondence := by
        exact congrArg FiniteCorrespondence.toRational
          (FiniteIrreducibleComponentDecomposition.identityFiniteCorrespondence_independent
            (_root_.Boundary.finiteProductSourceIrreducibleComponentDecomposition
              DX DY stableDX hstableDX)
            DProduct)

end FiniteCorrespondence

namespace SmCorQ

/-- Rational correspondence-level external-product/compose interchange exported
from the tensor-compatible external-product owner package.

The proof first installs the underlying canonical external-product family
carried by `family`, then applies the rational bilinear reduction from
`RationalCompositionCategory`; its prime-level input is exactly the
owner-level interchange field of `family`. -/
theorem externalProduct_comp_interchange_of_tensorCompatibleFamily
    (family : FiniteCorrespondence.TensorCompatibleExternalProductFamily (k := k))
    (category : SmCorQ (k := k))
    {W1 X1 Y1 W2 X2 Y2 : Geometry.SmSchemeOver k}
    (f : SmCorQ.Hom category W1 X1)
    (g : SmCorQ.Hom category X1 Y1)
    (f' : SmCorQ.Hom category W2 X2)
    (g' : SmCorQ.Hom category X2 Y2) :
    letI : FiniteCorrespondence.CanonicalExternalProductFamily (k := k) :=
      family.toGraphIdentityCompatibleExternalProductFamily.toCanonicalExternalProductFamily
    category.externalProduct (category.comp f g) (category.comp f' g')
      = category.comp (category.externalProduct f f')
          (category.externalProduct g g') := by
  letI : FiniteCorrespondence.CanonicalExternalProductFamily (k := k) :=
    family.toGraphIdentityCompatibleExternalProductFamily.toCanonicalExternalProductFamily
  exact SmCorQ.externalProduct_comp_interchange
    (category := category)
    (fun f g f' g' => by
      exact
        family.externalProduct_compPrime_interchange
          category.integral.composition f g f' g')
    f g f' g'

end SmCorQ

end

end Boundary
