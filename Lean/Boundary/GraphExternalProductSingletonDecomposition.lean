import Boundary.ExternalProduct
import Boundary.GraphProductSupportIso
import Geometry.Correspondences.Graph

universe u

open AlgebraicGeometry CategoryTheory Limits

namespace Boundary

noncomputable section

variable {k : Type u} [Field k] [PerfectField k]

namespace GraphExternalProductSingleton

abbrev rightRawSupport
    {X Y Z : Geometry.SmSchemeOver k}
    (C : ProductStableSourceComponent X)
    (D : SourceIrreducibleComponent Z)
    (f : SmOverHom X Y) : Scheme :=
  PrimeFiniteCorrespondenceSupport.externalProductSupportScheme
    (Geometry.ordinaryMorphismGraphPrimeSupport C.component f)
    (SourceIrreducibleComponent.diagonalRepresentedPrimeSupport D)

abbrev leftRawSupport
    {X Y Z : Geometry.SmSchemeOver k}
    (C : ProductStableSourceComponent X)
    (D : SourceIrreducibleComponent Y)
    (g : SmOverHom Y Z) : Scheme :=
  PrimeFiniteCorrespondenceSupport.externalProductSupportScheme
    (SourceIrreducibleComponent.diagonalRepresentedPrimeSupport C.component)
    (Geometry.ordinaryMorphismGraphPrimeSupport D g)

instance rightRawSupport_isIntegral
    {X Y Z : Geometry.SmSchemeOver k}
    (C : ProductStableSourceComponent X)
    (D : SourceIrreducibleComponent Z)
    (f : SmOverHom X Y) :
    IsIntegral (rightRawSupport C D f) := by
  let e := graphExternalProductSupportIso_id_right C D f
  letI : IsOpenImmersion e.hom := inferInstance
  haveI : IsIntegral (productSourceIrreducibleComponent C D).carrier.scheme :=
    (productSourceIrreducibleComponent C D).isIntegral
  haveI : Nonempty (rightRawSupport C D f).carrier :=
    ⟨e.inv.base (Classical.choice
      (inferInstance : Nonempty (productSourceIrreducibleComponent C D).carrier.scheme.carrier))⟩
  exact isIntegral_of_isOpenImmersion e.hom

instance leftRawSupport_isIntegral
    {X Y Z : Geometry.SmSchemeOver k}
    (C : ProductStableSourceComponent X)
    (D : SourceIrreducibleComponent Y)
    (g : SmOverHom Y Z) :
    IsIntegral (leftRawSupport C D g) := by
  let e := graphExternalProductSupportIso_id_left C D g
  letI : IsOpenImmersion e.hom := inferInstance
  haveI : IsIntegral (productSourceIrreducibleComponent C D).carrier.scheme :=
    (productSourceIrreducibleComponent C D).isIntegral
  haveI : Nonempty (leftRawSupport C D g).carrier :=
    ⟨e.inv.base (Classical.choice
      (inferInstance : Nonempty (productSourceIrreducibleComponent C D).carrier.scheme.carrier))⟩
  exact isIntegral_of_isOpenImmersion e.hom

private theorem univ_mem_irreducibleComponents_of_isIntegral
    (S : Scheme.{u}) [IsIntegral S] :
    Set.univ ∈ irreducibleComponents S := by
  rw [irreducibleComponents_eq_maximals_closed]
  refine ⟨?_, ?_⟩
  · exact ⟨isClosed_univ, IrreducibleSpace.isIrreducible_univ S.carrier⟩
  · intro t ht hsubset
    exact fun x _ => trivial

def wholeSupportComponent (S : Scheme.{u}) [IsIntegral S] :
    IrreducibleComponentAsIntClosedSubscheme S where
  carrier :=
    { scheme := S
      inclusion := 𝟙 S
      isClosedImm := by infer_instance
      isIntegral := inferInstance }
  isIrreducibleComponent := by
    exact univ_mem_irreducibleComponents_of_isIntegral S

def singletonRawSupportDecomposition (S : Scheme.{u}) [IsIntegral S] :
    FiniteIntegralClosedComponentDecomposition S where
  index := ULift Unit
  fintypeIndex := inferInstance
  decidableEqIndex := inferInstance
  component := fun _ => wholeSupportComponent S
  covers := by
    intro x
    exact ⟨ULift.up (), ⟨x, by simp [wholeSupportComponent]⟩⟩
  irredundant := by
    intro i j _h
    cases i
    cases j
    rfl

@[simp] theorem singletonRawSupportDecomposition_component_ulift_unit
    (S : Scheme.{u}) [IsIntegral S] :
    (singletonRawSupportDecomposition S).component (ULift.up ()) =
      wholeSupportComponent S := rfl

@[simp] theorem singletonRawSupportDecomposition_support_ulift_unit
    (S : Scheme.{u}) [IsIntegral S] :
    ((singletonRawSupportDecomposition S).component (ULift.up ())).carrier.scheme =
      S := rfl

@[simp] theorem singletonRawSupportDecomposition_inclusion_ulift_unit
    (S : Scheme.{u}) [IsIntegral S] :
    ((singletonRawSupportDecomposition S).component (ULift.up ())).carrier.inclusion =
      𝟙 S := by
  change (𝟙 S : S ⟶ S) = 𝟙 S
  rfl

theorem singletonRawSupportDecomposition_projection_ulift_unit
    (S : Scheme.{u}) [IsIntegral S] :
    ((singletonRawSupportDecomposition S).component (ULift.up ())).carrier.inclusion ≫
        𝟙 S =
      𝟙 S := by
  change (𝟙 S : S ⟶ S) ≫ 𝟙 S = 𝟙 S
  simp

@[simp] theorem singletonRawSupportDecomposition_sourceImage_ulift_unit
    (S : Scheme.{u}) [IsIntegral S] :
    ((singletonRawSupportDecomposition S).component (ULift.up ())).carrier =
      (wholeSupportComponent S).carrier := rfl

def rightSourceImage
    {X Y Z : Geometry.SmSchemeOver k}
    (C : ProductStableSourceComponent X)
    (D : SourceIrreducibleComponent Z)
    (f : SmOverHom X Y) :
    IntClosedSubscheme (overBaseProductObject X Z).scheme :=
  (Geometry.ordinaryMorphismGraphPrimeSupport
      (productSourceIrreducibleComponent C D)
      (overBaseProductMap f (𝟙 Z))).sourceImage.toIntClosedSubscheme

abbrev rightGraphPrime
    {X Y Z : Geometry.SmSchemeOver k}
    (C : ProductStableSourceComponent X)
    (D : SourceIrreducibleComponent Z)
    (f : SmOverHom X Y) :
    RepresentedPrimeSupport
      (overBaseProductObject X Z) (overBaseProductObject Y Z) :=
  Geometry.ordinaryMorphismGraphPrimeSupport
    (productSourceIrreducibleComponent C D)
    (overBaseProductMap f (𝟙 Z))

@[reassoc (attr := simp)]
theorem rightSourceImage_inclusion_structMap
    {X Y Z : Geometry.SmSchemeOver k}
    (C : ProductStableSourceComponent X)
    (D : SourceIrreducibleComponent Z)
    (f : SmOverHom X Y) :
    (rightSourceImage C D f).inclusion ≫
        (overBaseProductObject X Z).structMap =
      (rightGraphPrime C D f).sourceImage.carrier.structMap := by
  simpa [rightSourceImage, rightGraphPrime] using
    (rightGraphPrime C D f).sourceImage.toAmbient_overBase

noncomputable def rightSourceImage_sourceOverBaseProductIso
    {X Y Z : Geometry.SmSchemeOver k}
    (C : ProductStableSourceComponent X)
    (D : SourceIrreducibleComponent Z)
    (f : SmOverHom X Y) :
    pullback ((rightSourceImage C D f).inclusion ≫
        (overBaseProductObject X Z).structMap)
        (overBaseProductObject Y Z).structMap ≅
      sourceOverBaseProduct (rightGraphPrime C D f).sourceImage.carrier
        (overBaseProductObject Y Z) :=
  pullback.congrHom
    (rightSourceImage_inclusion_structMap C D f)
    rfl

@[simp, reassoc] theorem rightSourceImage_sourceOverBaseProductIso_inv_fst
    {X Y Z : Geometry.SmSchemeOver k}
    (C : ProductStableSourceComponent X)
    (D : SourceIrreducibleComponent Z)
    (f : SmOverHom X Y) :
    (rightSourceImage_sourceOverBaseProductIso C D f).inv ≫
        pullback.fst ((rightSourceImage C D f).inclusion ≫
          (overBaseProductObject X Z).structMap)
          (overBaseProductObject Y Z).structMap =
      sourceOverBaseProduct.fst (rightGraphPrime C D f).sourceImage.carrier
        (overBaseProductObject Y Z) := by
  simp [rightSourceImage_sourceOverBaseProductIso, sourceOverBaseProduct]

@[simp, reassoc] theorem rightSourceImage_sourceOverBaseProductIso_inv_snd
    {X Y Z : Geometry.SmSchemeOver k}
    (C : ProductStableSourceComponent X)
    (D : SourceIrreducibleComponent Z)
    (f : SmOverHom X Y) :
    (rightSourceImage_sourceOverBaseProductIso C D f).inv ≫
        pullback.snd ((rightSourceImage C D f).inclusion ≫
          (overBaseProductObject X Z).structMap)
          (overBaseProductObject Y Z).structMap =
      sourceOverBaseProduct.snd (rightGraphPrime C D f).sourceImage.carrier
        (overBaseProductObject Y Z) := by
  simp [rightSourceImage_sourceOverBaseProductIso, sourceOverBaseProduct]

theorem graphExternalProductSupportIso_id_right_hom_fst
    {X Y Z : Geometry.SmSchemeOver k}
    (C : ProductStableSourceComponent X)
    (D : SourceIrreducibleComponent Z)
    (f : SmOverHom X Y) :
    (graphExternalProductSupportIso_id_right C D f).hom ≫
        overBaseProduct.fst C.component.carrier D.carrier =
      pullback.fst
        ((Geometry.ordinaryMorphismGraphPrimeSupport C.component f).toAmbientSource ≫ X.structMap)
        ((SourceIrreducibleComponent.diagonalRepresentedPrimeSupport D).toAmbientSource ≫
          Z.structMap) := by
  let e := graphExternalProductSupportIso_id_right C D f
  calc
    e.hom ≫ overBaseProduct.fst C.component.carrier D.carrier =
        e.hom ≫ e.inv ≫
          pullback.fst
            ((Geometry.ordinaryMorphismGraphPrimeSupport C.component f).toAmbientSource ≫
              X.structMap)
            ((SourceIrreducibleComponent.diagonalRepresentedPrimeSupport D).toAmbientSource ≫
              Z.structMap) := by
          rw [← graphExternalProductSupportIso_id_right_inv_fst C D f]
    _ =
        pullback.fst
          ((Geometry.ordinaryMorphismGraphPrimeSupport C.component f).toAmbientSource ≫ X.structMap)
          ((SourceIrreducibleComponent.diagonalRepresentedPrimeSupport D).toAmbientSource ≫
            Z.structMap) := by
          simpa [Category.assoc] using
            e.hom_inv_id_assoc
              (pullback.fst
                ((Geometry.ordinaryMorphismGraphPrimeSupport C.component f).toAmbientSource ≫
                  X.structMap)
                ((SourceIrreducibleComponent.diagonalRepresentedPrimeSupport D).toAmbientSource ≫
                  Z.structMap))

theorem graphExternalProductSupportIso_id_right_hom_snd
    {X Y Z : Geometry.SmSchemeOver k}
    (C : ProductStableSourceComponent X)
    (D : SourceIrreducibleComponent Z)
    (f : SmOverHom X Y) :
    (graphExternalProductSupportIso_id_right C D f).hom ≫
        overBaseProduct.snd C.component.carrier D.carrier =
      pullback.snd
        ((Geometry.ordinaryMorphismGraphPrimeSupport C.component f).toAmbientSource ≫ X.structMap)
        ((SourceIrreducibleComponent.diagonalRepresentedPrimeSupport D).toAmbientSource ≫
          Z.structMap) := by
  let e := graphExternalProductSupportIso_id_right C D f
  calc
    e.hom ≫ overBaseProduct.snd C.component.carrier D.carrier =
        e.hom ≫ e.inv ≫
          pullback.snd
            ((Geometry.ordinaryMorphismGraphPrimeSupport C.component f).toAmbientSource ≫
              X.structMap)
            ((SourceIrreducibleComponent.diagonalRepresentedPrimeSupport D).toAmbientSource ≫
              Z.structMap) := by
          rw [← graphExternalProductSupportIso_id_right_inv_snd C D f]
    _ =
        pullback.snd
          ((Geometry.ordinaryMorphismGraphPrimeSupport C.component f).toAmbientSource ≫ X.structMap)
          ((SourceIrreducibleComponent.diagonalRepresentedPrimeSupport D).toAmbientSource ≫
            Z.structMap) := by
          simpa [Category.assoc] using
            e.hom_inv_id_assoc
              (pullback.snd
                ((Geometry.ordinaryMorphismGraphPrimeSupport C.component f).toAmbientSource ≫
                  X.structMap)
                ((SourceIrreducibleComponent.diagonalRepresentedPrimeSupport D).toAmbientSource ≫
                  Z.structMap))

theorem graphExternalProductSupportIso_id_right_hom_toProductSource
    {X Y Z : Geometry.SmSchemeOver k}
    (C : ProductStableSourceComponent X)
    (D : SourceIrreducibleComponent Z)
    (f : SmOverHom X Y) :
    (graphExternalProductSupportIso_id_right C D f).hom ≫
        (productSourceIrreducibleComponent C D).toAmbient =
      PrimeFiniteCorrespondenceSupport.externalProductToProductSource
        (Geometry.ordinaryMorphismGraphPrimeSupport C.component f)
        (SourceIrreducibleComponent.diagonalRepresentedPrimeSupport D) := by
  apply pullback.hom_ext
  · calc
      ((graphExternalProductSupportIso_id_right C D f).hom ≫
          (productSourceIrreducibleComponent C D).toAmbient) ≫ overBaseProduct.fst X Z =
        (graphExternalProductSupportIso_id_right C D f).hom ≫
          overBaseProduct.fst C.component.carrier D.carrier ≫ C.component.toAmbient := by
          change
            (graphExternalProductSupportIso_id_right C D f).hom ≫
              ((productSourceIrreducibleComponent C D).toAmbient ≫
                overBaseProduct.fst X Z) =
            (graphExternalProductSupportIso_id_right C D f).hom ≫
              (overBaseProduct.fst C.component.carrier D.carrier ≫ C.component.toAmbient)
          exact congrArg (fun h => (graphExternalProductSupportIso_id_right C D f).hom ≫ h)
            (productSourceIrreducibleComponent_fst_image C D)
      _ =
        pullback.fst
          ((Geometry.ordinaryMorphismGraphPrimeSupport C.component f).toAmbientSource ≫ X.structMap)
          ((SourceIrreducibleComponent.diagonalRepresentedPrimeSupport D).toAmbientSource ≫
            Z.structMap) ≫ C.component.toAmbient := by
          change
            ((graphExternalProductSupportIso_id_right C D f).hom ≫
              overBaseProduct.fst C.component.carrier D.carrier) ≫ C.component.toAmbient =
            pullback.fst
              ((Geometry.ordinaryMorphismGraphPrimeSupport C.component f).toAmbientSource ≫
                X.structMap)
              ((SourceIrreducibleComponent.diagonalRepresentedPrimeSupport D).toAmbientSource ≫
                Z.structMap) ≫ C.component.toAmbient
          exact congrArg (fun h => h ≫ C.component.toAmbient)
            (graphExternalProductSupportIso_id_right_hom_fst C D f)
      _ =
        PrimeFiniteCorrespondenceSupport.externalProductToProductSource
          (Geometry.ordinaryMorphismGraphPrimeSupport C.component f)
          (SourceIrreducibleComponent.diagonalRepresentedPrimeSupport D) ≫
            overBaseProduct.fst X Z := by
          simp [PrimeFiniteCorrespondenceSupport.externalProductToProductSource, Category.assoc,
            Geometry.ordinaryMorphismGraphPrimeSupport_toAmbientSource]
  · calc
      ((graphExternalProductSupportIso_id_right C D f).hom ≫
          (productSourceIrreducibleComponent C D).toAmbient) ≫ overBaseProduct.snd X Z =
        (graphExternalProductSupportIso_id_right C D f).hom ≫
          overBaseProduct.snd C.component.carrier D.carrier ≫ D.toAmbient := by
          change
            (graphExternalProductSupportIso_id_right C D f).hom ≫
              ((productSourceIrreducibleComponent C D).toAmbient ≫
                overBaseProduct.snd X Z) =
            (graphExternalProductSupportIso_id_right C D f).hom ≫
              (overBaseProduct.snd C.component.carrier D.carrier ≫ D.toAmbient)
          exact congrArg (fun h => (graphExternalProductSupportIso_id_right C D f).hom ≫ h)
            (productSourceIrreducibleComponent_snd_image C D)
      _ =
        pullback.snd
          ((Geometry.ordinaryMorphismGraphPrimeSupport C.component f).toAmbientSource ≫ X.structMap)
          ((SourceIrreducibleComponent.diagonalRepresentedPrimeSupport D).toAmbientSource ≫
            Z.structMap) ≫ D.toAmbient := by
          change
            ((graphExternalProductSupportIso_id_right C D f).hom ≫
              overBaseProduct.snd C.component.carrier D.carrier) ≫ D.toAmbient =
            pullback.snd
              ((Geometry.ordinaryMorphismGraphPrimeSupport C.component f).toAmbientSource ≫
                X.structMap)
              ((SourceIrreducibleComponent.diagonalRepresentedPrimeSupport D).toAmbientSource ≫
                Z.structMap) ≫ D.toAmbient
          exact congrArg (fun h => h ≫ D.toAmbient)
            (graphExternalProductSupportIso_id_right_hom_snd C D f)
      _ =
        PrimeFiniteCorrespondenceSupport.externalProductToProductSource
          (Geometry.ordinaryMorphismGraphPrimeSupport C.component f)
          (SourceIrreducibleComponent.diagonalRepresentedPrimeSupport D) ≫
            overBaseProduct.snd X Z := by
          calc
            pullback.snd
                ((Geometry.ordinaryMorphismGraphPrimeSupport C.component f).toAmbientSource ≫
                  X.structMap)
                ((SourceIrreducibleComponent.diagonalRepresentedPrimeSupport D).toAmbientSource ≫
                  Z.structMap) ≫ D.toAmbient =
              pullback.snd
                ((Geometry.ordinaryMorphismGraphPrimeSupport C.component f).toAmbientSource ≫
                  X.structMap)
                ((SourceIrreducibleComponent.diagonalRepresentedPrimeSupport D).toAmbientSource ≫
                  Z.structMap) ≫
                (SourceIrreducibleComponent.diagonalRepresentedPrimeSupport D).toSourceImage ≫
                  D.toAmbient := by
                rw [SourceIrreducibleComponent.diagonalRepresentedPrimeSupport_toSourceImage]
                let h :=
                  pullback.snd
                    ((Geometry.ordinaryMorphismGraphPrimeSupport C.component f).toAmbientSource ≫
                      X.structMap)
                    ((SourceIrreducibleComponent.diagonalRepresentedPrimeSupport D).toAmbientSource ≫
                      Z.structMap)
                change h ≫ D.toAmbient = (h ≫ 𝟙 D.carrier.scheme) ≫ D.toAmbient
                exact congrArg (fun q => q ≫ D.toAmbient) (Category.comp_id h).symm
            _ =
              PrimeFiniteCorrespondenceSupport.externalProductToProductSource
                (Geometry.ordinaryMorphismGraphPrimeSupport C.component f)
                (SourceIrreducibleComponent.diagonalRepresentedPrimeSupport D) ≫
                  overBaseProduct.snd X Z := by
                simp [PrimeFiniteCorrespondenceSupport.externalProductToProductSource,
                  PrimeFiniteCorrespondenceSupport.toAmbientSource, Category.assoc]

theorem graphExternalProductSupportIso_id_right_hom_toProductTarget
    {X Y Z : Geometry.SmSchemeOver k}
    (C : ProductStableSourceComponent X)
    (D : SourceIrreducibleComponent Z)
    (f : SmOverHom X Y) :
    (graphExternalProductSupportIso_id_right C D f).hom ≫
        (rightGraphPrime C D f).toTargetScheme =
      PrimeFiniteCorrespondenceSupport.externalProductToProductTarget
        (Geometry.ordinaryMorphismGraphPrimeSupport C.component f)
        (SourceIrreducibleComponent.diagonalRepresentedPrimeSupport D) := by
  apply pullback.hom_ext
  · calc
      ((graphExternalProductSupportIso_id_right C D f).hom ≫
          (rightGraphPrime C D f).toTargetScheme) ≫ overBaseProduct.fst Y Z =
        (graphExternalProductSupportIso_id_right C D f).hom ≫
          (productSourceIrreducibleComponent C D).toAmbient ≫
            (overBaseProductMap f (𝟙 Z)).hom ≫ overBaseProduct.fst Y Z := by
          simp [rightGraphPrime, Geometry.ordinaryMorphismGraphPrimeSupport_toTargetScheme,
            Category.assoc]
      _ = (graphExternalProductSupportIso_id_right C D f).hom ≫
          (productSourceIrreducibleComponent C D).toAmbient ≫
            overBaseProduct.fst X Z ≫ f.hom := by
          simp [overBaseProductMap, Category.assoc]
      _ = (graphExternalProductSupportIso_id_right C D f).hom ≫
          overBaseProduct.fst C.component.carrier D.carrier ≫
            C.component.toAmbient ≫ f.hom := by
          rw [productSourceIrreducibleComponent_fst_image]
      _ =
        pullback.fst
          ((Geometry.ordinaryMorphismGraphPrimeSupport C.component f).toAmbientSource ≫ X.structMap)
          ((SourceIrreducibleComponent.diagonalRepresentedPrimeSupport D).toAmbientSource ≫
            Z.structMap) ≫ C.component.toAmbient ≫ f.hom := by
          rw [graphExternalProductSupportIso_id_right_hom_fst]
      _ =
        PrimeFiniteCorrespondenceSupport.externalProductToProductTarget
          (Geometry.ordinaryMorphismGraphPrimeSupport C.component f)
          (SourceIrreducibleComponent.diagonalRepresentedPrimeSupport D) ≫
            overBaseProduct.fst Y Z := by
          simp [PrimeFiniteCorrespondenceSupport.externalProductToProductTarget,
            Geometry.ordinaryMorphismGraphPrimeSupport_toTargetScheme, Category.assoc]
  · calc
      ((graphExternalProductSupportIso_id_right C D f).hom ≫
          (rightGraphPrime C D f).toTargetScheme) ≫ overBaseProduct.snd Y Z =
        (graphExternalProductSupportIso_id_right C D f).hom ≫
          (productSourceIrreducibleComponent C D).toAmbient ≫
            (overBaseProductMap f (𝟙 Z)).hom ≫ overBaseProduct.snd Y Z := by
          simp [rightGraphPrime, Geometry.ordinaryMorphismGraphPrimeSupport_toTargetScheme,
            Category.assoc]
      _ = (graphExternalProductSupportIso_id_right C D f).hom ≫
          (productSourceIrreducibleComponent C D).toAmbient ≫ overBaseProduct.snd X Z := by
          simp [overBaseProductMap, Category.assoc]
      _ = (graphExternalProductSupportIso_id_right C D f).hom ≫
          overBaseProduct.snd C.component.carrier D.carrier ≫ D.toAmbient := by
          rw [productSourceIrreducibleComponent_snd_image]
      _ =
        pullback.snd
          ((Geometry.ordinaryMorphismGraphPrimeSupport C.component f).toAmbientSource ≫ X.structMap)
          ((SourceIrreducibleComponent.diagonalRepresentedPrimeSupport D).toAmbientSource ≫
            Z.structMap) ≫ D.toAmbient := by
          rw [graphExternalProductSupportIso_id_right_hom_snd]
      _ =
        PrimeFiniteCorrespondenceSupport.externalProductToProductTarget
          (Geometry.ordinaryMorphismGraphPrimeSupport C.component f)
          (SourceIrreducibleComponent.diagonalRepresentedPrimeSupport D) ≫
            overBaseProduct.snd Y Z := by
          simp [PrimeFiniteCorrespondenceSupport.externalProductToProductTarget,
            PrimeFiniteCorrespondenceSupport.toTargetScheme,
            SourceIrreducibleComponent.diagonalRepresentedPrimeSupport,
            SourceImageSubscheme.diagonalRepresentedPrimeSupport, Category.assoc]

def rightSingletonInclusion
    {X Y Z : Geometry.SmSchemeOver k}
    (C : ProductStableSourceComponent X)
    (D : SourceIrreducibleComponent Z)
    (f : SmOverHom X Y) :
    rightRawSupport C D f ⟶
      pullback ((rightSourceImage C D f).inclusion ≫ (overBaseProductObject X Z).structMap)
        (overBaseProductObject Y Z).structMap :=
  pullback.lift
    ((graphExternalProductSupportIso_id_right C D f).hom ≫
      (rightGraphPrime C D f).toSourceComponent)
    ((graphExternalProductSupportIso_id_right C D f).hom ≫
      (rightGraphPrime C D f).toTargetScheme)
    (by
      calc
        (((graphExternalProductSupportIso_id_right C D f).hom ≫
              (rightGraphPrime C D f).toSourceComponent) ≫
            (rightSourceImage C D f).inclusion) ≫
            (overBaseProductObject X Z).structMap =
          (graphExternalProductSupportIso_id_right C D f).hom ≫
            ((rightSourceImage C D f).inclusion ≫
              (overBaseProductObject X Z).structMap) := by
            simp [rightGraphPrime, Category.assoc]
        _ = (graphExternalProductSupportIso_id_right C D f).hom ≫
          (productSourceIrreducibleComponent C D).carrier.structMap := by
            exact congrArg
              (fun h => (graphExternalProductSupportIso_id_right C D f).hom ≫ h)
              (by
                simpa [rightSourceImage] using
                  (productSourceIrreducibleComponent C D).toSourceImageSubscheme.toAmbient_overBase)
        _ = (graphExternalProductSupportIso_id_right C D f).hom ≫
          (productSourceIrreducibleComponent C D).toAmbient ≫
            (overBaseProductMap f (𝟙 Z)).hom ≫
              (overBaseProductObject Y Z).structMap := by
            exact congrArg
              (fun h => (graphExternalProductSupportIso_id_right C D f).hom ≫ h)
              (by
                simpa [rightGraphPrime, Category.assoc] using
                  (PrimeFiniteCorrespondenceSupport.toSourceComponent_overBase
                    (rightGraphPrime C D f)))
        _ = ((graphExternalProductSupportIso_id_right C D f).hom ≫
              (rightGraphPrime C D f).toTargetScheme) ≫
            (overBaseProductObject Y Z).structMap := by
            simp [rightGraphPrime, Category.assoc])

theorem rightSingletonInclusion_eq_graphInclusion_iso_inv
    {X Y Z : Geometry.SmSchemeOver k}
    (C : ProductStableSourceComponent X)
    (D : SourceIrreducibleComponent Z)
    (f : SmOverHom X Y) :
    rightSingletonInclusion C D f =
      (graphExternalProductSupportIso_id_right C D f).hom ≫
        (rightGraphPrime C D f).inclusion ≫
          (rightSourceImage_sourceOverBaseProductIso C D f).inv := by
  apply pullback.hom_ext
  · calc
      rightSingletonInclusion C D f ≫
          pullback.fst ((rightSourceImage C D f).inclusion ≫
            (overBaseProductObject X Z).structMap)
            (overBaseProductObject Y Z).structMap =
        (graphExternalProductSupportIso_id_right C D f).hom ≫
          (rightGraphPrime C D f).toSourceComponent := by
          simp [rightSingletonInclusion]
      _ = (graphExternalProductSupportIso_id_right C D f).hom := by
          simp [rightGraphPrime]
      _ =
        ((graphExternalProductSupportIso_id_right C D f).hom ≫
          (rightGraphPrime C D f).inclusion ≫
          (rightSourceImage_sourceOverBaseProductIso C D f).inv) ≫
            pullback.fst ((rightSourceImage C D f).inclusion ≫
              (overBaseProductObject X Z).structMap)
              (overBaseProductObject Y Z).structMap := by
          calc
            (graphExternalProductSupportIso_id_right C D f).hom =
              (graphExternalProductSupportIso_id_right C D f).hom ≫
                (rightGraphPrime C D f).toSourceComponent := by
                simp [rightGraphPrime]
            _ = (graphExternalProductSupportIso_id_right C D f).hom ≫
                ((rightGraphPrime C D f).inclusion ≫
                  sourceOverBaseProduct.fst (rightGraphPrime C D f).sourceImage.carrier
                    (overBaseProductObject Y Z)) := by
                rw [(rightGraphPrime C D f).inclusion_fst]
            _ =
              ((graphExternalProductSupportIso_id_right C D f).hom ≫
                (rightGraphPrime C D f).inclusion ≫
                (rightSourceImage_sourceOverBaseProductIso C D f).inv) ≫
                  pullback.fst ((rightSourceImage C D f).inclusion ≫
                    (overBaseProductObject X Z).structMap)
                    (overBaseProductObject Y Z).structMap := by
                simp [Category.assoc]
  · calc
      rightSingletonInclusion C D f ≫
          pullback.snd ((rightSourceImage C D f).inclusion ≫
            (overBaseProductObject X Z).structMap)
            (overBaseProductObject Y Z).structMap =
        (graphExternalProductSupportIso_id_right C D f).hom ≫
          (rightGraphPrime C D f).toTargetScheme := by
          simp [rightSingletonInclusion]
      _ =
        ((graphExternalProductSupportIso_id_right C D f).hom ≫
          (rightGraphPrime C D f).inclusion ≫
          (rightSourceImage_sourceOverBaseProductIso C D f).inv) ≫
            pullback.snd ((rightSourceImage C D f).inclusion ≫
              (overBaseProductObject X Z).structMap)
              (overBaseProductObject Y Z).structMap := by
          calc
            (graphExternalProductSupportIso_id_right C D f).hom ≫
                (rightGraphPrime C D f).toTargetScheme =
              (graphExternalProductSupportIso_id_right C D f).hom ≫
                ((rightGraphPrime C D f).inclusion ≫
                  sourceOverBaseProduct.snd (rightGraphPrime C D f).sourceImage.carrier
                    (overBaseProductObject Y Z)) := by
                rw [(rightGraphPrime C D f).inclusion_snd]
            _ =
              ((graphExternalProductSupportIso_id_right C D f).hom ≫
                (rightGraphPrime C D f).inclusion ≫
                (rightSourceImage_sourceOverBaseProductIso C D f).inv) ≫
                  pullback.snd ((rightSourceImage C D f).inclusion ≫
                    (overBaseProductObject X Z).structMap)
                    (overBaseProductObject Y Z).structMap := by
                simp [Category.assoc]

set_option maxHeartbeats 800000 in
def graphExternalProduct_id_right_imageDecomposition_singleton
    {X Y Z : Geometry.SmSchemeOver k}
    (C : ProductStableSourceComponent X)
    (D : SourceIrreducibleComponent Z)
    (f : SmOverHom X Y) :
    ProductFiniteCorrespondenceImageDecomposition
      (PrimeFiniteCorrespondenceSupport.externalProductSupport
        (Geometry.ordinaryMorphismGraphPrimeSupport C.component f)
        (SourceIrreducibleComponent.diagonalRepresentedPrimeSupport D)) where
  components := singletonRawSupportDecomposition (rightRawSupport C D f)
  multiplicity := fun _ => 1
  sourceImage := fun _ => rightSourceImage C D f
  toSourceImage := fun _ =>
    (graphExternalProductSupportIso_id_right C D f).hom ≫
      (rightGraphPrime C D f).toSourceComponent
  finite_toSourceImage := by
    intro i
    cases i with
    | up down =>
    cases down
    haveI : IsIso (graphExternalProductSupportIso_id_right C D f).hom :=
      (graphExternalProductSupportIso_id_right C D f).isIso_hom
    simpa [rightGraphPrime] using
      (inferInstance :
        IsFinite
          ((graphExternalProductSupportIso_id_right C D f).hom ≫
            𝟙 (productSourceIrreducibleComponent C D).carrier.scheme))
  surjective_toSourceImage := by
    intro i y
    cases i with
    | up down =>
    cases down
    rcases (rightGraphPrime C D f).surjective_toSourceComponent y with ⟨x, hx⟩
    refine ⟨(graphExternalProductSupportIso_id_right C D f).inv.base x, ?_⟩
    have hcancel :
        ((graphExternalProductSupportIso_id_right C D f).hom.base
          ((graphExternalProductSupportIso_id_right C D f).inv.base x)) = x := by
      exact congrArg (fun h => h.base x)
        (graphExternalProductSupportIso_id_right C D f).inv_hom_id
    change (rightGraphPrime C D f).toSourceComponent.base
      ((graphExternalProductSupportIso_id_right C D f).hom.base
        ((graphExternalProductSupportIso_id_right C D f).inv.base x)) = y
    rw [hcancel]
    exact hx
  sourceImage_factorization := by
    intro i
    cases i with
    | up down =>
    cases down
    calc
      ((graphExternalProductSupportIso_id_right C D f).hom ≫
          (rightGraphPrime C D f).toSourceComponent) ≫
          (rightSourceImage C D f).inclusion =
        (graphExternalProductSupportIso_id_right C D f).hom ≫
          (rightGraphPrime C D f).toAmbientSource := by
          rfl
      _ = ((singletonRawSupportDecomposition (rightRawSupport C D f)).component
            (ULift.up ())).carrier.inclusion ≫
          PrimeFiniteCorrespondenceSupport.externalProductToProductSource
            (Geometry.ordinaryMorphismGraphPrimeSupport C.component f)
            (SourceIrreducibleComponent.diagonalRepresentedPrimeSupport D) := by
          change (graphExternalProductSupportIso_id_right C D f).hom ≫
              (rightGraphPrime C D f).toAmbientSource =
            ((singletonRawSupportDecomposition (rightRawSupport C D f)).component
              (ULift.up ())).carrier.inclusion ≫
                PrimeFiniteCorrespondenceSupport.externalProductToProductSource
                  (Geometry.ordinaryMorphismGraphPrimeSupport C.component f)
                  (SourceIrreducibleComponent.diagonalRepresentedPrimeSupport D)
          rw [singletonRawSupportDecomposition_inclusion_ulift_unit]
          rw [← graphExternalProductSupportIso_id_right_hom_toProductSource C D f]
          calc
            (graphExternalProductSupportIso_id_right C D f).hom ≫
                (rightGraphPrime C D f).toAmbientSource =
              (graphExternalProductSupportIso_id_right C D f).hom ≫
                (productSourceIrreducibleComponent C D).toAmbient := by
                simp [rightGraphPrime]
            _ =
              (𝟙 (rightRawSupport C D f) ≫
                (graphExternalProductSupportIso_id_right C D f).hom) ≫
                  (productSourceIrreducibleComponent C D).toAmbient := by
                rw [Category.id_comp]
  toProductTarget := fun _ =>
    (graphExternalProductSupportIso_id_right C D f).hom ≫
      (rightGraphPrime C D f).toTargetScheme
  target_factorization := by
    intro i
    cases i with
    | up down =>
    cases down
    rw [singletonRawSupportDecomposition_inclusion_ulift_unit]
    exact graphExternalProductSupportIso_id_right_hom_toProductTarget C D f
  inclusion := fun _ => rightSingletonInclusion C D f
  inclusion_fst := by
    intro i
    cases i with
    | up down =>
    cases down
    simp [rightSingletonInclusion]
  inclusion_snd := by
    intro i
    cases i with
    | up down =>
    cases down
    simp [rightSingletonInclusion]
  isClosedImmersion := by
    intro i
    cases i with
    | up down =>
    cases down
    rw [rightSingletonInclusion_eq_graphInclusion_iso_inv C D f]
    haveI : IsIso (graphExternalProductSupportIso_id_right C D f).hom :=
      (graphExternalProductSupportIso_id_right C D f).isIso_hom
    haveI : IsClosedImmersion (graphExternalProductSupportIso_id_right C D f).hom :=
      inferInstance
    haveI : IsClosedImmersion (rightGraphPrime C D f).inclusion :=
      (rightGraphPrime C D f).isClosedImmersion
    haveI : IsClosedImmersion (rightSourceImage_sourceOverBaseProductIso C D f).inv :=
      inferInstance
    infer_instance

theorem graphExternalProduct_id_right_decomposition_is_singleton
    {X Y Z : Geometry.SmSchemeOver k}
    (C : ProductStableSourceComponent X)
    (D : SourceIrreducibleComponent Z)
    (f : SmOverHom X Y) :
    (graphExternalProduct_id_right_imageDecomposition_singleton C D f).components =
        singletonRawSupportDecomposition (rightRawSupport C D f) ∧
      (graphExternalProduct_id_right_imageDecomposition_singleton C D f).multiplicity
          (ULift.up ()) = 1 ∧
      (graphExternalProduct_id_right_imageDecomposition_singleton C D f).sourceImage
          (ULift.up ()) = rightSourceImage C D f ∧
      (graphExternalProduct_id_right_imageDecomposition_singleton C D f).inclusion
          (ULift.up ()) = rightSingletonInclusion C D f := by
  simp [graphExternalProduct_id_right_imageDecomposition_singleton]

theorem graphExternalProduct_id_right_decomposition_multiplicity_one
    {X Y Z : Geometry.SmSchemeOver k}
    (C : ProductStableSourceComponent X)
    (D : SourceIrreducibleComponent Z)
    (f : SmOverHom X Y)
    (i :
      (graphExternalProduct_id_right_imageDecomposition_singleton C D f).components.index) :
    (graphExternalProduct_id_right_imageDecomposition_singleton C D f).multiplicity i = 1 := by
  cases i with
  | up down =>
  cases down
  rfl

theorem graphExternalProduct_id_right_decomposition_toSourceImage_isIso
    {X Y Z : Geometry.SmSchemeOver k}
    (C : ProductStableSourceComponent X)
    (D : SourceIrreducibleComponent Z)
    (f : SmOverHom X Y)
    (i :
      (graphExternalProduct_id_right_imageDecomposition_singleton C D f).components.index) :
    IsIso ((graphExternalProduct_id_right_imageDecomposition_singleton C D f).toSourceImage i) := by
  cases i with
  | up down =>
  cases down
  haveI : IsIso (graphExternalProductSupportIso_id_right C D f).hom :=
    (graphExternalProductSupportIso_id_right C D f).isIso_hom
  change IsIso
    ((graphExternalProductSupportIso_id_right C D f).hom ≫
      (rightGraphPrime C D f).toSourceComponent)
  simpa [rightGraphPrime] using
    (inferInstance :
      IsIso
        ((graphExternalProductSupportIso_id_right C D f).hom ≫
          𝟙 (productSourceIrreducibleComponent C D).carrier.scheme))

@[simp] theorem rightSourceImage_eq_toSourceImageSubscheme
    {X Y Z : Geometry.SmSchemeOver k}
    (C : ProductStableSourceComponent X)
    (D : SourceIrreducibleComponent Z)
    (f : SmOverHom X Y) :
    rightSourceImage C D f =
      (productSourceIrreducibleComponent C D).toSourceImageSubscheme := by
  rfl

theorem rightSourceImage_diagonalFiniteCorrespondence
    {X Y Z : Geometry.SmSchemeOver k}
    (C : ProductStableSourceComponent X)
    (D : SourceIrreducibleComponent Z)
    (f : SmOverHom X Y) :
    SourceImageSubscheme.diagonalFiniteCorrespondence (rightSourceImage C D f) =
      SourceIrreducibleComponent.diagonalFiniteCorrespondence
        (productSourceIrreducibleComponent C D) := by
  rfl

def leftSourceImage
    {X Y Z : Geometry.SmSchemeOver k}
    (C : ProductStableSourceComponent X)
    (D : SourceIrreducibleComponent Y)
    (g : SmOverHom Y Z) :
    IntClosedSubscheme (overBaseProductObject X Y).scheme :=
  (Geometry.ordinaryMorphismGraphPrimeSupport
      (productSourceIrreducibleComponent C D)
      (overBaseProductMap (𝟙 X) g)).sourceImage.toIntClosedSubscheme

end GraphExternalProductSingleton

end

end Boundary
