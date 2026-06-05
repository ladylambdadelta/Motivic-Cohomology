import Boundary.ExternalProduct
import Geometry.Correspondences.Graph

universe u

open AlgebraicGeometry CategoryTheory Limits

namespace Boundary

noncomputable section

variable {k : Type u} [Field k] [PerfectField k]

/-- The raw support of `graph(f) ⊠ Δ_Z` is canonically the pullback
`C × D` before rewriting it as the product source component carrier. -/
noncomputable def graphExternalProductSupportIso_id_right_raw
    {X Y Z : Geometry.SmSchemeOver k}
    (C : ProductStableSourceComponent X)
    (D : SourceIrreducibleComponent Z)
    (f : SmOverHom X Y) :
    PrimeFiniteCorrespondenceSupport.externalProductSupportScheme
        (Geometry.ordinaryMorphismGraphPrimeSupport C.component f)
        (SourceIrreducibleComponent.diagonalRepresentedPrimeSupport D) ≅
      overBaseProduct C.component.carrier D.carrier :=
  pullback.congrHom
    (by
      simpa [Geometry.ordinaryMorphismGraphPrimeSupport_toAmbientSource] using
        C.component.toAmbient_overBase)
    (by
      calc
        (SourceIrreducibleComponent.diagonalRepresentedPrimeSupport D).toAmbientSource ≫
            Z.structMap =
          D.toAmbient ≫ Z.structMap := by
            exact
              PrimeFiniteCorrespondenceSupport.diagonalRepresentedPrimeSupport_toAmbientSource_structMap
                (k := k) D
        _ = D.carrier.structMap := D.toAmbient_overBase)

/-- The raw support of `graph(f) ⊠ Δ_Z` is canonically the product source
component `C × D`. -/
noncomputable def graphExternalProductSupportIso_id_right
    {X Y Z : Geometry.SmSchemeOver k}
    (C : ProductStableSourceComponent X)
    (D : SourceIrreducibleComponent Z)
    (f : SmOverHom X Y) :
    PrimeFiniteCorrespondenceSupport.externalProductSupportScheme
        (Geometry.ordinaryMorphismGraphPrimeSupport C.component f)
        (SourceIrreducibleComponent.diagonalRepresentedPrimeSupport D) ≅
      (productSourceIrreducibleComponent C D).carrier.scheme :=
  graphExternalProductSupportIso_id_right_raw C D f ≪≫
    eqToIso (by
      rw [productSourceIrreducibleComponent_support_eq]
      rfl)

@[simp, reassoc] theorem graphExternalProductSupportIso_id_right_inv_fst
    {X Y Z : Geometry.SmSchemeOver k}
    (C : ProductStableSourceComponent X)
    (D : SourceIrreducibleComponent Z)
    (f : SmOverHom X Y) :
    (graphExternalProductSupportIso_id_right C D f).inv ≫
        pullback.fst
          ((Geometry.ordinaryMorphismGraphPrimeSupport C.component f).toAmbientSource ≫ X.structMap)
          ((SourceIrreducibleComponent.diagonalRepresentedPrimeSupport D).toAmbientSource ≫ Z.structMap) =
      overBaseProduct.fst C.component.carrier D.carrier := by
  simp [graphExternalProductSupportIso_id_right, graphExternalProductSupportIso_id_right_raw,
    overBaseProduct]

@[simp, reassoc] theorem graphExternalProductSupportIso_id_right_inv_snd
    {X Y Z : Geometry.SmSchemeOver k}
    (C : ProductStableSourceComponent X)
    (D : SourceIrreducibleComponent Z)
    (f : SmOverHom X Y) :
    (graphExternalProductSupportIso_id_right C D f).inv ≫
        pullback.snd
          ((Geometry.ordinaryMorphismGraphPrimeSupport C.component f).toAmbientSource ≫ X.structMap)
          ((SourceIrreducibleComponent.diagonalRepresentedPrimeSupport D).toAmbientSource ≫ Z.structMap) =
      overBaseProduct.snd C.component.carrier D.carrier := by
  simp [graphExternalProductSupportIso_id_right, graphExternalProductSupportIso_id_right_raw,
    overBaseProduct]

/-- The raw support of `Δ_X ⊠ graph(g)` is canonically the pullback
`C × D` before rewriting it as the product source component carrier. -/
noncomputable def graphExternalProductSupportIso_id_left_raw
    {X Y Z : Geometry.SmSchemeOver k}
    (C : ProductStableSourceComponent X)
    (D : SourceIrreducibleComponent Y)
    (g : SmOverHom Y Z) :
    PrimeFiniteCorrespondenceSupport.externalProductSupportScheme
        (SourceIrreducibleComponent.diagonalRepresentedPrimeSupport C.component)
        (Geometry.ordinaryMorphismGraphPrimeSupport D g) ≅
      overBaseProduct C.component.carrier D.carrier :=
  pullback.congrHom
    (by
      calc
        (SourceIrreducibleComponent.diagonalRepresentedPrimeSupport C.component).toAmbientSource ≫
            X.structMap =
          C.component.toAmbient ≫ X.structMap := by
            exact
              PrimeFiniteCorrespondenceSupport.diagonalRepresentedPrimeSupport_toAmbientSource_structMap
                (k := k) C.component
        _ = C.component.carrier.structMap := C.component.toAmbient_overBase)
    (by
      simpa [Geometry.ordinaryMorphismGraphPrimeSupport_toAmbientSource] using
        D.toAmbient_overBase)

/-- The raw support of `Δ_X ⊠ graph(g)` is canonically the product source
component `C × D`. -/
noncomputable def graphExternalProductSupportIso_id_left
    {X Y Z : Geometry.SmSchemeOver k}
    (C : ProductStableSourceComponent X)
    (D : SourceIrreducibleComponent Y)
    (g : SmOverHom Y Z) :
    PrimeFiniteCorrespondenceSupport.externalProductSupportScheme
        (SourceIrreducibleComponent.diagonalRepresentedPrimeSupport C.component)
        (Geometry.ordinaryMorphismGraphPrimeSupport D g) ≅
      (productSourceIrreducibleComponent C D).carrier.scheme :=
  graphExternalProductSupportIso_id_left_raw C D g ≪≫
    eqToIso (by
      rw [productSourceIrreducibleComponent_support_eq]
      rfl)

@[simp, reassoc] theorem graphExternalProductSupportIso_id_left_inv_fst
    {X Y Z : Geometry.SmSchemeOver k}
    (C : ProductStableSourceComponent X)
    (D : SourceIrreducibleComponent Y)
    (g : SmOverHom Y Z) :
    (graphExternalProductSupportIso_id_left C D g).inv ≫
        pullback.fst
          ((SourceIrreducibleComponent.diagonalRepresentedPrimeSupport C.component).toAmbientSource ≫
            X.structMap)
          ((Geometry.ordinaryMorphismGraphPrimeSupport D g).toAmbientSource ≫ Y.structMap) =
      overBaseProduct.fst C.component.carrier D.carrier := by
  simp [graphExternalProductSupportIso_id_left, graphExternalProductSupportIso_id_left_raw,
    overBaseProduct]

@[simp, reassoc] theorem graphExternalProductSupportIso_id_left_inv_snd
    {X Y Z : Geometry.SmSchemeOver k}
    (C : ProductStableSourceComponent X)
    (D : SourceIrreducibleComponent Y)
    (g : SmOverHom Y Z) :
    (graphExternalProductSupportIso_id_left C D g).inv ≫
        pullback.snd
          ((SourceIrreducibleComponent.diagonalRepresentedPrimeSupport C.component).toAmbientSource ≫
            X.structMap)
          ((Geometry.ordinaryMorphismGraphPrimeSupport D g).toAmbientSource ≫ Y.structMap) =
      overBaseProduct.snd C.component.carrier D.carrier := by
  simp [graphExternalProductSupportIso_id_left, graphExternalProductSupportIso_id_left_raw,
    overBaseProduct]

end

end Boundary
