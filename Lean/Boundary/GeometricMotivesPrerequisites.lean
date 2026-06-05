import Boundary.TateMotives
import Boundary.ExternalProduct
import Boundary.GraphExternalProductCompatibility
import Mathlib.CategoryTheory.Monoidal.Category

/-!
# Correspondence-level tensor input for canonical geometric motives

This file exports the concrete correspondence-level tensor facts already proved
in Boundary. It does not introduce a second tensor-descent package: the public
operation is `FiniteCorrespondence.externalProduct`, routed through the
canonical external-product family constructed in `ExternalProduct.lean`.

The motive-level descent theorem still belongs above this layer: one must prove
that external product sends the A1/Nis generators to maps inverted by the
effective-motive localization, then use the localization universal property.
-/

universe u

open CategoryTheory

namespace Boundary

noncomputable section

variable {k : Type u} [Field k] [PerfectField k]
variable [FiniteCorrespondence.CanonicalExternalProductFamily (k := k)]

/-- The canonical correspondence-level tensor product used as the first layer of
effective tensor descent. -/
def boundaryEffectiveTensorProduct
    {X1 Y1 X2 Y2 : Geometry.SmSchemeOver k}
    (left : FiniteCorrespondence X1 Y1)
    (right : FiniteCorrespondence X2 Y2) :
    FiniteCorrespondence
      (overBaseProductObject X1 X2) (overBaseProductObject Y1 Y2) :=
  FiniteCorrespondence.externalProduct (k := k) left right

/-- Boundary tensor product routed through an explicit tensor-compatible owner
package. This is the form used by downstream code that needs composition
interchange from the tensor owner. -/
def boundaryEffectiveTensorProductWithFamily
    (family : FiniteCorrespondence.TensorCompatibleExternalProductFamily (k := k))
    {X1 Y1 X2 Y2 : Geometry.SmSchemeOver k}
    (left : FiniteCorrespondence X1 Y1)
    (right : FiniteCorrespondence X2 Y2) :
    FiniteCorrespondence
      (overBaseProductObject X1 X2) (overBaseProductObject Y1 Y2) :=
  FiniteCorrespondence.externalProductWithFamily family.family left right

/-- Associator for the product object underlying the Boundary tensor product.
This is the geometric product-associator needed before proving associativity of
external products of correspondences. -/
noncomputable def boundaryEffectiveTensorProductAssociator
    (X Y Z : Geometry.SmSchemeOver k) :
    overBaseProductObject (overBaseProductObject X Y) Z ≅
      overBaseProductObject X (overBaseProductObject Y Z) :=
  overBaseProductAssoc X Y Z

@[simp, reassoc] theorem boundaryEffectiveTensorProductAssociator_hom_fst
    (X Y Z : Geometry.SmSchemeOver k) :
    (boundaryEffectiveTensorProductAssociator (k := k) X Y Z).hom.hom ≫
        overBaseProduct.fst X (overBaseProductObject Y Z) =
      overBaseProduct.fst (overBaseProductObject X Y) Z ≫
        overBaseProduct.fst X Y := by
  simpa [boundaryEffectiveTensorProductAssociator] using
    overBaseProductAssoc_hom_fst (k := k) X Y Z

@[simp, reassoc] theorem boundaryEffectiveTensorProductAssociator_hom_snd_fst
    (X Y Z : Geometry.SmSchemeOver k) :
    (boundaryEffectiveTensorProductAssociator (k := k) X Y Z).hom.hom ≫
        overBaseProduct.snd X (overBaseProductObject Y Z) ≫
          overBaseProduct.fst Y Z =
      overBaseProduct.fst (overBaseProductObject X Y) Z ≫
        overBaseProduct.snd X Y := by
  simpa [boundaryEffectiveTensorProductAssociator] using
    overBaseProductAssoc_hom_snd_fst (k := k) X Y Z

@[simp, reassoc] theorem boundaryEffectiveTensorProductAssociator_hom_snd_snd
    (X Y Z : Geometry.SmSchemeOver k) :
    (boundaryEffectiveTensorProductAssociator (k := k) X Y Z).hom.hom ≫
        overBaseProduct.snd X (overBaseProductObject Y Z) ≫
          overBaseProduct.snd Y Z =
      overBaseProduct.snd (overBaseProductObject X Y) Z := by
  simpa [boundaryEffectiveTensorProductAssociator] using
    overBaseProductAssoc_hom_snd_snd (k := k) X Y Z

@[simp, reassoc] theorem boundaryEffectiveTensorProductAssociator_inv_fst_fst
    (X Y Z : Geometry.SmSchemeOver k) :
    (boundaryEffectiveTensorProductAssociator (k := k) X Y Z).inv.hom ≫
        overBaseProduct.fst (overBaseProductObject X Y) Z ≫
          overBaseProduct.fst X Y =
      overBaseProduct.fst X (overBaseProductObject Y Z) := by
  simpa [boundaryEffectiveTensorProductAssociator] using
    overBaseProductAssoc_inv_fst_fst (k := k) X Y Z

@[simp, reassoc] theorem boundaryEffectiveTensorProductAssociator_inv_fst_snd
    (X Y Z : Geometry.SmSchemeOver k) :
    (boundaryEffectiveTensorProductAssociator (k := k) X Y Z).inv.hom ≫
        overBaseProduct.fst (overBaseProductObject X Y) Z ≫
          overBaseProduct.snd X Y =
      overBaseProduct.snd X (overBaseProductObject Y Z) ≫
        overBaseProduct.fst Y Z := by
  simpa [boundaryEffectiveTensorProductAssociator] using
    overBaseProductAssoc_inv_fst_snd (k := k) X Y Z

@[simp, reassoc] theorem boundaryEffectiveTensorProductAssociator_inv_snd
    (X Y Z : Geometry.SmSchemeOver k) :
    (boundaryEffectiveTensorProductAssociator (k := k) X Y Z).inv.hom ≫
        overBaseProduct.snd (overBaseProductObject X Y) Z =
      overBaseProduct.snd X (overBaseProductObject Y Z) ≫
        overBaseProduct.snd Y Z := by
  simpa [boundaryEffectiveTensorProductAssociator] using
    overBaseProductAssoc_inv_snd (k := k) X Y Z

@[simp] theorem boundaryEffectiveTensorProduct_zero_left
    {X1 Y1 X2 Y2 : Geometry.SmSchemeOver k}
    (right : FiniteCorrespondence X2 Y2) :
    boundaryEffectiveTensorProduct (k := k)
        (0 : FiniteCorrespondence X1 Y1) right = 0 := by
  exact
    FiniteCorrespondence.externalProduct_zero_left (k := k) right

@[simp] theorem boundaryEffectiveTensorProduct_zero_right
    {X1 Y1 X2 Y2 : Geometry.SmSchemeOver k}
    (left : FiniteCorrespondence X1 Y1) :
    boundaryEffectiveTensorProduct (k := k)
        left (0 : FiniteCorrespondence X2 Y2) = 0 := by
  exact
    FiniteCorrespondence.externalProduct_zero_right (k := k) left

theorem boundaryEffectiveTensorProduct_add_left
    {X1 Y1 X2 Y2 : Geometry.SmSchemeOver k}
    (left1 left2 : FiniteCorrespondence X1 Y1)
    (right : FiniteCorrespondence X2 Y2) :
    boundaryEffectiveTensorProduct (k := k) (left1 + left2) right =
      boundaryEffectiveTensorProduct (k := k) left1 right +
        boundaryEffectiveTensorProduct (k := k) left2 right := by
  exact
    FiniteCorrespondence.externalProduct_add_left (k := k) left1 left2 right

theorem boundaryEffectiveTensorProduct_add_right
    {X1 Y1 X2 Y2 : Geometry.SmSchemeOver k}
    (left : FiniteCorrespondence X1 Y1)
    (right1 right2 : FiniteCorrespondence X2 Y2) :
    boundaryEffectiveTensorProduct (k := k) left (right1 + right2) =
      boundaryEffectiveTensorProduct (k := k) left right1 +
        boundaryEffectiveTensorProduct (k := k) left right2 := by
  exact
    FiniteCorrespondence.externalProduct_add_right (k := k) left right1 right2

theorem boundaryEffectiveTensorProduct_smul_left
    {X1 Y1 X2 Y2 : Geometry.SmSchemeOver k}
    (coeff : ℤ)
    (left : FiniteCorrespondence X1 Y1)
    (right : FiniteCorrespondence X2 Y2) :
    boundaryEffectiveTensorProduct (k := k) (coeff • left) right =
      coeff • boundaryEffectiveTensorProduct (k := k) left right := by
  exact
    FiniteCorrespondence.externalProduct_smul_left (k := k) coeff left right

theorem boundaryEffectiveTensorProduct_smul_right
    {X1 Y1 X2 Y2 : Geometry.SmSchemeOver k}
    (coeff : ℤ)
    (left : FiniteCorrespondence X1 Y1)
    (right : FiniteCorrespondence X2 Y2) :
    boundaryEffectiveTensorProduct (k := k) left (coeff • right) =
      coeff • boundaryEffectiveTensorProduct (k := k) left right := by
  exact
    FiniteCorrespondence.externalProduct_smul_right (k := k) coeff left right

@[simp] theorem boundaryEffectiveTensorProduct_single_single
    {X1 Y1 X2 Y2 : Geometry.SmSchemeOver k}
    (leftPrime : PrimeFiniteCorrespondenceGeom X1 Y1)
    (rightPrime : PrimeFiniteCorrespondenceGeom X2 Y2)
    (leftCoeff rightCoeff : ℤ) :
    boundaryEffectiveTensorProduct (k := k)
        (Finsupp.single leftPrime leftCoeff)
        (Finsupp.single rightPrime rightCoeff) =
      (leftCoeff * rightCoeff) •
        (FiniteCorrespondence.CanonicalExternalProductFamily.family
          (k := k)).data.extPrime leftPrime rightPrime := by
  exact
    FiniteCorrespondence.externalProduct_single_single (k := k)
      leftPrime rightPrime leftCoeff rightCoeff

@[simp] theorem boundaryEffectiveTensorProduct_single_single_one
    {X1 Y1 X2 Y2 : Geometry.SmSchemeOver k}
    (leftPrime : PrimeFiniteCorrespondenceGeom X1 Y1)
    (rightPrime : PrimeFiniteCorrespondenceGeom X2 Y2) :
    boundaryEffectiveTensorProduct (k := k)
        (Finsupp.single leftPrime 1)
        (Finsupp.single rightPrime 1) =
      (FiniteCorrespondence.CanonicalExternalProductFamily.family
        (k := k)).data.extPrime leftPrime rightPrime := by
  exact
    FiniteCorrespondence.externalProduct_single_single_one (k := k)
      leftPrime rightPrime

/-- Consumer-facing singleton normalization for the canonical Boundary tensor
product. -/
@[simp] theorem boundaryEffectiveTensorProduct_singleton
    {X1 Y1 X2 Y2 : Geometry.SmSchemeOver k}
    (leftPrime : PrimeFiniteCorrespondenceGeom X1 Y1)
    (rightPrime : PrimeFiniteCorrespondenceGeom X2 Y2) :
    boundaryEffectiveTensorProduct (k := k)
        (Finsupp.single leftPrime 1)
        (Finsupp.single rightPrime 1) =
      (FiniteCorrespondence.CanonicalExternalProductFamily.family
        (k := k)).data.extPrime leftPrime rightPrime :=
  boundaryEffectiveTensorProduct_single_single_one
    (k := k) leftPrime rightPrime

/-- Prime-level external-product/compose interchange implies full interchange
for the canonical Boundary tensor product on finite correspondences. -/
theorem boundaryEffectiveTensorProduct_comp_interchange_of_primes
    (compData : FiniteCorrespondenceCompositionData (k := k))
    (hPrime :
      ∀ {W1 X1 Y1 W2 X2 Y2 : Geometry.SmSchemeOver k}
        (f : PrimeFiniteCorrespondenceGeom W1 X1)
        (g : PrimeFiniteCorrespondenceGeom X1 Y1)
        (f' : PrimeFiniteCorrespondenceGeom W2 X2)
        (g' : PrimeFiniteCorrespondenceGeom X2 Y2),
          boundaryEffectiveTensorProduct (k := k)
              (FiniteCorrespondenceCompositionData.compPrime compData f g)
              (FiniteCorrespondenceCompositionData.compPrime compData f' g')
            =
              FiniteCorrespondenceCompositionData.comp compData
                (boundaryEffectiveTensorProduct (k := k)
                  (Finsupp.single f 1) (Finsupp.single f' 1))
                (boundaryEffectiveTensorProduct (k := k)
                  (Finsupp.single g 1) (Finsupp.single g' 1)))
    {W1 X1 Y1 W2 X2 Y2 : Geometry.SmSchemeOver k}
    (f : FiniteCorrespondence W1 X1)
    (g : FiniteCorrespondence X1 Y1)
    (f' : FiniteCorrespondence W2 X2)
    (g' : FiniteCorrespondence X2 Y2) :
    boundaryEffectiveTensorProduct (k := k)
        (FiniteCorrespondenceCompositionData.comp compData f g)
        (FiniteCorrespondenceCompositionData.comp compData f' g')
      =
        FiniteCorrespondenceCompositionData.comp compData
          (boundaryEffectiveTensorProduct (k := k) f f')
          (boundaryEffectiveTensorProduct (k := k) g g') := by
  exact
    FiniteCorrespondence.externalProduct_comp_interchange_of_primes
      (k := k) compData hPrime f g f' g'

/-- Consumer-facing composition interchange for the canonical Boundary tensor
product on finite correspondences, using the tensor-compatible owner package. -/
theorem boundaryEffectiveTensorProduct_comp_interchange
    (family : FiniteCorrespondence.TensorCompatibleExternalProductFamily (k := k))
    (compData : FiniteCorrespondenceCompositionData (k := k))
    {W1 X1 Y1 W2 X2 Y2 : Geometry.SmSchemeOver k}
    (f : FiniteCorrespondence W1 X1)
    (g : FiniteCorrespondence X1 Y1)
    (f' : FiniteCorrespondence W2 X2)
    (g' : FiniteCorrespondence X2 Y2) :
    boundaryEffectiveTensorProductWithFamily (k := k) family
        (FiniteCorrespondenceCompositionData.comp compData f g)
        (FiniteCorrespondenceCompositionData.comp compData f' g')
      =
        FiniteCorrespondenceCompositionData.comp compData
          (boundaryEffectiveTensorProductWithFamily (k := k) family f f')
          (boundaryEffectiveTensorProductWithFamily (k := k) family g g') := by
  exact
    FiniteCorrespondence.TensorCompatibleExternalProductFamily.externalProduct_comp_interchange
      (k := k) family compData f g f' g'

/-- Graph-transfer identity law for tensoring a graph correspondence on the
right by an identity graph. This is the concrete graph-transfer endpoint used
when lifting the identity law from graph correspondences to arbitrary finite
correspondences. -/
theorem boundaryEffectiveTensorProduct_id_right_graphTransfer
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
        (_root_.Boundary.finiteProductSourceIrreducibleComponentDecomposition
          DX DZ stableDX hstableDX) =
      FiniteCorrespondence.toRational
        (∑ p in DX.components.attach.product DZ.components.attach,
          FiniteCorrespondence.ofPrimeSupport
            (graphExternalProductPrimeSupport_id_right (stableDX p.1) p.2.1 f)) :=
  graphTransfer_overBaseProductMap_id_right
    category DX DZ stableDX hstableDX f

/-- Graph-transfer identity law for tensoring an identity graph on the left by a
graph correspondence. This is the concrete graph-transfer endpoint used when
lifting the identity law from graph correspondences to arbitrary finite
correspondences. -/
theorem boundaryEffectiveTensorProduct_id_left_graphTransfer
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
        (_root_.Boundary.finiteProductSourceIrreducibleComponentDecomposition
          DX DY stableDX hstableDX) =
      FiniteCorrespondence.toRational
        (∑ p in DX.components.attach.product DY.components.attach,
          FiniteCorrespondence.ofPrimeSupport
            (graphExternalProductPrimeSupport_id_left (stableDX p.1) p.2.1 g)) :=
  graphTransfer_overBaseProductMap_id_left
    category DX DY stableDX hstableDX g

end

end Boundary
