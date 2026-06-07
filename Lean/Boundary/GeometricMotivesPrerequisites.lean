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

/-- `SmCorQ`-level graph-transfer identity law for tensoring a graph
correspondence on the right by an identity graph. This is the direct
`tensorHom` form of `boundaryEffectiveTensorProduct_id_right_graphTransfer`. -/
theorem boundaryEffectiveTensorProduct_tensorHom_graphTransfer_id_right
    (family : FiniteCorrespondence.TensorCompatibleExternalProductFamily (k := k))
    (category : SmCorQ (k := k))
    {X Y Z : Geometry.SmSchemeOver k}
    (DX : FiniteIrreducibleComponentDecomposition X)
    (DZ : FiniteIrreducibleComponentDecomposition Z)
    (stableDX :
      (listed : { listed : SourceIrreducibleComponent X // listed ∈ DX.components }) →
        ProductStableSourceComponent X)
    (hstableDX : ∀ listed, (stableDX listed).component = listed.1)
    (f : SmOverHom X Y) :
    SmCorQ.tensorHom family category
        (SmCorQ.graphTransfer category f DX)
        (FiniteCorrespondence.toRational DZ.identityFiniteCorrespondence) =
      SmCorQ.graphTransfer category
        (overBaseProductMap f (𝟙 Z))
        (_root_.Boundary.finiteProductSourceIrreducibleComponentDecomposition
          DX DZ stableDX hstableDX) := by
  exact
    SmCorQ.tensorHom_graphTransfer_id_right
      family category DX DZ stableDX hstableDX f

/-- Graph-transfer identity law for tensoring a graph correspondence on the
right by an identity graph, targeting any certified decomposition of the
product object. -/
theorem boundaryEffectiveTensorProduct_id_right_graphTransfer_of_product_decomposition
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
        DProduct :=
  FiniteCorrespondence.GraphIdentityCompatibleExternalProductFamily
    .externalProduct_graphTransfer_id_right_of_product_decomposition
    family category DX DZ stableDX hstableDX DProduct f

/-- `SmCorQ`-level graph-transfer identity law for tensoring a graph
correspondence on the right by an identity graph, targeting any certified
decomposition of the product object. -/
theorem boundaryEffectiveTensorProduct_tensorHom_graphTransfer_id_right_of_product_decomposition
    (family : FiniteCorrespondence.TensorCompatibleExternalProductFamily (k := k))
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
    SmCorQ.tensorHom family category
        (SmCorQ.graphTransfer category f DX)
        (FiniteCorrespondence.toRational DZ.identityFiniteCorrespondence) =
      SmCorQ.graphTransfer category
        (overBaseProductMap f (𝟙 Z))
        DProduct := by
  exact
    SmCorQ.tensorHom_graphTransfer_id_right_of_product_decomposition
      family category DX DZ stableDX hstableDX DProduct f

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

/-- `SmCorQ`-level graph-transfer identity law for tensoring an identity graph
on the left by a graph correspondence. This is the direct `tensorHom` form of
`boundaryEffectiveTensorProduct_id_left_graphTransfer`. -/
theorem boundaryEffectiveTensorProduct_tensorHom_id_left_graphTransfer
    (family : FiniteCorrespondence.TensorCompatibleExternalProductFamily (k := k))
    (category : SmCorQ (k := k))
    {X Y Z : Geometry.SmSchemeOver k}
    (DX : FiniteIrreducibleComponentDecomposition X)
    (DY : FiniteIrreducibleComponentDecomposition Y)
    (stableDX :
      (listed : { listed : SourceIrreducibleComponent X // listed ∈ DX.components }) →
        ProductStableSourceComponent X)
    (hstableDX : ∀ listed, (stableDX listed).component = listed.1)
    (g : SmOverHom Y Z) :
    SmCorQ.tensorHom family category
        (FiniteCorrespondence.toRational DX.identityFiniteCorrespondence)
        (SmCorQ.graphTransfer category g DY) =
      SmCorQ.graphTransfer category
        (overBaseProductMap (𝟙 X) g)
        (_root_.Boundary.finiteProductSourceIrreducibleComponentDecomposition
          DX DY stableDX hstableDX) := by
  exact
    SmCorQ.tensorHom_id_left_graphTransfer
      family category DX DY stableDX hstableDX g

/-- Graph-transfer identity law for tensoring an identity graph on the left by
a graph correspondence, targeting any certified decomposition of the product
object. -/
theorem boundaryEffectiveTensorProduct_id_left_graphTransfer_of_product_decomposition
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
        DProduct :=
  FiniteCorrespondence.GraphIdentityCompatibleExternalProductFamily
    .externalProduct_id_left_graphTransfer_of_product_decomposition
    family category DX DY stableDX hstableDX DProduct g

/-- `SmCorQ`-level graph-transfer identity law for tensoring an identity graph
on the left by a graph correspondence, targeting any certified decomposition
of the product object. -/
theorem boundaryEffectiveTensorProduct_tensorHom_id_left_graphTransfer_of_product_decomposition
    (family : FiniteCorrespondence.TensorCompatibleExternalProductFamily (k := k))
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
    SmCorQ.tensorHom family category
        (FiniteCorrespondence.toRational DX.identityFiniteCorrespondence)
        (SmCorQ.graphTransfer category g DY) =
      SmCorQ.graphTransfer category
        (overBaseProductMap (𝟙 X) g)
        DProduct := by
  exact
    SmCorQ.tensorHom_id_left_graphTransfer_of_product_decomposition
      family category DX DY stableDX hstableDX DProduct g

/-- Correspondence-level tensor identity under the route
`locally irreducible + integral component opens`
on each product model. This is the motive-facing wrapper over the clean
`SmCorQ` owner theorem. -/
theorem boundaryEffectiveTensorProduct_id_of_locallyIrreducible
    (family : FiniteCorrespondence.TensorCompatibleExternalProductFamily (k := k))
    (category : SmCorQ (k := k))
    (X Y : Geometry.SmSchemeOver k)
    (hLoc :
      ∀ (sourceX :
        { sourceX : SourceIrreducibleComponent X //
          sourceX ∈ (category.integral.composition.diagonalDecomposition X).components })
        (sourceY :
          { sourceY : SourceIrreducibleComponent Y //
          sourceY ∈ (category.integral.composition.diagonalDecomposition Y).components }),
        Geometry.Topology.LocallyIrreducibleSpace
          (product_diagonal_smoothObject (k := k) sourceX.1 sourceY.1).scheme)
    (hIntegral :
      ∀ (sourceX :
        { sourceX : SourceIrreducibleComponent X //
          sourceX ∈ (category.integral.composition.diagonalDecomposition X).components })
        (sourceY :
          { sourceY : SourceIrreducibleComponent Y //
            sourceY ∈ (category.integral.composition.diagonalDecomposition Y).components }),
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
      (boundaryEffectiveTensorProductWithFamily (k := k) family
        (category.id X) (category.id Y)) =
    category.id (overBaseProductObject X Y) := by
  change
    FiniteCorrespondence.toRational
      (FiniteCorrespondence.externalProductWithFamily family.family
        (category.integral.composition.diagonalDecomposition X).identityFiniteCorrespondence
        (category.integral.composition.diagonalDecomposition Y).identityFiniteCorrespondence) =
    FiniteCorrespondence.toRational
      ((category.integral.composition.diagonalDecomposition
        (overBaseProductObject X Y)).identityFiniteCorrespondence)
  exact congrArg FiniteCorrespondence.toRational
    (FiniteCorrespondence
      .externalProductWithFamily_identity_identity_eq_identityFiniteCorrespondence_of_locallyIrreducible
      (k := k) family.family
      (category.integral.composition.diagonalDecomposition X)
      (category.integral.composition.diagonalDecomposition Y)
      (category.integral.composition.diagonalDecomposition (overBaseProductObject X Y))
      hLoc hIntegral)

/-- `SmCorQ`-level tensor identity under the route
`locally irreducible + integral component opens`
on each product model, exported at the motive-prerequisite layer. -/
theorem boundaryEffectiveTensorProduct_tensorHom_id_of_locallyIrreducible
    (family : FiniteCorrespondence.TensorCompatibleExternalProductFamily (k := k))
    (category : SmCorQ (k := k))
    (X Y : Geometry.SmSchemeOver k)
    (hLoc :
      ∀ (sourceX :
        { sourceX : SourceIrreducibleComponent X //
          sourceX ∈ (category.integral.composition.diagonalDecomposition X).components })
        (sourceY :
          { sourceY : SourceIrreducibleComponent Y //
          sourceY ∈ (category.integral.composition.diagonalDecomposition Y).components }),
        Geometry.Topology.LocallyIrreducibleSpace
          (product_diagonal_smoothObject (k := k) sourceX.1 sourceY.1).scheme)
    (hIntegral :
      ∀ (sourceX :
        { sourceX : SourceIrreducibleComponent X //
          sourceX ∈ (category.integral.composition.diagonalDecomposition X).components })
        (sourceY :
          { sourceY : SourceIrreducibleComponent Y //
            sourceY ∈ (category.integral.composition.diagonalDecomposition Y).components }),
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
    SmCorQ.tensorHom family category (category.id X) (category.id Y) =
      category.id (overBaseProductObject X Y) := by
  exact
    SmCorQ.tensorHom_id_of_locallyIrreducible
      family category X Y hLoc hIntegral

/-- Correspondence-level tensor identity under the route
`reduced + locally irreducible`
on each product model. This is the motive-facing wrapper over the clean
`SmCorQ` owner theorem. -/
theorem boundaryEffectiveTensorProduct_id_of_reducedLocallyIrreducible
    (family : FiniteCorrespondence.TensorCompatibleExternalProductFamily (k := k))
    (category : SmCorQ (k := k))
    (X Y : Geometry.SmSchemeOver k)
    (hLoc :
      ∀ (sourceX :
        { sourceX : SourceIrreducibleComponent X //
          sourceX ∈ (category.integral.composition.diagonalDecomposition X).components })
        (sourceY :
          { sourceY : SourceIrreducibleComponent Y //
          sourceY ∈ (category.integral.composition.diagonalDecomposition Y).components }),
        Geometry.Topology.LocallyIrreducibleSpace
          (product_diagonal_smoothObject (k := k) sourceX.1 sourceY.1).scheme)
    (hReduced :
      ∀ (sourceX :
        { sourceX : SourceIrreducibleComponent X //
          sourceX ∈ (category.integral.composition.diagonalDecomposition X).components })
        (sourceY :
          { sourceY : SourceIrreducibleComponent Y //
          sourceY ∈ (category.integral.composition.diagonalDecomposition Y).components }),
        IsReduced
          (product_diagonal_smoothObject (k := k) sourceX.1 sourceY.1).scheme) :
    FiniteCorrespondence.toRational
      (boundaryEffectiveTensorProductWithFamily (k := k) family
        (category.id X) (category.id Y)) =
    category.id (overBaseProductObject X Y) := by
  change
    FiniteCorrespondence.toRational
      (FiniteCorrespondence.externalProductWithFamily family.family
        (category.integral.composition.diagonalDecomposition X).identityFiniteCorrespondence
        (category.integral.composition.diagonalDecomposition Y).identityFiniteCorrespondence) =
    FiniteCorrespondence.toRational
      ((category.integral.composition.diagonalDecomposition
        (overBaseProductObject X Y)).identityFiniteCorrespondence)
  exact congrArg FiniteCorrespondence.toRational
    (FiniteCorrespondence
      .externalProductWithFamily_identity_identity_eq_identityFiniteCorrespondence_of_reducedLocallyIrreducible
      (k := k) family.family
      (category.integral.composition.diagonalDecomposition X)
      (category.integral.composition.diagonalDecomposition Y)
      (category.integral.composition.diagonalDecomposition (overBaseProductObject X Y))
      hLoc hReduced)

/-- `SmCorQ`-level tensor identity under the route
`reduced + locally irreducible`
on each product model, exported at the motive-prerequisite layer. -/
theorem boundaryEffectiveTensorProduct_tensorHom_id_of_reducedLocallyIrreducible
    (family : FiniteCorrespondence.TensorCompatibleExternalProductFamily (k := k))
    (category : SmCorQ (k := k))
    (X Y : Geometry.SmSchemeOver k)
    (hLoc :
      ∀ (sourceX :
        { sourceX : SourceIrreducibleComponent X //
          sourceX ∈ (category.integral.composition.diagonalDecomposition X).components })
        (sourceY :
          { sourceY : SourceIrreducibleComponent Y //
          sourceY ∈ (category.integral.composition.diagonalDecomposition Y).components }),
        Geometry.Topology.LocallyIrreducibleSpace
          (product_diagonal_smoothObject (k := k) sourceX.1 sourceY.1).scheme)
    (hReduced :
      ∀ (sourceX :
        { sourceX : SourceIrreducibleComponent X //
          sourceX ∈ (category.integral.composition.diagonalDecomposition X).components })
        (sourceY :
          { sourceY : SourceIrreducibleComponent Y //
          sourceY ∈ (category.integral.composition.diagonalDecomposition Y).components }),
        IsReduced
          (product_diagonal_smoothObject (k := k) sourceX.1 sourceY.1).scheme) :
    SmCorQ.tensorHom family category (category.id X) (category.id Y) =
      category.id (overBaseProductObject X Y) := by
  exact
    SmCorQ.tensorHom_id_of_reducedLocallyIrreducible
      family category X Y hLoc hReduced

/-- Correspondence-level tensor identity under the route
`components open + reduced`
on each product model. This is the motive-facing wrapper over the clean
`SmCorQ` owner theorem. -/
theorem boundaryEffectiveTensorProduct_id_of_reducedComponentsOpen
    (family : FiniteCorrespondence.TensorCompatibleExternalProductFamily (k := k))
    (category : SmCorQ (k := k))
    (X Y : Geometry.SmSchemeOver k)
    (hOpen :
      ∀ (sourceX :
        { sourceX : SourceIrreducibleComponent X //
          sourceX ∈ (category.integral.composition.diagonalDecomposition X).components })
        (sourceY :
          { sourceY : SourceIrreducibleComponent Y //
          sourceY ∈ (category.integral.composition.diagonalDecomposition Y).components }),
        ∀ C :
          { C : Set (product_diagonal_smoothObject (k := k) sourceX.1 sourceY.1).scheme //
              C ∈ irreducibleComponents
                (product_diagonal_smoothObject (k := k) sourceX.1 sourceY.1).scheme },
          IsOpen C.1)
    (hReduced :
      ∀ (sourceX :
        { sourceX : SourceIrreducibleComponent X //
          sourceX ∈ (category.integral.composition.diagonalDecomposition X).components })
        (sourceY :
          { sourceY : SourceIrreducibleComponent Y //
          sourceY ∈ (category.integral.composition.diagonalDecomposition Y).components }),
        IsReduced
          (product_diagonal_smoothObject (k := k) sourceX.1 sourceY.1).scheme) :
    FiniteCorrespondence.toRational
      (boundaryEffectiveTensorProductWithFamily (k := k) family
        (category.id X) (category.id Y)) =
    category.id (overBaseProductObject X Y) := by
  change
    FiniteCorrespondence.toRational
      (FiniteCorrespondence.externalProductWithFamily family.family
        (category.integral.composition.diagonalDecomposition X).identityFiniteCorrespondence
        (category.integral.composition.diagonalDecomposition Y).identityFiniteCorrespondence) =
    FiniteCorrespondence.toRational
      ((category.integral.composition.diagonalDecomposition
        (overBaseProductObject X Y)).identityFiniteCorrespondence)
  exact congrArg FiniteCorrespondence.toRational
    (FiniteCorrespondence
      .externalProductWithFamily_identity_identity_eq_identityFiniteCorrespondence_of_reducedComponentsOpen
      (k := k) family.family
      (category.integral.composition.diagonalDecomposition X)
      (category.integral.composition.diagonalDecomposition Y)
      (category.integral.composition.diagonalDecomposition (overBaseProductObject X Y))
      hOpen hReduced)

/-- `SmCorQ`-level tensor identity under the route
`components open + reduced`
on each product model, exported at the motive-prerequisite layer. -/
theorem boundaryEffectiveTensorProduct_tensorHom_id_of_reducedComponentsOpen
    (family : FiniteCorrespondence.TensorCompatibleExternalProductFamily (k := k))
    (category : SmCorQ (k := k))
    (X Y : Geometry.SmSchemeOver k)
    (hOpen :
      ∀ (sourceX :
        { sourceX : SourceIrreducibleComponent X //
          sourceX ∈ (category.integral.composition.diagonalDecomposition X).components })
        (sourceY :
          { sourceY : SourceIrreducibleComponent Y //
          sourceY ∈ (category.integral.composition.diagonalDecomposition Y).components }),
        ∀ C :
          { C : Set (product_diagonal_smoothObject (k := k) sourceX.1 sourceY.1).scheme //
              C ∈ irreducibleComponents
                (product_diagonal_smoothObject (k := k) sourceX.1 sourceY.1).scheme },
          IsOpen C.1)
    (hReduced :
      ∀ (sourceX :
        { sourceX : SourceIrreducibleComponent X //
          sourceX ∈ (category.integral.composition.diagonalDecomposition X).components })
        (sourceY :
          { sourceY : SourceIrreducibleComponent Y //
          sourceY ∈ (category.integral.composition.diagonalDecomposition Y).components }),
        IsReduced
          (product_diagonal_smoothObject (k := k) sourceX.1 sourceY.1).scheme) :
    SmCorQ.tensorHom family category (category.id X) (category.id Y) =
      category.id (overBaseProductObject X Y) := by
  exact
    SmCorQ.tensorHom_id_of_reducedComponentsOpen
      family category X Y hOpen hReduced

/-- Correspondence-level tensor identity under the route
`components open + relative-dimension-zero standard-smooth affine charts`
on each product model. This is the motive-facing wrapper over the clean
`SmCorQ` owner theorem. -/
theorem boundaryEffectiveTensorProduct_id_of_standardSmoothOfRelativeDimensionZeroComponentsOpen
    (family : FiniteCorrespondence.TensorCompatibleExternalProductFamily (k := k))
    (category : SmCorQ (k := k))
    (X Y : Geometry.SmSchemeOver k)
    (hOpen :
      ∀ (sourceX :
        { sourceX : SourceIrreducibleComponent X //
          sourceX ∈ (category.integral.composition.diagonalDecomposition X).components })
        (sourceY :
          { sourceY : SourceIrreducibleComponent Y //
          sourceY ∈ (category.integral.composition.diagonalDecomposition Y).components }),
        ∀ C :
          { C : Set (product_diagonal_smoothObject (k := k) sourceX.1 sourceY.1).scheme //
              C ∈ irreducibleComponents
                (product_diagonal_smoothObject (k := k) sourceX.1 sourceY.1).scheme },
          IsOpen C.1)
    (hStd0 :
      ∀ (sourceX :
        { sourceX : SourceIrreducibleComponent X //
          sourceX ∈ (category.integral.composition.diagonalDecomposition X).components })
        (sourceY :
          { sourceY : SourceIrreducibleComponent Y //
          sourceY ∈ (category.integral.composition.diagonalDecomposition Y).components })
        (x : (product_diagonal_smoothObject (k := k) sourceX.1 sourceY.1).scheme),
        ∃ U :
          (product_diagonal_smoothObject (k := k) sourceX.1 sourceY.1).scheme.affineOpens,
          x ∈ U.1 ∧
          Algebra.IsStandardSmoothOfRelativeDimension 0 k
            (Γ((product_diagonal_smoothObject (k := k) sourceX.1 sourceY.1).scheme, U))) :
    FiniteCorrespondence.toRational
      (boundaryEffectiveTensorProductWithFamily (k := k) family
        (category.id X) (category.id Y)) =
    category.id (overBaseProductObject X Y) := by
  change
    FiniteCorrespondence.toRational
      (FiniteCorrespondence.externalProductWithFamily family.family
        (category.integral.composition.diagonalDecomposition X).identityFiniteCorrespondence
        (category.integral.composition.diagonalDecomposition Y).identityFiniteCorrespondence) =
    FiniteCorrespondence.toRational
      ((category.integral.composition.diagonalDecomposition
        (overBaseProductObject X Y)).identityFiniteCorrespondence)
  exact congrArg FiniteCorrespondence.toRational
    (FiniteCorrespondence
      .externalProductWithFamily_identity_identity_eq_identityFiniteCorrespondence_of_standardSmoothOfRelativeDimensionZero_componentsOpen
      (k := k) family.family
      (category.integral.composition.diagonalDecomposition X)
      (category.integral.composition.diagonalDecomposition Y)
      (category.integral.composition.diagonalDecomposition (overBaseProductObject X Y))
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

/-- `SmCorQ`-level tensor identity under the route
`components open + relative-dimension-zero standard-smooth affine charts`
on each product model, exported at the motive-prerequisite layer. -/
theorem boundaryEffectiveTensorProduct_tensorHom_id_of_standardSmoothOfRelativeDimensionZeroComponentsOpen
    (family : FiniteCorrespondence.TensorCompatibleExternalProductFamily (k := k))
    (category : SmCorQ (k := k))
    (X Y : Geometry.SmSchemeOver k)
    (hOpen :
      ∀ (sourceX :
        { sourceX : SourceIrreducibleComponent X //
          sourceX ∈ (category.integral.composition.diagonalDecomposition X).components })
        (sourceY :
          { sourceY : SourceIrreducibleComponent Y //
          sourceY ∈ (category.integral.composition.diagonalDecomposition Y).components }),
        ∀ C :
          { C : Set (product_diagonal_smoothObject (k := k) sourceX.1 sourceY.1).scheme //
              C ∈ irreducibleComponents
                (product_diagonal_smoothObject (k := k) sourceX.1 sourceY.1).scheme },
          IsOpen C.1)
    (hStd0 :
      ∀ (sourceX :
        { sourceX : SourceIrreducibleComponent X //
          sourceX ∈ (category.integral.composition.diagonalDecomposition X).components })
        (sourceY :
          { sourceY : SourceIrreducibleComponent Y //
          sourceY ∈ (category.integral.composition.diagonalDecomposition Y).components })
        (x : (product_diagonal_smoothObject (k := k) sourceX.1 sourceY.1).scheme),
        ∃ U :
          (product_diagonal_smoothObject (k := k) sourceX.1 sourceY.1).scheme.affineOpens,
          x ∈ U.1 ∧
          Algebra.IsStandardSmoothOfRelativeDimension 0 k
            (Γ((product_diagonal_smoothObject (k := k) sourceX.1 sourceY.1).scheme, U))) :
    SmCorQ.tensorHom family category (category.id X) (category.id Y) =
      category.id (overBaseProductObject X Y) := by
  exact
    SmCorQ.tensorHom_id_of_standardSmoothOfRelativeDimensionZeroComponentsOpen
      family category X Y hOpen hStd0

/-- Correspondence-level tensor identity under the route
`reduced locally irreducible + relative-dimension-zero standard-smooth affine charts`
on each product model. This is the motive-facing wrapper over the clean
`SmCorQ` owner theorem. -/
theorem boundaryEffectiveTensorProduct_id_of_standardSmoothOfRelativeDimensionZeroReducedLocallyIrreducible
    (family : FiniteCorrespondence.TensorCompatibleExternalProductFamily (k := k))
    (category : SmCorQ (k := k))
    (X Y : Geometry.SmSchemeOver k)
    (hStd0 :
      ∀ (sourceX :
        { sourceX : SourceIrreducibleComponent X //
          sourceX ∈ (category.integral.composition.diagonalDecomposition X).components })
        (sourceY :
          { sourceY : SourceIrreducibleComponent Y //
          sourceY ∈ (category.integral.composition.diagonalDecomposition Y).components })
        (x : (product_diagonal_smoothObject (k := k) sourceX.1 sourceY.1).scheme),
        ∃ U :
          (product_diagonal_smoothObject (k := k) sourceX.1 sourceY.1).scheme.affineOpens,
          x ∈ U.1 ∧
          Algebra.IsStandardSmoothOfRelativeDimension 0 k
            (Γ((product_diagonal_smoothObject (k := k) sourceX.1 sourceY.1).scheme, U))) :
    FiniteCorrespondence.toRational
      (boundaryEffectiveTensorProductWithFamily (k := k) family
        (category.id X) (category.id Y)) =
    category.id (overBaseProductObject X Y) := by
  change
    FiniteCorrespondence.toRational
      (FiniteCorrespondence.externalProductWithFamily family.family
        (category.integral.composition.diagonalDecomposition X).identityFiniteCorrespondence
        (category.integral.composition.diagonalDecomposition Y).identityFiniteCorrespondence) =
    FiniteCorrespondence.toRational
      ((category.integral.composition.diagonalDecomposition
        (overBaseProductObject X Y)).identityFiniteCorrespondence)
  exact congrArg FiniteCorrespondence.toRational
    (FiniteCorrespondence
      .externalProductWithFamily_identity_identity_eq_identityFiniteCorrespondence_of_standardSmoothOfRelativeDimensionZero_reducedLocallyIrreducible
      (k := k) family.family
      (category.integral.composition.diagonalDecomposition X)
      (category.integral.composition.diagonalDecomposition Y)
      (category.integral.composition.diagonalDecomposition (overBaseProductObject X Y))
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

/-- `SmCorQ`-level tensor identity under the route
`reduced locally irreducible + relative-dimension-zero standard-smooth affine charts`
on each product model, exported at the motive-prerequisite layer. -/
theorem boundaryEffectiveTensorProduct_tensorHom_id_of_standardSmoothOfRelativeDimensionZeroReducedLocallyIrreducible
    (family : FiniteCorrespondence.TensorCompatibleExternalProductFamily (k := k))
    (category : SmCorQ (k := k))
    (X Y : Geometry.SmSchemeOver k)
    (hStd0 :
      ∀ (sourceX :
        { sourceX : SourceIrreducibleComponent X //
          sourceX ∈ (category.integral.composition.diagonalDecomposition X).components })
        (sourceY :
          { sourceY : SourceIrreducibleComponent Y //
          sourceY ∈ (category.integral.composition.diagonalDecomposition Y).components })
        (x : (product_diagonal_smoothObject (k := k) sourceX.1 sourceY.1).scheme),
        ∃ U :
          (product_diagonal_smoothObject (k := k) sourceX.1 sourceY.1).scheme.affineOpens,
          x ∈ U.1 ∧
          Algebra.IsStandardSmoothOfRelativeDimension 0 k
            (Γ((product_diagonal_smoothObject (k := k) sourceX.1 sourceY.1).scheme, U))) :
    SmCorQ.tensorHom family category (category.id X) (category.id Y) =
      category.id (overBaseProductObject X Y) := by
  exact
    SmCorQ.tensorHom_id_of_standardSmoothOfRelativeDimensionZeroReducedLocallyIrreducible
      family category X Y hStd0

/-- Correspondence-level tensor identity under the direct route
`relative-dimension-zero standard-smooth affine charts`
on each product model. -/
theorem boundaryEffectiveTensorProduct_id_of_standardSmoothOfRelativeDimensionZeroAffine
    (family : FiniteCorrespondence.TensorCompatibleExternalProductFamily (k := k))
    (category : SmCorQ (k := k))
    (X Y : Geometry.SmSchemeOver k)
    (hStd0 :
      ∀ (sourceX :
        { sourceX : SourceIrreducibleComponent X //
          sourceX ∈ (category.integral.composition.diagonalDecomposition X).components })
        (sourceY :
          { sourceY : SourceIrreducibleComponent Y //
          sourceY ∈ (category.integral.composition.diagonalDecomposition Y).components })
        (x : (product_diagonal_smoothObject (k := k) sourceX.1 sourceY.1).scheme),
        ∃ U :
          (product_diagonal_smoothObject (k := k) sourceX.1 sourceY.1).scheme.affineOpens,
          x ∈ U.1 ∧
          Algebra.IsStandardSmoothOfRelativeDimension 0 k
            (Γ((product_diagonal_smoothObject (k := k) sourceX.1 sourceY.1).scheme, U))) :
    FiniteCorrespondence.toRational
      (boundaryEffectiveTensorProductWithFamily (k := k) family
        (category.id X) (category.id Y)) =
    category.id (overBaseProductObject X Y) := by
  change
    FiniteCorrespondence.toRational
      (FiniteCorrespondence.externalProductWithFamily family.family
        (category.integral.composition.diagonalDecomposition X).identityFiniteCorrespondence
        (category.integral.composition.diagonalDecomposition Y).identityFiniteCorrespondence) =
    FiniteCorrespondence.toRational
      ((category.integral.composition.diagonalDecomposition
        (overBaseProductObject X Y)).identityFiniteCorrespondence)
  exact congrArg FiniteCorrespondence.toRational
    (SmCorQ.externalProductIdentity_of_standardSmoothOfRelativeDimensionZeroAffine
      family category X Y hStd0)

/-- `SmCorQ`-level tensor identity under the direct route
`relative-dimension-zero standard-smooth affine charts`
on each product model. -/
theorem boundaryEffectiveTensorProduct_tensorHom_id_of_standardSmoothOfRelativeDimensionZeroAffine
    (family : FiniteCorrespondence.TensorCompatibleExternalProductFamily (k := k))
    (category : SmCorQ (k := k))
    (X Y : Geometry.SmSchemeOver k)
    (hStd0 :
      ∀ (sourceX :
        { sourceX : SourceIrreducibleComponent X //
          sourceX ∈ (category.integral.composition.diagonalDecomposition X).components })
        (sourceY :
          { sourceY : SourceIrreducibleComponent Y //
          sourceY ∈ (category.integral.composition.diagonalDecomposition Y).components })
        (x : (product_diagonal_smoothObject (k := k) sourceX.1 sourceY.1).scheme),
        ∃ U :
          (product_diagonal_smoothObject (k := k) sourceX.1 sourceY.1).scheme.affineOpens,
          x ∈ U.1 ∧
          Algebra.IsStandardSmoothOfRelativeDimension 0 k
            (Γ((product_diagonal_smoothObject (k := k) sourceX.1 sourceY.1).scheme, U))) :
    SmCorQ.tensorHom family category (category.id X) (category.id Y) =
      category.id (overBaseProductObject X Y) := by
  exact
    SmCorQ.tensorHom_id_of_standardSmoothOfRelativeDimensionZeroAffine
      family category X Y hStd0

/-- Correspondence-level tensor identity for the current default
product-stable route. This mirrors `SmCorQ.externalProductIdentity_of_productStableDiagonal`
at the motive-prerequisite layer. -/
theorem boundaryEffectiveTensorProduct_id
    (family : FiniteCorrespondence.TensorCompatibleExternalProductFamily (k := k))
    (category : SmCorQ (k := k))
    (X Y : Geometry.SmSchemeOver k)
    (stableDX :
      (listed :
        { listed : SourceIrreducibleComponent X //
          listed ∈ (category.integral.composition.diagonalDecomposition X).components }) →
        ProductStableSourceComponent X)
    (hstableDX : ∀ listed, (stableDX listed).component = listed.1) :
    FiniteCorrespondence.toRational
      (boundaryEffectiveTensorProductWithFamily (k := k) family
        (category.id X) (category.id Y)) =
    category.id (overBaseProductObject X Y) := by
  change
    FiniteCorrespondence.toRational
      (FiniteCorrespondence.externalProductWithFamily family.family
        (category.integral.composition.diagonalDecomposition X).identityFiniteCorrespondence
        (category.integral.composition.diagonalDecomposition Y).identityFiniteCorrespondence) =
    FiniteCorrespondence.toRational
      ((category.integral.composition.diagonalDecomposition
        (overBaseProductObject X Y)).identityFiniteCorrespondence)
  exact congrArg FiniteCorrespondence.toRational
    (SmCorQ.externalProductIdentity_of_productStableDiagonal
      family category X Y stableDX hstableDX)

/-- `SmCorQ`-level tensor identity for the current default product-stable
route, exported at the motive-prerequisite layer. -/
theorem boundaryEffectiveTensorProduct_tensorHom_id
    (family : FiniteCorrespondence.TensorCompatibleExternalProductFamily (k := k))
    (category : SmCorQ (k := k))
    (X Y : Geometry.SmSchemeOver k)
    (stableDX :
      (listed :
        { listed : SourceIrreducibleComponent X //
          listed ∈ (category.integral.composition.diagonalDecomposition X).components }) →
        ProductStableSourceComponent X)
    (hstableDX : ∀ listed, (stableDX listed).component = listed.1) :
    SmCorQ.tensorHom family category (category.id X) (category.id Y) =
      category.id (overBaseProductObject X Y) := by
  exact
    SmCorQ.tensorHom_id family category X Y stableDX hstableDX

end

end Boundary
