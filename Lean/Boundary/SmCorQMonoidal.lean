import Boundary.GraphExternalProductCompatibility
import Mathlib.CategoryTheory.Monoidal.Category

/-!
# Monoidal structure for the canonical rational correspondence category

This file builds the structural morphisms needed for the tensor product on
`SmCorQ`: ordinary isomorphisms over `Spec k` become isomorphisms in the
rational correspondence category by graph transfer.
-/

universe u

open AlgebraicGeometry CategoryTheory

namespace Boundary

noncomputable section

variable {k : Type u} [Field k] [PerfectField k]

namespace SmCorQ

/-- Object part of the tensor product on the rational correspondence category:
fiber product over `Spec k`. -/
abbrev tensorObj (X Y : Geometry.SmSchemeOver k) : Geometry.SmSchemeOver k :=
  overBaseProductObject X Y

/-- Tensor unit object for the rational correspondence category. -/
abbrev tensorUnit : Geometry.SmSchemeOver k :=
  overBaseUnitObject (k := k)

/-- Morphism part of the tensor product, routed through the tensor-compatible
external-product owner. -/
def tensorHom
    (family : FiniteCorrespondence.TensorCompatibleExternalProductFamily (k := k))
    (category : SmCorQ (k := k))
    {X1 Y1 X2 Y2 : Geometry.SmSchemeOver k}
    (left : SmCorQ.Hom category X1 Y1)
    (right : SmCorQ.Hom category X2 Y2) :
    SmCorQ.Hom category (tensorObj X1 X2) (tensorObj Y1 Y2) :=
  letI : FiniteCorrespondence.CanonicalExternalProductFamily (k := k) :=
    family.toGraphIdentityCompatibleExternalProductFamily.toCanonicalExternalProductFamily
  category.externalProduct left right

@[simp] theorem tensorHom_zero_left
    (family : FiniteCorrespondence.TensorCompatibleExternalProductFamily (k := k))
    (category : SmCorQ (k := k))
    {X1 Y1 X2 Y2 : Geometry.SmSchemeOver k}
    (right : SmCorQ.Hom category X2 Y2) :
    tensorHom family category (0 : SmCorQ.Hom category X1 Y1) right = 0 := by
  letI : FiniteCorrespondence.CanonicalExternalProductFamily (k := k) :=
    family.toGraphIdentityCompatibleExternalProductFamily.toCanonicalExternalProductFamily
  exact SmCorQ.externalProduct_zero_left category right

@[simp] theorem tensorHom_zero_right
    (family : FiniteCorrespondence.TensorCompatibleExternalProductFamily (k := k))
    (category : SmCorQ (k := k))
    {X1 Y1 X2 Y2 : Geometry.SmSchemeOver k}
    (left : SmCorQ.Hom category X1 Y1) :
    tensorHom family category left (0 : SmCorQ.Hom category X2 Y2) = 0 := by
  letI : FiniteCorrespondence.CanonicalExternalProductFamily (k := k) :=
    family.toGraphIdentityCompatibleExternalProductFamily.toCanonicalExternalProductFamily
  exact SmCorQ.externalProduct_zero_right category left

theorem tensorHom_add_left
    (family : FiniteCorrespondence.TensorCompatibleExternalProductFamily (k := k))
    (category : SmCorQ (k := k))
    {X1 Y1 X2 Y2 : Geometry.SmSchemeOver k}
    (left₁ left₂ : SmCorQ.Hom category X1 Y1)
    (right : SmCorQ.Hom category X2 Y2) :
    tensorHom family category (left₁ + left₂) right =
      tensorHom family category left₁ right +
        tensorHom family category left₂ right := by
  letI : FiniteCorrespondence.CanonicalExternalProductFamily (k := k) :=
    family.toGraphIdentityCompatibleExternalProductFamily.toCanonicalExternalProductFamily
  exact SmCorQ.externalProduct_add_left category left₁ left₂ right

theorem tensorHom_add_right
    (family : FiniteCorrespondence.TensorCompatibleExternalProductFamily (k := k))
    (category : SmCorQ (k := k))
    {X1 Y1 X2 Y2 : Geometry.SmSchemeOver k}
    (left : SmCorQ.Hom category X1 Y1)
    (right₁ right₂ : SmCorQ.Hom category X2 Y2) :
    tensorHom family category left (right₁ + right₂) =
      tensorHom family category left right₁ +
        tensorHom family category left right₂ := by
  letI : FiniteCorrespondence.CanonicalExternalProductFamily (k := k) :=
    family.toGraphIdentityCompatibleExternalProductFamily.toCanonicalExternalProductFamily
  exact SmCorQ.externalProduct_add_right category left right₁ right₂

theorem tensorHom_smul_left
    (family : FiniteCorrespondence.TensorCompatibleExternalProductFamily (k := k))
    (category : SmCorQ (k := k))
    {X1 Y1 X2 Y2 : Geometry.SmSchemeOver k}
    (coeff : ℚ)
    (left : SmCorQ.Hom category X1 Y1)
    (right : SmCorQ.Hom category X2 Y2) :
    tensorHom family category (coeff • left) right =
      coeff • tensorHom family category left right := by
  letI : FiniteCorrespondence.CanonicalExternalProductFamily (k := k) :=
    family.toGraphIdentityCompatibleExternalProductFamily.toCanonicalExternalProductFamily
  exact SmCorQ.externalProduct_smul_left category coeff left right

theorem tensorHom_smul_right
    (family : FiniteCorrespondence.TensorCompatibleExternalProductFamily (k := k))
    (category : SmCorQ (k := k))
    {X1 Y1 X2 Y2 : Geometry.SmSchemeOver k}
    (coeff : ℚ)
    (left : SmCorQ.Hom category X1 Y1)
    (right : SmCorQ.Hom category X2 Y2) :
    tensorHom family category left (coeff • right) =
      coeff • tensorHom family category left right := by
  letI : FiniteCorrespondence.CanonicalExternalProductFamily (k := k) :=
    family.toGraphIdentityCompatibleExternalProductFamily.toCanonicalExternalProductFamily
  exact SmCorQ.externalProduct_smul_right category coeff left right

/-- Tensor morphisms compose by the tensor-compatible external product
interchange theorem. This is the bifunctoriality core of the monoidal tensor
functor. -/
theorem tensorHom_comp
    (family : FiniteCorrespondence.TensorCompatibleExternalProductFamily (k := k))
    (category : SmCorQ (k := k))
    {W1 X1 Y1 W2 X2 Y2 : Geometry.SmSchemeOver k}
    (f : SmCorQ.Hom category W1 X1)
    (g : SmCorQ.Hom category X1 Y1)
    (f' : SmCorQ.Hom category W2 X2)
    (g' : SmCorQ.Hom category X2 Y2) :
    tensorHom family category (category.comp f g) (category.comp f' g')
      =
        category.comp
          (tensorHom family category f f')
          (tensorHom family category g g') := by
  letI : FiniteCorrespondence.CanonicalExternalProductFamily (k := k) :=
    family.toGraphIdentityCompatibleExternalProductFamily.toCanonicalExternalProductFamily
  exact
    SmCorQ.externalProduct_comp_interchange_of_tensorCompatibleFamily
      (k := k) family category f g f' g'

/-- Tensoring the two rational identity correspondences gives the rational
identity on the product, provided the chosen diagonal decomposition of the left
factor has product-stable listed components.

This is deliberately stated with the exact geometric input. The proof
uses the owner theorem that external products of diagonal identities identify
with any certified decomposition of the product, then specializes that product
decomposition to the one carried by the rational composition package. -/
theorem tensorHom_id_of_productStableDiagonal
    (family : FiniteCorrespondence.TensorCompatibleExternalProductFamily (k := k))
    (category : SmCorQ (k := k))
    (X Y : Geometry.SmSchemeOver k)
    (stableDX :
      (listed :
        { listed : SourceIrreducibleComponent X //
          listed ∈ (category.integral.composition.diagonalDecomposition X).components }) →
        ProductStableSourceComponent X)
    (hstableDX : ∀ listed, (stableDX listed).component = listed.1) :
    tensorHom family category (category.id X) (category.id Y) =
      category.id (tensorObj X Y) := by
  letI : FiniteCorrespondence.CanonicalExternalProductFamily (k := k) :=
    family.toGraphIdentityCompatibleExternalProductFamily.toCanonicalExternalProductFamily
  let DX := category.integral.composition.diagonalDecomposition X
  let DY := category.integral.composition.diagonalDecomposition Y
  let DXY := category.integral.composition.diagonalDecomposition (tensorObj X Y)
  calc
    tensorHom family category (category.id X) (category.id Y)
        = category.externalProduct
            (FiniteCorrespondence.toRational DX.identityFiniteCorrespondence)
            (FiniteCorrespondence.toRational DY.identityFiniteCorrespondence) := by
          simp [tensorHom, DX, DY, SmCorQ.id_eq_toRational_id,
            FiniteCorrespondenceCompositionData.id]
    _ = FiniteCorrespondence.toRational
          (FiniteCorrespondence.externalProductWithFamily family.family
            DX.identityFiniteCorrespondence DY.identityFiniteCorrespondence) := by
          exact
            SmCorQ.externalProduct_toRational
              (category := category)
              DX.identityFiniteCorrespondence DY.identityFiniteCorrespondence
    _ = FiniteCorrespondence.toRational DXY.identityFiniteCorrespondence := by
          exact FiniteCorrespondence.externalProduct_id_right_of_product_decomposition
            family.toGraphIdentityCompatibleExternalProductFamily category
            DX DY stableDX hstableDX DXY
    _ = category.id (tensorObj X Y) := by
          simp [DXY, SmCorQ.id_eq_toRational_id,
            FiniteCorrespondenceCompositionData.id]

/-- Tensoring a graph transfer on the right by an identity correspondence gives
the graph transfer of the product morphism `f × id`, for the product
decomposition constructed from the listed factor components. -/
theorem tensorHom_graphTransfer_id_right
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
    tensorHom family category
        (SmCorQ.graphTransfer category f DX)
        (FiniteCorrespondence.toRational DZ.identityFiniteCorrespondence) =
      SmCorQ.graphTransfer category
        (overBaseProductMap f (𝟙 Z))
        (_root_.Boundary.finiteProductSourceIrreducibleComponentDecomposition
          DX DZ stableDX hstableDX) := by
  letI : FiniteCorrespondence.CanonicalExternalProductFamily (k := k) :=
    family.toGraphIdentityCompatibleExternalProductFamily.toCanonicalExternalProductFamily
  calc
    tensorHom family category
        (SmCorQ.graphTransfer category f DX)
        (FiniteCorrespondence.toRational DZ.identityFiniteCorrespondence)
      = FiniteCorrespondence.toRational
          (FiniteCorrespondence.externalProductWithFamily family.family
            (Geometry.ordinaryMorphismGraph_finiteCorrespondenceOfDecomposition f DX)
            DZ.identityFiniteCorrespondence) := by
          simpa [tensorHom, SmCorQ.graphTransfer,
            Geometry.ordinaryMorphismGraph_rationalCorrespondenceOfDecomposition,
            FiniteCorrespondence.externalProduct] using
            SmCorQ.externalProduct_toRational
              (category := category)
              (Geometry.ordinaryMorphismGraph_finiteCorrespondenceOfDecomposition f DX)
              DZ.identityFiniteCorrespondence
    _ = SmCorQ.graphTransfer category
        (overBaseProductMap f (𝟙 Z))
        (_root_.Boundary.finiteProductSourceIrreducibleComponentDecomposition
          DX DZ stableDX hstableDX) := by
          exact
            FiniteCorrespondence.GraphIdentityCompatibleExternalProductFamily.externalProduct_graphTransfer_id_right
              family.toGraphIdentityCompatibleExternalProductFamily
              category DX DZ stableDX hstableDX f

/-- Left-handed graph-transfer tensor identity. -/
theorem tensorHom_id_left_graphTransfer
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
    tensorHom family category
        (FiniteCorrespondence.toRational DX.identityFiniteCorrespondence)
        (SmCorQ.graphTransfer category g DY) =
      SmCorQ.graphTransfer category
        (overBaseProductMap (𝟙 X) g)
        (_root_.Boundary.finiteProductSourceIrreducibleComponentDecomposition
          DX DY stableDX hstableDX) := by
  letI : FiniteCorrespondence.CanonicalExternalProductFamily (k := k) :=
    family.toGraphIdentityCompatibleExternalProductFamily.toCanonicalExternalProductFamily
  calc
    tensorHom family category
        (FiniteCorrespondence.toRational DX.identityFiniteCorrespondence)
        (SmCorQ.graphTransfer category g DY)
      = FiniteCorrespondence.toRational
          (FiniteCorrespondence.externalProductWithFamily family.family
            DX.identityFiniteCorrespondence
            (Geometry.ordinaryMorphismGraph_finiteCorrespondenceOfDecomposition g DY)) := by
          simpa [tensorHom, SmCorQ.graphTransfer,
            Geometry.ordinaryMorphismGraph_rationalCorrespondenceOfDecomposition,
            FiniteCorrespondence.externalProduct] using
            SmCorQ.externalProduct_toRational
              (category := category)
              DX.identityFiniteCorrespondence
              (Geometry.ordinaryMorphismGraph_finiteCorrespondenceOfDecomposition g DY)
    _ = SmCorQ.graphTransfer category
        (overBaseProductMap (𝟙 X) g)
        (_root_.Boundary.finiteProductSourceIrreducibleComponentDecomposition
          DX DY stableDX hstableDX) := by
          exact
            FiniteCorrespondence.GraphIdentityCompatibleExternalProductFamily.externalProduct_id_left_graphTransfer
              family.toGraphIdentityCompatibleExternalProductFamily
              category DX DY stableDX hstableDX g

/-- An ordinary isomorphism of smooth schemes over `Spec k` induces an
isomorphism in the canonical rational correspondence category by graph
transfer. -/
noncomputable def isoOfSmOverIso
    (composition : Boundary.CanonicalCompositionData (k := k))
    (hgraph : Geometry.CanonicalGraphPackageCompatibilityObligation composition)
    {X Y : Geometry.SmSchemeOver k}
    (e : X ≅ Y) :
    letI := SmCorQCat (Boundary.canonicalCategory composition)
    X ≅ Y := by
  let category := Boundary.canonicalCategory composition
  letI := SmCorQCat category
  refine
    { hom :=
        SmCorQ.graphTransfer category e.hom
          (composition.diagonalDecomposition X)
      inv :=
        SmCorQ.graphTransfer category e.inv
          (composition.diagonalDecomposition Y)
      hom_inv_id := ?_
      inv_hom_id := ?_ }
  · change category.comp
        (SmCorQ.graphTransfer category e.hom
          (composition.diagonalDecomposition X))
        (SmCorQ.graphTransfer category e.inv
          (composition.diagonalDecomposition Y)) =
      category.id X
    calc
      category.comp
          (SmCorQ.graphTransfer category e.hom
            (composition.diagonalDecomposition X))
          (SmCorQ.graphTransfer category e.inv
            (composition.diagonalDecomposition Y))
          = SmCorQ.graphTransfer category
              (Boundary.SmOverHom.comp e.hom e.inv)
              (composition.diagonalDecomposition X) := by
            simpa using
              canonicalCategory_graphTransfer_comp
                (composition := composition) hgraph e.hom e.inv
      _ = SmCorQ.graphTransfer category (Boundary.SmOverHom.id X)
              (composition.diagonalDecomposition X) := by
            congr 1
            apply Boundary.SmOverHom.ext
            exact e.hom_inv_id
      _ = category.id X := by
            simpa using
              canonicalCategory_graphTransfer_id (composition := composition) (X := X)
  · change category.comp
        (SmCorQ.graphTransfer category e.inv
          (composition.diagonalDecomposition Y))
        (SmCorQ.graphTransfer category e.hom
          (composition.diagonalDecomposition X)) =
      category.id Y
    calc
      category.comp
          (SmCorQ.graphTransfer category e.inv
            (composition.diagonalDecomposition Y))
          (SmCorQ.graphTransfer category e.hom
            (composition.diagonalDecomposition X))
          = SmCorQ.graphTransfer category
              (Boundary.SmOverHom.comp e.inv e.hom)
              (composition.diagonalDecomposition Y) := by
            simpa using
              canonicalCategory_graphTransfer_comp
                (composition := composition) hgraph e.inv e.hom
      _ = SmCorQ.graphTransfer category (Boundary.SmOverHom.id Y)
              (composition.diagonalDecomposition Y) := by
            congr 1
            apply Boundary.SmOverHom.ext
            exact e.inv_hom_id
      _ = category.id Y := by
            simpa using
              canonicalCategory_graphTransfer_id (composition := composition) (X := Y)

/-- The correspondence-category associator induced by the geometric product
associator. -/
noncomputable def productAssociatorIso
    (composition : Boundary.CanonicalCompositionData (k := k))
    (hgraph : Geometry.CanonicalGraphPackageCompatibilityObligation composition)
    (X Y Z : Geometry.SmSchemeOver k) :
    letI := SmCorQCat (Boundary.canonicalCategory composition)
    overBaseProductObject (overBaseProductObject X Y) Z ≅
      overBaseProductObject X (overBaseProductObject Y Z) :=
  isoOfSmOverIso composition hgraph (overBaseProductAssoc X Y Z)

/-- The correspondence-category left unitor induced by the geometric product
left unitor. -/
noncomputable def productLeftUnitorIso
    (composition : Boundary.CanonicalCompositionData (k := k))
    (hgraph : Geometry.CanonicalGraphPackageCompatibilityObligation composition)
    (X : Geometry.SmSchemeOver k) :
    letI := SmCorQCat (Boundary.canonicalCategory composition)
    overBaseProductObject (overBaseUnitObject (k := k)) X ≅ X :=
  isoOfSmOverIso composition hgraph (overBaseProductLeftUnitor X)

/-- The correspondence-category right unitor induced by the geometric product
right unitor. -/
noncomputable def productRightUnitorIso
    (composition : Boundary.CanonicalCompositionData (k := k))
    (hgraph : Geometry.CanonicalGraphPackageCompatibilityObligation composition)
    (X : Geometry.SmSchemeOver k) :
    letI := SmCorQCat (Boundary.canonicalCategory composition)
    overBaseProductObject X (overBaseUnitObject (k := k)) ≅ X :=
  isoOfSmOverIso composition hgraph (overBaseProductRightUnitor X)

end SmCorQ

end

end Boundary
