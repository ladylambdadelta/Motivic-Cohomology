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

/-- Core tensor-identity reduction: once the correspondence-level owner theorem
identifies the external product of the two identity finite correspondences with
the canonical identity finite correspondence on `X ×_k Y`, the rational tensor
identity in `SmCorQ` follows formally. This isolates the category-level algebra
from any particular geometric route to the identity-support decomposition. -/
theorem tensorHom_id_of_externalProductIdentity
    (family : FiniteCorrespondence.TensorCompatibleExternalProductFamily (k := k))
    (category : SmCorQ (k := k))
    (X Y : Geometry.SmSchemeOver k)
    (hIdentity :
      FiniteCorrespondence.externalProductWithFamily family.family
          (category.integral.composition.diagonalDecomposition X).identityFiniteCorrespondence
          (category.integral.composition.diagonalDecomposition Y).identityFiniteCorrespondence =
        (category.integral.composition.diagonalDecomposition
          (tensorObj X Y)).identityFiniteCorrespondence) :
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
          exact congrArg FiniteCorrespondence.toRational hIdentity
    _ = category.id (tensorObj X Y) := by
          simp [DXY, SmCorQ.id_eq_toRational_id,
            FiniteCorrespondenceCompositionData.id]

/-- Conditional product-component route to the correspondence-level identity
theorem. This remains as an auxiliary lemma until the direct product-support
decomposition proof replaces it upstream. -/
theorem externalProductIdentity_of_productStableDiagonal
    (family : FiniteCorrespondence.TensorCompatibleExternalProductFamily (k := k))
    (category : SmCorQ (k := k))
    (X Y : Geometry.SmSchemeOver k)
    (stableDX :
      (listed :
        { listed : SourceIrreducibleComponent X //
          listed ∈ (category.integral.composition.diagonalDecomposition X).components }) →
        ProductStableSourceComponent X)
    (hstableDX : ∀ listed, (stableDX listed).component = listed.1) :
    FiniteCorrespondence.externalProductWithFamily family.family
        (category.integral.composition.diagonalDecomposition X).identityFiniteCorrespondence
        (category.integral.composition.diagonalDecomposition Y).identityFiniteCorrespondence =
      (category.integral.composition.diagonalDecomposition
        (tensorObj X Y)).identityFiniteCorrespondence := by
  let DX := category.integral.composition.diagonalDecomposition X
  let DY := category.integral.composition.diagonalDecomposition Y
  let DXY := category.integral.composition.diagonalDecomposition (tensorObj X Y)
  calc
    FiniteCorrespondence.externalProductWithFamily family.family
        DX.identityFiniteCorrespondence DY.identityFiniteCorrespondence =
      (_root_.Boundary.finiteProductSourceIrreducibleComponentDecomposition
        DX DY stableDX hstableDX).identityFiniteCorrespondence := by
        exact
          FiniteCorrespondence
            .externalProductWithFamily_identity_identity_eq_identityFiniteCorrespondence
            family.toGraphIdentityCompatibleExternalProductFamily
            DX DY stableDX hstableDX
    _ = DXY.identityFiniteCorrespondence := by
        exact
          FiniteIrreducibleComponentDecomposition.identityFiniteCorrespondence_independent
            (_root_.Boundary.finiteProductSourceIrreducibleComponentDecomposition
              DX DY stableDX hstableDX)
            DXY

/-- Clean correspondence-level tensor-identity theorem under locally
irreducible product-model geometry. This replaces the false product-stability
route by the actual owner theorem on diagonal-product decompositions. -/
theorem externalProductIdentity_of_locallyIrreducible
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
    FiniteCorrespondence.externalProductWithFamily family.family
        (category.integral.composition.diagonalDecomposition X).identityFiniteCorrespondence
        (category.integral.composition.diagonalDecomposition Y).identityFiniteCorrespondence =
      (category.integral.composition.diagonalDecomposition
        (tensorObj X Y)).identityFiniteCorrespondence := by
  let DX := category.integral.composition.diagonalDecomposition X
  let DY := category.integral.composition.diagonalDecomposition Y
  let DXY := category.integral.composition.diagonalDecomposition (tensorObj X Y)
  exact
    FiniteCorrespondence
      .externalProductWithFamily_identity_identity_eq_identityFiniteCorrespondence_of_locallyIrreducible
      (k := k) family.family DX DY DXY
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

/-- Category-level tensor identity under locally irreducible product-model
geometry. -/
theorem tensorHom_id_of_locallyIrreducible
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
    tensorHom family category (category.id X) (category.id Y) =
      category.id (tensorObj X Y) :=
  tensorHom_id_of_externalProductIdentity family category X Y
    (externalProductIdentity_of_locallyIrreducible
      family category X Y hLoc hIntegral)

/-- Reduced locally irreducible specialization of the clean correspondence-level
tensor-identity theorem. -/
theorem externalProductIdentity_of_reducedLocallyIrreducible
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
    FiniteCorrespondence.externalProductWithFamily family.family
        (category.integral.composition.diagonalDecomposition X).identityFiniteCorrespondence
        (category.integral.composition.diagonalDecomposition Y).identityFiniteCorrespondence =
      (category.integral.composition.diagonalDecomposition
        (tensorObj X Y)).identityFiniteCorrespondence := by
  exact
    externalProductIdentity_of_locallyIrreducible family category X Y hLoc
      (fun sourceX sourceY C => by
        letI := hReduced sourceX sourceY
        exact
          irreducibleComponentOpen_isIntegral_of_isReduced_locallyIrreducible
            (product_diagonal_smoothObject (k := k) sourceX.1 sourceY.1).scheme
            (hLoc sourceX sourceY) C)

/-- Reduced locally irreducible specialization of the category-level tensor
identity theorem. -/
theorem tensorHom_id_of_reducedLocallyIrreducible
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
    tensorHom family category (category.id X) (category.id Y) =
      category.id (tensorObj X Y) :=
  tensorHom_id_of_externalProductIdentity family category X Y
    (externalProductIdentity_of_reducedLocallyIrreducible
      family category X Y hLoc hReduced)

/-- Clean correspondence-level tensor-identity theorem under the alternative
bottom geometry route `IsReduced + irreducible components open` on each
product model. -/
theorem externalProductIdentity_of_reducedComponentsOpen
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
    FiniteCorrespondence.externalProductWithFamily family.family
        (category.integral.composition.diagonalDecomposition X).identityFiniteCorrespondence
        (category.integral.composition.diagonalDecomposition Y).identityFiniteCorrespondence =
      (category.integral.composition.diagonalDecomposition
        (tensorObj X Y)).identityFiniteCorrespondence := by
  let DX := category.integral.composition.diagonalDecomposition X
  let DY := category.integral.composition.diagonalDecomposition Y
  let DXY := category.integral.composition.diagonalDecomposition (tensorObj X Y)
  exact
    FiniteCorrespondence
      .externalProductWithFamily_identity_identity_eq_identityFiniteCorrespondence_of_reduced_componentsOpen
      (k := k) family.family DX DY DXY
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

/-- Category-level tensor identity under the alternative bottom geometry route
`IsReduced + irreducible components open` on each product model. -/
theorem tensorHom_id_of_reducedComponentsOpen
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
    tensorHom family category (category.id X) (category.id Y) =
      category.id (tensorObj X Y) :=
  tensorHom_id_of_externalProductIdentity family category X Y
    (externalProductIdentity_of_reducedComponentsOpen
      family category X Y hOpen hReduced)

/-- Clean correspondence-level tensor-identity theorem under the route
`components open + relative-dimension-zero standard-smooth affine charts`
on each product model. -/
theorem externalProductIdentity_of_standardSmoothOfRelativeDimensionZeroComponentsOpen
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
    FiniteCorrespondence.externalProductWithFamily family.family
        (category.integral.composition.diagonalDecomposition X).identityFiniteCorrespondence
        (category.integral.composition.diagonalDecomposition Y).identityFiniteCorrespondence =
      (category.integral.composition.diagonalDecomposition
        (tensorObj X Y)).identityFiniteCorrespondence := by
  let DX := category.integral.composition.diagonalDecomposition X
  let DY := category.integral.composition.diagonalDecomposition Y
  let DXY := category.integral.composition.diagonalDecomposition (tensorObj X Y)
  exact
    FiniteCorrespondence
      .externalProductWithFamily_identity_identity_eq_identityFiniteCorrespondence_of_standardSmoothOfRelativeDimensionZero_componentsOpen
      (k := k) family.family DX DY DXY
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
      hOpen hStd0

/-- Category-level tensor identity under the route
`components open + relative-dimension-zero standard-smooth affine charts`
on each product model. -/
theorem tensorHom_id_of_standardSmoothOfRelativeDimensionZeroComponentsOpen
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
    tensorHom family category (category.id X) (category.id Y) =
      category.id (tensorObj X Y) :=
  tensorHom_id_of_externalProductIdentity family category X Y
    (externalProductIdentity_of_standardSmoothOfRelativeDimensionZeroComponentsOpen
      family category X Y hOpen hStd0)

/-- Clean correspondence-level tensor-identity theorem under the route
`reduced locally irreducible + relative-dimension-zero standard-smooth affine charts`
on each product model. -/
theorem externalProductIdentity_of_standardSmoothOfRelativeDimensionZeroReducedLocallyIrreducible
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
    FiniteCorrespondence.externalProductWithFamily family.family
        (category.integral.composition.diagonalDecomposition X).identityFiniteCorrespondence
        (category.integral.composition.diagonalDecomposition Y).identityFiniteCorrespondence =
      (category.integral.composition.diagonalDecomposition
        (tensorObj X Y)).identityFiniteCorrespondence := by
  let DX := category.integral.composition.diagonalDecomposition X
  let DY := category.integral.composition.diagonalDecomposition Y
  let DXY := category.integral.composition.diagonalDecomposition (tensorObj X Y)
  exact
    FiniteCorrespondence
      .externalProductWithFamily_identity_identity_eq_identityFiniteCorrespondence_of_standardSmoothOfRelativeDimensionZero_reducedLocallyIrreducible
      (k := k) family.family DX DY DXY
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
      hStd0

/-- Category-level tensor identity under the route
`reduced locally irreducible + relative-dimension-zero standard-smooth affine charts`
on each product model. -/
theorem tensorHom_id_of_standardSmoothOfRelativeDimensionZeroReducedLocallyIrreducible
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
    tensorHom family category (category.id X) (category.id Y) =
      category.id (tensorObj X Y) :=
  tensorHom_id_of_externalProductIdentity family category X Y
    (externalProductIdentity_of_standardSmoothOfRelativeDimensionZeroReducedLocallyIrreducible
      family category X Y hStd0)

/-- Direct correspondence-level tensor-identity theorem from the
relative-dimension-zero standard-smooth affine chart hypothesis on each product
model. -/
theorem externalProductIdentity_of_standardSmoothOfRelativeDimensionZeroAffine
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
    FiniteCorrespondence.externalProductWithFamily family.family
        (category.integral.composition.diagonalDecomposition X).identityFiniteCorrespondence
        (category.integral.composition.diagonalDecomposition Y).identityFiniteCorrespondence =
      (category.integral.composition.diagonalDecomposition
        (tensorObj X Y)).identityFiniteCorrespondence := by
  let DX := category.integral.composition.diagonalDecomposition X
  let DY := category.integral.composition.diagonalDecomposition Y
  let DXY := category.integral.composition.diagonalDecomposition (tensorObj X Y)
  exact
    FiniteCorrespondence
      .externalProductWithFamily_identity_identity_eq_identityFiniteCorrespondence_of_standardSmoothOfRelativeDimensionZeroAffine
      (k := k) family.family DX DY DXY
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
              (product_diagonal_smoothObject_irreducibleComponentsOpen_of_standardSmoothOfRelativeDimensionZeroAffine
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
              .product_diagonal_smoothObjectRealizationOfReducedComponentsOpen
              (k := k) sourceX.1 sourceY.1
              (product_diagonal_smoothObject_irreducibleComponentsOpen_of_standardSmoothOfRelativeDimensionZeroAffine
                (k := k) sourceX.1 sourceY.1 (hStd0 sourceX sourceY))))
          i)
      hStd0

/-- Direct category-level tensor-identity theorem from the
relative-dimension-zero standard-smooth affine chart hypothesis on each product
model. -/
theorem tensorHom_id_of_standardSmoothOfRelativeDimensionZeroAffine
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
    tensorHom family category (category.id X) (category.id Y) =
      category.id (tensorObj X Y) :=
  tensorHom_id_of_externalProductIdentity family category X Y
    (externalProductIdentity_of_standardSmoothOfRelativeDimensionZeroAffine
      family category X Y hStd0)

/-- Public tensor identity theorem for the current product-component route.
The only remaining geometric input is the existing product-stability witness
for the listed components of the chosen left diagonal decomposition. -/
theorem tensorHom_id
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
      category.id (tensorObj X Y) :=
  tensorHom_id_of_externalProductIdentity family category X Y
    (externalProductIdentity_of_productStableDiagonal
      family category X Y stableDX hstableDX)

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

/-- Tensoring a graph transfer on the right by an identity correspondence may
target any certified decomposition of the product object, since graph transfer
is independent of the chosen source decomposition. -/
theorem tensorHom_graphTransfer_id_right_of_product_decomposition
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
    tensorHom family category
        (SmCorQ.graphTransfer category f DX)
        (FiniteCorrespondence.toRational DZ.identityFiniteCorrespondence) =
      SmCorQ.graphTransfer category
        (overBaseProductMap f (𝟙 Z))
        DProduct := by
  letI : FiniteCorrespondence.CanonicalExternalProductFamily (k := k) :=
    family.toGraphIdentityCompatibleExternalProductFamily.toCanonicalExternalProductFamily
  calc
    tensorHom family category
        (SmCorQ.graphTransfer category f DX)
        (FiniteCorrespondence.toRational DZ.identityFiniteCorrespondence) =
      FiniteCorrespondence.toRational
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
        DProduct := by
          exact
            FiniteCorrespondence.GraphIdentityCompatibleExternalProductFamily
              .externalProduct_graphTransfer_id_right_of_product_decomposition
              family.toGraphIdentityCompatibleExternalProductFamily
              category DX DZ stableDX hstableDX DProduct f

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

/-- Tensoring an identity correspondence on the left by a graph transfer may
target any certified decomposition of the product object, since graph transfer
is independent of the chosen source decomposition. -/
theorem tensorHom_id_left_graphTransfer_of_product_decomposition
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
    tensorHom family category
        (FiniteCorrespondence.toRational DX.identityFiniteCorrespondence)
        (SmCorQ.graphTransfer category g DY) =
      SmCorQ.graphTransfer category
        (overBaseProductMap (𝟙 X) g)
        DProduct := by
  letI : FiniteCorrespondence.CanonicalExternalProductFamily (k := k) :=
    family.toGraphIdentityCompatibleExternalProductFamily.toCanonicalExternalProductFamily
  calc
    tensorHom family category
        (FiniteCorrespondence.toRational DX.identityFiniteCorrespondence)
        (SmCorQ.graphTransfer category g DY) =
      FiniteCorrespondence.toRational
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
        DProduct := by
          exact
            FiniteCorrespondence.GraphIdentityCompatibleExternalProductFamily
              .externalProduct_id_left_graphTransfer_of_product_decomposition
              family.toGraphIdentityCompatibleExternalProductFamily
              category DX DY stableDX hstableDX DProduct g

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
            exact
              canonicalCategory_graphTransfer_comp
                (composition := composition) hgraph e.hom e.inv
      _ = SmCorQ.graphTransfer category (Boundary.SmOverHom.id X)
              (composition.diagonalDecomposition X) := by
            congr 1
            apply Boundary.SmOverHom.ext
            exact e.hom_inv_id
      _ = category.id X := by
            exact
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
            exact
              canonicalCategory_graphTransfer_comp
                (composition := composition) hgraph e.inv e.hom
      _ = SmCorQ.graphTransfer category (Boundary.SmOverHom.id Y)
              (composition.diagonalDecomposition Y) := by
            congr 1
            apply Boundary.SmOverHom.ext
            exact e.inv_hom_id
      _ = category.id Y := by
            exact
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
