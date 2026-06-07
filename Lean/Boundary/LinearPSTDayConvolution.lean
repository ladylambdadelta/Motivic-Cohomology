import Boundary.SmCorQMonoidal
import Boundary.PresheavesWithTransfers

/-!
# Day convolution for linear presheaves with transfers

This file owns the `LinearPST` tensor construction induced by the correspondence
tensor on `SmCorQ`.  The representable layer constructed here identifies the
Day tensor of representables with the representable attached to the product
object of `SmCorQ`, and records the functorial algebra needed by
effective-motive generator arguments.

For Day convolution on functor categories, cf. Day, "On closed categories of
functors". For the motivic tensor product on correspondences and motives, cf.
Voevodsky, "Triangulated categories of motives over a field", §2.
-/

universe u

open AlgebraicGeometry CategoryTheory

namespace Boundary

noncomputable section

variable {k : Type u} [Field k] [PerfectField k]

namespace LinearPSTDayConvolution

/-- Object-level representable Day tensor: on representables, Day convolution
is represented by the tensor product object in `SmCorQ`; cf. Day, "On closed
categories of functors". -/
abbrev representableTensor
    (category : SmCorQ (k := k))
    (X Y : Geometry.SmSchemeOver k) :
    LinearPST category :=
  QtrLinear (category := category) (SmCorQ.tensorObj X Y)

/-- Public notation-free name for the tensor of two representable linear
presheaves with transfers. -/
abbrev QtrTensor
    (category : SmCorQ (k := k))
    (X Y : Geometry.SmSchemeOver k) :
    LinearPST category :=
  representableTensor category X Y

@[simp] theorem QtrTensor_toPST
    (category : SmCorQ (k := k))
    (X Y : Geometry.SmSchemeOver k) :
    (QtrTensor category X Y).toPST =
      Qtr (category := category) (SmCorQ.tensorObj X Y) :=
  rfl

/-- The represented object underlying the tensor of representables is the
fiber product over `Spec k`. -/
theorem QtrTensor_represents_product
    (category : SmCorQ (k := k))
    (X Y : Geometry.SmSchemeOver k) :
    QtrTensor category X Y =
      QtrLinear (category := category) (overBaseProductObject X Y) :=
  rfl

/-- Morphism on representable Day tensors induced by the correspondence-level
tensor product. -/
def QtrTensorMap
    (family : FiniteCorrespondence.TensorCompatibleExternalProductFamily (k := k))
    (category : SmCorQ (k := k))
    {X₁ Y₁ X₂ Y₂ : Geometry.SmSchemeOver k}
    (left : SmCorQ.Hom category X₁ Y₁)
    (right : SmCorQ.Hom category X₂ Y₂) :
    QtrTensor category X₁ X₂ ⟶ QtrTensor category Y₁ Y₂ :=
  QtrMap (category := category) (SmCorQ.tensorHom family category left right)

@[simp] theorem QtrTensorMap_zero_left
    (family : FiniteCorrespondence.TensorCompatibleExternalProductFamily (k := k))
    (category : SmCorQ (k := k))
    {X₁ Y₁ X₂ Y₂ : Geometry.SmSchemeOver k}
    (right : SmCorQ.Hom category X₂ Y₂) :
    QtrTensorMap family category (0 : SmCorQ.Hom category X₁ Y₁) right = 0 := by
  simp [QtrTensorMap]

@[simp] theorem QtrTensorMap_zero_right
    (family : FiniteCorrespondence.TensorCompatibleExternalProductFamily (k := k))
    (category : SmCorQ (k := k))
    {X₁ Y₁ X₂ Y₂ : Geometry.SmSchemeOver k}
    (left : SmCorQ.Hom category X₁ Y₁) :
    QtrTensorMap family category left (0 : SmCorQ.Hom category X₂ Y₂) = 0 := by
  simp [QtrTensorMap]

theorem QtrTensorMap_add_left
    (family : FiniteCorrespondence.TensorCompatibleExternalProductFamily (k := k))
    (category : SmCorQ (k := k))
    {X₁ Y₁ X₂ Y₂ : Geometry.SmSchemeOver k}
    (left₁ left₂ : SmCorQ.Hom category X₁ Y₁)
    (right : SmCorQ.Hom category X₂ Y₂) :
    QtrTensorMap family category (left₁ + left₂) right =
      QtrTensorMap family category left₁ right +
        QtrTensorMap family category left₂ right := by
  change
    QtrMap (category := category)
        (SmCorQ.tensorHom family category (left₁ + left₂) right) =
      QtrMap (category := category) (SmCorQ.tensorHom family category left₁ right) +
        QtrMap (category := category) (SmCorQ.tensorHom family category left₂ right)
  rw [SmCorQ.tensorHom_add_left]
  exact QtrMap_add (category := category)
    (SmCorQ.tensorHom family category left₁ right)
    (SmCorQ.tensorHom family category left₂ right)

theorem QtrTensorMap_add_right
    (family : FiniteCorrespondence.TensorCompatibleExternalProductFamily (k := k))
    (category : SmCorQ (k := k))
    {X₁ Y₁ X₂ Y₂ : Geometry.SmSchemeOver k}
    (left : SmCorQ.Hom category X₁ Y₁)
    (right₁ right₂ : SmCorQ.Hom category X₂ Y₂) :
    QtrTensorMap family category left (right₁ + right₂) =
      QtrTensorMap family category left right₁ +
        QtrTensorMap family category left right₂ := by
  change
    QtrMap (category := category)
        (SmCorQ.tensorHom family category left (right₁ + right₂)) =
      QtrMap (category := category) (SmCorQ.tensorHom family category left right₁) +
        QtrMap (category := category) (SmCorQ.tensorHom family category left right₂)
  rw [SmCorQ.tensorHom_add_right]
  exact QtrMap_add (category := category)
    (SmCorQ.tensorHom family category left right₁)
    (SmCorQ.tensorHom family category left right₂)

theorem QtrTensorMap_smul_left
    (family : FiniteCorrespondence.TensorCompatibleExternalProductFamily (k := k))
    (category : SmCorQ (k := k))
    {X₁ Y₁ X₂ Y₂ : Geometry.SmSchemeOver k}
    (coeff : ℚ)
    (left : SmCorQ.Hom category X₁ Y₁)
    (right : SmCorQ.Hom category X₂ Y₂) :
    QtrTensorMap family category (coeff • left) right =
      coeff • QtrTensorMap family category left right := by
  change
    QtrMap (category := category)
        (SmCorQ.tensorHom family category (coeff • left) right) =
      coeff • QtrMap (category := category) (SmCorQ.tensorHom family category left right)
  rw [SmCorQ.tensorHom_smul_left]
  exact QtrMap_smul (category := category) coeff
    (SmCorQ.tensorHom family category left right)

theorem QtrTensorMap_smul_right
    (family : FiniteCorrespondence.TensorCompatibleExternalProductFamily (k := k))
    (category : SmCorQ (k := k))
    {X₁ Y₁ X₂ Y₂ : Geometry.SmSchemeOver k}
    (coeff : ℚ)
    (left : SmCorQ.Hom category X₁ Y₁)
    (right : SmCorQ.Hom category X₂ Y₂) :
    QtrTensorMap family category left (coeff • right) =
      coeff • QtrTensorMap family category left right := by
  change
    QtrMap (category := category)
        (SmCorQ.tensorHom family category left (coeff • right)) =
      coeff • QtrMap (category := category) (SmCorQ.tensorHom family category left right)
  rw [SmCorQ.tensorHom_smul_right]
  exact QtrMap_smul (category := category) coeff
    (SmCorQ.tensorHom family category left right)

/-- Representable Day tensor maps compose by correspondence-level tensor
bifunctoriality. -/
theorem QtrTensorMap_comp
    (family : FiniteCorrespondence.TensorCompatibleExternalProductFamily (k := k))
    (category : SmCorQ (k := k))
    {W₁ X₁ Y₁ W₂ X₂ Y₂ : Geometry.SmSchemeOver k}
    (f : SmCorQ.Hom category W₁ X₁)
    (g : SmCorQ.Hom category X₁ Y₁)
    (f' : SmCorQ.Hom category W₂ X₂)
    (g' : SmCorQ.Hom category X₂ Y₂) :
    QtrTensorMap family category (category.comp f g) (category.comp f' g') =
      QtrTensorMap family category f f' ≫
        QtrTensorMap family category g g' := by
  change
    QtrMap (category := category)
        (SmCorQ.tensorHom family category (category.comp f g) (category.comp f' g')) =
      QtrMap (category := category) (SmCorQ.tensorHom family category f f') ≫
        QtrMap (category := category) (SmCorQ.tensorHom family category g g')
  rw [SmCorQ.tensorHom_comp]
  exact QtrMap_comp (category := category)
    (SmCorQ.tensorHom family category f f')
    (SmCorQ.tensorHom family category g g')

theorem QtrTensorMap_comp_left_id
    (family : FiniteCorrespondence.TensorCompatibleExternalProductFamily (k := k))
    (category : SmCorQ (k := k))
    {W X Y Z : Geometry.SmSchemeOver k}
    (f : SmCorQ.Hom category W X)
    (g : SmCorQ.Hom category X Y) :
    QtrTensorMap family category (category.comp f g) (category.id Z) =
      QtrTensorMap family category f (category.id Z) ≫
        QtrTensorMap family category g (category.id Z) := by
  calc
    QtrTensorMap family category (category.comp f g) (category.id Z) =
      QtrTensorMap family category
        (category.comp f g) (category.comp (category.id Z) (category.id Z)) := by
        rw [category.id_comp]
    _ = QtrTensorMap family category f (category.id Z) ≫
          QtrTensorMap family category g (category.id Z) := by
        exact QtrTensorMap_comp family category f g (category.id Z) (category.id Z)

theorem QtrTensorMap_comp_right_id
    (family : FiniteCorrespondence.TensorCompatibleExternalProductFamily (k := k))
    (category : SmCorQ (k := k))
    {W X Y Z : Geometry.SmSchemeOver k}
    (f : SmCorQ.Hom category X Y)
    (g : SmCorQ.Hom category Y Z) :
    QtrTensorMap family category (category.id W) (category.comp f g) =
      QtrTensorMap family category (category.id W) f ≫
        QtrTensorMap family category (category.id W) g := by
  calc
    QtrTensorMap family category (category.id W) (category.comp f g) =
      QtrTensorMap family category
        (category.comp (category.id W) (category.id W)) (category.comp f g) := by
        rw [category.id_comp]
    _ = QtrTensorMap family category (category.id W) f ≫
          QtrTensorMap family category (category.id W) g := by
        exact QtrTensorMap_comp family category
          (category.id W) (category.id W) f g

/-- Representable Day tensor identity law obtained from the corresponding
correspondence-level tensor identity theorem. -/
theorem QtrTensorMap_id_of_tensorHom_id
    (family : FiniteCorrespondence.TensorCompatibleExternalProductFamily (k := k))
    (category : SmCorQ (k := k))
    (X Y : Geometry.SmSchemeOver k)
    (hId :
      SmCorQ.tensorHom family category (category.id X) (category.id Y) =
        category.id (SmCorQ.tensorObj X Y)) :
    QtrTensorMap family category (category.id X) (category.id Y) =
      𝟙 (QtrTensor category X Y) := by
  change
    QtrMap (category := category)
        (SmCorQ.tensorHom family category (category.id X) (category.id Y)) =
      𝟙 (QtrLinear (category := category) (SmCorQ.tensorObj X Y))
  rw [hId]
  exact QtrMap_id (category := category) (SmCorQ.tensorObj X Y)

/-- Fixed-left representable tensor functor.  Its only identity-law input is
the correspondence-level theorem that tensoring the two identity
correspondences gives the identity on the product. -/
noncomputable def QtrTensorLeftFunctorOfTensorHomId
    (family : FiniteCorrespondence.TensorCompatibleExternalProductFamily (k := k))
    (category : SmCorQ (k := k))
    (X : Geometry.SmSchemeOver k)
    (hId :
      ∀ Y : Geometry.SmSchemeOver k,
        SmCorQ.tensorHom family category (category.id X) (category.id Y) =
          category.id (SmCorQ.tensorObj X Y)) :
    letI := SmCorQCat category
    Geometry.SmSchemeOver k ⥤ LinearPST category := by
  letI := SmCorQCat category
  exact
    { obj := fun Y => QtrTensor category X Y
      map := fun {Y Z} f =>
        QtrTensorMap family category (category.id X) f
      map_id := by
        intro Y
        exact QtrTensorMap_id_of_tensorHom_id family category X Y (hId Y)
      map_comp := by
        intro Y Z W f g
        exact QtrTensorMap_comp_right_id family category f g }

@[simp] theorem QtrTensorLeftFunctorOfTensorHomId_obj
    (family : FiniteCorrespondence.TensorCompatibleExternalProductFamily (k := k))
    (category : SmCorQ (k := k))
    (X Y : Geometry.SmSchemeOver k)
    (hId :
      ∀ Y : Geometry.SmSchemeOver k,
        SmCorQ.tensorHom family category (category.id X) (category.id Y) =
          category.id (SmCorQ.tensorObj X Y)) :
    letI := SmCorQCat category
    (QtrTensorLeftFunctorOfTensorHomId family category X hId).obj Y =
      QtrTensor category X Y := by
  rfl

@[simp] theorem QtrTensorLeftFunctorOfTensorHomId_map
    (family : FiniteCorrespondence.TensorCompatibleExternalProductFamily (k := k))
    (category : SmCorQ (k := k))
    (X : Geometry.SmSchemeOver k)
    {Y Z : Geometry.SmSchemeOver k}
    (f : SmCorQ.Hom category Y Z)
    (hId :
      ∀ Y : Geometry.SmSchemeOver k,
        SmCorQ.tensorHom family category (category.id X) (category.id Y) =
          category.id (SmCorQ.tensorObj X Y)) :
    letI := SmCorQCat category
    (QtrTensorLeftFunctorOfTensorHomId family category X hId).map f =
      QtrTensorMap family category (category.id X) f := by
  rfl

/-- Fixed-right representable tensor functor. -/
noncomputable def QtrTensorRightFunctorOfTensorHomId
    (family : FiniteCorrespondence.TensorCompatibleExternalProductFamily (k := k))
    (category : SmCorQ (k := k))
    (Y : Geometry.SmSchemeOver k)
    (hId :
      ∀ X : Geometry.SmSchemeOver k,
        SmCorQ.tensorHom family category (category.id X) (category.id Y) =
          category.id (SmCorQ.tensorObj X Y)) :
    letI := SmCorQCat category
    Geometry.SmSchemeOver k ⥤ LinearPST category := by
  letI := SmCorQCat category
  exact
    { obj := fun X => QtrTensor category X Y
      map := fun {X Z} f =>
        QtrTensorMap family category f (category.id Y)
      map_id := by
        intro X
        exact QtrTensorMap_id_of_tensorHom_id family category X Y (hId X)
      map_comp := by
        intro X Z W f g
        exact QtrTensorMap_comp_left_id family category f g }

@[simp] theorem QtrTensorRightFunctorOfTensorHomId_obj
    (family : FiniteCorrespondence.TensorCompatibleExternalProductFamily (k := k))
    (category : SmCorQ (k := k))
    (X Y : Geometry.SmSchemeOver k)
    (hId :
      ∀ X : Geometry.SmSchemeOver k,
        SmCorQ.tensorHom family category (category.id X) (category.id Y) =
          category.id (SmCorQ.tensorObj X Y)) :
    letI := SmCorQCat category
    (QtrTensorRightFunctorOfTensorHomId family category Y hId).obj X =
      QtrTensor category X Y := by
  rfl

@[simp] theorem QtrTensorRightFunctorOfTensorHomId_map
    (family : FiniteCorrespondence.TensorCompatibleExternalProductFamily (k := k))
    (category : SmCorQ (k := k))
    (Y : Geometry.SmSchemeOver k)
    {X Z : Geometry.SmSchemeOver k}
    (f : SmCorQ.Hom category X Z)
    (hId :
      ∀ X : Geometry.SmSchemeOver k,
        SmCorQ.tensorHom family category (category.id X) (category.id Y) =
          category.id (SmCorQ.tensorObj X Y)) :
    letI := SmCorQCat category
    (QtrTensorRightFunctorOfTensorHomId family category Y hId).map f =
      QtrTensorMap family category f (category.id Y) := by
  rfl

/-- Representable tensor bifunctor on pairs of smooth schemes.  The map on
morphisms is induced by `SmCorQ.tensorHom`; functoriality is exactly
`QtrTensorMap_comp`, and identities are exactly the correspondence-level
tensor identity theorem. -/
noncomputable def QtrTensorBifunctorOfTensorHomId
    (family : FiniteCorrespondence.TensorCompatibleExternalProductFamily (k := k))
    (category : SmCorQ (k := k))
    (hId :
      ∀ X Y : Geometry.SmSchemeOver k,
        SmCorQ.tensorHom family category (category.id X) (category.id Y) =
          category.id (SmCorQ.tensorObj X Y)) :
    letI := SmCorQCat category
    (Geometry.SmSchemeOver k × Geometry.SmSchemeOver k) ⥤ LinearPST category := by
  letI := SmCorQCat category
  exact
    { obj := fun pair => QtrTensor category pair.1 pair.2
      map := fun {pair₁ pair₂} f =>
        QtrTensorMap family category f.1 f.2
      map_id := by
        intro pair
        exact QtrTensorMap_id_of_tensorHom_id
          family category pair.1 pair.2 (hId pair.1 pair.2)
      map_comp := by
        intro pair₁ pair₂ pair₃ f g
        exact QtrTensorMap_comp family category f.1 g.1 f.2 g.2 }

@[simp] theorem QtrTensorBifunctorOfTensorHomId_obj
    (family : FiniteCorrespondence.TensorCompatibleExternalProductFamily (k := k))
    (category : SmCorQ (k := k))
    (X Y : Geometry.SmSchemeOver k)
    (hId :
      ∀ X Y : Geometry.SmSchemeOver k,
        SmCorQ.tensorHom family category (category.id X) (category.id Y) =
          category.id (SmCorQ.tensorObj X Y)) :
    letI := SmCorQCat category
    (QtrTensorBifunctorOfTensorHomId family category hId).obj (X, Y) =
      QtrTensor category X Y := by
  rfl

@[simp] theorem QtrTensorBifunctorOfTensorHomId_map
    (family : FiniteCorrespondence.TensorCompatibleExternalProductFamily (k := k))
    (category : SmCorQ (k := k))
    {X₁ Y₁ X₂ Y₂ : Geometry.SmSchemeOver k}
    (left : SmCorQ.Hom category X₁ Y₁)
    (right : SmCorQ.Hom category X₂ Y₂)
    (hId :
      ∀ X Y : Geometry.SmSchemeOver k,
        SmCorQ.tensorHom family category (category.id X) (category.id Y) =
          category.id (SmCorQ.tensorObj X Y)) :
    letI := SmCorQCat category
    (QtrTensorBifunctorOfTensorHomId family category hId).map (left, right) =
      QtrTensorMap family category left right := by
  rfl

/-- Fixed-left representable tensor functor using the public `SmCorQ`
tensor-identity reduction theorem. The only identity input is the
correspondence-level equality identifying the external product of the two
identity finite correspondences with the canonical identity correspondence on
the product. -/
noncomputable def QtrTensorLeftFunctorOfExternalProductIdentity
    (family : FiniteCorrespondence.TensorCompatibleExternalProductFamily (k := k))
    (category : SmCorQ (k := k))
    (X : Geometry.SmSchemeOver k)
    (hIdentity :
      ∀ Y : Geometry.SmSchemeOver k,
        FiniteCorrespondence.externalProductWithFamily family.family
            (category.integral.composition.diagonalDecomposition X).identityFiniteCorrespondence
            (category.integral.composition.diagonalDecomposition Y).identityFiniteCorrespondence =
          (category.integral.composition.diagonalDecomposition
            (SmCorQ.tensorObj X Y)).identityFiniteCorrespondence) :
    letI := SmCorQCat category
    Geometry.SmSchemeOver k ⥤ LinearPST category :=
  QtrTensorLeftFunctorOfTensorHomId family category X
    (fun Y =>
      SmCorQ.tensorHom_id_of_externalProductIdentity family category X Y (hIdentity Y))

/-- Fixed-left representable tensor functor using the locally irreducible
product-model route to the tensor identity theorem. -/
noncomputable def QtrTensorLeftFunctorOfLocallyIrreducible
    (family : FiniteCorrespondence.TensorCompatibleExternalProductFamily (k := k))
    (category : SmCorQ (k := k))
    (X : Geometry.SmSchemeOver k)
    (hLoc :
      ∀ (Y : Geometry.SmSchemeOver k)
        (sourceX :
          { sourceX : SourceIrreducibleComponent X //
            sourceX ∈ (category.integral.composition.diagonalDecomposition X).components })
        (sourceY :
          { sourceY : SourceIrreducibleComponent Y //
            sourceY ∈ (category.integral.composition.diagonalDecomposition Y).components }),
        Geometry.Topology.LocallyIrreducibleSpace
          (product_diagonal_smoothObject (k := k) sourceX.1 sourceY.1).scheme)
    (hIntegral :
      ∀ (Y : Geometry.SmSchemeOver k)
        (sourceX :
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
                  C.2 (hLoc Y sourceX sourceY)⟩ :
                (product_diagonal_smoothObject (k := k) sourceX.1 sourceY.1).scheme.Opens))) :
    letI := SmCorQCat category
    Geometry.SmSchemeOver k ⥤ LinearPST category :=
  QtrTensorLeftFunctorOfTensorHomId family category X
    (fun Y =>
      SmCorQ.tensorHom_id_of_locallyIrreducible family category X Y
        (hLoc Y) (hIntegral Y))

/-- Fixed-left representable tensor functor using the reduced locally
irreducible product-model route to the tensor identity theorem. -/
noncomputable def QtrTensorLeftFunctorOfReducedLocallyIrreducible
    (family : FiniteCorrespondence.TensorCompatibleExternalProductFamily (k := k))
    (category : SmCorQ (k := k))
    (X : Geometry.SmSchemeOver k)
    (hLoc :
      ∀ (Y : Geometry.SmSchemeOver k)
        (sourceX :
          { sourceX : SourceIrreducibleComponent X //
            sourceX ∈ (category.integral.composition.diagonalDecomposition X).components })
        (sourceY :
          { sourceY : SourceIrreducibleComponent Y //
            sourceY ∈ (category.integral.composition.diagonalDecomposition Y).components }),
        Geometry.Topology.LocallyIrreducibleSpace
          (product_diagonal_smoothObject (k := k) sourceX.1 sourceY.1).scheme)
    (hReduced :
      ∀ (Y : Geometry.SmSchemeOver k)
        (sourceX :
          { sourceX : SourceIrreducibleComponent X //
            sourceX ∈ (category.integral.composition.diagonalDecomposition X).components })
        (sourceY :
          { sourceY : SourceIrreducibleComponent Y //
            sourceY ∈ (category.integral.composition.diagonalDecomposition Y).components }),
        IsReduced
          (product_diagonal_smoothObject (k := k) sourceX.1 sourceY.1).scheme) :
    letI := SmCorQCat category
    Geometry.SmSchemeOver k ⥤ LinearPST category :=
  QtrTensorLeftFunctorOfTensorHomId family category X
    (fun Y =>
      SmCorQ.tensorHom_id_of_reducedLocallyIrreducible family category X Y
        (hLoc Y) (hReduced Y))

/-- Fixed-left representable tensor functor using the alternative bottom
geometry route `IsReduced + irreducible components open`. -/
noncomputable def QtrTensorLeftFunctorOfReducedComponentsOpen
    (family : FiniteCorrespondence.TensorCompatibleExternalProductFamily (k := k))
    (category : SmCorQ (k := k))
    (X : Geometry.SmSchemeOver k)
    (hOpen :
      ∀ (Y : Geometry.SmSchemeOver k)
        (sourceX :
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
      ∀ (Y : Geometry.SmSchemeOver k)
        (sourceX :
          { sourceX : SourceIrreducibleComponent X //
            sourceX ∈ (category.integral.composition.diagonalDecomposition X).components })
        (sourceY :
          { sourceY : SourceIrreducibleComponent Y //
            sourceY ∈ (category.integral.composition.diagonalDecomposition Y).components }),
        IsReduced
          (product_diagonal_smoothObject (k := k) sourceX.1 sourceY.1).scheme) :
    letI := SmCorQCat category
    Geometry.SmSchemeOver k ⥤ LinearPST category :=
  QtrTensorLeftFunctorOfTensorHomId family category X
    (fun Y =>
      SmCorQ.tensorHom_id_of_reducedComponentsOpen family category X Y
        (hOpen Y) (hReduced Y))

/-- Fixed-left representable tensor functor using the route
`components open + relative-dimension-zero standard-smooth affine charts`. -/
noncomputable def QtrTensorLeftFunctorOfStandardSmoothOfRelativeDimensionZeroComponentsOpen
    (family : FiniteCorrespondence.TensorCompatibleExternalProductFamily (k := k))
    (category : SmCorQ (k := k))
    (X : Geometry.SmSchemeOver k)
    (hOpen :
      ∀ (Y : Geometry.SmSchemeOver k)
        (sourceX :
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
      ∀ (Y : Geometry.SmSchemeOver k)
        (sourceX :
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
    letI := SmCorQCat category
    Geometry.SmSchemeOver k ⥤ LinearPST category :=
  QtrTensorLeftFunctorOfTensorHomId family category X
    (fun Y =>
      SmCorQ.tensorHom_id_of_standardSmoothOfRelativeDimensionZeroComponentsOpen
        family category X Y (hOpen Y) (hStd0 Y))

/-- Fixed-left representable tensor functor using the route
`reduced locally irreducible + relative-dimension-zero standard-smooth affine charts`. -/
noncomputable def QtrTensorLeftFunctorOfStandardSmoothOfRelativeDimensionZeroReducedLocallyIrreducible
    (family : FiniteCorrespondence.TensorCompatibleExternalProductFamily (k := k))
    (category : SmCorQ (k := k))
    (X : Geometry.SmSchemeOver k)
    (hStd0 :
      ∀ (Y : Geometry.SmSchemeOver k)
        (sourceX :
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
    letI := SmCorQCat category
    Geometry.SmSchemeOver k ⥤ LinearPST category :=
  QtrTensorLeftFunctorOfTensorHomId family category X
    (fun Y =>
      SmCorQ.tensorHom_id_of_standardSmoothOfRelativeDimensionZeroReducedLocallyIrreducible
        family category X Y (hStd0 Y))

/-- Fixed-left representable tensor functor using the direct route
`relative-dimension-zero standard-smooth affine charts` on each product model. -/
noncomputable def QtrTensorLeftFunctorOfStandardSmoothOfRelativeDimensionZeroAffine
    (family : FiniteCorrespondence.TensorCompatibleExternalProductFamily (k := k))
    (category : SmCorQ (k := k))
    (X : Geometry.SmSchemeOver k)
    (hStd0 :
      ∀ (Y : Geometry.SmSchemeOver k)
        (sourceX :
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
    letI := SmCorQCat category
    Geometry.SmSchemeOver k ⥤ LinearPST category :=
  QtrTensorLeftFunctorOfTensorHomId family category X
    (fun Y =>
      SmCorQ.tensorHom_id_of_standardSmoothOfRelativeDimensionZeroAffine
        family category X Y (hStd0 Y))

/-- Fixed-left representable tensor functor using the temporary
product-stable geometric route to the correspondence-level identity theorem. -/
noncomputable def QtrTensorLeftFunctor
    (family : FiniteCorrespondence.TensorCompatibleExternalProductFamily (k := k))
    (category : SmCorQ (k := k))
    (X : Geometry.SmSchemeOver k)
    (stableDX :
      (listed :
        { listed : SourceIrreducibleComponent X //
          listed ∈ (category.integral.composition.diagonalDecomposition X).components }) →
        ProductStableSourceComponent X)
    (hstableDX : ∀ listed, (stableDX listed).component = listed.1) :
    letI := SmCorQCat category
    Geometry.SmSchemeOver k ⥤ LinearPST category :=
  QtrTensorLeftFunctorOfExternalProductIdentity family category X
    (fun Y =>
      SmCorQ.externalProductIdentity_of_productStableDiagonal
        family category X Y stableDX hstableDX)

/-- Fixed-right representable tensor functor using the public `SmCorQ`
tensor-identity reduction theorem. This requires the correspondence-level
identity equality uniformly in the varying left object. -/
noncomputable def QtrTensorRightFunctorOfExternalProductIdentity
    (family : FiniteCorrespondence.TensorCompatibleExternalProductFamily (k := k))
    (category : SmCorQ (k := k))
    (Y : Geometry.SmSchemeOver k)
    (hIdentity :
      ∀ X : Geometry.SmSchemeOver k,
        FiniteCorrespondence.externalProductWithFamily family.family
            (category.integral.composition.diagonalDecomposition X).identityFiniteCorrespondence
            (category.integral.composition.diagonalDecomposition Y).identityFiniteCorrespondence =
          (category.integral.composition.diagonalDecomposition
            (SmCorQ.tensorObj X Y)).identityFiniteCorrespondence) :
    letI := SmCorQCat category
    Geometry.SmSchemeOver k ⥤ LinearPST category :=
  QtrTensorRightFunctorOfTensorHomId family category Y
    (fun X =>
      SmCorQ.tensorHom_id_of_externalProductIdentity family category X Y (hIdentity X))

/-- Fixed-right representable tensor functor using the locally irreducible
product-model route to the tensor identity theorem. -/
noncomputable def QtrTensorRightFunctorOfLocallyIrreducible
    (family : FiniteCorrespondence.TensorCompatibleExternalProductFamily (k := k))
    (category : SmCorQ (k := k))
    (Y : Geometry.SmSchemeOver k)
    (hLoc :
      ∀ (X : Geometry.SmSchemeOver k)
        (sourceX :
          { sourceX : SourceIrreducibleComponent X //
            sourceX ∈ (category.integral.composition.diagonalDecomposition X).components })
        (sourceY :
          { sourceY : SourceIrreducibleComponent Y //
            sourceY ∈ (category.integral.composition.diagonalDecomposition Y).components }),
        Geometry.Topology.LocallyIrreducibleSpace
          (product_diagonal_smoothObject (k := k) sourceX.1 sourceY.1).scheme)
    (hIntegral :
      ∀ (X : Geometry.SmSchemeOver k)
        (sourceX :
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
                  C.2 (hLoc X sourceX sourceY)⟩ :
                (product_diagonal_smoothObject (k := k) sourceX.1 sourceY.1).scheme.Opens))) :
    letI := SmCorQCat category
    Geometry.SmSchemeOver k ⥤ LinearPST category :=
  QtrTensorRightFunctorOfTensorHomId family category Y
    (fun X =>
      SmCorQ.tensorHom_id_of_locallyIrreducible family category X Y
        (hLoc X) (hIntegral X))

/-- Fixed-right representable tensor functor using the reduced locally
irreducible product-model route to the tensor identity theorem. -/
noncomputable def QtrTensorRightFunctorOfReducedLocallyIrreducible
    (family : FiniteCorrespondence.TensorCompatibleExternalProductFamily (k := k))
    (category : SmCorQ (k := k))
    (Y : Geometry.SmSchemeOver k)
    (hLoc :
      ∀ (X : Geometry.SmSchemeOver k)
        (sourceX :
          { sourceX : SourceIrreducibleComponent X //
            sourceX ∈ (category.integral.composition.diagonalDecomposition X).components })
        (sourceY :
          { sourceY : SourceIrreducibleComponent Y //
            sourceY ∈ (category.integral.composition.diagonalDecomposition Y).components }),
        Geometry.Topology.LocallyIrreducibleSpace
          (product_diagonal_smoothObject (k := k) sourceX.1 sourceY.1).scheme)
    (hReduced :
      ∀ (X : Geometry.SmSchemeOver k)
        (sourceX :
          { sourceX : SourceIrreducibleComponent X //
            sourceX ∈ (category.integral.composition.diagonalDecomposition X).components })
        (sourceY :
          { sourceY : SourceIrreducibleComponent Y //
            sourceY ∈ (category.integral.composition.diagonalDecomposition Y).components }),
        IsReduced
          (product_diagonal_smoothObject (k := k) sourceX.1 sourceY.1).scheme) :
    letI := SmCorQCat category
    Geometry.SmSchemeOver k ⥤ LinearPST category :=
  QtrTensorRightFunctorOfTensorHomId family category Y
    (fun X =>
      SmCorQ.tensorHom_id_of_reducedLocallyIrreducible family category X Y
        (hLoc X) (hReduced X))

/-- Fixed-right representable tensor functor using the alternative bottom
geometry route `IsReduced + irreducible components open`. -/
noncomputable def QtrTensorRightFunctorOfReducedComponentsOpen
    (family : FiniteCorrespondence.TensorCompatibleExternalProductFamily (k := k))
    (category : SmCorQ (k := k))
    (Y : Geometry.SmSchemeOver k)
    (hOpen :
      ∀ (X : Geometry.SmSchemeOver k)
        (sourceX :
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
      ∀ (X : Geometry.SmSchemeOver k)
        (sourceX :
          { sourceX : SourceIrreducibleComponent X //
            sourceX ∈ (category.integral.composition.diagonalDecomposition X).components })
        (sourceY :
          { sourceY : SourceIrreducibleComponent Y //
            sourceY ∈ (category.integral.composition.diagonalDecomposition Y).components }),
        IsReduced
          (product_diagonal_smoothObject (k := k) sourceX.1 sourceY.1).scheme) :
    letI := SmCorQCat category
    Geometry.SmSchemeOver k ⥤ LinearPST category :=
  QtrTensorRightFunctorOfTensorHomId family category Y
    (fun X =>
      SmCorQ.tensorHom_id_of_reducedComponentsOpen family category X Y
        (hOpen X) (hReduced X))

/-- Fixed-right representable tensor functor using the route
`components open + relative-dimension-zero standard-smooth affine charts`. -/
noncomputable def QtrTensorRightFunctorOfStandardSmoothOfRelativeDimensionZeroComponentsOpen
    (family : FiniteCorrespondence.TensorCompatibleExternalProductFamily (k := k))
    (category : SmCorQ (k := k))
    (Y : Geometry.SmSchemeOver k)
    (hOpen :
      ∀ (X : Geometry.SmSchemeOver k)
        (sourceX :
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
      ∀ (X : Geometry.SmSchemeOver k)
        (sourceX :
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
    letI := SmCorQCat category
    Geometry.SmSchemeOver k ⥤ LinearPST category :=
  QtrTensorRightFunctorOfTensorHomId family category Y
    (fun X =>
      SmCorQ.tensorHom_id_of_standardSmoothOfRelativeDimensionZeroComponentsOpen
        family category X Y (hOpen X) (hStd0 X))

/-- Fixed-right representable tensor functor using the route
`reduced locally irreducible + relative-dimension-zero standard-smooth affine charts`. -/
noncomputable def QtrTensorRightFunctorOfStandardSmoothOfRelativeDimensionZeroReducedLocallyIrreducible
    (family : FiniteCorrespondence.TensorCompatibleExternalProductFamily (k := k))
    (category : SmCorQ (k := k))
    (Y : Geometry.SmSchemeOver k)
    (hStd0 :
      ∀ (X : Geometry.SmSchemeOver k)
        (sourceX :
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
    letI := SmCorQCat category
    Geometry.SmSchemeOver k ⥤ LinearPST category :=
  QtrTensorRightFunctorOfTensorHomId family category Y
    (fun X =>
      SmCorQ.tensorHom_id_of_standardSmoothOfRelativeDimensionZeroReducedLocallyIrreducible
        family category X Y (hStd0 X))

/-- Fixed-right representable tensor functor using the direct route
`relative-dimension-zero standard-smooth affine charts` on each product model. -/
noncomputable def QtrTensorRightFunctorOfStandardSmoothOfRelativeDimensionZeroAffine
    (family : FiniteCorrespondence.TensorCompatibleExternalProductFamily (k := k))
    (category : SmCorQ (k := k))
    (Y : Geometry.SmSchemeOver k)
    (hStd0 :
      ∀ (X : Geometry.SmSchemeOver k)
        (sourceX :
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
    letI := SmCorQCat category
    Geometry.SmSchemeOver k ⥤ LinearPST category :=
  QtrTensorRightFunctorOfTensorHomId family category Y
    (fun X =>
      SmCorQ.tensorHom_id_of_standardSmoothOfRelativeDimensionZeroAffine
        family category X Y (hStd0 X))

/-- Fixed-right representable tensor functor using the temporary
product-stable geometric route. -/
noncomputable def QtrTensorRightFunctor
    (family : FiniteCorrespondence.TensorCompatibleExternalProductFamily (k := k))
    (category : SmCorQ (k := k))
    (Y : Geometry.SmSchemeOver k)
    (stable :
      ∀ X : Geometry.SmSchemeOver k,
        (listed :
          { listed : SourceIrreducibleComponent X //
            listed ∈ (category.integral.composition.diagonalDecomposition X).components }) →
          ProductStableSourceComponent X)
    (hstable :
      ∀ (X : Geometry.SmSchemeOver k) listed,
        (stable X listed).component = listed.1) :
    letI := SmCorQCat category
    Geometry.SmSchemeOver k ⥤ LinearPST category :=
  QtrTensorRightFunctorOfExternalProductIdentity family category Y
    (fun X =>
      SmCorQ.externalProductIdentity_of_productStableDiagonal
        family category X Y (stable X) (hstable X))

/-- Representable tensor bifunctor using the public `SmCorQ` tensor-identity
reduction theorem. -/
noncomputable def QtrTensorBifunctorOfExternalProductIdentity
    (family : FiniteCorrespondence.TensorCompatibleExternalProductFamily (k := k))
    (category : SmCorQ (k := k))
    (hIdentity :
      ∀ X Y : Geometry.SmSchemeOver k,
        FiniteCorrespondence.externalProductWithFamily family.family
            (category.integral.composition.diagonalDecomposition X).identityFiniteCorrespondence
            (category.integral.composition.diagonalDecomposition Y).identityFiniteCorrespondence =
          (category.integral.composition.diagonalDecomposition
            (SmCorQ.tensorObj X Y)).identityFiniteCorrespondence) :
    letI := SmCorQCat category
    (Geometry.SmSchemeOver k × Geometry.SmSchemeOver k) ⥤ LinearPST category :=
  QtrTensorBifunctorOfTensorHomId family category
    (fun X Y =>
      SmCorQ.tensorHom_id_of_externalProductIdentity family category X Y
        (hIdentity X Y))

/-- Representable tensor bifunctor using the locally irreducible product-model
route to the tensor identity theorem. -/
noncomputable def QtrTensorBifunctorOfLocallyIrreducible
    (family : FiniteCorrespondence.TensorCompatibleExternalProductFamily (k := k))
    (category : SmCorQ (k := k))
    (hLoc :
      ∀ (X Y : Geometry.SmSchemeOver k)
        (sourceX :
          { sourceX : SourceIrreducibleComponent X //
            sourceX ∈ (category.integral.composition.diagonalDecomposition X).components })
        (sourceY :
          { sourceY : SourceIrreducibleComponent Y //
            sourceY ∈ (category.integral.composition.diagonalDecomposition Y).components }),
        Geometry.Topology.LocallyIrreducibleSpace
          (product_diagonal_smoothObject (k := k) sourceX.1 sourceY.1).scheme)
    (hIntegral :
      ∀ (X Y : Geometry.SmSchemeOver k)
        (sourceX :
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
                  C.2 (hLoc X Y sourceX sourceY)⟩ :
                (product_diagonal_smoothObject (k := k) sourceX.1 sourceY.1).scheme.Opens))) :
    letI := SmCorQCat category
    (Geometry.SmSchemeOver k × Geometry.SmSchemeOver k) ⥤ LinearPST category :=
  QtrTensorBifunctorOfTensorHomId family category
    (fun X Y =>
      SmCorQ.tensorHom_id_of_locallyIrreducible family category X Y
        (hLoc X Y) (hIntegral X Y))

/-- Representable tensor bifunctor using the reduced locally irreducible
product-model route to the tensor identity theorem. -/
noncomputable def QtrTensorBifunctorOfReducedLocallyIrreducible
    (family : FiniteCorrespondence.TensorCompatibleExternalProductFamily (k := k))
    (category : SmCorQ (k := k))
    (hLoc :
      ∀ (X Y : Geometry.SmSchemeOver k)
        (sourceX :
          { sourceX : SourceIrreducibleComponent X //
            sourceX ∈ (category.integral.composition.diagonalDecomposition X).components })
        (sourceY :
          { sourceY : SourceIrreducibleComponent Y //
            sourceY ∈ (category.integral.composition.diagonalDecomposition Y).components }),
        Geometry.Topology.LocallyIrreducibleSpace
          (product_diagonal_smoothObject (k := k) sourceX.1 sourceY.1).scheme)
    (hReduced :
      ∀ (X Y : Geometry.SmSchemeOver k)
        (sourceX :
          { sourceX : SourceIrreducibleComponent X //
            sourceX ∈ (category.integral.composition.diagonalDecomposition X).components })
        (sourceY :
          { sourceY : SourceIrreducibleComponent Y //
            sourceY ∈ (category.integral.composition.diagonalDecomposition Y).components }),
        IsReduced
          (product_diagonal_smoothObject (k := k) sourceX.1 sourceY.1).scheme) :
    letI := SmCorQCat category
    (Geometry.SmSchemeOver k × Geometry.SmSchemeOver k) ⥤ LinearPST category :=
  QtrTensorBifunctorOfTensorHomId family category
    (fun X Y =>
      SmCorQ.tensorHom_id_of_reducedLocallyIrreducible family category X Y
        (hLoc X Y) (hReduced X Y))

/-- Representable tensor bifunctor using the alternative bottom geometry route
`IsReduced + irreducible components open`. -/
noncomputable def QtrTensorBifunctorOfReducedComponentsOpen
    (family : FiniteCorrespondence.TensorCompatibleExternalProductFamily (k := k))
    (category : SmCorQ (k := k))
    (hOpen :
      ∀ (X Y : Geometry.SmSchemeOver k)
        (sourceX :
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
      ∀ (X Y : Geometry.SmSchemeOver k)
        (sourceX :
          { sourceX : SourceIrreducibleComponent X //
            sourceX ∈ (category.integral.composition.diagonalDecomposition X).components })
        (sourceY :
          { sourceY : SourceIrreducibleComponent Y //
            sourceY ∈ (category.integral.composition.diagonalDecomposition Y).components }),
        IsReduced
          (product_diagonal_smoothObject (k := k) sourceX.1 sourceY.1).scheme) :
    letI := SmCorQCat category
    (Geometry.SmSchemeOver k × Geometry.SmSchemeOver k) ⥤ LinearPST category :=
  QtrTensorBifunctorOfTensorHomId family category
    (fun X Y =>
      SmCorQ.tensorHom_id_of_reducedComponentsOpen family category X Y
        (hOpen X Y) (hReduced X Y))

/-- Representable tensor bifunctor using the route
`components open + relative-dimension-zero standard-smooth affine charts`. -/
noncomputable def QtrTensorBifunctorOfStandardSmoothOfRelativeDimensionZeroComponentsOpen
    (family : FiniteCorrespondence.TensorCompatibleExternalProductFamily (k := k))
    (category : SmCorQ (k := k))
    (hOpen :
      ∀ (X Y : Geometry.SmSchemeOver k)
        (sourceX :
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
      ∀ (X Y : Geometry.SmSchemeOver k)
        (sourceX :
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
    letI := SmCorQCat category
    (Geometry.SmSchemeOver k × Geometry.SmSchemeOver k) ⥤ LinearPST category :=
  QtrTensorBifunctorOfTensorHomId family category
    (fun X Y =>
      SmCorQ.tensorHom_id_of_standardSmoothOfRelativeDimensionZeroComponentsOpen
        family category X Y (hOpen X Y) (hStd0 X Y))

/-- Representable tensor bifunctor using the route
`reduced locally irreducible + relative-dimension-zero standard-smooth affine charts`. -/
noncomputable def QtrTensorBifunctorOfStandardSmoothOfRelativeDimensionZeroReducedLocallyIrreducible
    (family : FiniteCorrespondence.TensorCompatibleExternalProductFamily (k := k))
    (category : SmCorQ (k := k))
    (hStd0 :
      ∀ (X Y : Geometry.SmSchemeOver k)
        (sourceX :
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
    letI := SmCorQCat category
    (Geometry.SmSchemeOver k × Geometry.SmSchemeOver k) ⥤ LinearPST category :=
  QtrTensorBifunctorOfTensorHomId family category
    (fun X Y =>
      SmCorQ.tensorHom_id_of_standardSmoothOfRelativeDimensionZeroReducedLocallyIrreducible
        family category X Y (hStd0 X Y))

/-- Representable tensor bifunctor using the direct route
`relative-dimension-zero standard-smooth affine charts` on each product model. -/
noncomputable def QtrTensorBifunctorOfStandardSmoothOfRelativeDimensionZeroAffine
    (family : FiniteCorrespondence.TensorCompatibleExternalProductFamily (k := k))
    (category : SmCorQ (k := k))
    (hStd0 :
      ∀ (X Y : Geometry.SmSchemeOver k)
        (sourceX :
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
    letI := SmCorQCat category
    (Geometry.SmSchemeOver k × Geometry.SmSchemeOver k) ⥤ LinearPST category :=
  QtrTensorBifunctorOfTensorHomId family category
    (fun X Y =>
      SmCorQ.tensorHom_id_of_standardSmoothOfRelativeDimensionZeroAffine
        family category X Y (hStd0 X Y))

/-- Representable tensor bifunctor using the temporary product-stable
geometric route. -/
noncomputable def QtrTensorBifunctor
    (family : FiniteCorrespondence.TensorCompatibleExternalProductFamily (k := k))
    (category : SmCorQ (k := k))
    (stable :
      ∀ X : Geometry.SmSchemeOver k,
        (listed :
          { listed : SourceIrreducibleComponent X //
            listed ∈ (category.integral.composition.diagonalDecomposition X).components }) →
          ProductStableSourceComponent X)
    (hstable :
      ∀ (X : Geometry.SmSchemeOver k) listed,
        (stable X listed).component = listed.1) :
    letI := SmCorQCat category
    (Geometry.SmSchemeOver k × Geometry.SmSchemeOver k) ⥤ LinearPST category :=
  QtrTensorBifunctorOfExternalProductIdentity family category
    (fun X Y =>
      SmCorQ.externalProductIdentity_of_productStableDiagonal
        family category X Y (stable X) (hstable X))

end LinearPSTDayConvolution

end

end Boundary
