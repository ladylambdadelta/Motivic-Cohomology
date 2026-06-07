import Boundary.EffectiveMotives
import Boundary.LinearPSTDayConvolution
import Boundary.NisnevichPullbackTransfer

/-!
# Canonical effective motive of a smooth scheme

This file packages the canonical effective motive construction

`X ↦ Q(h_X[0])`

as an honest functor

`Sm/k ⥤ DM_eff`

over the already-validated effective-motives quotient. The only geometric
input is the canonical graph-transfer composition theorem proved from the
existing diagonal/composition package in `NisnevichPullbackTransfer.lean`.
-/

universe u

open CategoryTheory

namespace Boundary

noncomputable section

variable {k : Type u} [Field k] [PerfectField k]

/-- The canonical representable linear presheaf with transfers attached to a
smooth `k`-scheme. -/
abbrev canonicalRepresentableLinearPST
    (composition : Boundary.CanonicalCompositionData (k := k))
    (X : Geometry.SmSchemeOver k) :
    LinearPST (Boundary.canonicalCategory composition) :=
  QtrLinear (category := Boundary.canonicalCategory composition) X

/-- The degree-zero derived object attached to the canonical representable
linear presheaf with transfers. -/
def canonicalRepresentableComplex
    (composition : Boundary.CanonicalCompositionData (k := k))
    [Abelian (LinearPST (Boundary.canonicalCategory composition))]
    [HasDerivedCategory (LinearPST (Boundary.canonicalCategory composition))]
    (X : Geometry.SmSchemeOver k) :
    canonicalEffectiveAmbientDerivedCategory composition :=
  ((DerivedCategory.singleFunctor
      (LinearPST (Boundary.canonicalCategory composition)) 0).obj
    (canonicalRepresentableLinearPST composition X))

/-- Morphism between canonical representable linear presheaves with transfers,
induced by the graph correspondence of an ordinary smooth morphism. -/
def canonicalRepresentableLinearPSTMap
    (composition : Boundary.CanonicalCompositionData (k := k))
    {X Y : Geometry.SmSchemeOver k}
    (f : Boundary.SmOverHom X Y) :
    canonicalRepresentableLinearPST composition X ⟶
      canonicalRepresentableLinearPST composition Y :=
  QtrMap (category := Boundary.canonicalCategory composition)
    (SmCorQ.graphTransfer
      (Boundary.canonicalCategory composition)
      f
      (composition.diagonalDecomposition X))

/-- The graph-transfer map attached to the identity morphism is the identity on
canonical representable presheaves with transfers. -/
theorem canonicalRepresentableLinearPSTMap_id
    (composition : Boundary.CanonicalCompositionData (k := k))
    (X : Geometry.SmSchemeOver k) :
    canonicalRepresentableLinearPSTMap composition (Boundary.SmOverHom.id X) =
      𝟙 (canonicalRepresentableLinearPST composition X) := by
  letI := SmCorQCat (Boundary.canonicalCategory composition)
  change
    (QtrMap (category := Boundary.canonicalCategory composition)
      (SmCorQ.graphTransfer
        (Boundary.canonicalCategory composition)
        (Boundary.SmOverHom.id X)
        (composition.diagonalDecomposition X)) :
      Qtr (category := Boundary.canonicalCategory composition) X ⟶
        Qtr (category := Boundary.canonicalCategory composition) X) =
      𝟙 (Qtr (category := Boundary.canonicalCategory composition) X)
  ext Z corr
  change (Boundary.canonicalCategory composition).comp corr
      (SmCorQ.graphTransfer
        (Boundary.canonicalCategory composition)
        (Boundary.SmOverHom.id X)
        (composition.diagonalDecomposition X)) = corr
  have hId :
      SmCorQ.graphTransfer
          (Boundary.canonicalCategory composition)
          (Boundary.SmOverHom.id X)
          (composition.diagonalDecomposition X) =
        (Boundary.canonicalCategory composition).id X := by
    exact
            (canonicalCategory_graphTransfer_id
        (composition := composition) (X := X))
  rw [hId]
  exact (Boundary.canonicalCategory composition).comp_id corr

/-- The degree-zero derived morphism induced by the canonical representable
map attached to an ordinary smooth morphism. -/
def canonicalRepresentableComplexMap
    (composition : Boundary.CanonicalCompositionData (k := k))
    [Abelian (LinearPST (Boundary.canonicalCategory composition))]
    [HasDerivedCategory (LinearPST (Boundary.canonicalCategory composition))]
    {X Y : Geometry.SmSchemeOver k}
    (f : Boundary.SmOverHom X Y) :
    canonicalRepresentableComplex composition X ⟶
      canonicalRepresentableComplex composition Y :=
  (DerivedCategory.singleFunctor
      (LinearPST (Boundary.canonicalCategory composition)) 0).map
    (canonicalRepresentableLinearPSTMap composition f)

/-- The degree-zero derived map attached to the identity morphism is the
identity on the canonical representable complex. -/
theorem canonicalRepresentableComplexMap_id
    (composition : Boundary.CanonicalCompositionData (k := k))
    [Abelian (LinearPST (Boundary.canonicalCategory composition))]
    [HasDerivedCategory (LinearPST (Boundary.canonicalCategory composition))]
    (X : Geometry.SmSchemeOver k) :
    canonicalRepresentableComplexMap composition (Boundary.SmOverHom.id X) =
      𝟙 (canonicalRepresentableComplex composition X) := by
  simp [canonicalRepresentableComplexMap, canonicalRepresentableComplex,
    canonicalRepresentableLinearPSTMap_id]

/-- Any graph-transfer composition identity in `SmCorQ` immediately upgrades to
the corresponding representable presheaf composition identity. -/
theorem canonicalRepresentableLinearPSTMap_comp_of_graphTransfer_comp
    (composition : Boundary.CanonicalCompositionData (k := k))
    {X Y Z : Geometry.SmSchemeOver k}
    (f : Boundary.SmOverHom X Y)
    (g : Boundary.SmOverHom Y Z)
    (hgraph : (Boundary.canonicalCategory composition).comp
      (SmCorQ.graphTransfer
        (Boundary.canonicalCategory composition)
        f
        (composition.diagonalDecomposition X))
      (SmCorQ.graphTransfer
        (Boundary.canonicalCategory composition)
        g
        (composition.diagonalDecomposition Y)) =
      SmCorQ.graphTransfer
        (Boundary.canonicalCategory composition)
        (Boundary.SmOverHom.comp f g)
        (composition.diagonalDecomposition X)) :
    canonicalRepresentableLinearPSTMap composition (Boundary.SmOverHom.comp f g) =
      canonicalRepresentableLinearPSTMap composition f ≫
        canonicalRepresentableLinearPSTMap composition g := by
  letI := SmCorQCat (Boundary.canonicalCategory composition)
  change
    (QtrMap (category := Boundary.canonicalCategory composition)
      (SmCorQ.graphTransfer
        (Boundary.canonicalCategory composition)
        (Boundary.SmOverHom.comp f g)
        (composition.diagonalDecomposition X)) :
      Qtr (category := Boundary.canonicalCategory composition) X ⟶
        Qtr (category := Boundary.canonicalCategory composition) Z) =
      (QtrMap (category := Boundary.canonicalCategory composition)
        (SmCorQ.graphTransfer
          (Boundary.canonicalCategory composition)
          f
          (composition.diagonalDecomposition X)) :
        Qtr (category := Boundary.canonicalCategory composition) X ⟶
          Qtr (category := Boundary.canonicalCategory composition) Y) ≫
      (QtrMap (category := Boundary.canonicalCategory composition)
        (SmCorQ.graphTransfer
          (Boundary.canonicalCategory composition)
          g
          (composition.diagonalDecomposition Y)) :
        Qtr (category := Boundary.canonicalCategory composition) Y ⟶
          Qtr (category := Boundary.canonicalCategory composition) Z)
  ext W corr
  change (Boundary.canonicalCategory composition).comp corr
      (SmCorQ.graphTransfer
        (Boundary.canonicalCategory composition)
        (Boundary.SmOverHom.comp f g)
        (composition.diagonalDecomposition X)) =
    (Boundary.canonicalCategory composition).comp
      ((Boundary.canonicalCategory composition).comp corr
        (SmCorQ.graphTransfer
          (Boundary.canonicalCategory composition)
          f
          (composition.diagonalDecomposition X)))
      (SmCorQ.graphTransfer
        (Boundary.canonicalCategory composition)
        g
        (composition.diagonalDecomposition Y))
  rw [(Boundary.canonicalCategory composition).assoc]
  rw [hgraph]

/-- The graph-transfer composition theorem for the canonical correspondence
category induces the expected composition law on representable presheaves with
transfers. -/
theorem canonicalRepresentableLinearPSTMap_comp
    (composition : Boundary.CanonicalCompositionData (k := k))
    (hgraph : Geometry.CanonicalGraphPackageCompatibilityObligation composition)
    [Abelian (LinearPST (Boundary.canonicalCategory composition))]
    [HasDerivedCategory (LinearPST (Boundary.canonicalCategory composition))]
    {X Y Z : Geometry.SmSchemeOver k}
    (f : Boundary.SmOverHom X Y)
    (g : Boundary.SmOverHom Y Z) :
    canonicalRepresentableLinearPSTMap composition (Boundary.SmOverHom.comp f g) =
      canonicalRepresentableLinearPSTMap composition f ≫
        canonicalRepresentableLinearPSTMap composition g := by
  exact canonicalRepresentableLinearPSTMap_comp_of_graphTransfer_comp composition f g
    (canonicalCategory_graphTransfer_comp (composition := composition) hgraph f g)

/-- The graph-transfer maps define the canonical representable functor
`Sm/k ⥤ LinearPST(canonicalSmCorQ)`. -/
def canonicalRepresentableLinearPSTFunctor
    (composition : Boundary.CanonicalCompositionData (k := k))
    (hgraph : Geometry.CanonicalGraphPackageCompatibilityObligation composition) :
    Geometry.SmSchemeOver k ⥤ LinearPST (Boundary.canonicalCategory composition) where
  obj := canonicalRepresentableLinearPST composition
  map f := canonicalRepresentableLinearPSTMap composition f
  map_id X := canonicalRepresentableLinearPSTMap_id composition X
  map_comp f g := canonicalRepresentableLinearPSTMap_comp composition hgraph f g

@[simp] theorem canonicalRepresentableLinearPSTFunctor_obj
    (composition : Boundary.CanonicalCompositionData (k := k))
    (hgraph : Geometry.CanonicalGraphPackageCompatibilityObligation composition)
    (X : Geometry.SmSchemeOver k) :
    (canonicalRepresentableLinearPSTFunctor composition hgraph).obj X =
      canonicalRepresentableLinearPST composition X :=
  rfl

@[simp] theorem canonicalRepresentableLinearPSTFunctor_map
    (composition : Boundary.CanonicalCompositionData (k := k))
    (hgraph : Geometry.CanonicalGraphPackageCompatibilityObligation composition)
    {X Y : Geometry.SmSchemeOver k}
    (f : X ⟶ Y) :
    (canonicalRepresentableLinearPSTFunctor composition hgraph).map f =
      canonicalRepresentableLinearPSTMap composition f :=
  rfl

/-- The external product of representable generators is represented by the
product smooth scheme. This is the honest generator-level tensor carrier before
descent through the `A1`/Nis localization:

`Q_tr(X) ⊠ Q_tr(Y) := Q_tr(X ×_k Y)`.
-/
abbrev canonicalRepresentableExternalProduct
    (composition : Boundary.CanonicalCompositionData (k := k))
    (X Y : Geometry.SmSchemeOver k) :
    LinearPST (Boundary.canonicalCategory composition) :=
  LinearPSTDayConvolution.QtrTensor
    (Boundary.canonicalCategory composition) X Y

/-- On morphisms, the representable external product is induced by the ordinary
product map in `Sm/k`, then sent through the actual representable functor just
constructed. -/
def canonicalRepresentableExternalProductMap
    (composition : Boundary.CanonicalCompositionData (k := k))
    {X₁ X₂ Y₁ Y₂ : Geometry.SmSchemeOver k}
    (f : Boundary.SmOverHom X₁ X₂)
    (g : Boundary.SmOverHom Y₁ Y₂) :
    canonicalRepresentableExternalProduct composition X₁ Y₁ ⟶
      canonicalRepresentableExternalProduct composition X₂ Y₂ :=
  canonicalRepresentableLinearPSTMap composition
    (overBaseProductMap f g)

/-- The canonical representable external product is the representable Day
tensor on the canonical correspondence category. -/
theorem canonicalRepresentableExternalProduct_eq_QtrTensor
    (composition : Boundary.CanonicalCompositionData (k := k))
    (X Y : Geometry.SmSchemeOver k) :
    canonicalRepresentableExternalProduct composition X Y =
      LinearPSTDayConvolution.QtrTensor
        (Boundary.canonicalCategory composition) X Y :=
  rfl

/-- The representable external product is functorial in both variables because
`overBaseProductMap` is functorial in `Sm/k` and
`canonicalRepresentableLinearPSTFunctor` is already an honest functor. -/
def canonicalRepresentableExternalProductFunctor
    (composition : Boundary.CanonicalCompositionData (k := k))
    (hgraph : Geometry.CanonicalGraphPackageCompatibilityObligation composition) :
    (Geometry.SmSchemeOver k × Geometry.SmSchemeOver k) ⥤
      LinearPST (Boundary.canonicalCategory composition) where
  obj XY := canonicalRepresentableExternalProduct composition XY.1 XY.2
  map fg := canonicalRepresentableExternalProductMap composition fg.1 fg.2
  map_id XY := by
    change canonicalRepresentableLinearPSTMap composition
      (overBaseProductMap (𝟙 XY.1) (𝟙 XY.2)) =
        𝟙 (canonicalRepresentableLinearPST composition
          (overBaseProductObject XY.1 XY.2))
    rw [overBaseProductMap_id]
    exact canonicalRepresentableLinearPSTMap_id composition _
  map_comp fg hg := by
    rcases fg with ⟨f₁, g₁⟩
    rcases hg with ⟨f₂, g₂⟩
    change canonicalRepresentableLinearPSTMap composition
      (overBaseProductMap (f₁ ≫ f₂) (g₁ ≫ g₂)) =
        canonicalRepresentableLinearPSTMap composition (overBaseProductMap f₁ g₁) ≫
          canonicalRepresentableLinearPSTMap composition (overBaseProductMap f₂ g₂)
    rw [overBaseProductMap_comp]
    exact canonicalRepresentableLinearPSTMap_comp composition hgraph
      (overBaseProductMap f₁ g₁) (overBaseProductMap f₂ g₂)

@[simp] theorem canonicalRepresentableExternalProductFunctor_obj
    (composition : Boundary.CanonicalCompositionData (k := k))
    (hgraph : Geometry.CanonicalGraphPackageCompatibilityObligation composition)
    (X Y : Geometry.SmSchemeOver k) :
    (canonicalRepresentableExternalProductFunctor composition hgraph).obj (X, Y) =
      canonicalRepresentableExternalProduct composition X Y :=
  rfl

@[simp] theorem canonicalRepresentableExternalProductFunctor_map
    (composition : Boundary.CanonicalCompositionData (k := k))
    (hgraph : Geometry.CanonicalGraphPackageCompatibilityObligation composition)
    {X₁ X₂ Y₁ Y₂ : Geometry.SmSchemeOver k}
    (f : X₁ ⟶ X₂) (g : Y₁ ⟶ Y₂) :
    (canonicalRepresentableExternalProductFunctor composition hgraph).map (f, g) =
      canonicalRepresentableExternalProductMap composition f g :=
  rfl

/-- For the canonical correspondence category, the representable map attached
to the ordinary `A¹` projection agrees with the decomposition-indexed owner
map from `A1Geometry.lean`. -/
theorem canonicalRepresentableLinearPSTMap_eq_projectionToBase_QtrMapOfDecomposition
    (composition : Boundary.CanonicalCompositionData (k := k))
    (X : Geometry.SmSchemeOver k)
    (D : FiniteIrreducibleComponentDecomposition (productWithA1 X)) :
    canonicalRepresentableLinearPSTMap composition (projectionToBase X) =
      (show QtrLinear (category := Boundary.canonicalCategory composition) (productWithA1 X) ⟶
          QtrLinear (category := Boundary.canonicalCategory composition) X from
        projectionToBase_QtrMapOfDecomposition
          (Boundary.canonicalCategory composition) X D) := by
  letI := SmCorQCat (Boundary.canonicalCategory composition)
  unfold canonicalRepresentableLinearPSTMap projectionToBase_QtrMapOfDecomposition
  congr 1
  unfold SmCorQ.graphTransfer
  simpa [projectionToBase_rationalCorrespondenceOfDecomposition,
    projectionToBase_finiteCorrespondenceOfDecomposition,
    projectionToBase_componentCorrespondence, projectionToBase_graphPrimeSupport,
    Geometry.ordinaryMorphismGraph_rationalCorrespondenceOfDecomposition,
    Geometry.ordinaryMorphismGraph_finiteCorrespondenceOfDecomposition,
    Geometry.ordinaryMorphismGraph_componentCorrespondence]

/-- Tensoring the `A¹` projection generator of `X` on the right by the
representable generator `Y` yields, after the geometric reassociation
`(X ×_k Y) ×_k A¹ ≅ (X ×_k A¹) ×_k Y`, the ordinary `A¹` projection generator
of `X ×_k Y`. Hence it is again a canonical `A¹`/Nis local equivalence. -/
theorem A1ProjectionGenerator_product_right_stable
    (composition : Boundary.CanonicalCompositionData (k := k))
    [Abelian (LinearPST (Boundary.canonicalCategory composition))]
    [HasDerivedCategory (LinearPST (Boundary.canonicalCategory composition))]
    (X Y : Geometry.SmSchemeOver k)
    (D : FiniteIrreducibleComponentDecomposition
      (productWithA1 (overBaseProductObject X Y))) :
    canonicalA1NisLocalEquivalences composition
      (canonicalRepresentableExternalProductMap composition (projectionToBase X) (𝟙 Y)) := by
  let W := canonicalA1NisLocalEquivalencesProperty composition
  letI : W.RespectsIso := canonicalA1NisLocalEquivalences_respectsIso composition
  have hproj :
      canonicalA1NisLocalEquivalences composition
        (canonicalRepresentableLinearPSTMap composition
          (projectionToBase (overBaseProductObject X Y))) := by
    rw [canonicalRepresentableLinearPSTMap_eq_projectionToBase_QtrMapOfDecomposition]
      using
        (canonicalA1NisGenerators_areCanonicalLocalEquivalences composition).1
          (overBaseProductObject X Y) D
  have hEq :
      overBaseProductMap (projectionToBase X) (𝟙 Y) =
        (productWithA1_product_right_iso (k := k) X Y).inv ≫
          projectionToBase (overBaseProductObject X Y) :=
    overBaseProductMap_projectionToBase_right_eq (k := k) X Y
  rw [canonicalRepresentableExternalProductMap, hEq]
  rw [canonicalRepresentableLinearPSTMap_comp]
  exact MorphismProperty.RespectsIso.precomp W
    (canonicalRepresentableLinearPSTMap composition
      ((productWithA1_product_right_iso (k := k) X Y).inv))
    (canonicalRepresentableLinearPSTMap composition
      (projectionToBase (overBaseProductObject X Y)))
    hproj

/-- Tensoring the `A¹` projection generator of `Y` on the left by the
representable generator `X` yields, after the reassociation
`(X ×_k Y) ×_k A¹ ≅ X ×_k (Y ×_k A¹)`, the ordinary `A¹` projection generator
of `X ×_k Y`. Hence it is again a canonical `A¹`/Nis local equivalence. -/
theorem A1ProjectionGenerator_product_left_stable
    (composition : Boundary.CanonicalCompositionData (k := k))
    [Abelian (LinearPST (Boundary.canonicalCategory composition))]
    [HasDerivedCategory (LinearPST (Boundary.canonicalCategory composition))]
    (X Y : Geometry.SmSchemeOver k)
    (D : FiniteIrreducibleComponentDecomposition
      (productWithA1 (overBaseProductObject X Y))) :
    canonicalA1NisLocalEquivalences composition
      (canonicalRepresentableExternalProductMap composition (𝟙 X) (projectionToBase Y)) := by
  let W := canonicalA1NisLocalEquivalencesProperty composition
  letI : W.RespectsIso := canonicalA1NisLocalEquivalences_respectsIso composition
  have hproj :
      canonicalA1NisLocalEquivalences composition
        (canonicalRepresentableLinearPSTMap composition
          (projectionToBase (overBaseProductObject X Y))) := by
    rw [canonicalRepresentableLinearPSTMap_eq_projectionToBase_QtrMapOfDecomposition]
      using
        (canonicalA1NisGenerators_areCanonicalLocalEquivalences composition).1
          (overBaseProductObject X Y) D
  have hEq :
      overBaseProductMap (𝟙 X) (projectionToBase Y) =
        (productWithA1_product_left_iso (k := k) X Y).inv ≫
          projectionToBase (overBaseProductObject X Y) :=
    overBaseProductMap_projectionToBase_left_eq (k := k) X Y
  rw [canonicalRepresentableExternalProductMap, hEq]
  rw [canonicalRepresentableLinearPSTMap_comp]
  exact MorphismProperty.RespectsIso.precomp W
    (canonicalRepresentableLinearPSTMap composition
      ((productWithA1_product_left_iso (k := k) X Y).inv))
    (canonicalRepresentableLinearPSTMap composition
      (projectionToBase (overBaseProductObject X Y)))
    hproj

/-- Right external product by a representable generator preserves primitive
canonical `A¹` projection generators. -/
theorem externalProduct_preserves_A1Generators_right
    (composition : Boundary.CanonicalCompositionData (k := k))
    [Abelian (LinearPST (Boundary.canonicalCategory composition))]
    [HasDerivedCategory (LinearPST (Boundary.canonicalCategory composition))]
    (X Y : Geometry.SmSchemeOver k)
    (D : FiniteIrreducibleComponentDecomposition
      (productWithA1 (overBaseProductObject X Y))) :
    canonicalA1NisLocalEquivalences composition
      (canonicalRepresentableExternalProductMap composition (projectionToBase X) (𝟙 Y)) :=
  A1ProjectionGenerator_product_right_stable composition X Y D

/-- Left external product by a representable generator preserves primitive
canonical `A¹` projection generators. -/
theorem externalProduct_preserves_A1Generators_left
    (composition : Boundary.CanonicalCompositionData (k := k))
    [Abelian (LinearPST (Boundary.canonicalCategory composition))]
    [HasDerivedCategory (LinearPST (Boundary.canonicalCategory composition))]
    (X Y : Geometry.SmSchemeOver k)
    (D : FiniteIrreducibleComponentDecomposition
      (productWithA1 (overBaseProductObject X Y))) :
    canonicalA1NisLocalEquivalences composition
      (canonicalRepresentableExternalProductMap composition (𝟙 X) (projectionToBase Y)) :=
  A1ProjectionGenerator_product_left_stable composition X Y D

/-- Pulling back a Nisnevich distinguished square along `base ×_k Y ⟶ base`
produces the right-product Nisnevich square in the canonical correspondence
category. -/
abbrev nisnevichSquare_product_right
    (composition : Boundary.CanonicalCompositionData (k := k))
    (hgraph : Geometry.CanonicalGraphPackageCompatibilityObligation composition)
    (sq : NisnevichDistinguishedSquareDataQ (Boundary.canonicalCategory composition))
    (Y : Geometry.SmSchemeOver k) :
    NisnevichDistinguishedSquareDataQ (Boundary.canonicalCategory composition) :=
  Boundary.NisnevichDistinguishedSquareDataQ.nisnevichSquare_product_right
    composition hgraph sq Y

/-- Pulling back a Nisnevich distinguished square along `X ×_k base ⟶ base`
produces the left-product Nisnevich square in the canonical correspondence
category. -/
abbrev nisnevichSquare_product_left
    (composition : Boundary.CanonicalCompositionData (k := k))
    (hgraph : Geometry.CanonicalGraphPackageCompatibilityObligation composition)
    (X : Geometry.SmSchemeOver k)
    (sq : NisnevichDistinguishedSquareDataQ (Boundary.canonicalCategory composition)) :
    NisnevichDistinguishedSquareDataQ (Boundary.canonicalCategory composition) :=
  Boundary.NisnevichDistinguishedSquareDataQ.nisnevichSquare_product_left
    composition hgraph X sq

/-- The Nisnevich descent generator remains a canonical local equivalence after
right product, because the product square is the canonical pullback square and
the owner theorem already identifies every canonical Nis generator as local. -/
theorem NisDescentGenerator_product_right_stable
    (composition : Boundary.CanonicalCompositionData (k := k))
    (hgraph : Geometry.CanonicalGraphPackageCompatibilityObligation composition)
    [Abelian (LinearPST (Boundary.canonicalCategory composition))]
    [HasDerivedCategory (LinearPST (Boundary.canonicalCategory composition))]
    (sq : NisnevichDistinguishedSquareDataQ (Boundary.canonicalCategory composition))
    (Y : Geometry.SmSchemeOver k) :
    canonicalA1NisLocalEquivalences composition
      ((nisnevichSquare_product_right composition hgraph sq Y).nisnevichDescentGeneratorMapLinear) := by
  simpa [nisnevichSquare_product_right] using
    (canonicalA1NisGenerators_areCanonicalLocalEquivalences composition).2
      (Boundary.NisnevichDistinguishedSquareDataQ.nisnevichSquare_product_right
        composition hgraph sq Y)

/-- The Nisnevich descent generator remains a canonical local equivalence after
left product, for the same reason as on the right: the product square is the
canonical pullback square, and canonical Nis generators are already local. -/
theorem NisDescentGenerator_product_left_stable
    (composition : Boundary.CanonicalCompositionData (k := k))
    (hgraph : Geometry.CanonicalGraphPackageCompatibilityObligation composition)
    [Abelian (LinearPST (Boundary.canonicalCategory composition))]
    [HasDerivedCategory (LinearPST (Boundary.canonicalCategory composition))]
    (X : Geometry.SmSchemeOver k)
    (sq : NisnevichDistinguishedSquareDataQ (Boundary.canonicalCategory composition)) :
    canonicalA1NisLocalEquivalences composition
      ((nisnevichSquare_product_left composition hgraph X sq).nisnevichDescentGeneratorMapLinear) := by
  simpa [nisnevichSquare_product_left] using
    (canonicalA1NisGenerators_areCanonicalLocalEquivalences composition).2
      (Boundary.NisnevichDistinguishedSquareDataQ.nisnevichSquare_product_left
        composition hgraph X sq)

/-- Right external product preserves primitive Nisnevich descent generators by
identifying them with the descent generator of the right-product pullback
square. -/
theorem externalProduct_preserves_NisGenerators_right
    (composition : Boundary.CanonicalCompositionData (k := k))
    (hgraph : Geometry.CanonicalGraphPackageCompatibilityObligation composition)
    [Abelian (LinearPST (Boundary.canonicalCategory composition))]
    [HasDerivedCategory (LinearPST (Boundary.canonicalCategory composition))]
    (sq : NisnevichDistinguishedSquareDataQ (Boundary.canonicalCategory composition))
    (Y : Geometry.SmSchemeOver k) :
    canonicalA1NisLocalEquivalences composition
      ((nisnevichSquare_product_right composition hgraph sq Y).nisnevichDescentGeneratorMapLinear) :=
  NisDescentGenerator_product_right_stable composition hgraph sq Y

/-- Left external product preserves primitive Nisnevich descent generators by
identifying them with the descent generator of the left-product pullback
square. -/
theorem externalProduct_preserves_NisGenerators_left
    (composition : Boundary.CanonicalCompositionData (k := k))
    (hgraph : Geometry.CanonicalGraphPackageCompatibilityObligation composition)
    [Abelian (LinearPST (Boundary.canonicalCategory composition))]
    [HasDerivedCategory (LinearPST (Boundary.canonicalCategory composition))]
    (X : Geometry.SmSchemeOver k)
    (sq : NisnevichDistinguishedSquareDataQ (Boundary.canonicalCategory composition)) :
    canonicalA1NisLocalEquivalences composition
      ((nisnevichSquare_product_left composition hgraph X sq).nisnevichDescentGeneratorMapLinear) :=
  NisDescentGenerator_product_left_stable composition hgraph X sq

/-- Combined right-product stability of the two primitive canonical generator
families: `A¹` projections and Nisnevich descent generators. -/
theorem externalProduct_preserves_A1NisGenerators_right
    (composition : Boundary.CanonicalCompositionData (k := k))
    (hgraph : Geometry.CanonicalGraphPackageCompatibilityObligation composition)
    [Abelian (LinearPST (Boundary.canonicalCategory composition))]
    [HasDerivedCategory (LinearPST (Boundary.canonicalCategory composition))]
    (X Y : Geometry.SmSchemeOver k)
    (D : FiniteIrreducibleComponentDecomposition
      (productWithA1 (overBaseProductObject X Y)))
    (sq : NisnevichDistinguishedSquareDataQ (Boundary.canonicalCategory composition)) :
    canonicalA1NisLocalEquivalences composition
        (canonicalRepresentableExternalProductMap composition (projectionToBase X) (𝟙 Y)) ∧
      canonicalA1NisLocalEquivalences composition
        ((nisnevichSquare_product_right composition hgraph sq Y).nisnevichDescentGeneratorMapLinear) :=
  ⟨externalProduct_preserves_A1Generators_right composition X Y D,
    externalProduct_preserves_NisGenerators_right composition hgraph sq Y⟩

/-- Combined left-product stability of the two primitive canonical generator
families: `A¹` projections and Nisnevich descent generators. -/
theorem externalProduct_preserves_A1NisGenerators_left
    (composition : Boundary.CanonicalCompositionData (k := k))
    (hgraph : Geometry.CanonicalGraphPackageCompatibilityObligation composition)
    [Abelian (LinearPST (Boundary.canonicalCategory composition))]
    [HasDerivedCategory (LinearPST (Boundary.canonicalCategory composition))]
    (X Y : Geometry.SmSchemeOver k)
    (D : FiniteIrreducibleComponentDecomposition
      (productWithA1 (overBaseProductObject X Y)))
    (sq : NisnevichDistinguishedSquareDataQ (Boundary.canonicalCategory composition)) :
    canonicalA1NisLocalEquivalences composition
        (canonicalRepresentableExternalProductMap composition (𝟙 X) (projectionToBase Y)) ∧
      canonicalA1NisLocalEquivalences composition
        ((nisnevichSquare_product_left composition hgraph X sq).nisnevichDescentGeneratorMapLinear) :=
  ⟨externalProduct_preserves_A1Generators_left composition X Y D,
    externalProduct_preserves_NisGenerators_left composition hgraph X sq⟩

/-- Right tensoring sends the primitive canonical `A¹` projection generator to
the Bousfield-generated canonical `A¹`/Nis weak-equivalence class. -/
theorem canonicalA1NisGeneratedWeakEquivalences_tensor_right
    (composition : Boundary.CanonicalCompositionData (k := k))
    [Abelian (LinearPST (Boundary.canonicalCategory composition))]
    [HasDerivedCategory (LinearPST (Boundary.canonicalCategory composition))]
    (X Y : Geometry.SmSchemeOver k)
    (D : FiniteIrreducibleComponentDecomposition
      (productWithA1 (overBaseProductObject X Y))) :
    canonicalA1NisGeneratedWeakEquivalences composition
      (canonicalRepresentableExternalProductMap composition (projectionToBase X) (𝟙 Y)) :=
  (canonicalA1NisGeneratedWeakEquivalences_eq_localEquivalences
      composition
      (canonicalRepresentableExternalProductMap composition (projectionToBase X) (𝟙 Y))).mpr
    (externalProduct_preserves_A1Generators_right composition X Y D)

/-- Left tensoring sends the primitive canonical `A¹` projection generator to
the Bousfield-generated canonical `A¹`/Nis weak-equivalence class. -/
theorem canonicalA1NisGeneratedWeakEquivalences_tensor_left
    (composition : Boundary.CanonicalCompositionData (k := k))
    [Abelian (LinearPST (Boundary.canonicalCategory composition))]
    [HasDerivedCategory (LinearPST (Boundary.canonicalCategory composition))]
    (X Y : Geometry.SmSchemeOver k)
    (D : FiniteIrreducibleComponentDecomposition
      (productWithA1 (overBaseProductObject X Y))) :
    canonicalA1NisGeneratedWeakEquivalences composition
      (canonicalRepresentableExternalProductMap composition (𝟙 X) (projectionToBase Y)) :=
  (canonicalA1NisGeneratedWeakEquivalences_eq_localEquivalences
      composition
      (canonicalRepresentableExternalProductMap composition (𝟙 X) (projectionToBase Y))).mpr
    (externalProduct_preserves_A1Generators_left composition X Y D)

/-- Right tensoring sends the product Nisnevich descent generator to the
Bousfield-generated canonical `A¹`/Nis weak-equivalence class. -/
theorem canonicalA1NisGeneratedWeakEquivalences_tensor_right_nis
    (composition : Boundary.CanonicalCompositionData (k := k))
    (hgraph : Geometry.CanonicalGraphPackageCompatibilityObligation composition)
    [Abelian (LinearPST (Boundary.canonicalCategory composition))]
    [HasDerivedCategory (LinearPST (Boundary.canonicalCategory composition))]
    (sq : NisnevichDistinguishedSquareDataQ (Boundary.canonicalCategory composition))
    (Y : Geometry.SmSchemeOver k) :
    canonicalA1NisGeneratedWeakEquivalences composition
      ((nisnevichSquare_product_right composition hgraph sq Y).nisnevichDescentGeneratorMapLinear) :=
  (canonicalA1NisGeneratedWeakEquivalences_eq_localEquivalences
      composition
      ((nisnevichSquare_product_right composition hgraph sq Y).nisnevichDescentGeneratorMapLinear)).mpr
    (externalProduct_preserves_NisGenerators_right composition hgraph sq Y)

/-- Left tensoring sends the product Nisnevich descent generator to the
Bousfield-generated canonical `A¹`/Nis weak-equivalence class. -/
theorem canonicalA1NisGeneratedWeakEquivalences_tensor_left_nis
    (composition : Boundary.CanonicalCompositionData (k := k))
    (hgraph : Geometry.CanonicalGraphPackageCompatibilityObligation composition)
    [Abelian (LinearPST (Boundary.canonicalCategory composition))]
    [HasDerivedCategory (LinearPST (Boundary.canonicalCategory composition))]
    (X : Geometry.SmSchemeOver k)
    (sq : NisnevichDistinguishedSquareDataQ (Boundary.canonicalCategory composition)) :
    canonicalA1NisGeneratedWeakEquivalences composition
      ((nisnevichSquare_product_left composition hgraph X sq).nisnevichDescentGeneratorMapLinear) :=
  (canonicalA1NisGeneratedWeakEquivalences_eq_localEquivalences
      composition
      ((nisnevichSquare_product_left composition hgraph X sq).nisnevichDescentGeneratorMapLinear)).mpr
    (externalProduct_preserves_NisGenerators_left composition hgraph X sq)

/-- The effective-motives localization inverts the degree-zero map obtained by
right external product of an `A¹` projection with a representable generator. -/
theorem canonicalEffectiveMotivesLocalization_inverts_externalProduct_A1Generator_right
    (composition : Boundary.CanonicalCompositionData (k := k))
    [Abelian (LinearPST (Boundary.canonicalCategory composition))]
    [HasDerivedCategory (LinearPST (Boundary.canonicalCategory composition))]
    [Abelian (canonicalA1NisLocalization composition)]
    [HasDerivedCategory (canonicalA1NisLocalization composition)]
    [(canonicalA1NisLocalizationFunctor composition).Additive]
    [Limits.PreservesFiniteLimits (canonicalA1NisLocalizationFunctor composition)]
    [Limits.PreservesFiniteColimits (canonicalA1NisLocalizationFunctor composition)]
    (X Y : Geometry.SmSchemeOver k)
    (D : FiniteIrreducibleComponentDecomposition
      (productWithA1 (overBaseProductObject X Y))) :
    IsIso
      ((canonicalEffectiveMotivesLocalizationFunctor composition).map
        ((DerivedCategory.singleFunctor
          (LinearPST (Boundary.canonicalCategory composition)) 0).map
          (canonicalRepresentableExternalProductMap composition (projectionToBase X) (𝟙 Y)))) :=
  canonicalEffectiveMotivesLocalizationFunctor_map_degreeZero_isIso_of_localEquivalence
    composition _
    (externalProduct_preserves_A1Generators_right composition X Y D)

/-- The effective-motives localization inverts the degree-zero map obtained by
left external product of a representable generator with an `A¹` projection. -/
theorem canonicalEffectiveMotivesLocalization_inverts_externalProduct_A1Generator_left
    (composition : Boundary.CanonicalCompositionData (k := k))
    [Abelian (LinearPST (Boundary.canonicalCategory composition))]
    [HasDerivedCategory (LinearPST (Boundary.canonicalCategory composition))]
    [Abelian (canonicalA1NisLocalization composition)]
    [HasDerivedCategory (canonicalA1NisLocalization composition)]
    [(canonicalA1NisLocalizationFunctor composition).Additive]
    [Limits.PreservesFiniteLimits (canonicalA1NisLocalizationFunctor composition)]
    [Limits.PreservesFiniteColimits (canonicalA1NisLocalizationFunctor composition)]
    (X Y : Geometry.SmSchemeOver k)
    (D : FiniteIrreducibleComponentDecomposition
      (productWithA1 (overBaseProductObject X Y))) :
    IsIso
      ((canonicalEffectiveMotivesLocalizationFunctor composition).map
        ((DerivedCategory.singleFunctor
          (LinearPST (Boundary.canonicalCategory composition)) 0).map
          (canonicalRepresentableExternalProductMap composition (𝟙 X) (projectionToBase Y)))) :=
  canonicalEffectiveMotivesLocalizationFunctor_map_degreeZero_isIso_of_localEquivalence
    composition _
    (externalProduct_preserves_A1Generators_left composition X Y D)

/-- The effective-motives localization inverts right-product Nisnevich descent
generators. -/
theorem canonicalEffectiveMotivesLocalization_inverts_externalProduct_NisGenerator_right
    (composition : Boundary.CanonicalCompositionData (k := k))
    (hgraph : Geometry.CanonicalGraphPackageCompatibilityObligation composition)
    [Abelian (LinearPST (Boundary.canonicalCategory composition))]
    [HasDerivedCategory (LinearPST (Boundary.canonicalCategory composition))]
    [Abelian (canonicalA1NisLocalization composition)]
    [HasDerivedCategory (canonicalA1NisLocalization composition)]
    [(canonicalA1NisLocalizationFunctor composition).Additive]
    [Limits.PreservesFiniteLimits (canonicalA1NisLocalizationFunctor composition)]
    [Limits.PreservesFiniteColimits (canonicalA1NisLocalizationFunctor composition)]
    (sq : NisnevichDistinguishedSquareDataQ (Boundary.canonicalCategory composition))
    (Y : Geometry.SmSchemeOver k) :
    IsIso
      ((canonicalEffectiveMotivesLocalizationFunctor composition).map
        ((DerivedCategory.singleFunctor
          (LinearPST (Boundary.canonicalCategory composition)) 0).map
          ((nisnevichSquare_product_right composition hgraph sq Y).nisnevichDescentGeneratorMapLinear))) :=
  canonicalEffectiveMotivesLocalizationFunctor_map_degreeZero_isIso_of_localEquivalence
    composition _
    (externalProduct_preserves_NisGenerators_right composition hgraph sq Y)

/-- The effective-motives localization inverts left-product Nisnevich descent
generators. -/
theorem canonicalEffectiveMotivesLocalization_inverts_externalProduct_NisGenerator_left
    (composition : Boundary.CanonicalCompositionData (k := k))
    (hgraph : Geometry.CanonicalGraphPackageCompatibilityObligation composition)
    [Abelian (LinearPST (Boundary.canonicalCategory composition))]
    [HasDerivedCategory (LinearPST (Boundary.canonicalCategory composition))]
    [Abelian (canonicalA1NisLocalization composition)]
    [HasDerivedCategory (canonicalA1NisLocalization composition)]
    [(canonicalA1NisLocalizationFunctor composition).Additive]
    [Limits.PreservesFiniteLimits (canonicalA1NisLocalizationFunctor composition)]
    [Limits.PreservesFiniteColimits (canonicalA1NisLocalizationFunctor composition)]
    (X : Geometry.SmSchemeOver k)
    (sq : NisnevichDistinguishedSquareDataQ (Boundary.canonicalCategory composition)) :
    IsIso
      ((canonicalEffectiveMotivesLocalizationFunctor composition).map
        ((DerivedCategory.singleFunctor
          (LinearPST (Boundary.canonicalCategory composition)) 0).map
          ((nisnevichSquare_product_left composition hgraph X sq).nisnevichDescentGeneratorMapLinear))) :=
  canonicalEffectiveMotivesLocalizationFunctor_map_degreeZero_isIso_of_localEquivalence
    composition _
    (externalProduct_preserves_NisGenerators_left composition hgraph X sq)

/-- The canonical Verdier `A¹`/Nis subcategory contains the degree-zero right
tensor image of every primitive `A¹` projection generator. -/
theorem canonicalA1NisVerdierLocalizingSubcategory_contains_tensor_A1Generator_right
    (composition : Boundary.CanonicalCompositionData (k := k))
    [Abelian (LinearPST (Boundary.canonicalCategory composition))]
    [HasDerivedCategory (LinearPST (Boundary.canonicalCategory composition))]
    [Abelian (canonicalA1NisLocalization composition)]
    [HasDerivedCategory (canonicalA1NisLocalization composition)]
    [(canonicalA1NisLocalizationFunctor composition).Additive]
    [Limits.PreservesFiniteLimits (canonicalA1NisLocalizationFunctor composition)]
    [Limits.PreservesFiniteColimits (canonicalA1NisLocalizationFunctor composition)]
    (X Y : Geometry.SmSchemeOver k)
    (D : FiniteIrreducibleComponentDecomposition
      (productWithA1 (overBaseProductObject X Y))) :
    canonicalA1NisVerdierLocalizingMorphisms composition
      ((DerivedCategory.singleFunctor
          (LinearPST (Boundary.canonicalCategory composition)) 0).map
        (canonicalRepresentableExternalProductMap composition (projectionToBase X) (𝟙 Y))) :=
  canonicalA1NisVerdierLocalizingSubcategory_contains_degreeZeroA1Nis
    composition _
    (canonicalA1NisGeneratedWeakEquivalences_tensor_right composition X Y D)

/-- The canonical Verdier `A¹`/Nis subcategory contains the degree-zero left
tensor image of every primitive `A¹` projection generator. -/
theorem canonicalA1NisVerdierLocalizingSubcategory_contains_tensor_A1Generator_left
    (composition : Boundary.CanonicalCompositionData (k := k))
    [Abelian (LinearPST (Boundary.canonicalCategory composition))]
    [HasDerivedCategory (LinearPST (Boundary.canonicalCategory composition))]
    [Abelian (canonicalA1NisLocalization composition)]
    [HasDerivedCategory (canonicalA1NisLocalization composition)]
    [(canonicalA1NisLocalizationFunctor composition).Additive]
    [Limits.PreservesFiniteLimits (canonicalA1NisLocalizationFunctor composition)]
    [Limits.PreservesFiniteColimits (canonicalA1NisLocalizationFunctor composition)]
    (X Y : Geometry.SmSchemeOver k)
    (D : FiniteIrreducibleComponentDecomposition
      (productWithA1 (overBaseProductObject X Y))) :
    canonicalA1NisVerdierLocalizingMorphisms composition
      ((DerivedCategory.singleFunctor
          (LinearPST (Boundary.canonicalCategory composition)) 0).map
        (canonicalRepresentableExternalProductMap composition (𝟙 X) (projectionToBase Y))) :=
  canonicalA1NisVerdierLocalizingSubcategory_contains_degreeZeroA1Nis
    composition _
    (canonicalA1NisGeneratedWeakEquivalences_tensor_left composition X Y D)

/-- The canonical Verdier `A¹`/Nis subcategory contains the degree-zero right
tensor image of every Nisnevich descent generator. -/
theorem canonicalA1NisVerdierLocalizingSubcategory_contains_tensor_NisGenerator_right
    (composition : Boundary.CanonicalCompositionData (k := k))
    (hgraph : Geometry.CanonicalGraphPackageCompatibilityObligation composition)
    [Abelian (LinearPST (Boundary.canonicalCategory composition))]
    [HasDerivedCategory (LinearPST (Boundary.canonicalCategory composition))]
    [Abelian (canonicalA1NisLocalization composition)]
    [HasDerivedCategory (canonicalA1NisLocalization composition)]
    [(canonicalA1NisLocalizationFunctor composition).Additive]
    [Limits.PreservesFiniteLimits (canonicalA1NisLocalizationFunctor composition)]
    [Limits.PreservesFiniteColimits (canonicalA1NisLocalizationFunctor composition)]
    (sq : NisnevichDistinguishedSquareDataQ (Boundary.canonicalCategory composition))
    (Y : Geometry.SmSchemeOver k) :
    canonicalA1NisVerdierLocalizingMorphisms composition
      ((DerivedCategory.singleFunctor
          (LinearPST (Boundary.canonicalCategory composition)) 0).map
        ((nisnevichSquare_product_right composition hgraph sq Y).nisnevichDescentGeneratorMapLinear)) :=
  canonicalA1NisVerdierLocalizingSubcategory_contains_degreeZeroA1Nis
    composition _
    (canonicalA1NisGeneratedWeakEquivalences_tensor_right_nis composition hgraph sq Y)

/-- The canonical Verdier `A¹`/Nis subcategory contains the degree-zero left
tensor image of every Nisnevich descent generator. -/
theorem canonicalA1NisVerdierLocalizingSubcategory_contains_tensor_NisGenerator_left
    (composition : Boundary.CanonicalCompositionData (k := k))
    (hgraph : Geometry.CanonicalGraphPackageCompatibilityObligation composition)
    [Abelian (LinearPST (Boundary.canonicalCategory composition))]
    [HasDerivedCategory (LinearPST (Boundary.canonicalCategory composition))]
    [Abelian (canonicalA1NisLocalization composition)]
    [HasDerivedCategory (canonicalA1NisLocalization composition)]
    [(canonicalA1NisLocalizationFunctor composition).Additive]
    [Limits.PreservesFiniteLimits (canonicalA1NisLocalizationFunctor composition)]
    [Limits.PreservesFiniteColimits (canonicalA1NisLocalizationFunctor composition)]
    (X : Geometry.SmSchemeOver k)
    (sq : NisnevichDistinguishedSquareDataQ (Boundary.canonicalCategory composition)) :
    canonicalA1NisVerdierLocalizingMorphisms composition
      ((DerivedCategory.singleFunctor
          (LinearPST (Boundary.canonicalCategory composition)) 0).map
        ((nisnevichSquare_product_left composition hgraph X sq).nisnevichDescentGeneratorMapLinear)) :=
  canonicalA1NisVerdierLocalizingSubcategory_contains_degreeZeroA1Nis
    composition _
    (canonicalA1NisGeneratedWeakEquivalences_tensor_left_nis composition hgraph X sq)

/-- Canonical `A¹`/Nis Verdier tensor-ideal package at the generator level:
tensoring any primitive `A¹` projection or Nisnevich descent generator on
either side by a representable generator remains in the canonical Verdier
localizing morphism class. This is the precise owner-level descent input used
before any ambient monoidal structure on effective motives is claimed. -/
theorem canonicalA1NisVerdierLocalizingSubcategory_tensorIdeal
    (composition : Boundary.CanonicalCompositionData (k := k))
    (hgraph : Geometry.CanonicalGraphPackageCompatibilityObligation composition)
    [Abelian (LinearPST (Boundary.canonicalCategory composition))]
    [HasDerivedCategory (LinearPST (Boundary.canonicalCategory composition))]
    [Abelian (canonicalA1NisLocalization composition)]
    [HasDerivedCategory (canonicalA1NisLocalization composition)]
    [(canonicalA1NisLocalizationFunctor composition).Additive]
    [Limits.PreservesFiniteLimits (canonicalA1NisLocalizationFunctor composition)]
    [Limits.PreservesFiniteColimits (canonicalA1NisLocalizationFunctor composition)]
    (X Y : Geometry.SmSchemeOver k)
    (D : FiniteIrreducibleComponentDecomposition
      (productWithA1 (overBaseProductObject X Y)))
    (sq : NisnevichDistinguishedSquareDataQ (Boundary.canonicalCategory composition)) :
    canonicalA1NisVerdierLocalizingMorphisms composition
        ((DerivedCategory.singleFunctor
            (LinearPST (Boundary.canonicalCategory composition)) 0).map
          (canonicalRepresentableExternalProductMap composition (projectionToBase X) (𝟙 Y))) ∧
      canonicalA1NisVerdierLocalizingMorphisms composition
        ((DerivedCategory.singleFunctor
            (LinearPST (Boundary.canonicalCategory composition)) 0).map
          (canonicalRepresentableExternalProductMap composition (𝟙 X) (projectionToBase Y))) ∧
      canonicalA1NisVerdierLocalizingMorphisms composition
        ((DerivedCategory.singleFunctor
            (LinearPST (Boundary.canonicalCategory composition)) 0).map
          ((nisnevichSquare_product_right composition hgraph sq Y).nisnevichDescentGeneratorMapLinear)) ∧
      canonicalA1NisVerdierLocalizingMorphisms composition
        ((DerivedCategory.singleFunctor
            (LinearPST (Boundary.canonicalCategory composition)) 0).map
          ((nisnevichSquare_product_left composition hgraph X sq).nisnevichDescentGeneratorMapLinear)) := by
  refine ⟨?_, ⟨?_, ⟨?_, ?_⟩⟩⟩
  · exact
      canonicalA1NisVerdierLocalizingSubcategory_contains_tensor_A1Generator_right
        composition X Y D
  · exact
      canonicalA1NisVerdierLocalizingSubcategory_contains_tensor_A1Generator_left
        composition X Y D
  · exact
      canonicalA1NisVerdierLocalizingSubcategory_contains_tensor_NisGenerator_right
        composition hgraph sq Y
  · exact
      canonicalA1NisVerdierLocalizingSubcategory_contains_tensor_NisGenerator_left
        composition hgraph X sq

/-- The degree-zero derived maps satisfy composition because
`DerivedCategory.singleFunctor` is functorial. -/
theorem canonicalRepresentableComplexMap_comp
    (composition : Boundary.CanonicalCompositionData (k := k))
    (hgraph : Geometry.CanonicalGraphPackageCompatibilityObligation composition)
    [Abelian (LinearPST (Boundary.canonicalCategory composition))]
    [HasDerivedCategory (LinearPST (Boundary.canonicalCategory composition))]
    {X Y Z : Geometry.SmSchemeOver k}
    (f : Boundary.SmOverHom X Y)
    (g : Boundary.SmOverHom Y Z) :
    canonicalRepresentableComplexMap composition (Boundary.SmOverHom.comp f g) =
      canonicalRepresentableComplexMap composition f ≫
        canonicalRepresentableComplexMap composition g := by
  simp [canonicalRepresentableComplexMap, canonicalRepresentableLinearPSTMap_comp composition hgraph,
    Functor.map_comp]

/-- The degree-zero representable complexes define the canonical functor
`Sm/k ⥤ D(LinearPST(canonicalSmCorQ))`. -/
def canonicalRepresentableComplexFunctor
    (composition : Boundary.CanonicalCompositionData (k := k))
    (hgraph : Geometry.CanonicalGraphPackageCompatibilityObligation composition)
    [Abelian (LinearPST (Boundary.canonicalCategory composition))]
    [HasDerivedCategory (LinearPST (Boundary.canonicalCategory composition))] :
    Geometry.SmSchemeOver k ⥤ canonicalEffectiveAmbientDerivedCategory composition where
  obj := canonicalRepresentableComplex composition
  map f := canonicalRepresentableComplexMap composition f
  map_id X := canonicalRepresentableComplexMap_id composition X
  map_comp f g := canonicalRepresentableComplexMap_comp composition hgraph f g

@[simp] theorem canonicalRepresentableComplexFunctor_obj
    (composition : Boundary.CanonicalCompositionData (k := k))
    (hgraph : Geometry.CanonicalGraphPackageCompatibilityObligation composition)
    [Abelian (LinearPST (Boundary.canonicalCategory composition))]
    [HasDerivedCategory (LinearPST (Boundary.canonicalCategory composition))]
    (X : Geometry.SmSchemeOver k) :
    (canonicalRepresentableComplexFunctor composition hgraph).obj X =
      canonicalRepresentableComplex composition X :=
  rfl

@[simp] theorem canonicalRepresentableComplexFunctor_map
    (composition : Boundary.CanonicalCompositionData (k := k))
    (hgraph : Geometry.CanonicalGraphPackageCompatibilityObligation composition)
    [Abelian (LinearPST (Boundary.canonicalCategory composition))]
    [HasDerivedCategory (LinearPST (Boundary.canonicalCategory composition))]
    {X Y : Geometry.SmSchemeOver k}
    (f : X ⟶ Y) :
    (canonicalRepresentableComplexFunctor composition hgraph).map f =
      canonicalRepresentableComplexMap composition f :=
  rfl

/-- Degree-zero derived external product on representable generators: the
generator attached to `(X,Y)` is the derived representable of `X ×_k Y`. -/
abbrev canonicalRepresentableComplexExternalProduct
    (composition : Boundary.CanonicalCompositionData (k := k))
    [Abelian (LinearPST (Boundary.canonicalCategory composition))]
    [HasDerivedCategory (LinearPST (Boundary.canonicalCategory composition))]
    (X Y : Geometry.SmSchemeOver k) :
    canonicalEffectiveAmbientDerivedCategory composition :=
  canonicalRepresentableComplex composition (overBaseProductObject X Y)

/-- Bifunctorial degree-zero derived external product on representable
generators. -/
def canonicalRepresentableComplexExternalProductFunctor
    (composition : Boundary.CanonicalCompositionData (k := k))
    (hgraph : Geometry.CanonicalGraphPackageCompatibilityObligation composition)
    [Abelian (LinearPST (Boundary.canonicalCategory composition))]
    [HasDerivedCategory (LinearPST (Boundary.canonicalCategory composition))] :
    (Geometry.SmSchemeOver k × Geometry.SmSchemeOver k) ⥤
      canonicalEffectiveAmbientDerivedCategory composition where
  obj XY := canonicalRepresentableComplexExternalProduct composition XY.1 XY.2
  map fg := canonicalRepresentableComplexMap composition
    (overBaseProductMap fg.1 fg.2)
  map_id XY := by
    change canonicalRepresentableComplexMap composition
      (overBaseProductMap (𝟙 XY.1) (𝟙 XY.2)) =
        𝟙 (canonicalRepresentableComplex composition
          (overBaseProductObject XY.1 XY.2))
    rw [overBaseProductMap_id]
    exact canonicalRepresentableComplexMap_id composition _
  map_comp fg hg := by
    rcases fg with ⟨f₁, g₁⟩
    rcases hg with ⟨f₂, g₂⟩
    change canonicalRepresentableComplexMap composition
      (overBaseProductMap (f₁ ≫ f₂) (g₁ ≫ g₂)) =
        canonicalRepresentableComplexMap composition (overBaseProductMap f₁ g₁) ≫
          canonicalRepresentableComplexMap composition (overBaseProductMap f₂ g₂)
    rw [overBaseProductMap_comp]
    exact canonicalRepresentableComplexMap_comp composition hgraph
      (overBaseProductMap f₁ g₁) (overBaseProductMap f₂ g₂)

@[simp] theorem canonicalRepresentableComplexExternalProductFunctor_obj
    (composition : Boundary.CanonicalCompositionData (k := k))
    (hgraph : Geometry.CanonicalGraphPackageCompatibilityObligation composition)
    [Abelian (LinearPST (Boundary.canonicalCategory composition))]
    [HasDerivedCategory (LinearPST (Boundary.canonicalCategory composition))]
    (X Y : Geometry.SmSchemeOver k) :
    (canonicalRepresentableComplexExternalProductFunctor composition hgraph).obj (X, Y) =
      canonicalRepresentableComplexExternalProduct composition X Y :=
  rfl

@[simp] theorem canonicalRepresentableComplexExternalProductFunctor_map
    (composition : Boundary.CanonicalCompositionData (k := k))
    (hgraph : Geometry.CanonicalGraphPackageCompatibilityObligation composition)
    [Abelian (LinearPST (Boundary.canonicalCategory composition))]
    [HasDerivedCategory (LinearPST (Boundary.canonicalCategory composition))]
    {X₁ X₂ Y₁ Y₂ : Geometry.SmSchemeOver k}
    (f : X₁ ⟶ X₂) (g : Y₁ ⟶ Y₂) :
    (canonicalRepresentableComplexExternalProductFunctor composition hgraph).map (f, g) =
      canonicalRepresentableComplexMap composition (overBaseProductMap f g) :=
  rfl

/-- The canonical effective motive object of a smooth `k`-scheme, defined as
the image of the degree-zero representable complex under the validated
effective-motives localization functor. -/
def canonicalEffectiveMotive
    (composition : Boundary.CanonicalCompositionData (k := k))
    [Abelian (LinearPST (Boundary.canonicalCategory composition))]
    [HasDerivedCategory (LinearPST (Boundary.canonicalCategory composition))]
    [Abelian (canonicalA1NisLocalization composition)]
    [HasDerivedCategory (canonicalA1NisLocalization composition)]
    [(canonicalA1NisLocalizationFunctor composition).Additive]
    [Limits.PreservesFiniteLimits (canonicalA1NisLocalizationFunctor composition)]
    [Limits.PreservesFiniteColimits (canonicalA1NisLocalizationFunctor composition)] :
    Geometry.SmSchemeOver k → canonicalEffectiveMotives composition :=
  fun X =>
    (canonicalEffectiveMotivesLocalizationFunctor composition).obj
      (canonicalRepresentableComplex composition X)

@[simp] theorem canonicalEffectiveMotive_eq_localization_obj
    (composition : Boundary.CanonicalCompositionData (k := k))
    [Abelian (LinearPST (Boundary.canonicalCategory composition))]
    [HasDerivedCategory (LinearPST (Boundary.canonicalCategory composition))]
    [Abelian (canonicalA1NisLocalization composition)]
    [HasDerivedCategory (canonicalA1NisLocalization composition)]
    [(canonicalA1NisLocalizationFunctor composition).Additive]
    [Limits.PreservesFiniteLimits (canonicalA1NisLocalizationFunctor composition)]
    [Limits.PreservesFiniteColimits (canonicalA1NisLocalizationFunctor composition)]
    (X : Geometry.SmSchemeOver k) :
    canonicalEffectiveMotive composition X =
      (canonicalEffectiveMotivesLocalizationFunctor composition).obj
        (canonicalRepresentableComplex composition X) :=
  rfl

/-- External product carrier on effective generators: the generator attached to
`(X,Y)` is the canonical effective motive of `X ×_k Y`. -/
abbrev canonicalEffectiveMotiveExternalProduct
    (composition : Boundary.CanonicalCompositionData (k := k))
    [Abelian (LinearPST (Boundary.canonicalCategory composition))]
    [HasDerivedCategory (LinearPST (Boundary.canonicalCategory composition))]
    [Abelian (canonicalA1NisLocalization composition)]
    [HasDerivedCategory (canonicalA1NisLocalization composition)]
    [(canonicalA1NisLocalizationFunctor composition).Additive]
    [Limits.PreservesFiniteLimits (canonicalA1NisLocalizationFunctor composition)]
    [Limits.PreservesFiniteColimits (canonicalA1NisLocalizationFunctor composition)]
    (X Y : Geometry.SmSchemeOver k) :
    canonicalEffectiveMotives composition :=
  canonicalEffectiveMotive composition (overBaseProductObject X Y)

@[simp] theorem canonicalEffectiveMotiveExternalProduct_eq
    (composition : Boundary.CanonicalCompositionData (k := k))
    [Abelian (LinearPST (Boundary.canonicalCategory composition))]
    [HasDerivedCategory (LinearPST (Boundary.canonicalCategory composition))]
    [Abelian (canonicalA1NisLocalization composition)]
    [HasDerivedCategory (canonicalA1NisLocalization composition)]
    [(canonicalA1NisLocalizationFunctor composition).Additive]
    [Limits.PreservesFiniteLimits (canonicalA1NisLocalizationFunctor composition)]
    [Limits.PreservesFiniteColimits (canonicalA1NisLocalizationFunctor composition)]
    (X Y : Geometry.SmSchemeOver k) :
    canonicalEffectiveMotiveExternalProduct composition X Y =
      canonicalEffectiveMotive composition (overBaseProductObject X Y) :=
  rfl

/-- Public name for the product carrier on canonical effective motive
generators. -/
abbrev canonicalEffectiveMotives_tensorProduct
    (composition : Boundary.CanonicalCompositionData (k := k))
    [Abelian (LinearPST (Boundary.canonicalCategory composition))]
    [HasDerivedCategory (LinearPST (Boundary.canonicalCategory composition))]
    [Abelian (canonicalA1NisLocalization composition)]
    [HasDerivedCategory (canonicalA1NisLocalization composition)]
    [(canonicalA1NisLocalizationFunctor composition).Additive]
    [Limits.PreservesFiniteLimits (canonicalA1NisLocalizationFunctor composition)]
    [Limits.PreservesFiniteColimits (canonicalA1NisLocalizationFunctor composition)]
    (X Y : Geometry.SmSchemeOver k) :
    canonicalEffectiveMotives composition :=
  canonicalEffectiveMotiveExternalProduct composition X Y

@[simp] theorem canonicalEffectiveMotives_tensorProduct_eq
    (composition : Boundary.CanonicalCompositionData (k := k))
    [Abelian (LinearPST (Boundary.canonicalCategory composition))]
    [HasDerivedCategory (LinearPST (Boundary.canonicalCategory composition))]
    [Abelian (canonicalA1NisLocalization composition)]
    [HasDerivedCategory (canonicalA1NisLocalization composition)]
    [(canonicalA1NisLocalizationFunctor composition).Additive]
    [Limits.PreservesFiniteLimits (canonicalA1NisLocalizationFunctor composition)]
    [Limits.PreservesFiniteColimits (canonicalA1NisLocalizationFunctor composition)]
    (X Y : Geometry.SmSchemeOver k) :
    canonicalEffectiveMotives_tensorProduct composition X Y =
      canonicalEffectiveMotiveExternalProduct composition X Y :=
  rfl

/-- Morphism induced by the graph correspondence of an ordinary smooth
morphism. -/
def canonicalEffectiveMotiveMap
    (composition : Boundary.CanonicalCompositionData (k := k))
    [Abelian (LinearPST (Boundary.canonicalCategory composition))]
    [HasDerivedCategory (LinearPST (Boundary.canonicalCategory composition))]
    [Abelian (canonicalA1NisLocalization composition)]
    [HasDerivedCategory (canonicalA1NisLocalization composition)]
  [(canonicalA1NisLocalizationFunctor composition).Additive]
  [Limits.PreservesFiniteLimits (canonicalA1NisLocalizationFunctor composition)]
  [Limits.PreservesFiniteColimits (canonicalA1NisLocalizationFunctor composition)]
    {X Y : Geometry.SmSchemeOver k}
    (f : Boundary.SmOverHom X Y) :
    canonicalEffectiveMotive composition X ⟶
      canonicalEffectiveMotive composition Y :=
  (canonicalEffectiveMotivesLocalizationFunctor composition).map
    (canonicalRepresentableComplexMap composition f)

/-- The effective-motive map attached to the identity morphism is already the
identity, once transported through the derived object and localization layers. -/
theorem canonicalEffectiveMotiveMap_id
    (composition : Boundary.CanonicalCompositionData (k := k))
    [Abelian (LinearPST (Boundary.canonicalCategory composition))]
    [HasDerivedCategory (LinearPST (Boundary.canonicalCategory composition))]
    [Abelian (canonicalA1NisLocalization composition)]
    [HasDerivedCategory (canonicalA1NisLocalization composition)]
    [(canonicalA1NisLocalizationFunctor composition).Additive]
    [Limits.PreservesFiniteLimits (canonicalA1NisLocalizationFunctor composition)]
    [Limits.PreservesFiniteColimits (canonicalA1NisLocalizationFunctor composition)]
    (X : Geometry.SmSchemeOver k) :
    canonicalEffectiveMotiveMap composition (Boundary.SmOverHom.id X) =
      𝟙 (canonicalEffectiveMotive composition X) := by
  simp [canonicalEffectiveMotiveMap, canonicalEffectiveMotive,
    canonicalRepresentableComplexMap_id]

/-- The effective-motive maps satisfy composition because the localization
functor out of the ambient derived category is functorial. -/
theorem canonicalEffectiveMotiveMap_comp
    (composition : Boundary.CanonicalCompositionData (k := k))
    (hgraph : Geometry.CanonicalGraphPackageCompatibilityObligation composition)
    [Abelian (LinearPST (Boundary.canonicalCategory composition))]
    [HasDerivedCategory (LinearPST (Boundary.canonicalCategory composition))]
    [Abelian (canonicalA1NisLocalization composition)]
    [HasDerivedCategory (canonicalA1NisLocalization composition)]
    [(canonicalA1NisLocalizationFunctor composition).Additive]
    [Limits.PreservesFiniteLimits (canonicalA1NisLocalizationFunctor composition)]
    [Limits.PreservesFiniteColimits (canonicalA1NisLocalizationFunctor composition)]
    {X Y Z : Geometry.SmSchemeOver k}
    (f : Boundary.SmOverHom X Y)
    (g : Boundary.SmOverHom Y Z) :
    canonicalEffectiveMotiveMap composition (Boundary.SmOverHom.comp f g) =
      canonicalEffectiveMotiveMap composition f ≫
        canonicalEffectiveMotiveMap composition g := by
  simp [canonicalEffectiveMotiveMap, canonicalRepresentableComplexMap_comp composition hgraph,
    Functor.map_comp]

/-- The canonical effective motive construction is functorial on smooth
`k`-schemes. -/
def canonicalEffectiveMotiveFunctor
    (composition : Boundary.CanonicalCompositionData (k := k))
    (hgraph : Geometry.CanonicalGraphPackageCompatibilityObligation composition)
    [Abelian (LinearPST (Boundary.canonicalCategory composition))]
    [HasDerivedCategory (LinearPST (Boundary.canonicalCategory composition))]
    [Abelian (canonicalA1NisLocalization composition)]
    [HasDerivedCategory (canonicalA1NisLocalization composition)]
    [(canonicalA1NisLocalizationFunctor composition).Additive]
    [Limits.PreservesFiniteLimits (canonicalA1NisLocalizationFunctor composition)]
    [Limits.PreservesFiniteColimits (canonicalA1NisLocalizationFunctor composition)] :
    Geometry.SmSchemeOver k ⥤ canonicalEffectiveMotives composition where
  obj := canonicalEffectiveMotive composition
  map f := canonicalEffectiveMotiveMap composition f
  map_id X := canonicalEffectiveMotiveMap_id composition X
  map_comp f g := canonicalEffectiveMotiveMap_comp composition hgraph f g

@[simp] theorem canonicalEffectiveMotiveFunctor_obj
    (composition : Boundary.CanonicalCompositionData (k := k))
    (hgraph : Geometry.CanonicalGraphPackageCompatibilityObligation composition)
    [Abelian (LinearPST (Boundary.canonicalCategory composition))]
    [HasDerivedCategory (LinearPST (Boundary.canonicalCategory composition))]
    [Abelian (canonicalA1NisLocalization composition)]
    [HasDerivedCategory (canonicalA1NisLocalization composition)]
    [(canonicalA1NisLocalizationFunctor composition).Additive]
    [Limits.PreservesFiniteLimits (canonicalA1NisLocalizationFunctor composition)]
    [Limits.PreservesFiniteColimits (canonicalA1NisLocalizationFunctor composition)]
    (X : Geometry.SmSchemeOver k) :
    (canonicalEffectiveMotiveFunctor composition hgraph).obj X =
      canonicalEffectiveMotive composition X :=
  rfl

@[simp] theorem canonicalEffectiveMotiveFunctor_map
    (composition : Boundary.CanonicalCompositionData (k := k))
    (hgraph : Geometry.CanonicalGraphPackageCompatibilityObligation composition)
    [Abelian (LinearPST (Boundary.canonicalCategory composition))]
    [HasDerivedCategory (LinearPST (Boundary.canonicalCategory composition))]
    [Abelian (canonicalA1NisLocalization composition)]
    [HasDerivedCategory (canonicalA1NisLocalization composition)]
    [(canonicalA1NisLocalizationFunctor composition).Additive]
    [Limits.PreservesFiniteLimits (canonicalA1NisLocalizationFunctor composition)]
    [Limits.PreservesFiniteColimits (canonicalA1NisLocalizationFunctor composition)]
    {X Y : Geometry.SmSchemeOver k}
    (f : X ⟶ Y) :
    (canonicalEffectiveMotiveFunctor composition hgraph).map f =
      canonicalEffectiveMotiveMap composition f :=
  rfl

/-- Bifunctorial external-product carrier on effective generators, obtained by
feeding the product object in `Sm/k` through the actual canonical effective
motive functor. -/
def canonicalEffectiveMotiveExternalProductFunctor
    (composition : Boundary.CanonicalCompositionData (k := k))
    (hgraph : Geometry.CanonicalGraphPackageCompatibilityObligation composition)
    [Abelian (LinearPST (Boundary.canonicalCategory composition))]
    [HasDerivedCategory (LinearPST (Boundary.canonicalCategory composition))]
    [Abelian (canonicalA1NisLocalization composition)]
    [HasDerivedCategory (canonicalA1NisLocalization composition)]
    [(canonicalA1NisLocalizationFunctor composition).Additive]
    [Limits.PreservesFiniteLimits (canonicalA1NisLocalizationFunctor composition)]
    [Limits.PreservesFiniteColimits (canonicalA1NisLocalizationFunctor composition)] :
    (Geometry.SmSchemeOver k × Geometry.SmSchemeOver k) ⥤
      canonicalEffectiveMotives composition where
  obj XY := canonicalEffectiveMotiveExternalProduct composition XY.1 XY.2
  map fg := canonicalEffectiveMotiveMap composition (overBaseProductMap fg.1 fg.2)
  map_id XY := by
    change canonicalEffectiveMotiveMap composition
      (overBaseProductMap (𝟙 XY.1) (𝟙 XY.2)) =
        𝟙 (canonicalEffectiveMotive composition
          (overBaseProductObject XY.1 XY.2))
    rw [overBaseProductMap_id]
    exact canonicalEffectiveMotiveMap_id composition _
  map_comp fg hg := by
    rcases fg with ⟨f₁, g₁⟩
    rcases hg with ⟨f₂, g₂⟩
    change canonicalEffectiveMotiveMap composition
      (overBaseProductMap (f₁ ≫ f₂) (g₁ ≫ g₂)) =
        canonicalEffectiveMotiveMap composition (overBaseProductMap f₁ g₁) ≫
          canonicalEffectiveMotiveMap composition (overBaseProductMap f₂ g₂)
    rw [overBaseProductMap_comp]
    exact canonicalEffectiveMotiveMap_comp composition hgraph
      (overBaseProductMap f₁ g₁) (overBaseProductMap f₂ g₂)

@[simp] theorem canonicalEffectiveMotiveExternalProductFunctor_obj
    (composition : Boundary.CanonicalCompositionData (k := k))
    (hgraph : Geometry.CanonicalGraphPackageCompatibilityObligation composition)
    [Abelian (LinearPST (Boundary.canonicalCategory composition))]
    [HasDerivedCategory (LinearPST (Boundary.canonicalCategory composition))]
    [Abelian (canonicalA1NisLocalization composition)]
    [HasDerivedCategory (canonicalA1NisLocalization composition)]
    [(canonicalA1NisLocalizationFunctor composition).Additive]
    [Limits.PreservesFiniteLimits (canonicalA1NisLocalizationFunctor composition)]
    [Limits.PreservesFiniteColimits (canonicalA1NisLocalizationFunctor composition)]
    (X Y : Geometry.SmSchemeOver k) :
    (canonicalEffectiveMotiveExternalProductFunctor composition hgraph).obj (X, Y) =
      canonicalEffectiveMotiveExternalProduct composition X Y :=
  rfl

@[simp] theorem canonicalEffectiveMotiveExternalProductFunctor_map
    (composition : Boundary.CanonicalCompositionData (k := k))
    (hgraph : Geometry.CanonicalGraphPackageCompatibilityObligation composition)
    [Abelian (LinearPST (Boundary.canonicalCategory composition))]
    [HasDerivedCategory (LinearPST (Boundary.canonicalCategory composition))]
    [Abelian (canonicalA1NisLocalization composition)]
    [HasDerivedCategory (canonicalA1NisLocalization composition)]
    [(canonicalA1NisLocalizationFunctor composition).Additive]
    [Limits.PreservesFiniteLimits (canonicalA1NisLocalizationFunctor composition)]
    [Limits.PreservesFiniteColimits (canonicalA1NisLocalizationFunctor composition)]
    {X₁ X₂ Y₁ Y₂ : Geometry.SmSchemeOver k}
    (f : X₁ ⟶ X₂) (g : Y₁ ⟶ Y₂) :
    (canonicalEffectiveMotiveExternalProductFunctor composition hgraph).map (f, g) =
      canonicalEffectiveMotiveMap composition (overBaseProductMap f g) :=
  rfl

/-- Associativity of the canonical product carrier on effective motive
generators, induced by the genuine associator of fiber products over the base. -/
noncomputable def canonicalEffectiveMotives_tensor_assoc
    (composition : Boundary.CanonicalCompositionData (k := k))
    (hgraph : Geometry.CanonicalGraphPackageCompatibilityObligation composition)
    [Abelian (LinearPST (Boundary.canonicalCategory composition))]
    [HasDerivedCategory (LinearPST (Boundary.canonicalCategory composition))]
    [Abelian (canonicalA1NisLocalization composition)]
    [HasDerivedCategory (canonicalA1NisLocalization composition)]
    [(canonicalA1NisLocalizationFunctor composition).Additive]
    [Limits.PreservesFiniteLimits (canonicalA1NisLocalizationFunctor composition)]
    [Limits.PreservesFiniteColimits (canonicalA1NisLocalizationFunctor composition)]
    (X Y Z : Geometry.SmSchemeOver k) :
    canonicalEffectiveMotives_tensorProduct composition
        (overBaseProductObject X Y) Z ≅
      canonicalEffectiveMotives_tensorProduct composition
        X (overBaseProductObject Y Z) :=
  (canonicalEffectiveMotiveFunctor composition hgraph).mapIso
    (overBaseProductAssoc X Y Z)

/-- Left unitor for the canonical product carrier on effective motive
generators, induced by the genuine left unitor of fiber products over the
base. -/
noncomputable def canonicalEffectiveMotives_tensor_leftUnitor
    (composition : Boundary.CanonicalCompositionData (k := k))
    (hgraph : Geometry.CanonicalGraphPackageCompatibilityObligation composition)
    [Abelian (LinearPST (Boundary.canonicalCategory composition))]
    [HasDerivedCategory (LinearPST (Boundary.canonicalCategory composition))]
    [Abelian (canonicalA1NisLocalization composition)]
    [HasDerivedCategory (canonicalA1NisLocalization composition)]
    [(canonicalA1NisLocalizationFunctor composition).Additive]
    [Limits.PreservesFiniteLimits (canonicalA1NisLocalizationFunctor composition)]
    [Limits.PreservesFiniteColimits (canonicalA1NisLocalizationFunctor composition)]
    (X : Geometry.SmSchemeOver k) :
    canonicalEffectiveMotives_tensorProduct composition
        (overBaseUnitObject (k := k)) X ≅
      canonicalEffectiveMotive composition X :=
  (canonicalEffectiveMotiveFunctor composition hgraph).mapIso
    (overBaseProductLeftUnitor X)

/-- Right unitor for the canonical product carrier on effective motive
generators, induced by the genuine right unitor of fiber products over the
base. -/
noncomputable def canonicalEffectiveMotives_tensor_rightUnitor
    (composition : Boundary.CanonicalCompositionData (k := k))
    (hgraph : Geometry.CanonicalGraphPackageCompatibilityObligation composition)
    [Abelian (LinearPST (Boundary.canonicalCategory composition))]
    [HasDerivedCategory (LinearPST (Boundary.canonicalCategory composition))]
    [Abelian (canonicalA1NisLocalization composition)]
    [HasDerivedCategory (canonicalA1NisLocalization composition)]
    [(canonicalA1NisLocalizationFunctor composition).Additive]
    [Limits.PreservesFiniteLimits (canonicalA1NisLocalizationFunctor composition)]
    [Limits.PreservesFiniteColimits (canonicalA1NisLocalizationFunctor composition)]
    (X : Geometry.SmSchemeOver k) :
    canonicalEffectiveMotives_tensorProduct composition
        X (overBaseUnitObject (k := k)) ≅
      canonicalEffectiveMotive composition X :=
  (canonicalEffectiveMotiveFunctor composition hgraph).mapIso
    (overBaseProductRightUnitor X)

/-- Canonical generator-level tensor geometry on effective motives.

This packages the already-constructed bifunctorial product carrier together
with its associator and unitors. It is an honest owner surface: every field is
constructed concretely in this file from the genuine product geometry of
smooth schemes and the functorial effective motive construction. -/
structure CanonicalEffectiveMotivesTensorGeometry where
  tensor :
    (Geometry.SmSchemeOver k × Geometry.SmSchemeOver k) ⥤
      canonicalEffectiveMotives composition
  assoc :
    ∀ (X Y Z : Geometry.SmSchemeOver k),
      tensor.obj (overBaseProductObject X Y, Z) ≅
        tensor.obj (X, overBaseProductObject Y Z)
  leftUnitor :
    ∀ (X : Geometry.SmSchemeOver k),
      tensor.obj (overBaseUnitObject (k := k), X) ≅
        canonicalEffectiveMotive composition X
  rightUnitor :
    ∀ (X : Geometry.SmSchemeOver k),
      tensor.obj (X, overBaseUnitObject (k := k)) ≅
        canonicalEffectiveMotive composition X

/-- The canonical generator-level tensor geometry carried by effective motives,
assembled from the external-product bifunctor on generators and the genuine
fiber-product coherence isomorphisms. -/
noncomputable def canonicalEffectiveMotives_tensorGeometry
    (composition : Boundary.CanonicalCompositionData (k := k))
    (hgraph : Geometry.CanonicalGraphPackageCompatibilityObligation composition)
    [Abelian (LinearPST (Boundary.canonicalCategory composition))]
    [HasDerivedCategory (LinearPST (Boundary.canonicalCategory composition))]
    [Abelian (canonicalA1NisLocalization composition)]
    [HasDerivedCategory (canonicalA1NisLocalization composition)]
    [(canonicalA1NisLocalizationFunctor composition).Additive]
    [Limits.PreservesFiniteLimits (canonicalA1NisLocalizationFunctor composition)]
    [Limits.PreservesFiniteColimits (canonicalA1NisLocalizationFunctor composition)] :
    CanonicalEffectiveMotivesTensorGeometry (composition := composition) where
  tensor := canonicalEffectiveMotiveExternalProductFunctor composition hgraph
  assoc := canonicalEffectiveMotives_tensor_assoc composition hgraph
  leftUnitor := canonicalEffectiveMotives_tensor_leftUnitor composition hgraph
  rightUnitor := canonicalEffectiveMotives_tensor_rightUnitor composition hgraph

@[simp] theorem canonicalEffectiveMotives_tensorGeometry_tensor_obj
    (composition : Boundary.CanonicalCompositionData (k := k))
    (hgraph : Geometry.CanonicalGraphPackageCompatibilityObligation composition)
    [Abelian (LinearPST (Boundary.canonicalCategory composition))]
    [HasDerivedCategory (LinearPST (Boundary.canonicalCategory composition))]
    [Abelian (canonicalA1NisLocalization composition)]
    [HasDerivedCategory (canonicalA1NisLocalization composition)]
    [(canonicalA1NisLocalizationFunctor composition).Additive]
    [Limits.PreservesFiniteLimits (canonicalA1NisLocalizationFunctor composition)]
    [Limits.PreservesFiniteColimits (canonicalA1NisLocalizationFunctor composition)]
    (X Y : Geometry.SmSchemeOver k) :
    (canonicalEffectiveMotives_tensorGeometry
      (composition := composition) hgraph).tensor.obj (X, Y) =
      canonicalEffectiveMotiveExternalProduct composition X Y :=
  rfl

@[simp] theorem canonicalEffectiveMotives_tensorGeometry_assoc
    (composition : Boundary.CanonicalCompositionData (k := k))
    (hgraph : Geometry.CanonicalGraphPackageCompatibilityObligation composition)
    [Abelian (LinearPST (Boundary.canonicalCategory composition))]
    [HasDerivedCategory (LinearPST (Boundary.canonicalCategory composition))]
    [Abelian (canonicalA1NisLocalization composition)]
    [HasDerivedCategory (canonicalA1NisLocalization composition)]
    [(canonicalA1NisLocalizationFunctor composition).Additive]
    [Limits.PreservesFiniteLimits (canonicalA1NisLocalizationFunctor composition)]
    [Limits.PreservesFiniteColimits (canonicalA1NisLocalizationFunctor composition)]
    (X Y Z : Geometry.SmSchemeOver k) :
    (canonicalEffectiveMotives_tensorGeometry
      (composition := composition) hgraph).assoc X Y Z =
      canonicalEffectiveMotives_tensor_assoc composition hgraph X Y Z :=
  rfl

@[simp] theorem canonicalEffectiveMotives_tensorGeometry_leftUnitor
    (composition : Boundary.CanonicalCompositionData (k := k))
    (hgraph : Geometry.CanonicalGraphPackageCompatibilityObligation composition)
    [Abelian (LinearPST (Boundary.canonicalCategory composition))]
    [HasDerivedCategory (LinearPST (Boundary.canonicalCategory composition))]
    [Abelian (canonicalA1NisLocalization composition)]
    [HasDerivedCategory (canonicalA1NisLocalization composition)]
    [(canonicalA1NisLocalizationFunctor composition).Additive]
    [Limits.PreservesFiniteLimits (canonicalA1NisLocalizationFunctor composition)]
    [Limits.PreservesFiniteColimits (canonicalA1NisLocalizationFunctor composition)]
    (X : Geometry.SmSchemeOver k) :
    (canonicalEffectiveMotives_tensorGeometry
      (composition := composition) hgraph).leftUnitor X =
      canonicalEffectiveMotives_tensor_leftUnitor composition hgraph X :=
  rfl

@[simp] theorem canonicalEffectiveMotives_tensorGeometry_rightUnitor
    (composition : Boundary.CanonicalCompositionData (k := k))
    (hgraph : Geometry.CanonicalGraphPackageCompatibilityObligation composition)
    [Abelian (LinearPST (Boundary.canonicalCategory composition))]
    [HasDerivedCategory (LinearPST (Boundary.canonicalCategory composition))]
    [Abelian (canonicalA1NisLocalization composition)]
    [HasDerivedCategory (canonicalA1NisLocalization composition)]
    [(canonicalA1NisLocalizationFunctor composition).Additive]
    [Limits.PreservesFiniteLimits (canonicalA1NisLocalizationFunctor composition)]
    [Limits.PreservesFiniteColimits (canonicalA1NisLocalizationFunctor composition)]
    (X : Geometry.SmSchemeOver k) :
    (canonicalEffectiveMotives_tensorGeometry
      (composition := composition) hgraph).rightUnitor X =
      canonicalEffectiveMotives_tensor_rightUnitor composition hgraph X :=
  rfl

end

end Boundary
