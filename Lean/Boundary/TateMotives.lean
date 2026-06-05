import Boundary.EffectiveMotiveFunctor
import Boundary.GeometricEffectiveMotives
import Boundary.ProjectiveLineGeometry
import Mathlib.AlgebraicGeometry.Spec
import Mathlib.CategoryTheory.Triangulated.Basic

/-!
# Canonical Tate-motive construction surface

This file starts the Tate slice above canonical effective and geometric
effective motives.

What is genuinely available on current owner surfaces:
- the unit object `M(Spec k)` can be defined concretely;
- the Boundary-side `P¹` owner object and its canonical basepoint are already
  constructed in `ProjectiveLineGeometry.lean`;
- this immediately determines the effective motive `M(P¹)` and the map from
  the unit motive.

Tensor-descent proof chain for the canonical Tate action:

1. `ExternalProduct.lean` constructs the bilinear external product on finite
   correspondences.
2. `A1Geometry.lean` identifies the canonical `A1` and Nisnevich generators as
   local equivalences, so tensor descent must show their external products are
   again inverted by the canonical localization.
3. The universal property of `canonicalEffectiveMotives` then descends the
   external product to a monoidal action on effective motives.
4. Right tensoring with the Tate object built here yields the Tate twist.

Tate-stabilization proof chain for the canonical object:

1. `ProjectiveLineGeometry.lean` constructs the honest `P¹_k` object and its
   canonical basepoint `Spec k → P¹_k`.
2. `EffectiveMotiveFunctor.lean` sends this to the actual motive map
   `M(Spec k) ⟶ M(P¹)`.
3. The pretriangulated structure on effective motives supplies a distinguished
   cone triangle for that map.
4. The Tate object is defined as the `(-2)`-shift of the cone, so
   `(Q(1)[2])[2] ≅ cone(M(Spec k) ⟶ M(P¹))`.

Accordingly, this file defines the unit motive concretely, constructs the
canonical Boundary Tate datum from the distinguished triangle on
`M(Spec k) ⟶ M(P¹)`, and isolates the remaining Tate-twist data.
-/

universe u

open AlgebraicGeometry CategoryTheory

namespace Boundary

noncomputable section

variable {k : Type u} [Field k] [PerfectField k]

variable (composition : Boundary.CanonicalCompositionData (k := k))
variable [Abelian (LinearPST (Boundary.canonicalCategory composition))]
variable [HasDerivedCategory (LinearPST (Boundary.canonicalCategory composition))]
variable [Abelian (canonicalA1NisLocalization composition)]
variable [HasDerivedCategory (canonicalA1NisLocalization composition)]
variable [(canonicalA1NisLocalizationFunctor composition).Additive]
variable [Limits.PreservesFiniteLimits (canonicalA1NisLocalizationFunctor composition)]
variable [Limits.PreservesFiniteColimits (canonicalA1NisLocalizationFunctor composition)]

/-- The base point `Spec k`, regarded as an object of `Sm/k`. -/
def canonicalUnitScheme : Geometry.SmSchemeOver k where
  scheme := Spec (CommRingCat.of k)
  structMap := 𝟙 _
  smooth := by
    infer_instance
  separated := by
    infer_instance
  finiteType := by
    constructor <;> infer_instance

/-- The canonical unit motive `M(Spec k)` in effective motives. -/
def canonicalUnitMotive : canonicalEffectiveMotives composition :=
  canonicalEffectiveMotive composition (canonicalUnitScheme (k := k))

/-- The canonical unit motive, viewed inside the geometric effective full
subcategory. -/
def canonicalUnitGeometricMotiveObject :
    canonicalGeometricEffectiveMotives composition :=
  canonicalGeometricEffectiveMotiveObject composition (canonicalUnitScheme (k := k))

/-- Generic Boundary-side input surface for speaking concretely about a
projective-line motive. The canonical Boundary `P¹` object and basepoint are
constructed below by instantiating this package with the resolved owner data
from `ProjectiveLineGeometry.lean`. -/
structure CanonicalProjectiveLineMotiveConstructionData
    (composition : Boundary.CanonicalCompositionData (k := k)) where
  projectiveLineScheme : Geometry.SmSchemeOver k
  unitToProjectiveLine :
    Boundary.SmOverHom (canonicalUnitScheme (k := k)) projectiveLineScheme

/-- The effective motive attached to the projective-line object in `Sm/k`. -/
def canonicalProjectiveLineMotive
  (data : CanonicalProjectiveLineMotiveConstructionData composition) :
    canonicalEffectiveMotives composition :=
  canonicalEffectiveMotive composition data.projectiveLineScheme

/-- The canonical map `M(Spec k) ⟶ M(P¹)` attached to the chosen base-point
inclusion, once the actual projective-line geometry has been supplied. -/
def canonicalUnitToProjectiveLineMotive
  (data : CanonicalProjectiveLineMotiveConstructionData composition) :
    canonicalUnitMotive composition ⟶ canonicalProjectiveLineMotive composition data :=
  canonicalEffectiveMotiveMap composition data.unitToProjectiveLine

/-- The projective-line motive lies in the geometric effective subcategory as
soon as the underlying `Sm/k` object is available. -/
def canonicalProjectiveLineGeometricMotiveObject
  (data : CanonicalProjectiveLineMotiveConstructionData composition) :
    canonicalGeometricEffectiveMotives composition :=
  canonicalGeometricEffectiveMotiveObject composition data.projectiveLineScheme

/-- Construction data for the reduced projective-line motive and the effective
Tate object, with laws recording their cone and shift relations. -/
structure CanonicalTateObjectConstructionData
  (p1Data : CanonicalProjectiveLineMotiveConstructionData composition) where
  reducedProjectiveLineMotive : canonicalEffectiveMotives composition
  tateObject : canonicalEffectiveMotives composition
  reducedProjectiveLine_isCone :
    ∃ (projectiveLineToReduced :
          canonicalProjectiveLineMotive composition p1Data ⟶ reducedProjectiveLineMotive)
        (reducedToShiftedUnit :
          reducedProjectiveLineMotive ⟶
            (shiftFunctor (canonicalEffectiveMotives composition) (1 : ℤ)).obj
              (canonicalUnitMotive composition)),
      ({ obj₁ := canonicalUnitMotive composition
         obj₂ := canonicalProjectiveLineMotive composition p1Data
         obj₃ := reducedProjectiveLineMotive
         mor₁ := canonicalUnitToProjectiveLineMotive composition p1Data
         mor₂ := projectiveLineToReduced
         mor₃ := reducedToShiftedUnit } :
          CategoryTheory.Pretriangulated.Triangle
            (canonicalEffectiveMotives composition)) ∈
        distTriang (canonicalEffectiveMotives composition)
  tateObject_shifted_iso_reducedProjectiveLine :
    Nonempty
      (((shiftFunctor (canonicalEffectiveMotives composition) (2 : ℤ)).obj tateObject) ≅
        reducedProjectiveLineMotive)

/-- Construction data for a Tate twist functor once a first-class
tensor/inversion API is in place. The `Prop` fields record laws about the
supplied functor. -/
structure CanonicalTateTwistFunctorConstructionData
    (p1Data : CanonicalProjectiveLineMotiveConstructionData composition)
    (tateData : CanonicalTateObjectConstructionData composition p1Data) where
  functor : canonicalEffectiveMotives composition ⥤ canonicalEffectiveMotives composition
  unitMotiveMapsToTateObject :
    Nonempty (functor.obj (canonicalUnitMotive composition) ≅ tateData.tateObject)
  preservesGeometricMotives :
    ∀ X : canonicalGeometricEffectiveMotives composition,
      (canonicalGeometricEffectiveThickSubcategory composition).P (functor.obj X.1)

/-- Concrete projective-line motive construction data coming from the now fully
constructed Boundary owner surface for `P¹_k`. This packages the honest smooth
projective line object together with its canonical basepoint map from `Spec k`.
-/
abbrev boundaryProjectiveLineMotiveConstructionData :
    CanonicalProjectiveLineMotiveConstructionData composition where
  projectiveLineScheme :=
    boundaryProjectiveLineConcreteObject (k := k)
  unitToProjectiveLine :=
    boundaryProjectiveLineCanonicalBasepoint
      (k := k)
      (boundaryProjectiveLineSmooth (k := k))
      (boundaryProjectiveLineFiniteType (k := k))

/-- The effective motive of the concrete canonical Boundary-side projective line. -/
abbrev boundaryProjectiveLineMotive : canonicalEffectiveMotives composition :=
  canonicalProjectiveLineMotive composition
    (boundaryProjectiveLineMotiveConstructionData (composition := composition))

/-- The unit-to-`P¹` motive map attached to the canonical Boundary-side basepoint. -/
abbrev boundaryUnitToProjectiveLineMotive :
    canonicalUnitMotive composition ⟶ boundaryProjectiveLineMotive composition :=
  canonicalUnitToProjectiveLineMotive composition
    (boundaryProjectiveLineMotiveConstructionData (composition := composition))

/-- The concrete Boundary-side projective-line motive lies in the geometric
effective subcategory immediately after packaging the canonical owner object. -/
abbrev boundaryProjectiveLineGeometricMotiveObject :
    canonicalGeometricEffectiveMotives composition :=
  canonicalProjectiveLineGeometricMotiveObject composition
    (boundaryProjectiveLineMotiveConstructionData (composition := composition))

/-- The Tate-object construction problem specialized to the concrete canonical
Boundary projective line. This is the exact stabilization seam now exposed by
the resolved `P¹` owner surface. -/
abbrev BoundaryTateObjectConstructionData :=
  CanonicalTateObjectConstructionData composition
    (boundaryProjectiveLineMotiveConstructionData (composition := composition))

/-- Canonical Boundary Tate datum obtained by choosing a distinguished triangle
for the actual motive map `M(Spec k) ⟶ M(P¹)` and defining the Tate object as
the `(-2)`-shift of the reduced projective-line motive. -/
def boundaryCanonicalTateObjectConstructionData :
    BoundaryTateObjectConstructionData composition := by
  let f := boundaryUnitToProjectiveLineMotive (composition := composition)
  let triangleExists := Pretriangulated.distinguished_cocone_triangle f
  let Z := Classical.choose triangleExists
  let gExists := Classical.choose_spec triangleExists
  let g := Classical.choose gExists
  let hExists := Classical.choose_spec gExists
  let h := Classical.choose hExists
  let hTriangle := Classical.choose_spec hExists
  refine
    { reducedProjectiveLineMotive := Z
      tateObject := (shiftFunctor (canonicalEffectiveMotives composition) (-2 : ℤ)).obj Z
      reducedProjectiveLine_isCone := ⟨g, h, hTriangle⟩
      tateObject_shifted_iso_reducedProjectiveLine := ?_ }
  refine ⟨?_⟩
  simpa using
    (shiftFunctorCompIsoId (canonicalEffectiveMotives composition) (-2 : ℤ) (2 : ℤ)
      (by norm_num)).app Z

/-- The canonical reduced projective-line motive, defined as the cone object in
the distinguished triangle of `M(Spec k) ⟶ M(P¹)`. -/
abbrev boundaryReducedProjectiveLineMotive :
    canonicalEffectiveMotives composition :=
  (boundaryCanonicalTateObjectConstructionData
    (composition := composition)).reducedProjectiveLineMotive

/-- The canonical effective Tate object obtained as the `(-2)`-shift of the
reduced projective-line motive. -/
abbrev boundaryEffectiveTateObject :
    canonicalEffectiveMotives composition :=
  (boundaryCanonicalTateObjectConstructionData
    (composition := composition)).tateObject

/-- The canonical cone data proving that the reduced projective-line motive is
the cone of `M(Spec k) ⟶ M(P¹)`. -/
theorem boundaryReducedProjectiveLineMotive_isCone :
    ∃ (projectiveLineToReduced :
          boundaryProjectiveLineMotive (composition := composition) ⟶
            boundaryReducedProjectiveLineMotive (composition := composition))
        (reducedToShiftedUnit :
          boundaryReducedProjectiveLineMotive (composition := composition) ⟶
            (shiftFunctor (canonicalEffectiveMotives composition) (1 : ℤ)).obj
              (canonicalUnitMotive composition)),
      ({ obj₁ := canonicalUnitMotive composition
         obj₂ := boundaryProjectiveLineMotive (composition := composition)
         obj₃ := boundaryReducedProjectiveLineMotive (composition := composition)
         mor₁ := boundaryUnitToProjectiveLineMotive (composition := composition)
         mor₂ := projectiveLineToReduced
         mor₃ := reducedToShiftedUnit } :
          CategoryTheory.Pretriangulated.Triangle
            (canonicalEffectiveMotives composition)) ∈
        distTriang (canonicalEffectiveMotives composition) :=
  (boundaryCanonicalTateObjectConstructionData
    (composition := composition)).reducedProjectiveLine_isCone

/-- Shifting the canonical effective Tate object by `2` recovers the reduced
projective-line motive. -/
theorem boundaryEffectiveTateObject_shifted_iso_reducedProjectiveLine :
    Nonempty
      (((shiftFunctor (canonicalEffectiveMotives composition) (2 : ℤ)).obj
          (boundaryEffectiveTateObject (composition := composition))) ≅
        boundaryReducedProjectiveLineMotive (composition := composition)) :=
  (boundaryCanonicalTateObjectConstructionData
    (composition := composition)).tateObject_shifted_iso_reducedProjectiveLine

/-- The Tate-twist functor construction problem specialized to the concrete
Boundary projective line and its associated Tate-object data. -/
abbrev BoundaryTateTwistFunctorConstructionData
    (tateData : BoundaryTateObjectConstructionData composition) :=
  CanonicalTateTwistFunctorConstructionData composition
    (boundaryProjectiveLineMotiveConstructionData (composition := composition))
    tateData

end

end Boundary
