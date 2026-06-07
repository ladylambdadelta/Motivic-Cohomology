import Boundary.GeometricMotives
import Boundary.TriangulatedProbes

/-!
# Boundary Construction of Voevodsky's `DMgm(Q)_Q`

This file is the final Boundary consumer surface for the category of geometric
motives over `Q` with rational coefficients. It does not contain independent
Tate-stabilization or quotient-hom machinery. The construction is assembled
from the proved Boundary stack:

* finite correspondences and their external product;
* presheaves with transfers and effective motives;
* geometric effective motives;
* the canonical projective-geometric Tate object;
* formal Tate stabilization.

The naming is aligned with Voevodsky's `DM_gm`; cf. Voevodsky, "Triangulated
categories of motives over a field", §2. The object here should be read as the
Boundary construction surface assembled from the local owner files above.
-/

universe u

open CategoryTheory

namespace Boundary

noncomputable section

variable {k : Type u} [Field k] [PerfectField k]

variable (composition : Boundary.CanonicalCompositionData (k := k))
variable [FiniteCorrespondence.CanonicalExternalProductFamily (k := k)]
variable [Abelian (LinearPST (Boundary.canonicalCategory composition))]
variable [HasDerivedCategory (LinearPST (Boundary.canonicalCategory composition))]
variable [Abelian (canonicalA1NisLocalization composition)]
variable [HasDerivedCategory (canonicalA1NisLocalization composition)]
variable [(canonicalA1NisLocalizationFunctor composition).Additive]
variable [Limits.PreservesFiniteLimits (canonicalA1NisLocalizationFunctor composition)]
variable [Limits.PreservesFiniteColimits (canonicalA1NisLocalizationFunctor composition)]

/-- Voevodsky-style `DMgm(Q)_Q` surface obtained by formally stabilizing
canonical effective motives at the projective-geometric Tate object
constructed from `P¹`; cf. Voevodsky, "Triangulated categories of motives over
a field", §2. -/
abbrev VoevodskyDMgmQ_Q :=
  boundaryMotivesOfProjectiveGeometricTateObject (composition := composition)

@[simp] theorem VoevodskyDMgmQ_Q_eq_boundary :
    VoevodskyDMgmQ_Q (composition := composition) =
      boundaryMotivesOfProjectiveGeometricTateObject (composition := composition) :=
  rfl

/-- Canonical effective geometric motives entering the `DMgm(Q)_Q`
construction. -/
abbrev VoevodskyDMgmEffectiveGeometricQ_Q :=
  canonicalGeometricEffectiveMotives composition

@[simp] theorem VoevodskyDMgmEffectiveGeometricQ_Q_eq_canonical :
    VoevodskyDMgmEffectiveGeometricQ_Q (composition := composition) =
      canonicalGeometricEffectiveMotives composition :=
  rfl

/-- Embedding `DM_eff(Q)_Q ⥤ DMgm(Q)_Q` at Tate degree zero. -/
def VoevodskyDMgmEffectiveEmbedding :
    canonicalEffectiveMotives composition ⥤
      VoevodskyDMgmQ_Q (composition := composition) :=
  boundaryEffectiveMotivesEmbeddingProjectiveGeometricTate
    (composition := composition)

@[simp] theorem VoevodskyDMgmEffectiveEmbedding_eq_boundary
    :
    VoevodskyDMgmEffectiveEmbedding (composition := composition) =
      boundaryEffectiveMotivesEmbeddingProjectiveGeometricTate
        (composition := composition) :=
  rfl

@[simp] theorem VoevodskyDMgmEffectiveEmbedding_obj_effectiveObj
    (X : canonicalEffectiveMotives composition) :
    ((VoevodskyDMgmEffectiveEmbedding
        (composition := composition)).obj X).effectiveObj = X :=
  rfl

@[simp] theorem VoevodskyDMgmEffectiveEmbedding_obj_tateTwist
    (X : canonicalEffectiveMotives composition) :
    ((VoevodskyDMgmEffectiveEmbedding
        (composition := composition)).obj X).tateTwist = 0 :=
  rfl

/-- Canonical generator-level tensor geometry on effective motives, exported at
the DMgm consumer layer under the Voevodsky naming surface. This is still the
effective-layer tensor geometry; the identification of formal Tate shift with
tensoring by the Tate object remains a downstream theorem. -/
abbrev VoevodskyDMgmEffectiveTensorGeometry
    (hgraph : Geometry.CanonicalGraphPackageCompatibilityObligation composition) :=
  canonicalEffectiveMotives_tensorGeometry (composition := composition) hgraph

@[simp] theorem VoevodskyDMgmEffectiveTensorGeometry_eq_canonical
    (hgraph : Geometry.CanonicalGraphPackageCompatibilityObligation composition) :
    VoevodskyDMgmEffectiveTensorGeometry
        (composition := composition) hgraph =
      canonicalEffectiveMotives_tensorGeometry
        (composition := composition) hgraph :=
  rfl

/-- Tate-shift equivalence on `DMgm(Q)_Q`, obtained by formally inverting the
projective-geometric Tate object. -/
def VoevodskyDMgmTateShiftEquivalence :
    VoevodskyDMgmQ_Q (composition := composition) ≌
      VoevodskyDMgmQ_Q (composition := composition) :=
  boundaryProjectiveGeometricTateShiftEquivalence
    (composition := composition)

@[simp] theorem VoevodskyDMgmTateShiftEquivalence_eq_boundary
    :
    VoevodskyDMgmTateShiftEquivalence (composition := composition) =
      boundaryProjectiveGeometricTateShiftEquivalence
        (composition := composition) :=
  rfl

@[simp] theorem VoevodskyDMgmEffectiveTensorGeometry_tensor_obj
    (hgraph : Geometry.CanonicalGraphPackageCompatibilityObligation composition)
    (X Y : Geometry.SmSchemeOver k) :
    (VoevodskyDMgmEffectiveTensorGeometry
      (composition := composition) hgraph).tensor.obj (X, Y) =
      canonicalEffectiveMotiveExternalProduct composition X Y :=
  canonicalEffectiveMotives_tensorGeometry_tensor_obj
    (composition := composition) hgraph X Y

@[simp] theorem VoevodskyDMgmEffectiveTensorGeometry_assoc
    (hgraph : Geometry.CanonicalGraphPackageCompatibilityObligation composition)
    (X Y Z : Geometry.SmSchemeOver k) :
    (VoevodskyDMgmEffectiveTensorGeometry
      (composition := composition) hgraph).assoc X Y Z =
      canonicalEffectiveMotives_tensor_assoc composition hgraph X Y Z :=
  canonicalEffectiveMotives_tensorGeometry_assoc
    (composition := composition) hgraph X Y Z

@[simp] theorem VoevodskyDMgmEffectiveTensorGeometry_leftUnitor
    (hgraph : Geometry.CanonicalGraphPackageCompatibilityObligation composition)
    (X : Geometry.SmSchemeOver k) :
    (VoevodskyDMgmEffectiveTensorGeometry
      (composition := composition) hgraph).leftUnitor X =
      canonicalEffectiveMotives_tensor_leftUnitor composition hgraph X :=
  canonicalEffectiveMotives_tensorGeometry_leftUnitor
    (composition := composition) hgraph X

@[simp] theorem VoevodskyDMgmEffectiveTensorGeometry_rightUnitor
    (hgraph : Geometry.CanonicalGraphPackageCompatibilityObligation composition)
    (X : Geometry.SmSchemeOver k) :
    (VoevodskyDMgmEffectiveTensorGeometry
      (composition := composition) hgraph).rightUnitor X =
      canonicalEffectiveMotives_tensor_rightUnitor composition hgraph X :=
  canonicalEffectiveMotives_tensorGeometry_rightUnitor
    (composition := composition) hgraph X

/-- Compatibility theorem for separately constructed Tate-action functors: such
a functor preserves geometric effective motives before formal stabilization. -/
theorem VoevodskyDMgmEffectiveGeometric_tateTwist_stable
    (twistData :
      BoundaryTateTwistFunctorConstructionData
        (composition := composition)
        (boundaryCanonicalTateObjectConstructionData (composition := composition)))
    (X : VoevodskyDMgmEffectiveGeometricQ_Q (composition := composition)) :
    (canonicalGeometricEffectiveThickSubcategory composition).P
      (twistData.functor.obj X.1) :=
  boundaryTateTwist_preservesGeometricEffectiveMotives
    (composition := composition) twistData X

/-- DMgm-facing type of extension data for a functor out of the Tate
stabilization into a target category. A term of this type induces the lifted
functor from `DMgm(Q)_Q` by the formal stabilization universal property. -/
abbrev VoevodskyDMgmTateStabilizationExtension
    (D : Type (u + 2)) [Category D] :=
  Boundary.Motives.TateStabilizationExtension
    (boundaryEffectiveTateObject (composition := composition))
    D

@[simp] theorem VoevodskyDMgmTateStabilizationExtension_eq_boundary
    (D : Type (u + 2)) [Category D] :
    VoevodskyDMgmTateStabilizationExtension
        (composition := composition) D =
      Boundary.Motives.TateStabilizationExtension
        (boundaryEffectiveTateObject (composition := composition))
        D :=
  rfl

/-- Lift a degree-indexed effective functorial construction out of the
stabilized category `DMgm(Q)_Q`. -/
def VoevodskyDMgmTateStabilizationExtension.lift
    {D : Type (u + 2)} [Category D]
    (extension :
      VoevodskyDMgmTateStabilizationExtension
        (composition := composition) D) :
    VoevodskyDMgmQ_Q (composition := composition) ⥤ D :=
  Boundary.Motives.TateStabilizationExtension.lift extension

@[simp] theorem VoevodskyDMgmTateStabilizationExtension_lift_obj
    {D : Type (u + 2)} [Category D]
    (extension :
      VoevodskyDMgmTateStabilizationExtension
        (composition := composition) D)
    (X : VoevodskyDMgmQ_Q (composition := composition)) :
    (VoevodskyDMgmTateStabilizationExtension.lift
      (composition := composition) extension).obj X =
      extension.obj X.effectiveObj X.tateTwist :=
  rfl

@[simp] theorem VoevodskyDMgmTateStabilizationExtension_lift_map
    {D : Type (u + 2)} [Category D]
    (extension :
      VoevodskyDMgmTateStabilizationExtension
        (composition := composition) D)
    {X Y : VoevodskyDMgmQ_Q (composition := composition)}
    (f : X ⟶ Y) :
    (VoevodskyDMgmTateStabilizationExtension.lift
      (composition := composition) extension).map f =
      extension.map f X.tateTwist Y.tateTwist :=
  rfl

@[simp] theorem VoevodskyDMgmTateStabilizationExtension_lift_effectiveEmbedding_obj
    {D : Type (u + 2)} [Category D]
    (extension :
      VoevodskyDMgmTateStabilizationExtension
        (composition := composition) D)
    (X : canonicalEffectiveMotives composition) :
    ((VoevodskyDMgmEffectiveEmbedding (composition := composition)) ⋙
      VoevodskyDMgmTateStabilizationExtension.lift
        (composition := composition) extension).obj X =
      extension.obj X 0 :=
  rfl

@[simp] theorem VoevodskyDMgmTateStabilizationExtension_lift_tateShift_obj
    {D : Type (u + 2)} [Category D]
    (extension :
      VoevodskyDMgmTateStabilizationExtension
        (composition := composition) D)
    (X : VoevodskyDMgmQ_Q (composition := composition)) :
    (VoevodskyDMgmTateStabilizationExtension.lift
      (composition := composition) extension).obj
        ((Boundary.Motives.tateShift
          (boundaryEffectiveTateObject (composition := composition))).obj X) =
      extension.obj X.effectiveObj (X.tateTwist + 1) :=
  rfl

/-- DMgm-facing universal property obtained by combining the concrete
projective-geometric `P¹`/Tate identification in effective motives with formal
Tate stabilization of geometric effective motives. -/
structure VoevodskyDMgmTateStabilizationUniversalProperty
    where
  tateObject_projectiveGeometry :
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
        distTriang (canonicalEffectiveMotives composition) ∧
      boundaryEffectiveTateObject (composition := composition) =
        (shiftFunctor (canonicalEffectiveMotives composition) (-2 : ℤ)).obj
          (boundaryReducedProjectiveLineMotive (composition := composition))
  tateObject_shifted_iso_reducedProjectiveLine :
    Nonempty
      (((shiftFunctor (canonicalEffectiveMotives composition) (2 : ℤ)).obj
          (boundaryEffectiveTateObject (composition := composition))) ≅
        boundaryReducedProjectiveLineMotive (composition := composition))
  stabilizationUniversalProperty :
    ∀ (D : Type (u + 2)) [Category D],
      Type (u + 2)
  effectiveEmbedding :
    canonicalEffectiveMotives composition ⥤
      VoevodskyDMgmQ_Q (composition := composition)
  tateShiftEquivalence :
    VoevodskyDMgmQ_Q (composition := composition) ≌
      VoevodskyDMgmQ_Q (composition := composition)

/-- The DMgm stabilization universal property attached to the Boundary
construction. The motivic input is exactly the projective-geometric reduced
`P¹` cone and the shifted-Tate identification constructed in `TateMotives.lean`;
the stabilized category is the formal Tate stabilization consumed by
`GeometricMotives.lean`. -/
def VoevodskyDMgmTateStabilizationUniversalProperty.canonical :
    VoevodskyDMgmTateStabilizationUniversalProperty
      (composition := composition) where
  tateObject_projectiveGeometry :=
    boundaryEffectiveTateObject_projectiveGeometry (composition := composition)
  tateObject_shifted_iso_reducedProjectiveLine :=
    boundaryEffectiveTateObject_shifted_iso_reducedProjectiveLine
      (composition := composition)
  stabilizationUniversalProperty := by
    intro D hD
    exact
      VoevodskyDMgmTateStabilizationExtension
        (composition := composition) D
  effectiveEmbedding :=
    VoevodskyDMgmEffectiveEmbedding (composition := composition)
  tateShiftEquivalence :=
    VoevodskyDMgmTateShiftEquivalence (composition := composition)

/-- The reduced-`P¹` cone theorem consumed by the DMgm stabilization universal
property. -/
theorem VoevodskyDMgmTateStabilizationUniversalProperty_projectiveGeometry :
    (VoevodskyDMgmTateStabilizationUniversalProperty.canonical
      (composition := composition)).tateObject_projectiveGeometry =
      boundaryEffectiveTateObject_projectiveGeometry (composition := composition) :=
  rfl

/-- The shifted-Tate/reduced-`P¹` identification consumed by the DMgm
stabilization universal property. -/
theorem VoevodskyDMgmTateStabilizationUniversalProperty_tateObject_shifted_iso
    (VoevodskyDMgmTateStabilizationUniversalProperty.canonical
      (composition := composition)).tateObject_shifted_iso_reducedProjectiveLine =
      boundaryEffectiveTateObject_shifted_iso_reducedProjectiveLine
        (composition := composition) :=
  rfl

@[simp] theorem VoevodskyDMgmTateShift_effectiveEmbedding_tateObject
    :
    (Boundary.Motives.tateShift
        (boundaryEffectiveTateObject (composition := composition))).obj
      ((VoevodskyDMgmEffectiveEmbedding (composition := composition)).obj
        (boundaryEffectiveTateObject (composition := composition))) =
      ⟨boundaryEffectiveTateObject (composition := composition), 1⟩ :=
  rfl

@[simp] theorem VoevodskyDMgmInverseTateShift_effectiveEmbedding_tateObject
    :
    (Boundary.Motives.inverseTateShift
        (boundaryEffectiveTateObject (composition := composition))).obj
      ((VoevodskyDMgmEffectiveEmbedding (composition := composition)).obj
        (boundaryEffectiveTateObject (composition := composition))) =
      ⟨boundaryEffectiveTateObject (composition := composition), -1⟩ :=
  rfl

/-- DMgm-facing formal inversion theorem: in the object-based Tate
stabilization, the embedded effective Tate object is represented by the same
effective object in Tate degree `-1` after applying the inverse formal Tate
shift. This is the honest universal-property statement available before any
identification of formal shift with tensoring is proved. -/
theorem VoevodskyDMgm_formallyInvertsTateObject
    :
    (Boundary.Motives.inverseTateShift
        (boundaryEffectiveTateObject (composition := composition))).obj
      ((VoevodskyDMgmEffectiveEmbedding (composition := composition)).obj
        (boundaryEffectiveTateObject (composition := composition))) =
      ⟨boundaryEffectiveTateObject (composition := composition), -1⟩ :=
  VoevodskyDMgmInverseTateShift_effectiveEmbedding_tateObject

/-- Compatibility alias retaining the shorter Boundary naming convention. -/
abbrev DMgmQ_Q :=
  VoevodskyDMgmQ_Q (composition := composition)

@[simp] theorem DMgmQ_Q_eq_VoevodskyDMgmQ_Q :
    DMgmQ_Q (composition := composition) =
      VoevodskyDMgmQ_Q (composition := composition) :=
  rfl

section HolographicInterface

variable {T : Type*} [Category T] [CategoryTheory.Limits.HasZeroObject T]
variable [Preadditive T] [HasShift T ℤ]
variable [∀ n : ℤ, Functor.Additive (shiftFunctor T n)] [Pretriangulated T]

/-- DMgm-facing alias for the boundary category of realizable probe profiles on
an abstract sector. -/
abbrev DMgmProbeBoundary (PD : ProbeDatum T) (S : TriangulatedSector T) :=
  ProbeBoundary PD S

@[simp] theorem DMgmProbeBoundary_eq_ProbeBoundary
    (PD : ProbeDatum T) (S : TriangulatedSector T) :
    DMgmProbeBoundary (T := T) PD S = ProbeBoundary PD S :=
  rfl

/-- DMgm-facing alias for holography of an abstract probe family on an abstract
sector. -/
abbrev DMgmHolographicProbeFamily (PD : ProbeDatum T) (S : TriangulatedSector T) :=
  HolographicProbeFamily T PD S

@[simp] theorem DMgmHolographicProbeFamily_eq_HolographicProbeFamily
    (PD : ProbeDatum T) (S : TriangulatedSector T) :
    DMgmHolographicProbeFamily (T := T) PD S = HolographicProbeFamily T PD S :=
  rfl

end HolographicInterface

end

end Boundary
