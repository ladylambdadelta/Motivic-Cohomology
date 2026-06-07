import Boundary.TateMotives
import Boundary.FormalTateStabilization

/-!
# Canonical Boundary Geometric Motives

This file is a consumer of Tate action functor data. It does not build local
monoidal or Tate-tensor facts. Those facts must be proved
where they mathematically belong:

* tensor descent begins with the bilinear finite-correspondence external
  product in `ExternalProduct.lean`;
* it descends across the canonical `A1`/Nis localization only after showing
  that the primitive `A1` and Nisnevich generators remain local equivalences
  after external product, so the localization universal property produces a
  monoidal action on effective motives;
* the Tate action is then right tensoring by the concrete Tate object built in
  `TateMotives.lean` from the distinguished triangle
  `M(Spec k) ⟶ M(P¹) ⟶ \tilde M(P¹)`.

The construction here is the formal Tate stabilization of geometric effective
motives at a Tate action functor on effective motives.
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

/-- Boundary motives obtained by formally stabilizing canonical effective
motives at the projective-geometric Tate object constructed from `P¹`. -/
abbrev boundaryMotivesOfProjectiveGeometricTateObject :=
  Boundary.Motives.DMgmQ_Q
    (canonicalEffectiveMotives composition)
    (boundaryEffectiveTateObject (composition := composition))

@[simp] theorem boundaryMotivesOfProjectiveGeometricTateObject_eq
    :
    boundaryMotivesOfProjectiveGeometricTateObject
        (composition := composition) =
      Boundary.Motives.DMgmQ_Q
        (canonicalEffectiveMotives composition)
        (boundaryEffectiveTateObject (composition := composition)) :=
  rfl

instance boundaryMotivesOfProjectiveGeometricTateObjectCategory :
    Category (boundaryMotivesOfProjectiveGeometricTateObject
      (composition := composition)) :=
  Boundary.Motives.stabilizedObjectCategory
    (boundaryEffectiveTateObject (composition := composition))

/-- Canonical effective motives embed as Tate-degree-zero objects after
formal stabilization at the projective-geometric Tate object. -/
def boundaryEffectiveMotivesEmbeddingProjectiveGeometricTate :
    canonicalEffectiveMotives composition ⥤
      boundaryMotivesOfProjectiveGeometricTateObject
        (composition := composition) :=
  Boundary.Motives.effectiveEmbedding
    (boundaryEffectiveTateObject (composition := composition))

/-- Formal Tate-shift equivalence after stabilizing at the
projective-geometric Tate object. -/
def boundaryProjectiveGeometricTateShiftEquivalence :
    boundaryMotivesOfProjectiveGeometricTateObject
        (composition := composition) ≌
      boundaryMotivesOfProjectiveGeometricTateObject
        (composition := composition) :=
  Boundary.Motives.tateShiftEquivalence
    (boundaryEffectiveTateObject (composition := composition))

@[simp] theorem boundaryProjectiveGeometricTateShiftEquivalence_eq
    :
    boundaryProjectiveGeometricTateShiftEquivalence
        (composition := composition) =
      Boundary.Motives.tateShiftEquivalence
        (boundaryEffectiveTateObject (composition := composition)) :=
  rfl

/-- Universal property of formal stabilization at the projective-geometric
Tate object. -/
abbrev boundaryProjectiveGeometricTateStabilizationUniversalProperty
    (D : Type (u + 2)) [Category D] :=
  Boundary.Motives.tateStabilizationUniversalProperty
    (boundaryEffectiveTateObject (composition := composition))
    D

@[simp] theorem boundaryProjectiveGeometricTateStabilizationUniversalProperty_eq
    (D : Type (u + 2)) [Category D] :
    boundaryProjectiveGeometricTateStabilizationUniversalProperty
        (composition := composition) D =
      Boundary.Motives.tateStabilizationUniversalProperty
        (boundaryEffectiveTateObject (composition := composition))
        D :=
  rfl

@[simp] theorem boundaryEffectiveMotivesEmbeddingProjectiveGeometricTate_obj_effectiveObj
    (X : canonicalEffectiveMotives composition) :
    ((boundaryEffectiveMotivesEmbeddingProjectiveGeometricTate
        (composition := composition)).obj X).effectiveObj = X :=
  rfl

@[simp] theorem boundaryEffectiveMotivesEmbeddingProjectiveGeometricTate_obj_tateTwist
    (X : canonicalEffectiveMotives composition) :
    ((boundaryEffectiveMotivesEmbeddingProjectiveGeometricTate
        (composition := composition)).obj X).tateTwist = 0 :=
  rfl

@[simp] theorem boundaryProjectiveGeometricTateShift_effectiveEmbedding_tateObject
    :
    (Boundary.Motives.tateShift
        (boundaryEffectiveTateObject (composition := composition))).obj
      ((boundaryEffectiveMotivesEmbeddingProjectiveGeometricTate
          (composition := composition)).obj
        (boundaryEffectiveTateObject (composition := composition))) =
      ⟨boundaryEffectiveTateObject (composition := composition), 1⟩ :=
  rfl

@[simp] theorem boundaryProjectiveGeometricInverseTateShift_effectiveEmbedding_tateObject
    :
    (Boundary.Motives.inverseTateShift
        (boundaryEffectiveTateObject (composition := composition))).obj
      ((boundaryEffectiveMotivesEmbeddingProjectiveGeometricTate
          (composition := composition)).obj
        (boundaryEffectiveTateObject (composition := composition))) =
      ⟨boundaryEffectiveTateObject (composition := composition), -1⟩ :=
  rfl

/-- Restrict a Boundary Tate-action endofunctor on effective motives to the
geometric effective subcategory, using its preservation proof. -/
def boundaryGeometricEffectiveTateTwistFunctor
    (twistData :
      BoundaryTateTwistFunctorConstructionData
        (composition := composition)
        (boundaryCanonicalTateObjectConstructionData (composition := composition))) :
    canonicalGeometricEffectiveMotives composition ⥤
      canonicalGeometricEffectiveMotives composition where
  obj X := ⟨twistData.functor.obj X.1, twistData.preservesGeometricMotives X⟩
  map {X Y} f := twistData.functor.map f
  map_id := by
    intro X
    exact twistData.functor.map_id X.1
  map_comp := by
    intro X Y Z f g
    exact twistData.functor.map_comp f g

/-- The Boundary Tate-action functor preserves the geometric effective
subcategory by its geometric-preservation law. -/
theorem boundaryTateTwist_preservesGeometricEffectiveMotives
    (twistData :
      BoundaryTateTwistFunctorConstructionData
        (composition := composition)
        (boundaryCanonicalTateObjectConstructionData (composition := composition)))
    (X : canonicalGeometricEffectiveMotives composition) :
    (canonicalGeometricEffectiveThickSubcategory composition).P
      (twistData.functor.obj X.1) :=
  twistData.preservesGeometricMotives X

/-- The restricted Boundary Tate-twist functor has the object prescribed by the
ambient effective Tate-twist functor. -/
@[simp] theorem boundaryGeometricEffectiveTateTwistFunctor_obj_val
    (twistData :
      BoundaryTateTwistFunctorConstructionData
        (composition := composition)
        (boundaryCanonicalTateObjectConstructionData (composition := composition)))
    (X : canonicalGeometricEffectiveMotives composition) :
    ((boundaryGeometricEffectiveTateTwistFunctor
      (composition := composition) twistData).obj X).1 =
      twistData.functor.obj X.1 :=
  rfl

/-- Boundary geometric motives obtained from geometric effective motives by
formal Tate stabilization at a Boundary Tate-action functor. -/
abbrev boundaryGeometricMotivesOfTateTwist
    (twistData :
      BoundaryTateTwistFunctorConstructionData
        (composition := composition)
        (boundaryCanonicalTateObjectConstructionData (composition := composition))) :=
  Boundary.Motives.DMgmQ_Q
    (canonicalGeometricEffectiveMotives composition)
    (boundaryGeometricEffectiveTateTwistFunctor
      (composition := composition) twistData)

@[simp] theorem boundaryGeometricMotivesOfTateTwist_eq
    (twistData :
      BoundaryTateTwistFunctorConstructionData
        (composition := composition)
        (boundaryCanonicalTateObjectConstructionData (composition := composition))) :
    boundaryGeometricMotivesOfTateTwist
        (composition := composition) twistData =
      Boundary.Motives.DMgmQ_Q
        (canonicalGeometricEffectiveMotives composition)
        (boundaryGeometricEffectiveTateTwistFunctor
          (composition := composition) twistData) :=
  rfl

instance boundaryGeometricMotivesOfTateTwistCategory
    (twistData :
      BoundaryTateTwistFunctorConstructionData
        (composition := composition)
        (boundaryCanonicalTateObjectConstructionData (composition := composition))) :
    Category (boundaryGeometricMotivesOfTateTwist
      (composition := composition) twistData) :=
  Boundary.Motives.stabilizedObjectCategory
    (boundaryGeometricEffectiveTateTwistFunctor
      (composition := composition) twistData)

/-- Effective geometric motives embed as Tate-degree-zero objects in the
Boundary geometric motives associated to a Tate-action functor. -/
def boundaryGeometricEffectiveEmbeddingOfTateTwist
    (twistData :
      BoundaryTateTwistFunctorConstructionData
        (composition := composition)
        (boundaryCanonicalTateObjectConstructionData (composition := composition))) :
    canonicalGeometricEffectiveMotives composition ⥤
      boundaryGeometricMotivesOfTateTwist
        (composition := composition) twistData :=
  Boundary.Motives.effectiveEmbedding
    (boundaryGeometricEffectiveTateTwistFunctor
      (composition := composition) twistData)

/-- Formal Tate-shift equivalence on Boundary geometric motives associated to a
Tate-action functor. -/
def boundaryGeometricMotivesTateShiftEquivalenceOfTateTwist
    (twistData :
      BoundaryTateTwistFunctorConstructionData
        (composition := composition)
        (boundaryCanonicalTateObjectConstructionData (composition := composition))) :
    boundaryGeometricMotivesOfTateTwist
        (composition := composition) twistData ≌
      boundaryGeometricMotivesOfTateTwist
        (composition := composition) twistData :=
  Boundary.Motives.tateShiftEquivalence
    (boundaryGeometricEffectiveTateTwistFunctor
      (composition := composition) twistData)

/-- Universal property of Boundary geometric motives as the formal Tate
stabilization of geometric effective motives at the Tate-action functor. -/
abbrev boundaryGeometricMotivesTateStabilizationUniversalProperty
    (twistData :
      BoundaryTateTwistFunctorConstructionData
        (composition := composition)
        (boundaryCanonicalTateObjectConstructionData (composition := composition)))
    (D : Type (u + 2)) [Category D] :=
  Boundary.Motives.tateStabilizationUniversalProperty
    (boundaryGeometricEffectiveTateTwistFunctor
      (composition := composition) twistData)
    D

@[simp] theorem boundaryGeometricMotivesTateStabilizationUniversalProperty_eq
    (twistData :
      BoundaryTateTwistFunctorConstructionData
        (composition := composition)
        (boundaryCanonicalTateObjectConstructionData (composition := composition)))
    (D : Type (u + 2)) [Category D] :
    boundaryGeometricMotivesTateStabilizationUniversalProperty
        (composition := composition) twistData D =
      Boundary.Motives.tateStabilizationUniversalProperty
        (boundaryGeometricEffectiveTateTwistFunctor
          (composition := composition) twistData)
        D :=
  rfl

@[simp] theorem boundaryGeometricEffectiveEmbedding_obj_effectiveObj
    (twistData :
      BoundaryTateTwistFunctorConstructionData
        (composition := composition)
        (boundaryCanonicalTateObjectConstructionData (composition := composition)))
    (X : canonicalGeometricEffectiveMotives composition) :
    ((boundaryGeometricEffectiveEmbeddingOfTateTwist
        (composition := composition) twistData).obj X).effectiveObj = X :=
  rfl

@[simp] theorem boundaryGeometricEffectiveEmbedding_obj_tateTwist
    (twistData :
      BoundaryTateTwistFunctorConstructionData
        (composition := composition)
        (boundaryCanonicalTateObjectConstructionData (composition := composition)))
    (X : canonicalGeometricEffectiveMotives composition) :
    ((boundaryGeometricEffectiveEmbeddingOfTateTwist
        (composition := composition) twistData).obj X).tateTwist = 0 :=
  rfl

/-- On Boundary geometric motives, the formal Tate shift increments the Tate
degree and leaves the effective object component unchanged. -/
theorem boundaryGeometricMotives_tateShift_obj
    (twistData :
      BoundaryTateTwistFunctorConstructionData
        (composition := composition)
        (boundaryCanonicalTateObjectConstructionData (composition := composition)))
    (X : boundaryGeometricMotivesOfTateTwist
        (composition := composition) twistData) :
    (Boundary.Motives.tateShift
        (boundaryGeometricEffectiveTateTwistFunctor
          (composition := composition) twistData)).obj X =
      ⟨X.effectiveObj, X.tateTwist + 1⟩ :=
  rfl

/-- On Boundary geometric motives, the inverse formal Tate shift decrements the
Tate degree and leaves the effective object component unchanged. -/
theorem boundaryGeometricMotives_inverseTateShift_obj
    (twistData :
      BoundaryTateTwistFunctorConstructionData
        (composition := composition)
        (boundaryCanonicalTateObjectConstructionData (composition := composition)))
    (X : boundaryGeometricMotivesOfTateTwist
        (composition := composition) twistData) :
    (Boundary.Motives.inverseTateShift
        (boundaryGeometricEffectiveTateTwistFunctor
          (composition := composition) twistData)).obj X =
      ⟨X.effectiveObj, X.tateTwist - 1⟩ :=
  rfl

@[simp] theorem boundaryGeometricMotives_inverseTateShift_tateShift
    (twistData :
      BoundaryTateTwistFunctorConstructionData
        (composition := composition)
        (boundaryCanonicalTateObjectConstructionData (composition := composition)))
    (X : boundaryGeometricMotivesOfTateTwist
        (composition := composition) twistData) :
    (Boundary.Motives.inverseTateShift
        (boundaryGeometricEffectiveTateTwistFunctor
          (composition := composition) twistData)).obj
      ((Boundary.Motives.tateShift
          (boundaryGeometricEffectiveTateTwistFunctor
            (composition := composition) twistData)).obj X) = X :=
  Boundary.Motives.inverseTateShift_obj_tateShift_obj
    (boundaryGeometricEffectiveTateTwistFunctor
      (composition := composition) twistData) X

@[simp] theorem boundaryGeometricMotives_tateShift_inverseTateShift
    (twistData :
      BoundaryTateTwistFunctorConstructionData
        (composition := composition)
        (boundaryCanonicalTateObjectConstructionData (composition := composition)))
    (X : boundaryGeometricMotivesOfTateTwist
        (composition := composition) twistData) :
    (Boundary.Motives.tateShift
        (boundaryGeometricEffectiveTateTwistFunctor
          (composition := composition) twistData)).obj
      ((Boundary.Motives.inverseTateShift
          (boundaryGeometricEffectiveTateTwistFunctor
            (composition := composition) twistData)).obj X) = X :=
  Boundary.Motives.tateShift_obj_inverseTateShift_obj
    (boundaryGeometricEffectiveTateTwistFunctor
      (composition := composition) twistData) X

abbrev boundaryCanonicalGeometricMotives
    (twistData :
      BoundaryTateTwistFunctorConstructionData
        (composition := composition)
        (boundaryCanonicalTateObjectConstructionData (composition := composition))) :=
  boundaryGeometricMotivesOfTateTwist
    (composition := composition)
    twistData

@[simp] theorem boundaryCanonicalGeometricMotives_eq
    (twistData :
      BoundaryTateTwistFunctorConstructionData
        (composition := composition)
        (boundaryCanonicalTateObjectConstructionData (composition := composition))) :
    boundaryCanonicalGeometricMotives
        (composition := composition) twistData =
      boundaryGeometricMotivesOfTateTwist
        (composition := composition) twistData :=
  rfl

instance boundaryCanonicalGeometricMotivesCategory
    (twistData :
      BoundaryTateTwistFunctorConstructionData
        (composition := composition)
        (boundaryCanonicalTateObjectConstructionData (composition := composition))) :
    Category (boundaryCanonicalGeometricMotives
      (composition := composition) twistData) :=
  boundaryGeometricMotivesOfTateTwistCategory
    (composition := composition)
    twistData

/-- Embedding of geometric effective motives into Boundary geometric motives,
routed through Tate-action data. -/
def boundaryCanonicalGeometricEffectiveEmbedding
    (twistData :
      BoundaryTateTwistFunctorConstructionData
        (composition := composition)
        (boundaryCanonicalTateObjectConstructionData (composition := composition))) :
    canonicalGeometricEffectiveMotives composition ⥤
      boundaryCanonicalGeometricMotives
        (composition := composition) twistData :=
  boundaryGeometricEffectiveEmbeddingOfTateTwist
    (composition := composition)
    twistData

@[simp] theorem boundaryCanonicalGeometricEffectiveEmbedding_eq
    (twistData :
      BoundaryTateTwistFunctorConstructionData
        (composition := composition)
        (boundaryCanonicalTateObjectConstructionData (composition := composition))) :
    boundaryCanonicalGeometricEffectiveEmbedding
        (composition := composition) twistData =
      boundaryGeometricEffectiveEmbeddingOfTateTwist
        (composition := composition) twistData :=
  rfl

@[simp] theorem boundaryCanonicalGeometricEffectiveEmbedding_obj_effectiveObj
    (twistData :
      BoundaryTateTwistFunctorConstructionData
        (composition := composition)
        (boundaryCanonicalTateObjectConstructionData (composition := composition)))
    (X : canonicalGeometricEffectiveMotives composition) :
    ((boundaryCanonicalGeometricEffectiveEmbedding
        (composition := composition) twistData).obj X).effectiveObj = X :=
  rfl

@[simp] theorem boundaryCanonicalGeometricEffectiveEmbedding_obj_tateTwist
    (twistData :
      BoundaryTateTwistFunctorConstructionData
        (composition := composition)
        (boundaryCanonicalTateObjectConstructionData (composition := composition)))
    (X : canonicalGeometricEffectiveMotives composition) :
    ((boundaryCanonicalGeometricEffectiveEmbedding
        (composition := composition) twistData).obj X).tateTwist = 0 :=
  rfl

/-- Tate-shift equivalence on Boundary geometric motives, routed through
Tate-action data. -/
def boundaryCanonicalGeometricMotivesTateShiftEquivalence
    (twistData :
      BoundaryTateTwistFunctorConstructionData
        (composition := composition)
        (boundaryCanonicalTateObjectConstructionData (composition := composition))) :
    boundaryCanonicalGeometricMotives
        (composition := composition) twistData ≌
      boundaryCanonicalGeometricMotives
        (composition := composition) twistData :=
  boundaryGeometricMotivesTateShiftEquivalenceOfTateTwist
    (composition := composition)
    twistData

@[simp] theorem boundaryCanonicalGeometricMotivesTateShiftEquivalence_eq
    (twistData :
      BoundaryTateTwistFunctorConstructionData
        (composition := composition)
        (boundaryCanonicalTateObjectConstructionData (composition := composition))) :
    boundaryCanonicalGeometricMotivesTateShiftEquivalence
        (composition := composition) twistData =
      boundaryGeometricMotivesTateShiftEquivalenceOfTateTwist
        (composition := composition) twistData :=
  rfl

@[simp] theorem boundaryCanonicalGeometricMotives_tateShift_obj
    (twistData :
      BoundaryTateTwistFunctorConstructionData
        (composition := composition)
        (boundaryCanonicalTateObjectConstructionData (composition := composition)))
    (X : boundaryCanonicalGeometricMotives
        (composition := composition) twistData) :
    (Boundary.Motives.tateShift
        (boundaryGeometricEffectiveTateTwistFunctor
          (composition := composition) twistData)).obj X =
      ⟨X.effectiveObj, X.tateTwist + 1⟩ :=
  rfl

@[simp] theorem boundaryCanonicalGeometricMotives_inverseTateShift_obj
    (twistData :
      BoundaryTateTwistFunctorConstructionData
        (composition := composition)
        (boundaryCanonicalTateObjectConstructionData (composition := composition)))
    (X : boundaryCanonicalGeometricMotives
        (composition := composition) twistData) :
    (Boundary.Motives.inverseTateShift
        (boundaryGeometricEffectiveTateTwistFunctor
          (composition := composition) twistData)).obj X =
      ⟨X.effectiveObj, X.tateTwist - 1⟩ :=
  rfl

end

end Boundary
