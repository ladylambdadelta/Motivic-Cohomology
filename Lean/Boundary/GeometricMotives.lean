import Boundary.TateMotives
import Boundary.FormalTateStabilization

/-!
# Canonical Boundary Geometric Motives

This file is a consumer of the owner-level Tate-twist construction surface. It
does not build local monoidal or Tate-tensor facts. Those facts must be proved
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
motives at a supplied Tate-twist functor on effective motives.
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

/-- Restrict the Boundary Tate-twist endofunctor on effective motives to the
geometric effective subcategory, using the preservation proof supplied by the
Tate-twist package. -/
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

/-- Boundary geometric motives obtained from geometric effective motives by
formal Tate stabilization at a supplied Boundary Tate-twist package. -/
abbrev boundaryGeometricMotivesOfTateTwist
    (twistData :
      BoundaryTateTwistFunctorConstructionData
        (composition := composition)
        (boundaryCanonicalTateObjectConstructionData (composition := composition))) :=
  Boundary.Motives.DMgmQ_Q
    (canonicalGeometricEffectiveMotives composition)
    (boundaryGeometricEffectiveTateTwistFunctor
      (composition := composition) twistData)

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
Boundary geometric motives associated to a Tate-twist package. -/
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
Tate-twist package. -/
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

abbrev boundaryCanonicalGeometricMotives
    (twistData :
      BoundaryTateTwistFunctorConstructionData
        (composition := composition)
        (boundaryCanonicalTateObjectConstructionData (composition := composition))) :=
  boundaryGeometricMotivesOfTateTwist
    (composition := composition)
    twistData

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

/-- Canonical embedding of geometric effective motives into Boundary geometric
motives, routed through the owner-level Tate-twist data. -/
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

/-- Canonical Tate-shift equivalence on Boundary geometric motives, routed
through the owner-level Tate-twist data. -/
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

end

end Boundary
