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
* the canonical Tate object;
* the owner-level Tate-twist construction data on effective motives;
* formal Tate stabilization.
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

/-- Voevodsky's `DMgm(Q)_Q`, as constructed by the canonical Boundary pipeline
from geometric effective motives and Tate stabilization. -/
abbrev VoevodskyDMgmQ_Q
    (twistData :
      BoundaryTateTwistFunctorConstructionData
        (composition := composition)
        (boundaryCanonicalTateObjectConstructionData (composition := composition))) :=
  boundaryCanonicalGeometricMotives (composition := composition) twistData

/-- Canonical effective geometric motives entering the `DMgm(Q)_Q`
construction. -/
abbrev VoevodskyDMgmEffectiveGeometricQ_Q :=
  canonicalGeometricEffectiveMotives composition

/-- Canonical embedding `DM_eff,gm(Q)_Q ⥤ DMgm(Q)_Q`. -/
def VoevodskyDMgmEffectiveEmbedding
    (twistData :
      BoundaryTateTwistFunctorConstructionData
        (composition := composition)
        (boundaryCanonicalTateObjectConstructionData (composition := composition))) :
    VoevodskyDMgmEffectiveGeometricQ_Q (composition := composition) ⥤
      VoevodskyDMgmQ_Q (composition := composition) twistData :=
  boundaryCanonicalGeometricEffectiveEmbedding
    (composition := composition)
    twistData

/-- Canonical Tate-shift equivalence on `DMgm(Q)_Q`. -/
def VoevodskyDMgmTateShiftEquivalence
    (twistData :
      BoundaryTateTwistFunctorConstructionData
        (composition := composition)
        (boundaryCanonicalTateObjectConstructionData (composition := composition))) :
    VoevodskyDMgmQ_Q (composition := composition) twistData ≌
      VoevodskyDMgmQ_Q (composition := composition) twistData :=
  boundaryCanonicalGeometricMotivesTateShiftEquivalence
    (composition := composition)
    twistData

/-- Compatibility alias retaining the shorter Boundary naming convention. -/
abbrev DMgmQ_Q
    (twistData :
      BoundaryTateTwistFunctorConstructionData
        (composition := composition)
        (boundaryCanonicalTateObjectConstructionData (composition := composition))) :=
  VoevodskyDMgmQ_Q (composition := composition) twistData

section HolographicInterface

variable {T : Type*} [Category T] [CategoryTheory.Limits.HasZeroObject T]
variable [Preadditive T] [HasShift T ℤ]
variable [∀ n : ℤ, Functor.Additive (shiftFunctor T n)] [Pretriangulated T]

/-- DMgm-facing alias for the boundary category of realizable probe profiles on
an abstract sector. -/
abbrev DMgmProbeBoundary (PD : ProbeDatum T) (S : TriangulatedSector T) :=
  ProbeBoundary PD S

/-- DMgm-facing alias for holography of an abstract probe family on an abstract
sector. -/
abbrev DMgmHolographicProbeFamily (PD : ProbeDatum T) (S : TriangulatedSector T) :=
  HolographicProbeFamily T PD S

end HolographicInterface

end

end Boundary
