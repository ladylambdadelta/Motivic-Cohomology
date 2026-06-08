import Boundary.TateMotives
import Boundary.DMgm

/-!
# Boundary effective layer: canonical DMgm stabilization

This file records the actual classical-layer connection available from the
Boundary effective-motive layer.

The effective category used here is `Boundary.canonicalEffectiveMotives`
itself, and the stabilized motive category is the canonical Boundary
`DMgmQ_Q` surface exported in `Boundary.DMgm`.
-/

universe u

open CategoryTheory

namespace MacLane.Motives.BoundarySpecialization

noncomputable section

variable {k : Type u} [Field k] [PerfectField k]

variable (composition : Boundary.CanonicalCompositionData (k := k))
variable [Abelian (Boundary.LinearPST (Boundary.canonicalCategory composition))]
variable [HasDerivedCategory (Boundary.LinearPST (Boundary.canonicalCategory composition))]
variable [Abelian (Boundary.canonicalA1NisLocalization composition)]
variable [HasDerivedCategory (Boundary.canonicalA1NisLocalization composition)]
variable [(Boundary.canonicalA1NisLocalizationFunctor composition).Additive]
variable [Limits.PreservesFiniteLimits (Boundary.canonicalA1NisLocalizationFunctor composition)]
variable [Limits.PreservesFiniteColimits (Boundary.canonicalA1NisLocalizationFunctor composition)]

/-- The actual morphism-bearing effective category exported by the Boundary
effective-motive layer. -/
abbrev EffectiveCategoryQ
    :=
  Boundary.canonicalEffectiveMotives composition

/-- The actual Boundary Tate object currently constructed on the effective
category. This is `\widetilde M(P¹)[-2]`. -/
abbrev boundaryTateObject : EffectiveCategoryQ composition :=
  (Boundary.boundaryCanonicalTateObjectConstructionData (composition := composition)).tateObject

/-- The cohomological shift by `[-2]` on the effective category. -/
def cohomologicalShiftEndofunctor
    : EffectiveCategoryQ composition ⥤ EffectiveCategoryQ composition :=
  shiftFunctor (Boundary.canonicalEffectiveMotives composition) (-2 : ℤ)

/-- The canonical Boundary stabilization of the effective category. -/
abbrev ShiftStabilizedEffectiveMotivesQ
    :=
  Boundary.DMgmQ_Q (composition := composition)

end

end MacLane.Motives.BoundarySpecialization
