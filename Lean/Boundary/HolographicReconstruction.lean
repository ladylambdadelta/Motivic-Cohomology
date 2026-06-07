import Mathlib.CategoryTheory.Functor.KanExtension.Adjunction
import Boundary.BoundaryProbeAPI

/-!
# Holographic reconstruction

This file owns the explicit reconstruction-side interface for the boundary
probe program.

The intended long-term reconstruction formula is a weighted boundary colimit
or coend. The file therefore exposes:

- a diagram object for the boundary dependency presentation,
- a normalized boundary colimit constructor,
- a quasi-inverse package with unit/counit comparison data,
- and the boundary-facing reconstruction avatar used downstream.

The actual proof content will come from the weighted-colimit/coend machinery
and the chosen boundary presentation data.
-/

noncomputable section

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.Preadditive
open CategoryTheory.Pretriangulated
open scoped ZeroObject

universe vT uT uD vD uJ vJ

namespace Boundary

/-- A boundary dependency diagram packages the indexing category and the
target-valued diagram to be colimited. -/
structure BoundaryDependencyDiagram (T : Type uT) [Category.{vT} T] where
  Shape : Type uJ
  shapeCategory : Category.{vJ} Shape
  diagram : Shape ⥤ T

attribute [instance] BoundaryDependencyDiagram.shapeCategory

namespace BoundaryDependencyDiagram

variable {T : Type uT} [Category.{vT} T]

/-- The normalized boundary colimit of a dependency diagram, when the colimit
exists. -/
noncomputable def normalizedBoundaryColimit
    (D : BoundaryDependencyDiagram T)
    [HasColimit D.diagram] : T :=
  colimit D.diagram

end BoundaryDependencyDiagram

/-- A boundary profile avatar remembers the source object and the comparison to
its probe profile. This is the conservative avatar fallback used by the
reconstruction package. -/
structure BoundaryProfileAvatar
    {T : Type uT} [Category.{vT} T]
    (profileCategory : Type uD) [Category.{vD} profileCategory] where
  source : T
  profile : profileCategory
  comparison : profileCategory ≅ profileCategory

/-- A boundary quasi-inverse package is the actual reconstruction interface:
it supplies a profile category, a reconstruction functor, and the unit/counit
comparison isomorphisms. -/
structure BoundaryHolographicQuasiInverse
    {T : Type uT} [Category.{vT} T]
    (profileCategory : Type uD) [Category.{vD} profileCategory] where
  reconstructFromBoundaryProfile : profileCategory ⥤ T
  boundaryProfileFunctor : T ⥤ profileCategory
  reconstruct_profile_counit :
    reconstructFromBoundaryProfile ⋙ boundaryProfileFunctor ≅ 𝟭 profileCategory
  profile_reconstruct_unit :
    boundaryProfileFunctor ⋙ reconstructFromBoundaryProfile ≅ 𝟭 T

namespace BoundaryHolographicQuasiInverse

variable {T : Type uT} [Category.{vT} T]
  {profileCategory : Type uD} [Category.{vD} profileCategory]
  (Q : BoundaryHolographicQuasiInverse (T := T) profileCategory)

abbrev holographicReconstructionFunctor : profileCategory ⥤ T :=
  Q.reconstructFromBoundaryProfile

abbrev boundaryProfileForwardFunctor : T ⥤ profileCategory :=
  Q.boundaryProfileFunctor

end BoundaryHolographicQuasiInverse

/-- The boundary reconstruction package specialized to a probe datum and
sector. This is the owner-level place where the explicit coend / weighted
colimit reconstruction will be instantiated. -/
structure BoundaryProbeReconstruction
    {T : Type uT} [Category.{vT} T] [CategoryTheory.Limits.HasZeroObject T]
    [Preadditive T] [HasShift T ℤ] [∀ n : ℤ, Functor.Additive (shiftFunctor T n)]
    [Pretriangulated T]
    (P : BoundaryProbeFamily T) (S : TriangulatedSector T) where
  profileCategory : Type uD
  profileCategoryCat : Category.{vD} profileCategory
  boundaryProfileFunctor : S.SectorCategory ⥤ profileCategory
  reconstructionFunctor : profileCategory ⥤ S.SectorCategory
  boundaryProfileCoendDiagram :
    profileCategory → BoundaryDependencyDiagram (S.SectorCategory)
  reconstruct_profile_counit :
    reconstructionFunctor ⋙ boundaryProfileFunctor ≅ 𝟭 profileCategory
  profile_reconstruct_unit :
    boundaryProfileFunctor ⋙ reconstructionFunctor ≅ 𝟭 S.SectorCategory

attribute [instance] BoundaryProbeReconstruction.profileCategoryCat

namespace BoundaryProbeReconstruction

variable {T : Type uT} [Category.{vT} T] [CategoryTheory.Limits.HasZeroObject T]
  [Preadditive T] [HasShift T ℤ] [∀ n : ℤ, Functor.Additive (shiftFunctor T n)]
  [Pretriangulated T]
  {P : BoundaryProbeFamily T} {S : TriangulatedSector T}
  (R : BoundaryProbeReconstruction (T := T) P S)

abbrev reconstructFromBoundaryProfileFunctor : R.profileCategory ⥤ S.SectorCategory :=
  R.reconstructionFunctor

abbrev boundaryProfileFunctor' : S.SectorCategory ⥤ R.profileCategory :=
  R.boundaryProfileFunctor

end BoundaryProbeReconstruction

end Boundary
