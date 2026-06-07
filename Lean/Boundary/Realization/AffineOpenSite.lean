import Boundary.Realization.Site
import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.CategoryTheory.Sites.DenseSubsite.InducedTopology
import Mathlib.Topology.Sets.Opens

/-!
# The affine-open realization site

For a smooth scheme `X`, the affine opens form a basis of the underlying topological space.
This file packages the inclusion of affine opens into all opens as a cover-dense functor and
records the induced topology comparison.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

namespace Boundary
namespace Realization

universe u

variable {k : Type u} [Field k] [PerfectField k]

/-- The inclusion of affine opens into all opens of the underlying topological space. -/
abbrev affineOpenInclusion (X : Geometry.SmSchemeOver k) :
    X.scheme.affineOpens ⥤ Opens X.scheme.toTopCat :=
  { obj := fun U => ((U : X.scheme.Opens) : Opens X.scheme.toTopCat)
    map := fun {U V} h => h
    map_id := by
      intro U
      rfl
    map_comp := by
      intro U V W f g
      rfl }

instance affineOpenInclusion_full (X : Geometry.SmSchemeOver k) :
    (affineOpenInclusion X).Full where
  map_surjective := by
    intro U V f
    exact ⟨homOfLE f.le, Subsingleton.elim _ _⟩

instance affineOpenInclusion_faithful (X : Geometry.SmSchemeOver k) :
    (affineOpenInclusion X).Faithful where
  map_injective := by
    intro U V f g h
    exact Subsingleton.elim _ _

instance affineOpenInclusion_isCoverDense (X : Geometry.SmSchemeOver k) :
    (affineOpenInclusion X).IsCoverDense (Opens.grothendieckTopology X.scheme.toTopCat) := by
  have hBasis :
      Opens.IsBasis (Set.range (fun U : X.scheme.affineOpens =>
        ((U : X.scheme.Opens) : Opens X.scheme.toTopCat))) := by
    rw [Subtype.range_coe]
    exact isBasis_affine_open X.scheme
  simpa [affineOpenInclusion] using
    (TopCat.Opens.coverDense_inducedFunctor
      (B := fun U : X.scheme.affineOpens => ((U : X.scheme.Opens) : Opens X.scheme.toTopCat))
      hBasis)

instance affineOpenInclusion_locallyCoverDense (X : Geometry.SmSchemeOver k) :
    (affineOpenInclusion X).LocallyCoverDense
      (Opens.grothendieckTopology X.scheme.toTopCat) where
  functorPushforward_functorPullback_mem := by
    intro U T
    exact Functor.IsCoverDense.functorPullback_pushforward_covering T

@[simp]
theorem affineOpenInclusion_obj (X : Geometry.SmSchemeOver k) (U : X.scheme.affineOpens) :
    (affineOpenInclusion X).obj U = ((U : X.scheme.Opens) : Opens X.scheme.toTopCat) := by
  rfl

end Realization
end Boundary
