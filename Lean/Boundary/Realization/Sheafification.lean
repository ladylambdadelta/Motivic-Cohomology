import Boundary.Realization.AffineOpenSite
import Boundary.Realization.AffineComplexPoints
import Boundary.Realization.DeRhamAffine
import Mathlib.CategoryTheory.Sites.LeftExact
import Mathlib.CategoryTheory.Sites.DenseSubsite.SheafEquiv

/-!
# Sheafification for the realization complexes

This file is the first honest global realization layer:

- sheafify the affine-open Betti/de Rham presheaves on the affine-open site;
- transport those sheaves across the dense affine-open inclusion to the open-site sheaves;
- expose the comparison equivalence that will later feed derived global sections.

The derived-global-sections and cohomology objects are still upstream of this file.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace

namespace Boundary
namespace Realization

universe u

variable {k : Type u} [Field k] [PerfectField k]

namespace AffineOpen

/-- The Grothendieck topology on the affine-open basis induced from the open-site topology. -/
abbrev topology (X : Geometry.SmSchemeOver k) :
    GrothendieckTopology X.scheme.affineOpens :=
  (affineOpenInclusion X).inducedTopology (Opens.grothendieckTopology X.scheme.toTopCat)

@[simp]
theorem topology_eq (X : Geometry.SmSchemeOver k) :
    topology X =
      (affineOpenInclusion X).inducedTopology (Opens.grothendieckTopology X.scheme.toTopCat) :=
  rfl

/-- Global Betti chains on the top affine open of an affine smooth scheme. -/
abbrev bettiGlobalSections (X : AffineSmOver ℂ) :
    ChainComplex (ModuleCat ℚ) ℕ :=
  smAffineOpenCanonicalBettiChains X.obj (affineSmOverTop X)

@[simp]
theorem bettiGlobalSections_eq (X : AffineSmOver ℂ) :
    bettiGlobalSections X = smAffineOpenCanonicalBettiChains X.obj (affineSmOverTop X) :=
  rfl

/-- Global affine de Rham cochains on the top affine open of an affine smooth scheme. -/
abbrev deRhamGlobalSections (X : AffineSmOver ℂ) :
    CochainComplex (ModuleCat ℂ) ℕ :=
  smAffineDeRhamCochainComplex (k := ℂ) X

@[simp]
theorem deRhamGlobalSections_eq (X : AffineSmOver ℂ) :
    deRhamGlobalSections X = smAffineDeRhamCochainComplex (k := ℂ) X :=
  rfl

end AffineOpen

end Realization
end Boundary
