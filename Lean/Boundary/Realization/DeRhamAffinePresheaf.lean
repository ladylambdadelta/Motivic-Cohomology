import Boundary.Realization.DeRhamAffine

/-!
# Affine de Rham realization API

This file is a stable import surface for the affine de Rham realization
construction. It keeps the affine-open family available under short, stable
names so later sheafification and comparison files do not have to reach into
the split owner files directly.
-/

noncomputable section

namespace Boundary
namespace Realization

universe u

variable {k : Type u} [Field k] [PerfectField k]

/-- The canonical affine-open de Rham cochain family. -/
abbrev canonicalSmAffineOpenDeRhamCochainComplex
    (X : Geometry.SmSchemeOver k) (U : X.scheme.affineOpens) :
    CochainComplex (ModuleCat k) ℕ :=
  smAffineOpenDeRhamCochainComplex (k := k) X U

/-- The canonical affine de Rham cochain complex on an affine smooth scheme. -/
abbrev canonicalSmAffineDeRhamCochainComplex
    (X : AffineSmOver k) :
    CochainComplex (ModuleCat k) ℕ :=
  smAffineDeRhamCochainComplex (k := k) X

@[simp] theorem canonicalSmAffineOpenDeRhamCochainComplex_eq
    (X : Geometry.SmSchemeOver k) (U : X.scheme.affineOpens) :
    canonicalSmAffineOpenDeRhamCochainComplex (k := k) X U =
      smAffineOpenDeRhamCochainComplex (k := k) X U := rfl

@[simp] theorem canonicalSmAffineDeRhamCochainComplex_eq
    (X : AffineSmOver k) :
    canonicalSmAffineDeRhamCochainComplex (k := k) X =
      smAffineDeRhamCochainComplex (k := k) X := rfl

end Realization
end Boundary
