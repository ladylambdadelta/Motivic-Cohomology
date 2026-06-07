import Boundary.Realization.AffineSmOver
import Boundary.Realization.DeRhamAffine.Complex

universe u

noncomputable section

open scoped TensorProduct
open scoped ModuleCat
open AlgebraicGeometry

namespace Boundary
namespace Realization

variable {k : Type u} [Field k] [PerfectField k]

/-- The truncated affine de Rham complex attached to an affine open of a smooth `k`-scheme,
using its canonical `k`-algebra structure on sections. -/
noncomputable abbrev smAffineOpenDeRhamCochainComplex
    (X : Geometry.SmSchemeOver k) (U : X.scheme.affineOpens) :
    CochainComplex (ModuleCat k) ℕ := by
  letI : Algebra k (Γ(X.scheme, (U : X.scheme.Opens))) :=
    smSchemeOpenSectionAlgebra X (U : X.scheme.Opens)
  exact affineDeRhamCochainComplex
    (R := k) (A := Γ(X.scheme, (U : X.scheme.Opens)))

theorem smAffineOpenDeRhamCochainComplex_obj_zero
    (X : Geometry.SmSchemeOver k) (U : X.scheme.affineOpens) :
    ((smAffineOpenDeRhamCochainComplex (k := k) X U).X 0 : ModuleCat k) =
      ModuleCat.of k (Γ(X.scheme, (U : X.scheme.Opens))) := by
  rfl

theorem smAffineOpenDeRhamCochainComplex_obj_one
    (X : Geometry.SmSchemeOver k) (U : X.scheme.affineOpens) :
    ((smAffineOpenDeRhamCochainComplex (k := k) X U).X 1 : ModuleCat k) =
      letI : Algebra k (Γ(X.scheme, (U : X.scheme.Opens))) :=
        smSchemeOpenSectionAlgebra X (U : X.scheme.Opens)
      ModuleCat.of k (affineFirstDeRhamPiece k (Γ(X.scheme, (U : X.scheme.Opens)))) := by
  rfl

theorem smAffineOpenDeRhamCochainComplex_obj_two
    (X : Geometry.SmSchemeOver k) (U : X.scheme.affineOpens) :
    ((smAffineOpenDeRhamCochainComplex (k := k) X U).X 2 : ModuleCat k) =
      letI : Algebra k (Γ(X.scheme, (U : X.scheme.Opens))) :=
        smSchemeOpenSectionAlgebra X (U : X.scheme.Opens)
      ModuleCat.of k (affineTwoForms (R := k) (S := Γ(X.scheme, (U : X.scheme.Opens)))) := by
  rfl

theorem smAffineOpenDeRhamCochainComplex_d_zero
    (X : Geometry.SmSchemeOver k) (U : X.scheme.affineOpens) :
    (smAffineOpenDeRhamCochainComplex (k := k) X U).d 0 1 =
      letI : Algebra k (Γ(X.scheme, (U : X.scheme.Opens))) :=
        smSchemeOpenSectionAlgebra X (U : X.scheme.Opens)
      ↟ (affineDeRhamDToFirstPiece
        (R := k) (A := Γ(X.scheme, (U : X.scheme.Opens)))) := by
  rfl

theorem smAffineOpenDeRhamCochainComplex_d_one
    (X : Geometry.SmSchemeOver k) (U : X.scheme.affineOpens) :
    (smAffineOpenDeRhamCochainComplex (k := k) X U).d 1 2 =
      letI : Algebra k (Γ(X.scheme, (U : X.scheme.Opens))) :=
        smSchemeOpenSectionAlgebra X (U : X.scheme.Opens)
      ↟ (affineD1 (R := k) (A := Γ(X.scheme, (U : X.scheme.Opens)))) := by
  rfl

/-- The truncated affine de Rham complex on an affine smooth scheme, evaluated on the canonical
top affine open. -/
abbrev smAffineDeRhamCochainComplex
    (X : AffineSmOver k) :
    CochainComplex (ModuleCat k) ℕ :=
  smAffineOpenDeRhamCochainComplex (k := k) X.obj (affineSmOverTop X)

theorem smAffineDeRhamCochainComplex_eq_top
    (X : AffineSmOver k) :
    smAffineDeRhamCochainComplex (k := k) X =
      smAffineOpenDeRhamCochainComplex (k := k) X.obj (affineSmOverTop X) := by
  rfl

theorem smAffineDeRhamCochainComplex_obj_zero
    (X : AffineSmOver k) :
    ((smAffineDeRhamCochainComplex (k := k) X).X 0 : ModuleCat k) =
      ModuleCat.of k
        (Γ(X.obj.scheme, ((affineSmOverTop X : X.obj.scheme.affineOpens) :
          X.obj.scheme.Opens))) := by
  rfl

theorem smAffineDeRhamCochainComplex_obj_one
    (X : AffineSmOver k) :
    ((smAffineDeRhamCochainComplex (k := k) X).X 1 : ModuleCat k) =
      letI : Algebra k
          (Γ(X.obj.scheme, ((affineSmOverTop X : X.obj.scheme.affineOpens) :
            X.obj.scheme.Opens))) :=
        smSchemeOpenSectionAlgebra X.obj (affineSmOverTop X : X.obj.scheme.Opens)
      ModuleCat.of k
        (affineFirstDeRhamPiece k
          (Γ(X.obj.scheme, ((affineSmOverTop X : X.obj.scheme.affineOpens) :
            X.obj.scheme.Opens)))) := by
  rfl

theorem smAffineDeRhamCochainComplex_obj_two
    (X : AffineSmOver k) :
    ((smAffineDeRhamCochainComplex (k := k) X).X 2 : ModuleCat k) =
      letI : Algebra k
          (Γ(X.obj.scheme, ((affineSmOverTop X : X.obj.scheme.affineOpens) :
            X.obj.scheme.Opens))) :=
        smSchemeOpenSectionAlgebra X.obj (affineSmOverTop X : X.obj.scheme.Opens)
      ModuleCat.of k
        (affineTwoForms (R := k)
          (S := Γ(X.obj.scheme, ((affineSmOverTop X : X.obj.scheme.affineOpens) :
            X.obj.scheme.Opens)))) := by
  rfl

end Realization
end Boundary
