import Boundary.Realization.DeRhamAffine.D1

universe u

noncomputable section

open scoped TensorProduct
open scoped ModuleCat

namespace Boundary
namespace Realization

variable (R S : Type u)
variable [CommRing R] [CommRing S] [Algebra R S]

section Map

variable {A : Type u}
variable [CommRing A] [Algebra R A]

/-- The affine degree-zero differential as an `R`-linear map into Kähler one-forms. -/
abbrev affineDeRhamDToFirstPiece :
    A →ₗ[R] affineFirstDeRhamPiece R A :=
  (affineDeRhamD R A).toLinearMap.restrictScalars R

private abbrev affineDeRhamCochainComplexObj (n : ℕ) :
    ModuleCat R :=
  match n with
  | 0 => ModuleCat.of R A
  | 1 => ModuleCat.of R (affineFirstDeRhamPiece R A)
  | 2 => ModuleCat.of R (affineTwoForms (R := R) (S := A))
  | _ + 3 => ModuleCat.of R PUnit

private abbrev affineDeRhamCochainComplexDiff (n : ℕ) :
    affineDeRhamCochainComplexObj (R := R) (A := A) n ⟶
      affineDeRhamCochainComplexObj (R := R) (A := A) (n + 1) :=
  match n with
  | 0 => ↟ (affineDeRhamDToFirstPiece (R := R) (A := A))
  | 1 => ↟ (affineD1 (R := R) (A := A))
  | _ + 2 => 0

/-- The currently constructed affine de Rham cochain complex:
`A -> Ω¹ -> Ω²`, concentrated in degrees `0`, `1`, and `2`. -/
noncomputable def affineDeRhamCochainComplex :
    CochainComplex (ModuleCat R) ℕ :=
  CochainComplex.of
    (affineDeRhamCochainComplexObj (R := R) (A := A))
    (affineDeRhamCochainComplexDiff (R := R) (A := A))
    (by
      intro n
      cases n with
      | zero =>
          exact affineD1_comp_affineDeRhamD0ToOneForms (R := R) (A := A)
      | succ n =>
          cases n <;> rfl)

theorem affineDeRhamCochainComplex_X_zero :
    (affineDeRhamCochainComplex (R := R) (A := A)).X 0 = ModuleCat.of R A :=
  rfl

theorem affineDeRhamCochainComplex_X_one :
    (affineDeRhamCochainComplex (R := R) (A := A)).X 1 =
      ModuleCat.of R (affineFirstDeRhamPiece R A) :=
  rfl

theorem affineDeRhamCochainComplex_X_two :
    (affineDeRhamCochainComplex (R := R) (A := A)).X 2 =
      ModuleCat.of R (affineTwoForms (R := R) (S := A)) :=
  rfl

theorem affineDeRhamCochainComplex_d_zero :
    (affineDeRhamCochainComplex (R := R) (A := A)).d 0 1 =
      ↟ (affineDeRhamDToFirstPiece (R := R) (A := A)) := by
  change (CochainComplex.of
      (affineDeRhamCochainComplexObj (R := R) (A := A))
      (affineDeRhamCochainComplexDiff (R := R) (A := A))
      (by
        intro n
        cases n with
        | zero =>
            exact affineD1_comp_affineDeRhamD0ToOneForms (R := R) (A := A)
        | succ n =>
            cases n <;> rfl)).d 0 (0 + 1) =
    affineDeRhamCochainComplexDiff (R := R) (A := A) 0
  exact CochainComplex.of_d
    (X := affineDeRhamCochainComplexObj (R := R) (A := A))
    (d := affineDeRhamCochainComplexDiff (R := R) (A := A))
    (sq := by
      intro n
      cases n with
      | zero =>
          exact affineD1_comp_affineDeRhamD0ToOneForms (R := R) (A := A)
      | succ n =>
          cases n <;> rfl)
    0

theorem affineDeRhamCochainComplex_d_one :
    (affineDeRhamCochainComplex (R := R) (A := A)).d 1 2 =
      ↟ (affineD1 (R := R) (A := A)) := by
  change (CochainComplex.of
      (affineDeRhamCochainComplexObj (R := R) (A := A))
      (affineDeRhamCochainComplexDiff (R := R) (A := A))
      (by
        intro n
        cases n with
        | zero =>
            exact affineD1_comp_affineDeRhamD0ToOneForms (R := R) (A := A)
        | succ n =>
            cases n <;> rfl)).d 1 (1 + 1) =
    affineDeRhamCochainComplexDiff (R := R) (A := A) 1
  exact CochainComplex.of_d
    (X := affineDeRhamCochainComplexObj (R := R) (A := A))
    (d := affineDeRhamCochainComplexDiff (R := R) (A := A))
    (sq := by
      intro n
      cases n with
      | zero =>
          exact affineD1_comp_affineDeRhamD0ToOneForms (R := R) (A := A)
      | succ n =>
          cases n <;> rfl)
    1

end Map

end Realization
end Boundary
