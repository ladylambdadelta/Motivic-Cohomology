import Boundary.Realization.DeRhamAffine.D1Precursor

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

/-- The affine degree-one de Rham differential descended to the Kähler presentation quotient. -/
noncomputable def affineD1FromQuotient :
    ((A →₀ A) ⧸ (KaehlerDifferential.kerTotal R A).restrictScalars R) →ₗ[R]
      affineTwoForms (R := R) (S := A) :=
  ((KaehlerDifferential.kerTotal R A).restrictScalars R).liftQ
    (affineD1Precursor (R := R) (A := A))
    (affineD1Precursor_kerTotal_le_ker (R := R) (A := A))

/-- The first affine degree-one de Rham differential on Kähler one-forms. -/
noncomputable def affineD1 :
    affineFirstDeRhamPiece R A →ₗ[R] affineTwoForms (R := R) (S := A) :=
  affineD1FromQuotient (R := R) (A := A) ∘ₗ
    (Submodule.Quotient.restrictScalarsEquiv R (KaehlerDifferential.kerTotal R A)).symm.toLinearMap ∘ₗ
      ((KaehlerDifferential.quotKerTotalEquiv R A).symm.toLinearMap.restrictScalars R)

theorem affineD1FromQuotient_apply_mkQ_single
    (x y : A) :
    affineD1FromQuotient (R := R) (A := A)
      (Submodule.Quotient.mk (Finsupp.single y x)) =
        affineD0WedgeOneForms (R := R) (A := A) x
          (affineDeRhamD0ToOneForms (R := R) (S := A) y) := by
  rw [affineD1FromQuotient, Submodule.liftQ_apply, affineD1Precursor_apply_single]

theorem affineD1_D
    (x : A) :
    affineD1 (R := R) (A := A) (affineDeRhamD R A x) = 0 := by
  have hquot :
      ((KaehlerDifferential.quotKerTotalEquiv R A).symm
        (affineDeRhamD R A x)) =
      Submodule.Quotient.mk (Finsupp.single x (1 : A)) := by
    exact DFunLike.congr_fun
      (KaehlerDifferential.quotKerTotalEquiv_symm_comp_D (R := R) (S := A)) x
  have hmk := congrArg
    ((Submodule.Quotient.restrictScalarsEquiv R (KaehlerDifferential.kerTotal R A)).symm) hquot
  have hval := congrArg (affineD1FromQuotient (R := R) (A := A)) hmk
  have hmk_single :
      (Submodule.Quotient.restrictScalarsEquiv R (KaehlerDifferential.kerTotal R A)).symm
        (Submodule.Quotient.mk (Finsupp.single x (1 : A))) =
          Submodule.Quotient.mk (Finsupp.single x (1 : A)) := by
    rfl
  rw [hmk_single] at hval
  rw [affineD1]
  rw [LinearMap.comp_apply, LinearMap.comp_apply]
  exact hval.trans <| by
    apply Subtype.ext
    have h1 : affineDeRhamD R A 1 = 0 := by
      exact Derivation.map_one_eq_zero (D := affineDeRhamD R A)
    have hι : affineDeRhamι R A 0 = 0 := by
      exact map_zero (affineDeRhamι R A)
    rw [affineD1FromQuotient_apply_mkQ_single, affineD0WedgeOneForms_apply_coe,
      affineDeRhamD0ToOneForms_apply, affineDeRhamD0_apply, h1]
    rw [hι]
    exact zero_mul ((affineDeRhamD0 R A) x)

end Map

end Realization
end Boundary
