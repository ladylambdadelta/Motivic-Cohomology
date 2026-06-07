import Boundary.Realization.DeRhamAffine.Maps

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

theorem affineDeRhamD0_mul_swap_add
    (x y : A) :
    affineDeRhamD0 R A x * affineDeRhamD0 R A y +
      affineDeRhamD0 R A y * affineDeRhamD0 R A x = 0 := by
  rw [affineDeRhamD0_apply, affineDeRhamD0_apply]
  change affineDeRhamι R A (affineDeRhamD R A x) *
      affineDeRhamι R A (affineDeRhamD R A y) +
    affineDeRhamι R A (affineDeRhamD R A y) *
      affineDeRhamι R A (affineDeRhamD R A x) = 0
  exact ExteriorAlgebra.ι_add_mul_swap (R := A)
    (M := affineFirstDeRhamPiece R A)
    (affineDeRhamD R A x) (affineDeRhamD R A y)

/-- Left multiplication by an exact one-form, viewed as a bilinear map on one-forms. -/
noncomputable def affineWedgeExactOneFormsLeft :
    affineExactOneForms R A →ₗ[R] affineOneForms R A →ₗ[R] affineTwoForms R A := by
  refine
    { toFun := fun ω =>
        { toFun := fun η =>
            ⟨(ω : affineDeRhamAlgebra R A) * η, ?_⟩
          map_add' := ?_
          map_smul' := ?_ }
      map_add' := ?_
      map_smul' := ?_ }
  · have hω : (ω : affineDeRhamAlgebra R A) ∈
        (⋀[A]^1 (affineFirstDeRhamPiece R A) : Submodule A (affineDeRhamAlgebra R A)) :=
      by
        exact (affineExactOneForms_mem_exteriorPower_one (R := R) (S := A)) ω.property
    have hη : (η : affineDeRhamAlgebra R A) ∈
        (⋀[A]^1 (affineFirstDeRhamPiece R A) : Submodule A (affineDeRhamAlgebra R A)) :=
      η.property
    exact SetLike.mul_mem_graded hω hη
  · intro ω₁ ω₂
    apply Subtype.ext
    exact mul_add _ _ _
  · intro a ω
    apply Subtype.ext
    exact mul_smul_comm _ _ _
  · intro ω₁ ω₂
    apply LinearMap.ext
    intro η
    apply Subtype.ext
    exact add_mul _ _ _
  · intro a ω
    apply LinearMap.ext
    intro η
    apply Subtype.ext
    exact smul_mul_assoc _ _ _

theorem affineWedgeExactOneFormsLeft_apply_coe
    (ω : affineExactOneForms R A) (η : affineOneForms R A) :
    ((affineWedgeExactOneFormsLeft (R := R) (A := A) ω η :
        affineTwoForms R A) : affineDeRhamAlgebra R A) =
      (ω : affineDeRhamAlgebra R A) * η := by
  rfl

/-- The degree-zero differential followed by wedge-left multiplication. -/
def affineD0WedgeOneForms :
    A →ₗ[R] affineOneForms R A →ₗ[R] affineTwoForms R A :=
  (affineWedgeExactOneFormsLeft (R := R) (A := A)).comp
    (affineDeRhamD0ToExactOneForms (R := R) (S := A))

theorem affineD0WedgeOneForms_apply
    (x : A) (η : affineOneForms R A) :
    affineD0WedgeOneForms (R := R) (A := A) x η =
      affineWedgeExactOneFormsLeft (R := R) (A := A)
        (affineDeRhamD0ToExactOneForms (R := R) (S := A) x) η :=
  rfl

theorem affineD0WedgeOneForms_apply_coe
    (x : A) (η : affineOneForms R A) :
    ((affineD0WedgeOneForms (R := R) (A := A) x η :
        affineTwoForms R A) : affineDeRhamAlgebra R A) =
    affineDeRhamD0 R A x * η := by
  rw [affineD0WedgeOneForms_apply, affineWedgeExactOneFormsLeft_apply_coe,
    affineDeRhamD0ToExactOneForms_apply]

theorem affineD0WedgeOneForms_swap_add
    (x y : A) :
    ((affineD0WedgeOneForms (R := R) (A := A) x
        (affineDeRhamD0ToOneForms (R := R) (S := A) y) :
          affineTwoForms R A) : affineDeRhamAlgebra R A) +
      ((affineD0WedgeOneForms (R := R) (A := A) y
        (affineDeRhamD0ToOneForms (R := R) (S := A) x) :
          affineTwoForms R A) : affineDeRhamAlgebra R A) = 0 := by
  rw [affineD0WedgeOneForms_apply_coe, affineD0WedgeOneForms_apply_coe]
  rw [affineDeRhamD0ToOneForms_apply, affineDeRhamD0ToOneForms_apply]
  rw [affineDeRhamD0_mul_swap_add]

end Map

end Realization
end Boundary
