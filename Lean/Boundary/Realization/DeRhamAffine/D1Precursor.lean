import Boundary.Realization.DeRhamAffine.Wedge

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

theorem affineDeRhamD0_mul_generator_relation
    (x y z : A) :
    affineDeRhamD0 R A (z * x) * affineDeRhamD0 R A y +
      affineDeRhamD0 R A (z * y) * affineDeRhamD0 R A x =
        affineDeRhamD0 R A z * affineDeRhamD0 R A (x * y) := by
  let dx := affineDeRhamD0 R A x
  let dy := affineDeRhamD0 R A y
  let dz := affineDeRhamD0 R A z
  have hz :
      z • (dx * dy) + z • (dy * dx) = 0 := by
    rw [← smul_add, affineDeRhamD0_mul_swap_add (R := R) (A := A) x y, smul_zero]
  rw [Derivation.leibniz, Derivation.leibniz, Derivation.leibniz]
  rw [add_mul, add_mul, mul_add]
  rw [Algebra.smul_mul_assoc, Algebra.smul_mul_assoc, Algebra.smul_mul_assoc,
    Algebra.smul_mul_assoc]
  rw [Algebra.mul_smul_comm, Algebra.mul_smul_comm]
  calc
    z • (dx * dy) + x • (dz * dy) + (z • (dy * dx) + y • (dz * dx))
        = (z • (dx * dy) + z • (dy * dx)) + (x • (dz * dy) + y • (dz * dx)) := by
            ac_rfl
    _ = 0 + (x • (dz * dy) + y • (dz * dx)) := by rw [hz]
    _ = x • (dz * dy) + y • (dz * dx) := zero_add _

/-- The presentation-level precursor to the affine degree-one de Rham differential:
`single y x` is sent to `d₀x ∧ d₀y`. -/
def affineD1Precursor :
    (A →₀ A) →ₗ[R] affineTwoForms (R := R) (S := A) :=
  Finsupp.lsum R fun y =>
    { toFun := fun x =>
        affineD0WedgeOneForms (R := R) (A := A) x
          (affineDeRhamD0ToOneForms (R := R) (S := A) y)
      map_add' := by
        intro x z
        exact DFunLike.congr_fun
          (map_add (affineD0WedgeOneForms (R := R) (A := A)) x z)
          (affineDeRhamD0ToOneForms (R := R) (S := A) y)
      map_smul' := by
        intro a x
        exact DFunLike.congr_fun
          (map_smul (affineD0WedgeOneForms (R := R) (A := A)) a x)
          (affineDeRhamD0ToOneForms (R := R) (S := A) y) }

theorem affineD1Precursor_apply_single
    (x y : A) :
    affineD1Precursor (R := R) (A := A) (Finsupp.single y x) =
      affineD0WedgeOneForms (R := R) (A := A) x
        (affineDeRhamD0ToOneForms (R := R) (S := A) y) := by
  rw [affineD1Precursor]
  exact Finsupp.lsum_single (S := R)
    (f := fun y =>
      { toFun := fun x =>
          affineD0WedgeOneForms (R := R) (A := A) x
            (affineDeRhamD0ToOneForms (R := R) (S := A) y)
        map_add' := by
          intro x z
          exact DFunLike.congr_fun
            (map_add (affineD0WedgeOneForms (R := R) (A := A)) x z)
            (affineDeRhamD0ToOneForms (R := R) (S := A) y)
        map_smul' := by
          intro a x
          exact DFunLike.congr_fun
            (map_smul (affineD0WedgeOneForms (R := R) (A := A)) a x)
            (affineDeRhamD0ToOneForms (R := R) (S := A) y) }) y x

theorem affineD1Precursor_apply_single_coe
    (x y : A) :
    ((affineD1Precursor (R := R) (A := A) (Finsupp.single y x) :
        affineTwoForms (R := R) (S := A)) : affineDeRhamAlgebra R A) =
      affineDeRhamD0 R A x * affineDeRhamD0 R A y := by
  rw [affineD1Precursor_apply_single, affineD0WedgeOneForms_apply_coe,
    affineDeRhamD0ToOneForms_apply]

theorem affineD1Precursor_kerTotal_add_generator
    (x y z : A) :
    affineD1Precursor (R := R) (A := A)
      (Finsupp.single x z + Finsupp.single y z - Finsupp.single (x + y) z) = 0 := by
  apply Subtype.ext
  rw [LinearMap.map_sub, LinearMap.map_add]
  change
    ((affineD1Precursor (R := R) (A := A) (Finsupp.single x z) :
      affineTwoForms (R := R) (S := A)) : affineDeRhamAlgebra R A) +
    ((affineD1Precursor (R := R) (A := A) (Finsupp.single y z) :
      affineTwoForms (R := R) (S := A)) : affineDeRhamAlgebra R A) -
    ((affineD1Precursor (R := R) (A := A) (Finsupp.single (x + y) z) :
      affineTwoForms (R := R) (S := A)) : affineDeRhamAlgebra R A) = 0
  rw [affineD1Precursor_apply_single_coe, affineD1Precursor_apply_single_coe,
    affineD1Precursor_apply_single_coe, affineDeRhamD0, map_add, mul_add]
  abel

theorem affineD1Precursor_kerTotal_algebraMap_generator
    (r : R) (x : A) :
    affineD1Precursor (R := R) (A := A) (Finsupp.single (algebraMap R A r) x) = 0 := by
  apply Subtype.ext
  rw [affineD1Precursor_apply_single_coe]
  rw [affineDeRhamD0_apply, Derivation.map_algebraMap, mul_zero]
  change (0 : affineDeRhamAlgebra R A) = 0
  rfl

theorem affineD1Precursor_kerTotal_mul_generator
    (x y z : A) :
    affineD1Precursor (R := R) (A := A)
      (Finsupp.single y (z * x) + Finsupp.single x (z * y) -
        Finsupp.single (x * y) z) = 0 := by
  apply Subtype.ext
  change
    ((affineD1Precursor (R := R) (A := A)
      (Finsupp.single y (z * x) + Finsupp.single x (z * y) -
        Finsupp.single (x * y) z) : affineTwoForms (R := R) (S := A)) :
          affineDeRhamAlgebra R A) = 0
  rw [LinearMap.map_sub, LinearMap.map_add]
  change
    ((affineD1Precursor (R := R) (A := A) (Finsupp.single y (z * x)) :
        affineTwoForms (R := R) (S := A)) : affineDeRhamAlgebra R A) +
      ((affineD1Precursor (R := R) (A := A) (Finsupp.single x (z * y)) :
        affineTwoForms (R := R) (S := A)) : affineDeRhamAlgebra R A) -
      ((affineD1Precursor (R := R) (A := A) (Finsupp.single (x * y) z) :
        affineTwoForms (R := R) (S := A)) : affineDeRhamAlgebra R A) = 0
  rw [affineD1Precursor_apply_single_coe, affineD1Precursor_apply_single_coe,
    affineD1Precursor_apply_single_coe]
  exact sub_eq_zero.mpr
    (affineDeRhamD0_mul_generator_relation (R := R) (A := A) x y z)

theorem affineD1Precursor_kerTotal_le_ker :
    (KaehlerDifferential.kerTotal R A).restrictScalars R ≤
      LinearMap.ker (affineD1Precursor (R := R) (A := A)) := by
  intro ξ hξ
  change affineD1Precursor (R := R) (A := A) ξ = 0
  change ξ ∈ KaehlerDifferential.kerTotal R A at hξ
  rw [KaehlerDifferential.kerTotal] at hξ
  let G : Set (A →₀ A) :=
    (((Set.range fun x : A × A =>
        Finsupp.single x.1 (1 : A) + Finsupp.single x.2 1 -
          Finsupp.single (x.1 + x.2) 1) ∪
      Set.range fun x : A × A =>
        Finsupp.single x.2 x.1 + Finsupp.single x.1 x.2 -
          Finsupp.single (x.1 * x.2) 1) ∪
      Set.range fun x : R =>
        Finsupp.single (algebraMap R A x) (1 : A))
  have hspan :
      ∀ η ∈ Submodule.span A G, ∀ a : A,
        affineD1Precursor (R := R) (A := A) (a • η) = 0 := by
    intro η hη
    refine Submodule.span_induction (R := A) (s := G)
      (p := fun η _ => ∀ a : A, affineD1Precursor (R := R) (A := A) (a • η) = 0) ?_ ?_ ?_ ?_ hη
    · intro η hη a
      rcases hη with (⟨⟨x, y⟩, rfl⟩ | ⟨⟨x, y⟩, rfl⟩) | ⟨r, rfl⟩
      · rw [smul_sub, smul_add, Finsupp.smul_single, Finsupp.smul_single,
          Finsupp.smul_single, smul_eq_mul, mul_one]
        change affineD1Precursor (R := R) (A := A)
          (Finsupp.single x a + Finsupp.single y a - Finsupp.single (x + y) a) = 0
        exact affineD1Precursor_kerTotal_add_generator (R := R) (A := A) x y a
      · rw [smul_sub, smul_add, Finsupp.smul_single, Finsupp.smul_single,
          Finsupp.smul_single, smul_eq_mul]
        change affineD1Precursor (R := R) (A := A)
          (Finsupp.single y (a * x) + Finsupp.single x (a * y) -
            Finsupp.single (x * y) (a * (1 : A))) = 0
        rw [mul_one]
        change affineD1Precursor (R := R) (A := A)
          (Finsupp.single y (a * x) + Finsupp.single x (a * y) -
            Finsupp.single (x * y) a) = 0
        exact affineD1Precursor_kerTotal_mul_generator (R := R) (A := A) x y a
      · rw [Finsupp.smul_single, smul_eq_mul, mul_one]
        change affineD1Precursor (R := R) (A := A)
          (Finsupp.single (algebraMap R A r) a) = 0
        exact affineD1Precursor_kerTotal_algebraMap_generator (R := R) (A := A) r a
    · intro a
      exact map_zero (affineD1Precursor (R := R) (A := A))
    · intro η₁ η₂ hη₁ hη₂ ih₁ ih₂ a
      rw [smul_add, LinearMap.map_add, ih₁ a, ih₂ a, add_zero]
    · intro b η hη ih a
      rw [smul_smul]
      exact ih (a * b)
  have h := hspan ξ hξ 1
  rw [one_smul] at h
  exact h

end Map

end Realization
end Boundary
