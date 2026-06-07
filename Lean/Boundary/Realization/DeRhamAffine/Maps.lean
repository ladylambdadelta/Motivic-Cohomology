import Boundary.Realization.DeRhamAffine.FirstPiece
import Boundary.ExteriorAlgebra.OfAlternating
import Mathlib.RingTheory.Kaehler.Basic
import Mathlib.LinearAlgebra.ExteriorAlgebra.Basic
import Mathlib.LinearAlgebra.ExteriorAlgebra.Grading

universe u

noncomputable section

open scoped TensorProduct
open scoped ModuleCat

namespace Boundary
namespace Realization

variable (R S : Type u)
variable [CommRing R] [CommRing S] [Algebra R S]

section Map

variable {A B C : Type u}
variable [CommRing A] [CommRing B] [CommRing C]
variable [Algebra R A] [Algebra R B] [Algebra R C]

/-- The induced algebra map on affine differential forms, using the universal property of the
exterior algebra over the source algebra. -/
noncomputable def affineDeRhamAlgebraMap (f : A →ₐ[R] B) :
    letI : Algebra A (affineDeRhamAlgebra R B) :=
      Algebra.compHom (affineDeRhamAlgebra R B) f.toRingHom
    affineDeRhamAlgebra R A →ₐ[A] affineDeRhamAlgebra R B := by
  letI : Algebra A B := f.toAlgebra
  letI : Algebra A (affineDeRhamAlgebra R B) :=
    Algebra.compHom (affineDeRhamAlgebra R B) f.toRingHom
  letI : Module A (affineFirstDeRhamPiece R B) :=
    Module.compHom (affineFirstDeRhamPiece R B) f.toRingHom
  let g : affineFirstDeRhamPiece R A →ₗ[A] affineDeRhamAlgebra R B :=
    ((affineDeRhamι R B).restrictScalars A).comp
      (affineFirstDeRhamPieceMap (R := R) f)
  have hg : ∀ x : affineFirstDeRhamPiece R A, g x * g x = 0 := by
    intro x
    change (affineDeRhamι R B (affineFirstDeRhamPieceMap (R := R) f x)) *
        (affineDeRhamι R B (affineFirstDeRhamPieceMap (R := R) f x)) = 0
    exact ExteriorAlgebra.ι_sq_zero
      (R := B) (M := affineFirstDeRhamPiece R B) (affineFirstDeRhamPieceMap (R := R) f x)
  exact ExteriorAlgebra.lift A ⟨g, hg⟩

theorem affineDeRhamAlgebraMap_apply_ι (f : A →ₐ[R] B)
    (x : affineFirstDeRhamPiece R A) :
    affineDeRhamAlgebraMap (R := R) f (affineDeRhamι R A x) =
      affineDeRhamι R B (affineFirstDeRhamPieceMap (R := R) f x) := by
  letI : Algebra A B := f.toAlgebra
  letI : Algebra A (affineDeRhamAlgebra R B) :=
    Algebra.compHom (affineDeRhamAlgebra R B) f.toRingHom
  letI : Module A (affineFirstDeRhamPiece R B) :=
    Module.compHom (affineFirstDeRhamPiece R B) f.toRingHom
  let g : affineFirstDeRhamPiece R A →ₗ[A] affineDeRhamAlgebra R B :=
    ((affineDeRhamι R B).restrictScalars A).comp
      (affineFirstDeRhamPieceMap (R := R) f)
  change ExteriorAlgebra.lift A ⟨g, ?_⟩ (ExteriorAlgebra.ι A x) =
      affineDeRhamι R B (affineFirstDeRhamPieceMap (R := R) f x)
  exact ExteriorAlgebra.lift_ι_apply (R := A) (M := affineFirstDeRhamPiece R A)
    (A := affineDeRhamAlgebra R B) g
    (by
      intro y
      change (affineDeRhamι R B (affineFirstDeRhamPieceMap (R := R) f y)) *
          (affineDeRhamι R B (affineFirstDeRhamPieceMap (R := R) f y)) = 0
      exact ExteriorAlgebra.ι_sq_zero
        (R := B) (M := affineFirstDeRhamPiece R B) (affineFirstDeRhamPieceMap (R := R) f y)) x

/-- The induced exterior-algebra map preserves exterior degree. -/
theorem affineDeRhamAlgebraMap_mem_exteriorPower
    (f : A →ₐ[R] B) (n : ℕ) {ω : affineDeRhamAlgebra R A}
    (hω : ω ∈ (⋀[A]^n (affineFirstDeRhamPiece R A) :
        Submodule A (affineDeRhamAlgebra R A))) :
    affineDeRhamAlgebraMap (R := R) f ω ∈
      (⋀[B]^n (affineFirstDeRhamPiece R B) :
        Submodule B (affineDeRhamAlgebra R B)) := by
  letI : Algebra A B := f.toAlgebra
  letI : Algebra A (affineDeRhamAlgebra R B) :=
    Algebra.compHom (affineDeRhamAlgebra R B) f.toRingHom
  letI : Module A (affineFirstDeRhamPiece R B) :=
    Module.compHom (affineFirstDeRhamPiece R B) f.toRingHom
  let F : affineDeRhamAlgebra R A →ₐ[A] affineDeRhamAlgebra R B :=
    affineDeRhamAlgebraMap (R := R) f
  let sourceOne :
      Submodule A (affineDeRhamAlgebra R A) :=
    LinearMap.range (affineDeRhamι R A)
  let targetOne :
      Submodule B (affineDeRhamAlgebra R B) :=
    LinearMap.range (affineDeRhamι R B)
  change ω ∈ sourceOne ^ n at hω
  change F ω ∈ targetOne ^ n
  induction hω using Submodule.pow_induction_on_left' with
  | algebraMap a =>
      change F (algebraMap A (affineDeRhamAlgebra R A) a) ∈ targetOne ^ 0
      rw [F.commutes]
      change algebraMap B (affineDeRhamAlgebra R B) (f a) ∈ targetOne ^ 0
      rw [pow_zero]
      exact Submodule.algebraMap_mem
        (R := B) (A := affineDeRhamAlgebra R B) (f a)
  | add x y i hx hy ihx ihy =>
      rw [map_add F]
      exact Submodule.add_mem (targetOne ^ i) ihx ihy
  | mem_mul m hm i x hx ih =>
      rw [map_mul F]
      have hmTarget : F m ∈ targetOne := by
        rcases hm with ⟨η, rfl⟩
        change affineDeRhamAlgebraMap (R := R) f
            (affineDeRhamι R A η) ∈ targetOne
        rw [affineDeRhamAlgebraMap_apply_ι]
        exact LinearMap.mem_range_self (affineDeRhamι R B)
          (affineFirstDeRhamPieceMap (R := R) f η)
      exact (pow_succ' targetOne i).symm ▸ Submodule.mul_mem_mul hmTarget ih

/-- The induced map on affine `n`-forms. -/
noncomputable def affineFormsMap (n : ℕ) (f : A →ₐ[R] B) :
    affineForms (R := R) (S := A) n →ₗ[R]
      affineForms (R := R) (S := B) n := by
  letI : Algebra A B := f.toAlgebra
  letI : Algebra A (affineDeRhamAlgebra R B) :=
    Algebra.compHom (affineDeRhamAlgebra R B) f.toRingHom
  letI : Module A (affineFirstDeRhamPiece R B) :=
    Module.compHom (affineFirstDeRhamPiece R B) f.toRingHom
  let F : affineDeRhamAlgebra R A →ₐ[A] affineDeRhamAlgebra R B :=
    affineDeRhamAlgebraMap (R := R) f
  refine
    { toFun := fun ω =>
        ⟨F (ω : affineDeRhamAlgebra R A),
          affineDeRhamAlgebraMap_mem_exteriorPower (R := R) f n ω.property⟩
      map_add' := ?_
      map_smul' := ?_ }
  · intro ω η
    apply Subtype.ext
    exact map_add F (ω : affineDeRhamAlgebra R A) η
  · intro r ω
    apply Subtype.ext
    exact LinearMap.map_smul_of_tower
      F.toLinearMap r
      (ω : affineDeRhamAlgebra R A)

theorem affineFormsMap_apply_coe
    (n : ℕ) (f : A →ₐ[R] B) (ω : affineForms (R := R) (S := A) n) :
    ((affineFormsMap (R := R) n f ω : affineForms (R := R) (S := B) n) :
      affineDeRhamAlgebra R B) =
      affineDeRhamAlgebraMap (R := R) f ω :=
  rfl

/-- The induced map on affine one-forms. -/
noncomputable abbrev affineOneFormsMap (f : A →ₐ[R] B) :
    affineOneForms R A →ₗ[R] affineOneForms R B :=
  affineFormsMap (R := R) 1 f

/-- The induced map on affine two-forms. -/
noncomputable abbrev affineTwoFormsMap (f : A →ₐ[R] B) :
    affineTwoForms R A →ₗ[R] affineTwoForms R B :=
  affineFormsMap (R := R) 2 f

end Map

end Realization
end Boundary
