import Mathlib.RingTheory.RingHom.StandardSmooth

universe u v w t w'

namespace Boundary

namespace _root_.Algebra

theorem algebra_isStandardSmooth_of_equiv
    {R : Type u} [CommRing R] {A : Type v} [CommRing A] {B : Type w} [CommRing B]
    [Algebra R A] [Algebra R B]
  (e : A ≃ₐ[R] B)
  [Algebra.IsStandardSmooth.{t, w'} R A] :
    RingHom.IsStandardSmooth.{t, w'} (algebraMap R B) := by
  letI : Algebra A B := e.toRingHom.toAlgebra
  haveI : IsScalarTower R A B := IsScalarTower.of_algHom e.toAlgHom
  have hAB : Algebra.IsStandardSmooth.{t, w'} A B :=
    (Algebra.IsStandardSmoothOfRelativeDimension.of_algebraMap_bijective e.bijective).isStandardSmooth
  haveI : Algebra.IsStandardSmooth.{t, w'} A B := hAB
  have hRB : Algebra.IsStandardSmooth.{t, w'} R B := by
    exact (Algebra.IsStandardSmooth.trans (R := R) (S := A) (T := B))
  have hAlgEq : (algebraMap R B).toAlgebra = (‹Algebra R B› : Algebra R B) := by
    ext r x
    change (algebraMap R B r) * x = r • x
    rw [Algebra.smul_def]
  rw [RingHom.IsStandardSmooth, hAlgEq]
  exact hRB

theorem algebra_isStandardSmoothOfRelativeDimension_of_equiv
    {R : Type u} [CommRing R] {A : Type v} [CommRing A] {B : Type w} [CommRing B]
    [Algebra R A] [Algebra R B]
  (n : ℕ)
  (e : A ≃ₐ[R] B)
  [Algebra.IsStandardSmoothOfRelativeDimension.{t, w'} n R A] :
    RingHom.IsStandardSmoothOfRelativeDimension.{t, w'} n (algebraMap R B) := by
  letI : Algebra A B := e.toRingHom.toAlgebra
  haveI : IsScalarTower R A B := IsScalarTower.of_algHom e.toAlgHom
  have hAB : Algebra.IsStandardSmoothOfRelativeDimension.{t, w'} 0 A B :=
    Algebra.IsStandardSmoothOfRelativeDimension.of_algebraMap_bijective e.bijective
  haveI : Algebra.IsStandardSmoothOfRelativeDimension.{t, w'} 0 A B := hAB
  have hRB : Algebra.IsStandardSmoothOfRelativeDimension.{t, w'} n R B := by
    have hTrans : Algebra.IsStandardSmoothOfRelativeDimension.{t, w'} (0 + n) R B :=
      Algebra.IsStandardSmoothOfRelativeDimension.trans (R := R) (S := A) (T := B)
        (n := n) (m := 0)
    rw [Nat.zero_add] at hTrans
    exact hTrans
  have hAlgEq : (algebraMap R B).toAlgebra = (‹Algebra R B› : Algebra R B) := by
    ext r x
    change (algebraMap R B r) * x = r • x
    rw [Algebra.smul_def]
  rw [RingHom.IsStandardSmoothOfRelativeDimension, hAlgEq]
  exact hRB

end _root_.Algebra

end Boundary
