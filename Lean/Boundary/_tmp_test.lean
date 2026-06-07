import Mathlib

universe u v w

example {R : Type u} [CommRing R] {A : Type v} [CommRing A] {B : Type w} [CommRing B]
  [Algebra R A] [Algebra R B]
  (e : A ≃ₐ[R] B) :
  (e.toRingHom.comp (algebraMap R A)).toAlgebra = (algebraMap R B).toAlgebra := by
  -- try ext
  ext r
  -- goal?
  simp [RingHom.comp_apply, e.commutes]
