import Mathlib.RingTheory.RingHom.StandardSmooth

set_option autoImplicit false

example
    {R A B : Type*} [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B]
    (e : A ≃ₐ[R] B) :
    SMul A B := by
  letI : Algebra A B := (e.toRingHom).toAlgebra
  infer_instance
