import Mathlib.LinearAlgebra.Determinant

example (A : Type) [CommRing A] :
    let f : ((PEmpty → A) →ₗ[A] (PEmpty → A)) := 0
    f.det = (1:A) := by
  intro f
  exact (LinearMap.det_eq_one_of_subsingleton (R := A) (M := PEmpty → A) f)
