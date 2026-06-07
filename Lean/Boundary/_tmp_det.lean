import Mathlib.LinearAlgebra.Determinant
import Mathlib.Algebra.Polynomial.Basic

example (A : Type*) [CommRing A] :
    True := by
  let hQ : ((PEmpty → A) →ₗ[A] (PEmpty → A)) := 0
  letI : Subsingleton (PEmpty → A) := by infer_instance
  have hdet : LinearMap.det hQ = (1:A) := by
    exact (LinearMap.det_eq_one_of_subsingleton (f := hQ))
  exact True.intro
