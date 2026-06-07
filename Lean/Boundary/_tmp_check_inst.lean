import Mathlib.RingTheory.Smooth.StandardSmooth
import Mathlib.Algebra.Polynomial.Basic

namespace Boundary

noncomputable section

namespace _root_.Algebra

example (A : Type*) [CommRing A] :
    Algebra.IsStandardSmoothOfRelativeDimension 1 A (MvPolynomial (Fin 1) A) := by
  infer_instance

example (R : Type*) [CommRing R] (n : ℕ) :
    Algebra.IsStandardSmoothOfRelativeDimension n R (MvPolynomial (Fin n) R) := by
  infer_instance

example (R : Type*) [CommRing R] :
    Algebra.IsStandardSmooth R (MvPolynomial (Fin 1) R) := by
  infer_instance

example (R : Type*) [CommRing R] (σ : Type*) [Finite σ] :
    Algebra.IsStandardSmooth R (MvPolynomial σ R) := by
  infer_instance

end _root_.Algebra

end Boundary
