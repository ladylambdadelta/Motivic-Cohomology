import Mathlib.LinearAlgebra.Charpoly.ToMatrix
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
import Mathlib.LinearAlgebra.Trace

/-!
# Algebraic Euler factors

This file starts the Boundary L-functions stack at the linear-algebra layer.
For a finite-dimensional endomorphism `F`, the Euler polynomial is the
basis-free reverse characteristic polynomial, i.e. the polynomial represented
in a basis by `det(1 - T F)`.

This is the linear-algebra convention underlying cohomological local factors;
cf. Serre, *Zeta and L Functions*, §1, and Milne, *Étale Cohomology*, VI.13.
-/

universe u v w

namespace Boundary
namespace LinearEulerFactor

noncomputable section

open Polynomial

variable {K : Type u} [Field K]
variable {V : Type v} {W : Type w}
variable [AddCommGroup V] [Module K V] [FiniteDimensional K V]
variable [AddCommGroup W] [Module K W] [FiniteDimensional K W]

/-- The algebraic Euler polynomial of a finite-dimensional endomorphism.

This is the reverse characteristic polynomial. In coordinates it is
`det (1 - T • F)`, so it is the local-factor polynomial before inversion; cf.
Serre, *Zeta and L Functions*, §1. -/
def eulerPolynomial (F : Module.End K V) : K[X] :=
  F.charpoly.reverse

/-- The scalar Euler factor obtained by evaluating the Euler polynomial. -/
def eulerFactor (F : Module.End K V) (T : K) : K :=
  (eulerPolynomial F).eval T

@[simp]
theorem eulerFactor_def (F : Module.End K V) (T : K) :
    eulerFactor F T = (eulerPolynomial F).eval T :=
  rfl

/-- The constant term of the Euler polynomial is `1`. -/
@[simp]
theorem eulerPolynomial_coeff_zero (F : Module.End K V) :
    (eulerPolynomial F).coeff 0 = 1 := by
  exact (Polynomial.coeff_zero_reverse (F.charpoly)).trans
    (LinearMap.charpoly_monic F).leadingCoeff

/-- The Euler factor is normalized to be `1` at `T = 0`. -/
@[simp]
theorem eulerFactor_zero (F : Module.End K V) :
    eulerFactor F 0 = 1 := by
  exact (Polynomial.coeff_zero_eq_eval_zero (eulerPolynomial F)).symm.trans
    (eulerPolynomial_coeff_zero F)

/-- The first nonconstant coefficient of `det(1 - T F)` is minus the trace of `F`. -/
theorem eulerPolynomial_coeff_one_trace (F : Module.End K V) :
    (eulerPolynomial F).coeff 1 = - LinearMap.trace K V F := by
  let b := Module.Free.chooseBasis K V
  have hchar :
      F.charpoly.reverse = (LinearMap.toMatrix b b F).charpoly.reverse := by
    exact congrArg Polynomial.reverse (LinearMap.charpoly_toMatrix (b := b) F)
  calc
    (eulerPolynomial F).coeff 1 = ((LinearMap.toMatrix b b F).charpoly.reverse).coeff 1 := by
      exact congrArg (fun p : K[X] => p.coeff 1) hchar
    _ = ((LinearMap.toMatrix b b F).charpolyRev).coeff 1 := by
      exact congrArg (fun p : K[X] => p.coeff 1) (Matrix.reverse_charpoly (LinearMap.toMatrix b b F))
    _ = - Matrix.trace (LinearMap.toMatrix b b F) := by
      exact Matrix.coeff_charpolyRev_eq_neg_trace (LinearMap.toMatrix b b F)
    _ = - LinearMap.trace K V F := by
      exact congrArg Neg.neg (LinearMap.trace_eq_matrix_trace K b F).symm

/-- The Euler polynomial has degree at most the dimension of the vector space. -/
theorem eulerPolynomial_natDegree_le (F : Module.End K V) :
    (eulerPolynomial F).natDegree ≤ Module.finrank K V := by
  exact le_trans F.charpoly.reverse_natDegree_le
    (le_of_eq (LinearMap.charpoly_natDegree F))

/-- The Euler polynomial is invariant under linear conjugacy. -/
theorem eulerPolynomial_conj (e : V ≃ₗ[K] W) (F : Module.End K V) :
    eulerPolynomial (e.conj F) = eulerPolynomial F := by
  exact congrArg Polynomial.reverse (LinearEquiv.charpoly_conj e F)

/-- The scalar Euler factor is invariant under linear conjugacy. -/
theorem eulerFactor_conj (e : V ≃ₗ[K] W) (F : Module.End K V) (T : K) :
    eulerFactor (e.conj F) T = eulerFactor F T := by
  exact congrArg (fun p : K[X] => p.eval T) (eulerPolynomial_conj e F)

/-- Euler polynomials multiply under product endomorphisms. -/
theorem eulerPolynomial_prodMap
    (F : Module.End K V) (G : Module.End K W) :
    eulerPolynomial (F.prodMap G) =
      eulerPolynomial F * eulerPolynomial G := by
  have hF : F.charpoly.leadingCoeff = 1 := (LinearMap.charpoly_monic F).leadingCoeff
  have hG : G.charpoly.leadingCoeff = 1 := (LinearMap.charpoly_monic G).leadingCoeff
  have hF0 : F.charpoly.leadingCoeff ≠ 0 := by
    intro h
    exact one_ne_zero (hF.symm.trans h)
  have hG0 : G.charpoly.leadingCoeff ≠ 0 := by
    intro h
    exact one_ne_zero (hG.symm.trans h)
  calc
    eulerPolynomial (F.prodMap G) = (F.charpoly * G.charpoly).reverse := by
      exact congrArg Polynomial.reverse (LinearMap.charpoly_prodMap F G)
    _ = eulerPolynomial F * eulerPolynomial G := by
      exact Polynomial.reverse_mul (mul_ne_zero hF0 hG0)

/-- Scalar Euler factors multiply under product endomorphisms. -/
theorem eulerFactor_prodMap
    (F : Module.End K V) (G : Module.End K W) (T : K) :
    eulerFactor (F.prodMap G) T = eulerFactor F T * eulerFactor G T := by
  calc
    eulerFactor (F.prodMap G) T = (eulerPolynomial (F.prodMap G)).eval T := by
      rfl
    _ = ((eulerPolynomial F * eulerPolynomial G).eval T) := by
      exact congrArg (fun p : K[X] => p.eval T) (eulerPolynomial_prodMap F G)
    _ = eulerFactor F T * eulerFactor G T := by
      exact Polynomial.eval_mul

end

end LinearEulerFactor
end Boundary
