import Boundary.LFunctions.EulerFactor
import Mathlib.FieldTheory.RatFunc.Basic

/-!
# Cohomological Euler factors

This file builds the first graded layer above `LinearEulerFactor`.  It remains
purely finite-dimensional linear algebra: a finite set of cohomological degrees
is assigned vector spaces and endomorphisms, and the local zeta factor is the
usual alternating product

`∏ᵢ det(1 - T Fᵢ)^((-1)^(i+1))`.

Since `LinearEulerFactor.eulerPolynomial` is `det(1 - T F)`, odd degrees appear
in the numerator and even degrees in the denominator.
-/

open scoped BigOperators

universe u v w

namespace Boundary
namespace CohomologicalEulerFactor

noncomputable section

open LinearEulerFactor

variable {K : Type u} [Field K]
variable {V : ℤ → Type v} {W : ℤ → Type w}
variable [∀ i, AddCommGroup (V i)] [∀ i, Module K (V i)]
variable [∀ i, FiniteDimensional K (V i)]
variable [∀ i, AddCommGroup (W i)] [∀ i, Module K (W i)]
variable [∀ i, FiniteDimensional K (W i)]

/-- Odd cohomological degrees contribute to the numerator of the local zeta
factor for the convention `det(1 - T F)`. -/
def localNumerator (degrees : Finset ℤ) (F : ∀ i, Module.End K (V i)) :
    Polynomial K :=
  ∏ i in degrees.filter (fun i => Odd i), eulerPolynomial (F i)

/-- Even cohomological degrees contribute to the denominator of the local zeta
factor for the convention `det(1 - T F)`. -/
def localDenominator (degrees : Finset ℤ) (F : ∀ i, Module.End K (V i)) :
    Polynomial K :=
  ∏ i in degrees.filter (fun i => Even i), eulerPolynomial (F i)

/-- The cohomological local zeta factor as a rational function.

The convention is
`∏ᵢ det(1 - T Fᵢ)^((-1)^(i+1))`, so odd degrees are in the numerator and even
degrees are in the denominator. -/
def localZetaFactorRatFunc (degrees : Finset ℤ) (F : ∀ i, Module.End K (V i)) :
    RatFunc K :=
  algebraMap (Polynomial K) (RatFunc K) (localNumerator (V := V) degrees F) /
    algebraMap (Polynomial K) (RatFunc K) (localDenominator (V := V) degrees F)

/-- Numerators are invariant under degreewise linear conjugacy. -/
@[simp]
theorem localNumerator_conj (degrees : Finset ℤ)
    (F : ∀ i, Module.End K (V i)) (e : ∀ i, V i ≃ₗ[K] W i) :
    localNumerator (V := W) degrees (fun i => (e i).conj (F i)) =
      localNumerator (V := V) degrees F := by
  simp [localNumerator, eulerPolynomial_conj]

/-- Denominators are invariant under degreewise linear conjugacy. -/
@[simp]
theorem localDenominator_conj (degrees : Finset ℤ)
    (F : ∀ i, Module.End K (V i)) (e : ∀ i, V i ≃ₗ[K] W i) :
    localDenominator (V := W) degrees (fun i => (e i).conj (F i)) =
      localDenominator (V := V) degrees F := by
  simp [localDenominator, eulerPolynomial_conj]

/-- The rational local zeta factor is invariant under degreewise linear
conjugacy. -/
@[simp]
theorem localZetaFactorRatFunc_conj (degrees : Finset ℤ)
    (F : ∀ i, Module.End K (V i)) (e : ∀ i, V i ≃ₗ[K] W i) :
    localZetaFactorRatFunc (V := W) degrees (fun i => (e i).conj (F i)) =
      localZetaFactorRatFunc (V := V) degrees F := by
  simp [localZetaFactorRatFunc]

/-- The numerator is normalized to evaluate to `1` at `T = 0`. -/
@[simp]
theorem localNumerator_eval_zero (degrees : Finset ℤ)
    (F : ∀ i, Module.End K (V i)) :
    (localNumerator (V := V) degrees F).eval 0 = 1 := by
  rw [localNumerator, Polynomial.eval_prod]
  exact Finset.prod_eq_one fun i _ => by
    simpa [eulerFactor] using eulerFactor_zero (F i)

/-- The denominator is normalized to evaluate to `1` at `T = 0`. -/
@[simp]
theorem localDenominator_eval_zero (degrees : Finset ℤ)
    (F : ∀ i, Module.End K (V i)) :
    (localDenominator (V := V) degrees F).eval 0 = 1 := by
  rw [localDenominator, Polynomial.eval_prod]
  exact Finset.prod_eq_one fun i _ => by
    simpa [eulerFactor] using eulerFactor_zero (F i)

/-- Numerators multiply for degreewise product endomorphisms. -/
@[simp]
theorem localNumerator_prodMap (degrees : Finset ℤ)
    (F : ∀ i, Module.End K (V i)) (G : ∀ i, Module.End K (W i)) :
    localNumerator (V := fun i => V i × W i) degrees
        (fun i => (F i).prodMap (G i)) =
      localNumerator (V := V) degrees F * localNumerator (V := W) degrees G := by
  simp [localNumerator, eulerPolynomial_prodMap, Finset.prod_mul_distrib]

/-- Denominators multiply for degreewise product endomorphisms. -/
@[simp]
theorem localDenominator_prodMap (degrees : Finset ℤ)
    (F : ∀ i, Module.End K (V i)) (G : ∀ i, Module.End K (W i)) :
    localDenominator (V := fun i => V i × W i) degrees
        (fun i => (F i).prodMap (G i)) =
      localDenominator (V := V) degrees F * localDenominator (V := W) degrees G := by
  simp [localDenominator, eulerPolynomial_prodMap, Finset.prod_mul_distrib]

/-- Rational local zeta factors multiply for degreewise product endomorphisms. -/
@[simp]
theorem localZetaFactorRatFunc_prodMap (degrees : Finset ℤ)
    (F : ∀ i, Module.End K (V i)) (G : ∀ i, Module.End K (W i)) :
    localZetaFactorRatFunc (V := fun i => V i × W i) degrees
        (fun i => (F i).prodMap (G i)) =
      localZetaFactorRatFunc (V := V) degrees F *
        localZetaFactorRatFunc (V := W) degrees G := by
  simp [localZetaFactorRatFunc, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm]

end

end CohomologicalEulerFactor
end Boundary
