import Boundary.LFunctions.EulerFactor
import Mathlib.Data.Matrix.Block
import Mathlib.FieldTheory.RatFunc.Basic

/-!
# Endomorphism object core

This file owns the basic finite-dimensional endomorphism-object layer and the
primitive trace/determinant compatibility lemmas.
-/

universe u v

namespace Boundary
namespace EndomorphismK0

noncomputable section

open LinearEulerFactor

variable (K : Type u) [Field K]

instance : AddCommGroup PUnit where
  add _ _ := PUnit.unit
  add_assoc _ _ _ := rfl
  zero := PUnit.unit
  zero_add _ := rfl
  add_zero _ := rfl
  neg _ := PUnit.unit
  sub _ _ := PUnit.unit
  sub_eq_add_neg _ _ := rfl
  nsmul _ _ := PUnit.unit
  zsmul _ _ := PUnit.unit
  neg_add_cancel _ := rfl
  add_comm _ _ := rfl

instance : Module K PUnit where
  smul _ _ := PUnit.unit
  one_smul _ := rfl
  mul_smul _ _ _ := rfl
  smul_zero _ := rfl
  smul_add _ _ _ := rfl
  add_smul _ _ _ := rfl
  zero_smul _ := rfl

instance : FiniteDimensional K PUnit := by
  infer_instance

/-- A finite-dimensional `K`-vector space equipped with an endomorphism. -/
structure EndomorphismObject where
  carrier : Type v
  addCommGroup : AddCommGroup carrier
  module : Module K carrier
  finiteDimensional : FiniteDimensional K carrier
  endomorphism : Module.End K carrier

attribute [instance] EndomorphismObject.addCommGroup
attribute [instance] EndomorphismObject.module
attribute [instance] EndomorphismObject.finiteDimensional

/-- An endomorphism object whose carrier is the zero vector space. -/
def IsZeroObject (A : EndomorphismObject.{u, v} K) : Prop :=
  Subsingleton A.carrier

namespace EndomorphismObject

variable {K}

/-- Transport an endomorphism object across a linear equivalence. -/
def conj (A : EndomorphismObject K) {B : EndomorphismObject K}
    (e : A.carrier ≃ₗ[K] B.carrier) : EndomorphismObject K :=
  { carrier := B.carrier
    addCommGroup := B.addCommGroup
    module := B.module
    finiteDimensional := B.finiteDimensional
    endomorphism := e.conj A.endomorphism }

/-- If transporting the endomorphism along a linear equivalence gives the
target endomorphism, the conjugated object is equal to the target object. -/
theorem conj_eq {A B : EndomorphismObject K} (e : A.carrier ≃ₗ[K] B.carrier)
    (h : e.conj A.endomorphism = B.endomorphism) :
    conj A e = B := by
  cases A
  cases B
  cases e
  simp [conj] at h ⊢
  exact h

/-- Direct sum/product of finite-dimensional endomorphism objects. -/
def product (A B : EndomorphismObject K) : EndomorphismObject K where
  carrier := A.carrier × B.carrier
  addCommGroup := inferInstance
  module := inferInstance
  finiteDimensional := inferInstance
  endomorphism := A.endomorphism.prodMap B.endomorphism

/-- The same finite-dimensional space with the `n`th power of its
endomorphism. -/
def power (A : EndomorphismObject K) (n : ℕ) : EndomorphismObject K where
  carrier := A.carrier
  addCommGroup := inferInstance
  module := inferInstance
  finiteDimensional := inferInstance
  endomorphism := A.endomorphism ^ n

/-- The determinant character value as a rational function. -/
def determinantRatFunc (A : EndomorphismObject K) : RatFunc K :=
  algebraMap (Polynomial K) (RatFunc K) (eulerPolynomial A.endomorphism)

/-- The Euler polynomial of an endomorphism object is nonzero because its
constant coefficient is `1`. -/
theorem eulerPolynomial_coeff_zero (A : EndomorphismObject K) :
    (eulerPolynomial A.endomorphism).coeff 0 = 1 := by
  simpa [LinearEulerFactor.eulerPolynomial, Polynomial.reverse] using
    LinearEulerFactor.eulerPolynomial_coeff_zero A.endomorphism

theorem eulerPolynomial_ne_zero (A : EndomorphismObject K) :
    eulerPolynomial A.endomorphism ≠ 0 := by
  intro h
  have hcoeff := congrArg (fun p : Polynomial K => p.coeff 0) h
  simpa [eulerPolynomial_coeff_zero (K := K) A] using hcoeff

/-- The determinant character value as a unit in the rational-function field. -/
def determinantUnit (A : EndomorphismObject K) : (RatFunc K)ˣ :=
  Units.mk0 (determinantRatFunc A)
    (RatFunc.algebraMap_ne_zero (eulerPolynomial_ne_zero A))

/-- A zero-object endomorphism has determinant unit `1`. -/
theorem determinantUnit_zeroObject (A : EndomorphismObject.{u, v} K)
    (hA : Subsingleton A.carrier) : EndomorphismObject.determinantUnit A = 1 := by
  haveI : Subsingleton A.carrier := hA
  have hfin : Module.finrank K A.carrier = 0 :=
    Module.finrank_zero_of_subsingleton
  have hchar :
      LinearMap.charpoly A.endomorphism = 1 := by
    rw [LinearMap.charpoly_def]
    rw [Matrix.charpoly]
    rw [Matrix.det_of_card_zero]
    rw [← Module.finrank_eq_card_chooseBasisIndex]
    exact hfin
  have hrev : Polynomial.reverse (1 : Polynomial K) = 1 := by
    ext n
    simp [Polynomial.reverse]
  ext
  simp [EndomorphismObject.determinantUnit, EndomorphismObject.determinantRatFunc,
    LinearEulerFactor.eulerPolynomial, hchar, hrev]

/-- The trace of the `n`th power of the endomorphism. -/
def tracePower (n : ℕ) (A : EndomorphismObject K) : K :=
  LinearMap.trace K A.carrier (A.endomorphism ^ n)

/-- Powers of product endomorphisms are product maps of powers. -/
theorem endomorphism_product_pow (A B : EndomorphismObject K) (n : ℕ) :
    (product A B).endomorphism ^ n =
      (A.endomorphism ^ n).prodMap (B.endomorphism ^ n) := by
  induction n with
  | zero =>
      ext x
      rfl
  | succ n ih =>
      rw [pow_succ]
      rw [ih]
      ext x
      rfl

/-- Taking powers commutes with direct sums of endomorphism objects. -/
theorem power_product (A B : EndomorphismObject K) (n : ℕ) :
    power (product A B) n = product (power A n) (power B n) := by
  have h := endomorphism_product_pow A B n
  simpa [power, product] using h

@[simp]
theorem power_one (A : EndomorphismObject K) :
    power A 1 = A := by
  cases A
  rfl

/-- Conjugation commutes with taking powers at the endomorphism level. -/
theorem conj_pow (n : ℕ) (A : EndomorphismObject K) {B : EndomorphismObject K}
    (e : A.carrier ≃ₗ[K] B.carrier) :
    (e.conj A.endomorphism) ^ n = e.conj (A.endomorphism ^ n) := by
  induction n with
  | zero =>
      ext x
      simp [LinearEquiv.conj_apply]
  | succ n ih =>
      ext x
      calc
        (e.conj A.endomorphism ^ (n + 1)) x = ((e.conj A.endomorphism ^ n) * (e.conj A.endomorphism)) x := by
          simp [pow_succ]
        _ = (e.conj (A.endomorphism ^ n) * e.conj A.endomorphism) x := by rw [ih]
        _ = (e.conj (A.endomorphism ^ n * A.endomorphism)) x := by
          simp [LinearEquiv.conj_apply, LinearMap.comp_assoc]
        _ = (e.conj (A.endomorphism ^ (n + 1))) x := by
          simp [pow_succ]

/-- Iterating the power operation multiplies exponents. -/
theorem power_power (A : EndomorphismObject K) (m n : ℕ) :
    power (power A m) n = power A (m * n) := by
  simpa [power] using (pow_mul (A.endomorphism) m n).symm

@[simp]
theorem tracePower_one_power (A : EndomorphismObject K) (n : ℕ) :
    tracePower 1 (power A n) = tracePower n A := by
  rfl

/-- Determinants multiply under direct sums. -/
@[simp]
theorem determinantRatFunc_product (A B : EndomorphismObject K) :
    determinantRatFunc (product A B) = determinantRatFunc A * determinantRatFunc B := by
  simpa [determinantRatFunc, product] using
    congrArg (algebraMap (Polynomial K) (RatFunc K))
      (eulerPolynomial_prodMap (A.endomorphism) (B.endomorphism))

/-- Determinant units multiply under direct sums. -/
@[simp]
theorem determinantUnit_product (A B : EndomorphismObject K) :
    determinantUnit (product A B) = determinantUnit A * determinantUnit B := by
  ext
  exact determinantRatFunc_product A B

/-- First traces add under direct sums. -/
@[simp]
theorem tracePower_one_product (A B : EndomorphismObject K) :
    tracePower 1 (product A B) = tracePower 1 A + tracePower 1 B := by
  simpa [tracePower, product] using LinearMap.trace_prodMap' A.endomorphism B.endomorphism

/-- Trace powers add under direct sums. -/
@[simp]
theorem tracePower_product (A B : EndomorphismObject K) (n : ℕ) :
    tracePower n (product A B) = tracePower n A + tracePower n B := by
  rw [tracePower, endomorphism_product_pow]
  exact LinearMap.trace_prodMap' (A.endomorphism ^ n) (B.endomorphism ^ n)

@[simp]
theorem determinantUnit_conj (A : EndomorphismObject K) {B : EndomorphismObject K}
    (e : A.carrier ≃ₗ[K] B.carrier) :
    determinantUnit (conj A e) = determinantUnit A := by
  ext
  simp [determinantUnit, determinantRatFunc, conj, LinearEulerFactor.eulerPolynomial_conj]

@[simp]
theorem tracePower_conj (n : ℕ) (A : EndomorphismObject K) {B : EndomorphismObject K}
    (e : A.carrier ≃ₗ[K] B.carrier) :
    tracePower n (conj A e) = tracePower n A := by
  rw [tracePower]
  have h := EndomorphismObject.conj_pow n A e
  change LinearMap.trace K B.carrier ((e.conj A.endomorphism) ^ n) =
    LinearMap.trace K A.carrier (A.endomorphism ^ n)
  rw [h]
  exact LinearMap.trace_conj' (A.endomorphism ^ n) e

end EndomorphismObject

end

end EndomorphismK0
end Boundary
