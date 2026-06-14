import Boundary.LFunctionsRootedTreeFinal.OutsideRHRootedImportCone.EndomorphismK0.backup.EulerFactor.Owner
import Mathlib.Data.Matrix.Block
import Mathlib.FieldTheory.RatFunc.Basic

/-!
# Endomorphism object core

This file owns the basic finite-dimensional endomorphism-object layer and the
primitive trace/determinant compatibility lemmas.
-/

universe u v w

namespace Boundary
namespace EndomorphismK0

noncomputable section

open LinearEulerFactor

variable (K : Type u) [Field K]

def punitAddCommGroup : AddCommGroup PUnit where
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

instance : AddCommGroup PUnit :=
  punitAddCommGroup

def punitModule : Module K PUnit where
  smul _ _ := PUnit.unit
  one_smul _ := rfl
  mul_smul _ _ _ := rfl
  smul_zero _ := rfl
  smul_add _ _ _ := rfl
  add_smul _ _ _ := rfl
  zero_smul _ := rfl

instance : Module K PUnit :=
  punitModule K

def punitFiniteDimensional : FiniteDimensional K PUnit :=
  Module.finite_of_rank_eq_nat (R := K) (M := PUnit)
    (show Module.rank K PUnit = 0 from rank_punit K)

instance : FiniteDimensional K PUnit :=
  punitFiniteDimensional K

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

noncomputable def productFiniteDimensional (A B : EndomorphismObject K) :
    FiniteDimensional K (A.carrier × B.carrier) :=
  Module.Finite.of_basis
    ((Module.Free.chooseBasis K A.carrier).prod
      (Module.Free.chooseBasis K B.carrier))

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
  cases B with
  | mk carrier addCommGroup module finiteDimensional endomorphism =>
      exact congrArg
        (fun T =>
          ({ carrier := carrier
             addCommGroup := addCommGroup
             module := module
             finiteDimensional := finiteDimensional
             endomorphism := T } : EndomorphismObject K))
        h

/-- Direct sum/product of finite-dimensional endomorphism objects. -/
def product (A B : EndomorphismObject K) : EndomorphismObject K where
  carrier := A.carrier × B.carrier
  addCommGroup := Prod.instAddCommGroup
  module := Prod.instModule
  finiteDimensional := productFiniteDimensional A B
  endomorphism := A.endomorphism.prodMap B.endomorphism

/-- The same finite-dimensional space with the `n`th power of its
endomorphism. -/
def power (A : EndomorphismObject K) (n : ℕ) : EndomorphismObject K where
  carrier := A.carrier
  addCommGroup := A.addCommGroup
  module := A.module
  finiteDimensional := A.finiteDimensional
  endomorphism := A.endomorphism ^ n

/-- The determinant character value as a rational function. -/
def determinantRatFunc (A : EndomorphismObject K) : RatFunc K :=
  algebraMap (Polynomial K) (RatFunc K) (eulerPolynomial A.endomorphism)

/-- The Euler polynomial of an endomorphism object is nonzero because its
constant coefficient is `1`. -/
theorem eulerPolynomial_coeff_zero (A : EndomorphismObject K) :
    (eulerPolynomial A.endomorphism).coeff 0 = 1 := by
  exact LinearEulerFactor.eulerPolynomial_coeff_zero A.endomorphism

theorem eulerPolynomial_ne_zero (A : EndomorphismObject K) :
    eulerPolynomial A.endomorphism ≠ 0 := by
  intro h
  exact one_ne_zero
    (Eq.trans (eulerPolynomial_coeff_zero (K := K) A).symm
      (Eq.trans (congrArg (fun p : Polynomial K => p.coeff 0) h) rfl))

/-- The determinant character value as a unit in the rational-function field. -/
def determinantUnit (A : EndomorphismObject K) : (RatFunc K)ˣ :=
  Units.mk0 (determinantRatFunc A)
    (RatFunc.algebraMap_ne_zero (eulerPolynomial_ne_zero A))

theorem matrix_charpoly_eq_charmatrix_det {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : Matrix ι ι K) :
    Matrix.charpoly M = (Matrix.charmatrix M).det := by
  rfl

theorem charpoly_eq_one_of_subsingleton (A : EndomorphismObject.{u, v} K)
    (hA : Subsingleton A.carrier) :
    LinearMap.charpoly A.endomorphism = 1 := by
  letI : Subsingleton A.carrier := hA
  exact Eq.trans
    (LinearMap.charpoly_def A.endomorphism)
    (Eq.trans
      (matrix_charpoly_eq_charmatrix_det
        (K := K)
        (LinearMap.toMatrix (Module.Free.chooseBasis K A.carrier)
          (Module.Free.chooseBasis K A.carrier) A.endomorphism))
      (Matrix.det_of_card_zero
        (Eq.trans (Module.finrank_eq_card_chooseBasisIndex K A.carrier).symm
          (Module.finrank_zero_of_subsingleton : Module.finrank K A.carrier = 0))
        _))

theorem polynomial_reverse_one : Polynomial.reverse (1 : Polynomial K) = 1 := by
  exact Eq.trans
    (congrArg Polynomial.reverse (Polynomial.C_1.symm : (1 : Polynomial K) = Polynomial.C 1))
    (Eq.trans (Polynomial.reverse_C (1 : K)) Polynomial.C_1)

theorem eulerPolynomial_eq_one_of_subsingleton (A : EndomorphismObject.{u, v} K)
    (hA : Subsingleton A.carrier) :
    eulerPolynomial A.endomorphism = 1 := by
  exact Eq.trans
    (congrArg Polynomial.reverse (charpoly_eq_one_of_subsingleton (K := K) A hA))
    (polynomial_reverse_one (K := K))

theorem determinantRatFunc_eq_one_of_subsingleton (A : EndomorphismObject.{u, v} K)
    (hA : Subsingleton A.carrier) :
    determinantRatFunc A = 1 := by
  exact Eq.trans
    (congrArg (algebraMap (Polynomial K) (RatFunc K))
      (eulerPolynomial_eq_one_of_subsingleton (K := K) A hA))
    (map_one (algebraMap (Polynomial K) (RatFunc K)))

/-- A zero-object endomorphism has determinant unit `1`. -/
theorem determinantUnit_zeroObject (A : EndomorphismObject.{u, v} K)
    (hA : Subsingleton A.carrier) : EndomorphismObject.determinantUnit A = 1 := by
  ext
  exact determinantRatFunc_eq_one_of_subsingleton (K := K) A hA

/-- The trace of the `n`th power of the endomorphism. -/
def tracePower (n : ℕ) (A : EndomorphismObject K) : K :=
  LinearMap.trace K A.carrier (A.endomorphism ^ n)

theorem prodMap_pow_zero
    {L : Type v} {M : Type w}
    [AddCommGroup L] [Module K L] [AddCommGroup M] [Module K M]
    (F : Module.End K L) (G : Module.End K M) :
    (F.prodMap G) ^ 0 = (F ^ 0).prodMap (G ^ 0) := by
  exact LinearMap.ext (fun x => Prod.ext rfl rfl)

theorem prodMap_mul
    {L : Type v} {M : Type w}
    [AddCommGroup L] [Module K L] [AddCommGroup M] [Module K M]
    (F F' : Module.End K L) (G G' : Module.End K M) :
    F.prodMap G * F'.prodMap G' = (F * F').prodMap (G * G') := by
  exact LinearMap.ext (fun x => Prod.ext rfl rfl)

/-- Powers of product endomorphisms are product maps of powers. -/
theorem endomorphism_product_pow (A B : EndomorphismObject K) (n : ℕ) :
    (product A B).endomorphism ^ n =
      (A.endomorphism ^ n).prodMap (B.endomorphism ^ n) := by
  change (A.endomorphism.prodMap B.endomorphism) ^ n =
    (A.endomorphism ^ n).prodMap (B.endomorphism ^ n)
  induction n with
  | zero =>
      exact prodMap_pow_zero (K := K) (L := A.carrier) (M := B.carrier)
        A.endomorphism B.endomorphism
  | succ n ih =>
      exact Eq.trans
        (pow_succ (A.endomorphism.prodMap B.endomorphism) n)
        (Eq.trans
          (congrArg (fun T => T * A.endomorphism.prodMap B.endomorphism) ih)
          (Eq.trans
            (prodMap_mul (K := K) (L := A.carrier) (M := B.carrier)
              (A.endomorphism ^ n) A.endomorphism
              (B.endomorphism ^ n) B.endomorphism)
            (congrArg₂ LinearMap.prodMap
              (pow_succ A.endomorphism n).symm
              (pow_succ B.endomorphism n).symm)))

/-- Taking powers commutes with direct sums of endomorphism objects. -/
theorem power_product (A B : EndomorphismObject K) (n : ℕ) :
    power (product A B) n = product (power A n) (power B n) := by
  exact congrArg
    (fun T => ({ product A B with endomorphism := T } : EndomorphismObject K))
    (endomorphism_product_pow A B n)

@[simp]
theorem power_one (A : EndomorphismObject K) :
    power A 1 = A := by
  cases A
  rfl

theorem linearEquiv_conj_pow_zero
    {L : Type v} {M : Type w}
    [AddCommGroup L] [Module K L] [AddCommGroup M] [Module K M]
    (e : L ≃ₗ[K] M) (F : Module.End K L) :
    (e.conj F) ^ 0 = e.conj (F ^ 0) := by
  exact LinearMap.ext (fun x => (e.apply_symm_apply x).symm)

theorem linearEquiv_conj_mul
    {L : Type v} {M : Type w}
    [AddCommGroup L] [Module K L] [AddCommGroup M] [Module K M]
    (e : L ≃ₗ[K] M) (F G : Module.End K L) :
    e.conj (F * G) = e.conj F * e.conj G := by
  exact Eq.trans
    (LinearEquiv.conj_comp e G F)
    (congrArg₂ LinearMap.comp rfl rfl)

theorem linearEquiv_conj_pow_succ
    {L : Type v} {M : Type w}
    [AddCommGroup L] [Module K L] [AddCommGroup M] [Module K M]
    (e : L ≃ₗ[K] M) (F : Module.End K L) (n : ℕ)
    (h : (e.conj F) ^ n = e.conj (F ^ n)) :
    (e.conj F) ^ (n + 1) = e.conj (F ^ (n + 1)) := by
  exact Eq.trans
    (pow_succ (e.conj F) n)
    (Eq.trans
      (congrArg (fun T => T * e.conj F) h)
      (Eq.trans
        (linearEquiv_conj_mul (K := K) e (F ^ n) F).symm
        (congrArg (e.conj) (pow_succ F n).symm)))

/-- Conjugation commutes with taking powers at the endomorphism level. -/
theorem conj_pow (n : ℕ) (A : EndomorphismObject K) {B : EndomorphismObject K}
    (e : A.carrier ≃ₗ[K] B.carrier) :
    (e.conj A.endomorphism) ^ n = e.conj (A.endomorphism ^ n) := by
  induction n with
  | zero =>
      exact linearEquiv_conj_pow_zero
        (K := K) (L := A.carrier) (M := B.carrier) e A.endomorphism
  | succ n ih =>
      exact linearEquiv_conj_pow_succ
        (K := K) (L := A.carrier) (M := B.carrier) e A.endomorphism n ih

/-- Iterating the power operation multiplies exponents. -/
theorem power_power (A : EndomorphismObject K) (m n : ℕ) :
    power (power A m) n = power A (m * n) := by
  cases A with
  | mk carrier addCommGroup module finiteDimensional endomorphism =>
      exact congrArg
        (fun T =>
          ({ carrier := carrier
             addCommGroup := addCommGroup
             module := module
             finiteDimensional := finiteDimensional
             endomorphism := T } : EndomorphismObject K))
        (pow_mul endomorphism m n).symm

@[simp]
theorem tracePower_one_power (A : EndomorphismObject K) (n : ℕ) :
    tracePower 1 (power A n) = tracePower n A := by
  rfl

/-- Determinants multiply under direct sums. -/
@[simp]
theorem determinantRatFunc_product (A B : EndomorphismObject K) :
    determinantRatFunc (product A B) = determinantRatFunc A * determinantRatFunc B := by
  change algebraMap (Polynomial K) (RatFunc K)
      (eulerPolynomial (A.endomorphism.prodMap B.endomorphism)) =
    algebraMap (Polynomial K) (RatFunc K) (eulerPolynomial A.endomorphism) *
      algebraMap (Polynomial K) (RatFunc K) (eulerPolynomial B.endomorphism)
  exact Eq.trans
    (congrArg (algebraMap (Polynomial K) (RatFunc K))
      (eulerPolynomial_prodMap (A.endomorphism) (B.endomorphism)))
    (map_mul (algebraMap (Polynomial K) (RatFunc K))
      (eulerPolynomial A.endomorphism) (eulerPolynomial B.endomorphism))

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
  change LinearMap.trace K (A.carrier × B.carrier)
      (A.endomorphism.prodMap B.endomorphism) =
    LinearMap.trace K A.carrier A.endomorphism +
      LinearMap.trace K B.carrier B.endomorphism
  exact LinearMap.trace_prodMap' A.endomorphism B.endomorphism

/-- Trace powers add under direct sums. -/
@[simp]
theorem tracePower_product (A B : EndomorphismObject K) (n : ℕ) :
    tracePower n (product A B) = tracePower n A + tracePower n B := by
  change LinearMap.trace K (A.carrier × B.carrier) ((product A B).endomorphism ^ n) =
    LinearMap.trace K A.carrier (A.endomorphism ^ n) +
      LinearMap.trace K B.carrier (B.endomorphism ^ n)
  exact Eq.trans
    (congrArg (LinearMap.trace K (A.carrier × B.carrier)) (endomorphism_product_pow A B n))
    (LinearMap.trace_prodMap' (A.endomorphism ^ n) (B.endomorphism ^ n))

@[simp]
theorem determinantUnit_conj (A : EndomorphismObject K) {B : EndomorphismObject K}
    (e : A.carrier ≃ₗ[K] B.carrier) :
    determinantUnit (conj A e) = determinantUnit A := by
  ext
  change determinantRatFunc (conj A e) = determinantRatFunc A
  exact congrArg (algebraMap (Polynomial K) (RatFunc K))
    (LinearEulerFactor.eulerPolynomial_conj e A.endomorphism)

@[simp]
theorem tracePower_conj (n : ℕ) (A : EndomorphismObject K) {B : EndomorphismObject K}
    (e : A.carrier ≃ₗ[K] B.carrier) :
    tracePower n (conj A e) = tracePower n A := by
  change LinearMap.trace K B.carrier ((e.conj A.endomorphism) ^ n) =
    LinearMap.trace K A.carrier (A.endomorphism ^ n)
  exact Eq.trans
    (congrArg (LinearMap.trace K B.carrier) (EndomorphismObject.conj_pow n A e))
    (LinearMap.trace_conj' (A.endomorphism ^ n) e)

end EndomorphismObject

end

end EndomorphismK0
end Boundary
