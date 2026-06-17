import Boundary.LFunctionsRootedTreeCanonicalAll._outside_RH_rooted_import_cone.EndomorphismK0.backup.EulerFactor.EulerFactor
import Mathlib.Data.Matrix.Block
import Mathlib.FieldTheory.RatFunc.Basic
import Mathlib.GroupTheory.FreeAbelianGroup
import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.Algebra.Exact

/-!
# Virtual finite-dimensional endomorphism classes

This file starts the conceptual owner layer beneath cohomological local factors.
It packages finite-dimensional vector spaces equipped with an endomorphism and
builds the free virtual abelian group on those objects.

The direct-sum relation is recorded as an explicit element, and the determinant
and first trace characters are proved to kill it, so both descend to the
direct-sum quotient.
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
  have h := LinearEulerFactor.eulerPolynomial_coeff_zero A.endomorphism
  simp [LinearEulerFactor.eulerPolynomial, Polynomial.reverse] at h ⊢

theorem eulerPolynomial_ne_zero (A : EndomorphismObject K) :
    eulerPolynomial A.endomorphism ≠ 0 := by
  intro h
  have hcoeff := congrArg (fun p : Polynomial K => p.coeff 0) h
  rw [eulerPolynomial_coeff_zero (K := K) A] at hcoeff
  simp at hcoeff

/-- The determinant character value as a unit in the rational-function field. -/
def determinantUnit (A : EndomorphismObject K) : (RatFunc K)ˣ :=
  Units.mk0 (determinantRatFunc A)
    (RatFunc.algebraMap_ne_zero (eulerPolynomial_ne_zero A))

/-- A zero-object endomorphism has determinant unit `1`. -/
theorem determinantUnit_zeroObject (A : EndomorphismObject.{u, v} K)
    (hA : IsZeroObject K A) : EndomorphismObject.determinantUnit A = 1 := by
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
  cases A
  cases B
  exact h

@[simp]
theorem power_one (A : EndomorphismObject K) :
    power A 1 = A := by
  cases A
  ext
  · rfl
  · exact pow_one _

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
  cases A
  ext
  · rfl
  · exact pow_mul _ _ _

@[simp]
theorem tracePower_one_power (A : EndomorphismObject K) (n : ℕ) :
    tracePower 1 (power A n) = tracePower n A := by
  rfl

/-- Determinants multiply under direct sums. -/
@[simp]
theorem determinantRatFunc_product (A B : EndomorphismObject K) :
    determinantRatFunc (product A B) = determinantRatFunc A * determinantRatFunc B := by
  exact congrArg (algebraMap (Polynomial K) (RatFunc K))
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
  exact LinearMap.trace_prodMap' A.endomorphism B.endomorphism

/-- Trace powers add under direct sums. -/
@[simp]
theorem tracePower_product (A B : EndomorphismObject K) (n : ℕ) :
    tracePower n (product A B) = tracePower n A + tracePower n B := by
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

/-- The free virtual abelian group on finite-dimensional endomorphism objects. -/
abbrev VirtualEndomorphism :=
  FreeAbelianGroup (EndomorphismObject.{u, v} K)

/-- Generator class of a finite-dimensional endomorphism object. -/
def of (A : EndomorphismObject.{u, v} K) : VirtualEndomorphism K :=
  FreeAbelianGroup.of A

/-- The chosen zero object in the endomorphism category. -/
def zeroObject : EndomorphismObject.{u, v} K where
  carrier := PUnit.{v + 1}
  addCommGroup := inferInstance
  module := inferInstance
  finiteDimensional := inferInstance
  endomorphism := 0

/-- An endomorphism object whose carrier is the zero vector space. -/
def IsZeroObject (A : EndomorphismObject.{u, v} K) : Prop :=
  Subsingleton A.carrier

/-- The direct-sum relation element `[A ⊕ B] - [A] - [B]`. -/
def directSumRelation (A B : EndomorphismObject.{u, v} K) : VirtualEndomorphism K :=
  of K (EndomorphismObject.product A B) - of K A - of K B

/-- The conjugacy relation element `[B, e A e⁻¹] - [A]`. -/
def conjRelation (A : EndomorphismObject.{u, v} K) {B : EndomorphismObject.{u, v} K}
    (e : A.carrier ≃ₗ[K] B.carrier) : VirtualEndomorphism K :=
  of K (EndomorphismObject.conj A e) - of K A

/-- The subgroup generated by direct-sum relations, conjugacy relations, and
the chosen zero object. -/
def directSumSubgroup : AddSubgroup (VirtualEndomorphism K) :=
  AddSubgroup.closure
    {x | (∃ A B : EndomorphismObject.{u, v} K, x = directSumRelation K A B) ∨
      (∃ A B : EndomorphismObject.{u, v} K, ∃ e : A.carrier ≃ₗ[K] B.carrier,
        x = conjRelation K A e) ∨
      ∃ A : EndomorphismObject.{u, v} K, IsZeroObject K A ∧ x = of K A}

/-- The direct-sum Grothendieck quotient of finite-dimensional endomorphism
objects. -/
abbrev K0 :=
  VirtualEndomorphism K ⧸ directSumSubgroup K

/-- Quotient map from the free virtual group to the direct-sum quotient. -/
def mk : VirtualEndomorphism K →+ K0 K :=
  QuotientAddGroup.mk' (directSumSubgroup K)

/-- The direct-sum relation lies in the subgroup it generates. -/
theorem directSumRelation_mem_directSumSubgroup (A B : EndomorphismObject.{u, v} K) :
    directSumRelation K A B ∈
      (directSumSubgroup K : AddSubgroup (VirtualEndomorphism K)) := by
  change directSumRelation K A B ∈
      AddSubgroup.closure
        {x : VirtualEndomorphism K |
          (∃ A B : EndomorphismObject.{u, v} K, x = directSumRelation K A B) ∨
            (∃ A B : EndomorphismObject.{u, v} K, ∃ e : A.carrier ≃ₗ[K] B.carrier,
              x = conjRelation K A e) ∨
            ∃ A : EndomorphismObject.{u, v} K, IsZeroObject K A ∧ x = of K A}
  exact AddSubgroup.subset_closure (Or.inl ⟨A, B, rfl⟩)

/-- Conjugacy relations lie in the subgroup. -/
theorem conjRelation_mem_directSumSubgroup
    (A : EndomorphismObject.{u, v} K) {B : EndomorphismObject.{u, v} K}
    (e : A.carrier ≃ₗ[K] B.carrier) :
    conjRelation K A e ∈
      (directSumSubgroup K : AddSubgroup (VirtualEndomorphism K)) := by
  change conjRelation K A e ∈
      AddSubgroup.closure
        {x : VirtualEndomorphism K |
          (∃ A B : EndomorphismObject.{u, v} K, x = directSumRelation K A B) ∨
            (∃ A B : EndomorphismObject.{u, v} K, ∃ e : A.carrier ≃ₗ[K] B.carrier,
              x = conjRelation K A e) ∨
            ∃ A : EndomorphismObject.{u, v} K, IsZeroObject K A ∧ x = of K A}
  exact AddSubgroup.subset_closure (Or.inr <| Or.inl ⟨A, B, e, rfl⟩)

/-- Zero-object generators lie in the subgroup. -/
theorem zeroObject_mem_directSumSubgroup (A : EndomorphismObject.{u, v} K)
    (hA : IsZeroObject K A) :
    of K A ∈
      (directSumSubgroup K : AddSubgroup (VirtualEndomorphism K)) := by
  change of K A ∈
      AddSubgroup.closure
        {x : VirtualEndomorphism K |
          (∃ A B : EndomorphismObject.{u, v} K, x = directSumRelation K A B) ∨
            (∃ A B : EndomorphismObject.{u, v} K, ∃ e : A.carrier ≃ₗ[K] B.carrier,
              x = conjRelation K A e) ∨
            ∃ A : EndomorphismObject.{u, v} K, IsZeroObject K A ∧ x = of K A}
  exact AddSubgroup.subset_closure (Or.inr (Or.inr ⟨A, hA, rfl⟩))

@[simp]
theorem mk_directSumRelation (A B : EndomorphismObject.{u, v} K) :
    mk K (directSumRelation K A B) = 0 := by
  change (directSumRelation K A B : K0 K) = 0
  exact (QuotientAddGroup.eq_zero_iff
    (N := directSumSubgroup K) (directSumRelation K A B)).2
      (directSumRelation_mem_directSumSubgroup K A B)

@[simp]
theorem mk_zeroObject_of_isZero (A : EndomorphismObject.{u, v} K)
    (hA : IsZeroObject K A) :
    mk K (of K A) = (0 : K0 K) := by
  change (of K A : K0 K) = 0
  exact (QuotientAddGroup.eq_zero_iff
    (N := directSumSubgroup K) (of K A)).2
      (zeroObject_mem_directSumSubgroup K A hA)

@[simp]
theorem mk_zeroObject :
    mk K (of K (zeroObject K)) = (0 : K0 K) := by
  exact mk_zeroObject_of_isZero K (zeroObject K)
    (by
      change Subsingleton PUnit
      infer_instance)

/-- In the quotient, a direct sum is the sum of the two classes. -/
theorem mk_directSum_eq_add (A B : EndomorphismObject.{u, v} K) :
    mk K (of K (EndomorphismObject.product A B)) = mk K (of K A) + mk K (of K B) := by
  apply eq_of_sub_eq_zero
  calc
    mk K (of K (EndomorphismObject.product A B)) - (mk K (of K A) + mk K (of K B))
        = mk K (of K (EndomorphismObject.product A B)) - mk K (of K A + of K B) := by
          exact congrArg (fun z : K0 K => mk K (of K (EndomorphismObject.product A B)) - z)
            (map_add (mk K) (of K A) (of K B))
    _ = mk K (of K (EndomorphismObject.product A B) - (of K A + of K B)) := by
          exact (map_sub (mk K) (of K (EndomorphismObject.product A B))
            (of K A + of K B)).symm
    _ = mk K (directSumRelation K A B) := by
          congr 1
          exact (sub_add_eq_sub_sub (of K (EndomorphismObject.product A B)) (of K A) (of K B)).symm
    _ = 0 := mk_directSumRelation K A B

/-- Conjugate endomorphism objects have the same class in `K0`. -/
@[simp]
theorem mk_conj_eq_mk (A : EndomorphismObject.{u, v} K) {B : EndomorphismObject.{u, v} K}
    (e : A.carrier ≃ₗ[K] B.carrier) :
    mk K (of K (EndomorphismObject.conj A e)) = mk K (of K A) := by
  apply eq_of_sub_eq_zero
  calc
    mk K (of K (EndomorphismObject.conj A e)) - mk K (of K A)
        = mk K (of K (EndomorphismObject.conj A e) - of K A) := by
            rfl
    _ = mk K (conjRelation K A e) := by
          rfl
    _ = 0 := by
      exact (QuotientAddGroup.eq_zero_iff
        (N := directSumSubgroup K) (conjRelation K A e)).2
          (conjRelation_mem_directSumSubgroup K A e)

/-- The determinant character on the free virtual group, valued additively in
the unit group of `RatFunc K`. -/
def determinantCharacter : VirtualEndomorphism K →+ Additive ((RatFunc K)ˣ) :=
  FreeAbelianGroup.lift fun A => Additive.ofMul (EndomorphismObject.determinantUnit A)

@[simp]
theorem determinantCharacter_of (A : EndomorphismObject.{u, v} K) :
    determinantCharacter K (of K A) =
      Additive.ofMul (EndomorphismObject.determinantUnit A) := by
  rfl

/-- The determinant character kills the direct-sum relation. -/
@[simp]
theorem determinantCharacter_directSumRelation (A B : EndomorphismObject.{u, v} K) :
    determinantCharacter K (directSumRelation K A B) = 0 := by
  calc
    determinantCharacter K (directSumRelation K A B)
        = determinantCharacter K (of K (EndomorphismObject.product A B)) -
            determinantCharacter K (of K A) -
            determinantCharacter K (of K B) := by
          rfl
    _ = Additive.ofMul (EndomorphismObject.determinantUnit (EndomorphismObject.product A B)) -
          Additive.ofMul (EndomorphismObject.determinantUnit A) -
          Additive.ofMul (EndomorphismObject.determinantUnit B) := by
          rw [determinantCharacter_of, determinantCharacter_of, determinantCharacter_of]
    _ = 0 := by
          exact sub_eq_zero.mpr (by
            simp [EndomorphismObject.determinantUnit_product])

theorem determinantCharacter_conjRelation
    (A : EndomorphismObject.{u, v} K) {B : EndomorphismObject.{u, v} K}
    (e : A.carrier ≃ₗ[K] B.carrier) :
    determinantCharacter K (conjRelation K A e) = 0 := by
  calc
    determinantCharacter K (conjRelation K A e)
        = determinantCharacter K (of K (EndomorphismObject.conj A e)) -
            determinantCharacter K (of K A) := by
          rfl
    _ = Additive.ofMul (EndomorphismObject.determinantUnit (EndomorphismObject.conj A e)) -
          Additive.ofMul (EndomorphismObject.determinantUnit A) := by
          rw [determinantCharacter_of, determinantCharacter_of]
    _ = 0 := by
          exact sub_eq_zero.mpr (by
            exact congrArg Additive.ofMul (EndomorphismObject.determinantUnit_conj A e))

@[simp]
theorem determinantCharacter_zeroObject (A : EndomorphismObject.{u, v} K)
    (hA : IsZeroObject K A) :
    determinantCharacter K (of K A) = 0 := by
  rw [determinantCharacter_of, determinantUnit_zeroObject (K := K) A hA]
  rfl

/-- The determinant character kills the subgroup generated by direct-sum
relations. -/
theorem directSumSubgroup_le_determinantCharacter_ker :
    directSumSubgroup K ≤ (determinantCharacter K).ker := by
  rw [directSumSubgroup, AddSubgroup.closure_le]
  rintro x (⟨A, B, rfl⟩ | ⟨A, B, e, rfl⟩ | ⟨A, hA, rfl⟩)
  · change determinantCharacter K (directSumRelation K A B) = 0
    exact determinantCharacter_directSumRelation K A B
  · change determinantCharacter K (conjRelation K A e) = 0
    exact determinantCharacter_conjRelation K A e
  · exact determinantCharacter_zeroObject K A hA

/-- The determinant character descended to the direct-sum quotient. Its target
is written additively because the quotient source is an additive group. -/
def determinantCharacterK0 : K0 K →+ Additive ((RatFunc K)ˣ) :=
  QuotientAddGroup.lift (directSumSubgroup K) (determinantCharacter K)
    (directSumSubgroup_le_determinantCharacter_ker K)

/-- Multiplicative form of the determinant character on the direct-sum
quotient. -/
def determinantCharacterK0Mul : Multiplicative (K0 K) →* (RatFunc K)ˣ where
  toFun x := Additive.toMul (determinantCharacterK0 K (Multiplicative.toAdd x))
  map_one' := by
    simp [determinantCharacterK0]
  map_mul' x y := by
    simp [determinantCharacterK0]

@[simp]
theorem determinantCharacterK0_mk (x : VirtualEndomorphism K) :
    determinantCharacterK0 K (mk K x) = determinantCharacter K x := by
  exact QuotientAddGroup.lift_mk (directSumSubgroup K)
    (directSumSubgroup_le_determinantCharacter_ker K) x

@[simp]
theorem determinantCharacterK0_of (A : EndomorphismObject.{u, v} K) :
    determinantCharacterK0 K (mk K (of K A)) =
      Additive.ofMul (EndomorphismObject.determinantUnit A) := by
  exact determinantCharacterK0_mk (K := K) (of K A)

@[simp]
theorem determinantCharacterK0Mul_of (A : EndomorphismObject.{u, v} K) :
    determinantCharacterK0Mul K (Multiplicative.ofAdd (mk K (of K A))) =
      EndomorphismObject.determinantUnit A := by
  change Additive.toMul (determinantCharacterK0 K (mk K (of K A))) =
    EndomorphismObject.determinantUnit A
  rw [determinantCharacterK0_of (K := K) A]
  rfl

/-- The trace-power character on the free virtual group. -/
def traceCharacter (n : ℕ) : VirtualEndomorphism K →+ K :=
  FreeAbelianGroup.lift fun A => EndomorphismObject.tracePower n A

/-- A zero-object endomorphism has vanishing trace powers. -/
theorem tracePower_zeroObject (n : ℕ) (A : EndomorphismObject.{u, v} K)
    (hA : IsZeroObject K A) : EndomorphismObject.tracePower n A = 0 := by
  haveI : Subsingleton A.carrier := hA
  have hfin : Module.finrank K A.carrier = 0 :=
    Module.finrank_zero_of_subsingleton
  change EndomorphismObject.tracePower n A = 0
  by_cases hn : n = 0
  · subst n
    simp [EndomorphismObject.tracePower, LinearMap.trace_one, hfin]
  · have hpow : A.endomorphism ^ n = 0 := by
      ext x
      exact Subsingleton.elim _ _
    simp [EndomorphismObject.tracePower, hpow]

@[simp]
theorem traceCharacter_of (n : ℕ) (A : EndomorphismObject.{u, v} K) :
    traceCharacter K n (of K A) = EndomorphismObject.tracePower n A := by
  rfl

/-- The trace-power character kills the direct-sum relation. -/
@[simp]
theorem traceCharacter_directSumRelation (n : ℕ) (A B : EndomorphismObject.{u, v} K) :
    traceCharacter K n (directSumRelation K A B) = 0 := by
  calc
    traceCharacter K n (directSumRelation K A B)
        = traceCharacter K n (of K (EndomorphismObject.product A B)) -
            traceCharacter K n (of K A) -
            traceCharacter K n (of K B) := by
          rfl
    _ = EndomorphismObject.tracePower n (EndomorphismObject.product A B) -
          EndomorphismObject.tracePower n A -
          EndomorphismObject.tracePower n B := by
          rw [traceCharacter_of, traceCharacter_of, traceCharacter_of]
    _ = 0 := by
          exact sub_eq_zero.mpr (by
            simp [EndomorphismObject.tracePower_product])

theorem traceCharacter_conjRelation (n : ℕ) (A : EndomorphismObject.{u, v} K)
    {B : EndomorphismObject.{u, v} K} (e : A.carrier ≃ₗ[K] B.carrier) :
    traceCharacter K n (conjRelation K A e) = 0 := by
  calc
    traceCharacter K n (conjRelation K A e)
        = traceCharacter K n (of K (EndomorphismObject.conj A e)) -
            traceCharacter K n (of K A) := by
          rfl
    _ = EndomorphismObject.tracePower n (EndomorphismObject.conj A e) -
          EndomorphismObject.tracePower n A := by
          rw [traceCharacter_of, traceCharacter_of]
    _ = 0 := by
          exact sub_eq_zero.mpr (EndomorphismObject.tracePower_conj n A e)

@[simp]
theorem traceCharacter_zeroObject (n : ℕ) (A : EndomorphismObject.{u, v} K)
    (hA : IsZeroObject K A) :
    traceCharacter K n (of K A) = 0 := by
  rw [traceCharacter_of]
  exact tracePower_zeroObject (K := K) n A hA

/-- The first trace character kills the direct-sum relation. -/
@[simp]
theorem traceCharacter_one_directSumRelation (A B : EndomorphismObject.{u, v} K) :
    traceCharacter K 1 (directSumRelation K A B) = 0 :=
  traceCharacter_directSumRelation K 1 A B

/-- The trace-power character kills the subgroup generated by direct-sum
relations. -/
theorem directSumSubgroup_le_traceCharacter_ker (n : ℕ) :
    directSumSubgroup K ≤ (traceCharacter K n).ker := by
  rw [directSumSubgroup, AddSubgroup.closure_le]
  rintro x (⟨A, B, rfl⟩ | ⟨A, B, e, rfl⟩ | ⟨A, hA, rfl⟩)
  · change traceCharacter K n (directSumRelation K A B) = 0
    exact traceCharacter_directSumRelation K n A B
  · change traceCharacter K n (conjRelation K A e) = 0
    exact traceCharacter_conjRelation K n A e
  · exact traceCharacter_zeroObject K n A hA

/-- The first trace character kills the subgroup generated by direct-sum
relations. -/
theorem directSumSubgroup_le_traceCharacter_one_ker :
    directSumSubgroup K ≤ (traceCharacter K 1).ker :=
  directSumSubgroup_le_traceCharacter_ker K 1

/-- The trace-power character descended to the direct-sum quotient. -/
def traceCharacterK0 (n : ℕ) : K0 K →+ K :=
  QuotientAddGroup.lift (directSumSubgroup K) (traceCharacter K n)
    (directSumSubgroup_le_traceCharacter_ker K n)

@[simp]
theorem traceCharacterK0_mk (n : ℕ) (x : VirtualEndomorphism K) :
    traceCharacterK0 K n (mk K x) = traceCharacter K n x := by
  exact QuotientAddGroup.lift_mk (directSumSubgroup K)
    (directSumSubgroup_le_traceCharacter_ker K n) x

@[simp]
theorem traceCharacterK0_of (n : ℕ) (A : EndomorphismObject.{u, v} K) :
    traceCharacterK0 K n (mk K (of K A)) = EndomorphismObject.tracePower n A := by
  exact traceCharacterK0_mk K n (of K A)

/-- The virtual power map `[V,F] ↦ [V,F^n]` on the free group. -/
def powerMapVirtual (n : ℕ) : VirtualEndomorphism K →+ VirtualEndomorphism K :=
  FreeAbelianGroup.lift fun A => of K (EndomorphismObject.power A n)

@[simp]
theorem powerMapVirtual_of (n : ℕ) (A : EndomorphismObject.{u, v} K) :
    powerMapVirtual K n (of K A) = of K (EndomorphismObject.power A n) := by
  simp [powerMapVirtual, of]

/-- The virtual power map sends direct-sum relations to direct-sum relations. -/
theorem powerMapVirtual_directSumRelation
    (n : ℕ) (A B : EndomorphismObject.{u, v} K) :
    powerMapVirtual K n (directSumRelation K A B) =
      directSumRelation K (EndomorphismObject.power A n)
        (EndomorphismObject.power B n) := by
  calc
    powerMapVirtual K n (directSumRelation K A B)
        = powerMapVirtual K n
            (of K (EndomorphismObject.product A B) - (of K A + of K B)) := by
          rfl
    _ = powerMapVirtual K n (of K (EndomorphismObject.product A B)) -
          powerMapVirtual K n (of K A + of K B) := by
          exact map_sub (powerMapVirtual K n) _ _
    _ = of K (EndomorphismObject.power (EndomorphismObject.product A B) n) -
          (powerMapVirtual K n (of K A) + powerMapVirtual K n (of K B)) := by
          congr 1
          exact map_add (powerMapVirtual K n) (of K A) (of K B)
    _ = of K (EndomorphismObject.product (EndomorphismObject.power A n)
            (EndomorphismObject.power B n)) -
          of K (EndomorphismObject.power A n) -
          of K (EndomorphismObject.power B n) := by
          congr 1
          exact EndomorphismObject.power_product A B n
    _ = directSumRelation K (EndomorphismObject.power A n)
        (EndomorphismObject.power B n) := by
          rfl

/-- The virtual power map carries a conjugacy relation to the conjugacy
relation of the powered endomorphism objects. -/
theorem powerMapVirtual_conjRelation
    (n : ℕ) (A : EndomorphismObject.{u, v} K) {B : EndomorphismObject.{u, v} K}
    (e : A.carrier ≃ₗ[K] B.carrier) :
    powerMapVirtual K n (conjRelation K A e) =
      conjRelation K (EndomorphismObject.power A n) e := by
  calc
    powerMapVirtual K n (conjRelation K A e)
        = powerMapVirtual K n (of K (EndomorphismObject.conj A e) - of K A) := by
          rfl
    _ = powerMapVirtual K n (of K (EndomorphismObject.conj A e)) -
          powerMapVirtual K n (of K A) := by
          exact map_sub (powerMapVirtual K n) _ _
    _ = of K (EndomorphismObject.power (EndomorphismObject.conj A e) n) -
          of K (EndomorphismObject.power A n) := by
          rw [powerMapVirtual_of, powerMapVirtual_of]
    _ = of K (EndomorphismObject.conj (EndomorphismObject.power A n) e) -
            of K (EndomorphismObject.power A n) := by
          rw [EndomorphismObject.conj_pow n A e]
    _ = conjRelation K (EndomorphismObject.power A n) e := by
          rfl

/-- The virtual power map sends conjugacy relations into the direct-sum
relation subgroup. -/
theorem powerMapVirtual_conjRelation_mem_directSumSubgroup
    (n : ℕ) (A : EndomorphismObject.{u, v} K) {B : EndomorphismObject.{u, v} K}
    (e : A.carrier ≃ₗ[K] B.carrier) :
    powerMapVirtual K n (conjRelation K A e) ∈ directSumSubgroup K := by
  rw [powerMapVirtual_conjRelation]
  exact conjRelation_mem_directSumSubgroup K (EndomorphismObject.power A n) e

/-- The virtual power map sends direct-sum relations into the direct-sum
relation subgroup. -/
theorem powerMapVirtual_directSumRelation_mem_directSumSubgroup
    (n : ℕ) (A B : EndomorphismObject.{u, v} K) :
    powerMapVirtual K n (directSumRelation K A B) ∈ directSumSubgroup K := by
  rw [powerMapVirtual_directSumRelation]
  exact directSumRelation_mem_directSumSubgroup K
    (EndomorphismObject.power A n) (EndomorphismObject.power B n)

theorem powerMapVirtual_zeroObject_mem_directSumSubgroup
    (n : ℕ) (A : EndomorphismObject.{u, v} K) (hA : IsZeroObject K A) :
    powerMapVirtual K n (of K A) ∈ directSumSubgroup K := by
  exact
    (powerMapVirtual_of (K := K) n A).symm ▸
      zeroObject_mem_directSumSubgroup K (EndomorphismObject.power A n) hA

/-- The virtual power map preserves the direct-sum relation subgroup. -/
theorem powerMapVirtual_directSumSubgroup_le (n : ℕ) :
    directSumSubgroup K ≤
      (directSumSubgroup K).comap (powerMapVirtual K n) := by
  rw [directSumSubgroup, AddSubgroup.closure_le]
  rintro x (⟨A, B, rfl⟩ | ⟨A, B, e, rfl⟩ | ⟨A, hA, rfl⟩)
  · exact powerMapVirtual_directSumRelation_mem_directSumSubgroup K n A B
  · exact powerMapVirtual_conjRelation_mem_directSumSubgroup K n A e
  · exact powerMapVirtual_zeroObject_mem_directSumSubgroup K n A hA

/-- The descended power operation on the direct-sum K₀ group. -/
def powerMapK0 (n : ℕ) : K0 K →+ K0 K :=
  QuotientAddGroup.lift (directSumSubgroup K)
    ((mk K).comp (powerMapVirtual K n))
    (by
      intro x hx
      exact (QuotientAddGroup.eq_zero_iff
        (N := directSumSubgroup K) (powerMapVirtual K n x)).2
          (powerMapVirtual_directSumSubgroup_le K n hx))

@[simp]
theorem powerMapK0_mk (n : ℕ) (x : VirtualEndomorphism K) :
    powerMapK0 K n (mk K x) = mk K (powerMapVirtual K n x) := by
  exact QuotientAddGroup.lift_mk (directSumSubgroup K)
    (by
      intro x hx
      exact (QuotientAddGroup.eq_zero_iff
        (N := directSumSubgroup K) (powerMapVirtual K n x)).2
          (powerMapVirtual_directSumSubgroup_le K n hx))
    x

@[simp]
theorem powerMapK0_of (n : ℕ) (A : EndomorphismObject.{u, v} K) :
    powerMapK0 K n (mk K (of K A)) =
      mk K (of K (EndomorphismObject.power A n)) := by
  exact powerMapK0_mk K n (of K A)

/-- The trace character compatibility with `powerMapK0` on a generator. -/
theorem traceCharacterK0_one_powerMapK0_of (n : ℕ) (A : EndomorphismObject.{u, v} K) :
    traceCharacterK0 K 1 (powerMapK0 K n (mk K (of K A))) =
      traceCharacterK0 K n (mk K (of K A)) := by
  calc
    traceCharacterK0 K 1 (powerMapK0 K n (mk K (of K A)))
        = traceCharacterK0 K 1 (mk K (of K (EndomorphismObject.power A n))) := by
          rfl
    _ = EndomorphismObject.tracePower 1 (EndomorphismObject.power A n) := by
          exact traceCharacterK0_of (K := K) 1 (EndomorphismObject.power A n)
    _ = EndomorphismObject.tracePower n A := by
          exact EndomorphismObject.tracePower_one_power A n
    _ = traceCharacterK0 K n (mk K (of K A)) := by
          symm
          exact traceCharacterK0_of (K := K) n A

/-- The trace-power compatibility proof respects additive recursion on the free
abelian group. -/
theorem traceCharacterK0_one_powerMapK0_induction
    (n : ℕ) (y : FreeAbelianGroup EndomorphismObject.{u, v} K) :
    traceCharacterK0 K 1 (powerMapK0 K n (mk K y)) =
      traceCharacterK0 K n (mk K y) := by
  induction y using FreeAbelianGroup.induction_on' with
  | C0 =>
      rfl
  | C1 A =>
      exact traceCharacterK0_one_powerMapK0_of (K := K) n A
  | Cn y hy =>
      exact congrArg Neg.neg hy
  | Cp y z hy hz =>
      exact congrArg₂ HAdd.hAdd hy hz

/-- Applying the ordinary trace character to the powered K₀ class recovers the
`n`th trace-power character. -/
theorem traceCharacterK0_one_powerMapK0 (n : ℕ) (x : K0 K) :
    traceCharacterK0 K 1 (powerMapK0 K n x) =
      traceCharacterK0 K n x := by
  refine Quotient.inductionOn' x ?_
  intro y
  exact traceCharacterK0_one_powerMapK0_induction (K := K) n y

/-- The power map fixes the `n=1` generator. -/
theorem powerMapK0_one_of (A : EndomorphismObject.{u, v} K) :
    powerMapK0 K 1 (mk K (of K A)) = mk K (of K A) := by
  calc
    powerMapK0 K 1 (mk K (of K A))
        = mk K (of K (EndomorphismObject.power A 1)) := by
          exact powerMapK0_of (K := K) 1 A
    _ = mk K (of K A) := by
          congr 1
          exact EndomorphismObject.power_one A

/-- The `n=1` power-map compatibility proof respects additive recursion on the
free abelian group. -/
theorem powerMapK0_one_induction
    (y : FreeAbelianGroup EndomorphismObject.{u, v} K) :
    powerMapK0 K 1 (mk K y) = mk K y := by
  induction y using FreeAbelianGroup.induction_on' with
  | C0 =>
      rfl
  | C1 A =>
      exact powerMapK0_one_of (K := K) A
  | Cn y hy =>
      exact congrArg Neg.neg hy
  | Cp y z hy hz =>
      exact congrArg₂ HAdd.hAdd hy hz

@[simp]
theorem powerMapK0_one (x : K0 K) :
    powerMapK0 K 1 x = x := by
  refine Quotient.inductionOn' x ?_
  intro y
  exact powerMapK0_one_induction (K := K) y

/-- The power maps compose on generators by multiplication of exponents. -/
theorem powerMapK0_comp_of (m n : ℕ) (A : EndomorphismObject.{u, v} K) :
    powerMapK0 K n (powerMapK0 K m (mk K (of K A))) =
      powerMapK0 K (m * n) (mk K (of K A)) := by
  calc
    powerMapK0 K n (powerMapK0 K m (mk K (of K A)))
        = mk K (of K (EndomorphismObject.power (EndomorphismObject.power A m) n)) := by
          exact powerMapK0_mk (K := K) n (of K (EndomorphismObject.power A m))
    _ = mk K (of K (EndomorphismObject.power A (m * n))) := by
          congr 1
          exact EndomorphismObject.power_power A m n
    _ = powerMapK0 K (m * n) (mk K (of K A)) := by
          symm
          exact powerMapK0_of (K := K) (m * n) A

/-- Composition of power maps respects additive recursion on the free abelian
group. -/
theorem powerMapK0_comp_induction
    (m n : ℕ) (y : FreeAbelianGroup EndomorphismObject.{u, v} K) :
    powerMapK0 K n (powerMapK0 K m (mk K y)) =
      powerMapK0 K (m * n) (mk K y) := by
  induction y using FreeAbelianGroup.induction_on' with
  | C0 =>
      rfl
  | C1 A =>
      exact powerMapK0_comp_of (K := K) m n A
  | Cn y hy =>
      exact congrArg Neg.neg hy
  | Cp y z hy hz =>
      exact congrArg₂ HAdd.hAdd hy hz

/-- Composing K₀ power maps multiplies the exponents. -/
theorem powerMapK0_comp (m n : ℕ) (x : K0 K) :
    powerMapK0 K n (powerMapK0 K m x) =
      powerMapK0 K (m * n) x := by
  refine Quotient.inductionOn' x ?_
  intro y
  exact powerMapK0_comp_induction (K := K) m n y

/-- The first trace character descended to the direct-sum quotient. -/
def traceCharacterOneK0 : K0 K →+ K :=
  traceCharacterK0 K 1

@[simp]
theorem traceCharacterOneK0_mk (x : VirtualEndomorphism K) :
    traceCharacterOneK0 K (mk K x) = traceCharacter K 1 x := by
  exact QuotientAddGroup.lift_mk (directSumSubgroup K)
    (directSumSubgroup_le_traceCharacter_one_ker K) x

@[simp]
theorem traceCharacterOneK0_of (A : EndomorphismObject.{u, v} K) :
    traceCharacterOneK0 K (mk K (of K A)) = EndomorphismObject.tracePower 1 A := by
  exact traceCharacterOneK0_mk K (of K A)

/-- A short exact sequence in the category of finite-dimensional endomorphism
objects.  The maps are required to commute with the endomorphisms. -/
structure ShortExactSequence where
  left : EndomorphismObject.{u, v} K
  middle : EndomorphismObject.{u, v} K
  right : EndomorphismObject.{u, v} K
  ι : left.carrier →ₗ[K] middle.carrier
  π : middle.carrier →ₗ[K] right.carrier
  exact : Function.Exact ι π
  injective : Function.Injective ι
  surjective : Function.Surjective π
  comm_left : ι.comp left.endomorphism = middle.endomorphism.comp ι
  comm_right : π.comp middle.endomorphism = right.endomorphism.comp π

namespace ShortExactSequence

variable {K}
variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]

/-- A canonical right inverse for the surjective map in a short exact sequence. -/
noncomputable def splittingSection (S : ShortExactSequence.{u, v} K) :
    S.right.carrier →ₗ[K] S.middle.carrier :=
  by
    classical
    exact (LinearMap.exists_rightInverse_of_surjective S.π (by
      exact LinearMap.range_eq_top.mpr S.surjective)).choose

@[simp]
theorem splittingSection_spec (S : ShortExactSequence.{u, v} K) :
    S.π.comp (S.splittingSection) = LinearMap.id := by
  classical
  exact (LinearMap.exists_rightInverse_of_surjective S.π (by
    exact LinearMap.range_eq_top.mpr S.surjective)).choose_spec

/-- The canonical splitting section is a right inverse for `π`. -/
theorem splittingSection_π (S : ShortExactSequence.{u, v} K) (x : S.right.carrier) :
    S.π (S.splittingSection x) = x := by
  exact LinearMap.congr_fun S.splittingSection_spec x

/-- The middle endomorphism commutes with the canonical inclusion into the left summand. -/
theorem middle_endomorphism_ι (S : ShortExactSequence.{u, v} K) (x : S.left.carrier) :
    S.middle.endomorphism (S.ι x) = S.ι (S.left.endomorphism x) := by
  exact (congrArg (fun f => f x) S.comm_left).symm

/-- The middle endomorphism commutes with the canonical splitting section into the right summand. -/
theorem middle_endomorphism_splittingSection (S : ShortExactSequence.{u, v} K)
    (x : S.right.carrier) :
    S.π (S.middle.endomorphism (S.splittingSection x)) = S.right.endomorphism x := by
  calc
    S.π (S.middle.endomorphism (S.splittingSection x)) =
        S.right.endomorphism (S.π (S.splittingSection x)) := by
          exact congrArg (fun f => f (S.splittingSection x)) S.comm_right
    _ = S.right.endomorphism x := by
          exact congrArg S.right.endomorphism (S.splittingSection_π x)

/-- The canonical splitting equivalence of a short exact sequence. -/
noncomputable def splittingEquiv (S : ShortExactSequence.{u, v} K) :
    S.middle.carrier ≃ₗ[K] S.left.carrier × S.right.carrier := by
  classical
  refine (LinearEquiv.ofBijective (LinearMap.coprod S.ι S.splittingSection) ?_).symm
  constructor
  · intro x y hxy
    have hsec : ∀ t, S.π (S.splittingSection t) = t := by
      intro t
      exact LinearMap.congr_fun S.splittingSection_spec t
    have hπ : x.2 = y.2 := by
      have h' := congrArg S.π hxy
      simp [LinearMap.coprod, S.exact.apply_apply_eq_zero, hsec] at h'
      exact h'
    have hι : S.ι x.1 = S.ι y.1 := by
      have h' := congrArg (fun z => z - S.splittingSection x.2) hxy
      simp [LinearMap.coprod, hπ, map_sub, hsec] at h'
      exact h'
    exact Prod.ext (S.injective hι) hπ
  · intro z
    have hsec : ∀ t, S.π (S.splittingSection t) = t := by
      intro t
      exact LinearMap.congr_fun S.splittingSection_spec t
    have hz : S.π (z - S.splittingSection (S.π z)) = 0 := by
      simp [map_sub, hsec]
    have hmem : z - S.splittingSection (S.π z) ∈ Set.range S.ι :=
      (S.exact (z - S.splittingSection (S.π z))).1 hz
    obtain ⟨x, hx⟩ := hmem
    refine ⟨(x, S.π z), ?_⟩
    calc
      S.ι x + S.splittingSection (S.π z) = z - S.splittingSection (S.π z) +
          S.splittingSection (S.π z) := by
            rw [hx]
      _ = z := by
            simp [sub_eq_add_neg, add_comm, add_left_comm, add_assoc]

@[simp]
theorem splittingEquiv_symm_inl (S : ShortExactSequence.{u, v} K) (x : S.left.carrier) :
    S.splittingEquiv.symm (LinearMap.inl K S.left.carrier S.right.carrier x) = S.ι x := by
  simp [ShortExactSequence.splittingEquiv]

@[simp]
theorem splittingEquiv_symm_inr (S : ShortExactSequence.{u, v} K) (x : S.right.carrier) :
    S.splittingEquiv.symm (LinearMap.inr K S.left.carrier S.right.carrier x) =
      S.splittingSection x := by
  simp [ShortExactSequence.splittingEquiv]

/-- The second coordinate of the splitting equivalence is the surjection `π`. -/
theorem splittingEquiv_snd (S : ShortExactSequence.{u, v} K) (x : S.middle.carrier) :
    (S.splittingEquiv x).2 = S.π x := by
  rcases h : S.splittingEquiv x with ⟨a, b⟩
  have hsymm := S.splittingEquiv.symm_apply_apply x
  rw [h] at hsymm
  have h0 : S.π (S.ι a) = 0 := S.exact.apply_apply_eq_zero a
  have hpi' : S.π (S.splittingSection b) = b := S.splittingSection_π b
  have hπ : b = S.π x := by
    calc
      b = S.π (S.ι a + S.splittingSection b) := by
            rw [map_add, h0, hpi']
      _ = S.π x := congrArg S.π hsymm
  exact hπ

/-- The splitting equivalence sends the canonical section to the right summand. -/
theorem splittingEquiv_splittingSection (S : ShortExactSequence.{u, v} K)
    (x : S.right.carrier) :
    S.splittingEquiv (S.splittingSection x) = (0, x) := by
  calc
    S.splittingEquiv (S.splittingSection x)
        = S.splittingEquiv (S.splittingEquiv.symm
            (LinearMap.inr K S.left.carrier S.right.carrier x)) := by
            congr 1
            exact (S.splittingEquiv_symm_inr x).symm
    _ = LinearMap.inr K S.left.carrier S.right.carrier x := by
          exact S.splittingEquiv.apply_symm_apply
            (LinearMap.inr K S.left.carrier S.right.carrier x)

/-- The splitting equivalence carries the image of `ι` to the left summand. -/
theorem splittingEquiv_ι (S : ShortExactSequence.{u, v} K) (x : S.left.carrier) :
    S.splittingEquiv (S.ι x) = (x, 0) := by
  calc
    S.splittingEquiv (S.ι x)
        = S.splittingEquiv (S.splittingEquiv.symm
            (LinearMap.inl K S.left.carrier S.right.carrier x)) := by
            congr 1
            exact (S.splittingEquiv_symm_inl (S := S) (x := x)).symm
    _ = LinearMap.inl K S.left.carrier S.right.carrier x := by
          exact S.splittingEquiv.apply_symm_apply
            (LinearMap.inl K S.left.carrier S.right.carrier x)

/-- The transported middle endomorphism carries the left summand to the left summand. -/
theorem splittingEquiv_conj_inl (S : ShortExactSequence.{u, v} K)
    (x : S.left.carrier) :
    (S.splittingEquiv.conj S.middle.endomorphism)
        (LinearMap.inl K S.left.carrier S.right.carrier x) =
      LinearMap.inl K S.left.carrier S.right.carrier (S.left.endomorphism x) := by
  calc
    (S.splittingEquiv.conj S.middle.endomorphism)
        (LinearMap.inl K S.left.carrier S.right.carrier x)
        = S.splittingEquiv
            (S.middle.endomorphism
              (S.splittingEquiv.symm (LinearMap.inl K S.left.carrier S.right.carrier x))) := by
            rfl
    _ = S.splittingEquiv
          (S.middle.endomorphism (S.ι x)) := by
            congr 1
            exact S.splittingEquiv_symm_inl x
    _ = S.splittingEquiv (S.ι (S.left.endomorphism x)) := by
            congr 1
            exact S.middle_endomorphism_ι x
    _ = LinearMap.inl K S.left.carrier S.right.carrier (S.left.endomorphism x) := by
            exact S.splittingEquiv_ι (S.left.endomorphism x)

/-- The transported middle endomorphism carries the right summand to the right summand. -/
theorem splittingEquiv_conj_inr_snd (S : ShortExactSequence.{u, v} K)
    (x : S.right.carrier) :
    ((S.splittingEquiv.conj S.middle.endomorphism)
        (LinearMap.inr K S.left.carrier S.right.carrier x)).2 =
      S.right.endomorphism x := by
  calc
    ((S.splittingEquiv.conj S.middle.endomorphism)
        (LinearMap.inr K S.left.carrier S.right.carrier x)).2
        = (S.splittingEquiv (S.middle.endomorphism (S.splittingSection x))).2 := by
            rfl
    _ = S.π (S.middle.endomorphism (S.splittingSection x)) := by
            exact S.splittingEquiv_snd (S.middle.endomorphism (S.splittingSection x))
    _ = S.right.endomorphism x := by
            exact S.middle_endomorphism_splittingSection x

/-- The transported middle endomorphism has zero lower-left block in the
canonical product basis. -/
theorem splittingEquiv_conj_toBlocks₂₁
    (S : ShortExactSequence.{u, v} K)
    (bL : Basis ι K S.left.carrier) (bR : Basis κ K S.right.carrier) :
    (LinearMap.toMatrix (bL.prod bR) (bL.prod bR)
        (S.splittingEquiv.conj S.middle.endomorphism)).toBlocks₂₁ = 0 := by
  ext i j
  change (LinearMap.toMatrix (bL.prod bR) (bL.prod bR)
      (S.splittingEquiv.conj S.middle.endomorphism)) (Sum.inr i) (Sum.inl j) = 0
  have hT :
      (S.splittingEquiv.conj S.middle.endomorphism) (LinearMap.inl K S.left.carrier S.right.carrier (bL j)) =
        LinearMap.inl K S.left.carrier S.right.carrier (S.left.endomorphism (bL j)) := by
    exact S.splittingEquiv_conj_inl (bL j)
  have hpair :
      (S.splittingEquiv.conj S.middle.endomorphism) (bL j, 0) =
        (S.left.endomorphism (bL j), 0) := by
    simpa [Basis.prod_apply] using hT
  cases hpair
  rfl

/-- The transported middle endomorphism preserves the left diagonal block in
the canonical product basis. -/
theorem splittingEquiv_conj_toBlocks₁₁
    (S : ShortExactSequence.{u, v} K)
    (bL : Basis ι K S.left.carrier) (bR : Basis κ K S.right.carrier) :
    (LinearMap.toMatrix (bL.prod bR) (bL.prod bR)
        (S.splittingEquiv.conj S.middle.endomorphism)).toBlocks₁₁ =
      LinearMap.toMatrix bL bL S.left.endomorphism := by
  ext i j
  change (LinearMap.toMatrix (bL.prod bR) (bL.prod bR)
      (S.splittingEquiv.conj S.middle.endomorphism)) (Sum.inl i) (Sum.inl j) =
    LinearMap.toMatrix bL bL S.left.endomorphism i j
  have hT :
      (S.splittingEquiv.conj S.middle.endomorphism) (LinearMap.inl K S.left.carrier S.right.carrier (bL j)) =
        LinearMap.inl K S.left.carrier S.right.carrier (S.left.endomorphism (bL j)) := by
    exact S.splittingEquiv_conj_inl (bL j)
  have hrepr := congrArg (fun x => (bL.prod bR).repr x (Sum.inl i)) hT
  simpa [LinearMap.toMatrix_apply, Basis.prod_apply] using hrepr

/-- The transported middle endomorphism preserves the right diagonal block in
the canonical product basis. -/
theorem splittingEquiv_conj_toBlocks₂₂
    (S : ShortExactSequence.{u, v} K)
    (bL : Basis ι K S.left.carrier) (bR : Basis κ K S.right.carrier) :
    (LinearMap.toMatrix (bL.prod bR) (bL.prod bR)
        (S.splittingEquiv.conj S.middle.endomorphism)).toBlocks₂₂ =
      LinearMap.toMatrix bR bR S.right.endomorphism := by
  ext i j
  change (LinearMap.toMatrix (bL.prod bR) (bL.prod bR)
      (S.splittingEquiv.conj S.middle.endomorphism)) (Sum.inr i) (Sum.inr j) =
    LinearMap.toMatrix bR bR S.right.endomorphism i j
  have hT :
      ((S.splittingEquiv.conj S.middle.endomorphism)
        (LinearMap.inr K S.left.carrier S.right.carrier (bR j))).2 =
        S.right.endomorphism (bR j) := by
    exact S.splittingEquiv_conj_inr_snd (bR j)
  exact congrArg (fun x : S.right.carrier => bR.repr x i) hT

/-- The conjugated middle endomorphism has the expected block-diagonal charpoly. -/
theorem splittingEquiv_conj_charpoly
    (S : ShortExactSequence.{u, v} K)
    (bL : Basis ι K S.left.carrier) (bR : Basis κ K S.right.carrier) :
    (S.splittingEquiv.conj S.middle.endomorphism).charpoly =
      S.left.endomorphism.charpoly * S.right.endomorphism.charpoly := by
  let M :
      Matrix (Module.Free.ChooseBasisIndex K S.left.carrier ⊕
        Module.Free.ChooseBasisIndex K S.right.carrier)
        (Module.Free.ChooseBasisIndex K S.left.carrier ⊕
          Module.Free.ChooseBasisIndex K S.right.carrier) K :=
      LinearMap.toMatrix (bL.prod bR) (bL.prod bR)
        (S.splittingEquiv.conj S.middle.endomorphism)
  have hdiag :
      M.toBlocks₁₁ =
        LinearMap.toMatrix bL bL S.left.endomorphism := by
    exact S.splittingEquiv_conj_toBlocks₁₁ (bL := bL) (bR := bR)
  have hdiag₂ :
      M.toBlocks₂₂ =
        LinearMap.toMatrix bR bR S.right.endomorphism := by
    exact S.splittingEquiv_conj_toBlocks₂₂ (bL := bL) (bR := bR)
  have htri :
      M.toBlocks₂₁ = 0 := by
    exact S.splittingEquiv_conj_toBlocks₂₁ (bL := bL) (bR := bR)
  let U := M.toBlocks₁₂
  have hmat :
      M =
        Matrix.fromBlocks (LinearMap.toMatrix bL bL S.left.endomorphism) U 0
          (LinearMap.toMatrix bR bR S.right.endomorphism) := by
    rw [← Matrix.fromBlocks_toBlocks M, hdiag, htri, hdiag₂]
  have hcharM :
      M.charpoly =
        LinearMap.charpoly S.left.endomorphism * LinearMap.charpoly S.right.endomorphism := by
    calc
      M.charpoly =
          (Matrix.fromBlocks (LinearMap.toMatrix bL bL S.left.endomorphism) U 0
            (LinearMap.toMatrix bR bR S.right.endomorphism)).charpoly := by
            exact congrArg Matrix.charpoly hmat
      _ = LinearMap.charpoly S.left.endomorphism * LinearMap.charpoly S.right.endomorphism := by
            simpa [LinearMap.charpoly_toMatrix] using
              (Matrix.charpoly_fromBlocks_zero₂₁
                (M₁₁ := LinearMap.toMatrix bL bL S.left.endomorphism)
                (M₁₂ := U)
                (M₂₂ := LinearMap.toMatrix bR bR S.right.endomorphism))
  exact hcharM

/-- The conjugated middle endomorphism has the expected trace. -/
theorem splittingEquiv_conj_trace
    (S : ShortExactSequence.{u, v} K)
    (bL : Basis ι K S.left.carrier) (bR : Basis κ K S.right.carrier) :
    LinearMap.trace K S.left.carrier S.left.endomorphism +
      LinearMap.trace K S.right.carrier S.right.endomorphism =
      LinearMap.trace K (S.left.carrier × S.right.carrier)
        (S.splittingEquiv.conj S.middle.endomorphism) := by
  let M :
      Matrix (Module.Free.ChooseBasisIndex K S.left.carrier ⊕
        Module.Free.ChooseBasisIndex K S.right.carrier)
        (Module.Free.ChooseBasisIndex K S.left.carrier ⊕
          Module.Free.ChooseBasisIndex K S.right.carrier) K :=
      LinearMap.toMatrix (bL.prod bR) (bL.prod bR)
        (S.splittingEquiv.conj S.middle.endomorphism)
  have htri :
      M.toBlocks₂₁ = 0 := by
    exact S.splittingEquiv_conj_toBlocks₂₁ (bL := bL) (bR := bR)
  have hdiag :
      M.toBlocks₁₁ =
        LinearMap.toMatrix bL bL S.left.endomorphism := by
    exact S.splittingEquiv_conj_toBlocks₁₁ (bL := bL) (bR := bR)
  have hdiag₂ :
      M.toBlocks₂₂ =
        LinearMap.toMatrix bR bR S.right.endomorphism := by
    exact S.splittingEquiv_conj_toBlocks₂₂ (bL := bL) (bR := bR)
  let U := M.toBlocks₁₂
  have hmat :
      M =
        Matrix.fromBlocks (LinearMap.toMatrix bL bL S.left.endomorphism) U 0
          (LinearMap.toMatrix bR bR S.right.endomorphism) := by
    rw [← Matrix.fromBlocks_toBlocks M, hdiag, htri, hdiag₂]
  have hleft :
      (LinearMap.toMatrix bL bL S.left.endomorphism).trace =
        LinearMap.trace K S.left.carrier S.left.endomorphism := by
    symm
    exact LinearMap.trace_eq_matrix_trace K bL S.left.endomorphism
  have hright :
      (LinearMap.toMatrix bR bR S.right.endomorphism).trace =
        LinearMap.trace K S.right.carrier S.right.endomorphism := by
    symm
    exact LinearMap.trace_eq_matrix_trace K bR S.right.endomorphism
  calc
    LinearMap.trace K (S.left.carrier × S.right.carrier)
        (S.splittingEquiv.conj S.middle.endomorphism)
        = M.trace := by
            rw [LinearMap.trace_eq_matrix_trace K (bL.prod bR)
              (S.splittingEquiv.conj S.middle.endomorphism)]
    _ = (LinearMap.toMatrix bL bL S.left.endomorphism).trace +
          (LinearMap.toMatrix bR bR S.right.endomorphism).trace := by
          rw [hmat]
          exact by
            simp [Matrix.trace, Matrix.fromBlocks, hdiag, hdiag₂, U]
    _ = LinearMap.trace K S.left.carrier S.left.endomorphism +
          LinearMap.trace K S.right.carrier S.right.endomorphism := by
          simp [hleft, hright]

/-- The short exact sequence forces the middle trace to equal the sum of the
left and right traces. -/
theorem shortExact_trace_additivity (S : ShortExactSequence.{u, v} K) :
    LinearMap.trace K S.middle.carrier S.middle.endomorphism =
      LinearMap.trace K S.left.carrier S.left.endomorphism +
        LinearMap.trace K S.right.carrier S.right.endomorphism := by
  let bL := Module.Free.chooseBasis K S.left.carrier
  let bR := Module.Free.chooseBasis K S.right.carrier
  exact (LinearMap.trace_conj' (S.middle.endomorphism) S.splittingEquiv).trans
    (S.splittingEquiv_conj_trace (bL := bL) (bR := bR))

/-- The short exact sequence forces the middle charpoly to equal the product of
the left and right charpolys. -/
theorem shortExact_middle_charpoly_eq (S : ShortExactSequence.{u, v} K) :
    S.middle.endomorphism.charpoly =
      (S.left.product S.right).endomorphism.charpoly := by
  let bL := Module.Free.chooseBasis K S.left.carrier
  let bR := Module.Free.chooseBasis K S.right.carrier
  calc
    S.middle.endomorphism.charpoly =
        (S.splittingEquiv.conj S.middle.endomorphism).charpoly := by
          symm
          exact LinearEquiv.charpoly_conj (e := S.splittingEquiv)
            (φ := S.middle.endomorphism)
    _ = S.left.endomorphism.charpoly * S.right.endomorphism.charpoly := by
          exact S.splittingEquiv_conj_charpoly (bL := bL) (bR := bR)
    _ = (S.left.product S.right).endomorphism.charpoly := by
      exact (LinearMap.charpoly_prodMap S.left.endomorphism S.right.endomorphism).symm

/-- The short exact sequence identifies the determinant unit of the middle
object with that of the corresponding product object. -/
theorem shortExact_middle_determinantUnit_eq (S : ShortExactSequence.{u, v} K) :
    EndomorphismObject.determinantUnit (S.middle) =
      EndomorphismObject.determinantUnit (EndomorphismObject.product S.left S.right) := by
  change
    Units.mk0 (EndomorphismObject.determinantRatFunc S.middle)
      (RatFunc.algebraMap_ne_zero (EndomorphismObject.eulerPolynomial_ne_zero S.middle)) =
    Units.mk0 (EndomorphismObject.determinantRatFunc (EndomorphismObject.product S.left S.right))
      (RatFunc.algebraMap_ne_zero
        (EndomorphismObject.eulerPolynomial_ne_zero (EndomorphismObject.product S.left S.right)))
  ext
  simp [EndomorphismObject.determinantUnit, EndomorphismObject.determinantRatFunc,
    LinearEulerFactor.eulerPolynomial, S.shortExact_middle_charpoly_eq]

/-- The short exact sequence forces the determinant unit of the middle object
to be the product of the left and right determinant units. -/
theorem shortExact_determinantUnit_mul (S : ShortExactSequence.{u, v} K) :
    EndomorphismObject.determinantUnit (S.middle) =
      EndomorphismObject.determinantUnit (S.left) *
        EndomorphismObject.determinantUnit (S.right) := by
  calc
    EndomorphismObject.determinantUnit (S.middle) =
        EndomorphismObject.determinantUnit (EndomorphismObject.product S.left S.right) := by
      exact S.shortExact_middle_determinantUnit_eq
    _ = EndomorphismObject.determinantUnit (S.left) *
        EndomorphismObject.determinantUnit (S.right) := by
      exact (EndomorphismObject.determinantUnit_product S.left S.right).symm

/-- The relation attached to a short exact sequence of endomorphism objects:
`[middle] - [left] - [right]`. -/
def shortExactRelation (K : Type u) [Field K] (S : ShortExactSequence.{u, v} K) :
    VirtualEndomorphism K :=
  of K S.middle - of K S.left - of K S.right

/-- The subgroup generated by direct-sum, conjugacy, zero-object, and
short-exact-sequence relations. -/
def shortExactSubgroup (K : Type u) [Field K] : AddSubgroup (VirtualEndomorphism K) :=
  AddSubgroup.closure
    {x | (∃ A B : EndomorphismObject.{u, v} K, x = directSumRelation K A B) ∨
      (∃ A B : EndomorphismObject.{u, v} K, ∃ e : A.carrier ≃ₗ[K] B.carrier,
        x = conjRelation K A e) ∨
      (∃ A : EndomorphismObject.{u, v} K, IsZeroObject K A ∧ x = of K A) ∨
      ∃ S : ShortExactSequence.{u, v} K, x = shortExactRelation K S}

/-- The exact-sequence Grothendieck quotient of finite-dimensional endomorphism
objects. -/
abbrev K0Exact (K : Type u) [Field K] :=
  VirtualEndomorphism K ⧸ shortExactSubgroup K

/-- Quotient map from the free virtual group to the exact-sequence quotient. -/
def mkExact (K : Type u) [Field K] : VirtualEndomorphism K →+ K0Exact K :=
  QuotientAddGroup.mk' (shortExactSubgroup K)

/-- The short exact sequence relation lies in the subgroup it generates. -/
theorem shortExactRelation_mem_shortExactSubgroup (K : Type u) [Field K]
    (S : ShortExactSequence.{u, v} K) :
    shortExactRelation K S ∈ (shortExactSubgroup K : AddSubgroup (VirtualEndomorphism K)) := by
  change shortExactRelation K S ∈
      AddSubgroup.closure
        {x : VirtualEndomorphism K |
          (∃ A B : EndomorphismObject.{u, v} K, x = directSumRelation K A B) ∨
            (∃ A B : EndomorphismObject.{u, v} K, ∃ e : A.carrier ≃ₗ[K] B.carrier,
              x = conjRelation K A e) ∨
            (∃ A : EndomorphismObject.{u, v} K, IsZeroObject K A ∧ x = of K A) ∨
            ∃ S : ShortExactSequence.{u, v} K, x = shortExactRelation K S}
  exact AddSubgroup.subset_closure (Or.inr <| Or.inr <| Or.inr ⟨S, rfl⟩)

@[simp]
theorem mkExact_shortExactRelation (K : Type u) [Field K]
    (S : ShortExactSequence.{u, v} K) :
    mkExact K (shortExactRelation K S) = 0 := by
  change (shortExactRelation K S : K0Exact K) = 0
  exact (QuotientAddGroup.eq_zero_iff
    (N := shortExactSubgroup K) (shortExactRelation K S)).2
      (shortExactRelation_mem_shortExactSubgroup K S)

/-- Exact-sequence additivity in the exact-sequence Grothendieck quotient. -/
theorem mkExact_shortExact_eq_add (K : Type u) [Field K]
    (S : ShortExactSequence.{u, v} K) :
    mkExact K (of K S.middle) = mkExact K (of K S.left) + mkExact K (of K S.right) := by
  apply eq_of_sub_eq_zero
  calc
    mkExact K (of K S.middle) - (mkExact K (of K S.left) + mkExact K (of K S.right))
        = mkExact K (of K S.middle - (of K S.left + of K S.right)) := by
          exact (map_sub (mkExact K) (of K S.middle) (of K S.left + of K S.right)).symm
    _ = mkExact K (shortExactRelation K S) := by
          rfl
    _ = 0 := mkExact_shortExactRelation K S

/-- The determinant character kills the short exact sequence relation. -/
theorem determinantCharacter_shortExactRelation (K : Type u) [Field K]
    (S : ShortExactSequence.{u, v} K) :
    determinantCharacter K (shortExactRelation K S) = 0 := by
  calc
    determinantCharacter K (shortExactRelation K S)
        = determinantCharacter K (of K S.middle) -
            determinantCharacter K (of K S.left) -
            determinantCharacter K (of K S.right) := by
          rfl
    _ = Additive.ofMul (EndomorphismObject.determinantUnit S.middle) -
          Additive.ofMul (EndomorphismObject.determinantUnit S.left) -
          Additive.ofMul (EndomorphismObject.determinantUnit S.right) := by
          rw [determinantCharacter_of, determinantCharacter_of, determinantCharacter_of]
    _ = 0 := by
          exact sub_eq_zero.mpr (by
            exact S.shortExact_determinantUnit_mul)

/-- The first trace character kills the short exact sequence relation. -/
theorem traceCharacter_one_shortExactRelation (K : Type u) [Field K]
    (S : ShortExactSequence.{u, v} K) :
    traceCharacter K 1 (shortExactRelation K S) = 0 := by
  calc
    traceCharacter K 1 (shortExactRelation K S)
        = traceCharacter K 1 (of K S.middle) -
            traceCharacter K 1 (of K S.left) -
            traceCharacter K 1 (of K S.right) := by
          rfl
    _ = EndomorphismObject.tracePower 1 S.middle -
          EndomorphismObject.tracePower 1 S.left -
          EndomorphismObject.tracePower 1 S.right := by
          rw [traceCharacter_of, traceCharacter_of, traceCharacter_of]
    _ = 0 := by
          exact sub_eq_zero.mpr (by
            exact S.shortExact_trace_additivity)

/-- The determinant character kills the full exact-sequence relation subgroup. -/
theorem shortExactSubgroup_le_determinantCharacter_ker :
    shortExactSubgroup K ≤ (determinantCharacter K).ker := by
  rw [shortExactSubgroup, AddSubgroup.closure_le]
  rintro x (⟨A, B, rfl⟩ | ⟨A, B, e, rfl⟩ | ⟨A, hA, rfl⟩ | ⟨S, rfl⟩)
  · exact determinantCharacter_directSumRelation K A B
  · exact determinantCharacter_conjRelation K A e
  · exact determinantCharacter_zeroObject K A hA
  · exact determinantCharacter_shortExactRelation K S

/-- The determinant character descends to the exact-sequence quotient. -/
def determinantCharacterK0Exact : K0Exact K →+ Additive ((RatFunc K)ˣ) :=
  QuotientAddGroup.lift (shortExactSubgroup K) (determinantCharacter K)
    (shortExactSubgroup_le_determinantCharacter_ker (K := K))

/-- Multiplicative form of the determinant character on the exact-sequence
quotient. -/
def determinantCharacterK0ExactMul : Multiplicative (K0Exact K) →* (RatFunc K)ˣ where
  toFun x := Additive.toMul (determinantCharacterK0Exact (K := K) (Multiplicative.toAdd x))
  map_one' := by
    rfl
  map_mul' x y := by
    rfl

@[simp]
theorem determinantCharacterK0ExactMul_ofAdd (x : K0Exact K) :
    determinantCharacterK0ExactMul K (Multiplicative.ofAdd x) =
      Additive.toMul (determinantCharacterK0Exact K x) := by
  rfl

@[simp]
theorem determinantCharacterK0Exact_mk (x : VirtualEndomorphism K) :
    determinantCharacterK0Exact (mkExact K x) = determinantCharacter K x := by
  exact QuotientAddGroup.lift_mk (shortExactSubgroup K)
    (shortExactSubgroup_le_determinantCharacter_ker (K := K)) x

@[simp]
theorem determinantCharacterK0Exact_of (A : EndomorphismObject.{u, v} K) :
    determinantCharacterK0Exact (mkExact K (of K A)) =
      Additive.ofMul (EndomorphismObject.determinantUnit A) := by
  exact determinantCharacterK0Exact_mk (K := K) (of K A)

@[simp]
theorem determinantCharacterK0ExactMul_of (A : EndomorphismObject.{u, v} K) :
    determinantCharacterK0ExactMul (K := K) (Multiplicative.ofAdd (mkExact K (of K A))) =
      EndomorphismObject.determinantUnit A := by
  exact (determinantCharacterK0ExactMul_ofAdd (K := K) (mkExact K (of K A))).trans
    (congrArg Additive.toMul (determinantCharacterK0Exact_of (K := K) A))

/-- The first trace character kills the full exact-sequence relation subgroup. -/
theorem shortExactSubgroup_le_traceCharacter_one_ker :
    shortExactSubgroup K ≤ (traceCharacter K 1).ker := by
  rw [shortExactSubgroup, AddSubgroup.closure_le]
  rintro x (⟨A, B, rfl⟩ | ⟨A, B, e, rfl⟩ | ⟨A, hA, rfl⟩ | ⟨S, rfl⟩)
  · exact traceCharacter_directSumRelation K 1 A B
  · exact traceCharacter_conjRelation K 1 A e
  · exact traceCharacter_zeroObject K 1 A hA
  · exact traceCharacter_one_shortExactRelation K S

/-- The first trace character descends to the exact-sequence quotient. -/
def traceCharacterOneK0Exact : K0Exact K →+ K :=
  QuotientAddGroup.lift (shortExactSubgroup K) (traceCharacter K 1)
    (shortExactSubgroup_le_traceCharacter_one_ker (K := K))

@[simp]
theorem traceCharacterOneK0Exact_mk (x : VirtualEndomorphism K) :
    traceCharacterOneK0Exact (mkExact K x) = traceCharacter K 1 x := by
  exact QuotientAddGroup.lift_mk (shortExactSubgroup K)
    (shortExactSubgroup_le_traceCharacter_one_ker (K := K)) x

@[simp]
theorem traceCharacterOneK0Exact_of (A : EndomorphismObject.{u, v} K) :
    traceCharacterOneK0Exact (mkExact K (of K A)) = EndomorphismObject.tracePower 1 A := by
  change traceCharacter K 1 (of K A) = EndomorphismObject.tracePower 1 A
  exact traceCharacter_of (K := K) 1 A

end ShortExactSequence

end

end EndomorphismK0
end Boundary
