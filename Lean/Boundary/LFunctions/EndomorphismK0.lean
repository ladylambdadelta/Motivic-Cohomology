import Boundary.LFunctions.EulerFactor
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
theorem eulerPolynomial_ne_zero (A : EndomorphismObject K) :
    eulerPolynomial A.endomorphism ≠ 0 := by
  intro h
  have hcoeff := congrArg (fun p : Polynomial K => p.coeff 0) h
  simp at hcoeff

/-- The determinant character value as a unit in the rational-function field. -/
def determinantUnit (A : EndomorphismObject K) : (RatFunc K)ˣ :=
  Units.mk0 (determinantRatFunc A)
    (RatFunc.algebraMap_ne_zero (eulerPolynomial_ne_zero A))

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
      simp [product]
  | succ n ih =>
      rw [pow_succ, ih]
      ext x
      simp [product, LinearMap.prodMap, pow_succ]

/-- Taking powers commutes with direct sums of endomorphism objects. -/
theorem power_product (A B : EndomorphismObject K) (n : ℕ) :
    power (product A B) n = product (power A n) (power B n) := by
  have h := endomorphism_product_pow A B n
  cases A
  cases B
  simp [power, product] at h ⊢
  exact h

@[simp]
theorem power_one (A : EndomorphismObject K) :
    power A 1 = A := by
  cases A
  simp [power]

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
  simp [power, pow_mul]

@[simp]
theorem tracePower_one_power (A : EndomorphismObject K) (n : ℕ) :
    tracePower 1 (power A n) = tracePower n A := by
  simp [tracePower, power]

/-- Determinants multiply under direct sums. -/
@[simp]
theorem determinantRatFunc_product (A B : EndomorphismObject K) :
    determinantRatFunc (product A B) = determinantRatFunc A * determinantRatFunc B := by
  simp [determinantRatFunc, product, eulerPolynomial_prodMap]

/-- Determinant units multiply under direct sums. -/
@[simp]
theorem determinantUnit_product (A B : EndomorphismObject K) :
    determinantUnit (product A B) = determinantUnit A * determinantUnit B := by
  ext
  simp [determinantUnit]

/-- First traces add under direct sums. -/
@[simp]
theorem tracePower_one_product (A B : EndomorphismObject K) :
    tracePower 1 (product A B) = tracePower 1 A + tracePower 1 B := by
  simp [tracePower, product, LinearMap.trace_prodMap']

/-- Trace powers add under direct sums. -/
@[simp]
theorem tracePower_product (A B : EndomorphismObject K) (n : ℕ) :
    tracePower n (product A B) = tracePower n A + tracePower n B := by
  rw [tracePower, endomorphism_product_pow]
  change LinearMap.trace K (A.carrier × B.carrier)
      ((A.endomorphism ^ n).prodMap (B.endomorphism ^ n)) =
    LinearMap.trace K A.carrier (A.endomorphism ^ n) +
      LinearMap.trace K B.carrier (B.endomorphism ^ n)
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
        = mk K (of K (EndomorphismObject.product A B) - (of K A + of K B)) := by
          simp
    _ = mk K (directSumRelation K A B) := by
          congr 1
          simp [directSumRelation]
          rw [sub_add_eq_sub_sub]
    _ = 0 := mk_directSumRelation K A B

/-- Conjugate endomorphism objects have the same class in `K0`. -/
@[simp]
theorem mk_conj_eq_mk (A : EndomorphismObject.{u, v} K) {B : EndomorphismObject.{u, v} K}
    (e : A.carrier ≃ₗ[K] B.carrier) :
    mk K (of K (EndomorphismObject.conj A e)) = mk K (of K A) := by
  apply eq_of_sub_eq_zero
  calc
    mk K (of K (EndomorphismObject.conj A e)) - mk K (of K A)
        = mk K (conjRelation K A e) := by
            simp [conjRelation]
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
  simp [determinantCharacter, of]

/-- The determinant character kills the direct-sum relation. -/
@[simp]
theorem determinantCharacter_directSumRelation (A B : EndomorphismObject.{u, v} K) :
    determinantCharacter K (directSumRelation K A B) = 0 := by
  simp [directSumRelation]

theorem determinantCharacter_conjRelation
    (A : EndomorphismObject.{u, v} K) {B : EndomorphismObject.{u, v} K}
    (e : A.carrier ≃ₗ[K] B.carrier) :
    determinantCharacter K (conjRelation K A e) = 0 := by
  rw [conjRelation, map_sub, determinantCharacter_of, determinantCharacter_of]
  simp [EndomorphismObject.determinantUnit_conj]

@[simp]
theorem determinantCharacter_zeroObject (A : EndomorphismObject.{u, v} K)
    (hA : IsZeroObject K A) :
    determinantCharacter K (of K A) = 0 := by
  rw [determinantCharacter_of]
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
  change EndomorphismObject.determinantUnit A = 1
  ext
  simp [EndomorphismObject.determinantUnit, EndomorphismObject.determinantRatFunc,
    LinearEulerFactor.eulerPolynomial, hchar, hrev]

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
  simp

@[simp]
theorem determinantCharacterK0Mul_of (A : EndomorphismObject.{u, v} K) :
    determinantCharacterK0Mul K (Multiplicative.ofAdd (mk K (of K A))) =
      EndomorphismObject.determinantUnit A := by
  simp [determinantCharacterK0Mul]

/-- The trace-power character on the free virtual group. -/
def traceCharacter (n : ℕ) : VirtualEndomorphism K →+ K :=
  FreeAbelianGroup.lift fun A => EndomorphismObject.tracePower n A

@[simp]
theorem traceCharacter_of (n : ℕ) (A : EndomorphismObject.{u, v} K) :
    traceCharacter K n (of K A) = EndomorphismObject.tracePower n A := by
  simp [traceCharacter, of]

/-- The trace-power character kills the direct-sum relation. -/
@[simp]
theorem traceCharacter_directSumRelation (n : ℕ) (A B : EndomorphismObject.{u, v} K) :
    traceCharacter K n (directSumRelation K A B) = 0 := by
  simp [directSumRelation]

theorem traceCharacter_conjRelation (n : ℕ) (A : EndomorphismObject.{u, v} K)
    {B : EndomorphismObject.{u, v} K} (e : A.carrier ≃ₗ[K] B.carrier) :
    traceCharacter K n (conjRelation K A e) = 0 := by
  rw [conjRelation, map_sub, traceCharacter_of, traceCharacter_of]
  exact sub_eq_zero.mpr (EndomorphismObject.tracePower_conj n A e)

@[simp]
theorem traceCharacter_zeroObject (n : ℕ) (A : EndomorphismObject.{u, v} K)
    (hA : IsZeroObject K A) :
    traceCharacter K n (of K A) = 0 := by
  rw [traceCharacter_of]
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
  simp

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
  simp [directSumRelation, EndomorphismObject.power_product]

theorem powerMapVirtual_zeroObject_mem_directSumSubgroup
    (n : ℕ) (A : EndomorphismObject.{u, v} K) (hA : IsZeroObject K A) :
    powerMapVirtual K n (of K A) ∈ directSumSubgroup K := by
  rw [powerMapVirtual_of]
  exact zeroObject_mem_directSumSubgroup K (EndomorphismObject.power A n) hA

/-- The virtual power map preserves the direct-sum relation subgroup. -/
theorem powerMapVirtual_directSumSubgroup_le (n : ℕ) :
    directSumSubgroup K ≤
      (directSumSubgroup K).comap (powerMapVirtual K n) := by
  rw [directSumSubgroup, AddSubgroup.closure_le]
  rintro x (⟨A, B, rfl⟩ | ⟨A, B, e, rfl⟩ | ⟨A, hA, rfl⟩)
  · change powerMapVirtual K n (directSumRelation K A B) ∈ directSumSubgroup K
    rw [powerMapVirtual_directSumRelation]
    exact directSumRelation_mem_directSumSubgroup K
      (EndomorphismObject.power A n) (EndomorphismObject.power B n)
  · change powerMapVirtual K n (conjRelation K A e) ∈ directSumSubgroup K
    rw [conjRelation, map_sub, powerMapVirtual_of, powerMapVirtual_of]
    simpa [EndomorphismObject.power, EndomorphismObject.conj, EndomorphismObject.conj_pow n A e] using
      (conjRelation_mem_directSumSubgroup K (EndomorphismObject.power A n) e)
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
  simp [powerMapK0_mk]

/-- Applying the ordinary trace character to the powered K₀ class recovers the
`n`th trace-power character. -/
theorem traceCharacterK0_one_powerMapK0 (n : ℕ) (x : K0 K) :
    traceCharacterK0 K 1 (powerMapK0 K n x) =
      traceCharacterK0 K n x := by
  refine Quotient.inductionOn' x ?_
  intro y
  refine FreeAbelianGroup.induction_on' y ?zero ?of ?neg ?add
  · simp
  · intro A
    change traceCharacterK0 K 1 (powerMapK0 K n (mk K (of K A))) =
      traceCharacterK0 K n (mk K (of K A))
    simp [EndomorphismObject.tracePower_one_power]
  · intro y hy
    simp [hy]
  · intro y z hy hz
    simp [hy, hz]

@[simp]
theorem powerMapK0_one (x : K0 K) :
    powerMapK0 K 1 x = x := by
  refine Quotient.inductionOn' x ?_
  intro y
  induction y using FreeAbelianGroup.induction_on' with
  | C0 =>
      simp
  | C1 A =>
      change powerMapK0 K 1 (mk K (of K A)) = mk K (of K A)
      simp [EndomorphismObject.power_one]
  | Cn y hy =>
      exact congrArg Neg.neg hy
  | Cp y z hy hz =>
      simpa [map_add] using congrArg₂ HAdd.hAdd hy hz

/-- Composing K₀ power maps multiplies the exponents. -/
theorem powerMapK0_comp (m n : ℕ) (x : K0 K) :
    powerMapK0 K n (powerMapK0 K m x) =
      powerMapK0 K (m * n) x := by
  refine Quotient.inductionOn' x ?_
  intro y
  induction y using FreeAbelianGroup.induction_on' with
  | C0 =>
      simp
  | C1 A =>
      change powerMapK0 K n (powerMapK0 K m (mk K (of K A))) =
        powerMapK0 K (m * n) (mk K (of K A))
      simp [EndomorphismObject.power_power]
  | Cn y hy =>
      exact congrArg Neg.neg hy
  | Cp y z hy hz =>
      simpa [map_add] using congrArg₂ HAdd.hAdd hy hz

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
  simp

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
    haveI : Module.Projective K S.right.carrier := by infer_instance
    exact (LinearMap.exists_rightInverse_of_surjective S.π (by
      simpa [LinearMap.range_eq_top] using S.surjective)).choose

@[simp]
theorem splittingSection_spec (S : ShortExactSequence.{u, v} K) :
    S.π.comp (S.splittingSection) = LinearMap.id := by
  classical
  simpa [ShortExactSequence.splittingSection] using
    (LinearMap.exists_rightInverse_of_surjective S.π (by
      simpa [LinearMap.range_eq_top] using S.surjective)).choose_spec

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
  have hpi := congrArg S.π hsymm
  have h0 : S.π (S.ι a) = 0 := S.exact.apply_apply_eq_zero a
  simp [ShortExactSequence.splittingEquiv, splittingSection_spec, h0] at hpi
  have hsec : S.π (S.splittingSection b) = b := by
    exact LinearMap.congr_fun S.splittingSection_spec b
  simpa [h, hsec] using hpi

/-- The splitting equivalence sends the canonical section to the right summand. -/
theorem splittingEquiv_splittingSection (S : ShortExactSequence.{u, v} K)
    (x : S.right.carrier) :
    S.splittingEquiv (S.splittingSection x) = (0, x) := by
  rw [← splittingEquiv_symm_inr]
  exact S.splittingEquiv.apply_symm_apply (LinearMap.inr K S.left.carrier S.right.carrier x)

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
    change S.splittingEquiv (S.middle.endomorphism
      (S.splittingEquiv.symm (LinearMap.inl K S.left.carrier S.right.carrier (bL j)))) =
      LinearMap.inl K S.left.carrier S.right.carrier (S.left.endomorphism (bL j))
    rw [splittingEquiv_symm_inl]
    have hcomm : S.middle.endomorphism (S.ι (bL j)) = S.ι (S.left.endomorphism (bL j)) := by
      simpa [LinearMap.comp_apply] using (congrArg (fun f => f (bL j)) S.comm_left).symm
    have hleft :
        S.splittingEquiv (S.ι (S.left.endomorphism (bL j))) =
          (S.left.endomorphism (bL j), 0) := by
      have h := congrArg S.splittingEquiv
        (splittingEquiv_symm_inl (S := S) (x := S.left.endomorphism (bL j)))
      exact h.symm
    rw [ShortExactSequence.splittingEquiv, hcomm, hleft]
  have hpair :
      (S.splittingEquiv.conj S.middle.endomorphism) (bL j, 0) =
        (S.left.endomorphism (bL j), 0) := by
    simpa [Basis.prod_apply] using hT
  simp [LinearMap.toMatrix_apply, Basis.prod_apply, hpair]

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
    change S.splittingEquiv (S.middle.endomorphism
      (S.splittingEquiv.symm (LinearMap.inl K S.left.carrier S.right.carrier (bL j)))) =
      LinearMap.inl K S.left.carrier S.right.carrier (S.left.endomorphism (bL j))
    rw [splittingEquiv_symm_inl]
    have hcomm : S.middle.endomorphism (S.ι (bL j)) = S.ι (S.left.endomorphism (bL j)) := by
      simpa [LinearMap.comp_apply] using (congrArg (fun f => f (bL j)) S.comm_left).symm
    have hleft :
        S.splittingEquiv (S.ι (S.left.endomorphism (bL j))) =
          (S.left.endomorphism (bL j), 0) := by
      simpa [eq_comm] using congrArg S.splittingEquiv
        (splittingEquiv_symm_inl (S := S) (x := S.left.endomorphism (bL j)))
    rw [ShortExactSequence.splittingEquiv, hcomm, hleft]
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
    have hsymm := S.splittingEquiv_symm_inr (x := bR j)
    have hsec : S.π (S.splittingSection (bR j)) = bR j := by
      exact LinearMap.congr_fun S.splittingSection_spec (bR j)
    have hmid :
        (S.splittingEquiv (S.middle.endomorphism (S.splittingSection (bR j)))).2 =
          S.right.endomorphism (bR j) := by
      rw [splittingEquiv_snd]
      calc
        S.π (S.middle.endomorphism (S.splittingSection (bR j))) =
            S.right.endomorphism (S.π (S.splittingSection (bR j))) := by
              simpa [LinearMap.comp_apply] using
                congrArg (fun f => f (S.splittingSection (bR j))) S.comm_right
        _ = S.right.endomorphism (bR j) := by
              simp [hsec]
    change ((S.splittingEquiv (S.middle.endomorphism
      (S.splittingEquiv.symm (LinearMap.inr K S.left.carrier S.right.carrier (bR j)))))).2 =
      S.right.endomorphism (bR j)
    rw [hsymm]
    exact hmid
  simpa [LinearMap.toMatrix_apply, Basis.prod_apply] using
    congrArg (fun x : S.right.carrier => bR.repr x i) hT

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
        = mkExact K (shortExactRelation K S) := by
          simp [shortExactRelation]
          rw [sub_add_eq_sub_sub]
    _ = 0 := mkExact_shortExactRelation K S

/-- The determinant character kills the short exact sequence relation. -/
theorem determinantCharacter_shortExactRelation (K : Type u) [Field K]
    (S : ShortExactSequence.{u, v} K) :
    determinantCharacter K (shortExactRelation K S) = 0 := by
  let bL := Module.Free.chooseBasis K S.left.carrier
  let bR := Module.Free.chooseBasis K S.right.carrier
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
  let b : (Module.Free.ChooseBasisIndex K S.left.carrier ⊕
      Module.Free.ChooseBasisIndex K S.right.carrier) → Fin 2 := Sum.elim (fun _ => 0) fun _ => 1
  let U :=
    M.toBlocks₁₂
  have hmat :
      M =
        Matrix.fromBlocks (LinearMap.toMatrix bL bL S.left.endomorphism) U 0
          (LinearMap.toMatrix bR bR S.right.endomorphism) := by
    rw [← Matrix.fromBlocks_toBlocks M, hdiag, htri, hdiag₂]
  have hcharM :
      M.charpoly =
        LinearMap.charpoly S.left.endomorphism * LinearMap.charpoly S.right.endomorphism := by
    simpa [hmat, LinearMap.charpoly_toMatrix] using
      (Matrix.charpoly_fromBlocks_zero₂₁
        (M₁₁ := LinearMap.toMatrix bL bL S.left.endomorphism)
        (M₁₂ := U)
        (M₂₂ := LinearMap.toMatrix bR bR S.right.endomorphism))
  have hchar :
      (S.splittingEquiv.conj S.middle.endomorphism).charpoly =
        S.left.endomorphism.charpoly * S.right.endomorphism.charpoly := by
    simpa [M] using hcharM
  have hmid :
      S.middle.endomorphism.charpoly =
        (S.left.product S.right).endomorphism.charpoly := by
    calc
      S.middle.endomorphism.charpoly =
          (S.splittingEquiv.conj S.middle.endomorphism).charpoly := by
            symm
            exact LinearEquiv.charpoly_conj (e := S.splittingEquiv)
              (φ := S.middle.endomorphism)
      _ = S.left.endomorphism.charpoly * S.right.endomorphism.charpoly := hchar
      _ = (S.left.product S.right).endomorphism.charpoly := by
        simp [EndomorphismObject.product, LinearMap.charpoly_prodMap]
  have hdet :
      EndomorphismObject.determinantUnit (S.middle) =
        EndomorphismObject.determinantUnit (S.left) * EndomorphismObject.determinantUnit (S.right) := by
    calc
      EndomorphismObject.determinantUnit (S.middle) =
          EndomorphismObject.determinantUnit (EndomorphismObject.product S.left S.right) := by
        simp [EndomorphismObject.determinantUnit, EndomorphismObject.determinantRatFunc,
          LinearEulerFactor.eulerPolynomial, hmid]
      _ = EndomorphismObject.determinantUnit (S.left) * EndomorphismObject.determinantUnit (S.right) := by
        exact (EndomorphismObject.determinantUnit_product S.left S.right).symm
  rw [shortExactRelation, map_sub, map_sub, determinantCharacter_of,
    determinantCharacter_of, determinantCharacter_of, hdet]
  simp

/-- The first trace character kills the short exact sequence relation. -/
theorem traceCharacter_one_shortExactRelation (K : Type u) [Field K]
    (S : ShortExactSequence.{u, v} K) :
    traceCharacter K 1 (shortExactRelation K S) = 0 := by
  let bL := Module.Free.chooseBasis K S.left.carrier
  let bR := Module.Free.chooseBasis K S.right.carrier
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
  let U :=
    M.toBlocks₁₂
  have hmat :
      M =
        Matrix.fromBlocks (LinearMap.toMatrix bL bL S.left.endomorphism) U 0
          (LinearMap.toMatrix bR bR S.right.endomorphism) := by
    rw [← Matrix.fromBlocks_toBlocks M, hdiag, htri, hdiag₂]
  have htrace :
      LinearMap.trace K S.middle.carrier S.middle.endomorphism =
        LinearMap.trace K S.left.carrier S.left.endomorphism +
          LinearMap.trace K S.right.carrier S.right.endomorphism := by
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
    have htrace' :
        LinearMap.trace K (S.left.carrier × S.right.carrier)
          (S.splittingEquiv.conj S.middle.endomorphism) =
          LinearMap.trace K S.left.carrier S.left.endomorphism +
            LinearMap.trace K S.right.carrier S.right.endomorphism := by
      calc
        LinearMap.trace K (S.left.carrier × S.right.carrier)
            (S.splittingEquiv.conj S.middle.endomorphism)
            = M.trace := by
              rw [LinearMap.trace_eq_matrix_trace K (bL.prod bR)
                (S.splittingEquiv.conj S.middle.endomorphism)]
        _ = (LinearMap.toMatrix bL bL S.left.endomorphism).trace +
              (LinearMap.toMatrix bR bR S.right.endomorphism).trace := by
              rw [hmat]
              simp [Matrix.trace, Matrix.fromBlocks, hdiag, hdiag₂, U]
        _ = LinearMap.trace K S.left.carrier S.left.endomorphism +
              LinearMap.trace K S.right.carrier S.right.endomorphism := by
              simp [hleft, hright]
    have hconj := LinearMap.trace_conj' (S.middle.endomorphism) S.splittingEquiv
    exact hconj.symm.trans htrace'
  rw [shortExactRelation, map_sub, map_sub, traceCharacter_of, traceCharacter_of,
    traceCharacter_of]
  simp [EndomorphismObject.tracePower, htrace]

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
    simp [determinantCharacterK0Exact]
  map_mul' x y := by
    simp [determinantCharacterK0Exact]

@[simp]
theorem determinantCharacterK0Exact_mk (x : VirtualEndomorphism K) :
    determinantCharacterK0Exact (mkExact K x) = determinantCharacter K x := by
  exact QuotientAddGroup.lift_mk (shortExactSubgroup K)
    (shortExactSubgroup_le_determinantCharacter_ker (K := K)) x

@[simp]
theorem determinantCharacterK0Exact_of (A : EndomorphismObject.{u, v} K) :
    determinantCharacterK0Exact (mkExact K (of K A)) =
      Additive.ofMul (EndomorphismObject.determinantUnit A) := by
  change determinantCharacter K (of K A) = Additive.ofMul (EndomorphismObject.determinantUnit A)
  simp [determinantCharacter, of]

@[simp]
theorem determinantCharacterK0ExactMul_of (A : EndomorphismObject.{u, v} K) :
    determinantCharacterK0ExactMul (K := K) (Multiplicative.ofAdd (mkExact K (of K A))) =
      EndomorphismObject.determinantUnit A := by
  simp [determinantCharacterK0ExactMul]

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
  simp [traceCharacter, of]

end ShortExactSequence

end

end EndomorphismK0
end Boundary
