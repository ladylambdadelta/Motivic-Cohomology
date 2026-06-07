import Boundary.LFunctions.EndomorphismK0
import Boundary.LFunctions.EulerFactorLog
import Boundary.LFunctions.K0TraceLog
import Boundary.LFunctions.TraceExpansion
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

open scoped BigOperators PowerSeries

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

/-- For a finite product of polynomials whose constant coefficients are all
`1`, the linear coefficient is the sum of the linear coefficients. -/
theorem prod_coeff_one_of_coeff_zero_eq_one {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (p : ι → Polynomial K)
    (h0 : ∀ i ∈ s, (p i).coeff 0 = 1) :
    (∏ i in s, p i).coeff 1 = ∑ i in s, (p i).coeff 1 := by
  classical
  revert h0
  refine Finset.induction_on s ?empty ?insert
  · intro h0
    simp [Polynomial.coeff_one]
  · intro a s ha ih h0
    rw [Finset.prod_insert ha, Finset.sum_insert ha]
    rw [Polynomial.mul_coeff_one]
    have hp0 : (p a).coeff 0 = 1 := h0 a (Finset.mem_insert_self a s)
    have hprod0 : (∏ x in s, p x).coeff 0 = 1 := by
      rw [← Polynomial.constantCoeff_apply]
      rw [map_prod]
      exact Finset.prod_eq_one fun x hx => by
        rw [Polynomial.constantCoeff_apply]
        exact h0 x (Finset.mem_insert_of_mem hx)
    rw [ih]
    · rw [hp0, hprod0]
      rw [one_mul, mul_one]
      rw [add_comm]
    · intro i hi
      exact h0 i (Finset.mem_insert_of_mem hi)

/-- The linear coefficient of the numerator is the negative sum of traces in
odd degrees. -/
theorem localNumerator_coeff_one (degrees : Finset ℤ)
    (F : ∀ i, Module.End K (V i)) :
    (localNumerator (V := V) degrees F).coeff 1 =
      -∑ i in degrees.filter (fun i => Odd i), LinearMap.trace K (V i) (F i) := by
  rw [localNumerator]
  rw [prod_coeff_one_of_coeff_zero_eq_one]
  · simp [LinearEulerFactor.eulerPolynomial_coeff_one_trace]
  · intro i hi
    exact LinearEulerFactor.eulerPolynomial_coeff_zero (F i)

/-- The linear coefficient of the denominator is the negative sum of traces in
even degrees. -/
theorem localDenominator_coeff_one (degrees : Finset ℤ)
    (F : ∀ i, Module.End K (V i)) :
    (localDenominator (V := V) degrees F).coeff 1 =
      -∑ i in degrees.filter (fun i => Even i), LinearMap.trace K (V i) (F i) := by
  rw [localDenominator]
  rw [prod_coeff_one_of_coeff_zero_eq_one]
  · simp [LinearEulerFactor.eulerPolynomial_coeff_one_trace]
  · intro i hi
    exact LinearEulerFactor.eulerPolynomial_coeff_zero (F i)

/-- The finite-dimensional endomorphism object attached to one cohomological
degree. -/
def endomorphismObject (F : ∀ i, Module.End K (V i)) (i : ℤ) :
    Boundary.EndomorphismK0.EndomorphismObject K where
  carrier := V i
  addCommGroup := inferInstance
  module := inferInstance
  finiteDimensional := inferInstance
  endomorphism := F i

/-- The virtual endomorphism class whose determinant is the cohomological local
zeta factor. Odd degrees occur positively and even degrees negatively, matching
the `localZetaFactorRatFunc` convention. -/
def cohomologicalEndomorphismClass (degrees : Finset ℤ)
    (F : ∀ i, Module.End K (V i)) : Boundary.EndomorphismK0.K0 K :=
  ∑ i in degrees.filter (fun i => Odd i),
      Boundary.EndomorphismK0.mk K
        (Boundary.EndomorphismK0.of K (endomorphismObject (V := V) F i)) -
    ∑ i in degrees.filter (fun i => Even i),
      Boundary.EndomorphismK0.mk K
        (Boundary.EndomorphismK0.of K (endomorphismObject (V := V) F i))

/-- The first trace character on the cohomological class is the odd trace sum
minus the even trace sum. -/
theorem traceCharacterK0_cohomologicalEndomorphismClass
    (degrees : Finset ℤ) (F : ∀ i, Module.End K (V i)) :
    Boundary.EndomorphismK0.traceCharacterK0 K 1
        (cohomologicalEndomorphismClass (V := V) degrees F) =
      (∑ i in degrees.filter (fun i => Odd i), LinearMap.trace K (V i) (F i)) -
        ∑ i in degrees.filter (fun i => Even i), LinearMap.trace K (V i) (F i) := by
  simp [cohomologicalEndomorphismClass, endomorphismObject,
    Boundary.EndomorphismK0.EndomorphismObject.tracePower]

/-- The `n`th trace character on the cohomological class is the odd trace-power
sum minus the even trace-power sum. -/
theorem traceCharacterK0_cohomologicalEndomorphismClass_pow
    (degrees : Finset ℤ) (F : ∀ i, Module.End K (V i)) (n : ℕ) :
    Boundary.EndomorphismK0.traceCharacterK0 K n
        (cohomologicalEndomorphismClass (V := V) degrees F) =
      (∑ i in degrees.filter (fun i => Odd i),
          LinearMap.trace K (V i) ((F i) ^ n)) -
        ∑ i in degrees.filter (fun i => Even i),
          LinearMap.trace K (V i) ((F i) ^ n) := by
  simp [cohomologicalEndomorphismClass, endomorphismObject,
    Boundary.EndomorphismK0.EndomorphismObject.tracePower]

/-- Powering every degreewise endomorphism is the same as applying the K₀ power
map to the cohomological virtual endomorphism class. -/
theorem cohomologicalEndomorphismClass_power_eq_powerMapK0
    (degrees : Finset ℤ) (F : ∀ i, Module.End K (V i)) (n : ℕ) :
    cohomologicalEndomorphismClass (V := V) degrees (fun i => (F i) ^ n) =
      Boundary.EndomorphismK0.powerMapK0 K n
        (cohomologicalEndomorphismClass (V := V) degrees F) := by
  simp [cohomologicalEndomorphismClass, endomorphismObject,
    Boundary.EndomorphismK0.EndomorphismObject.power]

/-- The ordinary trace character of the powered cohomological class agrees with
the `n`th trace-power character of the original class. -/
theorem traceCharacterK0_one_powered_cohomologicalEndomorphismClass
    (degrees : Finset ℤ) (F : ∀ i, Module.End K (V i)) (n : ℕ) :
    Boundary.EndomorphismK0.traceCharacterK0 K 1
        (cohomologicalEndomorphismClass (V := V) degrees (fun i => (F i) ^ n)) =
      Boundary.EndomorphismK0.traceCharacterK0 K n
        (cohomologicalEndomorphismClass (V := V) degrees F) := by
  rw [cohomologicalEndomorphismClass_power_eq_powerMapK0]
  exact Boundary.EndomorphismK0.traceCharacterK0_one_powerMapK0 K n
    (cohomologicalEndomorphismClass (V := V) degrees F)

/-- The formal logarithm of the cohomological local zeta factor, expressed as
the alternating logarithm of its determinant factors. This is the additive
logarithm of the same virtual endomorphism class used by `determinantCharacterK0`. -/
def localZetaFormalLog (degrees : Finset ℤ) (F : ∀ i, Module.End K (V i)) :
    K⟦X⟧ :=
  (∑ i in degrees.filter (fun i => Odd i),
      Boundary.TraceExpansion.formalLog
        (LinearEulerFactor.eulerPolynomial (F i) : K⟦X⟧)) -
    ∑ i in degrees.filter (fun i => Even i),
      Boundary.TraceExpansion.formalLog
        (LinearEulerFactor.eulerPolynomial (F i) : K⟦X⟧)

/-- Coefficients of the cohomological logarithmic trace expansion are controlled
by the trace-power character of the same virtual endomorphism class. -/
theorem coeff_localZetaFormalLog_eq_neg_traceCharacterK0
    [CharZero K] (degrees : Finset ℤ) (F : ∀ i, Module.End K (V i))
    (n : ℕ) (hn : n ≠ 0) :
    PowerSeries.coeff K n (localZetaFormalLog (V := V) degrees F) =
      -Boundary.EndomorphismK0.traceCharacterK0 K n
        (cohomologicalEndomorphismClass (V := V) degrees F) / (n : K) := by
  rw [localZetaFormalLog]
  rw [map_sub, map_sum, map_sum]
  simp_rw [Boundary.TraceExpansion.coeff_formalLog_eulerPolynomial_eq_neg_trace_pow
    (K := K) (m := n) (hm := hn)]
  rw [traceCharacterK0_cohomologicalEndomorphismClass_pow]
  rw [← Finset.sum_div, ← Finset.sum_div]
  rw [Finset.sum_neg_distrib, Finset.sum_neg_distrib]
  rw [← sub_div]
  rw [show
    -∑ x in degrees.filter (fun i => Odd i), LinearMap.trace K (V x) (F x ^ n) -
        -∑ x in degrees.filter (fun i => Even i), LinearMap.trace K (V x) (F x ^ n) =
      -(∑ x in degrees.filter (fun i => Odd i), LinearMap.trace K (V x) (F x ^ n) -
        ∑ x in degrees.filter (fun i => Even i), LinearMap.trace K (V x) (F x ^ n)) by
      rw [neg_sub]
      rw [sub_eq_add_neg, neg_neg]
      rw [add_comm]
      rw [← sub_eq_add_neg]]

/-- Coefficient form using the K₀ power operation explicitly. -/
theorem coeff_localZetaFormalLog_eq_trace_powerMapK0
    [CharZero K] (degrees : Finset ℤ) (F : ∀ i, Module.End K (V i))
    (n : ℕ) (hn : n ≠ 0) :
    PowerSeries.coeff K n (localZetaFormalLog (V := V) degrees F) =
      -Boundary.EndomorphismK0.traceCharacterK0 K 1
          (Boundary.EndomorphismK0.powerMapK0 K n
            (cohomologicalEndomorphismClass (V := V) degrees F)) / (n : K) := by
  rw [coeff_localZetaFormalLog_eq_neg_traceCharacterK0 (V := V) degrees F n hn]
  rw [← Boundary.EndomorphismK0.traceCharacterK0_one_powerMapK0]

/-- The cohomological formal logarithm is the K₀ trace logarithm of the
cohomological virtual endomorphism class. -/
theorem localZetaFormalLog_eq_tracePowerLog
    [CharZero K] (degrees : Finset ℤ) (F : ∀ i, Module.End K (V i)) :
    localZetaFormalLog (V := V) degrees F =
      Boundary.K0TraceLog.tracePowerLog K
        (cohomologicalEndomorphismClass (V := V) degrees F) := by
  apply PowerSeries.ext
  intro n
  by_cases hn : n = 0
  · subst n
    rw [localZetaFormalLog]
    rw [map_sub, map_sum, map_sum]
    simp [Boundary.TraceExpansion.coeff_formalLog_zero]
  · rw [coeff_localZetaFormalLog_eq_trace_powerMapK0 (V := V) degrees F n hn]
    rw [Boundary.K0TraceLog.coeff_tracePowerLog (K := K)
      (cohomologicalEndomorphismClass (V := V) degrees F) n hn]

/-- The cohomological formal logarithm is the determinant/Euler logarithm of
the cohomological virtual class. -/
theorem localZetaFormalLog_eq_eulerLog
    [CharZero K] (degrees : Finset ℤ) (F : ∀ i, Module.End K (V i)) :
    localZetaFormalLog (V := V) degrees F =
      Boundary.EulerFactorLog.eulerLog K
        (cohomologicalEndomorphismClass (V := V) degrees F) := by
  rw [Boundary.EulerFactorLog.eulerLog]
  exact localZetaFormalLog_eq_tracePowerLog (V := V) degrees F

/-- The reciprocal local zeta logarithm attached to the same cohomological
virtual class. This is the negative of the determinant/Euler logarithm. -/
def reciprocalLocalZetaFormalLog
    (degrees : Finset ℤ) (F : ∀ i, Module.End K (V i)) : K⟦X⟧ :=
  Boundary.EulerFactorLog.zetaLog K
    (cohomologicalEndomorphismClass (V := V) degrees F)

/-- The reciprocal local zeta logarithm is the negative of the determinant
cohomological formal logarithm. -/
theorem reciprocalLocalZetaFormalLog_eq_neg_localZetaFormalLog
    [CharZero K] (degrees : Finset ℤ) (F : ∀ i, Module.End K (V i)) :
    reciprocalLocalZetaFormalLog (V := V) degrees F =
      -localZetaFormalLog (V := V) degrees F := by
  rw [reciprocalLocalZetaFormalLog]
  rw [localZetaFormalLog_eq_eulerLog (V := V) degrees F]
  rfl

/-- Positive coefficients of the reciprocal cohomological local zeta logarithm
carry the positive trace-power sign. -/
theorem coeff_reciprocalLocalZetaFormalLog_eq_trace_powerMapK0
    [CharZero K] (degrees : Finset ℤ) (F : ∀ i, Module.End K (V i))
    (n : ℕ) (hn : n ≠ 0) :
    PowerSeries.coeff K n (reciprocalLocalZetaFormalLog (V := V) degrees F) =
      Boundary.EndomorphismK0.traceCharacterK0 K 1
          (Boundary.EndomorphismK0.powerMapK0 K n
            (cohomologicalEndomorphismClass (V := V) degrees F)) / (n : K) := by
  rw [reciprocalLocalZetaFormalLog]
  exact Boundary.EulerFactorLog.coeff_zetaLog (K := K)
    (cohomologicalEndomorphismClass (V := V) degrees F) n hn

@[simp]
theorem localZetaFormalLog_empty (F : ∀ i, Module.End K (V i)) :
    localZetaFormalLog (V := V) ∅ F = 0 := by
  simp [localZetaFormalLog]

@[simp]
theorem coeff_localZetaFormalLog_zero
    (degrees : Finset ℤ) (F : ∀ i, Module.End K (V i)) :
    PowerSeries.coeff K 0 (localZetaFormalLog (V := V) degrees F) = 0 := by
  rw [localZetaFormalLog]
  rw [map_sub, map_sum, map_sum]
  simp [Boundary.TraceExpansion.coeff_formalLog_zero]

@[simp]
theorem localZetaFormalLog_conj (degrees : Finset ℤ)
    (F : ∀ i, Module.End K (V i)) (e : ∀ i, V i ≃ₗ[K] W i) :
    localZetaFormalLog (V := W) degrees (fun i => (e i).conj (F i)) =
      localZetaFormalLog (V := V) degrees F := by
  simp [localZetaFormalLog, eulerPolynomial_conj]

/-- Coefficients of the logarithmic cohomological factor are invariant under
degreewise conjugacy. -/
theorem coeff_localZetaFormalLog_conj (degrees : Finset ℤ)
    (F : ∀ i, Module.End K (V i)) (e : ∀ i, V i ≃ₗ[K] W i) (n : ℕ) :
    PowerSeries.coeff K n
        (localZetaFormalLog (V := W) degrees (fun i => (e i).conj (F i))) =
      PowerSeries.coeff K n (localZetaFormalLog (V := V) degrees F) := by
  rw [localZetaFormalLog_conj]

/-- The normalized linear coefficient of the local zeta factor, computed from
its numerator and denominator with both constant coefficients equal to `1`. -/
def localZetaLinearCoeff (degrees : Finset ℤ) (F : ∀ i, Module.End K (V i)) : K :=
  (localNumerator (V := V) degrees F).coeff 1 -
    (localDenominator (V := V) degrees F).coeff 1

/-- The first-order term of the cohomological local zeta factor is controlled
by the first trace character of the same virtual endomorphism class. -/
theorem localZetaLinearCoeff_eq_neg_traceCharacterK0
    (degrees : Finset ℤ) (F : ∀ i, Module.End K (V i)) :
    localZetaLinearCoeff (V := V) degrees F =
      -Boundary.EndomorphismK0.traceCharacterK0 K 1
        (cohomologicalEndomorphismClass (V := V) degrees F) := by
  rw [localZetaLinearCoeff, localNumerator_coeff_one, localDenominator_coeff_one,
    traceCharacterK0_cohomologicalEndomorphismClass]
  rw [neg_sub]
  rw [sub_eq_add_neg, neg_neg]
  rw [add_comm]
  rw [← sub_eq_add_neg]

/-- Equivalent concrete form of the first-order trace expansion: even degrees
contribute positively and odd degrees negatively. -/
theorem localZetaLinearCoeff_eq_alternatingTrace
    (degrees : Finset ℤ) (F : ∀ i, Module.End K (V i)) :
    localZetaLinearCoeff (V := V) degrees F =
      (∑ i in degrees.filter (fun i => Even i), LinearMap.trace K (V i) (F i)) -
        ∑ i in degrees.filter (fun i => Odd i), LinearMap.trace K (V i) (F i) := by
  rw [localZetaLinearCoeff, localNumerator_coeff_one, localDenominator_coeff_one]
  rw [sub_eq_add_neg, neg_neg]
  rw [add_comm]
  rw [← sub_eq_add_neg]

/-- The determinant character of the virtual cohomological class recovers the
concrete cohomological local zeta factor. -/
theorem determinantCharacterK0_cohomologicalEndomorphismClass
    (degrees : Finset ℤ) (F : ∀ i, Module.End K (V i)) :
    ((Boundary.EndomorphismK0.determinantCharacterK0Mul K
        (Multiplicative.ofAdd (cohomologicalEndomorphismClass (V := V) degrees F)) :
        (RatFunc K)ˣ) : RatFunc K) =
      localZetaFactorRatFunc (V := V) degrees F := by
  simp [cohomologicalEndomorphismClass, localZetaFactorRatFunc, localNumerator, localDenominator,
    Boundary.EndomorphismK0.determinantCharacterK0Mul,
    Boundary.EndomorphismK0.EndomorphismObject.determinantUnit,
    Boundary.EndomorphismK0.EndomorphismObject.determinantRatFunc,
    endomorphismObject, div_eq_mul_inv]

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

@[simp]
theorem localNumerator_empty (F : ∀ i, Module.End K (V i)) :
    localNumerator (V := V) ∅ F = 1 := by
  simp [localNumerator]

@[simp]
theorem localDenominator_empty (F : ∀ i, Module.End K (V i)) :
    localDenominator (V := V) ∅ F = 1 := by
  simp [localDenominator]

@[simp]
theorem localZetaFactorRatFunc_empty (F : ∀ i, Module.End K (V i)) :
    localZetaFactorRatFunc (V := V) ∅ F = 1 := by
  simp [localZetaFactorRatFunc]

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
