import Boundary.LFunctionsRootedTreeCanonicalAll._outside_RH_rooted_import_cone.CohomologicalEulerFactor.EndomorphismK0.EndomorphismK0
import Boundary.LFunctionsRootedTreeCanonicalAll._outside_RH_rooted_import_cone.CohomologicalEulerFactor.EulerFactorLog.EulerFactorLog
import Boundary.LFunctionsRootedTreeCanonicalAll._outside_RH_rooted_import_cone.CohomologicalEulerFactor.K0TraceLog.K0TraceLog
import Boundary.LFunctionsRootedTreeCanonicalAll._outside_RH_rooted_import_cone.CohomologicalEulerFactor.TraceExpansion.TraceExpansion
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

theorem sub_neg_sub_eq_neg_sub {G : Type*} [AddCommGroup G] (a b : G) :
    -a - -b = -(a - b) :=
  Eq.trans
    (sub_eq_add_neg (-a) (-b))
    (Eq.trans
      (congrArg (fun t : G => -a + t) (neg_neg b))
      (Eq.trans
        (add_comm (-a) b)
        (Eq.trans
          (congrArg (fun t : G => t) (sub_eq_add_neg b a).symm)
          (neg_sub a b).symm)))

theorem neg_sub_eq_sub_swap {G : Type*} [AddCommGroup G] (a b : G) :
    -(a - b) = b - a :=
  neg_sub a b

theorem neg_trace_sub_eq_alternating_trace (odd even : K) :
    -odd - -even = -(odd - even) :=
  sub_neg_sub_eq_neg_sub odd even

theorem alternating_trace_sign_swap (odd even : K) :
    -odd - -even = even - odd :=
  Eq.trans
    (sub_neg_sub_eq_neg_sub odd even)
    (neg_sub_eq_sub_swap odd even)

theorem finset_prod_congr_same_set {ι α : Type*} [CommMonoid α]
    (s : Finset ι) {f g : ι → α} (h : ∀ i ∈ s, f i = g i) :
    (∏ i in s, f i) = ∏ i in s, g i :=
  Finset.prod_congr (Eq.refl s) h

theorem finset_prod_mul_distrib_explicit {ι α : Type*} [CommMonoid α]
    (s : Finset ι) (f g : ι → α) :
    (∏ i in s, f i * g i) = (∏ i in s, f i) * ∏ i in s, g i :=
  Finset.prod_mul_distrib

theorem eulerPolynomial_eval_zero_eq_one {i : ℤ} (F : Module.End K (V i)) :
    (LinearEulerFactor.eulerPolynomial F).eval 0 = 1 :=
  LinearEulerFactor.eulerFactor_zero F

theorem product_eulerPolynomial_eval_zero_eq_one
    (s : Finset ℤ) (F : ∀ i, Module.End K (V i)) :
    (∏ i in s, LinearEulerFactor.eulerPolynomial (F i)).eval 0 = 1 :=
  Eq.trans
    (Polynomial.eval_prod s (fun i => LinearEulerFactor.eulerPolynomial (F i)) 0)
    (Finset.prod_eq_one
      (fun i _ => eulerPolynomial_eval_zero_eq_one (V := V) (F i)))

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
theorem polynomial_one_coeff_one_eq_zero :
    (1 : Polynomial K).coeff 1 = 0 :=
  Eq.trans
    (Polynomial.coeff_one (R := K) (n := 1))
    (if_neg Nat.one_ne_zero)

theorem prod_coeff_one_empty {ι : Type*} (p : ι → Polynomial K) :
    (∏ i in (∅ : Finset ι), p i).coeff 1 =
      ∑ i in (∅ : Finset ι), (p i).coeff 1 :=
  Eq.trans
    (congrArg (fun q : Polynomial K => q.coeff 1) (Finset.prod_empty : ∏ i in (∅ : Finset ι), p i = 1))
    (Eq.trans polynomial_one_coeff_one_eq_zero (Finset.sum_empty.symm))

theorem prod_coeff_zero_eq_one_of_coeff_zero_eq_one {ι : Type*}
    (s : Finset ι) (p : ι → Polynomial K)
    (h0 : ∀ i ∈ s, (p i).coeff 0 = 1) :
    (∏ i in s, p i).coeff 0 = 1 :=
  Eq.trans
    (Polynomial.coeff_zero_prod s p)
    (Finset.prod_eq_one h0)

theorem coeff_one_insert_algebra (a b : K) :
    1 * b + a * 1 = a + b :=
  Eq.trans
    (congrArg₂ HAdd.hAdd (one_mul b) (mul_one a))
    (add_comm b a)

theorem prod_coeff_one_insert_step {ι : Type*} [DecidableEq ι]
    (a : ι) (s : Finset ι) (ha : a ∉ s) (p : ι → Polynomial K)
    (hp0 : (p a).coeff 0 = 1)
    (hprod0 : (∏ x in s, p x).coeff 0 = 1)
    (ih : (∏ x in s, p x).coeff 1 = ∑ x in s, (p x).coeff 1) :
    (∏ x in insert a s, p x).coeff 1 =
      ∑ x in insert a s, (p x).coeff 1 :=
  Eq.trans
    (congrArg (fun q : Polynomial K => q.coeff 1) (Finset.prod_insert ha))
    (Eq.trans
      (Polynomial.mul_coeff_one (p a) (∏ x in s, p x))
      (Eq.trans
        (congrArg₂ HAdd.hAdd
          (congrArg₂ HMul.hMul hp0 ih)
          (congrArg (fun t : K => (p a).coeff 1 * t) hprod0))
        (Eq.trans
          (coeff_one_insert_algebra
            ((p a).coeff 1) (∑ x in s, (p x).coeff 1))
          (Finset.sum_insert (s := s) (f := fun x => (p x).coeff 1) ha).symm)))

theorem prod_coeff_one_of_coeff_zero_eq_one {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (p : ι → Polynomial K)
    (h0 : ∀ i ∈ s, (p i).coeff 0 = 1) :
    (∏ i in s, p i).coeff 1 = ∑ i in s, (p i).coeff 1 :=
  Finset.induction_on s
    (fun _ => prod_coeff_one_empty p)
    (fun a s ha ih h0 =>
      prod_coeff_one_insert_step a s ha p
        (h0 a (Finset.mem_insert_self a s))
        (prod_coeff_zero_eq_one_of_coeff_zero_eq_one s p
          (fun x hx => h0 x (Finset.mem_insert_of_mem hx)))
        (ih (fun i hi => h0 i (Finset.mem_insert_of_mem hi))))
    h0

theorem sum_eulerPolynomial_coeff_one_eq_neg_trace_sum
    (s : Finset ℤ) (F : ∀ i, Module.End K (V i)) :
    (∑ i in s, (LinearEulerFactor.eulerPolynomial (F i)).coeff 1) =
      -∑ i in s, LinearMap.trace K (V i) (F i) :=
  Eq.trans
    (Finset.sum_congr (Eq.refl s)
      (fun i _ => LinearEulerFactor.eulerPolynomial_coeff_one_trace (F i)))
    (Finset.sum_neg_distrib)

theorem product_eulerPolynomial_coeff_one_eq_neg_trace_sum
    (s : Finset ℤ) (F : ∀ i, Module.End K (V i)) :
    (∏ i in s, LinearEulerFactor.eulerPolynomial (F i)).coeff 1 =
      -∑ i in s, LinearMap.trace K (V i) (F i) :=
  Eq.trans
    (prod_coeff_one_of_coeff_zero_eq_one s
      (fun i => LinearEulerFactor.eulerPolynomial (F i))
      (fun i _ => LinearEulerFactor.eulerPolynomial_coeff_zero (F i)))
    (sum_eulerPolynomial_coeff_one_eq_neg_trace_sum s F)

/-- The linear coefficient of the numerator is the negative sum of traces in
odd degrees. -/
theorem localNumerator_coeff_one (degrees : Finset ℤ)
    (F : ∀ i, Module.End K (V i)) :
    (localNumerator (V := V) degrees F).coeff 1 =
      -∑ i in degrees.filter (fun i => Odd i), LinearMap.trace K (V i) (F i) :=
  product_eulerPolynomial_coeff_one_eq_neg_trace_sum
  (V := V) (degrees.filter (fun i => Odd i)) F

/-- The linear coefficient of the denominator is the negative sum of traces in
even degrees. -/
theorem localDenominator_coeff_one (degrees : Finset ℤ)
    (F : ∀ i, Module.End K (V i)) :
    (localDenominator (V := V) degrees F).coeff 1 =
      -∑ i in degrees.filter (fun i => Even i), LinearMap.trace K (V i) (F i) :=
  product_eulerPolynomial_coeff_one_eq_neg_trace_sum
  (V := V) (degrees.filter (fun i => Even i)) F

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

theorem traceCharacterK0_sum_endomorphismObject
    (s : Finset ℤ) (F : ∀ i, Module.End K (V i)) (n : ℕ) :
    Boundary.EndomorphismK0.traceCharacterK0 K n
        (∑ i in s,
          Boundary.EndomorphismK0.mk K
            (Boundary.EndomorphismK0.of K (endomorphismObject (V := V) F i))) =
      ∑ i in s, LinearMap.trace K (V i) ((F i) ^ n) :=
  Eq.trans
    (map_sum (Boundary.EndomorphismK0.traceCharacterK0 K n)
      (fun i =>
        Boundary.EndomorphismK0.mk K
          (Boundary.EndomorphismK0.of K (endomorphismObject (V := V) F i))) s)
    (Finset.sum_congr (Eq.refl s)
      (fun i _ =>
        Boundary.EndomorphismK0.traceCharacterK0_of
          (K := K) n (endomorphismObject (V := V) F i)))

theorem powerMapK0_sum_endomorphismObject
    (s : Finset ℤ) (F : ∀ i, Module.End K (V i)) (n : ℕ) :
    Boundary.EndomorphismK0.powerMapK0 K n
        (∑ i in s,
          Boundary.EndomorphismK0.mk K
            (Boundary.EndomorphismK0.of K (endomorphismObject (V := V) F i))) =
      ∑ i in s,
          Boundary.EndomorphismK0.mk K
            (Boundary.EndomorphismK0.of K
              (endomorphismObject (V := V) (fun j => (F j) ^ n) i)) :=
  Eq.trans
    (map_sum (Boundary.EndomorphismK0.powerMapK0 K n)
      (fun i =>
        Boundary.EndomorphismK0.mk K
          (Boundary.EndomorphismK0.of K (endomorphismObject (V := V) F i))) s)
    (Finset.sum_congr (Eq.refl s)
      (fun i _ =>
        Boundary.EndomorphismK0.powerMapK0_of
          (K := K) n (endomorphismObject (V := V) F i)))

omit [∀ i, FiniteDimensional K (V i)] in
theorem trace_pow_one_eq_trace {i : ℤ} (F : Module.End K (V i)) :
    LinearMap.trace K (V i) (F ^ 1) = LinearMap.trace K (V i) F :=
  congrArg (LinearMap.trace K (V i)) (pow_one F)

omit [∀ i, FiniteDimensional K (V i)] in
theorem sum_trace_pow_one_eq_trace
    (s : Finset ℤ) (F : ∀ i, Module.End K (V i)) :
    (∑ i in s, LinearMap.trace K (V i) ((F i) ^ 1)) =
      ∑ i in s, LinearMap.trace K (V i) (F i) :=
  Finset.sum_congr (Eq.refl s) (fun i _ => trace_pow_one_eq_trace (V := V) (F i))

theorem sum_formalLog_eulerPolynomial_conj
    (s : Finset ℤ) (F : ∀ i, Module.End K (V i)) (e : ∀ i, V i ≃ₗ[K] W i) :
    (∑ i in s,
      Boundary.TraceExpansion.formalLog
        (LinearEulerFactor.eulerPolynomial ((e i).conj (F i)) : K⟦X⟧)) =
      ∑ i in s,
        Boundary.TraceExpansion.formalLog
          (LinearEulerFactor.eulerPolynomial (F i) : K⟦X⟧) :=
  Finset.sum_congr (Eq.refl s)
    (fun i _ =>
      congrArg
        (fun p : Polynomial K =>
          Boundary.TraceExpansion.formalLog (p : K⟦X⟧))
        (LinearEulerFactor.eulerPolynomial_conj (e i) (F i)))

/-- The `n`th trace character on the cohomological class is the odd trace-power
sum minus the even trace-power sum. -/
theorem traceCharacterK0_cohomologicalEndomorphismClass_pow
    (degrees : Finset ℤ) (F : ∀ i, Module.End K (V i)) (n : ℕ) :
    Boundary.EndomorphismK0.traceCharacterK0 K n
        (cohomologicalEndomorphismClass (V := V) degrees F) =
      (∑ i in degrees.filter (fun i => Odd i),
          LinearMap.trace K (V i) ((F i) ^ n)) -
        ∑ i in degrees.filter (fun i => Even i),
          LinearMap.trace K (V i) ((F i) ^ n) :=
  Eq.trans
  (map_sub (Boundary.EndomorphismK0.traceCharacterK0 K n)
    (∑ i in degrees.filter (fun i => Odd i),
      Boundary.EndomorphismK0.mk K
        (Boundary.EndomorphismK0.of K (endomorphismObject (V := V) F i)))
    (∑ i in degrees.filter (fun i => Even i),
      Boundary.EndomorphismK0.mk K
        (Boundary.EndomorphismK0.of K (endomorphismObject (V := V) F i))))
  (congrArg₂ Sub.sub
    (traceCharacterK0_sum_endomorphismObject
      (V := V) (degrees.filter (fun i => Odd i)) F n)
    (traceCharacterK0_sum_endomorphismObject
      (V := V) (degrees.filter (fun i => Even i)) F n))

/-- The first trace character on the cohomological class is the odd trace sum
minus the even trace sum. -/
theorem traceCharacterK0_cohomologicalEndomorphismClass
    (degrees : Finset ℤ) (F : ∀ i, Module.End K (V i)) :
    Boundary.EndomorphismK0.traceCharacterK0 K 1
        (cohomologicalEndomorphismClass (V := V) degrees F) =
      (∑ i in degrees.filter (fun i => Odd i), LinearMap.trace K (V i) (F i)) -
        ∑ i in degrees.filter (fun i => Even i), LinearMap.trace K (V i) (F i) :=
  Eq.trans
  (traceCharacterK0_cohomologicalEndomorphismClass_pow (V := V) degrees F 1)
  (congrArg₂ Sub.sub
    (sum_trace_pow_one_eq_trace (V := V) (degrees.filter (fun i => Odd i)) F)
    (sum_trace_pow_one_eq_trace (V := V) (degrees.filter (fun i => Even i)) F))

/-- Powering every degreewise endomorphism is the same as applying the K₀ power
map to the cohomological virtual endomorphism class. -/
theorem cohomologicalEndomorphismClass_power_eq_powerMapK0
    (degrees : Finset ℤ) (F : ∀ i, Module.End K (V i)) (n : ℕ) :
    cohomologicalEndomorphismClass (V := V) degrees (fun i => (F i) ^ n) =
      Boundary.EndomorphismK0.powerMapK0 K n
        (cohomologicalEndomorphismClass (V := V) degrees F) :=
  Eq.trans
  (congrArg₂ Sub.sub
    (powerMapK0_sum_endomorphismObject
      (V := V) (degrees.filter (fun i => Odd i)) F n).symm
    (powerMapK0_sum_endomorphismObject
      (V := V) (degrees.filter (fun i => Even i)) F n).symm)
  (map_sub (Boundary.EndomorphismK0.powerMapK0 K n)
    (∑ i in degrees.filter (fun i => Odd i),
      Boundary.EndomorphismK0.mk K
        (Boundary.EndomorphismK0.of K (endomorphismObject (V := V) F i)))
    (∑ i in degrees.filter (fun i => Even i),
      Boundary.EndomorphismK0.mk K
        (Boundary.EndomorphismK0.of K (endomorphismObject (V := V) F i)))).symm

/-- The ordinary trace character of the powered cohomological class agrees with
the `n`th trace-power character of the original class. -/
theorem traceCharacterK0_one_powered_cohomologicalEndomorphismClass
    (degrees : Finset ℤ) (F : ∀ i, Module.End K (V i)) (n : ℕ) :
    Boundary.EndomorphismK0.traceCharacterK0 K 1
        (cohomologicalEndomorphismClass (V := V) degrees (fun i => (F i) ^ n)) =
      Boundary.EndomorphismK0.traceCharacterK0 K n
        (cohomologicalEndomorphismClass (V := V) degrees F) :=
  Eq.trans
  (congrArg (Boundary.EndomorphismK0.traceCharacterK0 K 1)
    (cohomologicalEndomorphismClass_power_eq_powerMapK0 (V := V) degrees F n))
  (Boundary.EndomorphismK0.traceCharacterK0_one_powerMapK0 K n
    (cohomologicalEndomorphismClass (V := V) degrees F))

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

theorem coeff_zero_sum_formalLog_eulerPolynomial
    (s : Finset ℤ) (F : ∀ i, Module.End K (V i)) :
    PowerSeries.coeff K 0
        (∑ i in s,
          Boundary.TraceExpansion.formalLog
            (LinearEulerFactor.eulerPolynomial (F i) : K⟦X⟧)) = 0 :=
  Eq.trans
    (map_sum (PowerSeries.coeff K 0)
      (fun i =>
        Boundary.TraceExpansion.formalLog
          (LinearEulerFactor.eulerPolynomial (F i) : K⟦X⟧)) s)
    (Finset.sum_eq_zero
      (fun i _ =>
        Boundary.TraceExpansion.coeff_formalLog_zero
          (K := K) (LinearEulerFactor.eulerPolynomial (F i) : K⟦X⟧)))

theorem coeff_zero_sub_zero (a b : K⟦X⟧)
    (ha : PowerSeries.coeff K 0 a = 0)
    (hb : PowerSeries.coeff K 0 b = 0) :
    PowerSeries.coeff K 0 (a - b) = 0 :=
  Eq.trans
    (map_sub (PowerSeries.coeff K 0) a b)
    (Eq.trans (congrArg₂ Sub.sub ha hb) (sub_self 0))

omit [∀ i, FiniteDimensional K (V i)] in
theorem sum_neg_trace_div_eq_neg_sum_div
    (s : Finset ℤ) (F : ∀ i, Module.End K (V i)) (n : ℕ) :
    (∑ i in s, -LinearMap.trace K (V i) ((F i) ^ n) / (n : K)) =
      -(∑ i in s, LinearMap.trace K (V i) ((F i) ^ n)) / (n : K) :=
  Eq.trans
    (Finset.sum_congr (Eq.refl s)
      (fun i _ => neg_div (n : K) (LinearMap.trace K (V i) ((F i) ^ n))))
    (Eq.trans
      (Finset.sum_neg_distrib)
      (Eq.trans
        (congrArg Neg.neg
          (Finset.sum_div s
            (fun i => LinearMap.trace K (V i) ((F i) ^ n)) (n : K)).symm)
        (neg_div (n : K) (∑ i in s, LinearMap.trace K (V i) ((F i) ^ n))).symm))

theorem coeff_sum_formalLog_eulerPolynomial_eq_neg_trace_div
    [CharZero K] (s : Finset ℤ) (F : ∀ i, Module.End K (V i))
    (n : ℕ) (hn : n ≠ 0) :
    PowerSeries.coeff K n
        (∑ i in s,
          Boundary.TraceExpansion.formalLog
            (LinearEulerFactor.eulerPolynomial (F i) : K⟦X⟧)) =
      -(∑ i in s, LinearMap.trace K (V i) ((F i) ^ n)) / (n : K) :=
  Eq.trans
    (map_sum (PowerSeries.coeff K n)
      (fun i =>
        Boundary.TraceExpansion.formalLog
          (LinearEulerFactor.eulerPolynomial (F i) : K⟦X⟧)) s)
    (Eq.trans
      (Finset.sum_congr (Eq.refl s)
        (fun i _ =>
          Boundary.TraceExpansion.coeff_formalLog_eulerPolynomial_eq_neg_trace_pow
            (K := K) (F := F i) (m := n) (hm := hn)))
      (sum_neg_trace_div_eq_neg_sum_div (V := V) s F n))

theorem neg_div_sub_neg_div_eq_neg_sub_div (a b c : K) :
    -a / c - -b / c = -(a - b) / c :=
  Eq.trans
    (sub_div (-a) (-b) c).symm
    (congrArg (fun t : K => t / c) (sub_neg_sub_eq_neg_sub a b))

theorem coeff_sub_formalLog_sums_eq_neg_trace_sub_div
    [CharZero K] (s t : Finset ℤ) (F : ∀ i, Module.End K (V i))
    (n : ℕ) (hn : n ≠ 0) :
    PowerSeries.coeff K n
        ((∑ i in s,
          Boundary.TraceExpansion.formalLog
            (LinearEulerFactor.eulerPolynomial (F i) : K⟦X⟧)) -
        (∑ i in t,
          Boundary.TraceExpansion.formalLog
            (LinearEulerFactor.eulerPolynomial (F i) : K⟦X⟧))) =
      -((∑ i in s, LinearMap.trace K (V i) ((F i) ^ n)) -
        ∑ i in t, LinearMap.trace K (V i) ((F i) ^ n)) / (n : K) :=
  Eq.trans
    (map_sub (PowerSeries.coeff K n)
      (∑ i in s,
        Boundary.TraceExpansion.formalLog
          (LinearEulerFactor.eulerPolynomial (F i) : K⟦X⟧))
      (∑ i in t,
        Boundary.TraceExpansion.formalLog
          (LinearEulerFactor.eulerPolynomial (F i) : K⟦X⟧)))
    (Eq.trans
      (congrArg₂ Sub.sub
        (coeff_sum_formalLog_eulerPolynomial_eq_neg_trace_div (V := V) s F n hn)
        (coeff_sum_formalLog_eulerPolynomial_eq_neg_trace_div (V := V) t F n hn))
      (neg_div_sub_neg_div_eq_neg_sub_div
        (∑ i in s, LinearMap.trace K (V i) ((F i) ^ n))
        (∑ i in t, LinearMap.trace K (V i) ((F i) ^ n))
        (n : K)))

theorem coeff_localZetaFormalLog_zero
    (degrees : Finset ℤ) (F : ∀ i, Module.End K (V i)) :
    PowerSeries.coeff K 0 (localZetaFormalLog (V := V) degrees F) = 0 :=
  coeff_zero_sub_zero
  (∑ i in degrees.filter (fun i => Odd i),
    Boundary.TraceExpansion.formalLog
      (LinearEulerFactor.eulerPolynomial (F i) : K⟦X⟧))
  (∑ i in degrees.filter (fun i => Even i),
    Boundary.TraceExpansion.formalLog
      (LinearEulerFactor.eulerPolynomial (F i) : K⟦X⟧))
  (coeff_zero_sum_formalLog_eulerPolynomial (V := V)
    (degrees.filter (fun i => Odd i)) F)
  (coeff_zero_sum_formalLog_eulerPolynomial (V := V)
    (degrees.filter (fun i => Even i)) F)

/-- Coefficients of the cohomological logarithmic trace expansion are controlled
by the trace-power character of the same virtual endomorphism class. -/
theorem coeff_localZetaFormalLog_eq_neg_traceCharacterK0
    [CharZero K] (degrees : Finset ℤ) (F : ∀ i, Module.End K (V i))
    (n : ℕ) (hn : n ≠ 0) :
    PowerSeries.coeff K n (localZetaFormalLog (V := V) degrees F) =
      -Boundary.EndomorphismK0.traceCharacterK0 K n
        (cohomologicalEndomorphismClass (V := V) degrees F) / (n : K) :=
  Eq.trans
  (coeff_sub_formalLog_sums_eq_neg_trace_sub_div
    (V := V) (degrees.filter (fun i => Odd i))
    (degrees.filter (fun i => Even i)) F n hn)
  (congrArg (fun t : K => -t / (n : K))
    (traceCharacterK0_cohomologicalEndomorphismClass_pow (V := V) degrees F n).symm)

/-- Coefficient form using the K₀ power operation explicitly. -/
theorem coeff_localZetaFormalLog_eq_trace_powerMapK0
    [CharZero K] (degrees : Finset ℤ) (F : ∀ i, Module.End K (V i))
    (n : ℕ) (hn : n ≠ 0) :
    PowerSeries.coeff K n (localZetaFormalLog (V := V) degrees F) =
      -Boundary.EndomorphismK0.traceCharacterK0 K 1
          (Boundary.EndomorphismK0.powerMapK0 K n
            (cohomologicalEndomorphismClass (V := V) degrees F)) / (n : K) :=
  Eq.trans
  (coeff_localZetaFormalLog_eq_neg_traceCharacterK0 (V := V) degrees F n hn)
  (congrArg
    (fun t : K => -t / (n : K))
    (Boundary.EndomorphismK0.traceCharacterK0_one_powerMapK0 K n
      (cohomologicalEndomorphismClass (V := V) degrees F)).symm)

theorem coeff_localZetaFormalLog_eq_tracePowerLog_coeff_zero
    [CharZero K] (degrees : Finset ℤ) (F : ∀ i, Module.End K (V i)) :
    PowerSeries.coeff K 0 (localZetaFormalLog (V := V) degrees F) =
      PowerSeries.coeff K 0
        (Boundary.K0TraceLog.tracePowerLog K
          (cohomologicalEndomorphismClass (V := V) degrees F)) :=
  Eq.trans
    (coeff_localZetaFormalLog_zero (V := V) degrees F)
    (Boundary.K0TraceLog.coeff_tracePowerLog_zero K
      (cohomologicalEndomorphismClass (V := V) degrees F)).symm

theorem coeff_localZetaFormalLog_eq_tracePowerLog_coeff_ne_zero
    [CharZero K] (degrees : Finset ℤ) (F : ∀ i, Module.End K (V i))
    (n : ℕ) (hn : n ≠ 0) :
    PowerSeries.coeff K n (localZetaFormalLog (V := V) degrees F) =
      PowerSeries.coeff K n
        (Boundary.K0TraceLog.tracePowerLog K
          (cohomologicalEndomorphismClass (V := V) degrees F)) :=
  Eq.trans
    (coeff_localZetaFormalLog_eq_trace_powerMapK0 (V := V) degrees F n hn)
    (Boundary.K0TraceLog.coeff_tracePowerLog (K := K)
      (cohomologicalEndomorphismClass (V := V) degrees F) n hn).symm

theorem coeff_localZetaFormalLog_eq_tracePowerLog_coeff_eq_zero
    [CharZero K] (degrees : Finset ℤ) (F : ∀ i, Module.End K (V i))
    {n : ℕ} (hn : n = 0) :
    PowerSeries.coeff K n (localZetaFormalLog (V := V) degrees F) =
      PowerSeries.coeff K n
        (Boundary.K0TraceLog.tracePowerLog K
          (cohomologicalEndomorphismClass (V := V) degrees F)) :=
  Eq.subst
    (motive := fun m : ℕ =>
      PowerSeries.coeff K m (localZetaFormalLog (V := V) degrees F) =
        PowerSeries.coeff K m
          (Boundary.K0TraceLog.tracePowerLog K
            (cohomologicalEndomorphismClass (V := V) degrees F)))
    hn.symm
    (coeff_localZetaFormalLog_eq_tracePowerLog_coeff_zero (V := V) degrees F)

theorem coeff_localZetaFormalLog_eq_tracePowerLog_coeff
    [CharZero K] (degrees : Finset ℤ) (F : ∀ i, Module.End K (V i))
    (n : ℕ) :
    PowerSeries.coeff K n (localZetaFormalLog (V := V) degrees F) =
      PowerSeries.coeff K n
        (Boundary.K0TraceLog.tracePowerLog K
          (cohomologicalEndomorphismClass (V := V) degrees F)) :=
  match eq_or_ne n 0 with
  | Or.inl hn =>
      coeff_localZetaFormalLog_eq_tracePowerLog_coeff_eq_zero (V := V) degrees F hn
  | Or.inr hn =>
      coeff_localZetaFormalLog_eq_tracePowerLog_coeff_ne_zero (V := V) degrees F n hn

/-- The cohomological formal logarithm is the K₀ trace logarithm of the
cohomological virtual endomorphism class. -/
theorem localZetaFormalLog_eq_tracePowerLog
    [CharZero K] (degrees : Finset ℤ) (F : ∀ i, Module.End K (V i)) :
    localZetaFormalLog (V := V) degrees F =
      Boundary.K0TraceLog.tracePowerLog K
        (cohomologicalEndomorphismClass (V := V) degrees F) :=
  PowerSeries.ext
  (coeff_localZetaFormalLog_eq_tracePowerLog_coeff (V := V) degrees F)

/-- The cohomological formal logarithm is the determinant/Euler logarithm of
the cohomological virtual class. -/
theorem localZetaFormalLog_eq_eulerLog
    [CharZero K] (degrees : Finset ℤ) (F : ∀ i, Module.End K (V i)) :
    localZetaFormalLog (V := V) degrees F =
      Boundary.EulerFactorLog.eulerLog K
        (cohomologicalEndomorphismClass (V := V) degrees F) :=
  localZetaFormalLog_eq_tracePowerLog (V := V) degrees F

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
      -localZetaFormalLog (V := V) degrees F :=
  congrArg Neg.neg (localZetaFormalLog_eq_eulerLog (V := V) degrees F).symm

/-- Positive coefficients of the reciprocal cohomological local zeta logarithm
carry the positive trace-power sign. -/
theorem coeff_reciprocalLocalZetaFormalLog_eq_trace_powerMapK0
    [CharZero K] (degrees : Finset ℤ) (F : ∀ i, Module.End K (V i))
    (n : ℕ) (hn : n ≠ 0) :
    PowerSeries.coeff K n (reciprocalLocalZetaFormalLog (V := V) degrees F) =
      Boundary.EndomorphismK0.traceCharacterK0 K 1
          (Boundary.EndomorphismK0.powerMapK0 K n
            (cohomologicalEndomorphismClass (V := V) degrees F)) / (n : K) :=
  Boundary.EulerFactorLog.coeff_zetaLog (K := K)
  (cohomologicalEndomorphismClass (V := V) degrees F) n hn

theorem localZetaFormalLog_empty (F : ∀ i, Module.End K (V i)) :
    localZetaFormalLog (V := V) ∅ F = 0 :=
  Eq.trans
  (congrArg₂ Sub.sub
    (Finset.sum_empty :
      (∑ i in (∅ : Finset ℤ),
        Boundary.TraceExpansion.formalLog
          (LinearEulerFactor.eulerPolynomial (F i) : K⟦X⟧)) = 0)
    (Finset.sum_empty :
      (∑ i in (∅ : Finset ℤ),
        Boundary.TraceExpansion.formalLog
          (LinearEulerFactor.eulerPolynomial (F i) : K⟦X⟧)) = 0))
  (sub_self 0)

theorem localZetaFormalLog_conj (degrees : Finset ℤ)
    (F : ∀ i, Module.End K (V i)) (e : ∀ i, V i ≃ₗ[K] W i) :
    localZetaFormalLog (V := W) degrees (fun i => (e i).conj (F i)) =
      localZetaFormalLog (V := V) degrees F :=
  congrArg₂ Sub.sub
  (sum_formalLog_eulerPolynomial_conj
    (V := V) (W := W) (degrees.filter (fun i => Odd i)) F e)
  (sum_formalLog_eulerPolynomial_conj
    (V := V) (W := W) (degrees.filter (fun i => Even i)) F e)

/-- Coefficients of the logarithmic cohomological factor are invariant under
degreewise conjugacy. -/
theorem coeff_localZetaFormalLog_conj (degrees : Finset ℤ)
    (F : ∀ i, Module.End K (V i)) (e : ∀ i, V i ≃ₗ[K] W i) (n : ℕ) :
    PowerSeries.coeff K n
        (localZetaFormalLog (V := W) degrees (fun i => (e i).conj (F i))) =
      PowerSeries.coeff K n (localZetaFormalLog (V := V) degrees F) :=
  congrArg (PowerSeries.coeff K n)
  (localZetaFormalLog_conj (V := V) (W := W) degrees F e)

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
        (cohomologicalEndomorphismClass (V := V) degrees F) :=
  Eq.trans
  (congrArg₂ Sub.sub
    (localNumerator_coeff_one (V := V) degrees F)
    (localDenominator_coeff_one (V := V) degrees F))
  (Eq.trans
    (neg_trace_sub_eq_alternating_trace
      (∑ i in degrees.filter (fun i => Odd i), LinearMap.trace K (V i) (F i))
      (∑ i in degrees.filter (fun i => Even i), LinearMap.trace K (V i) (F i)))
    (congrArg Neg.neg
      (traceCharacterK0_cohomologicalEndomorphismClass (V := V) degrees F).symm))

/-- Equivalent concrete form of the first-order trace expansion: even degrees
contribute positively and odd degrees negatively. -/
theorem localZetaLinearCoeff_eq_alternatingTrace
    (degrees : Finset ℤ) (F : ∀ i, Module.End K (V i)) :
    localZetaLinearCoeff (V := V) degrees F =
      (∑ i in degrees.filter (fun i => Even i), LinearMap.trace K (V i) (F i)) -
        ∑ i in degrees.filter (fun i => Odd i), LinearMap.trace K (V i) (F i) :=
  Eq.trans
  (congrArg₂ Sub.sub
    (localNumerator_coeff_one (V := V) degrees F)
    (localDenominator_coeff_one (V := V) degrees F))
  (alternating_trace_sign_swap
    (∑ i in degrees.filter (fun i => Odd i), LinearMap.trace K (V i) (F i))
    (∑ i in degrees.filter (fun i => Even i), LinearMap.trace K (V i) (F i)))

theorem coe_determinantUnit_endomorphismObject
    (F : ∀ i, Module.End K (V i)) (i : ℤ) :
    ((Boundary.EndomorphismK0.EndomorphismObject.determinantUnit
        (endomorphismObject (V := V) F i) : (RatFunc K)ˣ) : RatFunc K) =
      algebraMap (Polynomial K) (RatFunc K) (LinearEulerFactor.eulerPolynomial (F i)) :=
  Eq.refl
    ((Boundary.EndomorphismK0.EndomorphismObject.determinantUnit
      (endomorphismObject (V := V) F i) : (RatFunc K)ˣ) : RatFunc K)

theorem coe_prod_determinantUnit_endomorphismObject
    (s : Finset ℤ) (F : ∀ i, Module.End K (V i)) :
    (((∏ i in s,
      Boundary.EndomorphismK0.EndomorphismObject.determinantUnit
        (endomorphismObject (V := V) F i)) : (RatFunc K)ˣ) : RatFunc K) =
      algebraMap (Polynomial K) (RatFunc K)
        (∏ i in s, LinearEulerFactor.eulerPolynomial (F i)) :=
  Eq.trans
    (map_prod (Units.coeHom (RatFunc K))
      (fun i =>
        Boundary.EndomorphismK0.EndomorphismObject.determinantUnit
          (endomorphismObject (V := V) F i)) s)
    (Eq.trans
      (Finset.prod_congr (Eq.refl s)
        (fun i _ => coe_determinantUnit_endomorphismObject (V := V) F i))
      (map_prod (algebraMap (Polynomial K) (RatFunc K))
        (fun i => LinearEulerFactor.eulerPolynomial (F i)) s).symm)

/-- The determinant character of the virtual cohomological class recovers the
concrete cohomological local zeta factor. -/
theorem determinantCharacterK0_cohomologicalEndomorphismClass
    (degrees : Finset ℤ) (F : ∀ i, Module.End K (V i)) :
    ((Boundary.EndomorphismK0.determinantCharacterK0Mul K
        (Multiplicative.ofAdd (cohomologicalEndomorphismClass (V := V) degrees F)) :
        (RatFunc K)ˣ) : RatFunc K) =
      localZetaFactorRatFunc (V := V) degrees F :=
  Eq.trans
    (congrArg (fun u : (RatFunc K)ˣ => (u : RatFunc K))
      (Boundary.EndomorphismK0.determinantCharacterK0Mul_sub_sum_of
        (K := K)
        (degrees.filter (fun i => Odd i))
        (degrees.filter (fun i => Even i))
        (fun i => endomorphismObject (V := V) F i)
        (fun i => endomorphismObject (V := V) F i)))
    (Eq.trans
      (Units.val_div_eq_div_val
        (∏ i in degrees.filter (fun i => Odd i),
          Boundary.EndomorphismK0.EndomorphismObject.determinantUnit
            (endomorphismObject (V := V) F i))
        (∏ i in degrees.filter (fun i => Even i),
          Boundary.EndomorphismK0.EndomorphismObject.determinantUnit
            (endomorphismObject (V := V) F i)))
      (congrArg₂ HDiv.hDiv
        (coe_prod_determinantUnit_endomorphismObject
          (V := V) (degrees.filter (fun i => Odd i)) F)
        (coe_prod_determinantUnit_endomorphismObject
          (V := V) (degrees.filter (fun i => Even i)) F)))

/-- Numerators are invariant under degreewise linear conjugacy. -/
theorem localNumerator_conj (degrees : Finset ℤ)
    (F : ∀ i, Module.End K (V i)) (e : ∀ i, V i ≃ₗ[K] W i) :
    localNumerator (V := W) degrees (fun i => (e i).conj (F i)) =
      localNumerator (V := V) degrees F :=
  finset_prod_congr_same_set
  (degrees.filter (fun i => Odd i))
  (fun i _ => LinearEulerFactor.eulerPolynomial_conj (e i) (F i))

/-- Denominators are invariant under degreewise linear conjugacy. -/
theorem localDenominator_conj (degrees : Finset ℤ)
    (F : ∀ i, Module.End K (V i)) (e : ∀ i, V i ≃ₗ[K] W i) :
    localDenominator (V := W) degrees (fun i => (e i).conj (F i)) =
      localDenominator (V := V) degrees F :=
  finset_prod_congr_same_set
  (degrees.filter (fun i => Even i))
  (fun i _ => LinearEulerFactor.eulerPolynomial_conj (e i) (F i))

/-- The rational local zeta factor is invariant under degreewise linear
conjugacy. -/
theorem localZetaFactorRatFunc_conj (degrees : Finset ℤ)
    (F : ∀ i, Module.End K (V i)) (e : ∀ i, V i ≃ₗ[K] W i) :
    localZetaFactorRatFunc (V := W) degrees (fun i => (e i).conj (F i)) =
      localZetaFactorRatFunc (V := V) degrees F :=
  congrArg₂ HDiv.hDiv
  (congrArg (algebraMap (Polynomial K) (RatFunc K))
    (localNumerator_conj (V := V) (W := W) degrees F e))
  (congrArg (algebraMap (Polynomial K) (RatFunc K))
    (localDenominator_conj (V := V) (W := W) degrees F e))

/-- The numerator is normalized to evaluate to `1` at `T = 0`. -/
theorem localNumerator_eval_zero (degrees : Finset ℤ)
    (F : ∀ i, Module.End K (V i)) :
    (localNumerator (V := V) degrees F).eval 0 = 1 :=
  product_eulerPolynomial_eval_zero_eq_one
  (V := V) (degrees.filter (fun i => Odd i)) F

/-- The denominator is normalized to evaluate to `1` at `T = 0`. -/
theorem localDenominator_eval_zero (degrees : Finset ℤ)
    (F : ∀ i, Module.End K (V i)) :
    (localDenominator (V := V) degrees F).eval 0 = 1 :=
  product_eulerPolynomial_eval_zero_eq_one
  (V := V) (degrees.filter (fun i => Even i)) F

theorem localNumerator_empty (F : ∀ i, Module.End K (V i)) :
    localNumerator (V := V) ∅ F = 1 :=
  Finset.prod_empty

theorem localDenominator_empty (F : ∀ i, Module.End K (V i)) :
    localDenominator (V := V) ∅ F = 1 :=
  Finset.prod_empty

theorem one_div_one_ratFunc : (1 : RatFunc K) / 1 = 1 :=
  one_div_one

theorem algebraMap_one_div_one_ratFunc :
    algebraMap (Polynomial K) (RatFunc K) 1 /
        algebraMap (Polynomial K) (RatFunc K) 1 =
      (1 : RatFunc K) / 1 :=
  congrArg₂ HDiv.hDiv
    (map_one (algebraMap (Polynomial K) (RatFunc K)))
    (map_one (algebraMap (Polynomial K) (RatFunc K)))

theorem localZetaFactorRatFunc_empty_from_parts (F : ∀ i, Module.End K (V i)) :
    localZetaFactorRatFunc (V := V) ∅ F =
      algebraMap (Polynomial K) (RatFunc K) 1 /
        algebraMap (Polynomial K) (RatFunc K) 1 :=
  congrArg₂ HDiv.hDiv
    (congrArg (algebraMap (Polynomial K) (RatFunc K)) (localNumerator_empty (V := V) F))
    (congrArg (algebraMap (Polynomial K) (RatFunc K)) (localDenominator_empty (V := V) F))

theorem localZetaFactorRatFunc_empty (F : ∀ i, Module.End K (V i)) :
    localZetaFactorRatFunc (V := V) ∅ F = 1 :=
  Eq.trans
  (localZetaFactorRatFunc_empty_from_parts (V := V) F)
  (Eq.trans algebraMap_one_div_one_ratFunc one_div_one_ratFunc)

/-- Numerators multiply for degreewise product endomorphisms. -/
theorem localNumerator_prodMap (degrees : Finset ℤ)
    (F : ∀ i, Module.End K (V i)) (G : ∀ i, Module.End K (W i)) :
    localNumerator (V := fun i => V i × W i) degrees
        (fun i => (F i).prodMap (G i)) =
      localNumerator (V := V) degrees F * localNumerator (V := W) degrees G :=
  Eq.trans
  (finset_prod_congr_same_set
    (degrees.filter (fun i => Odd i))
    (fun i _ => LinearEulerFactor.eulerPolynomial_prodMap (F i) (G i)))
  (finset_prod_mul_distrib_explicit
    (degrees.filter (fun i => Odd i))
    (fun i => LinearEulerFactor.eulerPolynomial (F i))
    (fun i => LinearEulerFactor.eulerPolynomial (G i)))

/-- Denominators multiply for degreewise product endomorphisms. -/
theorem localDenominator_prodMap (degrees : Finset ℤ)
    (F : ∀ i, Module.End K (V i)) (G : ∀ i, Module.End K (W i)) :
    localDenominator (V := fun i => V i × W i) degrees
        (fun i => (F i).prodMap (G i)) =
      localDenominator (V := V) degrees F * localDenominator (V := W) degrees G :=
  Eq.trans
  (finset_prod_congr_same_set
    (degrees.filter (fun i => Even i))
    (fun i _ => LinearEulerFactor.eulerPolynomial_prodMap (F i) (G i)))
  (finset_prod_mul_distrib_explicit
    (degrees.filter (fun i => Even i))
    (fun i => LinearEulerFactor.eulerPolynomial (F i))
    (fun i => LinearEulerFactor.eulerPolynomial (G i)))

theorem localZetaFactorRatFunc_prodMap_from_parts (degrees : Finset ℤ)
    (F : ∀ i, Module.End K (V i)) (G : ∀ i, Module.End K (W i)) :
    localZetaFactorRatFunc (V := fun i => V i × W i) degrees
        (fun i => (F i).prodMap (G i)) =
      algebraMap (Polynomial K) (RatFunc K)
          (localNumerator (V := V) degrees F * localNumerator (V := W) degrees G) /
        algebraMap (Polynomial K) (RatFunc K)
          (localDenominator (V := V) degrees F * localDenominator (V := W) degrees G) :=
  congrArg₂ HDiv.hDiv
  (congrArg (algebraMap (Polynomial K) (RatFunc K))
    (localNumerator_prodMap (V := V) (W := W) degrees F G))
  (congrArg (algebraMap (Polynomial K) (RatFunc K))
    (localDenominator_prodMap (V := V) (W := W) degrees F G))

theorem localZetaFactorRatFunc_prodMap_algebra (degrees : Finset ℤ)
    (F : ∀ i, Module.End K (V i)) (G : ∀ i, Module.End K (W i)) :
    algebraMap (Polynomial K) (RatFunc K)
          (localNumerator (V := V) degrees F * localNumerator (V := W) degrees G) /
        algebraMap (Polynomial K) (RatFunc K)
          (localDenominator (V := V) degrees F * localDenominator (V := W) degrees G) =
      localZetaFactorRatFunc (V := V) degrees F *
        localZetaFactorRatFunc (V := W) degrees G :=
  Eq.trans
  (congrArg₂ HDiv.hDiv
    (map_mul (algebraMap (Polynomial K) (RatFunc K))
      (localNumerator (V := V) degrees F)
      (localNumerator (V := W) degrees G))
    (map_mul (algebraMap (Polynomial K) (RatFunc K))
      (localDenominator (V := V) degrees F)
      (localDenominator (V := W) degrees G)))
  (div_mul_div_comm
    (algebraMap (Polynomial K) (RatFunc K) (localNumerator (V := V) degrees F))
    (algebraMap (Polynomial K) (RatFunc K) (localDenominator (V := V) degrees F))
    (algebraMap (Polynomial K) (RatFunc K) (localNumerator (V := W) degrees G))
    (algebraMap (Polynomial K) (RatFunc K) (localDenominator (V := W) degrees G))).symm

/-- Rational local zeta factors multiply for degreewise product endomorphisms. -/
theorem localZetaFactorRatFunc_prodMap (degrees : Finset ℤ)
    (F : ∀ i, Module.End K (V i)) (G : ∀ i, Module.End K (W i)) :
    localZetaFactorRatFunc (V := fun i => V i × W i) degrees
        (fun i => (F i).prodMap (G i)) =
      localZetaFactorRatFunc (V := V) degrees F *
        localZetaFactorRatFunc (V := W) degrees G :=
  Eq.trans
  (localZetaFactorRatFunc_prodMap_from_parts (V := V) (W := W) degrees F G)
  (localZetaFactorRatFunc_prodMap_algebra (V := V) (W := W) degrees F G)

end

end CohomologicalEulerFactor
end Boundary
