import Boundary.LFunctions.EulerFactor
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.RingTheory.PowerSeries.Derivative

/-!
# Formal logarithmic trace expansions: core

This file owns the coefficientwise formal logarithm and the finite geometric
inverse lemmas used by the later Euler-factor and matrix trace expansion files.
-/

open scoped BigOperators PowerSeries

namespace Boundary
namespace TraceExpansion

noncomputable section

variable {K : Type*} [Field K]

def formalLog (f : K⟦X⟧) : K⟦X⟧ :=
  PowerSeries.mk fun n =>
    if n = 0 then 0
    else
      ∑ k in Finset.range (n + 1),
        ((-1 : K) ^ (k + 1) / (k : K)) *
          PowerSeries.coeff K n ((f - 1) ^ k)

@[simp]
theorem coeff_formalLog_zero (f : K⟦X⟧) :
    PowerSeries.coeff K 0 (formalLog f) = 0 := by
  exact (PowerSeries.coeff_mk 0 (fun n =>
    if n = 0 then 0 else
      ∑ k in Finset.range (n + 1),
        ((-1 : K) ^ (k + 1) / (k : K)) *
          PowerSeries.coeff K n ((f - 1) ^ k))).trans (if_pos rfl)

theorem coeff_formalLog_of_ne_zero (f : K⟦X⟧) {n : ℕ} (hn : n ≠ 0) :
    PowerSeries.coeff K n (formalLog f) =
      ∑ k in Finset.range (n + 1),
        ((-1 : K) ^ (k + 1) / (k : K)) *
          PowerSeries.coeff K n ((f - 1) ^ k) := by
  exact (PowerSeries.coeff_mk n (fun m =>
    if m = 0 then 0 else
      ∑ k in Finset.range (m + 1),
        ((-1 : K) ^ (k + 1) / (k : K)) *
          PowerSeries.coeff K m ((f - 1) ^ k))).trans (if_neg hn)

theorem coeff_derivative_formalLog (f : K⟦X⟧) (n : ℕ) :
    PowerSeries.coeff K n (PowerSeries.derivative K (formalLog f)) =
      PowerSeries.coeff K (n + 1) (formalLog f) * (n + 1 : K) := by
  exact PowerSeries.coeff_derivative (formalLog f) n

theorem coeff_smul_coeff
    (c : K) (f : K⟦X⟧) (n : ℕ) :
    PowerSeries.coeff K n (c • f) = c • PowerSeries.coeff K n f := by
  exact PowerSeries.coeff_smul n f c

theorem coeff_smul_powerSeries_eq_mul_coeff
    (c : K) (f : K⟦X⟧) (n : ℕ) :
    PowerSeries.coeff K n (c • f) = c • PowerSeries.coeff K n f := by
  exact coeff_smul_coeff (K := K) c f n

theorem coeff_C_mul_X_pow_eq_self {x : K} {n : ℕ} :
    PowerSeries.coeff K n (PowerSeries.C K x * PowerSeries.X ^ n : K⟦X⟧) = x := by
  calc
    PowerSeries.coeff K n (PowerSeries.C K x * PowerSeries.X ^ n : K⟦X⟧) =
        if n = n then x else 0 := by
          exact PowerSeries.coeff_C_mul_X_pow (R := K) x n n
    _ = x := by
          exact if_pos rfl

theorem coeff_C_mul_X_pow_eq_zero_of_ne {x : K} {m n : ℕ} (h : m ≠ n) :
    PowerSeries.coeff K m (PowerSeries.C K x * PowerSeries.X ^ n : K⟦X⟧) = 0 := by
  calc
    PowerSeries.coeff K m (PowerSeries.C K x * PowerSeries.X ^ n : K⟦X⟧) =
        if m = n then x else 0 := by
          exact PowerSeries.coeff_C_mul_X_pow (R := K) x n m
    _ = 0 := by
          exact if_neg h

theorem one_sub_scalar_factor_sub_one (a : K) :
    (1 - PowerSeries.C K a * PowerSeries.X : K⟦X⟧) - 1 =
      -(PowerSeries.C K a * PowerSeries.X) := by
  abel

def finiteGeomInverse (g : K⟦X⟧) (N : ℕ) : K⟦X⟧ :=
  ∑ r in Finset.range (N + 1), (-g) ^ r

theorem finiteGeomInverse_range_zero
    (g : K⟦X⟧) :
    (∑ r in Finset.range 1, (-g) ^ r) = (-g) ^ 0 := by
  calc
    ∑ r in Finset.range 1, (-g) ^ r =
        ∑ r in Finset.range 0, (-g) ^ r + (-g) ^ 0 := by
          exact Finset.sum_range_succ (fun r => (-g) ^ r) 0
    _ = (-g) ^ 0 := by
          exact zero_add ((-g) ^ 0)

theorem one_add_mul_finiteGeomInverse_core_succ_sum
    (g : K⟦X⟧) (N : ℕ) :
    ∑ r in Finset.range (N.succ + 1), (-g) ^ r =
      ∑ r in Finset.range (N + 1), (-g) ^ r + (-g) ^ (N + 1) := by
  exact Finset.sum_range_succ (fun r => (-g) ^ r) (N + 1)

theorem one_add_mul_finiteGeomInverse_core_succ_mul
    (g : K⟦X⟧) (N : ℕ) :
    (1 + g) * ((∑ r in Finset.range (N + 1), (-g) ^ r) + (-g) ^ (N + 1)) =
      (1 + g) * ∑ r in Finset.range (N + 1), (-g) ^ r +
        (1 + g) * (-g) ^ (N + 1) := by
  exact mul_add (1 + g) (∑ r in Finset.range (N + 1), (-g) ^ r) ((-g) ^ (N + 1))

theorem one_add_mul_finiteGeomInverse_core_succ_step_expand
    (g : K⟦X⟧) (N : ℕ) :
    (1 - (-g) ^ (N + 1)) + (1 + g) * (-g) ^ (N + 1) =
      (1 + (-(-g) ^ (N + 1))) + ((-g) ^ (N + 1) + g * (-g) ^ (N + 1)) := by
  have hsub : 1 - (-g) ^ (N + 1) = 1 + (-(-g) ^ (N + 1)) := by
    exact sub_eq_add_neg 1 ((-g) ^ (N + 1))
  have hmul : (1 + g) * (-g) ^ (N + 1) = (-g) ^ (N + 1) + g * (-g) ^ (N + 1) := by
    calc
      (1 + g) * (-g) ^ (N + 1) = 1 * (-g) ^ (N + 1) + g * (-g) ^ (N + 1) := by
        exact add_mul 1 g ((-g) ^ (N + 1))
      _ = (-g) ^ (N + 1) + g * (-g) ^ (N + 1) := by
        exact congrArg (fun t : K⟦X⟧ => t + g * (-g) ^ (N + 1))
          (one_mul ((-g) ^ (N + 1)))
  calc
    (1 - (-g) ^ (N + 1)) + (1 + g) * (-g) ^ (N + 1) =
        (1 + (-(-g) ^ (N + 1))) + ((1 + g) * (-g) ^ (N + 1)) := by
          exact congrArg (fun t : K⟦X⟧ => t + (1 + g) * (-g) ^ (N + 1)) hsub
    _ = (1 + (-(-g) ^ (N + 1))) + ((-g) ^ (N + 1) + g * (-g) ^ (N + 1)) := by
          exact congrArg (fun t : K⟦X⟧ => (1 + (-(-g) ^ (N + 1))) + t) hmul

theorem one_add_mul_finiteGeomInverse_core_succ_step_assoc
    (g : K⟦X⟧) (N : ℕ) :
    (1 + (-(-g) ^ (N + 1))) + ((-g) ^ (N + 1) + g * (-g) ^ (N + 1)) =
      1 + ((-(-g) ^ (N + 1)) + (-g) ^ (N + 1)) + g * (-g) ^ (N + 1) := by
  have h :=
    add_assoc 1 (-(-g) ^ (N + 1)) ((-g) ^ (N + 1) + g * (-g) ^ (N + 1))
  have h' :
      1 + ((-(-g) ^ (N + 1)) + ((-g) ^ (N + 1) + g * (-g) ^ (N + 1))) =
        1 + ((-(-g) ^ (N + 1)) + (-g) ^ (N + 1)) + g * (-g) ^ (N + 1) := by
    calc
      1 + ((-(-g) ^ (N + 1)) + ((-g) ^ (N + 1) + g * (-g) ^ (N + 1))) =
          1 + (((-(-g) ^ (N + 1)) + (-g) ^ (N + 1)) + g * (-g) ^ (N + 1)) := by
            exact congrArg (fun t : K⟦X⟧ => 1 + t)
              (Eq.symm (add_assoc (-(-g) ^ (N + 1)) ((-g) ^ (N + 1)) (g * (-g) ^ (N + 1))))
      _ = 1 + ((-(-g) ^ (N + 1)) + (-g) ^ (N + 1)) + g * (-g) ^ (N + 1) := by
            exact Eq.symm
              (add_assoc 1 ((-(-g) ^ (N + 1)) + (-g) ^ (N + 1)) (g * (-g) ^ (N + 1)))
  exact Eq.trans h h'

theorem one_add_mul_finiteGeomInverse_core_succ_step_cancel
    (g : K⟦X⟧) (N : ℕ) :
    1 + ((-(-g) ^ (N + 1)) + (-g) ^ (N + 1)) + g * (-g) ^ (N + 1) =
      1 + 0 + g * (-g) ^ (N + 1) := by
  exact congrArg (fun t : K⟦X⟧ => 1 + t + g * (-g) ^ (N + 1))
    (neg_add_cancel ((-g) ^ (N + 1)))

theorem one_add_mul_finiteGeomInverse_core_succ_step_zero_add
    (g : K⟦X⟧) (N : ℕ) :
    1 + 0 + g * (-g) ^ (N + 1) = 1 + g * (-g) ^ (N + 1) := by
  exact congrArg (fun t : K⟦X⟧ => t + g * (-g) ^ (N + 1)) (add_zero 1)

theorem one_add_mul_finiteGeomInverse_core_succ_step_pow
    (g : K⟦X⟧) (N : ℕ) :
    1 + g * (-g) ^ (N + 1) = 1 - ((-g) ^ (N + 1) * (-g)) := by
  have hcomm : g * (-g) ^ (N + 1) = -(((-g) ^ (N + 1)) * (-g)) := by
    calc
      g * (-g) ^ (N + 1) = (-g) ^ (N + 1) * g := by
        exact mul_comm g ((-g) ^ (N + 1))
      _ = -(((-g) ^ (N + 1)) * (-g)) := by
        exact Eq.trans (congrArg (fun t : K⟦X⟧ => (-g) ^ (N + 1) * t) (Eq.symm (neg_neg g)))
          (mul_neg ((-g) ^ (N + 1)) (-g))
  calc
    1 + g * (-g) ^ (N + 1) = 1 + (-(((-g) ^ (N + 1)) * (-g))) := by
      exact congrArg (fun t : K⟦X⟧ => 1 + t) hcomm
    _ = 1 - ((-g) ^ (N + 1) * (-g)) := by
      exact Eq.symm (sub_eq_add_neg 1 (((-g) ^ (N + 1)) * (-g)))

theorem one_add_mul_finiteGeomInverse_core_succ_step
    (g : K⟦X⟧) (N : ℕ) :
    (1 - (-g) ^ (N + 1)) + (1 + g) * (-g) ^ (N + 1) =
      1 - (-g) ^ (N.succ + 1) := by
  calc
    (1 - (-g) ^ (N + 1)) + (1 + g) * (-g) ^ (N + 1) =
        (1 + (-(-g) ^ (N + 1))) + ((-g) ^ (N + 1) + g * (-g) ^ (N + 1)) := by
          exact one_add_mul_finiteGeomInverse_core_succ_step_expand (K := K) g N
    _ = 1 + ((-(-g) ^ (N + 1)) + (-g) ^ (N + 1)) + g * (-g) ^ (N + 1) := by
          exact one_add_mul_finiteGeomInverse_core_succ_step_assoc (K := K) g N
    _ = 1 + 0 + g * (-g) ^ (N + 1) := by
          exact one_add_mul_finiteGeomInverse_core_succ_step_cancel (K := K) g N
    _ = 1 + g * (-g) ^ (N + 1) := by
          exact one_add_mul_finiteGeomInverse_core_succ_step_zero_add (K := K) g N
    _ = 1 - ((-g) ^ (N + 1) * (-g)) := by
          exact one_add_mul_finiteGeomInverse_core_succ_step_pow (K := K) g N
    _ = 1 - (-g) ^ (N.succ + 1) := by
          rfl

theorem one_add_mul_finiteGeomInverse_core_succ_explicit
    (g : K⟦X⟧) (N : ℕ)
    (ih : (1 + g) * ∑ r in Finset.range (N + 1), (-g) ^ r =
      1 - (-g) ^ (N + 1)) :
    (1 + g) * ∑ r in Finset.range (N.succ + 1), (-g) ^ r =
      1 - (-g) ^ (N.succ + 1) := by
  have hsum := one_add_mul_finiteGeomInverse_core_succ_sum (K := K) g N
  have hmul := one_add_mul_finiteGeomInverse_core_succ_mul (K := K) g N
  have hstep := one_add_mul_finiteGeomInverse_core_succ_step (K := K) g N
  calc
    (1 + g) * ∑ r in Finset.range (N.succ + 1), (-g) ^ r =
        (1 + g) * (∑ r in Finset.range (N + 1), (-g) ^ r + (-g) ^ (N + 1)) := by
          exact congrArg ((1 + g) * ·) hsum
    _ = (1 + g) * ∑ r in Finset.range (N + 1), (-g) ^ r +
        (1 + g) * (-g) ^ (N + 1) := hmul
    _ = (1 - (-g) ^ (N + 1)) + (1 + g) * (-g) ^ (N + 1) := by
          exact congrArg (fun t : K⟦X⟧ => t + (1 + g) * (-g) ^ (N + 1)) ih
    _ = 1 - (-g) ^ (N.succ + 1) := hstep

theorem one_add_mul_finiteGeomInverse_core_zero_reduce
    (g : K⟦X⟧) :
    (1 + g) * ((-g) ^ 0) = 1 - (-g) ^ 1 := by
  calc
    (1 + g) * ((-g) ^ 0) = (1 + g) * 1 := by
      exact congrArg (fun t : K⟦X⟧ => (1 + g) * t) (pow_zero (-g))
    _ = 1 + g := by
      exact mul_one (1 + g)
    _ = 1 - (-g) ^ 1 := by
      have h1 : (1 : K⟦X⟧) + g = 1 - (-g) := by
        calc
          (1 : K⟦X⟧) + g = 1 + -(-g) := by
            exact congrArg (fun t : K⟦X⟧ => (1 : K⟦X⟧) + t) (Eq.symm (neg_neg g))
          _ = 1 - (-g) := by
            exact Eq.symm (sub_eq_add_neg 1 (-g))
      have h2 : (1 : K⟦X⟧) - (-g) = 1 - (-g) ^ 1 := by
        exact congrArg (fun t : K⟦X⟧ => 1 - t) (pow_one (-g)).symm
      exact Eq.trans h1 h2

theorem one_add_mul_finiteGeomInverse_core_zero
    (g : K⟦X⟧) :
    (1 + g) * (∑ r in Finset.range 1, (-g) ^ r) = 1 - (-g) ^ 1 := by
  calc
    (1 + g) * (∑ r in Finset.range 1, (-g) ^ r) =
        (1 + g) * ((-g) ^ 0) := by
          exact congrArg (fun t : K⟦X⟧ => (1 + g) * t) (finiteGeomInverse_range_zero (K := K) g)
    _ = 1 - (-g) ^ 1 := by
          exact one_add_mul_finiteGeomInverse_core_zero_reduce (K := K) g

theorem one_add_mul_finiteGeomInverse_core_succ
    (g : K⟦X⟧) (N : ℕ)
    (ih : (1 + g) * ∑ r in Finset.range (N + 1), (-g) ^ r =
      1 - (-g) ^ (N + 1)) :
    (1 + g) * ∑ r in Finset.range (N.succ + 1), (-g) ^ r =
      1 - (-g) ^ (N.succ + 1) := by
  exact one_add_mul_finiteGeomInverse_core_succ_explicit (K := K) (g := g) (N := N) ih

theorem one_add_mul_finiteGeomInverse
    (g : K⟦X⟧) (N : ℕ) :
    (1 + g) * finiteGeomInverse (K := K) g N =
      1 - (-g) ^ (N + 1) := by
  change (1 + g) * (∑ r in Finset.range (N + 1), (-g) ^ r) =
    1 - (-g) ^ (N + 1)
  induction N with
  | zero =>
      exact one_add_mul_finiteGeomInverse_core_zero (K := K) g
  | succ N ih =>
      exact one_add_mul_finiteGeomInverse_core_succ (K := K) g N ih

theorem one_add_mul_finiteGeomInverse_geometric_identity_core
    (g : K⟦X⟧) (N : ℕ) :
    (1 + g) * finiteGeomInverse (K := K) g N =
      1 - (-g) ^ (N + 1) := by
  exact one_add_mul_finiteGeomInverse (K := K) g N

theorem one_add_mul_finiteGeomInverse_succ_step_core
    (g : K⟦X⟧) (N : ℕ) :
    (1 + g) * finiteGeomInverse (K := K) g (N + 1) =
      1 - (-g) ^ (N + 2) := by
  exact one_add_mul_finiteGeomInverse (K := K) g (N + 1)

theorem finiteGeomInverse_zero_core
    (g : K⟦X⟧) :
    finiteGeomInverse (K := K) g 0 = 1 := by
  change ∑ r in Finset.range 1, (-g) ^ r = 1
  calc
    ∑ r in Finset.range 1, (-g) ^ r = ∑ r in Finset.range 0, (-g) ^ r + (-g) ^ 0 := by
      exact Finset.sum_range_succ (fun r => (-g) ^ r) 0
    _ = 0 + (-g) ^ 0 := by
      rfl
    _ = 1 := by
      exact Eq.trans (zero_add ((-g) ^ 0)) (pow_zero (-g))

theorem finiteGeomInverse_succ_core
    (g : K⟦X⟧) (N : ℕ) :
    finiteGeomInverse (K := K) g (N + 1) =
      finiteGeomInverse (K := K) g N + (-g) ^ (N + 1) := by
  calc
    finiteGeomInverse (K := K) g (N + 1) =
        ∑ r in Finset.range (N + 2), (-g) ^ r := by
          rfl
    _ = ∑ r in Finset.range (N + 1), (-g) ^ r + (-g) ^ (N + 1) := by
          exact Finset.sum_range_succ (fun r => (-g) ^ r) (N + 1)
    _ = finiteGeomInverse (K := K) g N + (-g) ^ (N + 1) := by
          rfl

theorem one_add_mul_finiteGeomInverse_zero_core
    (g : K⟦X⟧) :
    (1 + g) * finiteGeomInverse (K := K) g 0 = 1 - (-g) ^ 1 := by
  exact one_add_mul_finiteGeomInverse (K := K) g 0

theorem one_add_mul_finiteGeomInverse_succ_core
    (g : K⟦X⟧) (N : ℕ) :
    (1 + g) * finiteGeomInverse (K := K) g (N + 1) =
      1 - (-g) ^ (N + 2) := by
  exact one_add_mul_finiteGeomInverse (K := K) g (N + 1)

theorem coeff_mul_pow_succ_eq_zero_from_X_factor_core
    {g q h : K⟦X⟧} {N d : ℕ}
    (hgx : g = PowerSeries.X * h) (hd : d < N + 1) :
    PowerSeries.coeff K d (q * g ^ (N + 1)) = 0 := by
  have hpow :
      g ^ (N + 1) = PowerSeries.X ^ (N + 1) * h ^ (N + 1) := by
    calc
      g ^ (N + 1) = (PowerSeries.X * h) ^ (N + 1) := by
        exact congrArg (fun t : K⟦X⟧ => t ^ (N + 1)) hgx
      _ = PowerSeries.X ^ (N + 1) * h ^ (N + 1) := by
        exact mul_pow PowerSeries.X h (N + 1)
  have hshift :
      q * (PowerSeries.X ^ (N + 1) * h ^ (N + 1)) =
        (q * h ^ (N + 1)) * PowerSeries.X ^ (N + 1) := by
    calc
      q * (PowerSeries.X ^ (N + 1) * h ^ (N + 1)) =
          q * (h ^ (N + 1) * PowerSeries.X ^ (N + 1)) := by
            exact congrArg (fun t : K⟦X⟧ => q * t)
              (mul_comm (PowerSeries.X ^ (N + 1)) (h ^ (N + 1)))
      _ = (q * h ^ (N + 1)) * PowerSeries.X ^ (N + 1) := by
            exact Eq.symm (mul_assoc q (h ^ (N + 1)) (PowerSeries.X ^ (N + 1)))
  have hcoeff :
      PowerSeries.coeff K d
        ((q * h ^ (N + 1)) * PowerSeries.X ^ (N + 1)) = 0 := by
    have hpow :
        PowerSeries.coeff K d
          (q * h ^ (N + 1) * PowerSeries.X ^ (N + 1)) =
            ite (N + 1 ≤ d) (PowerSeries.coeff K (d - (N + 1)) (q * h ^ (N + 1))) 0 := by
      exact PowerSeries.coeff_mul_X_pow' (R := K) (q * h ^ (N + 1)) (N + 1) d
    calc
      PowerSeries.coeff K d
          ((q * h ^ (N + 1)) * PowerSeries.X ^ (N + 1)) =
            ite (N + 1 ≤ d) (PowerSeries.coeff K (d - (N + 1)) (q * h ^ (N + 1))) 0 := by
              exact hpow
      _ = 0 := by
            exact if_neg hd.not_le
  calc
    PowerSeries.coeff K d (q * g ^ (N + 1)) =
        PowerSeries.coeff K d (q * (PowerSeries.X ^ (N + 1) * h ^ (N + 1))) := by
          exact congrArg (PowerSeries.coeff K d)
            (congrArg (fun t : K⟦X⟧ => q * t) hpow)
    _ = PowerSeries.coeff K d ((q * h ^ (N + 1)) * PowerSeries.X ^ (N + 1)) := by
          exact congrArg (PowerSeries.coeff K d) hshift
    _ = 0 := hcoeff

theorem coeff_mul_pow_succ_eq_zero_from_X_factor_power
    {g h : K⟦X⟧} {N : ℕ}
    (hgx : g = PowerSeries.X * h) :
    g ^ (N + 1) = PowerSeries.X ^ (N + 1) * h ^ (N + 1) := by
  calc
    g ^ (N + 1) = (PowerSeries.X * h) ^ (N + 1) := by
      exact congrArg (fun t : K⟦X⟧ => t ^ (N + 1)) hgx
    _ = PowerSeries.X ^ (N + 1) * h ^ (N + 1) := by
      exact mul_pow PowerSeries.X h (N + 1)

theorem coeff_mul_pow_succ_eq_zero_from_X_factor_shift
    {q h : K⟦X⟧} {N d : ℕ}
    (hd : d < N + 1) :
    PowerSeries.coeff K d
        ((q * h ^ (N + 1)) * PowerSeries.X ^ (N + 1)) = 0 := by
  have hpow :
      PowerSeries.coeff K d
        (q * h ^ (N + 1) * PowerSeries.X ^ (N + 1)) =
          ite (N + 1 ≤ d) (PowerSeries.coeff K (d - (N + 1)) (q * h ^ (N + 1))) 0 := by
    exact PowerSeries.coeff_mul_X_pow' (R := K) (q * h ^ (N + 1)) (N + 1) d
  calc
    PowerSeries.coeff K d
        ((q * h ^ (N + 1)) * PowerSeries.X ^ (N + 1)) =
          ite (N + 1 ≤ d) (PowerSeries.coeff K (d - (N + 1)) (q * h ^ (N + 1))) 0 := by
            exact hpow
    _ = 0 := by
          exact if_neg hd.not_le

theorem coeff_mul_pow_succ_eq_zero_from_X_factor_shift_core
    {q h : K⟦X⟧} {N d : ℕ}
    (hd : d < N + 1) :
    PowerSeries.coeff K d
        ((q * h ^ (N + 1)) * PowerSeries.X ^ (N + 1)) = 0 := by
  have hcoeff :
      PowerSeries.coeff K d ((q * h ^ (N + 1)) * PowerSeries.X ^ (N + 1)) =
        ite (N + 1 ≤ d) (PowerSeries.coeff K (d - (N + 1)) (q * h ^ (N + 1))) 0 := by
    exact PowerSeries.coeff_mul_X_pow' (R := K) (q * h ^ (N + 1)) (N + 1) d
  calc
    PowerSeries.coeff K d
        ((q * h ^ (N + 1)) * PowerSeries.X ^ (N + 1)) =
          ite (N + 1 ≤ d) (PowerSeries.coeff K (d - (N + 1)) (q * h ^ (N + 1))) 0 := hcoeff
    _ = 0 := by
          exact if_neg hd.not_le

theorem coeff_mul_pow_succ_eq_zero_from_X_factor_shift_transport_core
    {q h : K⟦X⟧} {N d : ℕ}
    (hd : d < N + 1) :
    PowerSeries.coeff K d
        ((q * h ^ (N + 1)) * PowerSeries.X ^ (N + 1)) = 0 := by
  exact coeff_mul_pow_succ_eq_zero_from_X_factor_shift_core (K := K) (q := q) (h := h)
    (N := N) (d := d) hd

theorem coeff_mul_pow_succ_eq_zero_from_X_factor_commute
    {q h : K⟦X⟧} {N : ℕ} :
    q * (PowerSeries.X ^ (N + 1) * h ^ (N + 1)) =
      (q * h ^ (N + 1)) * PowerSeries.X ^ (N + 1) := by
  calc
    q * (PowerSeries.X ^ (N + 1) * h ^ (N + 1)) =
        q * (h ^ (N + 1) * PowerSeries.X ^ (N + 1)) := by
          exact congrArg (fun t : K⟦X⟧ => q * t)
            (mul_comm (PowerSeries.X ^ (N + 1)) (h ^ (N + 1)))
    _ = (q * h ^ (N + 1)) * PowerSeries.X ^ (N + 1) := by
          exact Eq.symm (mul_assoc q (h ^ (N + 1)) (PowerSeries.X ^ (N + 1)))

theorem coeff_mul_pow_succ_eq_zero_from_X_factor_transport
    {g q h : K⟦X⟧} {N d : ℕ}
    (hgx : g = PowerSeries.X * h) (hd : d < N + 1) :
    PowerSeries.coeff K d (q * g ^ (N + 1)) = 0 := by
  have hpow :
      g ^ (N + 1) = PowerSeries.X ^ (N + 1) * h ^ (N + 1) := by
    exact coeff_mul_pow_succ_eq_zero_from_X_factor_power (K := K) (g := g) (h := h)
      (N := N) hgx
  have hshift :
      q * (PowerSeries.X ^ (N + 1) * h ^ (N + 1)) =
        (q * h ^ (N + 1)) * PowerSeries.X ^ (N + 1) := by
    exact coeff_mul_pow_succ_eq_zero_from_X_factor_commute (K := K) (q := q) (h := h)
      (N := N)
  have hcoeff :
      PowerSeries.coeff K d
        ((q * h ^ (N + 1)) * PowerSeries.X ^ (N + 1)) = 0 := by
    exact coeff_mul_pow_succ_eq_zero_from_X_factor_shift (K := K) (q := q) (h := h)
      (N := N) (d := d) hd
  calc
    PowerSeries.coeff K d (q * g ^ (N + 1)) =
        PowerSeries.coeff K d (q * (PowerSeries.X ^ (N + 1) * h ^ (N + 1))) := by
          exact congrArg (PowerSeries.coeff K d)
            (congrArg (fun t : K⟦X⟧ => q * t) hpow)
    _ = PowerSeries.coeff K d ((q * h ^ (N + 1)) * PowerSeries.X ^ (N + 1)) := by
          exact congrArg (PowerSeries.coeff K d) hshift
    _ = 0 := hcoeff

theorem coeff_mul_pow_succ_eq_zero_from_X_factor_aux
    {g q h : K⟦X⟧} {N d : ℕ}
    (hgx : g = PowerSeries.X * h) (hd : d < N + 1) :
    PowerSeries.coeff K d (q * g ^ (N + 1)) = 0 := by
  exact coeff_mul_pow_succ_eq_zero_from_X_factor_core (K := K) (g := g) (q := q) (h := h)
    (N := N) (d := d) hgx hd

theorem coeff_mul_pow_succ_eq_zero_from_X_factor' (g q h : K⟦X⟧) (N d : ℕ)
    (hgx : g = PowerSeries.X * h) (hd : d < N + 1) :
    PowerSeries.coeff K d (q * g ^ (N + 1)) = 0 := by
  exact coeff_mul_pow_succ_eq_zero_from_X_factor_core (K := K) (g := g) (q := q) (h := h) (N := N)
    (d := d) hgx hd

theorem coeff_mul_pow_succ_eq_zero_of_constantCoeff_eq_zero_core
    {g q : K⟦X⟧} {N d : ℕ}
    (hg : PowerSeries.constantCoeff K g = 0) (hd : d < N + 1) :
    PowerSeries.coeff K d (q * g ^ (N + 1)) = 0 := by
  obtain ⟨h, hh⟩ := (PowerSeries.X_dvd_iff (R := K) (φ := g)).mpr hg
  have hgx : g = PowerSeries.X * h := by
    exact hh
  exact coeff_mul_pow_succ_eq_zero_from_X_factor_aux (K := K) (g := g) (q := q) (h := h)
    hgx hd

theorem mul_assoc_right_swap
    {α : Type*} [CommMagma α] (a b c : α) :
    a * (b * c) = a * (c * b) := by
  calc
    a * (b * c) = a * (c * b) := by
      exact congrArg (fun t : α => a * t) (mul_comm b c)

theorem mul_assoc_left_right
    {α : Type*} [Semigroup α] (a b c : α) :
    a * (b * c) = (a * b) * c := by
  exact Eq.symm (mul_assoc a b c)

theorem coeff_mul_right_sub_coeff_sub
    {g q : K⟦X⟧} {N : ℕ} :
    q * (1 + g)⁻¹ * (1 - (-g) ^ (N + 1)) =
      q * (1 + g)⁻¹ - q * (1 + g)⁻¹ * (-g) ^ (N + 1) := by
  calc
    q * (1 + g)⁻¹ * (1 - (-g) ^ (N + 1)) =
        (q * (1 + g)⁻¹) * (1 - (-g) ^ (N + 1)) := by
          rfl
    _ = (q * (1 + g)⁻¹) * 1 - (q * (1 + g)⁻¹) * (-g) ^ (N + 1) := by
          exact mul_sub _ _ _
    _ = q * (1 + g)⁻¹ - q * (1 + g)⁻¹ * (-g) ^ (N + 1) := by
          exact congrArg (fun t : K⟦X⟧ => t - (q * (1 + g)⁻¹) * (-g) ^ (N + 1))
            (mul_one (q * (1 + g)⁻¹))

theorem coeff_mul_right_sub_coeff_eq_map_sub_eq_map
    {g q : K⟦X⟧} {N d : ℕ}
    (_ : PowerSeries.coeff K d (q * (1 + g)⁻¹ * (-g) ^ (N + 1)) = 0) :
    PowerSeries.coeff K d
        (q * (1 + g)⁻¹ * (1 - (-g) ^ (N + 1))) =
      PowerSeries.coeff K d (q * (1 + g)⁻¹) -
        PowerSeries.coeff K d (q * (1 + g)⁻¹ * (-g) ^ (N + 1)) := by
  have hmul :
      PowerSeries.coeff K d
          (q * (1 + g)⁻¹ * (1 - (-g) ^ (N + 1))) =
        PowerSeries.coeff K d
          (q * (1 + g)⁻¹ - q * (1 + g)⁻¹ * (-g) ^ (N + 1)) := by
    exact congrArg (PowerSeries.coeff K d)
      (coeff_mul_right_sub_coeff_sub (K := K) (g := g) (q := q) (N := N))
  have hshift :
      PowerSeries.coeff K d
          (q * (1 + g)⁻¹ - q * (1 + g)⁻¹ * (-g) ^ (N + 1)) =
        PowerSeries.coeff K d (q * (1 + g)⁻¹) -
          PowerSeries.coeff K d (q * (1 + g)⁻¹ * (-g) ^ (N + 1)) := by
    exact map_sub (PowerSeries.coeff K d) _ _
  exact Eq.trans hmul hshift

theorem coeff_mul_right_sub_coeff_eq_map_sub_eq_map_core_step
    {g q : K⟦X⟧} {N d : ℕ} :
    PowerSeries.coeff K d
        (q * (1 + g)⁻¹ * 1 - q * (1 + g)⁻¹ * (-g) ^ (N + 1)) =
      PowerSeries.coeff K d (q * (1 + g)⁻¹) -
        PowerSeries.coeff K d (q * (1 + g)⁻¹ * (-g) ^ (N + 1)) := by
  exact congrArg (PowerSeries.coeff K d)
    (by
      calc
        q * (1 + g)⁻¹ * 1 - q * (1 + g)⁻¹ * (-g) ^ (N + 1) =
            q * (1 + g)⁻¹ - q * (1 + g)⁻¹ * (-g) ^ (N + 1) := by
              exact congrArg
                (fun t : K⟦X⟧ => t - q * (1 + g)⁻¹ * (-g) ^ (N + 1))
                (mul_one (q * (1 + g)⁻¹))
        _ = q * (1 + g)⁻¹ - q * (1 + g)⁻¹ * (-g) ^ (N + 1) := by
              rfl)

theorem coeff_mul_right_sub_coeff_eq_map_sub_eq_map_core_step' 
    {g q : K⟦X⟧} {N d : ℕ} :
    PowerSeries.coeff K d
        (q * (1 + g)⁻¹ * 1 - q * (1 + g)⁻¹ * (-g) ^ (N + 1)) =
      PowerSeries.coeff K d (q * (1 + g)⁻¹) -
        PowerSeries.coeff K d (q * (1 + g)⁻¹ * (-g) ^ (N + 1)) := by
  exact coeff_mul_right_sub_coeff_eq_map_sub_eq_map_core_step (K := K) (g := g) (q := q)
    (N := N) (d := d)

theorem coeff_mul_right_sub_coeff_eq_core
    {g q : K⟦X⟧} {N d : ℕ}
    (hzero : PowerSeries.coeff K d (q * (1 + g)⁻¹ * (-g) ^ (N + 1)) = 0) :
    PowerSeries.coeff K d
        (q * (1 + g)⁻¹ * (1 - (-g) ^ (N + 1))) =
      PowerSeries.coeff K d (q * (1 + g)⁻¹) := by
  have hmap :
      PowerSeries.coeff K d
          (q * (1 + g)⁻¹ * (1 - (-g) ^ (N + 1))) =
        PowerSeries.coeff K d (q * (1 + g)⁻¹) -
          PowerSeries.coeff K d (q * (1 + g)⁻¹ * (-g) ^ (N + 1)) := by
    exact coeff_mul_right_sub_coeff_eq_map_sub_eq_map (K := K) (g := g) (q := q) (N := N)
      (d := d) hzero
  have hsub :
      PowerSeries.coeff K d (q * (1 + g)⁻¹) -
          PowerSeries.coeff K d (q * (1 + g)⁻¹ * (-g) ^ (N + 1)) =
        PowerSeries.coeff K d (q * (1 + g)⁻¹) - 0 := by
    exact congrArg
      (fun t : K => PowerSeries.coeff K d (q * (1 + g)⁻¹) - t) hzero
  calc
    PowerSeries.coeff K d
        (q * (1 + g)⁻¹ * (1 - (-g) ^ (N + 1))) =
      PowerSeries.coeff K d (q * (1 + g)⁻¹) -
        PowerSeries.coeff K d (q * (1 + g)⁻¹ * (-g) ^ (N + 1)) := hmap
    _ = PowerSeries.coeff K d (q * (1 + g)⁻¹) - 0 := hsub
    _ = PowerSeries.coeff K d (q * (1 + g)⁻¹) := by
          exact sub_zero _

theorem coeff_mul_right_sub_coeff_eq
    {g q : K⟦X⟧} {N d : ℕ}
    (hzero : PowerSeries.coeff K d (q * (1 + g)⁻¹ * (-g) ^ (N + 1)) = 0) :
    PowerSeries.coeff K d
        (q * (1 + g)⁻¹ * (1 - (-g) ^ (N + 1))) =
      PowerSeries.coeff K d (q * (1 + g)⁻¹) := by
  exact coeff_mul_right_sub_coeff_eq_core (K := K) (g := g) (q := q) (N := N) (d := d) hzero

theorem coeff_mul_right_sub_coeff_eq_map_sub_core
    {g q : K⟦X⟧} {N d : ℕ}
    (hzero : PowerSeries.coeff K d (q * (1 + g)⁻¹ * (-g) ^ (N + 1)) = 0) :
    PowerSeries.coeff K d
        (q * (1 + g)⁻¹ * (1 - (-g) ^ (N + 1))) =
      PowerSeries.coeff K d (q * (1 + g)⁻¹) -
        PowerSeries.coeff K d (q * (1 + g)⁻¹ * (-g) ^ (N + 1)) := by
  exact coeff_mul_right_sub_coeff_eq_map_sub_eq_map (K := K) (g := g) (q := q) (N := N)
    (d := d) hzero

theorem coeff_mul_right_sub_coeff_eq_of_hzero_core
    {g q : K⟦X⟧} {N d : ℕ}
    (hzero : PowerSeries.coeff K d (q * (1 + g)⁻¹ * (-g) ^ (N + 1)) = 0) :
    PowerSeries.coeff K d
        (q * (1 + g)⁻¹ * (1 - (-g) ^ (N + 1))) =
      PowerSeries.coeff K d (q * (1 + g)⁻¹) := by
  exact coeff_mul_right_sub_coeff_eq (K := K) (g := g) (q := q) (N := N) (d := d) hzero

theorem coeff_mul_right_sub_coeff_eq_zero_sub_core
    {g q : K⟦X⟧} {N d : ℕ}
    (hzero : PowerSeries.coeff K d (q * (1 + g)⁻¹ * (-g) ^ (N + 1)) = 0) :
    PowerSeries.coeff K d
        (q * (1 + g)⁻¹ * (1 - (-g) ^ (N + 1))) =
      PowerSeries.coeff K d (q * (1 + g)⁻¹) := by
  exact coeff_mul_right_sub_coeff_eq_of_hzero_core (K := K) (g := g) (q := q) (N := N) (d := d)
    hzero

theorem coeff_mul_right_sub_coeff_eq_zero_sub_cancel_core
    {g q : K⟦X⟧} {N d : ℕ}
    (hzero : PowerSeries.coeff K d (q * (1 + g)⁻¹ * (-g) ^ (N + 1)) = 0) :
    PowerSeries.coeff K d
        (q * (1 + g)⁻¹) -
        PowerSeries.coeff K d (q * (1 + g)⁻¹ * (-g) ^ (N + 1)) =
      PowerSeries.coeff K d (q * (1 + g)⁻¹) := by
  calc
    PowerSeries.coeff K d (q * (1 + g)⁻¹) -
        PowerSeries.coeff K d (q * (1 + g)⁻¹ * (-g) ^ (N + 1)) =
      PowerSeries.coeff K d (q * (1 + g)⁻¹) - 0 := by
        exact congrArg
          (fun t : K => PowerSeries.coeff K d (q * (1 + g)⁻¹) - t) hzero
    _ = PowerSeries.coeff K d (q * (1 + g)⁻¹) := by
        exact sub_zero _

theorem coeff_mul_right_sub_core_step
    {g q : K⟦X⟧} {N d : ℕ}
    (hzero : PowerSeries.coeff K d (q * (1 + g)⁻¹ * (-g) ^ (N + 1)) = 0) :
    PowerSeries.coeff K d (q * (1 + g)⁻¹) -
        PowerSeries.coeff K d (q * (1 + g)⁻¹ * (-g) ^ (N + 1)) =
      PowerSeries.coeff K d (q * (1 + g)⁻¹) := by
  exact coeff_mul_right_sub_coeff_eq_zero_sub_cancel_core (K := K) (g := g) (q := q)
    (N := N) (d := d) hzero

theorem coeff_mul_right_sub_core
    {g q : K⟦X⟧} {N d : ℕ}
    (hzero : PowerSeries.coeff K d (q * (1 + g)⁻¹ * (-g) ^ (N + 1)) = 0) :
    PowerSeries.coeff K d (q * (1 + g)⁻¹ - q * (1 + g)⁻¹ * (-g) ^ (N + 1)) =
      PowerSeries.coeff K d (q * (1 + g)⁻¹) := by
  have hmap :
      PowerSeries.coeff K d
          (q * (1 + g)⁻¹ - q * (1 + g)⁻¹ * (-g) ^ (N + 1)) =
        PowerSeries.coeff K d (q * (1 + g)⁻¹) -
          PowerSeries.coeff K d (q * (1 + g)⁻¹ * (-g) ^ (N + 1)) := by
    exact map_sub (PowerSeries.coeff K d) _ _
  exact Eq.trans hmap
    (coeff_mul_right_sub_core_step (K := K) (g := g) (q := q) (N := N) (d := d) hzero)

theorem coeff_mul_right_sub
    {g q : K⟦X⟧} {N d : ℕ}
    (hzero : PowerSeries.coeff K d (q * (1 + g)⁻¹ * (-g) ^ (N + 1)) = 0) :
    PowerSeries.coeff K d (q * (1 + g)⁻¹ - q * (1 + g)⁻¹ * (-g) ^ (N + 1)) =
      PowerSeries.coeff K d (q * (1 + g)⁻¹) := by
  exact coeff_mul_right_sub_core (K := K) (g := g) (q := q) (N := N) (d := d) hzero

theorem coeff_mul_right_sub_final_step_core
    {g q : K⟦X⟧} {N d : ℕ}
    (hzero : PowerSeries.coeff K d (q * (1 + g)⁻¹ * (-g) ^ (N + 1)) = 0) :
    PowerSeries.coeff K d
        (q * (1 + g)⁻¹ * (1 - (-g) ^ (N + 1))) =
      PowerSeries.coeff K d (q * (1 + g)⁻¹) := by
  exact coeff_mul_right_sub_coeff_eq (K := K) (g := g) (q := q) (N := N) (d := d) hzero

theorem coeff_mul_right_sub_aux_core
    {g q : K⟦X⟧} {N d : ℕ}
    (hzero : PowerSeries.coeff K d (q * (1 + g)⁻¹ * (-g) ^ (N + 1)) = 0) :
    PowerSeries.coeff K d (q * (1 + g)⁻¹ - q * (1 + g)⁻¹ * (-g) ^ (N + 1)) =
      PowerSeries.coeff K d (q * (1 + g)⁻¹) := by
  exact coeff_mul_right_sub_core (K := K) (g := g) (q := q) (N := N) (d := d) hzero

theorem coeff_mul_right_sub' {g q : K⟦X⟧} {N d : ℕ}
    (hzero : PowerSeries.coeff K d (q * (1 + g)⁻¹ * (-g) ^ (N + 1)) = 0) :
    PowerSeries.coeff K d (q * (1 + g)⁻¹ - q * (1 + g)⁻¹ * (-g) ^ (N + 1)) =
      PowerSeries.coeff K d (q * (1 + g)⁻¹) := by
  exact coeff_mul_right_sub_core (K := K) (g := g) (q := q) (N := N) (d := d) hzero

theorem coeff_mul_finiteGeomInverse_eq_coeff_inv_const_core
    {g : K⟦X⟧} (hg : PowerSeries.constantCoeff K g = 0) :
    PowerSeries.constantCoeff K (1 + g) ≠ 0 := by
  intro h
  have hsum : PowerSeries.constantCoeff K (1 + g) = 1 := by
    calc
      PowerSeries.constantCoeff K (1 + g) =
          PowerSeries.constantCoeff K 1 + PowerSeries.constantCoeff K g := by
            exact map_add (PowerSeries.constantCoeff K) 1 g
      _ = 1 + 0 := by
            exact congrArg (fun t : K => 1 + t) hg
      _ = 1 := by
            exact add_zero 1
  have h01 : (1 : K) = 0 := by
    calc
      (1 : K) = PowerSeries.constantCoeff K (1 + g) := by
        exact hsum.symm
      _ = 0 := h
  exact one_ne_zero h01

theorem coeff_mul_finiteGeomInverse_eq_coeff_inv_const
    {g : K⟦X⟧} (hg : PowerSeries.constantCoeff K g = 0) :
    PowerSeries.constantCoeff K (1 + g) ≠ 0 := by
  exact coeff_mul_finiteGeomInverse_eq_coeff_inv_const_core (K := K) (g := g) hg

theorem coeff_mul_finiteGeomInverse_eq_coeff_inv_left_core
    {g q : K⟦X⟧} {N : ℕ}
    (_ : PowerSeries.constantCoeff K g = 0) :
    q * finiteGeomInverse (K := K) g N * (1 + g) =
      q * (1 - (-g) ^ (N + 1)) := by
  exact Eq.trans
    (Eq.trans
      (mul_assoc q (finiteGeomInverse (K := K) g N) (1 + g))
      (congrArg (fun t : K⟦X⟧ => q * t)
        (mul_comm (finiteGeomInverse (K := K) g N) (1 + g))))
    (congrArg (fun t : K⟦X⟧ => q * t) (one_add_mul_finiteGeomInverse (K := K) g N))

theorem coeff_mul_finiteGeomInverse_eq_coeff_inv_left
    {g q : K⟦X⟧} {N : ℕ}
    (hg : PowerSeries.constantCoeff K g = 0) :
    q * finiteGeomInverse (K := K) g N * (1 + g) =
      q * (1 - (-g) ^ (N + 1)) := by
  exact coeff_mul_finiteGeomInverse_eq_coeff_inv_left_core (K := K) (g := g) (q := q)
    (N := N) hg

theorem coeff_mul_finiteGeomInverse_eq_coeff_inv_cancel_mul_core
    {g q : K⟦X⟧} {N : ℕ}
    (hconst : PowerSeries.constantCoeff K (1 + g) ≠ 0) :
    q * finiteGeomInverse (K := K) g N =
      (q * finiteGeomInverse (K := K) g N * (1 + g)) * (1 + g)⁻¹ := by
  calc
    q * finiteGeomInverse (K := K) g N =
        (q * finiteGeomInverse (K := K) g N) * 1 := by
          exact Eq.symm (mul_one (q * finiteGeomInverse (K := K) g N))
    _ = (q * finiteGeomInverse (K := K) g N) * ((1 + g) * (1 + g)⁻¹) := by
          exact congrArg (fun t : K⟦X⟧ => (q * finiteGeomInverse (K := K) g N) * t)
            (Eq.symm (PowerSeries.mul_inv_cancel (1 + g) hconst))
    _ = (q * finiteGeomInverse (K := K) g N * (1 + g)) * (1 + g)⁻¹ := by
          exact Eq.symm (mul_assoc (q * finiteGeomInverse (K := K) g N) (1 + g) (1 + g)⁻¹)

theorem coeff_mul_finiteGeomInverse_eq_coeff_inv_cancel_mul
    {g q : K⟦X⟧} {N : ℕ}
    (hconst : PowerSeries.constantCoeff K (1 + g) ≠ 0) :
    q * finiteGeomInverse (K := K) g N =
      (q * finiteGeomInverse (K := K) g N * (1 + g)) * (1 + g)⁻¹ := by
  exact coeff_mul_finiteGeomInverse_eq_coeff_inv_cancel_mul_core (K := K) (g := g) (q := q)
    (N := N) hconst

theorem coeff_mul_finiteGeomInverse_eq_coeff_inv_cancel_hleft_core
    {g q : K⟦X⟧} {N : ℕ}
    (hleft : q * finiteGeomInverse (K := K) g N * (1 + g) =
        q * (1 - (-g) ^ (N + 1))) :
    (q * finiteGeomInverse (K := K) g N * (1 + g)) * (1 + g)⁻¹ =
      q * (1 - (-g) ^ (N + 1)) * (1 + g)⁻¹ := by
  exact congrArg (fun t : K⟦X⟧ => t * (1 + g)⁻¹) hleft

theorem coeff_mul_finiteGeomInverse_eq_coeff_inv_cancel_hleft
    {g q : K⟦X⟧} {N : ℕ}
    (hleft : q * finiteGeomInverse (K := K) g N * (1 + g) =
        q * (1 - (-g) ^ (N + 1))) :
    (q * finiteGeomInverse (K := K) g N * (1 + g)) * (1 + g)⁻¹ =
      q * (1 - (-g) ^ (N + 1)) * (1 + g)⁻¹ := by
  exact coeff_mul_finiteGeomInverse_eq_coeff_inv_cancel_hleft_core (K := K) (g := g)
    (q := q) (N := N) hleft

theorem coeff_mul_finiteGeomInverse_eq_coeff_inv_swap_core
    {g q : K⟦X⟧} {N : ℕ} :
    q * (1 - (-g) ^ (N + 1)) * (1 + g)⁻¹ =
      q * (1 + g)⁻¹ * (1 - (-g) ^ (N + 1)) := by
  calc
    q * (1 - (-g) ^ (N + 1)) * (1 + g)⁻¹ =
        q * ((1 - (-g) ^ (N + 1)) * (1 + g)⁻¹) := by
          exact mul_assoc q (1 - (-g) ^ (N + 1)) (1 + g)⁻¹
    _ = q * ((1 + g)⁻¹ * (1 - (-g) ^ (N + 1))) := by
          exact congrArg (fun t : K⟦X⟧ => q * t)
            (mul_comm (1 - (-g) ^ (N + 1)) (1 + g)⁻¹)
    _ = q * (1 + g)⁻¹ * (1 - (-g) ^ (N + 1)) := by
          exact Eq.symm (mul_assoc q (1 + g)⁻¹ (1 - (-g) ^ (N + 1)))

theorem coeff_mul_finiteGeomInverse_eq_coeff_inv_swap
    {g q : K⟦X⟧} {N : ℕ} :
    q * (1 - (-g) ^ (N + 1)) * (1 + g)⁻¹ =
      q * (1 + g)⁻¹ * (1 - (-g) ^ (N + 1)) := by
  exact coeff_mul_finiteGeomInverse_eq_coeff_inv_swap_core (K := K) (g := g) (q := q)
    (N := N)

theorem coeff_mul_finiteGeomInverse_eq_coeff_mul_inv_cancel_core
    {g q : K⟦X⟧} {N : ℕ}
    (hg : PowerSeries.constantCoeff K g = 0) :
    q * finiteGeomInverse (K := K) g N =
      q * (1 + g)⁻¹ * (1 - (-g) ^ (N + 1)) := by
  have hconst :
      PowerSeries.constantCoeff K (1 + g) ≠ 0 := by
    exact coeff_mul_finiteGeomInverse_eq_coeff_inv_const (K := K) (g := g) hg
  have hleft :
      q * finiteGeomInverse (K := K) g N * (1 + g) =
        q * (1 - (-g) ^ (N + 1)) := by
    exact coeff_mul_finiteGeomInverse_eq_coeff_inv_left (K := K) (g := g) (q := q)
      (N := N) hg
  have hcancel1 :
      q * finiteGeomInverse (K := K) g N =
        (q * finiteGeomInverse (K := K) g N * (1 + g)) * (1 + g)⁻¹ := by
    exact coeff_mul_finiteGeomInverse_eq_coeff_inv_cancel_mul (K := K) (g := g) (q := q)
      (N := N) hconst
  have hcancel2 :
      (q * finiteGeomInverse (K := K) g N * (1 + g)) * (1 + g)⁻¹ =
        q * (1 - (-g) ^ (N + 1)) * (1 + g)⁻¹ := by
    exact coeff_mul_finiteGeomInverse_eq_coeff_inv_cancel_hleft
      (K := K) (g := g) (q := q) (N := N) hleft
  have hswap :
      q * (1 - (-g) ^ (N + 1)) * (1 + g)⁻¹ =
        q * (1 + g)⁻¹ * (1 - (-g) ^ (N + 1)) := by
    exact coeff_mul_finiteGeomInverse_eq_coeff_inv_swap
      (K := K) (g := g) (q := q) (N := N)
  exact Eq.trans (Eq.trans hcancel1 hcancel2) hswap


end

end TraceExpansion
end Boundary
