import Boundary.LFunctions.EulerFactor
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.RingTheory.PowerSeries.Derivative

/-!
# Formal logarithmic trace expansions

This file starts the logarithmic side of the Boundary L-functions stack with
the coefficient expansion of the formal logarithm for a single normalized
scalar Euler factor.
-/

open scoped BigOperators PowerSeries

namespace Boundary
namespace TraceExpansion

noncomputable section

variable {K : Type*} [Field K]

/-- The coefficientwise formal logarithm around `1`.

For coefficient `n`, the sum is finite because only powers up to `n` can
contribute to the `X^n` coefficient when the input is normalized. -/
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
  simp [formalLog]

theorem coeff_formalLog_of_ne_zero (f : K⟦X⟧) {n : ℕ} (hn : n ≠ 0) :
    PowerSeries.coeff K n (formalLog f) =
      ∑ k in Finset.range (n + 1),
        ((-1 : K) ^ (k + 1) / (k : K)) *
          PowerSeries.coeff K n ((f - 1) ^ k) := by
  simp [formalLog, hn]

/-- Coefficients of the derivative of the project-local `formalLog`. -/
theorem coeff_derivative_formalLog (f : K⟦X⟧) (n : ℕ) :
    PowerSeries.coeff K n (PowerSeries.derivative K (formalLog f)) =
      PowerSeries.coeff K (n + 1) (formalLog f) * (n + 1 : K) := by
  rw [PowerSeries.coeff_derivative]

/-- A finite geometric inverse for `1 + g`, through degree `N`. -/
def finiteGeomInverse (g : K⟦X⟧) (N : ℕ) : K⟦X⟧ :=
  ∑ r in Finset.range (N + 1), (-g) ^ r

/-- The finite geometric inverse has the expected exact product error. -/
theorem one_add_mul_finiteGeomInverse
    (g : K⟦X⟧) (N : ℕ) :
    (1 + g) * finiteGeomInverse (K := K) g N =
      1 - (-g) ^ (N + 1) := by
  rw [finiteGeomInverse]
  induction N with
  | zero =>
      simp
  | succ N ih =>
      rw [Finset.sum_range_succ, mul_add, ih]
      ring_nf

/-- If `g` has zero constant coefficient, then any multiple of `g^(N+1)` has
zero coefficients through degree `N`. -/
theorem coeff_mul_pow_succ_eq_zero_of_constantCoeff_eq_zero
    {g q : K⟦X⟧} {N d : ℕ}
    (hg : PowerSeries.constantCoeff K g = 0) (hd : d < N + 1) :
    PowerSeries.coeff K d (q * g ^ (N + 1)) = 0 := by
  obtain ⟨h, hh⟩ := (PowerSeries.X_dvd_iff (R := K) (φ := g)).mpr hg
  rw [hh]
  rw [mul_pow]
  change PowerSeries.coeff K d (q * (PowerSeries.X ^ (N + 1) * h ^ (N + 1))) = 0
  rw [show q * (PowerSeries.X ^ (N + 1) * h ^ (N + 1)) =
      (q * h ^ (N + 1)) * PowerSeries.X ^ (N + 1) by
    calc
      q * (PowerSeries.X ^ (N + 1) * h ^ (N + 1)) =
          q * (h ^ (N + 1) * PowerSeries.X ^ (N + 1)) := by
            rw [mul_comm (PowerSeries.X ^ (N + 1)) (h ^ (N + 1))]
      _ = (q * h ^ (N + 1)) * PowerSeries.X ^ (N + 1) := by
            rw [mul_assoc]]
  rw [PowerSeries.coeff_mul_X_pow']
  simp [hd.not_le]

/-- Through degree `N`, the finite geometric inverse agrees with the true
inverse of a normalized series `1 + g`. -/
theorem coeff_mul_finiteGeomInverse_eq_coeff_mul_inv
    {g q : K⟦X⟧} {N d : ℕ}
    (hg : PowerSeries.constantCoeff K g = 0) (hd : d < N + 1) :
    PowerSeries.coeff K d (q * finiteGeomInverse (K := K) g N) =
      PowerSeries.coeff K d (q * (1 + g)⁻¹) := by
  have hconst : PowerSeries.constantCoeff K (1 + g) ≠ 0 := by
    simp [hg]
  have hleft :
      q * finiteGeomInverse (K := K) g N * (1 + g) =
        q * (1 - (-g) ^ (N + 1)) := by
    calc
      q * finiteGeomInverse (K := K) g N * (1 + g) =
          q * (finiteGeomInverse (K := K) g N * (1 + g)) := by
            rw [mul_assoc]
      _ = q * ((1 + g) * finiteGeomInverse (K := K) g N) := by
            rw [mul_comm (finiteGeomInverse (K := K) g N) (1 + g)]
      _ = q * (1 - (-g) ^ (N + 1)) := by
          rw [one_add_mul_finiteGeomInverse]
  have hinv :
      q * (1 + g)⁻¹ * (1 + g) = q := by
    rw [mul_assoc, PowerSeries.inv_mul_cancel (1 + g) hconst, mul_one]
  -- Multiplication by `1+g` is injective; use the inverse to cancel after
  -- converting both sides back through degree `d`.
  have hcancel :
      q * finiteGeomInverse (K := K) g N =
        q * (1 + g)⁻¹ * (1 - (-g) ^ (N + 1)) := by
    calc
      q * finiteGeomInverse (K := K) g N =
          (q * finiteGeomInverse (K := K) g N * (1 + g)) * (1 + g)⁻¹ := by
            rw [mul_assoc, PowerSeries.mul_inv_cancel (1 + g) hconst, mul_one]
      _ = q * (1 - (-g) ^ (N + 1)) * (1 + g)⁻¹ := by rw [hleft]
      _ = q * (1 + g)⁻¹ * (1 - (-g) ^ (N + 1)) := by
            calc
              q * (1 - (-g) ^ (N + 1)) * (1 + g)⁻¹ =
                  q * ((1 - (-g) ^ (N + 1)) * (1 + g)⁻¹) := by
                    rw [mul_assoc]
              _ = q * ((1 + g)⁻¹ * (1 - (-g) ^ (N + 1))) := by
                    rw [mul_comm (1 - (-g) ^ (N + 1)) (1 + g)⁻¹]
              _ = q * (1 + g)⁻¹ * (1 - (-g) ^ (N + 1)) := by
                    rw [← mul_assoc]
  rw [hcancel]
  rw [mul_sub, map_sub]
  have hzero :
      PowerSeries.coeff K d (q * (1 + g)⁻¹ * (-g) ^ (N + 1)) = 0 := by
    have hgneg : PowerSeries.constantCoeff K (-g) = 0 := by
      simp [hg]
    simpa [mul_assoc] using
      coeff_mul_pow_succ_eq_zero_of_constantCoeff_eq_zero
        (K := K) (g := -g) (q := q * (1 + g)⁻¹) hgneg hd
  simp [hzero]

/-- Scalar cancellation used when differentiating the `k`th logarithm term.
This is the characteristic-zero cancellation of `k + 1` against its inverse,
embedded into the power-series coefficient ring. -/
theorem natCast_add_one_mul_inv_powerSeries
    [CharZero K] (r : ℕ) :
    ((r : K⟦X⟧) + 1) *
        (algebraMap K K⟦X⟧) (1 + (r : K))⁻¹ = 1 := by
  have hr : (1 + (r : K)) ≠ 0 := by
    simpa [add_comm] using Nat.cast_add_one_ne_zero (R := K) r
  rw [show (r : K⟦X⟧) + 1 = (algebraMap K K⟦X⟧) (1 + (r : K)) by
    simp [add_comm]]
  rw [← map_mul]
  rw [mul_inv_cancel₀ hr]
  rw [map_one]

/-- Derivative of a single nonzero formal-log term. This is the local
characteristic-zero cancellation behind `d log(1+g) = g'/(1+g)`. -/
theorem derivative_formalLog_term
    [CharZero K] (g : K⟦X⟧) (r : ℕ) :
    ((-1 : K) ^ (r + 1 + 1) / ((r + 1 : ℕ) : K)) •
        PowerSeries.derivative K (g ^ (r + 1)) =
      (-g) ^ r * PowerSeries.derivative K g := by
  rw [Derivation.leibniz_pow]
  simp only [add_tsub_cancel_right, nsmul_eq_mul]
  rw [div_eq_mul_inv]
  simp only [Algebra.smul_def, map_mul, map_inv₀, map_pow, map_neg, map_one]
  rw [show ((r + 1 : ℕ) : K⟦X⟧) = (r : K⟦X⟧) + 1 by simp]
  calc
    (((-1 : K⟦X⟧) ^ (r + 1 + 1) * (algebraMap K K⟦X⟧) ((r + 1 : ℕ) : K)⁻¹) *
        (((r : K⟦X⟧) + 1) *
          ((algebraMap K⟦X⟧ K⟦X⟧) g ^ r * PowerSeries.derivative K g))) =
      (((r : K⟦X⟧) + 1) * (algebraMap K K⟦X⟧) (1 + (r : K))⁻¹) *
        (((-1 : K⟦X⟧) ^ (r + 1 + 1)) *
          ((algebraMap K⟦X⟧ K⟦X⟧) g ^ r) * PowerSeries.derivative K g) := by
        rw [show (((r + 1 : ℕ) : K)) = 1 + (r : K) by simp [add_comm]]
        ac_rfl
    _ = ((-1 : K⟦X⟧) ^ (r + 1 + 1)) * g ^ r * PowerSeries.derivative K g := by
        rw [natCast_add_one_mul_inv_powerSeries (K := K) r, one_mul]
        simp
    _ = (-g) ^ r * PowerSeries.derivative K g := by
        have hpow : ((-1 : K⟦X⟧) ^ (r + 1 + 1)) = (-1 : K⟦X⟧) ^ r := by
          rw [show r + 1 + 1 = r + 2 by rw [add_assoc]]
          rw [pow_add]
          rw [show ((-1 : K⟦X⟧) ^ 2) = 1 by
            rw [pow_two]
            rw [neg_mul_neg]
            rw [one_mul]]
          rw [mul_one]
        rw [hpow]
        rw [show (-g) ^ r = (-1 : K⟦X⟧) ^ r * g ^ r by
          rw [neg_eq_neg_one_mul, mul_pow]]

/-- Coefficientwise derivative of the project-local logarithm, expressed using
the finite geometric inverse through the coefficient being read. -/
theorem coeff_derivative_formalLog_eq_coeff_mul_finiteGeomInverse
    [CharZero K] (f : K⟦X⟧) (n : ℕ) :
    PowerSeries.coeff K n (PowerSeries.derivative K (formalLog f)) =
      PowerSeries.coeff K n
        (PowerSeries.derivative K f * finiteGeomInverse (K := K) (f - 1) n) := by
  let g : K⟦X⟧ := f - 1
  have hgderiv : PowerSeries.derivative K g = PowerSeries.derivative K f := by
    simp [g]
  rw [coeff_derivative_formalLog]
  rw [coeff_formalLog_of_ne_zero _ (Nat.succ_ne_zero n)]
  rw [Finset.sum_mul]
  have hterm :
      ∀ k ∈ Finset.range (n + 2),
        ((-1 : K) ^ (k + 1) / (k : K)) *
            PowerSeries.coeff K (n + 1) ((f - 1) ^ k) * (n + 1 : K) =
          PowerSeries.coeff K n
            (((-1 : K) ^ (k + 1) / (k : K)) •
              PowerSeries.derivative K ((f - 1) ^ k)) := by
    intro k hk
    rw [map_smul, PowerSeries.coeff_derivative]
    simp [smul_eq_mul]
    rw [mul_assoc]
  rw [show
      (∑ k in Finset.range (n + 2),
        ((-1 : K) ^ (k + 1) / (k : K)) *
          PowerSeries.coeff K (n + 1) ((f - 1) ^ k) * (n + 1 : K)) =
      ∑ k in Finset.range (n + 2),
        PowerSeries.coeff K n
          (((-1 : K) ^ (k + 1) / (k : K)) •
            PowerSeries.derivative K ((f - 1) ^ k)) by
        apply Finset.sum_congr rfl
        intro k hk
        exact hterm k hk]
  rw [← map_sum]
  have hderive :
      (∑ k in Finset.range (n + 2),
          ((-1 : K) ^ (k + 1) / (k : K)) •
            PowerSeries.derivative K ((f - 1) ^ k)) =
        PowerSeries.derivative K f * finiteGeomInverse (K := K) (f - 1) n := by
    rw [finiteGeomInverse]
    rw [Finset.sum_range_succ']
    simp only [pow_zero, map_zero, smul_zero, zero_add]
    rw [Finset.mul_sum]
    rw [show (((-1 : K) ^ 1 / ((0 : ℕ) : K)) • PowerSeries.derivative K (1 : K⟦X⟧)) = 0 by
      simp]
    rw [add_zero]
    apply Finset.sum_congr rfl
    intro r hr
    calc
      ((-1 : K) ^ (r + 1 + 1) / ((r + 1 : ℕ) : K)) •
          PowerSeries.derivative K ((f - 1) ^ (r + 1)) =
          (-(f - 1)) ^ r * PowerSeries.derivative K (f - 1) := by
            exact derivative_formalLog_term (K := K) (g := f - 1) r
      _ = PowerSeries.derivative K f * (-(f - 1)) ^ r := by
            rw [show PowerSeries.derivative K (f - 1) = PowerSeries.derivative K f by simp]
            rw [mul_comm]
  rw [hderive]

/-- Coefficientwise logarithmic derivative identity for normalized power
series. The characteristic-zero hypothesis is necessary because `formalLog`
uses division by natural numbers. -/
theorem coeff_derivative_formalLog_eq_coeff_derivative_mul_inv
    [CharZero K] (f : K⟦X⟧)
    (h0 : PowerSeries.coeff K 0 f = 1) (n : ℕ) :
    PowerSeries.coeff K n (PowerSeries.derivative K (formalLog f)) =
      PowerSeries.coeff K n (PowerSeries.derivative K f * f⁻¹) := by
  rw [coeff_derivative_formalLog_eq_coeff_mul_finiteGeomInverse (K := K) f n]
  have hg : PowerSeries.constantCoeff K (f - 1) = 0 := by
    have hf0 : PowerSeries.constantCoeff K f = 1 := by
      simpa [PowerSeries.coeff_zero_eq_constantCoeff_apply] using h0
    simp [hf0]
  have hfinite :=
    coeff_mul_finiteGeomInverse_eq_coeff_mul_inv
      (K := K) (g := f - 1) (q := PowerSeries.derivative K f)
      (N := n) (d := n) hg (Nat.lt_succ_self n)
  simpa [sub_eq_add_neg, add_assoc] using hfinite

/-- Logarithmic derivative identity for normalized power series. -/
theorem derivative_formalLog_eq_derivative_mul_inv
    [CharZero K] (f : K⟦X⟧)
    (h0 : PowerSeries.coeff K 0 f = 1) :
    PowerSeries.derivative K (formalLog f) =
      PowerSeries.derivative K f * f⁻¹ := by
  apply PowerSeries.ext
  intro n
  exact coeff_derivative_formalLog_eq_coeff_derivative_mul_inv
    (K := K) f h0 n

@[simp]
theorem coeff_C_mul_X_pow_eq_self {x : K} {n : ℕ} :
    PowerSeries.coeff K n (PowerSeries.C K x * PowerSeries.X ^ n : K⟦X⟧) = x := by
  simp [PowerSeries.coeff_C_mul_X_pow]

theorem coeff_C_mul_X_pow_eq_zero_of_ne {x : K} {m n : ℕ} (h : m ≠ n) :
    PowerSeries.coeff K m (PowerSeries.C K x * PowerSeries.X ^ n : K⟦X⟧) = 0 := by
  rw [PowerSeries.coeff_C_mul_X_pow, if_neg h]

theorem one_sub_scalar_factor_sub_one (a : K) :
    (1 - PowerSeries.C K a * PowerSeries.X : K⟦X⟧) - 1 =
      -(PowerSeries.C K a * PowerSeries.X) := by
  rw [sub_eq_add_neg]
  rw [sub_eq_add_neg]
  rw [add_assoc]
  rw [add_right_neg]
  rw [zero_add]

theorem neg_scalar_X_pow (a : K) (k : ℕ) :
    (-(PowerSeries.C K a * PowerSeries.X) : K⟦X⟧) ^ k =
      PowerSeries.C K ((-a) ^ k) * PowerSeries.X ^ k := by
  induction k with
  | zero =>
      simp
  | succ k ih =>
      rw [pow_succ, ih]
      simp only [map_pow, map_neg, map_mul]
      calc
        (PowerSeries.C K ((-a) ^ k) * PowerSeries.X ^ k) *
            -(PowerSeries.C K a * PowerSeries.X) =
            -(PowerSeries.C K ((-a) ^ k) * PowerSeries.C K a *
              (PowerSeries.X ^ k * PowerSeries.X)) := by
              rw [mul_neg]
              rw [mul_assoc]
              rw [show PowerSeries.X ^ k * (PowerSeries.C K a * PowerSeries.X) =
                  PowerSeries.C K a * (PowerSeries.X ^ k * PowerSeries.X) by
                calc
                  PowerSeries.X ^ k * (PowerSeries.C K a * PowerSeries.X) =
                      (PowerSeries.X ^ k * PowerSeries.C K a) * PowerSeries.X := by
                        rw [mul_assoc]
                  _ = (PowerSeries.C K a * PowerSeries.X ^ k) * PowerSeries.X := by
                        rw [mul_comm (PowerSeries.X ^ k) (PowerSeries.C K a)]
                  _ = PowerSeries.C K a * (PowerSeries.X ^ k * PowerSeries.X) := by
                        rw [mul_assoc]]
              rw [← mul_assoc]
        _ = PowerSeries.C K ((-a) ^ (k + 1)) * PowerSeries.X ^ (k + 1) := by
              rw [pow_succ]
              rw [PowerSeries.C_mul]
              rw [← neg_mul]
              rw [show -((-a) ^ k * a) = (-a) ^ k * -a by
                rw [mul_neg]]
              rw [← PowerSeries.C_mul]
              rw [pow_succ]

theorem coeff_neg_scalar_X_pow (a : K) (m n : ℕ) :
    PowerSeries.coeff K n ((-(PowerSeries.C K a * PowerSeries.X) : K⟦X⟧) ^ m) =
      if n = m then (-a) ^ m else 0 := by
  rw [neg_scalar_X_pow]
  exact PowerSeries.coeff_C_mul_X_pow ((-a) ^ m) m n

/-- The logarithm of a normalized scalar Euler factor has the expected
coefficient expansion. -/
theorem coeff_formalLog_one_sub_scalar_mul_X
    (a : K) {n : ℕ} (hn : n ≠ 0) :
    PowerSeries.coeff K n
        (formalLog (1 - PowerSeries.C K a * PowerSeries.X : K⟦X⟧)) =
      -a ^ n / (n : K) := by
  rw [coeff_formalLog_of_ne_zero _ hn]
  rw [one_sub_scalar_factor_sub_one]
  refine (Finset.sum_eq_single_of_mem n ?mem ?off).trans ?_
  · exact Finset.mem_range.mpr (Nat.lt_succ_self n)
  · intro k hk hkn
    rw [coeff_neg_scalar_X_pow]
    simp [hkn.symm]
  · simp only [coeff_neg_scalar_X_pow, if_pos rfl]
    have hnegpow : (-a) ^ n = (-1 : K) ^ n * a ^ n := by
      rw [neg_eq_neg_one_mul, mul_pow]
    rw [hnegpow]
    field_simp [hn]
    ring_nf
    have hsign : (-1 : K) ^ (n * 2) = 1 := by
      rw [mul_comm, pow_mul]
      simp
    rw [hsign]
    ring

/-- Polynomial-to-power-series form of the scalar logarithmic Euler factor
expansion. -/
theorem coeff_formalLog_coe_one_sub_C_mul_X
    (a : K) {n : ℕ} (hn : n ≠ 0) :
    PowerSeries.coeff K n
        (formalLog ((1 - Polynomial.C a * Polynomial.X : Polynomial K) : K⟦X⟧)) =
      -a ^ n / (n : K) := by
  simpa [Polynomial.coe_one, Polynomial.coe_sub, Polynomial.coe_mul,
    Polynomial.coe_C, Polynomial.coe_X] using
    coeff_formalLog_one_sub_scalar_mul_X (K := K) a hn

section MatrixSeries

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Product rule for a finite product of polynomials, in `Finset` form. -/
theorem derivative_finset_prod {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (f : ι → Polynomial K) :
    Polynomial.derivative (∏ i in s, f i) =
      ∑ i in s, (∏ j in s.erase i, f j) * Polynomial.derivative (f i) := by
  classical
  refine Finset.induction_on s ?empty ?insert
  · simp
  · intro a s ha ih
    rw [Finset.prod_insert ha, Polynomial.derivative_mul, ih, Finset.sum_insert ha]
    simp only [Finset.erase_insert ha, Finset.prod_eq_one, mul_one, Finset.mul_sum]
    apply congrArg₂ HAdd.hAdd
    · ring
    · apply Finset.sum_congr rfl
      intro i hi
      have hai : a ≠ i := by
        intro h
        exact ha (h.symm ▸ hi)
      rw [Finset.erase_insert_of_ne hai]
      rw [Finset.prod_insert]
      · ring
      · simp [ha]

/-- Expanding a determinant after replacing one row, expressed using the
adjugate of the original matrix. -/
theorem det_updateRow_eq_sum_mul_adjugate
    (A : Matrix n n (Polynomial K)) (i : n) (v : n → Polynomial K) :
    (A.updateRow i v).det = ∑ j : n, v j * A.adjugate j i := by
  rw [← Matrix.cramer_transpose_apply (A := A) (b := v) (i := i)]
  rw [Matrix.cramer_eq_adjugate_mulVec]
  rw [← Matrix.adjugate_transpose A]
  simp [Matrix.mulVec, Matrix.dotProduct, mul_comm]

/-- Expanding a determinant after replacing one column, expressed using the
adjugate of the original matrix. -/
theorem det_updateColumn_eq_sum_mul_adjugate
    (A : Matrix n n (Polynomial K)) (j : n) (v : n → Polynomial K) :
    (A.updateColumn j v).det = ∑ i : n, v i * A.adjugate j i := by
  rw [← Matrix.cramer_apply (A := A) (b := v) (i := j)]
  rw [Matrix.cramer_eq_adjugate_mulVec]
  simp [Matrix.mulVec, Matrix.dotProduct, mul_comm]

/-- The derivative of the determinant of `1 - XM`, as a sum over differentiated
columns. -/
theorem derivative_charpolyRev_eq_sum_updateColumn
    (M : Matrix n n K) :
    Polynomial.derivative M.charpolyRev =
      ∑ j : n,
        ((1 - (Polynomial.X : Polynomial K) • M.map Polynomial.C).updateColumn j
          (fun i => -Polynomial.C (M i j))).det := by
  classical
  have hderiv_if :
      ∀ (σ : Equiv.Perm n) (i : n),
        Polynomial.derivative ((if σ i = i then 1 else 0 : Polynomial K)) = 0 := by
    intro σ i
    split <;> simp
  rw [Matrix.charpolyRev, Matrix.det_apply']
  simp [Polynomial.derivative_sum, derivative_finset_prod, Matrix.updateColumn,
    Matrix.det_apply', Matrix.one_apply, Matrix.map_apply, Pi.smul_apply, Finset.mul_sum,
    Polynomial.derivative_C, Polynomial.derivative_one, Polynomial.derivative_zero,
    Polynomial.derivative_natCast, hderiv_if]
  rw [Finset.sum_comm]
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro y hy
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro σ hσ
  have hprod :
      (∏ x_2 : n,
          Function.update
            (((1 : Matrix n n (Polynomial K)) -
              (Polynomial.X : Polynomial K) • M.map Polynomial.C) (σ x_2)) y
            (-Polynomial.C (M (σ x_2) y)) x_2) =
        -((∏ x_1 in Finset.univ.erase y,
            ((if σ x_1 = x_1 then 1 else 0) -
              Polynomial.C (M (σ x_1) x_1) * Polynomial.X)) *
          Polynomial.C (M (σ y) y)) := by
    calc
      (∏ x_2 : n,
          Function.update
            (((1 : Matrix n n (Polynomial K)) -
              (Polynomial.X : Polynomial K) • M.map Polynomial.C) (σ x_2)) y
            (-Polynomial.C (M (σ x_2) y)) x_2) =
          (∏ x_2 in Finset.univ.erase y,
            Function.update
              (((1 : Matrix n n (Polynomial K)) -
                (Polynomial.X : Polynomial K) • M.map Polynomial.C) (σ x_2)) y
              (-Polynomial.C (M (σ x_2) y)) x_2) *
            Function.update
              (((1 : Matrix n n (Polynomial K)) -
                (Polynomial.X : Polynomial K) • M.map Polynomial.C) (σ y)) y
              (-Polynomial.C (M (σ y) y)) y := by
            rw [Finset.prod_erase_mul (s := Finset.univ)
              (f := fun x_2 =>
                Function.update
                  (((1 : Matrix n n (Polynomial K)) -
                    (Polynomial.X : Polynomial K) • M.map Polynomial.C) (σ x_2)) y
                  (-Polynomial.C (M (σ x_2) y)) x_2) (a := y) (Finset.mem_univ y)]
      _ = (∏ x_1 in Finset.univ.erase y,
            ((if σ x_1 = x_1 then 1 else 0) -
              Polynomial.C (M (σ x_1) x_1) * Polynomial.X)) *
            (-Polynomial.C (M (σ y) y)) := by
            congr 1
            · apply Finset.prod_congr rfl
              intro x hx
              have hxy : x ≠ y := by
                exact (Finset.mem_erase.mp hx).1
              simp [Function.update_noteq hxy, Matrix.one_apply, Matrix.map_apply, Pi.smul_apply]
            · rw [Function.update_same]
      _ = -((∏ x_1 in Finset.univ.erase y,
            ((if σ x_1 = x_1 then 1 else 0) -
              Polynomial.C (M (σ x_1) x_1) * Polynomial.X)) *
          Polynomial.C (M (σ y) y)) := by
            ring
  rw [hprod]
  ring

/-- Jacobi's formula for the special polynomial matrix `1 - XM`, expressed
with the adjugate. -/
theorem derivative_charpolyRev_eq_neg_trace_adjugate
    (M : Matrix n n K) :
    Polynomial.derivative M.charpolyRev =
      -(∑ i : n, ∑ j : n,
        Polynomial.C (M i j) *
          (1 - (Polynomial.X : Polynomial K) • M.map Polynomial.C).adjugate j i) := by
  classical
  rw [derivative_charpolyRev_eq_sum_updateColumn]
  simp [det_updateColumn_eq_sum_mul_adjugate]
  rw [Finset.sum_comm]

/-- The matrix geometric series with coefficient `M^k` in degree `k`. -/
def matrixGeometricSeries (M : Matrix n n K) : (Matrix n n K)⟦X⟧ :=
  PowerSeries.mk fun k => M ^ k

@[simp]
theorem coeff_matrixGeometricSeries (M : Matrix n n K) (k : ℕ) :
    PowerSeries.coeff (Matrix n n K) k (matrixGeometricSeries (K := K) M) = M ^ k := by
  simp [matrixGeometricSeries]

@[simp]
theorem coeff_C_mul_matrixGeometricSeries (M : Matrix n n K) (k : ℕ) :
    PowerSeries.coeff (Matrix n n K) k
        (PowerSeries.C (Matrix n n K) M * matrixGeometricSeries (K := K) M) =
      M ^ (k + 1) := by
  rw [PowerSeries.coeff_C_mul]
  simp [matrixGeometricSeries, pow_succ']

/-- The trace-resolvent series whose `k`th coefficient is `trace(M^(k+1))`. -/
def traceResolventSeries (M : Matrix n n K) : K⟦X⟧ :=
  PowerSeries.mk fun k => Matrix.trace (M ^ (k + 1))

@[simp]
theorem coeff_traceResolventSeries (M : Matrix n n K) (k : ℕ) :
    PowerSeries.coeff K k (traceResolventSeries (K := K) M) =
      Matrix.trace (M ^ (k + 1)) := by
  simp [traceResolventSeries]

@[simp]
theorem coeff_trace_C_mul_matrixGeometricSeries (M : Matrix n n K) (k : ℕ) :
    Matrix.trace
      (PowerSeries.coeff (Matrix n n K) k
        (PowerSeries.C (Matrix n n K) M * matrixGeometricSeries (K := K) M)) =
      Matrix.trace (M ^ (k + 1)) := by
  rw [coeff_C_mul_matrixGeometricSeries]

/-- The same geometric resolvent, expressed as a matrix whose entries are
scalar power series. This is the form used by adjugates over `K⟦X⟧`. -/
def matrixResolvent (M : Matrix n n K) : Matrix n n K⟦X⟧ :=
  fun i j => PowerSeries.mk fun k => (M ^ k) i j

@[simp]
theorem coeff_matrixResolvent (M : Matrix n n K) (i j : n) (k : ℕ) :
    PowerSeries.coeff K k (matrixResolvent (K := K) M i j) = (M ^ k) i j := by
  simp [matrixResolvent]

/-- The polynomial matrix `1 - XM`, mapped to scalar power series. -/
def oneSubXMatrix (M : Matrix n n K) : Matrix n n K⟦X⟧ :=
  1 - (PowerSeries.X : K⟦X⟧) • M.map (PowerSeries.C K)

omit [Fintype n] in
@[simp]
theorem oneSubXMatrix_apply (M : Matrix n n K) (i j : n) :
    oneSubXMatrix (K := K) M i j =
      (if i = j then 1 else 0) - PowerSeries.X * PowerSeries.C K (M i j) := by
  simp [oneSubXMatrix, Matrix.one_apply, Matrix.map_apply, Pi.smul_apply, smul_eq_mul]

/-- The entrywise geometric resolvent is a right inverse to `1 - XM`. -/
theorem matrixResolvent_mul_oneSubXMatrix (M : Matrix n n K) :
    matrixResolvent (K := K) M * oneSubXMatrix (K := K) M = 1 := by
  classical
  apply Matrix.ext
  intro i j
  apply PowerSeries.ext
  intro k
  cases k with
  | zero =>
      simp [matrixResolvent, oneSubXMatrix, Matrix.mul_apply, Matrix.one_apply,
        Matrix.map_apply, Pi.smul_apply, smul_eq_mul]
  | succ k =>
      rw [Matrix.mul_apply]
      simp only [Finset.sum_apply, oneSubXMatrix_apply]
      rw [map_sum]
      have hterm :
          ∀ r : n,
            PowerSeries.coeff K (k + 1)
              (matrixResolvent (K := K) M i r *
                ((if r = j then 1 else 0 : K⟦X⟧) -
                  PowerSeries.X * PowerSeries.C K (M r j))) =
              (if r = j then (M ^ (k + 1)) i r else 0) -
                (M ^ k) i r * M r j := by
        intro r
        rw [mul_sub, map_sub]
        have hconst :
            PowerSeries.coeff K (k + 1)
              (matrixResolvent (K := K) M i r * (if r = j then 1 else 0 : K⟦X⟧)) =
              (if r = j then (M ^ (k + 1)) i r else 0) := by
          by_cases hrj : r = j
          · simp [hrj, matrixResolvent]
          · simp [hrj, matrixResolvent]
        have hx :
            PowerSeries.coeff K (k + 1)
              (matrixResolvent (K := K) M i r * (PowerSeries.X * PowerSeries.C K (M r j))) =
              (M ^ k) i r * M r j := by
          calc
            PowerSeries.coeff K (k + 1)
                (matrixResolvent (K := K) M i r *
                  (PowerSeries.X * PowerSeries.C K (M r j))) =
                PowerSeries.coeff K (k + 1)
                  ((matrixResolvent (K := K) M i r * PowerSeries.X) *
                    PowerSeries.C K (M r j)) := by
                  rw [mul_assoc]
            _ = PowerSeries.coeff K k (matrixResolvent (K := K) M i r) * M r j := by
                rw [PowerSeries.coeff_mul_C]
                exact
                  (PowerSeries.coeff_mul_X_pow
                    (p := matrixResolvent (K := K) M i r) (n := 1) (d := k))
            _ = (M ^ k) i r * M r j := by simp
        rw [hconst, hx]
      simp_rw [hterm]
      have hsum_const :
          (∑ r : n, if r = j then (M ^ (k + 1)) i r else 0) =
            (M ^ (k + 1)) i j := by
        simp
      have hsum_mul :
          (∑ r : n, (M ^ k) i r * M r j) = (M ^ (k + 1)) i j := by
        rw [pow_succ]
        simp [Matrix.mul_apply]
      rw [Finset.sum_sub_distrib, hsum_const, hsum_mul]
      rw [sub_self]
      change 0 = PowerSeries.coeff K (k + 1) (if i = j then 1 else 0 : K⟦X⟧)
      by_cases hij : i = j <;> simp [hij, PowerSeries.coeff_one]

/-- The entrywise geometric resolvent is a left inverse to `1 - XM`. -/
theorem oneSubXMatrix_mul_matrixResolvent (M : Matrix n n K) :
    oneSubXMatrix (K := K) M * matrixResolvent (K := K) M = 1 := by
  classical
  apply Matrix.ext
  intro i j
  apply PowerSeries.ext
  intro k
  cases k with
  | zero =>
      simp [matrixResolvent, oneSubXMatrix, Matrix.mul_apply, Matrix.one_apply,
        Matrix.map_apply, Pi.smul_apply, smul_eq_mul]
  | succ k =>
      rw [Matrix.mul_apply]
      simp only [Finset.sum_apply, oneSubXMatrix_apply]
      rw [map_sum]
      have hterm :
          ∀ r : n,
            PowerSeries.coeff K (k + 1)
              (((if i = r then 1 else 0 : K⟦X⟧) -
                  PowerSeries.X * PowerSeries.C K (M i r)) *
                matrixResolvent (K := K) M r j) =
              (if i = r then (M ^ (k + 1)) r j else 0) -
                M i r * (M ^ k) r j := by
        intro r
        rw [sub_mul, map_sub]
        have hconst :
            PowerSeries.coeff K (k + 1)
              ((if i = r then 1 else 0 : K⟦X⟧) *
                matrixResolvent (K := K) M r j) =
              (if i = r then (M ^ (k + 1)) r j else 0) := by
          by_cases hir : i = r
          · simp [hir, matrixResolvent]
          · simp [hir, matrixResolvent]
        have hx :
            PowerSeries.coeff K (k + 1)
              ((PowerSeries.X * PowerSeries.C K (M i r)) *
                matrixResolvent (K := K) M r j) =
              M i r * (M ^ k) r j := by
          calc
            PowerSeries.coeff K (k + 1)
                ((PowerSeries.X * PowerSeries.C K (M i r)) *
                  matrixResolvent (K := K) M r j) =
                PowerSeries.coeff K (k + 1)
                  (PowerSeries.C K (M i r) *
                    (PowerSeries.X * matrixResolvent (K := K) M r j)) := by
                  calc
                    (PowerSeries.X * PowerSeries.C K (M i r)) *
                        matrixResolvent (K := K) M r j =
                        PowerSeries.X *
                          (PowerSeries.C K (M i r) *
                            matrixResolvent (K := K) M r j) := by
                          rw [mul_assoc]
                    _ = PowerSeries.X *
                          (matrixResolvent (K := K) M r j *
                            PowerSeries.C K (M i r)) := by
                          rw [mul_comm (PowerSeries.C K (M i r))
                            (matrixResolvent (K := K) M r j)]
                    _ = (PowerSeries.X * matrixResolvent (K := K) M r j) *
                          PowerSeries.C K (M i r) := by
                          rw [mul_assoc]
                    _ = PowerSeries.C K (M i r) *
                          (PowerSeries.X * matrixResolvent (K := K) M r j) := by
                          rw [mul_comm]
            _ = M i r *
                  PowerSeries.coeff K (k + 1)
                    (PowerSeries.X * matrixResolvent (K := K) M r j) := by
                rw [PowerSeries.coeff_C_mul]
            _ = M i r * PowerSeries.coeff K k (matrixResolvent (K := K) M r j) := by
                rw [show (PowerSeries.X : K⟦X⟧) = PowerSeries.X ^ 1 by simp]
                rw [PowerSeries.coeff_X_pow_mul
                  (p := matrixResolvent (K := K) M r j) (n := 1) (d := k)]
            _ = M i r * (M ^ k) r j := by simp
        rw [hconst, hx]
      simp_rw [hterm]
      have hsum_const :
          (∑ r : n, if i = r then (M ^ (k + 1)) r j else 0) =
            (M ^ (k + 1)) i j := by
        simp
      have hsum_mul :
          (∑ r : n, M i r * (M ^ k) r j) = (M ^ (k + 1)) i j := by
        rw [pow_succ']
        simp [Matrix.mul_apply]
      rw [Finset.sum_sub_distrib, hsum_const, hsum_mul]
      rw [sub_self]
      change 0 = PowerSeries.coeff K (k + 1) (if i = j then 1 else 0 : K⟦X⟧)
      by_cases hij : i = j <;> simp [hij, PowerSeries.coeff_one]

/-- Mapping the polynomial matrix `1 - XM` into power series gives
`oneSubXMatrix`. -/
theorem coeToPowerSeries_mapMatrix_one_sub_X_matrix (M : Matrix n n K) :
    (Polynomial.coeToPowerSeries.ringHom.mapMatrix
      (1 - (Polynomial.X : Polynomial K) • M.map Polynomial.C)) =
      oneSubXMatrix (K := K) M := by
  apply Matrix.ext
  intro i j
  simp [oneSubXMatrix, Matrix.one_apply, Matrix.map_apply, Pi.smul_apply, smul_eq_mul]
  by_cases hij : i = j
  · rw [if_pos hij]
    rw [hij]
    rw [sub_eq_add_neg]
  · rw [if_neg hij]
    rw [sub_eq_add_neg]

/-- The determinant of `1 - XM` over scalar power series is `M.charpolyRev`. -/
theorem det_oneSubXMatrix (M : Matrix n n K) :
    (oneSubXMatrix (K := K) M).det = (M.charpolyRev : K⟦X⟧) := by
  rw [← coeToPowerSeries_mapMatrix_one_sub_X_matrix (K := K) M]
  rw [← RingHom.map_det]
  simp [Matrix.charpolyRev]

/-- For `A = 1 - XM`, the adjugate is `det(A)` times the geometric
resolvent. -/
theorem adjugate_oneSubXMatrix_eq_charpolyRev_smul_matrixResolvent
    (M : Matrix n n K) :
    (oneSubXMatrix (K := K) M).adjugate =
      (M.charpolyRev : K⟦X⟧) • matrixResolvent (K := K) M := by
  let A : Matrix n n K⟦X⟧ := oneSubXMatrix (K := K) M
  let R : Matrix n n K⟦X⟧ := matrixResolvent (K := K) M
  have hAR : A * R = 1 := by
    simpa [A, R] using oneSubXMatrix_mul_matrixResolvent (K := K) M
  have hdet : A.det = (M.charpolyRev : K⟦X⟧) := by
    simpa [A] using det_oneSubXMatrix (K := K) M
  calc
    A.adjugate = A.adjugate * 1 := by rw [mul_one]
    _ = A.adjugate * (A * R) := by rw [hAR]
    _ = (A.adjugate * A) * R := by rw [Matrix.mul_assoc]
    _ = (A.det • (1 : Matrix n n K⟦X⟧)) * R := by rw [Matrix.adjugate_mul]
    _ = A.det • R := by simp [Matrix.smul_mul]
    _ = (M.charpolyRev : K⟦X⟧) • R := by rw [hdet]
    _ = (M.charpolyRev : K⟦X⟧) • matrixResolvent (K := K) M := by rfl

/-- The trace-resolvent series is the entrywise trace contraction
`trace(MR)`. -/
theorem traceResolventSeries_eq_sum_matrixResolvent (M : Matrix n n K) :
    traceResolventSeries (K := K) M =
      ∑ i : n, ∑ j : n,
        PowerSeries.C K (M i j) * matrixResolvent (K := K) M j i := by
  classical
  apply PowerSeries.ext
  intro k
  simp [traceResolventSeries, Matrix.trace, Matrix.mul_apply, pow_succ',
    Finset.mul_sum, Finset.sum_mul]

/-- The adjugate contraction is `det(1 - XM)` times the resolvent trace. -/
theorem charpolyRev_mul_traceResolventSeries_eq_trace_adjugate
    (M : Matrix n n K) :
    (M.charpolyRev : K⟦X⟧) * traceResolventSeries (K := K) M =
      ∑ i : n, ∑ j : n,
        PowerSeries.C K (M i j) *
          (oneSubXMatrix (K := K) M).adjugate j i := by
  classical
  rw [traceResolventSeries_eq_sum_matrixResolvent (K := K) M]
  rw [adjugate_oneSubXMatrix_eq_charpolyRev_smul_matrixResolvent (K := K) M]
  simp [Pi.smul_apply, smul_eq_mul, Finset.mul_sum, Finset.sum_mul, mul_assoc,
    mul_comm, mul_left_comm]

/-- Coercing the polynomial Jacobi adjugate contraction into power series gives
the adjugate contraction for `oneSubXMatrix`. -/
theorem coe_trace_adjugate_eq_trace_adjugate_oneSubXMatrix
    (M : Matrix n n K) :
    ((∑ i : n, ∑ j : n,
        Polynomial.C (M i j) *
          (1 - (Polynomial.X : Polynomial K) • M.map Polynomial.C).adjugate j i :
      Polynomial K) : K⟦X⟧) =
      ∑ i : n, ∑ j : n,
        PowerSeries.C K (M i j) *
          (oneSubXMatrix (K := K) M).adjugate j i := by
  classical
  let Aₚ : Matrix n n (Polynomial K) :=
    1 - (Polynomial.X : Polynomial K) • M.map Polynomial.C
  have hentry :
      ∀ i j : n,
        ((Aₚ.adjugate j i : Polynomial K) : K⟦X⟧) =
          (oneSubXMatrix (K := K) M).adjugate j i := by
    intro i j
    have hmat :
        Polynomial.coeToPowerSeries.ringHom.mapMatrix Aₚ.adjugate =
          (oneSubXMatrix (K := K) M).adjugate := by
      rw [RingHom.map_adjugate]
      exact congrArg Matrix.adjugate
        (by simpa [Aₚ] using coeToPowerSeries_mapMatrix_one_sub_X_matrix (K := K) M)
    exact congrFun (congrFun hmat j) i
  change Polynomial.coeToPowerSeries.ringHom
      (∑ i : n, ∑ j : n,
        Polynomial.C (M i j) * Aₚ.adjugate j i) =
      ∑ i : n, ∑ j : n,
        PowerSeries.C K (M i j) *
          (oneSubXMatrix (K := K) M).adjugate j i
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro j hj
  rw [map_mul]
  simp [Polynomial.coeToPowerSeries.ringHom_apply, Polynomial.coe_C, hentry]

/-- The Jacobi/log-derivative numerator identity for `det(1 - XM)`. -/
theorem derivative_charpolyRev_eq_neg_charpolyRev_mul_traceResolventSeries
    (M : Matrix n n K) :
    ((Polynomial.derivative M.charpolyRev : Polynomial K) : K⟦X⟧) =
      -((M.charpolyRev : K⟦X⟧) * traceResolventSeries (K := K) M) := by
  classical
  have h :=
    congrArg (fun p : Polynomial K => (p : K⟦X⟧))
      (derivative_charpolyRev_eq_neg_trace_adjugate (K := K) M)
  change (fun p : Polynomial K => (p : K⟦X⟧)) (Polynomial.derivative M.charpolyRev) =
      -((M.charpolyRev : K⟦X⟧) * traceResolventSeries (K := K) M)
  rw [h]
  simp only [Polynomial.coe_neg]
  rw [coe_trace_adjugate_eq_trace_adjugate_oneSubXMatrix (K := K) M]
  rw [← charpolyRev_mul_traceResolventSeries_eq_trace_adjugate (K := K) M]

/-- Power-series derivative form of the Jacobi/log-derivative numerator
identity for `det(1 - XM)`. -/
theorem powerSeries_derivative_charpolyRev_eq_neg_charpolyRev_mul_traceResolventSeries
    (M : Matrix n n K) :
    PowerSeries.derivative K (M.charpolyRev : K⟦X⟧) =
      -((M.charpolyRev : K⟦X⟧) * traceResolventSeries (K := K) M) := by
  rw [PowerSeries.derivative_coe]
  exact derivative_charpolyRev_eq_neg_charpolyRev_mul_traceResolventSeries (K := K) M

/-- The reverse characteristic polynomial is normalized at `X = 0`. -/
theorem coeff_zero_charpolyRev (M : Matrix n n K) :
    PowerSeries.coeff K 0 (M.charpolyRev : K⟦X⟧) = 1 := by
  rw [Polynomial.coeff_coe]
  rw [Polynomial.coeff_zero_eq_eval_zero]
  rw [Matrix.charpolyRev]
  change Polynomial.evalRingHom (R := K) 0
      ((1 - (Polynomial.X : Polynomial K) • M.map Polynomial.C).det) = 1
  rw [RingHom.map_det]
  have hmat :
      (Polynomial.evalRingHom (R := K) 0).mapMatrix
          (1 - (Polynomial.X : Polynomial K) • M.map Polynomial.C) =
        (1 : Matrix n n K) := by
    ext i j
    by_cases hij : i = j <;>
      simp [hij, Matrix.one_apply, Matrix.map_apply, Pi.smul_apply]
  rw [hmat, Matrix.det_one]

/-- The logarithmic derivative of `det(1 - XM)` is the negative trace
resolvent. -/
theorem derivative_formalLog_charpolyRev
    [CharZero K] (M : Matrix n n K) :
    PowerSeries.derivative K (formalLog (M.charpolyRev : K⟦X⟧)) =
      -traceResolventSeries (K := K) M := by
  let f : K⟦X⟧ := (M.charpolyRev : K⟦X⟧)
  have h0 : PowerSeries.coeff K 0 f = 1 := by
    simpa [f] using coeff_zero_charpolyRev (K := K) M
  have hconst : PowerSeries.constantCoeff K f ≠ 0 := by
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply]
    simp [h0]
  rw [derivative_formalLog_eq_derivative_mul_inv (K := K) f h0]
  have hderiv :
      PowerSeries.derivative K f =
        -(f * traceResolventSeries (K := K) M) := by
    simpa [f] using
      powerSeries_derivative_charpolyRev_eq_neg_charpolyRev_mul_traceResolventSeries
        (K := K) M
  rw [hderiv]
  calc
    (-(f * traceResolventSeries (K := K) M)) * f⁻¹ =
        -(traceResolventSeries (K := K) M * (f * f⁻¹)) := by
          calc
            (-(f * traceResolventSeries (K := K) M)) * f⁻¹ =
                -((f * traceResolventSeries (K := K) M) * f⁻¹) := by
                  rw [neg_mul]
            _ = -(f * (traceResolventSeries (K := K) M * f⁻¹)) := by
                  rw [mul_assoc]
            _ = -((traceResolventSeries (K := K) M * f) * f⁻¹) := by
                  rw [mul_comm f (traceResolventSeries (K := K) M)]
            _ = -(traceResolventSeries (K := K) M * (f * f⁻¹)) := by
                  rw [mul_assoc]
    _ = -traceResolventSeries (K := K) M := by
        rw [PowerSeries.mul_inv_cancel f hconst, mul_one]

/-- The coefficient form of the determinant trace expansion for positive
degrees, written with an explicit successor index. -/
theorem coeff_formalLog_charpolyRev_succ
    [CharZero K] (M : Matrix n n K) (k : ℕ) :
    PowerSeries.coeff K (k + 1)
        (formalLog (M.charpolyRev : K⟦X⟧)) =
      -Matrix.trace (M ^ (k + 1)) / ((k + 1 : ℕ) : K) := by
  have hderiv := congrArg (PowerSeries.coeff K k)
    (derivative_formalLog_charpolyRev (K := K) M)
  rw [PowerSeries.coeff_derivative] at hderiv
  have hneg :
      PowerSeries.coeff K k (-traceResolventSeries (K := K) M) =
        -PowerSeries.coeff K k (traceResolventSeries (K := K) M) := by
    simp
  rw [hneg, coeff_traceResolventSeries] at hderiv
  have hk : ((k + 1 : ℕ) : K) ≠ 0 := by
    simpa [add_comm] using Nat.cast_add_one_ne_zero (R := K) k
  rw [eq_div_iff hk]
  simpa [mul_comm] using hderiv

/-- The coefficient form of
`log det(1 - XM) = -∑_{m ≥ 1} trace(M^m) X^m / m`. -/
theorem coeff_formalLog_charpolyRev
    [CharZero K] (M : Matrix n n K) (m : ℕ) (hm : m ≠ 0) :
    PowerSeries.coeff K m
        (formalLog (M.charpolyRev : K⟦X⟧)) =
      -Matrix.trace (M ^ m) / (m : K) := by
  cases m with
  | zero => contradiction
  | succ k =>
      simpa [Nat.succ_eq_add_one] using
        coeff_formalLog_charpolyRev_succ (K := K) M k

/-- The logarithmic trace expansion for the Euler polynomial of a
finite-dimensional linear endomorphism. -/
theorem coeff_formalLog_eulerPolynomial_eq_neg_trace_pow
    [CharZero K]
    {V : Type*} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (F : Module.End K V) (m : ℕ) (hm : m ≠ 0) :
    PowerSeries.coeff K m
        (formalLog (Boundary.LinearEulerFactor.eulerPolynomial F : K⟦X⟧)) =
      -LinearMap.trace K V (F ^ m) / (m : K) := by
  let b := Module.Free.chooseBasis K V
  have hchar :
      F.charpoly.reverse = (LinearMap.toMatrix b b F).charpoly.reverse := by
    rw [LinearMap.charpoly_toMatrix]
  have hpoly :
      Boundary.LinearEulerFactor.eulerPolynomial F =
        (LinearMap.toMatrix b b F).charpolyRev := by
    calc
      Boundary.LinearEulerFactor.eulerPolynomial F = F.charpoly.reverse := rfl
      _ = (LinearMap.toMatrix b b F).charpoly.reverse := hchar
      _ = (LinearMap.toMatrix b b F).charpolyRev := by
          rw [Matrix.reverse_charpoly]
  rw [hpoly]
  rw [coeff_formalLog_charpolyRev (K := K) (M := LinearMap.toMatrix b b F) m hm]
  rw [LinearMap.trace_eq_matrix_trace K b (F ^ m)]
  rw [LinearMap.toMatrix_pow]

/-- The matrix geometric series is a right inverse to `1 - MX`. -/
theorem matrixGeometricSeries_mul_one_sub_C_mul_X (M : Matrix n n K) :
    matrixGeometricSeries (K := K) M *
        (1 - PowerSeries.C (Matrix n n K) M * PowerSeries.X) =
      1 := by
  apply PowerSeries.ext
  intro k
  cases k with
  | zero =>
      simp [matrixGeometricSeries]
  | succ k =>
      change PowerSeries.coeff (Matrix n n K) (k + 1)
          (matrixGeometricSeries (K := K) M *
            (1 - PowerSeries.C (Matrix n n K) M * PowerSeries.X)) =
        PowerSeries.coeff (Matrix n n K) (k + 1) 1
      have hmul :
          matrixGeometricSeries (K := K) M * (PowerSeries.C (Matrix n n K) M * PowerSeries.X) =
            (matrixGeometricSeries (K := K) M * PowerSeries.C (Matrix n n K) M) *
              PowerSeries.X := by
        rw [mul_assoc]
      rw [sub_eq_add_neg, mul_add, mul_neg]
      have hcoeff :
          PowerSeries.coeff (Matrix n n K) (k + 1)
            (matrixGeometricSeries (K := K) M *
              (PowerSeries.C (Matrix n n K) M * PowerSeries.X)) =
            M ^ k * M := by
        calc
          PowerSeries.coeff (Matrix n n K) (k + 1)
              (matrixGeometricSeries (K := K) M *
                (PowerSeries.C (Matrix n n K) M * PowerSeries.X)) =
              PowerSeries.coeff (Matrix n n K) (k + 1)
                ((matrixGeometricSeries (K := K) M * PowerSeries.C (Matrix n n K) M) *
                  PowerSeries.X) := by simpa [hmul]
          _ = PowerSeries.coeff (Matrix n n K) k
                (matrixGeometricSeries (K := K) M * PowerSeries.C (Matrix n n K) M) := by
                exact
                  (PowerSeries.coeff_mul_X_pow
                    (p := matrixGeometricSeries (K := K) M * PowerSeries.C (Matrix n n K) M)
                    (n := 1) (d := k))
          _ = M ^ k * M := by
                rw [PowerSeries.coeff_mul_C]
                simp [matrixGeometricSeries]
      simp [matrixGeometricSeries] at hcoeff
      simp [matrixGeometricSeries]
      have hcoeff_neg :
          -(PowerSeries.coeff (Matrix n n K) (k + 1)
              ((PowerSeries.mk fun k => M ^ k) *
                (PowerSeries.C (Matrix n n K) M * PowerSeries.X))) =
            -(M ^ k * M) := by
        exact congrArg Neg.neg hcoeff
      rw [hcoeff_neg]
      simp [pow_succ]

/-- The matrix geometric series is a left inverse to `1 - MX`. -/
theorem one_sub_C_mul_X_mul_matrixGeometricSeries (M : Matrix n n K) :
    (1 - PowerSeries.C (Matrix n n K) M * PowerSeries.X) *
        matrixGeometricSeries (K := K) M =
      1 := by
  apply PowerSeries.ext
  intro k
  cases k with
  | zero =>
      simp [matrixGeometricSeries]
  | succ k =>
      change PowerSeries.coeff (Matrix n n K) (k + 1)
          ((1 - PowerSeries.C (Matrix n n K) M * PowerSeries.X) *
            matrixGeometricSeries (K := K) M) =
        PowerSeries.coeff (Matrix n n K) (k + 1) 1
      have hmul :
          (PowerSeries.C (Matrix n n K) M * PowerSeries.X) *
              matrixGeometricSeries (K := K) M =
            PowerSeries.C (Matrix n n K) M *
              (PowerSeries.X * matrixGeometricSeries (K := K) M) := by
        rw [mul_assoc]
      rw [sub_eq_add_neg, add_mul, neg_mul]
      have hcoeff :
          PowerSeries.coeff (Matrix n n K) (k + 1)
            ((PowerSeries.C (Matrix n n K) M * PowerSeries.X) *
              matrixGeometricSeries (K := K) M) =
            M * M ^ k := by
        calc
          PowerSeries.coeff (Matrix n n K) (k + 1)
              ((PowerSeries.C (Matrix n n K) M * PowerSeries.X) *
                matrixGeometricSeries (K := K) M) =
              PowerSeries.coeff (Matrix n n K) (k + 1)
                (PowerSeries.C (Matrix n n K) M *
                  (PowerSeries.X * matrixGeometricSeries (K := K) M)) := by
                  rw [hmul]
          _ = M * PowerSeries.coeff (Matrix n n K) (k + 1)
                (PowerSeries.X * matrixGeometricSeries (K := K) M) := by
                rw [PowerSeries.coeff_C_mul]
          _ = M * PowerSeries.coeff (Matrix n n K) k
                (matrixGeometricSeries (K := K) M) := by
                rw [show (PowerSeries.X : (Matrix n n K)⟦X⟧) =
                    PowerSeries.X ^ 1 by simp]
                rw [PowerSeries.coeff_X_pow_mul (p := matrixGeometricSeries (K := K) M)
                  (n := 1) (d := k)]
          _ = M * M ^ k := by
                simp [matrixGeometricSeries]
      simp [matrixGeometricSeries] at hcoeff
      simp [matrixGeometricSeries]
      have hcoeff_neg :
          -(PowerSeries.coeff (Matrix n n K) (k + 1)
              ((PowerSeries.C (Matrix n n K) M * PowerSeries.X) *
                (PowerSeries.mk fun k => M ^ k))) =
            -(M * M ^ k) := by
        exact congrArg Neg.neg hcoeff
      rw [hcoeff_neg]
      simp [pow_succ']

/-- The determinant side and the resolvent trace side agree in degree zero of
the logarithmic derivative identity for `det(1 - XM)`. -/
theorem derivative_charpolyRev_eval_zero_eq_neg_traceResolventCoeff
    (M : Matrix n n K) :
    (Polynomial.derivative M.charpolyRev).eval 0 =
      -PowerSeries.coeff K 0 (traceResolventSeries (K := K) M) := by
  rw [← Polynomial.coeff_zero_eq_eval_zero, Polynomial.coeff_derivative]
  simp [Matrix.coeff_charpolyRev_eq_neg_trace, traceResolventSeries]

end MatrixSeries

end

end TraceExpansion
end Boundary
