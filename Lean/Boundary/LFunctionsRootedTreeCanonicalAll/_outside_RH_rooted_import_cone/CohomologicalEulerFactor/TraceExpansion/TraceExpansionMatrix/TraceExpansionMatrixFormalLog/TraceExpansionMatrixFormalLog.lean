import Boundary.LFunctionsRootedTreeCanonicalAll._outside_RH_rooted_import_cone.TraceExpansionMatrixDeterminant.TraceExpansionMatrixDeterminant
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.RingTheory.PowerSeries.Derivative

/-!
# Formal logarithmic trace expansions: matrix formal-log layer

This file owns evaluation-at-zero facts, the formal logarithm of `charpolyRev`,
and Euler-polynomial coefficient consequences.
-/

open scoped BigOperators PowerSeries

namespace Boundary
namespace TraceExpansion

noncomputable section

variable {K : Type*} [Field K]

section MatrixSeries

variable {n : Type*} [Fintype n] [DecidableEq n]

theorem coeff_zero_coe_polynomial_eq_eval_zero (p : Polynomial K) :
    PowerSeries.coeff K 0 (p : K⟦X⟧) =
      Polynomial.evalRingHom (R := K) 0 p := by
  exact (Polynomial.coeff_coe (R := K) p 0).trans
    (Polynomial.coeff_zero_eq_eval_zero p)

omit [Fintype n] in
theorem eval_zero_polynomial_indicator (i j : n) :
    Polynomial.evalRingHom (R := K) 0 (if i = j then 1 else 0 : Polynomial K) =
      if i = j then 1 else 0 := by
  match (inferInstance : Decidable (i = j)) with
  | .isTrue hij =>
      exact ((congrArg (Polynomial.evalRingHom (R := K) 0) (if_pos hij)).trans
        ((map_one (Polynomial.evalRingHom (R := K) 0)).trans (if_pos hij).symm))
  | .isFalse hij =>
      exact ((congrArg (Polynomial.evalRingHom (R := K) 0) (if_neg hij)).trans
        ((map_zero (Polynomial.evalRingHom (R := K) 0)).trans (if_neg hij).symm))

theorem eval_zero_X_mul_C (a : K) :
    Polynomial.evalRingHom (R := K) 0 (Polynomial.X * Polynomial.C a) = 0 := by
  have hmul :
      Polynomial.evalRingHom (R := K) 0 (Polynomial.X * Polynomial.C a) =
        Polynomial.evalRingHom (R := K) 0 Polynomial.X *
          Polynomial.evalRingHom (R := K) 0 (Polynomial.C a) := by
    exact map_mul (Polynomial.evalRingHom (R := K) 0) Polynomial.X (Polynomial.C a)
  have hx :
      Polynomial.evalRingHom (R := K) 0 Polynomial.X *
          Polynomial.evalRingHom (R := K) 0 (Polynomial.C a) =
        0 * Polynomial.evalRingHom (R := K) 0 (Polynomial.C a) := by
    exact congrArg (fun t : K => t * Polynomial.evalRingHom (R := K) 0 (Polynomial.C a))
      (Polynomial.eval_X : Polynomial.evalRingHom (R := K) 0 Polynomial.X = 0)
  have hzero : 0 * Polynomial.evalRingHom (R := K) 0 (Polynomial.C a) = 0 := by
    exact zero_mul (Polynomial.evalRingHom (R := K) 0 (Polynomial.C a))
  exact hmul.trans (hx.trans hzero)

omit [Fintype n] in
theorem eval_zero_polynomial_one_sub_X_matrix_entry
    (M : Matrix n n K) (i j : n) :
    Polynomial.evalRingHom (R := K) 0
        ((1 - (Polynomial.X : Polynomial K) • M.map Polynomial.C) i j) =
      (1 : Matrix n n K) i j := by
  have hentry :
      Polynomial.evalRingHom (R := K) 0
        ((1 - (Polynomial.X : Polynomial K) • M.map Polynomial.C) i j) =
        Polynomial.evalRingHom (R := K) 0
          ((if i = j then 1 else 0 : Polynomial K) -
            Polynomial.X * Polynomial.C (M i j)) := by
    exact congrArg (Polynomial.evalRingHom (R := K) 0)
      (polynomial_one_sub_X_matrix_entry (K := K) M i j)
  have hsub :
      Polynomial.evalRingHom (R := K) 0
          ((if i = j then 1 else 0 : Polynomial K) -
            Polynomial.X * Polynomial.C (M i j)) =
        Polynomial.evalRingHom (R := K) 0
          (if i = j then 1 else 0 : Polynomial K) -
        Polynomial.evalRingHom (R := K) 0 (Polynomial.X * Polynomial.C (M i j)) := by
    exact map_sub (Polynomial.evalRingHom (R := K) 0)
      (if i = j then 1 else 0 : Polynomial K)
      (Polynomial.X * Polynomial.C (M i j))
  have hindicator :
      Polynomial.evalRingHom (R := K) 0 (if i = j then 1 else 0 : Polynomial K) -
        Polynomial.evalRingHom (R := K) 0 (Polynomial.X * Polynomial.C (M i j)) =
      (if i = j then 1 else 0) -
        Polynomial.evalRingHom (R := K) 0 (Polynomial.X * Polynomial.C (M i j)) := by
    exact congrArg
      (fun t : K => t -
        Polynomial.evalRingHom (R := K) 0 (Polynomial.X * Polynomial.C (M i j)))
      (eval_zero_polynomial_indicator (K := K) i j)
  have hmonomial :
      (if i = j then 1 else 0 : K) -
        Polynomial.evalRingHom (R := K) 0 (Polynomial.X * Polynomial.C (M i j)) =
      (if i = j then 1 else 0 : K) - 0 := by
    exact congrArg (fun t : K => (if i = j then 1 else 0 : K) - t)
      (eval_zero_X_mul_C (K := K) (M i j))
  have hzero :
      (if i = j then 1 else 0 : K) - 0 = (if i = j then 1 else 0 : K) := by
    exact sub_zero (if i = j then 1 else 0 : K)
  have hone :
      (if i = j then 1 else 0 : K) = (1 : Matrix n n K) i j := by
    exact (Matrix.one_apply :
      (1 : Matrix n n K) i j = if i = j then 1 else 0).symm
  exact hentry.trans (hsub.trans (hindicator.trans (hmonomial.trans (hzero.trans hone))))

theorem eval_zero_mapMatrix_one_sub_X_matrix_entry
    (M : Matrix n n K) (i j : n) :
    ((Polynomial.evalRingHom (R := K) 0).mapMatrix
      (1 - (Polynomial.X : Polynomial K) • M.map Polynomial.C)) i j =
      (1 : Matrix n n K) i j := by
  have hentry :
      ((Polynomial.evalRingHom (R := K) 0).mapMatrix
        (1 - (Polynomial.X : Polynomial K) • M.map Polynomial.C)) i j =
        Polynomial.evalRingHom (R := K) 0
          ((1 - (Polynomial.X : Polynomial K) • M.map Polynomial.C) i j) := by
    exact Matrix.map_apply
      (M := 1 - (Polynomial.X : Polynomial K) • M.map Polynomial.C)
      (f := Polynomial.evalRingHom (R := K) 0) (i := i) (j := j)
  have hone :
      Polynomial.evalRingHom (R := K) 0
          ((1 - (Polynomial.X : Polynomial K) • M.map Polynomial.C) i j) =
        (1 : Matrix n n K) i j := by
    exact eval_zero_polynomial_one_sub_X_matrix_entry (K := K) M i j
  exact hentry.trans hone

theorem eval_zero_mapMatrix_one_sub_X_matrix
    (M : Matrix n n K) :
    (Polynomial.evalRingHom (R := K) 0).mapMatrix
        (1 - (Polynomial.X : Polynomial K) • M.map Polynomial.C) =
      (1 : Matrix n n K) := by
  exact Matrix.ext
    (fun i j => eval_zero_mapMatrix_one_sub_X_matrix_entry (K := K) M i j)

theorem eval_zero_det_one_sub_X_matrix (M : Matrix n n K) :
    Polynomial.evalRingHom (R := K) 0
        ((1 - (Polynomial.X : Polynomial K) • M.map Polynomial.C).det) =
      1 := by
  have hdet :
      Polynomial.evalRingHom (R := K) 0
        ((1 - (Polynomial.X : Polynomial K) • M.map Polynomial.C).det) =
        ((Polynomial.evalRingHom (R := K) 0).mapMatrix
          (1 - (Polynomial.X : Polynomial K) • M.map Polynomial.C)).det := by
    exact RingHom.map_det (Polynomial.evalRingHom (R := K) 0)
      (1 - (Polynomial.X : Polynomial K) • M.map Polynomial.C)
  have hmatrix :
      ((Polynomial.evalRingHom (R := K) 0).mapMatrix
          (1 - (Polynomial.X : Polynomial K) • M.map Polynomial.C)).det =
        (1 : Matrix n n K).det := by
    exact congrArg Matrix.det (eval_zero_mapMatrix_one_sub_X_matrix (K := K) M)
  have hone : (1 : Matrix n n K).det = 1 := by
    exact Matrix.det_one
  exact hdet.trans (hmatrix.trans hone)

theorem eval_zero_charpolyRev (M : Matrix n n K) :
    Polynomial.evalRingHom (R := K) 0 M.charpolyRev = 1 := by
  have hchar :
      Polynomial.evalRingHom (R := K) 0 M.charpolyRev =
        Polynomial.evalRingHom (R := K) 0
          ((1 - (Polynomial.X : Polynomial K) • M.map Polynomial.C).det) := by
    exact congrArg (Polynomial.evalRingHom (R := K) 0)
      (charpolyRev_eq_det_one_sub_X_matrix (K := K) M)
  have hdet :
      Polynomial.evalRingHom (R := K) 0
          ((1 - (Polynomial.X : Polynomial K) • M.map Polynomial.C).det) = 1 := by
    exact eval_zero_det_one_sub_X_matrix (K := K) M
  exact hchar.trans hdet

theorem coeff_zero_charpolyRev (M : Matrix n n K) :
    PowerSeries.coeff K 0 (M.charpolyRev : K⟦X⟧) = 1 := by
  exact (coeff_zero_coe_polynomial_eq_eval_zero (K := K) M.charpolyRev).trans
    (eval_zero_charpolyRev (K := K) M)

theorem derivative_formalLog_charpolyRev_eq_derivative_mul_inv
    [CharZero K] (M : Matrix n n K) :
    PowerSeries.derivative K (formalLog (M.charpolyRev : K⟦X⟧)) =
      PowerSeries.derivative K (M.charpolyRev : K⟦X⟧) *
        (M.charpolyRev : K⟦X⟧)⁻¹ := by
  exact derivative_formalLog_eq_derivative_mul_inv
    (K := K) (M.charpolyRev : K⟦X⟧) (coeff_zero_charpolyRev (K := K) M)

theorem derivative_charpolyRev_mul_inv_eq_neg_traceResolventSeries
    (M : Matrix n n K) :
    PowerSeries.derivative K (M.charpolyRev : K⟦X⟧) *
        (M.charpolyRev : K⟦X⟧)⁻¹ =
      -traceResolventSeries (K := K) M := by
  have hderivative :
      PowerSeries.derivative K (M.charpolyRev : K⟦X⟧) *
        (M.charpolyRev : K⟦X⟧)⁻¹ =
        (-((M.charpolyRev : K⟦X⟧) * traceResolventSeries (K := K) M)) *
          (M.charpolyRev : K⟦X⟧)⁻¹ := by
    exact congrArg (fun t : K⟦X⟧ => t * (M.charpolyRev : K⟦X⟧)⁻¹)
      (powerSeries_derivative_charpolyRev_eq_neg_charpolyRev_mul_traceResolventSeries
        (K := K) M)
  have hcancel :
      (-((M.charpolyRev : K⟦X⟧) * traceResolventSeries (K := K) M)) *
          (M.charpolyRev : K⟦X⟧)⁻¹ =
        -traceResolventSeries (K := K) M := by
    exact neg_mul_mul_inv_cancel_comm
      (M.charpolyRev : K⟦X⟧)
      (traceResolventSeries (K := K) M)
      (coeff_zero_charpolyRev (K := K) M)
  exact hderivative.trans hcancel

theorem derivative_formalLog_charpolyRev
    [CharZero K] (M : Matrix n n K) :
    PowerSeries.derivative K (formalLog (M.charpolyRev : K⟦X⟧)) =
      -traceResolventSeries (K := K) M := by
  exact (derivative_formalLog_charpolyRev_eq_derivative_mul_inv (K := K) M).trans
    (derivative_charpolyRev_mul_inv_eq_neg_traceResolventSeries (K := K) M)

theorem coeff_neg_traceResolventSeries (M : Matrix n n K) (k : ℕ) :
    PowerSeries.coeff K k (-traceResolventSeries (K := K) M) =
      -PowerSeries.coeff K k (traceResolventSeries (K := K) M) := by
  exact map_neg (PowerSeries.coeff K k) (traceResolventSeries (K := K) M)

theorem coeff_neg_traceResolventSeries_eq_neg_trace
    (M : Matrix n n K) (k : ℕ) :
    PowerSeries.coeff K k (-traceResolventSeries (K := K) M) =
      -Matrix.trace (M ^ (k + 1)) := by
  exact (coeff_neg_traceResolventSeries (K := K) M k).trans
    (congrArg Neg.neg (coeff_traceResolventSeries (K := K) M k))

theorem coeff_derivative_formalLog_charpolyRev_eq_neg_trace
    [CharZero K] (M : Matrix n n K) (k : ℕ) :
    PowerSeries.coeff K k
        (PowerSeries.derivative K (formalLog (M.charpolyRev : K⟦X⟧))) =
      -Matrix.trace (M ^ (k + 1)) := by
  exact (congrArg (PowerSeries.coeff K k)
    (derivative_formalLog_charpolyRev (K := K) M)).trans
    (coeff_neg_traceResolventSeries_eq_neg_trace (K := K) M k)

theorem coeff_derivative_formalLog_charpolyRev_as_mul_coeff
    (M : Matrix n n K) (k : ℕ) :
    PowerSeries.coeff K k
        (PowerSeries.derivative K (formalLog (M.charpolyRev : K⟦X⟧))) =
      ((k + 1 : ℕ) : K) *
        PowerSeries.coeff K (k + 1)
          (formalLog (M.charpolyRev : K⟦X⟧)) := by
  have hderivative :
      PowerSeries.coeff K k
        (PowerSeries.derivative K (formalLog (M.charpolyRev : K⟦X⟧))) =
        PowerSeries.coeff K (k + 1)
          (formalLog (M.charpolyRev : K⟦X⟧)) * ((k : K) + 1) := by
    exact PowerSeries.coeff_derivative
      (formalLog (M.charpolyRev : K⟦X⟧)) k
  have hcast :
      PowerSeries.coeff K (k + 1)
          (formalLog (M.charpolyRev : K⟦X⟧)) * ((k : K) + 1) =
        PowerSeries.coeff K (k + 1)
          (formalLog (M.charpolyRev : K⟦X⟧)) * ((k + 1 : ℕ) : K) := by
    exact congrArg
      (fun t : K =>
        PowerSeries.coeff K (k + 1) (formalLog (M.charpolyRev : K⟦X⟧)) * t)
      (Nat.cast_add_one k).symm
  have hcomm :
      PowerSeries.coeff K (k + 1)
          (formalLog (M.charpolyRev : K⟦X⟧)) * ((k + 1 : ℕ) : K) =
        ((k + 1 : ℕ) : K) *
        PowerSeries.coeff K (k + 1)
          (formalLog (M.charpolyRev : K⟦X⟧)) := by
    exact mul_comm
      (PowerSeries.coeff K (k + 1) (formalLog (M.charpolyRev : K⟦X⟧)))
      ((k + 1 : ℕ) : K)
  exact hderivative.trans (hcast.trans hcomm)

theorem nat_cast_succ_ne_zero_field [CharZero K] (k : ℕ) :
    ((k + 1 : ℕ) : K) ≠ 0 := by
  intro hzero
  have hzero' : (k : K) + 1 = 0 := by
    exact (Nat.cast_add_one k).symm.trans hzero
  exact Nat.cast_add_one_ne_zero (R := K) k hzero'

theorem eq_div_of_mul_eq {a x y : K} (ha : a ≠ 0) (h : a * x = y) :
    x = y / a := by
  have hone : x = 1 * x := by
    exact (one_mul x).symm
  have hinv : 1 * x = (a⁻¹ * a) * x := by
    exact congrArg (fun t : K => t * x) (inv_mul_cancel₀ ha).symm
  have hassoc : (a⁻¹ * a) * x = a⁻¹ * (a * x) := by
    exact mul_assoc a⁻¹ a x
  have hmul : a⁻¹ * (a * x) = a⁻¹ * y := by
    exact congrArg (fun t : K => a⁻¹ * t) h
  have hcomm : a⁻¹ * y = y * a⁻¹ := by
    exact mul_comm a⁻¹ y
  have hdiv : y * a⁻¹ = y / a := by
    exact (div_eq_mul_inv y a).symm
  exact hone.trans (hinv.trans (hassoc.trans (hmul.trans (hcomm.trans hdiv))))

theorem coeff_formalLog_charpolyRev_succ_mul_eq_neg_trace
    [CharZero K] (M : Matrix n n K) (k : ℕ) :
    ((k + 1 : ℕ) : K) *
        PowerSeries.coeff K (k + 1)
          (formalLog (M.charpolyRev : K⟦X⟧)) =
      -Matrix.trace (M ^ (k + 1)) := by
  exact (coeff_derivative_formalLog_charpolyRev_as_mul_coeff (K := K) M k).symm.trans
    (coeff_derivative_formalLog_charpolyRev_eq_neg_trace (K := K) M k)

theorem coeff_formalLog_charpolyRev_succ
    [CharZero K] (M : Matrix n n K) (k : ℕ) :
    PowerSeries.coeff K (k + 1)
        (formalLog (M.charpolyRev : K⟦X⟧)) =
      -Matrix.trace (M ^ (k + 1)) / ((k + 1 : ℕ) : K) := by
  exact eq_div_of_mul_eq
    (K := K)
    (nat_cast_succ_ne_zero_field (K := K) k)
    (coeff_formalLog_charpolyRev_succ_mul_eq_neg_trace (K := K) M k)

theorem coeff_formalLog_charpolyRev_nat_succ
    [CharZero K] (M : Matrix n n K) (k : ℕ) :
    PowerSeries.coeff K (Nat.succ k)
        (formalLog (M.charpolyRev : K⟦X⟧)) =
      -Matrix.trace (M ^ Nat.succ k) / ((Nat.succ k : ℕ) : K) := by
  have hindex :
      PowerSeries.coeff K (Nat.succ k)
        (formalLog (M.charpolyRev : K⟦X⟧)) =
        PowerSeries.coeff K (k + 1)
          (formalLog (M.charpolyRev : K⟦X⟧)) := by
    exact congrArg
      (fun t : ℕ =>
        PowerSeries.coeff K t (formalLog (M.charpolyRev : K⟦X⟧)))
      (Nat.succ_eq_add_one k)
  have hcoeff :
      PowerSeries.coeff K (k + 1)
          (formalLog (M.charpolyRev : K⟦X⟧)) =
        -Matrix.trace (M ^ (k + 1)) / ((k + 1 : ℕ) : K) := by
    exact coeff_formalLog_charpolyRev_succ (K := K) M k
  have hsucc :
      -Matrix.trace (M ^ (k + 1)) / ((k + 1 : ℕ) : K) =
        -Matrix.trace (M ^ Nat.succ k) / ((Nat.succ k : ℕ) : K) := by
    exact congrArg
      (fun t : ℕ => -Matrix.trace (M ^ t) / (t : K))
      (Nat.succ_eq_add_one k).symm
  exact hindex.trans (hcoeff.trans hsucc)

theorem coeff_formalLog_charpolyRev
    [CharZero K] (M : Matrix n n K) (m : ℕ) (hm : m ≠ 0) :
    PowerSeries.coeff K m
        (formalLog (M.charpolyRev : K⟦X⟧)) =
      -Matrix.trace (M ^ m) / (m : K) := by
  cases m with
  | zero => contradiction
  | succ k =>
      exact coeff_formalLog_charpolyRev_nat_succ (K := K) M k

theorem eulerPolynomial_eq_charpoly_reverse
    {V : Type*} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (F : Module.End K V) :
    Boundary.LinearEulerFactor.eulerPolynomial F = F.charpoly.reverse := by
  rfl

theorem linearMap_charpoly_reverse_eq_toMatrix_charpoly_reverse
    {V ι : Type*} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    [Fintype ι] [DecidableEq ι]
    (b : Basis ι K V) (F : Module.End K V) :
    F.charpoly.reverse = (LinearMap.toMatrix b b F).charpoly.reverse := by
  exact congrArg Polynomial.reverse (LinearMap.charpoly_toMatrix b (f := F)).symm

theorem matrix_charpoly_reverse_eq_charpolyRev
    (M : Matrix n n K) :
    M.charpoly.reverse = M.charpolyRev := by
  exact Matrix.reverse_charpoly M

theorem eulerPolynomial_eq_toMatrix_charpolyRev
    {V ι : Type*} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    [Fintype ι] [DecidableEq ι]
    (b : Basis ι K V) (F : Module.End K V) :
    Boundary.LinearEulerFactor.eulerPolynomial F =
      (LinearMap.toMatrix b b F).charpolyRev := by
  exact (eulerPolynomial_eq_charpoly_reverse (K := K) F).trans
    ((linearMap_charpoly_reverse_eq_toMatrix_charpoly_reverse (K := K) b F).trans
      (matrix_charpoly_reverse_eq_charpolyRev (K := K) (LinearMap.toMatrix b b F)))

theorem coeff_formalLog_eulerPolynomial_eq_matrix_trace_pow
    [CharZero K]
    {V ι : Type*} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    [Fintype ι] [DecidableEq ι]
    (b : Basis ι K V)
    (F : Module.End K V) (m : ℕ) (hm : m ≠ 0) :
    PowerSeries.coeff K m
        (formalLog (Boundary.LinearEulerFactor.eulerPolynomial F : K⟦X⟧)) =
      -Matrix.trace ((LinearMap.toMatrix b b F) ^ m) / (m : K) := by
  have hpoly :
      PowerSeries.coeff K m
        (formalLog (Boundary.LinearEulerFactor.eulerPolynomial F : K⟦X⟧)) =
        PowerSeries.coeff K m
          (formalLog ((LinearMap.toMatrix b b F).charpolyRev : K⟦X⟧)) := by
    exact congrArg
      (fun p : Polynomial K =>
        PowerSeries.coeff K m (formalLog (p : K⟦X⟧)))
      (eulerPolynomial_eq_toMatrix_charpolyRev (K := K) b F)
  have hcoeff :
      PowerSeries.coeff K m
          (formalLog ((LinearMap.toMatrix b b F).charpolyRev : K⟦X⟧)) =
        -Matrix.trace ((LinearMap.toMatrix b b F) ^ m) / (m : K) := by
    exact coeff_formalLog_charpolyRev
      (K := K) (M := LinearMap.toMatrix b b F) m hm
  exact hpoly.trans hcoeff

theorem linearMap_trace_eq_matrix_trace_toMatrix_pow
    {V ι : Type*} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    [Fintype ι] [DecidableEq ι]
    (b : Basis ι K V)
    (F : Module.End K V) (m : ℕ) :
    LinearMap.trace K V (F ^ m) =
      Matrix.trace ((LinearMap.toMatrix b b F) ^ m) := by
  have htrace :
      LinearMap.trace K V (F ^ m) =
        Matrix.trace (LinearMap.toMatrix b b (F ^ m)) := by
    exact LinearMap.trace_eq_matrix_trace K b (F ^ m)
  have hpow :
      Matrix.trace (LinearMap.toMatrix b b (F ^ m)) =
        Matrix.trace ((LinearMap.toMatrix b b F) ^ m) := by
    exact congrArg Matrix.trace (LinearMap.toMatrix_pow (v₁ := b) F m).symm
  exact htrace.trans hpow

theorem neg_matrix_trace_pow_div_eq_neg_linearMap_trace_div
    {V ι : Type*} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    [Fintype ι] [DecidableEq ι]
    (b : Basis ι K V)
    (F : Module.End K V) (m : ℕ) :
    -Matrix.trace ((LinearMap.toMatrix b b F) ^ m) / (m : K) =
      -LinearMap.trace K V (F ^ m) / (m : K) := by
  exact congrArg (fun t : K => -t / (m : K))
    (linearMap_trace_eq_matrix_trace_toMatrix_pow (K := K) b F m).symm

theorem coeff_formalLog_eulerPolynomial_eq_neg_trace_pow_of_basis
    [CharZero K]
    {V ι : Type*} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    [Fintype ι] [DecidableEq ι]
    (b : Basis ι K V)
    (F : Module.End K V) (m : ℕ) (hm : m ≠ 0) :
    PowerSeries.coeff K m
        (formalLog (Boundary.LinearEulerFactor.eulerPolynomial F : K⟦X⟧)) =
      -LinearMap.trace K V (F ^ m) / (m : K) := by
  exact (coeff_formalLog_eulerPolynomial_eq_matrix_trace_pow (K := K) b F m hm).trans
    (neg_matrix_trace_pow_div_eq_neg_linearMap_trace_div (K := K) b F m)

theorem coeff_formalLog_eulerPolynomial_eq_neg_trace_pow
    [CharZero K]
    {V : Type*} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (F : Module.End K V) (m : ℕ) (hm : m ≠ 0) :
    PowerSeries.coeff K m
        (formalLog (Boundary.LinearEulerFactor.eulerPolynomial F : K⟦X⟧)) =
      -LinearMap.trace K V (F ^ m) / (m : K) := by
  let b := Module.Free.chooseBasis K V
  exact coeff_formalLog_eulerPolynomial_eq_neg_trace_pow_of_basis (K := K) b F m hm
end MatrixSeries

end

end TraceExpansion
end Boundary
