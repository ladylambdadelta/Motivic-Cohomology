import Boundary.LFunctionsRootedTreeFinal.OutsideRHRootedImportCone.CohomologicalEulerFactor.TraceExpansion.TraceExpansionEuler.Owner
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.RingTheory.PowerSeries.Derivative

/-!
# Formal logarithmic trace expansions: matrix resolvent layer

This file owns matrix geometric/resolvent series, `oneSubXMatrix`,
and coefficient identities for the resolvent inverse calculus.
-/

open scoped BigOperators PowerSeries

namespace Boundary
namespace TraceExpansion

noncomputable section

variable {K : Type*} [Field K]

section MatrixSeries

variable {n : Type*} [Fintype n] [DecidableEq n]

def matrixGeometricSeries (M : Matrix n n K) : (Matrix n n K)⟦X⟧ :=
  PowerSeries.mk fun k => M ^ k

theorem coeff_matrixGeometricSeries_def (M : Matrix n n K) (k : ℕ) :
    PowerSeries.coeff (Matrix n n K) k (PowerSeries.mk fun k => M ^ k) = M ^ k := by
  exact PowerSeries.coeff_mk k (fun k => M ^ k)

theorem coeff_matrixGeometricSeries (M : Matrix n n K) (k : ℕ) :
    PowerSeries.coeff (Matrix n n K) k (matrixGeometricSeries (K := K) M) = M ^ k := by
  exact coeff_matrixGeometricSeries_def (K := K) M k

theorem matrix_pow_succ_eq_left_mul (M : Matrix n n K) (k : ℕ) :
    M ^ (k + 1) = M * M ^ k := by
  exact pow_succ' M k

theorem coeff_C_mul_matrixGeometricSeries_after_coeff_C_mul
    (M : Matrix n n K) (k : ℕ) :
    PowerSeries.coeff (Matrix n n K) k
        (PowerSeries.C (Matrix n n K) M * matrixGeometricSeries (K := K) M) =
      M * M ^ k := by
  exact (PowerSeries.coeff_C_mul
    (R := Matrix n n K) k (matrixGeometricSeries (K := K) M) M).trans
    (congrArg (fun T : Matrix n n K => M * T)
      (coeff_matrixGeometricSeries (K := K) M k))

theorem coeff_C_mul_matrixGeometricSeries (M : Matrix n n K) (k : ℕ) :
    PowerSeries.coeff (Matrix n n K) k
        (PowerSeries.C (Matrix n n K) M * matrixGeometricSeries (K := K) M) =
      M ^ (k + 1) := by
  exact (coeff_C_mul_matrixGeometricSeries_after_coeff_C_mul (K := K) M k).trans
    (matrix_pow_succ_eq_left_mul (K := K) M k).symm

def traceResolventSeries (M : Matrix n n K) : K⟦X⟧ :=
  PowerSeries.mk fun k => Matrix.trace (M ^ (k + 1))

theorem coeff_traceResolventSeries_def (M : Matrix n n K) (k : ℕ) :
    PowerSeries.coeff K k (PowerSeries.mk fun k => Matrix.trace (M ^ (k + 1))) =
      Matrix.trace (M ^ (k + 1)) := by
  exact PowerSeries.coeff_mk k (fun k => Matrix.trace (M ^ (k + 1)))

theorem coeff_traceResolventSeries (M : Matrix n n K) (k : ℕ) :
    PowerSeries.coeff K k (traceResolventSeries (K := K) M) =
      Matrix.trace (M ^ (k + 1)) := by
  exact coeff_traceResolventSeries_def (K := K) M k

theorem coeff_trace_C_mul_matrixGeometricSeries (M : Matrix n n K) (k : ℕ) :
    Matrix.trace
      (PowerSeries.coeff (Matrix n n K) k
        (PowerSeries.C (Matrix n n K) M * matrixGeometricSeries (K := K) M)) =
      Matrix.trace (M ^ (k + 1)) := by
  exact congrArg Matrix.trace (coeff_C_mul_matrixGeometricSeries (K := K) M k)

def matrixResolvent (M : Matrix n n K) : Matrix n n K⟦X⟧ :=
  fun i j => PowerSeries.mk fun k => (M ^ k) i j

theorem coeff_matrixResolvent_def (M : Matrix n n K) (i j : n) (k : ℕ) :
    PowerSeries.coeff K k (PowerSeries.mk fun k => (M ^ k) i j) = (M ^ k) i j := by
  exact PowerSeries.coeff_mk k (fun k => (M ^ k) i j)

theorem coeff_matrixResolvent (M : Matrix n n K) (i j : n) (k : ℕ) :
    PowerSeries.coeff K k (matrixResolvent (K := K) M i j) = (M ^ k) i j := by
  exact coeff_matrixResolvent_def (K := K) M i j k

def oneSubXMatrix (M : Matrix n n K) : Matrix n n K⟦X⟧ :=
  1 - (PowerSeries.X : K⟦X⟧) • M.map (PowerSeries.C K)

omit [Fintype n] in
theorem oneSubXMatrix_apply_def (M : Matrix n n K) (i j : n) :
    oneSubXMatrix (K := K) M i j =
      (1 : Matrix n n K⟦X⟧) i j -
        ((PowerSeries.X : K⟦X⟧) • M.map (PowerSeries.C K)) i j := by
  rfl

omit [Fintype n] in
omit [DecidableEq n] in
theorem oneSubXMatrix_smul_apply (M : Matrix n n K) (i j : n) :
    ((PowerSeries.X : K⟦X⟧) • M.map (PowerSeries.C K)) i j =
      PowerSeries.X * PowerSeries.C K (M i j) := by
  rfl

omit [Fintype n] in
theorem oneSubXMatrix_one_apply (i j : n) :
    (1 : Matrix n n K⟦X⟧) i j = if i = j then 1 else 0 := by
  exact Matrix.one_apply

omit [Fintype n] in
theorem oneSubXMatrix_apply (M : Matrix n n K) (i j : n) :
    oneSubXMatrix (K := K) M i j =
      (if i = j then 1 else 0) - PowerSeries.X * PowerSeries.C K (M i j) := by
  exact (oneSubXMatrix_apply_def (K := K) M i j).trans
    (congrArg₂ Sub.sub
      (oneSubXMatrix_one_apply (K := K) i j)
      (oneSubXMatrix_smul_apply (K := K) M i j))

theorem matrixResolvent_mul_X_C_reassociate (M : Matrix n n K) (i j : n) :
    matrixResolvent (K := K) M i j * (PowerSeries.X * PowerSeries.C K (M i j)) =
      (matrixResolvent (K := K) M i j * PowerSeries.X) *
        PowerSeries.C K (M i j) := by
  exact (mul_assoc (matrixResolvent (K := K) M i j)
    PowerSeries.X (PowerSeries.C K (M i j))).symm

theorem matrixResolvent_mul_X_C_reassociate_scalar (M : Matrix n n K) (i j : n) (a : K) :
    matrixResolvent (K := K) M i j * (PowerSeries.X * PowerSeries.C K a) =
      (matrixResolvent (K := K) M i j * PowerSeries.X) *
        PowerSeries.C K a := by
  exact (mul_assoc (matrixResolvent (K := K) M i j)
    PowerSeries.X (PowerSeries.C K a)).symm

theorem coeff_matrixResolvent_mul_X (M : Matrix n n K) (i j : n) (k : ℕ) :
    PowerSeries.coeff K (k + 1) (matrixResolvent (K := K) M i j * PowerSeries.X) =
      PowerSeries.coeff K k (matrixResolvent (K := K) M i j) := by
  have hpow :
      PowerSeries.coeff K (k + 1) (matrixResolvent (K := K) M i j * PowerSeries.X) =
        PowerSeries.coeff K (k + 1)
          (matrixResolvent (K := K) M i j * PowerSeries.X ^ 1) := by
    exact congrArg (PowerSeries.coeff K (k + 1))
      (congrArg (fun t : K⟦X⟧ => matrixResolvent (K := K) M i j * t)
        (pow_one (PowerSeries.X : K⟦X⟧))).symm
  have hcoeff :
      PowerSeries.coeff K (k + 1)
          (matrixResolvent (K := K) M i j * PowerSeries.X ^ 1) =
        PowerSeries.coeff K k (matrixResolvent (K := K) M i j) := by
    exact PowerSeries.coeff_mul_X_pow
      (p := matrixResolvent (K := K) M i j) (n := 1) (d := k)
  exact hpow.trans hcoeff

theorem coeff_matrixResolvent_mul_X_C_scalar (M : Matrix n n K) (i j : n) (a : K) (k : ℕ) :
    PowerSeries.coeff K (k + 1)
        (matrixResolvent (K := K) M i j * (PowerSeries.X * PowerSeries.C K a)) =
      (M ^ k) i j * a := by
  have hreassociate :
      PowerSeries.coeff K (k + 1)
        (matrixResolvent (K := K) M i j * (PowerSeries.X * PowerSeries.C K a)) =
        PowerSeries.coeff K (k + 1)
          ((matrixResolvent (K := K) M i j * PowerSeries.X) *
            PowerSeries.C K a) := by
    exact congrArg (PowerSeries.coeff K (k + 1))
      (matrixResolvent_mul_X_C_reassociate_scalar (K := K) M i j a)
  have hcoeffC :
      PowerSeries.coeff K (k + 1)
          ((matrixResolvent (K := K) M i j * PowerSeries.X) *
            PowerSeries.C K a) =
        PowerSeries.coeff K (k + 1)
          (matrixResolvent (K := K) M i j * PowerSeries.X) * a := by
    exact PowerSeries.coeff_mul_C
      (R := K) (k + 1) (matrixResolvent (K := K) M i j * PowerSeries.X) a
  have hshift :
      PowerSeries.coeff K (k + 1)
          (matrixResolvent (K := K) M i j * PowerSeries.X) * a =
        PowerSeries.coeff K k (matrixResolvent (K := K) M i j) * a := by
    exact congrArg (fun t : K => t * a)
      (coeff_matrixResolvent_mul_X (K := K) M i j k)
  have hmatrix :
      PowerSeries.coeff K k (matrixResolvent (K := K) M i j) * a =
        (M ^ k) i j * a := by
    exact congrArg (fun t : K => t * a) (coeff_matrixResolvent (K := K) M i j k)
  exact hreassociate.trans (hcoeffC.trans (hshift.trans hmatrix))

theorem coeff_matrixResolvent_mul_X_C (M : Matrix n n K) (i j : n) (k : ℕ) :
    PowerSeries.coeff K (k + 1)
        (matrixResolvent (K := K) M i j * (PowerSeries.X * PowerSeries.C K (M i j))) =
      (M ^ k) i j * M i j := by
  exact coeff_matrixResolvent_mul_X_C_scalar (K := K) M i j (M i j) k

theorem X_C_mul_matrixResolvent_reassociate_scalar (M : Matrix n n K) (i j : n) (a : K) :
    (PowerSeries.X * PowerSeries.C K a) *
        matrixResolvent (K := K) M i j =
      PowerSeries.C K a *
        (PowerSeries.X * matrixResolvent (K := K) M i j) := by
  have hassocLeft :
      (PowerSeries.X * PowerSeries.C K a) *
        matrixResolvent (K := K) M i j =
        PowerSeries.X *
          (PowerSeries.C K a * matrixResolvent (K := K) M i j) := by
    exact mul_assoc PowerSeries.X (PowerSeries.C K a) (matrixResolvent (K := K) M i j)
  have hcomm :
      PowerSeries.X *
          (PowerSeries.C K a * matrixResolvent (K := K) M i j) =
        PowerSeries.X *
          (matrixResolvent (K := K) M i j * PowerSeries.C K a) := by
    exact congrArg (fun t : K⟦X⟧ => PowerSeries.X * t)
      (mul_comm (PowerSeries.C K a) (matrixResolvent (K := K) M i j))
  have hassocRight :
      PowerSeries.X *
          (matrixResolvent (K := K) M i j * PowerSeries.C K a) =
        (PowerSeries.X * matrixResolvent (K := K) M i j) *
          PowerSeries.C K a := by
    exact (mul_assoc PowerSeries.X (matrixResolvent (K := K) M i j)
      (PowerSeries.C K a)).symm
  have hcommRight :
      (PowerSeries.X * matrixResolvent (K := K) M i j) *
          PowerSeries.C K a =
        PowerSeries.C K a *
          (PowerSeries.X * matrixResolvent (K := K) M i j) := by
    exact mul_comm ((PowerSeries.X * matrixResolvent (K := K) M i j))
      (PowerSeries.C K a)
  exact hassocLeft.trans (hcomm.trans (hassocRight.trans hcommRight))

theorem X_C_mul_matrixResolvent_reassociate (M : Matrix n n K) (i j : n) :
    (PowerSeries.X * PowerSeries.C K (M i j)) *
        matrixResolvent (K := K) M i j =
      PowerSeries.C K (M i j) *
        (PowerSeries.X * matrixResolvent (K := K) M i j) := by
  exact X_C_mul_matrixResolvent_reassociate_scalar (K := K) M i j (M i j)

theorem coeff_X_mul_matrixResolvent (M : Matrix n n K) (i j : n) (k : ℕ) :
    PowerSeries.coeff K (k + 1) (PowerSeries.X * matrixResolvent (K := K) M i j) =
      PowerSeries.coeff K k (matrixResolvent (K := K) M i j) := by
  have hpow :
      PowerSeries.coeff K (k + 1) (PowerSeries.X * matrixResolvent (K := K) M i j) =
        PowerSeries.coeff K (k + 1)
          (PowerSeries.X ^ 1 * matrixResolvent (K := K) M i j) := by
    exact congrArg (PowerSeries.coeff K (k + 1))
      (congrArg (fun t : K⟦X⟧ => t * matrixResolvent (K := K) M i j)
        (pow_one (PowerSeries.X : K⟦X⟧))).symm
  have hcoeff :
      PowerSeries.coeff K (k + 1)
          (PowerSeries.X ^ 1 * matrixResolvent (K := K) M i j) =
        PowerSeries.coeff K k (matrixResolvent (K := K) M i j) := by
    exact PowerSeries.coeff_X_pow_mul
      (p := matrixResolvent (K := K) M i j) (n := 1) (d := k)
  exact hpow.trans hcoeff

theorem coeff_X_C_mul_matrixResolvent_scalar (M : Matrix n n K) (i j : n) (a : K) (k : ℕ) :
    PowerSeries.coeff K (k + 1)
        ((PowerSeries.X * PowerSeries.C K a) *
          matrixResolvent (K := K) M i j) =
      a * (M ^ k) i j := by
  have hreassociate :
      PowerSeries.coeff K (k + 1)
        ((PowerSeries.X * PowerSeries.C K a) *
          matrixResolvent (K := K) M i j) =
        PowerSeries.coeff K (k + 1)
          (PowerSeries.C K a *
            (PowerSeries.X * matrixResolvent (K := K) M i j)) := by
    exact congrArg (PowerSeries.coeff K (k + 1))
      (X_C_mul_matrixResolvent_reassociate_scalar (K := K) M i j a)
  have hcoeffC :
      PowerSeries.coeff K (k + 1)
          (PowerSeries.C K a *
            (PowerSeries.X * matrixResolvent (K := K) M i j)) =
        a *
          PowerSeries.coeff K (k + 1)
            (PowerSeries.X * matrixResolvent (K := K) M i j) := by
    exact PowerSeries.coeff_C_mul
      (R := K) (k + 1) (PowerSeries.X * matrixResolvent (K := K) M i j) a
  have hshift :
      a * PowerSeries.coeff K (k + 1)
          (PowerSeries.X * matrixResolvent (K := K) M i j) =
        a * PowerSeries.coeff K k (matrixResolvent (K := K) M i j) := by
    exact congrArg (fun t : K => a * t)
      (coeff_X_mul_matrixResolvent (K := K) M i j k)
  have hmatrix :
      a * PowerSeries.coeff K k (matrixResolvent (K := K) M i j) =
        a * (M ^ k) i j := by
    exact congrArg (fun t : K => a * t) (coeff_matrixResolvent (K := K) M i j k)
  exact hreassociate.trans (hcoeffC.trans (hshift.trans hmatrix))

theorem coeff_X_C_mul_matrixResolvent (M : Matrix n n K) (i j : n) (k : ℕ) :
    PowerSeries.coeff K (k + 1)
        ((PowerSeries.X * PowerSeries.C K (M i j)) *
          matrixResolvent (K := K) M i j) =
      M i j * (M ^ k) i j := by
  exact coeff_X_C_mul_matrixResolvent_scalar (K := K) M i j (M i j) k

theorem coeff_matrixResolvent_mul_X_C_zero_scalar (M : Matrix n n K) (i j : n) (a : K) :
    PowerSeries.coeff K 0
        (matrixResolvent (K := K) M i j * (PowerSeries.X * PowerSeries.C K a)) = 0 := by
  have hreassociate :
      PowerSeries.coeff K 0
        (matrixResolvent (K := K) M i j * (PowerSeries.X * PowerSeries.C K a)) =
        PowerSeries.coeff K 0
          ((matrixResolvent (K := K) M i j * PowerSeries.X) * PowerSeries.C K a) := by
    exact congrArg (PowerSeries.coeff K 0)
      (matrixResolvent_mul_X_C_reassociate_scalar (K := K) M i j a)
  have hcoeffC :
      PowerSeries.coeff K 0
          ((matrixResolvent (K := K) M i j * PowerSeries.X) * PowerSeries.C K a) =
        PowerSeries.coeff K 0 (matrixResolvent (K := K) M i j * PowerSeries.X) * a := by
    exact PowerSeries.coeff_mul_C
      (R := K) 0 (matrixResolvent (K := K) M i j * PowerSeries.X) a
  have hzeroCoeff :
      PowerSeries.coeff K 0 (matrixResolvent (K := K) M i j * PowerSeries.X) * a =
        0 * a := by
    exact congrArg (fun t : K => t * a)
      (PowerSeries.coeff_zero_mul_X (matrixResolvent (K := K) M i j))
  have hzero : (0 : K) * a = 0 := by
    exact zero_mul a
  exact hreassociate.trans (hcoeffC.trans (hzeroCoeff.trans hzero))

theorem coeff_X_C_mul_matrixResolvent_zero_scalar (M : Matrix n n K) (i j : n) (a : K) :
    PowerSeries.coeff K 0
        ((PowerSeries.X * PowerSeries.C K a) * matrixResolvent (K := K) M i j) = 0 := by
  have hreassociate :
      PowerSeries.coeff K 0
        ((PowerSeries.X * PowerSeries.C K a) * matrixResolvent (K := K) M i j) =
        PowerSeries.coeff K 0
          (PowerSeries.C K a * (PowerSeries.X * matrixResolvent (K := K) M i j)) := by
    exact congrArg (PowerSeries.coeff K 0)
      (X_C_mul_matrixResolvent_reassociate_scalar (K := K) M i j a)
  have hcoeffC :
      PowerSeries.coeff K 0
          (PowerSeries.C K a * (PowerSeries.X * matrixResolvent (K := K) M i j)) =
        a * PowerSeries.coeff K 0 (PowerSeries.X * matrixResolvent (K := K) M i j) := by
    exact PowerSeries.coeff_C_mul
      (R := K) 0 (PowerSeries.X * matrixResolvent (K := K) M i j) a
  have hzeroCoeff :
      a * PowerSeries.coeff K 0 (PowerSeries.X * matrixResolvent (K := K) M i j) =
        a * 0 := by
    exact congrArg (fun t : K => a * t)
      (PowerSeries.coeff_zero_X_mul (matrixResolvent (K := K) M i j))
  have hzero : a * (0 : K) = 0 := by
    exact mul_zero a
  exact hreassociate.trans (hcoeffC.trans (hzeroCoeff.trans hzero))

theorem matrix_pow_zero_apply (M : Matrix n n K) (i j : n) :
    (M ^ 0) i j = if i = j then 1 else 0 := by
  exact (congrFun (congrFun (pow_zero M) i) j).trans
    (Matrix.one_apply : (1 : Matrix n n K) i j = if i = j then 1 else 0)

theorem coeff_zero_powerSeries (k : ℕ) :
    PowerSeries.coeff K k (0 : K⟦X⟧) = 0 := by
  exact map_zero (PowerSeries.coeff K k)

theorem coeff_one_powerSeries_succ (k : ℕ) :
    PowerSeries.coeff K (k + 1) (1 : K⟦X⟧) = 0 := by
  exact (PowerSeries.coeff_one (R := K) (k + 1)).trans
    (if_neg (Nat.succ_ne_zero k))

omit [Fintype n] in
theorem coeff_if_one_zero_succ (i j : n) (k : ℕ) :
    PowerSeries.coeff K (k + 1) (if i = j then 1 else 0 : K⟦X⟧) = 0 := by
  match (inferInstance : Decidable (i = j)) with
  | .isTrue hij =>
      exact ((congrArg (PowerSeries.coeff K (k + 1)) (if_pos hij)).trans
        (coeff_one_powerSeries_succ (K := K) k))
  | .isFalse hij =>
      exact ((congrArg (PowerSeries.coeff K (k + 1)) (if_neg hij)).trans
        (coeff_zero_powerSeries (K := K) (k + 1)))

theorem coeff_matrixResolvent_mul_indicator_right
    (M : Matrix n n K) (i r j : n) (k : ℕ) :
    PowerSeries.coeff K k
        (matrixResolvent (K := K) M i r * (if r = j then 1 else 0 : K⟦X⟧)) =
      if r = j then (M ^ k) i r else 0 := by
  match (inferInstance : Decidable (r = j)) with
  | .isTrue hrj =>
      exact
      (congrArg (PowerSeries.coeff K k)
        (congrArg (fun t : K⟦X⟧ => matrixResolvent (K := K) M i r * t)
          (if_pos hrj))).trans
        ((congrArg (PowerSeries.coeff K k)
          (mul_one (matrixResolvent (K := K) M i r))).trans
          ((coeff_matrixResolvent (K := K) M i r k).trans
            (if_pos hrj).symm))
  | .isFalse hrj =>
      exact
      (congrArg (PowerSeries.coeff K k)
        (congrArg (fun t : K⟦X⟧ => matrixResolvent (K := K) M i r * t)
          (if_neg hrj))).trans
        ((congrArg (PowerSeries.coeff K k)
          (mul_zero (matrixResolvent (K := K) M i r))).trans
          ((coeff_zero_powerSeries (K := K) k).trans
            (if_neg hrj).symm))

theorem coeff_indicator_left_mul_matrixResolvent
    (M : Matrix n n K) (i r j : n) (k : ℕ) :
    PowerSeries.coeff K k
        ((if i = r then 1 else 0 : K⟦X⟧) * matrixResolvent (K := K) M r j) =
      if i = r then (M ^ k) r j else 0 := by
  match (inferInstance : Decidable (i = r)) with
  | .isTrue hir =>
      exact
      (congrArg (PowerSeries.coeff K k)
        (congrArg (fun t : K⟦X⟧ => t * matrixResolvent (K := K) M r j)
          (if_pos hir))).trans
        ((congrArg (PowerSeries.coeff K k)
          (one_mul (matrixResolvent (K := K) M r j))).trans
          ((coeff_matrixResolvent (K := K) M r j k).trans
            (if_pos hir).symm))
  | .isFalse hir =>
      exact
      (congrArg (PowerSeries.coeff K k)
        (congrArg (fun t : K⟦X⟧ => t * matrixResolvent (K := K) M r j)
          (if_neg hir))).trans
        ((congrArg (PowerSeries.coeff K k)
          (zero_mul (matrixResolvent (K := K) M r j))).trans
          ((coeff_zero_powerSeries (K := K) k).trans
            (if_neg hir).symm))

theorem coeff_matrixResolvent_mul_oneSubXMatrix_succ_term
    (M : Matrix n n K) (i r j : n) (k : ℕ) :
    PowerSeries.coeff K (k + 1)
        (matrixResolvent (K := K) M i r *
          ((if r = j then 1 else 0 : K⟦X⟧) -
            PowerSeries.X * PowerSeries.C K (M r j))) =
      (if r = j then (M ^ (k + 1)) i r else 0) -
        (M ^ k) i r * M r j := by
  have hmul :
      PowerSeries.coeff K (k + 1)
        (matrixResolvent (K := K) M i r *
          ((if r = j then 1 else 0 : K⟦X⟧) -
            PowerSeries.X * PowerSeries.C K (M r j))) =
        PowerSeries.coeff K (k + 1)
          (matrixResolvent (K := K) M i r * (if r = j then 1 else 0 : K⟦X⟧) -
            matrixResolvent (K := K) M i r * (PowerSeries.X * PowerSeries.C K (M r j))) := by
    exact congrArg (PowerSeries.coeff K (k + 1))
      (mul_sub (matrixResolvent (K := K) M i r)
        (if r = j then 1 else 0 : K⟦X⟧)
        (PowerSeries.X * PowerSeries.C K (M r j)))
  have hcoeff :
      PowerSeries.coeff K (k + 1)
          (matrixResolvent (K := K) M i r * (if r = j then 1 else 0 : K⟦X⟧) -
            matrixResolvent (K := K) M i r * (PowerSeries.X * PowerSeries.C K (M r j))) =
        PowerSeries.coeff K (k + 1)
          (matrixResolvent (K := K) M i r * (if r = j then 1 else 0 : K⟦X⟧)) -
          PowerSeries.coeff K (k + 1)
            (matrixResolvent (K := K) M i r * (PowerSeries.X * PowerSeries.C K (M r j))) := by
    exact map_sub (PowerSeries.coeff K (k + 1))
      (matrixResolvent (K := K) M i r * (if r = j then 1 else 0 : K⟦X⟧))
      (matrixResolvent (K := K) M i r * (PowerSeries.X * PowerSeries.C K (M r j)))
  have hterms :
      PowerSeries.coeff K (k + 1)
          (matrixResolvent (K := K) M i r * (if r = j then 1 else 0 : K⟦X⟧)) -
          PowerSeries.coeff K (k + 1)
            (matrixResolvent (K := K) M i r * (PowerSeries.X * PowerSeries.C K (M r j))) =
        (if r = j then (M ^ (k + 1)) i r else 0) -
          (M ^ k) i r * M r j := by
    exact congrArg₂ Sub.sub
      (coeff_matrixResolvent_mul_indicator_right (K := K) M i r j (k + 1))
      (coeff_matrixResolvent_mul_X_C_scalar (K := K) M i r (M r j) k)
  exact hmul.trans (hcoeff.trans hterms)

theorem coeff_oneSubXMatrix_mul_matrixResolvent_succ_term
    (M : Matrix n n K) (i r j : n) (k : ℕ) :
    PowerSeries.coeff K (k + 1)
        (((if i = r then 1 else 0 : K⟦X⟧) -
            PowerSeries.X * PowerSeries.C K (M i r)) *
          matrixResolvent (K := K) M r j) =
      (if i = r then (M ^ (k + 1)) r j else 0) -
        M i r * (M ^ k) r j := by
  have hmul :
      PowerSeries.coeff K (k + 1)
        (((if i = r then 1 else 0 : K⟦X⟧) -
            PowerSeries.X * PowerSeries.C K (M i r)) *
          matrixResolvent (K := K) M r j) =
        PowerSeries.coeff K (k + 1)
          ((if i = r then 1 else 0 : K⟦X⟧) * matrixResolvent (K := K) M r j -
            (PowerSeries.X * PowerSeries.C K (M i r)) * matrixResolvent (K := K) M r j) := by
    exact congrArg (PowerSeries.coeff K (k + 1))
      (sub_mul
        (if i = r then 1 else 0 : K⟦X⟧)
        (PowerSeries.X * PowerSeries.C K (M i r))
        (matrixResolvent (K := K) M r j))
  have hcoeff :
      PowerSeries.coeff K (k + 1)
          ((if i = r then 1 else 0 : K⟦X⟧) * matrixResolvent (K := K) M r j -
            (PowerSeries.X * PowerSeries.C K (M i r)) * matrixResolvent (K := K) M r j) =
        PowerSeries.coeff K (k + 1)
          ((if i = r then 1 else 0 : K⟦X⟧) * matrixResolvent (K := K) M r j) -
          PowerSeries.coeff K (k + 1)
            ((PowerSeries.X * PowerSeries.C K (M i r)) * matrixResolvent (K := K) M r j) := by
    exact map_sub (PowerSeries.coeff K (k + 1))
      ((if i = r then 1 else 0 : K⟦X⟧) * matrixResolvent (K := K) M r j)
      ((PowerSeries.X * PowerSeries.C K (M i r)) * matrixResolvent (K := K) M r j)
  have hterms :
      PowerSeries.coeff K (k + 1)
          ((if i = r then 1 else 0 : K⟦X⟧) * matrixResolvent (K := K) M r j) -
          PowerSeries.coeff K (k + 1)
            ((PowerSeries.X * PowerSeries.C K (M i r)) * matrixResolvent (K := K) M r j) =
        (if i = r then (M ^ (k + 1)) r j else 0) -
          M i r * (M ^ k) r j := by
    exact congrArg₂ Sub.sub
      (coeff_indicator_left_mul_matrixResolvent (K := K) M i r j (k + 1))
      (coeff_X_C_mul_matrixResolvent_scalar (K := K) M r j (M i r) k)
  exact hmul.trans (hcoeff.trans hterms)

theorem sum_indicator_right_matrix_pow (M : Matrix n n K) (i j : n) (k : ℕ) :
    (∑ r : n, if r = j then (M ^ (k + 1)) i r else 0) =
      (M ^ (k + 1)) i j := by
  exact (Fintype.sum_eq_single j
    (fun r hrj => if_neg hrj)).trans
    (if_pos rfl)

theorem sum_indicator_left_matrix_pow (M : Matrix n n K) (i j : n) (k : ℕ) :
    (∑ r : n, if i = r then (M ^ (k + 1)) r j else 0) =
      (M ^ (k + 1)) i j := by
  exact (Fintype.sum_eq_single i
    (fun r hir => if_neg hir.symm)).trans
    (if_pos rfl)

theorem sum_matrix_pow_mul_entry_right (M : Matrix n n K) (i j : n) (k : ℕ) :
    (∑ r : n, (M ^ k) i r * M r j) = (M ^ (k + 1)) i j := by
  exact ((congrFun (congrFun (pow_succ M k) i) j).trans
    (Matrix.mul_apply :
      (M ^ k * M) i j = ∑ r : n, (M ^ k) i r * M r j)).symm

theorem sum_entry_mul_matrix_pow_left (M : Matrix n n K) (i j : n) (k : ℕ) :
    (∑ r : n, M i r * (M ^ k) r j) = (M ^ (k + 1)) i j := by
  exact ((congrFun (congrFun (pow_succ' M k) i) j).trans
    (Matrix.mul_apply :
      (M * M ^ k) i j = ∑ r : n, M i r * (M ^ k) r j)).symm

theorem sum_matrixResolvent_mul_oneSubXMatrix_succ_terms
    (M : Matrix n n K) (i j : n) (k : ℕ) :
    (∑ r : n,
        ((if r = j then (M ^ (k + 1)) i r else 0) -
          (M ^ k) i r * M r j)) = 0 := by
  have hsplit :
      (∑ r : n,
        ((if r = j then (M ^ (k + 1)) i r else 0) -
          (M ^ k) i r * M r j)) =
        (∑ r : n, if r = j then (M ^ (k + 1)) i r else 0) -
          (∑ r : n, (M ^ k) i r * M r j) := by
    exact Finset.sum_sub_distrib
  have heval :
      (∑ r : n, if r = j then (M ^ (k + 1)) i r else 0) -
          (∑ r : n, (M ^ k) i r * M r j) =
        (M ^ (k + 1)) i j - (M ^ (k + 1)) i j := by
    exact congrArg₂ Sub.sub
      (sum_indicator_right_matrix_pow (K := K) M i j k)
      (sum_matrix_pow_mul_entry_right (K := K) M i j k)
  have hzero : (M ^ (k + 1)) i j - (M ^ (k + 1)) i j = 0 := by
    exact sub_self ((M ^ (k + 1)) i j)
  exact hsplit.trans (heval.trans hzero)

theorem sum_oneSubXMatrix_mul_matrixResolvent_succ_terms
    (M : Matrix n n K) (i j : n) (k : ℕ) :
    (∑ r : n,
        ((if i = r then (M ^ (k + 1)) r j else 0) -
          M i r * (M ^ k) r j)) = 0 := by
  have hsplit :
      (∑ r : n,
        ((if i = r then (M ^ (k + 1)) r j else 0) -
          M i r * (M ^ k) r j)) =
        (∑ r : n, if i = r then (M ^ (k + 1)) r j else 0) -
          (∑ r : n, M i r * (M ^ k) r j) := by
    exact Finset.sum_sub_distrib
  have heval :
      (∑ r : n, if i = r then (M ^ (k + 1)) r j else 0) -
          (∑ r : n, M i r * (M ^ k) r j) =
        (M ^ (k + 1)) i j - (M ^ (k + 1)) i j := by
    exact congrArg₂ Sub.sub
      (sum_indicator_left_matrix_pow (K := K) M i j k)
      (sum_entry_mul_matrix_pow_left (K := K) M i j k)
  have hzero : (M ^ (k + 1)) i j - (M ^ (k + 1)) i j = 0 := by
    exact sub_self ((M ^ (k + 1)) i j)
  exact hsplit.trans (heval.trans hzero)

theorem coeff_matrixResolvent_mul_oneSubXMatrix_zero_term
    (M : Matrix n n K) (i r j : n) :
    PowerSeries.coeff K 0
        (matrixResolvent (K := K) M i r *
          ((if r = j then 1 else 0 : K⟦X⟧) -
            PowerSeries.X * PowerSeries.C K (M r j))) =
      if r = j then (M ^ 0) i r else 0 := by
  have hmul :
      PowerSeries.coeff K 0
        (matrixResolvent (K := K) M i r *
          ((if r = j then 1 else 0 : K⟦X⟧) -
            PowerSeries.X * PowerSeries.C K (M r j))) =
        PowerSeries.coeff K 0
          (matrixResolvent (K := K) M i r * (if r = j then 1 else 0 : K⟦X⟧) -
            matrixResolvent (K := K) M i r * (PowerSeries.X * PowerSeries.C K (M r j))) := by
    exact congrArg (PowerSeries.coeff K 0)
      (mul_sub (matrixResolvent (K := K) M i r)
        (if r = j then 1 else 0 : K⟦X⟧)
        (PowerSeries.X * PowerSeries.C K (M r j)))
  have hcoeff :
      PowerSeries.coeff K 0
          (matrixResolvent (K := K) M i r * (if r = j then 1 else 0 : K⟦X⟧) -
            matrixResolvent (K := K) M i r * (PowerSeries.X * PowerSeries.C K (M r j))) =
        PowerSeries.coeff K 0
          (matrixResolvent (K := K) M i r * (if r = j then 1 else 0 : K⟦X⟧)) -
          PowerSeries.coeff K 0
            (matrixResolvent (K := K) M i r * (PowerSeries.X * PowerSeries.C K (M r j))) := by
    exact map_sub (PowerSeries.coeff K 0)
      (matrixResolvent (K := K) M i r * (if r = j then 1 else 0 : K⟦X⟧))
      (matrixResolvent (K := K) M i r * (PowerSeries.X * PowerSeries.C K (M r j)))
  have hterms :
      PowerSeries.coeff K 0
          (matrixResolvent (K := K) M i r * (if r = j then 1 else 0 : K⟦X⟧)) -
          PowerSeries.coeff K 0
            (matrixResolvent (K := K) M i r * (PowerSeries.X * PowerSeries.C K (M r j))) =
        (if r = j then (M ^ 0) i r else 0) - 0 := by
    exact congrArg₂ Sub.sub
      (coeff_matrixResolvent_mul_indicator_right (K := K) M i r j 0)
      (coeff_matrixResolvent_mul_X_C_zero_scalar (K := K) M i r (M r j))
  have hzero :
      (if r = j then (M ^ 0) i r else 0) - 0 =
        if r = j then (M ^ 0) i r else 0 := by
    exact sub_zero (if r = j then (M ^ 0) i r else 0)
  exact hmul.trans (hcoeff.trans (hterms.trans hzero))

theorem coeff_oneSubXMatrix_mul_matrixResolvent_zero_term
    (M : Matrix n n K) (i r j : n) :
    PowerSeries.coeff K 0
        (((if i = r then 1 else 0 : K⟦X⟧) -
            PowerSeries.X * PowerSeries.C K (M i r)) *
          matrixResolvent (K := K) M r j) =
      if i = r then (M ^ 0) r j else 0 := by
  have hmul :
      PowerSeries.coeff K 0
        (((if i = r then 1 else 0 : K⟦X⟧) -
            PowerSeries.X * PowerSeries.C K (M i r)) *
          matrixResolvent (K := K) M r j) =
        PowerSeries.coeff K 0
          ((if i = r then 1 else 0 : K⟦X⟧) * matrixResolvent (K := K) M r j -
            (PowerSeries.X * PowerSeries.C K (M i r)) * matrixResolvent (K := K) M r j) := by
    exact congrArg (PowerSeries.coeff K 0)
      (sub_mul
        (if i = r then 1 else 0 : K⟦X⟧)
        (PowerSeries.X * PowerSeries.C K (M i r))
        (matrixResolvent (K := K) M r j))
  have hcoeff :
      PowerSeries.coeff K 0
          ((if i = r then 1 else 0 : K⟦X⟧) * matrixResolvent (K := K) M r j -
            (PowerSeries.X * PowerSeries.C K (M i r)) * matrixResolvent (K := K) M r j) =
        PowerSeries.coeff K 0
          ((if i = r then 1 else 0 : K⟦X⟧) * matrixResolvent (K := K) M r j) -
          PowerSeries.coeff K 0
            ((PowerSeries.X * PowerSeries.C K (M i r)) * matrixResolvent (K := K) M r j) := by
    exact map_sub (PowerSeries.coeff K 0)
      ((if i = r then 1 else 0 : K⟦X⟧) * matrixResolvent (K := K) M r j)
      ((PowerSeries.X * PowerSeries.C K (M i r)) * matrixResolvent (K := K) M r j)
  have hterms :
      PowerSeries.coeff K 0
          ((if i = r then 1 else 0 : K⟦X⟧) * matrixResolvent (K := K) M r j) -
          PowerSeries.coeff K 0
            ((PowerSeries.X * PowerSeries.C K (M i r)) * matrixResolvent (K := K) M r j) =
        (if i = r then (M ^ 0) r j else 0) - 0 := by
    exact congrArg₂ Sub.sub
      (coeff_indicator_left_mul_matrixResolvent (K := K) M i r j 0)
      (coeff_X_C_mul_matrixResolvent_zero_scalar (K := K) M r j (M i r))
  have hzero :
      (if i = r then (M ^ 0) r j else 0) - 0 =
        if i = r then (M ^ 0) r j else 0 := by
    exact sub_zero (if i = r then (M ^ 0) r j else 0)
  exact hmul.trans (hcoeff.trans (hterms.trans hzero))

theorem sum_matrixResolvent_mul_oneSubXMatrix_zero_terms
    (M : Matrix n n K) (i j : n) :
    (∑ r : n, if r = j then (M ^ 0) i r else 0) =
      if i = j then 1 else 0 := by
  exact ((Fintype.sum_eq_single j
    (fun r hrj => if_neg hrj)).trans
    (if_pos rfl)).trans
    (matrix_pow_zero_apply (K := K) M i j)

theorem sum_oneSubXMatrix_mul_matrixResolvent_zero_terms
    (M : Matrix n n K) (i j : n) :
    (∑ r : n, if i = r then (M ^ 0) r j else 0) =
      if i = j then 1 else 0 := by
  exact ((Fintype.sum_eq_single i
    (fun r hir => if_neg hir.symm)).trans
    (if_pos rfl)).trans
    (matrix_pow_zero_apply (K := K) M i j)

omit [Fintype n] in
theorem coeff_matrix_one_apply_zero (i j : n) :
    PowerSeries.coeff K 0 ((1 : Matrix n n K⟦X⟧) i j) =
      if i = j then 1 else 0 := by
  match (inferInstance : Decidable (i = j)) with
  | .isTrue hij =>
      exact ((congrArg (PowerSeries.coeff K 0)
      ((Matrix.one_apply : (1 : Matrix n n K⟦X⟧) i j = if i = j then 1 else 0).trans
        (if_pos hij))).trans
      ((PowerSeries.coeff_zero_one (R := K)).trans (if_pos hij).symm))
  | .isFalse hij =>
      exact ((congrArg (PowerSeries.coeff K 0)
      ((Matrix.one_apply : (1 : Matrix n n K⟦X⟧) i j = if i = j then 1 else 0).trans
        (if_neg hij))).trans
      ((coeff_zero_powerSeries (K := K) 0).trans (if_neg hij).symm))

omit [Fintype n] in
theorem coeff_matrix_one_apply_succ (i j : n) (k : ℕ) :
    PowerSeries.coeff K (k + 1) ((1 : Matrix n n K⟦X⟧) i j) = 0 := by
  exact (congrArg (PowerSeries.coeff K (k + 1))
    (Matrix.one_apply : (1 : Matrix n n K⟦X⟧) i j = if i = j then 1 else 0)).trans
    (coeff_if_one_zero_succ (K := K) i j k)

theorem coeff_matrixResolvent_mul_oneSubXMatrix_zero_expanded
    (M : Matrix n n K) (i j : n) :
    PowerSeries.coeff K 0
        ((matrixResolvent (K := K) M * oneSubXMatrix (K := K) M) i j) =
      ∑ r : n, if r = j then (M ^ 0) i r else 0 := by
  have hmul :
      PowerSeries.coeff K 0
        ((matrixResolvent (K := K) M * oneSubXMatrix (K := K) M) i j) =
        PowerSeries.coeff K 0
          (∑ r : n, matrixResolvent (K := K) M i r * oneSubXMatrix (K := K) M r j) := by
    exact congrArg (PowerSeries.coeff K 0)
        (Matrix.mul_apply :
          (matrixResolvent (K := K) M * oneSubXMatrix (K := K) M) i j =
            ∑ r : n, matrixResolvent (K := K) M i r * oneSubXMatrix (K := K) M r j)
  have hentry :
      PowerSeries.coeff K 0
          (∑ r : n, matrixResolvent (K := K) M i r * oneSubXMatrix (K := K) M r j) =
        PowerSeries.coeff K 0
          (∑ r : n,
            matrixResolvent (K := K) M i r *
              ((if r = j then 1 else 0 : K⟦X⟧) -
                PowerSeries.X * PowerSeries.C K (M r j))) := by
    exact congrArg (PowerSeries.coeff K 0)
      (Finset.sum_congr rfl
        (fun r _ => congrArg
          (fun t : K⟦X⟧ => matrixResolvent (K := K) M i r * t)
          (oneSubXMatrix_apply (K := K) M r j)))
  have hcoeff :
      PowerSeries.coeff K 0
          (∑ r : n,
            matrixResolvent (K := K) M i r *
              ((if r = j then 1 else 0 : K⟦X⟧) -
                PowerSeries.X * PowerSeries.C K (M r j))) =
        ∑ r : n,
          PowerSeries.coeff K 0
            (matrixResolvent (K := K) M i r *
              ((if r = j then 1 else 0 : K⟦X⟧) -
                PowerSeries.X * PowerSeries.C K (M r j))) := by
    exact map_sum (PowerSeries.coeff K 0)
      (fun r => matrixResolvent (K := K) M i r *
        ((if r = j then 1 else 0 : K⟦X⟧) -
          PowerSeries.X * PowerSeries.C K (M r j))) Finset.univ
  have hterm :
      (∑ r : n,
          PowerSeries.coeff K 0
            (matrixResolvent (K := K) M i r *
              ((if r = j then 1 else 0 : K⟦X⟧) -
                PowerSeries.X * PowerSeries.C K (M r j)))) =
        ∑ r : n, if r = j then (M ^ 0) i r else 0 := by
    exact Finset.sum_congr rfl
      (fun r _ => coeff_matrixResolvent_mul_oneSubXMatrix_zero_term (K := K) M i r j)
  exact hmul.trans (hentry.trans (hcoeff.trans hterm))

theorem coeff_matrixResolvent_mul_oneSubXMatrix_zero
    (M : Matrix n n K) (i j : n) :
    PowerSeries.coeff K 0
        ((matrixResolvent (K := K) M * oneSubXMatrix (K := K) M) i j) =
      PowerSeries.coeff K 0 ((1 : Matrix n n K⟦X⟧) i j) := by
  have hexpand :
      PowerSeries.coeff K 0
        ((matrixResolvent (K := K) M * oneSubXMatrix (K := K) M) i j) =
        ∑ r : n, if r = j then (M ^ 0) i r else 0 := by
    exact coeff_matrixResolvent_mul_oneSubXMatrix_zero_expanded (K := K) M i j
  have hsum :
      (∑ r : n, if r = j then (M ^ 0) i r else 0) =
        if i = j then 1 else 0 := by
    exact sum_matrixResolvent_mul_oneSubXMatrix_zero_terms (K := K) M i j
  have hone :
      (if i = j then 1 else 0) =
        PowerSeries.coeff K 0 ((1 : Matrix n n K⟦X⟧) i j) := by
    exact (coeff_matrix_one_apply_zero (K := K) i j).symm
  exact hexpand.trans (hsum.trans hone)

theorem coeff_oneSubXMatrix_mul_matrixResolvent_zero_expanded
    (M : Matrix n n K) (i j : n) :
    PowerSeries.coeff K 0
        ((oneSubXMatrix (K := K) M * matrixResolvent (K := K) M) i j) =
      ∑ r : n, if i = r then (M ^ 0) r j else 0 := by
  have hmul :
      PowerSeries.coeff K 0
        ((oneSubXMatrix (K := K) M * matrixResolvent (K := K) M) i j) =
        PowerSeries.coeff K 0
          (∑ r : n, oneSubXMatrix (K := K) M i r * matrixResolvent (K := K) M r j) := by
    exact congrArg (PowerSeries.coeff K 0)
        (Matrix.mul_apply :
          (oneSubXMatrix (K := K) M * matrixResolvent (K := K) M) i j =
            ∑ r : n, oneSubXMatrix (K := K) M i r * matrixResolvent (K := K) M r j)
  have hentry :
      PowerSeries.coeff K 0
          (∑ r : n, oneSubXMatrix (K := K) M i r * matrixResolvent (K := K) M r j) =
        PowerSeries.coeff K 0
          (∑ r : n,
            ((if i = r then 1 else 0 : K⟦X⟧) -
              PowerSeries.X * PowerSeries.C K (M i r)) *
              matrixResolvent (K := K) M r j) := by
    exact congrArg (PowerSeries.coeff K 0)
      (Finset.sum_congr rfl
        (fun r _ => congrArg
          (fun t : K⟦X⟧ => t * matrixResolvent (K := K) M r j)
          (oneSubXMatrix_apply (K := K) M i r)))
  have hcoeff :
      PowerSeries.coeff K 0
          (∑ r : n,
            ((if i = r then 1 else 0 : K⟦X⟧) -
              PowerSeries.X * PowerSeries.C K (M i r)) *
              matrixResolvent (K := K) M r j) =
        ∑ r : n,
          PowerSeries.coeff K 0
            (((if i = r then 1 else 0 : K⟦X⟧) -
              PowerSeries.X * PowerSeries.C K (M i r)) *
              matrixResolvent (K := K) M r j) := by
    exact map_sum (PowerSeries.coeff K 0)
      (fun r => ((if i = r then 1 else 0 : K⟦X⟧) -
        PowerSeries.X * PowerSeries.C K (M i r)) *
        matrixResolvent (K := K) M r j) Finset.univ
  have hterm :
      (∑ r : n,
          PowerSeries.coeff K 0
            (((if i = r then 1 else 0 : K⟦X⟧) -
              PowerSeries.X * PowerSeries.C K (M i r)) *
              matrixResolvent (K := K) M r j)) =
        ∑ r : n, if i = r then (M ^ 0) r j else 0 := by
    exact Finset.sum_congr rfl
      (fun r _ => coeff_oneSubXMatrix_mul_matrixResolvent_zero_term (K := K) M i r j)
  exact hmul.trans (hentry.trans (hcoeff.trans hterm))

theorem coeff_oneSubXMatrix_mul_matrixResolvent_zero
    (M : Matrix n n K) (i j : n) :
    PowerSeries.coeff K 0
        ((oneSubXMatrix (K := K) M * matrixResolvent (K := K) M) i j) =
      PowerSeries.coeff K 0 ((1 : Matrix n n K⟦X⟧) i j) := by
  have hexpand :
      PowerSeries.coeff K 0
        ((oneSubXMatrix (K := K) M * matrixResolvent (K := K) M) i j) =
        ∑ r : n, if i = r then (M ^ 0) r j else 0 := by
    exact coeff_oneSubXMatrix_mul_matrixResolvent_zero_expanded (K := K) M i j
  have hsum :
      (∑ r : n, if i = r then (M ^ 0) r j else 0) =
        if i = j then 1 else 0 := by
    exact sum_oneSubXMatrix_mul_matrixResolvent_zero_terms (K := K) M i j
  have hone :
      (if i = j then 1 else 0) =
        PowerSeries.coeff K 0 ((1 : Matrix n n K⟦X⟧) i j) := by
    exact (coeff_matrix_one_apply_zero (K := K) i j).symm
  exact hexpand.trans (hsum.trans hone)

theorem coeff_matrixResolvent_mul_oneSubXMatrix_succ_expanded
    (M : Matrix n n K) (i j : n) (k : ℕ) :
    PowerSeries.coeff K (k + 1)
        ((matrixResolvent (K := K) M * oneSubXMatrix (K := K) M) i j) =
      ∑ r : n,
          ((if r = j then (M ^ (k + 1)) i r else 0) -
            (M ^ k) i r * M r j) := by
  have hmul :
      PowerSeries.coeff K (k + 1)
        ((matrixResolvent (K := K) M * oneSubXMatrix (K := K) M) i j) =
        PowerSeries.coeff K (k + 1)
          (∑ r : n, matrixResolvent (K := K) M i r * oneSubXMatrix (K := K) M r j) := by
    exact congrArg (PowerSeries.coeff K (k + 1))
        (Matrix.mul_apply :
          (matrixResolvent (K := K) M * oneSubXMatrix (K := K) M) i j =
            ∑ r : n, matrixResolvent (K := K) M i r * oneSubXMatrix (K := K) M r j)
  have hentry :
      PowerSeries.coeff K (k + 1)
          (∑ r : n, matrixResolvent (K := K) M i r * oneSubXMatrix (K := K) M r j) =
        PowerSeries.coeff K (k + 1)
          (∑ r : n,
            matrixResolvent (K := K) M i r *
              ((if r = j then 1 else 0 : K⟦X⟧) -
                PowerSeries.X * PowerSeries.C K (M r j))) := by
    exact congrArg (PowerSeries.coeff K (k + 1))
      (Finset.sum_congr rfl
        (fun r _ => congrArg
          (fun t : K⟦X⟧ => matrixResolvent (K := K) M i r * t)
          (oneSubXMatrix_apply (K := K) M r j)))
  have hcoeff :
      PowerSeries.coeff K (k + 1)
          (∑ r : n,
            matrixResolvent (K := K) M i r *
              ((if r = j then 1 else 0 : K⟦X⟧) -
                PowerSeries.X * PowerSeries.C K (M r j))) =
        ∑ r : n,
          PowerSeries.coeff K (k + 1)
            (matrixResolvent (K := K) M i r *
              ((if r = j then 1 else 0 : K⟦X⟧) -
                PowerSeries.X * PowerSeries.C K (M r j))) := by
    exact map_sum (PowerSeries.coeff K (k + 1))
      (fun r => matrixResolvent (K := K) M i r *
        ((if r = j then 1 else 0 : K⟦X⟧) -
          PowerSeries.X * PowerSeries.C K (M r j))) Finset.univ
  have hterm :
      (∑ r : n,
          PowerSeries.coeff K (k + 1)
            (matrixResolvent (K := K) M i r *
              ((if r = j then 1 else 0 : K⟦X⟧) -
                PowerSeries.X * PowerSeries.C K (M r j)))) =
        ∑ r : n,
          ((if r = j then (M ^ (k + 1)) i r else 0) -
            (M ^ k) i r * M r j) := by
    exact Finset.sum_congr rfl
      (fun r _ => coeff_matrixResolvent_mul_oneSubXMatrix_succ_term (K := K) M i r j k)
  exact hmul.trans (hentry.trans (hcoeff.trans hterm))

theorem coeff_matrixResolvent_mul_oneSubXMatrix_succ
    (M : Matrix n n K) (i j : n) (k : ℕ) :
    PowerSeries.coeff K (k + 1)
        ((matrixResolvent (K := K) M * oneSubXMatrix (K := K) M) i j) =
      PowerSeries.coeff K (k + 1) ((1 : Matrix n n K⟦X⟧) i j) := by
  have hexpand :
      PowerSeries.coeff K (k + 1)
        ((matrixResolvent (K := K) M * oneSubXMatrix (K := K) M) i j) =
        ∑ r : n,
          ((if r = j then (M ^ (k + 1)) i r else 0) -
            (M ^ k) i r * M r j) := by
    exact coeff_matrixResolvent_mul_oneSubXMatrix_succ_expanded (K := K) M i j k
  have hsum :
      (∑ r : n,
          ((if r = j then (M ^ (k + 1)) i r else 0) -
            (M ^ k) i r * M r j)) = 0 := by
    exact sum_matrixResolvent_mul_oneSubXMatrix_succ_terms (K := K) M i j k
  have hone :
      0 = PowerSeries.coeff K (k + 1) ((1 : Matrix n n K⟦X⟧) i j) := by
    exact (coeff_matrix_one_apply_succ (K := K) i j k).symm
  exact hexpand.trans (hsum.trans hone)

theorem coeff_oneSubXMatrix_mul_matrixResolvent_succ_expanded
    (M : Matrix n n K) (i j : n) (k : ℕ) :
    PowerSeries.coeff K (k + 1)
        ((oneSubXMatrix (K := K) M * matrixResolvent (K := K) M) i j) =
      ∑ r : n,
          ((if i = r then (M ^ (k + 1)) r j else 0) -
            M i r * (M ^ k) r j) := by
  have hmul :
      PowerSeries.coeff K (k + 1)
        ((oneSubXMatrix (K := K) M * matrixResolvent (K := K) M) i j) =
        PowerSeries.coeff K (k + 1)
          (∑ r : n, oneSubXMatrix (K := K) M i r * matrixResolvent (K := K) M r j) := by
    exact congrArg (PowerSeries.coeff K (k + 1))
        (Matrix.mul_apply :
          (oneSubXMatrix (K := K) M * matrixResolvent (K := K) M) i j =
            ∑ r : n, oneSubXMatrix (K := K) M i r * matrixResolvent (K := K) M r j)
  have hentry :
      PowerSeries.coeff K (k + 1)
          (∑ r : n, oneSubXMatrix (K := K) M i r * matrixResolvent (K := K) M r j) =
        PowerSeries.coeff K (k + 1)
          (∑ r : n,
            ((if i = r then 1 else 0 : K⟦X⟧) -
              PowerSeries.X * PowerSeries.C K (M i r)) *
              matrixResolvent (K := K) M r j) := by
    exact congrArg (PowerSeries.coeff K (k + 1))
      (Finset.sum_congr rfl
        (fun r _ => congrArg
          (fun t : K⟦X⟧ => t * matrixResolvent (K := K) M r j)
          (oneSubXMatrix_apply (K := K) M i r)))
  have hcoeff :
      PowerSeries.coeff K (k + 1)
          (∑ r : n,
            ((if i = r then 1 else 0 : K⟦X⟧) -
              PowerSeries.X * PowerSeries.C K (M i r)) *
              matrixResolvent (K := K) M r j) =
        ∑ r : n,
          PowerSeries.coeff K (k + 1)
            (((if i = r then 1 else 0 : K⟦X⟧) -
              PowerSeries.X * PowerSeries.C K (M i r)) *
              matrixResolvent (K := K) M r j) := by
    exact map_sum (PowerSeries.coeff K (k + 1))
      (fun r => ((if i = r then 1 else 0 : K⟦X⟧) -
        PowerSeries.X * PowerSeries.C K (M i r)) *
        matrixResolvent (K := K) M r j) Finset.univ
  have hterm :
      (∑ r : n,
          PowerSeries.coeff K (k + 1)
            (((if i = r then 1 else 0 : K⟦X⟧) -
              PowerSeries.X * PowerSeries.C K (M i r)) *
              matrixResolvent (K := K) M r j)) =
        ∑ r : n,
          ((if i = r then (M ^ (k + 1)) r j else 0) -
            M i r * (M ^ k) r j) := by
    exact Finset.sum_congr rfl
      (fun r _ => coeff_oneSubXMatrix_mul_matrixResolvent_succ_term (K := K) M i r j k)
  exact hmul.trans (hentry.trans (hcoeff.trans hterm))

theorem coeff_oneSubXMatrix_mul_matrixResolvent_succ
    (M : Matrix n n K) (i j : n) (k : ℕ) :
    PowerSeries.coeff K (k + 1)
        ((oneSubXMatrix (K := K) M * matrixResolvent (K := K) M) i j) =
      PowerSeries.coeff K (k + 1) ((1 : Matrix n n K⟦X⟧) i j) := by
  have hexpand :
      PowerSeries.coeff K (k + 1)
        ((oneSubXMatrix (K := K) M * matrixResolvent (K := K) M) i j) =
        ∑ r : n,
          ((if i = r then (M ^ (k + 1)) r j else 0) -
            M i r * (M ^ k) r j) := by
    exact coeff_oneSubXMatrix_mul_matrixResolvent_succ_expanded (K := K) M i j k
  have hsum :
      (∑ r : n,
          ((if i = r then (M ^ (k + 1)) r j else 0) -
            M i r * (M ^ k) r j)) = 0 := by
    exact sum_oneSubXMatrix_mul_matrixResolvent_succ_terms (K := K) M i j k
  have hone :
      0 = PowerSeries.coeff K (k + 1) ((1 : Matrix n n K⟦X⟧) i j) := by
    exact (coeff_matrix_one_apply_succ (K := K) i j k).symm
  exact hexpand.trans (hsum.trans hone)

theorem coeff_matrixResolvent_mul_oneSubXMatrix
    (M : Matrix n n K) (i j : n) (k : ℕ) :
    PowerSeries.coeff K k
        ((matrixResolvent (K := K) M * oneSubXMatrix (K := K) M) i j) =
      PowerSeries.coeff K k ((1 : Matrix n n K⟦X⟧) i j) := by
  match k with
  | 0 =>
      exact coeff_matrixResolvent_mul_oneSubXMatrix_zero (K := K) M i j
  | k + 1 =>
      exact coeff_matrixResolvent_mul_oneSubXMatrix_succ (K := K) M i j k

theorem coeff_oneSubXMatrix_mul_matrixResolvent
    (M : Matrix n n K) (i j : n) (k : ℕ) :
    PowerSeries.coeff K k
        ((oneSubXMatrix (K := K) M * matrixResolvent (K := K) M) i j) =
      PowerSeries.coeff K k ((1 : Matrix n n K⟦X⟧) i j) := by
  match k with
  | 0 =>
      exact coeff_oneSubXMatrix_mul_matrixResolvent_zero (K := K) M i j
  | k + 1 =>
      exact coeff_oneSubXMatrix_mul_matrixResolvent_succ (K := K) M i j k

theorem matrixResolvent_mul_oneSubXMatrix_entry
    (M : Matrix n n K) (i j : n) :
    (matrixResolvent (K := K) M * oneSubXMatrix (K := K) M) i j =
      (1 : Matrix n n K⟦X⟧) i j := by
  exact PowerSeries.ext
    (fun k => coeff_matrixResolvent_mul_oneSubXMatrix (K := K) M i j k)

theorem oneSubXMatrix_mul_matrixResolvent_entry
    (M : Matrix n n K) (i j : n) :
    (oneSubXMatrix (K := K) M * matrixResolvent (K := K) M) i j =
      (1 : Matrix n n K⟦X⟧) i j := by
  exact PowerSeries.ext
    (fun k => coeff_oneSubXMatrix_mul_matrixResolvent (K := K) M i j k)

theorem neg_mul_right_assoc (a b c : K⟦X⟧) :
    (-(a * b)) * c = -((a * b) * c) := by
  exact neg_mul (a * b) c

theorem neg_mul_right_reassociate (a b c : K⟦X⟧) :
    -((a * b) * c) = -(a * (b * c)) := by
  exact congrArg Neg.neg (mul_assoc a b c)

theorem neg_mul_commute_left_factor (a b c : K⟦X⟧) :
    -(a * (b * c)) = -((b * a) * c) := by
  exact congrArg Neg.neg
    ((mul_assoc a b c).symm.trans
      (congrArg (fun t : K⟦X⟧ => t * c) (mul_comm a b)))

theorem neg_mul_group_inverse_tail (a b : K⟦X⟧) :
    -((b * a) * a⁻¹) = -(b * (a * a⁻¹)) := by
  exact congrArg Neg.neg (mul_assoc b a a⁻¹)

theorem neg_mul_inv_cancel_tail (a b : K⟦X⟧)
    (h0 : PowerSeries.coeff K 0 a = 1) :
    -(b * (a * a⁻¹)) = -b := by
  have hconst : PowerSeries.constantCoeff K a ≠ 0 := by
    intro hzero
    have hcoeff_zero : PowerSeries.coeff K 0 a = 0 := by
      exact (PowerSeries.coeff_zero_eq_constantCoeff_apply a).trans hzero
    exact zero_ne_one (hcoeff_zero.symm.trans h0)
  exact congrArg Neg.neg
    ((congrArg (fun t : K⟦X⟧ => b * t) (PowerSeries.mul_inv_cancel a hconst)).trans
      (mul_one b))

theorem neg_mul_mul_inv_cancel_comm (a b : K⟦X⟧)
    (h0 : PowerSeries.coeff K 0 a = 1) :
    (-(a * b)) * a⁻¹ = -b := by
  exact
    (neg_mul_right_assoc a b a⁻¹).trans
      ((neg_mul_right_reassociate a b a⁻¹).trans
        ((neg_mul_commute_left_factor a b a⁻¹).trans
          ((neg_mul_group_inverse_tail a b).trans
            (neg_mul_inv_cancel_tail a b h0))))

theorem matrixResolvent_mul_oneSubXMatrix (M : Matrix n n K) :
    matrixResolvent (K := K) M * oneSubXMatrix (K := K) M = 1 := by
  exact Matrix.ext
    (fun i j => matrixResolvent_mul_oneSubXMatrix_entry (K := K) M i j)

theorem oneSubXMatrix_mul_matrixResolvent (M : Matrix n n K) :
    oneSubXMatrix (K := K) M * matrixResolvent (K := K) M = 1 := by
  exact Matrix.ext
    (fun i j => oneSubXMatrix_mul_matrixResolvent_entry (K := K) M i j)
end MatrixSeries

end

end TraceExpansion
end Boundary
