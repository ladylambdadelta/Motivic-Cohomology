import Boundary.LFunctions.TraceExpansionMatrixResolvent
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.RingTheory.PowerSeries.Derivative

/-!
# Formal logarithmic trace expansions: matrix determinant layer

This file owns the polynomial/coercion bridge, determinant/adjugate identities,
and the derivative of `charpolyRev`.
-/

open scoped BigOperators PowerSeries

namespace Boundary
namespace TraceExpansion

noncomputable section

variable {K : Type*} [Field K]

section MatrixSeries

variable {n : Type*} [Fintype n] [DecidableEq n]

theorem adjugate_eq_det_smul_of_right_inverse
    (A R : Matrix n n K⟦X⟧) (hAR : A * R = 1) :
    A.adjugate = A.det • R := by
  have hone : A.adjugate = A.adjugate * 1 := by
    exact (mul_one A.adjugate).symm
  have hright : A.adjugate * 1 = A.adjugate * (A * R) := by
    exact congrArg (fun T : Matrix n n K⟦X⟧ => A.adjugate * T) hAR.symm
  have hassoc : A.adjugate * (A * R) = (A.adjugate * A) * R := by
    exact (Matrix.mul_assoc A.adjugate A R).symm
  have hadj :
      (A.adjugate * A) * R = (A.det • (1 : Matrix n n K⟦X⟧)) * R := by
    exact congrArg (fun T : Matrix n n K⟦X⟧ => T * R) (Matrix.adjugate_mul A)
  have hsmul :
      (A.det • (1 : Matrix n n K⟦X⟧)) * R = A.det • (1 * R) := by
    exact Matrix.smul_mul A.det (1 : Matrix n n K⟦X⟧) R
  have hunit : A.det • (1 * R) = A.det • R := by
    exact congrArg (fun T : Matrix n n K⟦X⟧ => A.det • T) (one_mul R)
  exact hone.trans (hright.trans (hassoc.trans (hadj.trans (hsmul.trans hunit))))

omit [Fintype n] in
theorem polynomial_one_sub_X_matrix_entry_raw (M : Matrix n n K) (i j : n) :
    (1 - (Polynomial.X : Polynomial K) • M.map Polynomial.C) i j =
      (1 : Matrix n n (Polynomial K)) i j -
        ((Polynomial.X : Polynomial K) • M.map Polynomial.C) i j := by
  rfl

omit [Fintype n] [DecidableEq n] in
theorem polynomial_X_smul_matrix_entry (M : Matrix n n K) (i j : n) :
    ((Polynomial.X : Polynomial K) • M.map Polynomial.C) i j =
      Polynomial.X * Polynomial.C (M i j) := by
  have happly :
      ((Polynomial.X : Polynomial K) • M.map Polynomial.C) i j =
        (Polynomial.X : Polynomial K) • ((M.map Polynomial.C) i j) := by
    exact Matrix.smul_apply (Polynomial.X : Polynomial K) (M.map Polynomial.C) i j
  have hmap :
      (Polynomial.X : Polynomial K) • ((M.map Polynomial.C) i j) =
        (Polynomial.X : Polynomial K) • Polynomial.C (M i j) := by
    exact congrArg (fun t : Polynomial K => (Polynomial.X : Polynomial K) • t)
      (Matrix.map_apply (M := M) (f := Polynomial.C) (i := i) (j := j))
  have hscalar :
      (Polynomial.X : Polynomial K) • Polynomial.C (M i j) =
        Polynomial.X * Polynomial.C (M i j) := by
    rfl
  exact happly.trans (hmap.trans hscalar)

omit [Fintype n] in
theorem polynomial_one_sub_X_matrix_entry (M : Matrix n n K) (i j : n) :
    (1 - (Polynomial.X : Polynomial K) • M.map Polynomial.C) i j =
      (if i = j then 1 else 0) - Polynomial.X * Polynomial.C (M i j) := by
  exact (polynomial_one_sub_X_matrix_entry_raw (K := K) M i j).trans
    (congrArg₂ Sub.sub
        (Matrix.one_apply : (1 : Matrix n n (Polynomial K)) i j = if i = j then 1 else 0)
      (polynomial_X_smul_matrix_entry (K := K) M i j))

omit [Fintype n] in
theorem coe_polynomial_indicator_sub_X_C (M : Matrix n n K) (i j : n) :
    (((if i = j then 1 else 0 : Polynomial K) -
        Polynomial.X * Polynomial.C (M i j) : Polynomial K) : K⟦X⟧) =
      ((if i = j then 1 else 0 : K⟦X⟧) -
        PowerSeries.X * PowerSeries.C K (M i j)) := by
  have hsub :
      (((if i = j then 1 else 0 : Polynomial K) -
        Polynomial.X * Polynomial.C (M i j) : Polynomial K) : K⟦X⟧) =
        ((if i = j then 1 else 0 : Polynomial K) : K⟦X⟧) -
          ((Polynomial.X * Polynomial.C (M i j) : Polynomial K) : K⟦X⟧) := by
    exact Polynomial.coe_sub
      (if i = j then 1 else 0 : Polynomial K)
      (Polynomial.X * Polynomial.C (M i j))
  have hindicator :
      ((if i = j then 1 else 0 : Polynomial K) : K⟦X⟧) -
          ((Polynomial.X * Polynomial.C (M i j) : Polynomial K) : K⟦X⟧) =
        ((if i = j then 1 else 0 : K⟦X⟧) -
          ((Polynomial.X * Polynomial.C (M i j) : Polynomial K) : K⟦X⟧)) := by
    match (inferInstance : Decidable (i = j)) with
    | .isTrue hij =>
        exact (congrArg (fun t : K⟦X⟧ => t -
          ((Polynomial.X * Polynomial.C (M i j) : Polynomial K) : K⟦X⟧))
        (((congrArg (fun t : Polynomial K => (t : K⟦X⟧)) (if_pos hij)).trans
          (Polynomial.coe_C 1)).trans (if_pos hij).symm))
    | .isFalse hij =>
        exact (congrArg (fun t : K⟦X⟧ => t -
          ((Polynomial.X * Polynomial.C (M i j) : Polynomial K) : K⟦X⟧))
        (((congrArg (fun t : Polynomial K => (t : K⟦X⟧)) (if_neg hij)).trans
          (map_zero Polynomial.coeToPowerSeries.ringHom)).trans (if_neg hij).symm))
  have hmonomial :
      ((if i = j then 1 else 0 : K⟦X⟧) -
          ((Polynomial.X * Polynomial.C (M i j) : Polynomial K) : K⟦X⟧)) =
        ((if i = j then 1 else 0 : K⟦X⟧) -
          PowerSeries.X * PowerSeries.C K (M i j)) := by
    exact congrArg (fun t : K⟦X⟧ => (if i = j then 1 else 0 : K⟦X⟧) - t)
      ((map_mul Polynomial.coeToPowerSeries.ringHom Polynomial.X (Polynomial.C (M i j))).trans
        (congrArg₂ Mul.mul
          (Polynomial.coe_X (R := K))
          (Polynomial.coe_C (M i j))))
  exact hsub.trans (hindicator.trans hmonomial)

theorem coeToPowerSeries_mapMatrix_entry (A : Matrix n n (Polynomial K)) (i j : n) :
    (Polynomial.coeToPowerSeries.ringHom.mapMatrix A) i j =
      (Polynomial.coeToPowerSeries.ringHom (A i j)) := by
  exact Matrix.map_apply (M := A) (f := Polynomial.coeToPowerSeries.ringHom) (i := i) (j := j)

theorem coeToPowerSeries_mapMatrix_one_sub_X_matrix_entry (M : Matrix n n K) (i j : n) :
    (Polynomial.coeToPowerSeries.ringHom.mapMatrix
      (1 - (Polynomial.X : Polynomial K) • M.map Polynomial.C)) i j =
      oneSubXMatrix (K := K) M i j := by
  have hentry :
      (Polynomial.coeToPowerSeries.ringHom.mapMatrix
      (1 - (Polynomial.X : Polynomial K) • M.map Polynomial.C)) i j =
        (Polynomial.coeToPowerSeries.ringHom
          ((1 - (Polynomial.X : Polynomial K) • M.map Polynomial.C) i j)) := by
    exact coeToPowerSeries_mapMatrix_entry
      (K := K) (1 - (Polynomial.X : Polynomial K) • M.map Polynomial.C) i j
  have hpoly :
      (Polynomial.coeToPowerSeries.ringHom
          ((1 - (Polynomial.X : Polynomial K) • M.map Polynomial.C) i j)) =
        (Polynomial.coeToPowerSeries.ringHom
          ((if i = j then 1 else 0 : Polynomial K) -
            Polynomial.X * Polynomial.C (M i j))) := by
    exact congrArg Polynomial.coeToPowerSeries.ringHom
      (polynomial_one_sub_X_matrix_entry (K := K) M i j)
  have hcoe :
      (Polynomial.coeToPowerSeries.ringHom
          ((if i = j then 1 else 0 : Polynomial K) -
            Polynomial.X * Polynomial.C (M i j))) =
        ((if i = j then 1 else 0 : K⟦X⟧) -
          PowerSeries.X * PowerSeries.C K (M i j)) := by
    exact coe_polynomial_indicator_sub_X_C (K := K) M i j
  have hmatrix :
      ((if i = j then 1 else 0 : K⟦X⟧) -
          PowerSeries.X * PowerSeries.C K (M i j)) =
        oneSubXMatrix (K := K) M i j := by
    exact (oneSubXMatrix_apply (K := K) M i j).symm
  exact hentry.trans (hpoly.trans (hcoe.trans hmatrix))

theorem coeToPowerSeries_mapMatrix_one_sub_X_matrix (M : Matrix n n K) :
    (Polynomial.coeToPowerSeries.ringHom.mapMatrix
      (1 - (Polynomial.X : Polynomial K) • M.map Polynomial.C)) =
      oneSubXMatrix (K := K) M := by
  apply Matrix.ext
  intro i j
  exact coeToPowerSeries_mapMatrix_one_sub_X_matrix_entry (K := K) M i j

theorem coeToPowerSeries_det_one_sub_X_matrix (M : Matrix n n K) :
    Polynomial.coeToPowerSeries.ringHom
        ((1 - (Polynomial.X : Polynomial K) • M.map Polynomial.C).det) =
      (Polynomial.coeToPowerSeries.ringHom.mapMatrix
        (1 - (Polynomial.X : Polynomial K) • M.map Polynomial.C)).det := by
  exact RingHom.map_det Polynomial.coeToPowerSeries.ringHom
    (1 - (Polynomial.X : Polynomial K) • M.map Polynomial.C)

theorem charpolyRev_eq_det_one_sub_X_matrix (M : Matrix n n K) :
    M.charpolyRev =
      (1 - (Polynomial.X : Polynomial K) • M.map Polynomial.C).det := by
  rfl

theorem coe_charpolyRev_eq_coe_det_one_sub_X_matrix (M : Matrix n n K) :
    (M.charpolyRev : K⟦X⟧) =
      Polynomial.coeToPowerSeries.ringHom
        ((1 - (Polynomial.X : Polynomial K) • M.map Polynomial.C).det) := by
  exact congrArg Polynomial.coeToPowerSeries.ringHom
    (charpolyRev_eq_det_one_sub_X_matrix (K := K) M)

theorem det_oneSubXMatrix (M : Matrix n n K) :
    (oneSubXMatrix (K := K) M).det = (M.charpolyRev : K⟦X⟧) := by
  have hmatrix :
      (oneSubXMatrix (K := K) M).det =
        (Polynomial.coeToPowerSeries.ringHom.mapMatrix
          (1 - (Polynomial.X : Polynomial K) • M.map Polynomial.C)).det := by
    exact congrArg Matrix.det
      (coeToPowerSeries_mapMatrix_one_sub_X_matrix (K := K) M).symm
  have hdet :
      (Polynomial.coeToPowerSeries.ringHom.mapMatrix
          (1 - (Polynomial.X : Polynomial K) • M.map Polynomial.C)).det =
        Polynomial.coeToPowerSeries.ringHom
        ((1 - (Polynomial.X : Polynomial K) • M.map Polynomial.C).det) := by
    exact (coeToPowerSeries_det_one_sub_X_matrix (K := K) M).symm
  have hchar :
      Polynomial.coeToPowerSeries.ringHom
          ((1 - (Polynomial.X : Polynomial K) • M.map Polynomial.C).det) =
        (M.charpolyRev : K⟦X⟧) := by
    exact (coe_charpolyRev_eq_coe_det_one_sub_X_matrix (K := K) M).symm
  exact hmatrix.trans (hdet.trans hchar)

theorem oneSubXMatrix_right_inverse_alias (M : Matrix n n K) :
    oneSubXMatrix (K := K) M * matrixResolvent (K := K) M = 1 := by
  exact oneSubXMatrix_mul_matrixResolvent (K := K) M

theorem oneSubXMatrix_det_alias (M : Matrix n n K) :
    (oneSubXMatrix (K := K) M).det = (M.charpolyRev : K⟦X⟧) := by
  exact det_oneSubXMatrix (K := K) M

theorem adjugate_oneSubXMatrix_eq_charpolyRev_smul_matrixResolvent
    (M : Matrix n n K) :
    (oneSubXMatrix (K := K) M).adjugate =
      (M.charpolyRev : K⟦X⟧) • matrixResolvent (K := K) M := by
  have hadj :
      (oneSubXMatrix (K := K) M).adjugate =
        (oneSubXMatrix (K := K) M).det • matrixResolvent (K := K) M := by
    exact adjugate_eq_det_smul_of_right_inverse
      (oneSubXMatrix (K := K) M)
      (matrixResolvent (K := K) M)
      (oneSubXMatrix_right_inverse_alias (K := K) M)
  have hdet :
      (oneSubXMatrix (K := K) M).det • matrixResolvent (K := K) M =
        (M.charpolyRev : K⟦X⟧) • matrixResolvent (K := K) M := by
    exact congrArg (fun t : K⟦X⟧ => t • matrixResolvent (K := K) M)
      (oneSubXMatrix_det_alias (K := K) M)
  exact hadj.trans hdet

theorem coeff_C_mul_matrixResolvent (M : Matrix n n K) (i j : n) (a : K) (k : ℕ) :
    PowerSeries.coeff K k
        (PowerSeries.C K a * matrixResolvent (K := K) M i j) =
      a * (M ^ k) i j := by
  have hcoeff :
      PowerSeries.coeff K k
        (PowerSeries.C K a * matrixResolvent (K := K) M i j) =
        a * PowerSeries.coeff K k (matrixResolvent (K := K) M i j) := by
    exact PowerSeries.coeff_C_mul
      (R := K) k (matrixResolvent (K := K) M i j) a
  have hres :
      a * PowerSeries.coeff K k (matrixResolvent (K := K) M i j) =
        a * (M ^ k) i j := by
    exact congrArg (fun t : K => a * t)
      (coeff_matrixResolvent (K := K) M i j k)
  exact hcoeff.trans hres

theorem coeff_sum_C_mul_matrixResolvent_row
    (M : Matrix n n K) (i : n) (k : ℕ) :
    PowerSeries.coeff K k
        (∑ j : n, PowerSeries.C K (M i j) * matrixResolvent (K := K) M j i) =
      ∑ j : n, M i j * (M ^ k) j i := by
  have hsum :
      PowerSeries.coeff K k
        (∑ j : n, PowerSeries.C K (M i j) * matrixResolvent (K := K) M j i) =
        ∑ j : n,
          PowerSeries.coeff K k
            (PowerSeries.C K (M i j) * matrixResolvent (K := K) M j i) := by
    exact map_sum (PowerSeries.coeff K k)
      (fun j => PowerSeries.C K (M i j) * matrixResolvent (K := K) M j i)
      Finset.univ
  have hcoeff :
      (∑ j : n,
          PowerSeries.coeff K k
            (PowerSeries.C K (M i j) * matrixResolvent (K := K) M j i)) =
        ∑ j : n, M i j * (M ^ k) j i := by
    exact Finset.sum_congr rfl
      (fun j _ => coeff_C_mul_matrixResolvent (K := K) M j i (M i j) k)
  exact hsum.trans hcoeff

theorem coeff_sum_sum_C_mul_matrixResolvent
    (M : Matrix n n K) (k : ℕ) :
    PowerSeries.coeff K k
        (∑ i : n, ∑ j : n,
          PowerSeries.C K (M i j) * matrixResolvent (K := K) M j i) =
      ∑ i : n, ∑ j : n, M i j * (M ^ k) j i := by
  have hsum :
      PowerSeries.coeff K k
        (∑ i : n, ∑ j : n,
          PowerSeries.C K (M i j) * matrixResolvent (K := K) M j i) =
        ∑ i : n,
          PowerSeries.coeff K k
            (∑ j : n, PowerSeries.C K (M i j) * matrixResolvent (K := K) M j i) := by
    exact map_sum (PowerSeries.coeff K k)
      (fun i => ∑ j : n, PowerSeries.C K (M i j) * matrixResolvent (K := K) M j i)
      Finset.univ
  have hrows :
      (∑ i : n,
          PowerSeries.coeff K k
            (∑ j : n, PowerSeries.C K (M i j) * matrixResolvent (K := K) M j i)) =
        ∑ i : n, ∑ j : n, M i j * (M ^ k) j i := by
    exact Finset.sum_congr rfl
      (fun i _ => coeff_sum_C_mul_matrixResolvent_row (K := K) M i k)
  exact hsum.trans hrows

theorem trace_matrix_pow_succ_eq_sum_entry_mul_pow
    (M : Matrix n n K) (k : ℕ) :
    Matrix.trace (M ^ (k + 1)) =
      ∑ i : n, ∑ j : n, M i j * (M ^ k) j i := by
  have htrace :
      Matrix.trace (M ^ (k + 1)) =
        ∑ i : n, (M ^ (k + 1)) i i := by
    rfl
  have hpow :
      (∑ i : n, (M ^ (k + 1)) i i) =
        ∑ i : n, ∑ j : n, M i j * (M ^ k) j i := by
    exact Finset.sum_congr rfl
      (fun i _ => (sum_entry_mul_matrix_pow_left (K := K) M i i k).symm)
  exact htrace.trans hpow

theorem coeff_sum_sum_C_mul_matrixResolvent_eq_trace
    (M : Matrix n n K) (k : ℕ) :
    PowerSeries.coeff K k
        (∑ i : n, ∑ j : n,
          PowerSeries.C K (M i j) * matrixResolvent (K := K) M j i) =
      Matrix.trace (M ^ (k + 1)) := by
  exact (coeff_sum_sum_C_mul_matrixResolvent (K := K) M k).trans
    (trace_matrix_pow_succ_eq_sum_entry_mul_pow (K := K) M k).symm

theorem traceResolventSeries_eq_sum_matrixResolvent (M : Matrix n n K) :
    traceResolventSeries (K := K) M =
      ∑ i : n, ∑ j : n,
        PowerSeries.C K (M i j) * matrixResolvent (K := K) M j i := by
  apply PowerSeries.ext
  intro k
  exact (coeff_traceResolventSeries (K := K) M k).trans
    (coeff_sum_sum_C_mul_matrixResolvent_eq_trace (K := K) M k).symm

theorem mul_C_mul_reassociate (a c r : K⟦X⟧) :
    a * (c * r) = c * (a * r) := by
  have hassoc_left : a * (c * r) = (a * c) * r := by
    exact (mul_assoc a c r).symm
  have hcomm : (a * c) * r = (c * a) * r := by
    exact congrArg (fun t : K⟦X⟧ => t * r) (mul_comm a c)
  have hassoc_right : (c * a) * r = c * (a * r) := by
    exact mul_assoc c a r
  exact hassoc_left.trans (hcomm.trans hassoc_right)

theorem mul_sum_C_mul_matrixResolvent_row
    (M : Matrix n n K) (a : K⟦X⟧) (i : n) :
    a * (∑ j : n, PowerSeries.C K (M i j) * matrixResolvent (K := K) M j i) =
      ∑ j : n, PowerSeries.C K (M i j) *
        (a * matrixResolvent (K := K) M j i) := by
  have hdist :
      a * (∑ j : n, PowerSeries.C K (M i j) * matrixResolvent (K := K) M j i) =
        ∑ j : n, a * (PowerSeries.C K (M i j) * matrixResolvent (K := K) M j i) := by
    exact Finset.mul_sum
      (s := Finset.univ)
      (f := fun j : n => PowerSeries.C K (M i j) * matrixResolvent (K := K) M j i)
      (a := a)
  have hterms :
      (∑ j : n, a * (PowerSeries.C K (M i j) * matrixResolvent (K := K) M j i)) =
        ∑ j : n, PowerSeries.C K (M i j) *
        (a * matrixResolvent (K := K) M j i) := by
    exact Finset.sum_congr rfl
      (fun j _ => mul_C_mul_reassociate
        (K := K) a (PowerSeries.C K (M i j)) (matrixResolvent (K := K) M j i))
  exact hdist.trans hterms

theorem mul_sum_sum_C_mul_matrixResolvent
    (M : Matrix n n K) (a : K⟦X⟧) :
    a * (∑ i : n, ∑ j : n,
        PowerSeries.C K (M i j) * matrixResolvent (K := K) M j i) =
      ∑ i : n, ∑ j : n, PowerSeries.C K (M i j) *
        (a * matrixResolvent (K := K) M j i) := by
  have hdist :
      a * (∑ i : n, ∑ j : n,
        PowerSeries.C K (M i j) * matrixResolvent (K := K) M j i) =
        ∑ i : n, a *
          (∑ j : n, PowerSeries.C K (M i j) * matrixResolvent (K := K) M j i) := by
    exact Finset.mul_sum
      (s := Finset.univ)
      (f := fun i : n =>
        ∑ j : n, PowerSeries.C K (M i j) * matrixResolvent (K := K) M j i)
      (a := a)
  have hrows :
      (∑ i : n, a *
          (∑ j : n, PowerSeries.C K (M i j) * matrixResolvent (K := K) M j i)) =
        ∑ i : n, ∑ j : n, PowerSeries.C K (M i j) *
        (a * matrixResolvent (K := K) M j i) := by
    exact Finset.sum_congr rfl
      (fun i _ => mul_sum_C_mul_matrixResolvent_row (K := K) M a i)
  exact hdist.trans hrows

theorem adjugate_oneSubXMatrix_entry_eq_charpolyRev_mul_matrixResolvent
    (M : Matrix n n K) (i j : n) :
    (oneSubXMatrix (K := K) M).adjugate j i =
      (M.charpolyRev : K⟦X⟧) * matrixResolvent (K := K) M j i := by
  have hentry :
      (oneSubXMatrix (K := K) M).adjugate j i =
        (((M.charpolyRev : K⟦X⟧) • matrixResolvent (K := K) M) j i) := by
    exact congrFun (congrFun
      (adjugate_oneSubXMatrix_eq_charpolyRev_smul_matrixResolvent (K := K) M) j) i
  have hsmul :
      (((M.charpolyRev : K⟦X⟧) • matrixResolvent (K := K) M) j i) =
        (M.charpolyRev : K⟦X⟧) • matrixResolvent (K := K) M j i := by
    rfl
  have hmul :
      (M.charpolyRev : K⟦X⟧) • matrixResolvent (K := K) M j i =
        (M.charpolyRev : K⟦X⟧) * matrixResolvent (K := K) M j i := by
    rfl
  exact hentry.trans (hsmul.trans hmul)

theorem sum_sum_C_mul_charpolyRev_matrixResolvent_eq_trace_adjugate
    (M : Matrix n n K) :
    (∑ i : n, ∑ j : n, PowerSeries.C K (M i j) *
        ((M.charpolyRev : K⟦X⟧) * matrixResolvent (K := K) M j i)) =
      ∑ i : n, ∑ j : n,
        PowerSeries.C K (M i j) *
          (oneSubXMatrix (K := K) M).adjugate j i := by
  exact Finset.sum_congr rfl
    (fun i _ => Finset.sum_congr rfl
      (fun j _ => congrArg (fun t : K⟦X⟧ => PowerSeries.C K (M i j) * t)
        (adjugate_oneSubXMatrix_entry_eq_charpolyRev_mul_matrixResolvent
          (K := K) M i j).symm))

theorem charpolyRev_mul_traceResolventSeries_eq_trace_adjugate
    (M : Matrix n n K) :
    (M.charpolyRev : K⟦X⟧) * traceResolventSeries (K := K) M =
      ∑ i : n, ∑ j : n,
        PowerSeries.C K (M i j) *
          (oneSubXMatrix (K := K) M).adjugate j i := by
  have htrace :
      (M.charpolyRev : K⟦X⟧) * traceResolventSeries (K := K) M =
        (M.charpolyRev : K⟦X⟧) *
          (∑ i : n, ∑ j : n,
            PowerSeries.C K (M i j) * matrixResolvent (K := K) M j i) := by
    exact congrArg (fun t : K⟦X⟧ => (M.charpolyRev : K⟦X⟧) * t)
      (traceResolventSeries_eq_sum_matrixResolvent (K := K) M)
  have hdist :
      (M.charpolyRev : K⟦X⟧) *
          (∑ i : n, ∑ j : n,
            PowerSeries.C K (M i j) * matrixResolvent (K := K) M j i) =
        ∑ i : n, ∑ j : n, PowerSeries.C K (M i j) *
        ((M.charpolyRev : K⟦X⟧) * matrixResolvent (K := K) M j i) := by
    exact mul_sum_sum_C_mul_matrixResolvent (K := K) M (M.charpolyRev : K⟦X⟧)
  have hadj :
      (∑ i : n, ∑ j : n, PowerSeries.C K (M i j) *
        ((M.charpolyRev : K⟦X⟧) * matrixResolvent (K := K) M j i)) =
        ∑ i : n, ∑ j : n,
        PowerSeries.C K (M i j) *
          (oneSubXMatrix (K := K) M).adjugate j i := by
    exact sum_sum_C_mul_charpolyRev_matrixResolvent_eq_trace_adjugate (K := K) M
  exact htrace.trans (hdist.trans hadj)

theorem coeToPowerSeries_mapMatrix_adjugate
    (A : Matrix n n (Polynomial K)) :
    Polynomial.coeToPowerSeries.ringHom.mapMatrix A.adjugate =
      (Polynomial.coeToPowerSeries.ringHom.mapMatrix A).adjugate := by
  exact RingHom.map_adjugate Polynomial.coeToPowerSeries.ringHom A

theorem coe_adjugate_one_sub_X_matrix_entry
    (M : Matrix n n K) (i j : n) :
    (((1 - (Polynomial.X : Polynomial K) • M.map Polynomial.C).adjugate j i :
      Polynomial K) : K⟦X⟧) =
      (oneSubXMatrix (K := K) M).adjugate j i := by
  have hentry :
      (((1 - (Polynomial.X : Polynomial K) • M.map Polynomial.C).adjugate j i :
      Polynomial K) : K⟦X⟧) =
        (Polynomial.coeToPowerSeries.ringHom.mapMatrix
          (1 - (Polynomial.X : Polynomial K) • M.map Polynomial.C).adjugate) j i := by
    exact (coeToPowerSeries_mapMatrix_entry
      (K := K)
      ((1 - (Polynomial.X : Polynomial K) • M.map Polynomial.C).adjugate) j i).symm
  have hadj :
      (Polynomial.coeToPowerSeries.ringHom.mapMatrix
          (1 - (Polynomial.X : Polynomial K) • M.map Polynomial.C).adjugate) j i =
        (Polynomial.coeToPowerSeries.ringHom.mapMatrix
          (1 - (Polynomial.X : Polynomial K) • M.map Polynomial.C)).adjugate j i := by
    exact congrFun (congrFun
      (coeToPowerSeries_mapMatrix_adjugate
        (K := K) (1 - (Polynomial.X : Polynomial K) • M.map Polynomial.C)) j) i
  have hmatrix :
      (Polynomial.coeToPowerSeries.ringHom.mapMatrix
          (1 - (Polynomial.X : Polynomial K) • M.map Polynomial.C)).adjugate j i =
        (oneSubXMatrix (K := K) M).adjugate j i := by
    exact congrFun (congrFun
      (congrArg Matrix.adjugate
        (coeToPowerSeries_mapMatrix_one_sub_X_matrix (K := K) M)) j) i
  exact hentry.trans (hadj.trans hmatrix)

theorem coe_polynomial_C_mul_adjugate_one_sub_X_matrix_entry
    (M : Matrix n n K) (i j : n) :
    ((Polynomial.C (M i j) *
        (1 - (Polynomial.X : Polynomial K) • M.map Polynomial.C).adjugate j i :
      Polynomial K) : K⟦X⟧) =
      PowerSeries.C K (M i j) *
        (oneSubXMatrix (K := K) M).adjugate j i := by
  have hmul :
      ((Polynomial.C (M i j) *
        (1 - (Polynomial.X : Polynomial K) • M.map Polynomial.C).adjugate j i :
      Polynomial K) : K⟦X⟧) =
        ((Polynomial.C (M i j) : Polynomial K) : K⟦X⟧) *
          (((1 - (Polynomial.X : Polynomial K) • M.map Polynomial.C).adjugate j i :
            Polynomial K) : K⟦X⟧) := by
    exact map_mul Polynomial.coeToPowerSeries.ringHom
      (Polynomial.C (M i j))
      ((1 - (Polynomial.X : Polynomial K) • M.map Polynomial.C).adjugate j i)
  have hconst :
      ((Polynomial.C (M i j) : Polynomial K) : K⟦X⟧) *
          (((1 - (Polynomial.X : Polynomial K) • M.map Polynomial.C).adjugate j i :
            Polynomial K) : K⟦X⟧) =
        PowerSeries.C K (M i j) *
        (((1 - (Polynomial.X : Polynomial K) • M.map Polynomial.C).adjugate j i :
          Polynomial K) : K⟦X⟧) := by
    exact congrArg
      (fun t : K⟦X⟧ => t *
        (((1 - (Polynomial.X : Polynomial K) • M.map Polynomial.C).adjugate j i :
          Polynomial K) : K⟦X⟧))
      (Polynomial.coe_C (M i j))
  have hadj :
      PowerSeries.C K (M i j) *
        (((1 - (Polynomial.X : Polynomial K) • M.map Polynomial.C).adjugate j i :
          Polynomial K) : K⟦X⟧) =
        PowerSeries.C K (M i j) *
        (oneSubXMatrix (K := K) M).adjugate j i := by
    exact congrArg (fun t : K⟦X⟧ => PowerSeries.C K (M i j) * t)
      (coe_adjugate_one_sub_X_matrix_entry (K := K) M i j)
  exact hmul.trans (hconst.trans hadj)

theorem coe_sum_polynomial_C_mul_adjugate_one_sub_X_matrix_row
    (M : Matrix n n K) (i : n) :
    ((∑ j : n, Polynomial.C (M i j) *
        (1 - (Polynomial.X : Polynomial K) • M.map Polynomial.C).adjugate j i :
      Polynomial K) : K⟦X⟧) =
      ∑ j : n, PowerSeries.C K (M i j) *
        (oneSubXMatrix (K := K) M).adjugate j i := by
  have hsum :
      ((∑ j : n, Polynomial.C (M i j) *
        (1 - (Polynomial.X : Polynomial K) • M.map Polynomial.C).adjugate j i :
      Polynomial K) : K⟦X⟧) =
        ∑ j : n,
          ((Polynomial.C (M i j) *
            (1 - (Polynomial.X : Polynomial K) • M.map Polynomial.C).adjugate j i :
          Polynomial K) : K⟦X⟧) := by
    exact map_sum Polynomial.coeToPowerSeries.ringHom
      (fun j => Polynomial.C (M i j) *
        (1 - (Polynomial.X : Polynomial K) • M.map Polynomial.C).adjugate j i)
      Finset.univ
  have hterms :
      (∑ j : n,
          ((Polynomial.C (M i j) *
            (1 - (Polynomial.X : Polynomial K) • M.map Polynomial.C).adjugate j i :
          Polynomial K) : K⟦X⟧)) =
        ∑ j : n, PowerSeries.C K (M i j) *
        (oneSubXMatrix (K := K) M).adjugate j i := by
    exact Finset.sum_congr rfl
      (fun j _ =>
        coe_polynomial_C_mul_adjugate_one_sub_X_matrix_entry (K := K) M i j)
  exact hsum.trans hterms

theorem coe_sum_sum_polynomial_C_mul_adjugate_one_sub_X_matrix
    (M : Matrix n n K) :
    ((∑ i : n, ∑ j : n,
        Polynomial.C (M i j) *
          (1 - (Polynomial.X : Polynomial K) • M.map Polynomial.C).adjugate j i :
      Polynomial K) : K⟦X⟧) =
      ∑ i : n, ∑ j : n,
        PowerSeries.C K (M i j) *
          (oneSubXMatrix (K := K) M).adjugate j i := by
  have hsum :
      ((∑ i : n, ∑ j : n,
        Polynomial.C (M i j) *
          (1 - (Polynomial.X : Polynomial K) • M.map Polynomial.C).adjugate j i :
      Polynomial K) : K⟦X⟧) =
        ∑ i : n,
          ((∑ j : n,
            Polynomial.C (M i j) *
              (1 - (Polynomial.X : Polynomial K) • M.map Polynomial.C).adjugate j i :
          Polynomial K) : K⟦X⟧) := by
    exact map_sum Polynomial.coeToPowerSeries.ringHom
      (fun i => ∑ j : n, Polynomial.C (M i j) *
        (1 - (Polynomial.X : Polynomial K) • M.map Polynomial.C).adjugate j i)
      Finset.univ
  have hrows :
      (∑ i : n,
          ((∑ j : n,
            Polynomial.C (M i j) *
              (1 - (Polynomial.X : Polynomial K) • M.map Polynomial.C).adjugate j i :
          Polynomial K) : K⟦X⟧)) =
        ∑ i : n, ∑ j : n,
        PowerSeries.C K (M i j) *
          (oneSubXMatrix (K := K) M).adjugate j i := by
    exact Finset.sum_congr rfl
      (fun i _ =>
        coe_sum_polynomial_C_mul_adjugate_one_sub_X_matrix_row (K := K) M i)
  exact hsum.trans hrows

theorem coe_trace_adjugate_eq_trace_adjugate_oneSubXMatrix
    (M : Matrix n n K) :
    ((∑ i : n, ∑ j : n,
        Polynomial.C (M i j) *
          (1 - (Polynomial.X : Polynomial K) • M.map Polynomial.C).adjugate j i :
      Polynomial K) : K⟦X⟧) =
      ∑ i : n, ∑ j : n,
        PowerSeries.C K (M i j) *
          (oneSubXMatrix (K := K) M).adjugate j i := by
  exact coe_sum_sum_polynomial_C_mul_adjugate_one_sub_X_matrix (K := K) M

theorem derivative_finset_prod_empty {ι : Type*} [DecidableEq ι] (f : ι → Polynomial K) :
    Polynomial.derivative (∏ i in (∅ : Finset ι), f i) =
      ∑ i in (∅ : Finset ι), (∏ j in (∅ : Finset ι).erase i, f j) *
        Polynomial.derivative (f i) := by
  have hprod : (∏ i in (∅ : Finset ι), f i) = 1 := by
    exact Finset.prod_empty
  have hderivative :
      Polynomial.derivative (∏ i in (∅ : Finset ι), f i) =
        Polynomial.derivative (1 : Polynomial K) := by
    exact congrArg Polynomial.derivative hprod
  have hone : Polynomial.derivative (1 : Polynomial K) = 0 := by
    exact Polynomial.derivative_one
  have hsum :
      (∑ i in (∅ : Finset ι), (∏ j in (∅ : Finset ι).erase i, f j) *
        Polynomial.derivative (f i)) = 0 := by
    exact Finset.sum_empty
  exact hderivative.trans (hone.trans hsum.symm)

theorem derivative_finset_prod {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (f : ι → Polynomial K) :
    Polynomial.derivative (∏ i in s, f i) =
      ∑ i in s, (∏ j in s.erase i, f j) * Polynomial.derivative (f i) := by
  exact Polynomial.derivative_prod (s := s.val) (f := f)

theorem det_updateColumn_eq_sum_mul_adjugate
    (A : Matrix n n (Polynomial K)) (j : n) (v : n → Polynomial K) :
    (A.updateColumn j v).det = ∑ i : n, v i * A.adjugate j i := by
  have hcramer : (A.updateColumn j v).det = Matrix.cramer A v j := by
    exact (Matrix.cramer_apply (A := A) (b := v) (i := j)).symm
  have hadjugate : Matrix.cramer A v j = Matrix.mulVec A.adjugate v j := by
    exact congrFun (Matrix.cramer_eq_adjugate_mulVec (A := A) (b := v)) j
  have hdot : Matrix.mulVec A.adjugate v j = Matrix.dotProduct (A.adjugate j) v := by
    rfl
  have hsum :
      Matrix.dotProduct (A.adjugate j) v = ∑ i : n, A.adjugate j i * v i := by
    rfl
  have hcomm :
      (∑ i : n, A.adjugate j i * v i) =
        ∑ i : n, v i * A.adjugate j i := by
    exact Finset.sum_congr rfl
      (fun i _ => mul_comm (A.adjugate j i) (v i))
  exact hcramer.trans (hadjugate.trans (hdot.trans (hsum.trans hcomm)))

omit [Fintype n] in
theorem update_oneSubXMatrix_off_column_entry
    (M : Matrix n n K) (σ : Equiv.Perm n) {x y : n} (hxy : x ≠ y) :
    Function.update
        (((1 : Matrix n n (Polynomial K)) -
          (Polynomial.X : Polynomial K) • M.map Polynomial.C) (σ x)) y
        (-Polynomial.C (M (σ x) y)) x =
      ((if σ x = x then 1 else 0) -
        Polynomial.C (M (σ x) x) * Polynomial.X) := by
  have hoff :
      Function.update
          (((1 : Matrix n n (Polynomial K)) -
            (Polynomial.X : Polynomial K) • M.map Polynomial.C) (σ x)) y
          (-Polynomial.C (M (σ x) y)) x =
        ((1 : Matrix n n (Polynomial K)) -
          (Polynomial.X : Polynomial K) • M.map Polynomial.C) (σ x) x := by
    exact Function.update_noteq hxy (-Polynomial.C (M (σ x) y))
      (((1 : Matrix n n (Polynomial K)) -
        (Polynomial.X : Polynomial K) • M.map Polynomial.C) (σ x))
  have hentry :
      ((1 : Matrix n n (Polynomial K)) -
          (Polynomial.X : Polynomial K) • M.map Polynomial.C) (σ x) x =
        ((if σ x = x then 1 else 0) -
          Polynomial.X * Polynomial.C (M (σ x) x)) := by
    exact polynomial_one_sub_X_matrix_entry (K := K) M (σ x) x
  have hmul :
      ((if σ x = x then 1 else 0) -
          Polynomial.X * Polynomial.C (M (σ x) x)) =
        ((if σ x = x then 1 else 0) -
          Polynomial.C (M (σ x) x) * Polynomial.X) := by
    exact congrArg (fun t : Polynomial K => (if σ x = x then 1 else 0) - t)
      (mul_comm Polynomial.X (Polynomial.C (M (σ x) x)))
  exact hoff.trans (hentry.trans hmul)

omit [Fintype n] in
theorem update_oneSubXMatrix_column_entry
    (M : Matrix n n K) (σ : Equiv.Perm n) (y : n) :
    Function.update
        (((1 : Matrix n n (Polynomial K)) -
          (Polynomial.X : Polynomial K) • M.map Polynomial.C) (σ y)) y
        (-Polynomial.C (M (σ y) y)) y =
      -Polynomial.C (M (σ y) y) := by
  exact Function.update_same y (-Polynomial.C (M (σ y) y))
    (((1 : Matrix n n (Polynomial K)) -
      (Polynomial.X : Polynomial K) • M.map Polynomial.C) (σ y))

theorem updateColumn_oneSubXMatrix_perm_product_eq_neg_erased_diag_product
    (M : Matrix n n K) (σ : Equiv.Perm n) (y : n) :
    (∏ x : n,
        Function.update
          (((1 : Matrix n n (Polynomial K)) -
            (Polynomial.X : Polynomial K) • M.map Polynomial.C) (σ x)) y
          (-Polynomial.C (M (σ x) y)) x) =
      -((∏ x in Finset.univ.erase y,
          ((if σ x = x then 1 else 0) -
            Polynomial.C (M (σ x) x) * Polynomial.X)) *
        Polynomial.C (M (σ y) y)) := by
  have hsplit :
      (∏ x : n,
        Function.update
          (((1 : Matrix n n (Polynomial K)) -
            (Polynomial.X : Polynomial K) • M.map Polynomial.C) (σ x)) y
          (-Polynomial.C (M (σ x) y)) x) =
        (∏ x in Finset.univ.erase y,
          Function.update
            (((1 : Matrix n n (Polynomial K)) -
              (Polynomial.X : Polynomial K) • M.map Polynomial.C) (σ x)) y
            (-Polynomial.C (M (σ x) y)) x) *
          Function.update
            (((1 : Matrix n n (Polynomial K)) -
              (Polynomial.X : Polynomial K) • M.map Polynomial.C) (σ y)) y
            (-Polynomial.C (M (σ y) y)) y := by
    exact (Finset.prod_erase_mul (s := Finset.univ)
      (f := fun x =>
        Function.update
          (((1 : Matrix n n (Polynomial K)) -
            (Polynomial.X : Polynomial K) • M.map Polynomial.C) (σ x)) y
          (-Polynomial.C (M (σ x) y)) x) (a := y) (Finset.mem_univ y)).symm
  have hentries :
      (∏ x in Finset.univ.erase y,
          Function.update
            (((1 : Matrix n n (Polynomial K)) -
              (Polynomial.X : Polynomial K) • M.map Polynomial.C) (σ x)) y
            (-Polynomial.C (M (σ x) y)) x) *
          Function.update
            (((1 : Matrix n n (Polynomial K)) -
              (Polynomial.X : Polynomial K) • M.map Polynomial.C) (σ y)) y
            (-Polynomial.C (M (σ y) y)) y =
        (∏ x in Finset.univ.erase y,
          ((if σ x = x then 1 else 0) -
            Polynomial.C (M (σ x) x) * Polynomial.X)) *
          (-Polynomial.C (M (σ y) y)) := by
    congr 1
    · apply Finset.prod_congr rfl
      intro x hx
      have hxy : x ≠ y := by
        exact (Finset.mem_erase.mp hx).1
      exact update_oneSubXMatrix_off_column_entry (K := K) M σ hxy
    · exact update_oneSubXMatrix_column_entry (K := K) M σ y
  have hneg :
      (∏ x in Finset.univ.erase y,
          ((if σ x = x then 1 else 0) -
            Polynomial.C (M (σ x) x) * Polynomial.X)) *
          (-Polynomial.C (M (σ y) y)) =
        -((∏ x in Finset.univ.erase y,
          ((if σ x = x then 1 else 0) -
            Polynomial.C (M (σ x) x) * Polynomial.X)) *
        Polynomial.C (M (σ y) y)) := by
    exact mul_neg
      (∏ x in Finset.univ.erase y,
        ((if σ x = x then 1 else 0) -
          Polynomial.C (M (σ x) x) * Polynomial.X))
      (Polynomial.C (M (σ y) y))
  exact hsplit.trans (hentries.trans hneg)

omit [Fintype n] in
theorem derivative_polynomial_perm_indicator_eq_zero
    (σ : Equiv.Perm n) (i : n) :
    Polynomial.derivative ((if σ i = i then 1 else 0 : Polynomial K)) = 0 := by
  match (inferInstance : Decidable (σ i = i)) with
  | .isTrue hσi =>
      exact (congrArg Polynomial.derivative (if_pos hσi)).trans
        Polynomial.derivative_one
  | .isFalse hσi =>
      exact (congrArg Polynomial.derivative (if_neg hσi)).trans
        Polynomial.derivative_zero

omit [Fintype n] in
theorem derivative_X_mul_C (a : K) :
    Polynomial.derivative (Polynomial.X * Polynomial.C a) = Polynomial.C a := by
  have hcomm :
      Polynomial.derivative (Polynomial.X * Polynomial.C a) =
        Polynomial.derivative (Polynomial.C a * Polynomial.X) := by
    exact congrArg Polynomial.derivative (mul_comm Polynomial.X (Polynomial.C a))
  have hconst :
      Polynomial.derivative (Polynomial.C a * Polynomial.X) =
        Polynomial.C a * Polynomial.derivative Polynomial.X := by
    exact Polynomial.derivative_C_mul a Polynomial.X
  have hx :
      Polynomial.C a * Polynomial.derivative Polynomial.X =
        Polynomial.C a * (1 : Polynomial K) := by
    exact congrArg (fun t : Polynomial K => Polynomial.C a * t)
      (Polynomial.derivative_X : Polynomial.derivative Polynomial.X = (1 : Polynomial K))
  have hone : Polynomial.C a * (1 : Polynomial K) = Polynomial.C a := by
    exact mul_one (Polynomial.C a)
  exact hcomm.trans (hconst.trans (hx.trans hone))

omit [Fintype n] in
theorem one_sub_X_matrix_perm_diag_entry
    (M : Matrix n n K) (σ : Equiv.Perm n) (x : n) :
    ((1 : Matrix n n (Polynomial K)) -
        (Polynomial.X : Polynomial K) • M.map Polynomial.C) (σ x) x =
      (if σ x = x then 1 else 0) -
        Polynomial.C (M (σ x) x) * Polynomial.X := by
  have hentry :
      ((1 : Matrix n n (Polynomial K)) -
          (Polynomial.X : Polynomial K) • M.map Polynomial.C) (σ x) x =
        (if σ x = x then 1 else 0) -
          Polynomial.X * Polynomial.C (M (σ x) x) := by
    exact polynomial_one_sub_X_matrix_entry (K := K) M (σ x) x
  have hcomm :
      (if σ x = x then 1 else 0) -
          Polynomial.X * Polynomial.C (M (σ x) x) =
        (if σ x = x then 1 else 0) -
          Polynomial.C (M (σ x) x) * Polynomial.X := by
    exact congrArg (fun t : Polynomial K => (if σ x = x then 1 else 0) - t)
      (mul_comm Polynomial.X (Polynomial.C (M (σ x) x)))
  exact hentry.trans hcomm

omit [Fintype n] in
theorem derivative_one_sub_X_matrix_perm_diag_entry
    (M : Matrix n n K) (σ : Equiv.Perm n) (x : n) :
    Polynomial.derivative
        (((1 : Matrix n n (Polynomial K)) -
          (Polynomial.X : Polynomial K) • M.map Polynomial.C) (σ x) x) =
      -Polynomial.C (M (σ x) x) := by
  have hentry :
      Polynomial.derivative
          (((1 : Matrix n n (Polynomial K)) -
            (Polynomial.X : Polynomial K) • M.map Polynomial.C) (σ x) x) =
        Polynomial.derivative
          ((if σ x = x then 1 else 0 : Polynomial K) -
            Polynomial.X * Polynomial.C (M (σ x) x)) := by
    exact congrArg Polynomial.derivative
      (polynomial_one_sub_X_matrix_entry (K := K) M (σ x) x)
  have hsub :
      Polynomial.derivative
          ((if σ x = x then 1 else 0 : Polynomial K) -
            Polynomial.X * Polynomial.C (M (σ x) x)) =
        Polynomial.derivative (if σ x = x then 1 else 0 : Polynomial K) -
          Polynomial.derivative (Polynomial.X * Polynomial.C (M (σ x) x)) := by
    exact Polynomial.derivative_sub
  have hindicator :
      Polynomial.derivative (if σ x = x then 1 else 0 : Polynomial K) -
          Polynomial.derivative (Polynomial.X * Polynomial.C (M (σ x) x)) =
        0 - Polynomial.derivative (Polynomial.X * Polynomial.C (M (σ x) x)) := by
    exact congrArg
      (fun t : Polynomial K =>
        t - Polynomial.derivative (Polynomial.X * Polynomial.C (M (σ x) x)))
      (derivative_polynomial_perm_indicator_eq_zero (K := K) σ x)
  have hmonomial :
      0 - Polynomial.derivative (Polynomial.X * Polynomial.C (M (σ x) x)) =
        0 - Polynomial.C (M (σ x) x) := by
    exact congrArg (fun t : Polynomial K => 0 - t)
      (derivative_X_mul_C (K := K) (M (σ x) x))
  have hneg : 0 - Polynomial.C (M (σ x) x) = -Polynomial.C (M (σ x) x) := by
    exact zero_sub (Polynomial.C (M (σ x) x))
  exact hentry.trans (hsub.trans (hindicator.trans (hmonomial.trans hneg)))

theorem one_sub_X_matrix_perm_diag_product_erase
    (M : Matrix n n K) (σ : Equiv.Perm n) (y : n) :
    (∏ x in Finset.univ.erase y,
        ((1 : Matrix n n (Polynomial K)) -
          (Polynomial.X : Polynomial K) • M.map Polynomial.C) (σ x) x) =
      ∏ x in Finset.univ.erase y,
        ((if σ x = x then 1 else 0) -
          Polynomial.C (M (σ x) x) * Polynomial.X) := by
  exact Finset.prod_congr rfl
    (fun x _ => one_sub_X_matrix_perm_diag_entry (K := K) M σ x)

theorem signed_product_mul_neg_C_eq_signed_neg_product_mul_C
    (ε P C : Polynomial K) :
    ε * (P * (-C)) = ε * (-(P * C)) := by
  exact congrArg (fun t : Polynomial K => ε * t) (mul_neg P C)

theorem derivative_signed_perm_product_eq_signed_erased_product_sum
    (M : Matrix n n K) (σ : Equiv.Perm n) :
    Polynomial.derivative
        (((Equiv.Perm.sign σ : ℤ) : Polynomial K) *
          ∏ x : n,
            ((1 : Matrix n n (Polynomial K)) -
              (Polynomial.X : Polynomial K) • M.map Polynomial.C) (σ x) x) =
      ∑ y : n,
        ((Equiv.Perm.sign σ : ℤ) : Polynomial K) *
          ((∏ x in Finset.univ.erase y,
              ((if σ x = x then 1 else 0) -
                Polynomial.C (M (σ x) x) * Polynomial.X)) *
            (-Polynomial.C (M (σ y) y))) := by
  let A : Matrix n n (Polynomial K) :=
    (1 : Matrix n n (Polynomial K)) -
      (Polynomial.X : Polynomial K) • M.map Polynomial.C
  let ε : Polynomial K := ((Equiv.Perm.sign σ : ℤ) : Polynomial K)
  let raw : n → Polynomial K := fun x => A (σ x) x
  have hsigned :
      Polynomial.derivative (ε * ∏ x : n, raw x) =
        ε * Polynomial.derivative (∏ x : n, raw x) := by
    exact Polynomial.derivative_intCast_mul
      (n := (Equiv.Perm.sign σ : ℤ))
      (f := ∏ x : n, raw x)
  have hprod :
      Polynomial.derivative (∏ x : n, raw x) =
        ∑ y : n,
          (∏ x in Finset.univ.erase y, raw x) *
            Polynomial.derivative (raw y) := by
    exact derivative_finset_prod (K := K) (s := Finset.univ) raw
  have hsubst :
      ε * Polynomial.derivative (∏ x : n, raw x) =
        ε * (∑ y : n,
          (∏ x in Finset.univ.erase y, raw x) *
            Polynomial.derivative (raw y)) := by
    exact congrArg (fun t : Polynomial K => ε * t) hprod
  have hdist :
      ε * (∑ y : n,
          (∏ x in Finset.univ.erase y, raw x) *
            Polynomial.derivative (raw y)) =
        ∑ y : n, ε *
          ((∏ x in Finset.univ.erase y, raw x) *
            Polynomial.derivative (raw y)) := by
    exact Finset.mul_sum
      (s := Finset.univ)
      (f := fun y : n =>
        (∏ x in Finset.univ.erase y, raw x) *
          Polynomial.derivative (raw y))
      (a := ε)
  have hnormalize :
      (∑ y : n, ε *
          ((∏ x in Finset.univ.erase y, raw x) *
            Polynomial.derivative (raw y))) =
        ∑ y : n,
          ((Equiv.Perm.sign σ : ℤ) : Polynomial K) *
            ((∏ x in Finset.univ.erase y,
                ((if σ x = x then 1 else 0) -
                  Polynomial.C (M (σ x) x) * Polynomial.X)) *
              (-Polynomial.C (M (σ y) y))) := by
    exact Finset.sum_congr rfl
      (fun y _ => by
        have hprod_norm :
            (∏ x in Finset.univ.erase y, raw x) =
              ∏ x in Finset.univ.erase y,
                ((if σ x = x then 1 else 0) -
                  Polynomial.C (M (σ x) x) * Polynomial.X) := by
          exact one_sub_X_matrix_perm_diag_product_erase (K := K) M σ y
        have hderiv_norm :
            Polynomial.derivative (raw y) =
              -Polynomial.C (M (σ y) y) := by
          exact derivative_one_sub_X_matrix_perm_diag_entry (K := K) M σ y
        exact congrArg
          (fun t : Polynomial K => ε * t)
          (congrArg₂ Mul.mul hprod_norm hderiv_norm))
  exact hsigned.trans (hsubst.trans (hdist.trans hnormalize))

theorem derivative_leibniz_one_sub_X_matrix_eq_signed_erased_product_sum
    (M : Matrix n n K) :
    Polynomial.derivative
        (∑ σ : Equiv.Perm n,
          ((Equiv.Perm.sign σ : ℤ) : Polynomial K) *
            ∏ x : n,
              ((1 - (Polynomial.X : Polynomial K) • M.map Polynomial.C) (σ x) x)) =
      ∑ σ : Equiv.Perm n, ∑ y : n,
        ((Equiv.Perm.sign σ : ℤ) : Polynomial K) *
          ((∏ x in Finset.univ.erase y,
              ((if σ x = x then 1 else 0) -
                Polynomial.C (M (σ x) x) * Polynomial.X)) *
            (-Polynomial.C (M (σ y) y))) := by
  have hsum :
      Polynomial.derivative
          (∑ σ : Equiv.Perm n,
            ((Equiv.Perm.sign σ : ℤ) : Polynomial K) *
              ∏ x : n,
                ((1 : Matrix n n (Polynomial K)) -
                  (Polynomial.X : Polynomial K) • M.map Polynomial.C) (σ x) x) =
        ∑ σ : Equiv.Perm n,
          Polynomial.derivative
            (((Equiv.Perm.sign σ : ℤ) : Polynomial K) *
              ∏ x : n,
                ((1 : Matrix n n (Polynomial K)) -
                  (Polynomial.X : Polynomial K) • M.map Polynomial.C) (σ x) x) := by
    exact Polynomial.derivative_sum
  have hterms :
      (∑ σ : Equiv.Perm n,
          Polynomial.derivative
            (((Equiv.Perm.sign σ : ℤ) : Polynomial K) *
              ∏ x : n,
                ((1 : Matrix n n (Polynomial K)) -
                  (Polynomial.X : Polynomial K) • M.map Polynomial.C) (σ x) x)) =
        ∑ σ : Equiv.Perm n, ∑ y : n,
          ((Equiv.Perm.sign σ : ℤ) : Polynomial K) *
            ((∏ x in Finset.univ.erase y,
                ((if σ x = x then 1 else 0) -
                  Polynomial.C (M (σ x) x) * Polynomial.X)) *
              (-Polynomial.C (M (σ y) y))) := by
    exact Finset.sum_congr rfl
      (fun σ _ => derivative_signed_perm_product_eq_signed_erased_product_sum (K := K) M σ)
  exact hsum.trans hterms

theorem signed_erased_product_sum_eq_updateColumn_det_sum
    (M : Matrix n n K) :
    (∑ σ : Equiv.Perm n, ∑ y : n,
        ((Equiv.Perm.sign σ : ℤ) : Polynomial K) *
          ((∏ x in Finset.univ.erase y,
              ((if σ x = x then 1 else 0) -
                Polynomial.C (M (σ x) x) * Polynomial.X)) *
            (-Polynomial.C (M (σ y) y)))) =
      ∑ j : n,
        ((1 - (Polynomial.X : Polynomial K) • M.map Polynomial.C).updateColumn j
          (fun i => -Polynomial.C (M i j))).det := by
  have hcomm :
      (∑ σ : Equiv.Perm n, ∑ y : n,
          ((Equiv.Perm.sign σ : ℤ) : Polynomial K) *
            ((∏ x in Finset.univ.erase y,
                ((if σ x = x then 1 else 0) -
                  Polynomial.C (M (σ x) x) * Polynomial.X)) *
              (-Polynomial.C (M (σ y) y)))) =
        ∑ y : n, ∑ σ : Equiv.Perm n,
          ((Equiv.Perm.sign σ : ℤ) : Polynomial K) *
            ((∏ x in Finset.univ.erase y,
                ((if σ x = x then 1 else 0) -
                  Polynomial.C (M (σ x) x) * Polynomial.X)) *
              (-Polynomial.C (M (σ y) y))) := by
    exact Finset.sum_comm
  have hterms :
      (∑ y : n, ∑ σ : Equiv.Perm n,
          ((Equiv.Perm.sign σ : ℤ) : Polynomial K) *
            ((∏ x in Finset.univ.erase y,
                ((if σ x = x then 1 else 0) -
                  Polynomial.C (M (σ x) x) * Polynomial.X)) *
              (-Polynomial.C (M (σ y) y)))) =
        ∑ y : n, ∑ σ : Equiv.Perm n,
          ((Equiv.Perm.sign σ : ℤ) : Polynomial K) *
            (∏ x_2 : n,
              Function.update
                (((1 : Matrix n n (Polynomial K)) -
                  (Polynomial.X : Polynomial K) • M.map Polynomial.C) (σ x_2)) y
                (-Polynomial.C (M (σ x_2) y)) x_2) := by
    exact Finset.sum_congr rfl
      (fun y _ => Finset.sum_congr rfl
        (fun σ _ =>
          let hprod :=
            updateColumn_oneSubXMatrix_perm_product_eq_neg_erased_diag_product
              (K := K) M σ y
          let hproduct_signed :
              ((Equiv.Perm.sign σ : ℤ) : Polynomial K) *
                  (∏ x_2 : n,
                    Function.update
                      (((1 : Matrix n n (Polynomial K)) -
                        (Polynomial.X : Polynomial K) • M.map Polynomial.C) (σ x_2)) y
                      (-Polynomial.C (M (σ x_2) y)) x_2) =
                ((Equiv.Perm.sign σ : ℤ) : Polynomial K) *
                  (-((∏ x_1 in Finset.univ.erase y,
                      ((if σ x_1 = x_1 then 1 else 0) -
                        Polynomial.C (M (σ x_1) x_1) * Polynomial.X)) *
                    Polynomial.C (M (σ y) y))) :=
            congrArg
              (fun t : Polynomial K => ((Equiv.Perm.sign σ : ℤ) : Polynomial K) * t)
              hprod
          let halgebra :
              ((Equiv.Perm.sign σ : ℤ) : Polynomial K) *
                  ((∏ x_1 in Finset.univ.erase y,
                      ((if σ x_1 = x_1 then 1 else 0) -
                        Polynomial.C (M (σ x_1) x_1) * Polynomial.X)) *
                    (-Polynomial.C (M (σ y) y))) =
                ((Equiv.Perm.sign σ : ℤ) : Polynomial K) *
                  (-((∏ x_1 in Finset.univ.erase y,
                      ((if σ x_1 = x_1 then 1 else 0) -
                        Polynomial.C (M (σ x_1) x_1) * Polynomial.X)) *
                    Polynomial.C (M (σ y) y))) :=
            signed_product_mul_neg_C_eq_signed_neg_product_mul_C
              (K := K)
              ((Equiv.Perm.sign σ : ℤ) : Polynomial K)
              (∏ x_1 in Finset.univ.erase y,
                ((if σ x_1 = x_1 then 1 else 0) -
                  Polynomial.C (M (σ x_1) x_1) * Polynomial.X))
              (Polynomial.C (M (σ y) y))
          halgebra.trans hproduct_signed.symm))
  have hdet :
      (∑ y : n, ∑ σ : Equiv.Perm n,
          ((Equiv.Perm.sign σ : ℤ) : Polynomial K) *
            (∏ x_2 : n,
              Function.update
                (((1 : Matrix n n (Polynomial K)) -
                  (Polynomial.X : Polynomial K) • M.map Polynomial.C) (σ x_2)) y
                (-Polynomial.C (M (σ x_2) y)) x_2)) =
        ∑ j : n,
          ((1 - (Polynomial.X : Polynomial K) • M.map Polynomial.C).updateColumn j
            (fun i => -Polynomial.C (M i j))).det := by
    exact Finset.sum_congr rfl
      (fun j _ =>
        (Matrix.det_apply'
          ((1 - (Polynomial.X : Polynomial K) • M.map Polynomial.C).updateColumn j
            (fun i => -Polynomial.C (M i j)))).symm)
  exact hcomm.trans (hterms.trans hdet)

theorem derivative_leibniz_one_sub_X_matrix_eq_updateColumn_det_sum
    (M : Matrix n n K) :
    Polynomial.derivative
        (∑ σ : Equiv.Perm n,
          ((Equiv.Perm.sign σ : ℤ) : Polynomial K) *
            ∏ x : n,
              ((1 - (Polynomial.X : Polynomial K) • M.map Polynomial.C) (σ x) x)) =
      ∑ j : n,
        ((1 - (Polynomial.X : Polynomial K) • M.map Polynomial.C).updateColumn j
          (fun i => -Polynomial.C (M i j))).det := by
  exact (derivative_leibniz_one_sub_X_matrix_eq_signed_erased_product_sum (K := K) M).trans
    (signed_erased_product_sum_eq_updateColumn_det_sum (K := K) M)

theorem derivative_charpolyRev_eq_sum_updateColumn
    (M : Matrix n n K) :
    Polynomial.derivative M.charpolyRev =
      ∑ j : n,
        ((1 - (Polynomial.X : Polynomial K) • M.map Polynomial.C).updateColumn j
          (fun i => -Polynomial.C (M i j))).det := by
  have hcharpoly :
      Polynomial.derivative M.charpolyRev =
        Polynomial.derivative
          ((1 - (Polynomial.X : Polynomial K) • M.map Polynomial.C).det) := by
    exact congrArg Polynomial.derivative
      (charpolyRev_eq_det_one_sub_X_matrix (K := K) M)
  have hdet :
      Polynomial.derivative
          ((1 - (Polynomial.X : Polynomial K) • M.map Polynomial.C).det) =
        Polynomial.derivative
          (∑ σ : Equiv.Perm n,
            ((Equiv.Perm.sign σ : ℤ) : Polynomial K) *
              ∏ x : n,
                ((1 - (Polynomial.X : Polynomial K) • M.map Polynomial.C) (σ x) x)) := by
    exact congrArg Polynomial.derivative
      (Matrix.det_apply'
        (1 - (Polynomial.X : Polynomial K) • M.map Polynomial.C))
  have hpermutation :
      Polynomial.derivative
          (∑ σ : Equiv.Perm n,
            ((Equiv.Perm.sign σ : ℤ) : Polynomial K) *
              ∏ x : n,
                ((1 - (Polynomial.X : Polynomial K) • M.map Polynomial.C) (σ x) x)) =
        ∑ j : n,
          ((1 - (Polynomial.X : Polynomial K) • M.map Polynomial.C).updateColumn j
            (fun i => -Polynomial.C (M i j))).det := by
    exact derivative_leibniz_one_sub_X_matrix_eq_updateColumn_det_sum (K := K) M
  exact hcharpoly.trans (hdet.trans hpermutation)

theorem derivative_charpolyRev_eq_neg_trace_adjugate
    (M : Matrix n n K) :
    Polynomial.derivative M.charpolyRev =
      -(∑ i : n, ∑ j : n,
        Polynomial.C (M i j) *
          (1 - (Polynomial.X : Polynomial K) • M.map Polynomial.C).adjugate j i) := by
  have hupdate :
      Polynomial.derivative M.charpolyRev =
        ∑ j : n,
          ((1 - (Polynomial.X : Polynomial K) • M.map Polynomial.C).updateColumn j
            (fun i => -Polynomial.C (M i j))).det := by
    exact derivative_charpolyRev_eq_sum_updateColumn (K := K) M
  have hdet :
      (∑ j : n,
          ((1 - (Polynomial.X : Polynomial K) • M.map Polynomial.C).updateColumn j
            (fun i => -Polynomial.C (M i j))).det) =
        ∑ j : n, ∑ i : n,
          (-Polynomial.C (M i j)) *
            (1 - (Polynomial.X : Polynomial K) • M.map Polynomial.C).adjugate j i := by
    exact Finset.sum_congr rfl
      (fun j _ =>
        det_updateColumn_eq_sum_mul_adjugate
          (K := K)
          (1 - (Polynomial.X : Polynomial K) • M.map Polynomial.C)
          j
          (fun i => -Polynomial.C (M i j)))
  have hneg_terms :
      (∑ j : n, ∑ i : n,
          (-Polynomial.C (M i j)) *
            (1 - (Polynomial.X : Polynomial K) • M.map Polynomial.C).adjugate j i) =
        ∑ j : n, ∑ i : n,
          -(Polynomial.C (M i j) *
            (1 - (Polynomial.X : Polynomial K) • M.map Polynomial.C).adjugate j i) := by
    exact Finset.sum_congr rfl
      (fun j _ => Finset.sum_congr rfl
        (fun i _ =>
          neg_mul (Polynomial.C (M i j))
            ((1 - (Polynomial.X : Polynomial K) • M.map Polynomial.C).adjugate j i)))
  have hneg_inner :
      (∑ j : n, ∑ i : n,
          -(Polynomial.C (M i j) *
            (1 - (Polynomial.X : Polynomial K) • M.map Polynomial.C).adjugate j i)) =
        ∑ j : n,
          -(∑ i : n,
            Polynomial.C (M i j) *
              (1 - (Polynomial.X : Polynomial K) • M.map Polynomial.C).adjugate j i) := by
    exact Finset.sum_congr rfl
      (fun j _ =>
        Finset.sum_neg_distrib
          (s := Finset.univ)
          (f := fun i : n =>
            Polynomial.C (M i j) *
              (1 - (Polynomial.X : Polynomial K) • M.map Polynomial.C).adjugate j i))
  have hneg_outer :
      (∑ j : n,
          -(∑ i : n,
            Polynomial.C (M i j) *
              (1 - (Polynomial.X : Polynomial K) • M.map Polynomial.C).adjugate j i)) =
        -(∑ j : n, ∑ i : n,
            Polynomial.C (M i j) *
              (1 - (Polynomial.X : Polynomial K) • M.map Polynomial.C).adjugate j i) := by
    exact Finset.sum_neg_distrib
      (s := Finset.univ)
      (f := fun j : n =>
        ∑ i : n,
          Polynomial.C (M i j) *
            (1 - (Polynomial.X : Polynomial K) • M.map Polynomial.C).adjugate j i)
  have hcomm :
      -(∑ j : n, ∑ i : n,
          Polynomial.C (M i j) *
            (1 - (Polynomial.X : Polynomial K) • M.map Polynomial.C).adjugate j i) =
        -(∑ i : n, ∑ j : n,
          Polynomial.C (M i j) *
            (1 - (Polynomial.X : Polynomial K) • M.map Polynomial.C).adjugate j i) := by
    exact congrArg Neg.neg
      (Finset.sum_comm :
        (∑ j : n, ∑ i : n,
          Polynomial.C (M i j) *
            (1 - (Polynomial.X : Polynomial K) • M.map Polynomial.C).adjugate j i) =
          ∑ i : n, ∑ j : n,
            Polynomial.C (M i j) *
              (1 - (Polynomial.X : Polynomial K) • M.map Polynomial.C).adjugate j i)
  exact hupdate.trans
    (hdet.trans (hneg_terms.trans (hneg_inner.trans (hneg_outer.trans hcomm))))

theorem coe_derivative_charpolyRev_eq_coe_neg_trace_adjugate
    (M : Matrix n n K) :
    ((Polynomial.derivative M.charpolyRev : Polynomial K) : K⟦X⟧) =
      ((-(∑ i : n, ∑ j : n,
        Polynomial.C (M i j) *
          (1 - (Polynomial.X : Polynomial K) • M.map Polynomial.C).adjugate j i) :
        Polynomial K) : K⟦X⟧) := by
  exact congrArg (fun p : Polynomial K => (p : K⟦X⟧))
    (derivative_charpolyRev_eq_neg_trace_adjugate (K := K) M)

theorem coe_neg_trace_adjugate_eq_neg_coe_trace_adjugate
    (M : Matrix n n K) :
    ((-(∑ i : n, ∑ j : n,
        Polynomial.C (M i j) *
          (1 - (Polynomial.X : Polynomial K) • M.map Polynomial.C).adjugate j i) :
        Polynomial K) : K⟦X⟧) =
      -(((∑ i : n, ∑ j : n,
        Polynomial.C (M i j) *
          (1 - (Polynomial.X : Polynomial K) • M.map Polynomial.C).adjugate j i :
        Polynomial K) : K⟦X⟧)) := by
  exact map_neg Polynomial.coeToPowerSeries.ringHom
    (∑ i : n, ∑ j : n,
      Polynomial.C (M i j) *
        (1 - (Polynomial.X : Polynomial K) • M.map Polynomial.C).adjugate j i)

theorem neg_coe_trace_adjugate_eq_neg_trace_adjugate_oneSubXMatrix
    (M : Matrix n n K) :
    -(((∑ i : n, ∑ j : n,
        Polynomial.C (M i j) *
          (1 - (Polynomial.X : Polynomial K) • M.map Polynomial.C).adjugate j i :
        Polynomial K) : K⟦X⟧)) =
      -(∑ i : n, ∑ j : n,
        PowerSeries.C K (M i j) *
          (oneSubXMatrix (K := K) M).adjugate j i) := by
  exact congrArg Neg.neg
    (coe_trace_adjugate_eq_trace_adjugate_oneSubXMatrix (K := K) M)

theorem neg_trace_adjugate_oneSubXMatrix_eq_neg_charpolyRev_mul_traceResolventSeries
    (M : Matrix n n K) :
    -(∑ i : n, ∑ j : n,
        PowerSeries.C K (M i j) *
          (oneSubXMatrix (K := K) M).adjugate j i) =
      -((M.charpolyRev : K⟦X⟧) * traceResolventSeries (K := K) M) := by
  exact congrArg Neg.neg
    (charpolyRev_mul_traceResolventSeries_eq_trace_adjugate (K := K) M).symm

theorem derivative_charpolyRev_eq_neg_charpolyRev_mul_traceResolventSeries
    (M : Matrix n n K) :
    ((Polynomial.derivative M.charpolyRev : Polynomial K) : K⟦X⟧) =
      -((M.charpolyRev : K⟦X⟧) * traceResolventSeries (K := K) M) := by
  exact (coe_derivative_charpolyRev_eq_coe_neg_trace_adjugate (K := K) M).trans
    ((coe_neg_trace_adjugate_eq_neg_coe_trace_adjugate (K := K) M).trans
      ((neg_coe_trace_adjugate_eq_neg_trace_adjugate_oneSubXMatrix (K := K) M).trans
        (neg_trace_adjugate_oneSubXMatrix_eq_neg_charpolyRev_mul_traceResolventSeries
          (K := K) M)))

theorem powerSeries_derivative_charpolyRev_eq_neg_charpolyRev_mul_traceResolventSeries
    (M : Matrix n n K) :
    PowerSeries.derivative K (M.charpolyRev : K⟦X⟧) =
      -((M.charpolyRev : K⟦X⟧) * traceResolventSeries (K := K) M) := by
  exact (PowerSeries.derivative_coe (R := K) M.charpolyRev).trans
    (derivative_charpolyRev_eq_neg_charpolyRev_mul_traceResolventSeries (K := K) M)
end MatrixSeries

end

end TraceExpansion
end Boundary
