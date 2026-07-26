import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalization.BoundaryEulerAbel.BoundaryGrowth.OwnerParts.Part11_ZetaTailLogGrowth

/-!
# Boundary growth owner part 12

This file is a mechanical forward-order split of `BoundaryGrowth.Owner`.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open scoped Filter Topology
local notation "π" => Real.pi

/-- A logarithmic zeta estimate on `re = 1` gives the log-linear estimate for the
pole-cleared product `(s - 1)ζ(s)`. -/
theorem boundaryLine_one_zeta_log_growth_bound_to_poleCleared_log_linear_growth_bound
    (hzeta :
      ∃ A : ℝ,
        0 < A ∧
        ∀ w : ℂ,
          w.re = 1 →
          1 ≤ ‖w.im‖ →
          ‖riemannZeta w‖ ≤ A * Real.log (2 + ‖w.im‖)) :
    ∃ A : ℝ,
      0 < A ∧
      ∀ w : ℂ,
        w.re = 1 →
        1 ≤ ‖w.im‖ →
        ‖(w - 1) * riemannZeta w‖ ≤
          A * (1 + ‖w.im‖) * Real.log (2 + ‖w.im‖) := by
  exact Exists.elim hzeta
    (fun A hA =>
      Exists.intro A
        (And.intro hA.left
          (fun w hw_re hw_im =>
            let hpole_norm :
                ‖w - 1‖ ≤ 1 + ‖w.im‖ :=
              boundaryLine_one_sub_one_norm_le_vertical_height hw_re
            let hzeta_norm :
                ‖riemannZeta w‖ ≤ A * Real.log (2 + ‖w.im‖) :=
              hA.right w hw_re hw_im
            let hheight_nonneg : 0 ≤ 1 + ‖w.im‖ :=
              le_trans zero_le_one (le_add_of_nonneg_right (norm_nonneg w.im))
            let hmul :
                ‖w - 1‖ * ‖riemannZeta w‖ ≤
                  (1 + ‖w.im‖) * (A * Real.log (2 + ‖w.im‖)) :=
              mul_le_mul hpole_norm hzeta_norm (norm_nonneg (riemannZeta w)) hheight_nonneg
            let htarget_eq :
                (1 + ‖w.im‖) * (A * Real.log (2 + ‖w.im‖)) =
                  A * (1 + ‖w.im‖) * Real.log (2 + ‖w.im‖) := by
              calc
                (1 + ‖w.im‖) * (A * Real.log (2 + ‖w.im‖)) =
                    ((1 + ‖w.im‖) * A) * Real.log (2 + ‖w.im‖) := by
                  exact (mul_assoc (1 + ‖w.im‖) A (Real.log (2 + ‖w.im‖))).symm
                _ =
                    (A * (1 + ‖w.im‖)) * Real.log (2 + ‖w.im‖) := by
                  exact congrArg
                    (fun x : ℝ => x * Real.log (2 + ‖w.im‖))
                    (mul_comm (1 + ‖w.im‖) A)
                _ =
                    A * (1 + ‖w.im‖) * Real.log (2 + ‖w.im‖) := by
                  exact rfl
            let hnorm_eq :
                ‖(w - 1) * riemannZeta w‖ = ‖w - 1‖ * ‖riemannZeta w‖ :=
              norm_mul (w - 1) (riemannZeta w)
            Eq.subst
              (motive := fun x : ℝ =>
                ‖(w - 1) * riemannZeta w‖ ≤ x)
              htarget_eq
              (Eq.subst
                (motive := fun x : ℝ => x ≤
                  (1 + ‖w.im‖) * (A * Real.log (2 + ‖w.im‖)))
                hnorm_eq.symm
                hmul))))

/-- Classical logarithmic vertical growth of zeta on the boundary line `re = 1`, proved
by Euler-Maclaurin/Abel truncation.

This is the exact analytic number-theory input: truncate the Dirichlet series at
height comparable to `|t|`, control the tail by Abel summation or Euler-Maclaurin,
and derive the standard `O(log (2 + |t|))` boundary-line bound. -/
theorem classicalZeta_boundaryLine_one_vertical_log_growth_bound_from_EulerMaclaurin_truncation :
    ∃ A : ℝ,
      0 < A ∧
      ∀ w : ℂ,
        w.re = 1 →
        1 ≤ ‖w.im‖ →
        boundaryLineOneVerticalTruncationHypotheses w →
        ‖riemannZeta w‖ ≤ A * Real.log (2 + ‖w.im‖) := by
  exact Exists.elim
    classicalZeta_boundaryLineOneZetaRealParam_vertical_log_growth_bound_from_EulerMaclaurin_truncation
    (fun A hA =>
      Exists.intro A
        (And.intro hA.left
          (fun w hw_re hw_im htrunc =>
            Eq.subst
              (motive := fun x : ℝ => x ≤ A * Real.log (2 + ‖w.im‖))
              (norm_riemannZeta_boundaryLine_one_eq_norm_realParam hw_re).symm
              (hA.right w.im hw_im htrunc.left htrunc.right))))

/-- Classical logarithmic vertical growth of zeta on the boundary line `re = 1`, in the
standard partial-summation/truncation form. -/
theorem classicalZeta_boundaryLine_one_vertical_log_growth_bound_from_truncation :
    ∃ A : ℝ,
      0 < A ∧
      ∀ w : ℂ,
        w.re = 1 →
        1 ≤ ‖w.im‖ →
        boundaryLineOneVerticalTruncationHypotheses w →
        ‖riemannZeta w‖ ≤ A * Real.log (2 + ‖w.im‖) := by
  exact
    classicalZeta_boundaryLine_one_vertical_log_growth_bound_from_EulerMaclaurin_truncation

/-- Classical log-linear vertical growth of the pole-cleared zeta factor on the boundary
line `re = 1`, obtained from the raw boundary-line zeta estimate and the elementary
pole-clearing factor. -/
theorem classicalZeta_poleCleared_boundaryLine_one_vertical_log_linear_growth_bound_from_truncation :
    ∃ A : ℝ,
      0 < A ∧
      ∀ w : ℂ,
        w.re = 1 →
        1 ≤ ‖w.im‖ →
        boundaryLineOneVerticalTruncationHypotheses w →
        ‖(w - 1) * riemannZeta w‖ ≤
          A * (1 + ‖w.im‖) * Real.log (2 + ‖w.im‖) := by
  exact Exists.elim
    classicalZeta_boundaryLine_one_vertical_log_growth_bound_from_truncation
    (fun A hA =>
      Exists.intro A
        (And.intro hA.left
          (fun w hw_re hw_im htrunc =>
            let hpole_norm :
                ‖w - 1‖ ≤ 1 + ‖w.im‖ :=
              boundaryLine_one_sub_one_norm_le_vertical_height hw_re
            let hzeta_norm :
                ‖riemannZeta w‖ ≤ A * Real.log (2 + ‖w.im‖) :=
              hA.right w hw_re hw_im htrunc
            let hheight_nonneg : 0 ≤ 1 + ‖w.im‖ :=
              le_trans zero_le_one (le_add_of_nonneg_right (norm_nonneg w.im))
            let hmul :
                ‖w - 1‖ * ‖riemannZeta w‖ ≤
                  (1 + ‖w.im‖) * (A * Real.log (2 + ‖w.im‖)) :=
              mul_le_mul hpole_norm hzeta_norm (norm_nonneg (riemannZeta w)) hheight_nonneg
            let htarget_eq :
                (1 + ‖w.im‖) * (A * Real.log (2 + ‖w.im‖)) =
                  A * (1 + ‖w.im‖) * Real.log (2 + ‖w.im‖) := by
              calc
                (1 + ‖w.im‖) * (A * Real.log (2 + ‖w.im‖)) =
                    ((1 + ‖w.im‖) * A) * Real.log (2 + ‖w.im‖) := by
                  exact (mul_assoc (1 + ‖w.im‖) A (Real.log (2 + ‖w.im‖))).symm
                _ = (A * (1 + ‖w.im‖)) * Real.log (2 + ‖w.im‖) := by
                  exact congrArg
                    (fun x : ℝ => x * Real.log (2 + ‖w.im‖))
                    (mul_comm (1 + ‖w.im‖) A)
                _ = A * (1 + ‖w.im‖) * Real.log (2 + ‖w.im‖) := by
                  rfl
            let hnorm_eq :
                ‖(w - 1) * riemannZeta w‖ =
                  ‖w - 1‖ * ‖riemannZeta w‖ :=
              norm_mul (w - 1) (riemannZeta w)
            Eq.subst
              (motive := fun x : ℝ =>
                ‖(w - 1) * riemannZeta w‖ ≤ x)
              htarget_eq
              (Eq.subst
                (motive := fun x : ℝ => x ≤
                  (1 + ‖w.im‖) * (A * Real.log (2 + ‖w.im‖)))
                hnorm_eq.symm
                hmul))))

/-- The logarithmic boundary-line zeta estimate gives the log-linear estimate for the
pole-cleared product `(s - 1)ζ(s)`. -/
theorem classicalZeta_poleCleared_boundaryLine_one_vertical_log_linear_growth_bound_of_zeta_log
    (hzeta :
      ∃ A : ℝ,
        0 < A ∧
        ∀ w : ℂ,
          w.re = 1 →
          1 ≤ ‖w.im‖ →
          ‖riemannZeta w‖ ≤ A * Real.log (2 + ‖w.im‖)) :
    ∃ A : ℝ,
      0 < A ∧
      ∀ w : ℂ,
        w.re = 1 →
        1 ≤ ‖w.im‖ →
        ‖(w - 1) * riemannZeta w‖ ≤
          A * (1 + ‖w.im‖) * Real.log (2 + ‖w.im‖) := by
  exact boundaryLine_one_zeta_log_growth_bound_to_poleCleared_log_linear_growth_bound hzeta

/-- Classical log-linear vertical growth of the pole-cleared zeta factor on the boundary
line `re = 1`.  This is the standard boundary-line zeta estimate in the form needed before
coarsening to a finite polynomial envelope. -/
theorem classicalZeta_poleCleared_boundaryLine_one_vertical_log_linear_growth_bound :
    ∃ A : ℝ,
      0 < A ∧
      ∀ w : ℂ,
        w.re = 1 →
        1 ≤ ‖w.im‖ →
        boundaryLineOneVerticalTruncationHypotheses w →
        ‖(w - 1) * riemannZeta w‖ ≤
          A * (1 + ‖w.im‖) * Real.log (2 + ‖w.im‖) := by
  exact classicalZeta_poleCleared_boundaryLine_one_vertical_log_linear_growth_bound_from_truncation

/-- A conditional log-linear vertical-height boundary estimate gives the coarser
conditional polynomial envelope used by the normalization chain. -/
theorem boundaryLine_one_log_linear_growth_bound_to_polynomial_growth_bound
    {f : ℂ → ℂ}
    (P : ℂ → Prop)
    (hlog :
      ∃ A : ℝ,
        0 < A ∧
        ∀ w : ℂ,
          w.re = 1 →
          1 ≤ ‖w.im‖ →
          P w →
          ‖f w‖ ≤ A * (1 + ‖w.im‖) * Real.log (2 + ‖w.im‖)) :
    ∃ A : ℝ, ∃ m : ℕ,
      0 < A ∧
      ∀ w : ℂ,
        w.re = 1 →
        1 ≤ ‖w.im‖ →
        P w →
        ‖f w‖ ≤ A * (1 + ‖w.im‖) ^ m := by
  exact Exists.elim hlog
    (fun A hA =>
      Exists.intro (2 * A)
        (Exists.intro 2
          (And.intro
            (mul_pos two_pos hA.left)
            (fun w hw_re hw_im hP =>
              let H : ℝ := 1 + ‖w.im‖
              let hH_nonneg : 0 ≤ H :=
                le_trans zero_le_one (le_add_of_nonneg_right (norm_nonneg w.im))
              let hlog_arg_pos : 0 < 2 + ‖w.im‖ :=
                add_pos_of_pos_of_nonneg zero_lt_two (norm_nonneg w.im)
              let hlog_le_arg :
                  Real.log (2 + ‖w.im‖) ≤ 2 + ‖w.im‖ :=
                Real.log_le_self hlog_arg_pos.le
              let hnorm_le_two_norm : ‖w.im‖ ≤ 2 * ‖w.im‖ := by
                calc
                  ‖w.im‖ = 1 * ‖w.im‖ := by
                    exact (one_mul ‖w.im‖).symm
                  _ ≤ 2 * ‖w.im‖ :=
                    mul_le_mul_of_nonneg_right one_le_two (norm_nonneg w.im)
              let harg_le_twoH : 2 + ‖w.im‖ ≤ 2 * H := by
                calc
                  2 + ‖w.im‖ ≤ 2 + 2 * ‖w.im‖ :=
                    add_le_add_left hnorm_le_two_norm 2
                  _ = 2 * (1 + ‖w.im‖) := by
                    calc
                      2 + 2 * ‖w.im‖ = 2 * 1 + 2 * ‖w.im‖ := by
                        exact congrArg (fun y : ℝ => y + 2 * ‖w.im‖)
                          (mul_one 2).symm
                      _ = 2 * (1 + ‖w.im‖) :=
                        (left_distrib 2 1 ‖w.im‖).symm
                  _ = 2 * H := rfl
              let hlog_le_twoH :
                  Real.log (2 + ‖w.im‖) ≤ 2 * H :=
                le_trans hlog_le_arg harg_le_twoH
              let hleft_nonneg : 0 ≤ A * H :=
                mul_nonneg (le_of_lt hA.left) hH_nonneg
              let hmul_log_le :
                  A * H * Real.log (2 + ‖w.im‖) ≤ A * H * (2 * H) :=
                mul_le_mul_of_nonneg_left hlog_le_twoH hleft_nonneg
              let htarget_eq :
                  A * H * (2 * H) = (2 * A) * H ^ (2 : ℕ) := by
                calc
                  A * H * (2 * H) = (A * H * 2) * H := by
                    exact (mul_assoc (A * H) 2 H).symm
                  _ = (2 * (A * H)) * H := by
                    exact congrArg (fun x : ℝ => x * H) (mul_comm (A * H) 2)
                  _ = ((2 * A) * H) * H := by
                    exact congrArg (fun x : ℝ => x * H) (mul_assoc 2 A H).symm
                  _ = (2 * A) * (H * H) := by
                    exact mul_assoc (2 * A) H H
                  _ = (2 * A) * H ^ (2 : ℕ) := by
                    exact congrArg (fun x : ℝ => (2 * A) * x) (pow_two H).symm
              le_trans (hA.right w hw_re hw_im hP)
                (Eq.subst
                  (motive := fun x : ℝ =>
                    A * H * Real.log (2 + ‖w.im‖) ≤ x)
                  htarget_eq
                  hmul_log_le)))))

/-- A conditional polynomial vertical-height boundary estimate gives the
conditional exponential finite-order envelope in the same vertical-height
variable. -/
theorem boundaryLine_one_polynomial_growth_bound_to_exponential_growth_bound_of_condition
    {f : ℂ → ℂ}
    (P : ℂ → Prop)
    (hpoly :
      ∃ A : ℝ, ∃ m : ℕ,
        0 < A ∧
        ∀ w : ℂ,
          w.re = 1 →
          1 ≤ ‖w.im‖ →
          P w →
          ‖f w‖ ≤ A * (1 + ‖w.im‖) ^ m) :
    ∃ A : ℝ, ∃ B : ℝ, ∃ m : ℕ,
      0 < A ∧
      0 < B ∧
      ∀ w : ℂ,
        w.re = 1 →
        1 ≤ ‖w.im‖ →
        P w →
        ‖f w‖ ≤ A * Real.exp (B * (1 + ‖w.im‖) ^ m) := by
  exact match hpoly with
    | ⟨A, m, hA_pos, hbound⟩ =>
      ⟨A, 1, m, hA_pos, zero_lt_one, fun w hw_re hw_im hP => by
        let H : ℝ := (1 + ‖w.im‖) ^ m
        have hH_nonneg : 0 ≤ H :=
          pow_nonneg
            (le_trans zero_le_one (le_add_of_nonneg_right (norm_nonneg w.im)))
            m
        have hH_le_exp : H ≤ Real.exp ((1 : ℝ) * H) := by
          have hone_mul : (1 : ℝ) * H = H := by
            exact one_mul H
          have hH_le_H_add_one : H ≤ H + 1 :=
            le_add_of_nonneg_right zero_le_one
          have hH_add_one_le_exp : H + 1 ≤ Real.exp H :=
            Real.add_one_le_exp H
          have hH_le_exp_H : H ≤ Real.exp H :=
            le_trans hH_le_H_add_one hH_add_one_le_exp
          exact Eq.subst
            (motive := fun x : ℝ => H ≤ Real.exp x)
            hone_mul.symm
            hH_le_exp_H
        have hscaled :
            A * H ≤ A * Real.exp ((1 : ℝ) * H) :=
          mul_le_mul_of_nonneg_left hH_le_exp (le_of_lt hA_pos)
        exact le_trans (hbound w hw_re hw_im hP) hscaled⟩

/-- Standard polynomial vertical growth of the pole-cleared zeta factor on the boundary
line `re = 1`.

This is the classical boundary-line estimate for the removable meromorphic factor
`(s - 1)ζ(s)`, stated before conversion to the coarser finite-order envelope. -/
theorem riemannZeta_poleCleared_boundaryLine_one_vertical_polynomial_growth_bound_standard :
    ∃ A : ℝ, ∃ m : ℕ,
      0 < A ∧
      ∀ w : ℂ,
        w.re = 1 →
        1 ≤ ‖w.im‖ →
        boundaryLineOneVerticalTruncationHypotheses w →
        ‖(w - 1) * riemannZeta w‖ ≤
          A * (1 + ‖w.im‖) ^ m := by
  exact boundaryLine_one_log_linear_growth_bound_to_polynomial_growth_bound
    boundaryLineOneVerticalTruncationHypotheses
    classicalZeta_poleCleared_boundaryLine_one_vertical_log_linear_growth_bound

/-- The boundary polynomial estimate with its Abel-tail input discharged at
the real-parameter owner level. -/
theorem riemannZeta_poleCleared_boundaryLine_one_vertical_polynomial_growth_bound_owner :
    ∃ A : ℝ, ∃ m : ℕ,
      0 < A ∧
      ∀ w : ℂ,
        w.re = 1 →
        1 ≤ ‖w.im‖ →
        ‖(w - 1) * riemannZeta w‖ ≤
          A * (1 + ‖w.im‖) ^ m := by
  match riemannZeta_poleCleared_boundaryLine_one_vertical_polynomial_growth_bound_standard with
  | ⟨A, m, hA, hbound⟩ =>
      exact ⟨A, m, hA, fun w hw ht =>
        hbound w hw ht (boundaryLineOneVerticalTruncationHypotheses_owner w hw ht)⟩

/-- Standard finite-order vertical growth of the pole-cleared zeta factor on the boundary
line `re = 1`, converted from the polynomial boundary-line estimate.

This is the zeta-side finite-order theorem that must come from boundary-line estimates
for the pole-cleared meromorphic zeta function, not from the false far-right `re = 2`
Dirichlet-series route. -/
theorem riemannZeta_poleCleared_boundaryLine_one_vertical_growth_bound_standard :
    ∃ A : ℝ, ∃ B : ℝ, ∃ m : ℕ,
      0 < A ∧
      0 < B ∧
      ∀ w : ℂ,
        w.re = 1 →
        1 ≤ ‖w.im‖ →
        boundaryLineOneVerticalTruncationHypotheses w →
        ‖(w - 1) * riemannZeta w‖ ≤
          A * Real.exp (B * (1 + ‖w.im‖) ^ m) := by
  exact boundaryLine_one_polynomial_growth_bound_to_exponential_growth_bound_of_condition
    boundaryLineOneVerticalTruncationHypotheses
    riemannZeta_poleCleared_boundaryLine_one_vertical_polynomial_growth_bound_standard

/-- The finite-order boundary estimate with the Abel-tail condition discharged
by the boundary owner. -/
theorem riemannZeta_poleCleared_boundaryLine_one_vertical_growth_bound_owner :
    ∃ A : ℝ, ∃ B : ℝ, ∃ m : ℕ,
      0 < A ∧
      0 < B ∧
      ∀ w : ℂ,
        w.re = 1 →
        1 ≤ ‖w.im‖ →
        ‖(w - 1) * riemannZeta w‖ ≤
          A * Real.exp (B * (1 + ‖w.im‖) ^ m) := by
  match riemannZeta_poleCleared_boundaryLine_one_vertical_growth_bound_standard with
  | ⟨A, B, m, hA, hB, hbound⟩ =>
      exact ⟨A, B, m, hA, hB, fun w hw ht =>
        hbound w hw ht (boundaryLineOneVerticalTruncationHypotheses_owner w hw ht)⟩

/-- The standard vertical-height finite-order estimate for `(s - 1)ζ(s)` on `re = 1`
implies the complex-height envelope consumed by the strip-normalization chain. -/
theorem riemannZeta_poleCleared_boundaryLine_one_growth_bound_of_vertical_growth
    (hvertical :
      ∃ A : ℝ, ∃ B : ℝ, ∃ m : ℕ,
        0 < A ∧
        0 < B ∧
        ∀ w : ℂ,
          w.re = 1 →
          1 ≤ ‖w.im‖ →
          boundaryLineOneVerticalTruncationHypotheses w →
          ‖(w - 1) * riemannZeta w‖ ≤
            A * Real.exp (B * (1 + ‖w.im‖) ^ m)) :
    ∃ A : ℝ, ∃ B : ℝ, ∃ m : ℕ,
      0 < A ∧
      0 < B ∧
      ∀ w : ℂ,
        w.re = 1 →
        1 ≤ ‖w.im‖ →
        boundaryLineOneVerticalTruncationHypotheses w →
        ‖(w - 1) * riemannZeta w‖ ≤
          A * Real.exp (B * (1 + ‖w‖) ^ m) := by
  exact Exists.elim hvertical
    (fun A hA_tail =>
      Exists.elim hA_tail
        (fun B hB_tail =>
          Exists.elim hB_tail
            (fun m hdata =>
              Exists.intro A
                (Exists.intro B
                  (Exists.intro m
                    (And.intro hdata.left
                      (And.intro hdata.right.left
                        (fun w hw_re hw_im htrunc =>
                          le_trans (hdata.right.right w hw_re hw_im htrunc)
                            (finiteOrder_vertical_envelope_le_complex_envelope
                              (le_of_lt hdata.left)
                              (le_of_lt hdata.right.left))))))))))

/-- Standard finite-order vertical growth of the pole-cleared zeta factor on the boundary
line `re = 1`, in the complex-height envelope used downstream. -/
theorem riemannZeta_poleCleared_boundaryLine_one_growth_bound_standard :
    ∃ A : ℝ, ∃ B : ℝ, ∃ m : ℕ,
      0 < A ∧
      0 < B ∧
      ∀ w : ℂ,
        w.re = 1 →
        1 ≤ ‖w.im‖ →
        boundaryLineOneVerticalTruncationHypotheses w →
        ‖(w - 1) * riemannZeta w‖ ≤
          A * Real.exp (B * (1 + ‖w‖) ^ m) := by
  exact riemannZeta_poleCleared_boundaryLine_one_growth_bound_of_vertical_growth
    riemannZeta_poleCleared_boundaryLine_one_vertical_growth_bound_standard

/-- The removable pole-cleared boundary-line estimate implies the raw
`(s - 1)ζ(s)` boundary-line estimate on the vertical tail.

The vertical-tail hypothesis excludes the removable point `1`, so the raw product and
`poleClearedRiemannZeta` agree there. -/
theorem riemannZeta_boundaryLine_one_raw_growth_bound_of_poleCleared_growth_bound
    (hpole :
      ∃ A : ℝ, ∃ B : ℝ, ∃ m : ℕ,
        0 < A ∧
        0 < B ∧
        ∀ w : ℂ,
          w.re = 1 →
          1 ≤ ‖w.im‖ →
          ‖poleClearedRiemannZeta w‖ ≤
            A * Real.exp (B * (1 + ‖w‖) ^ m)) :
    ∃ A : ℝ, ∃ B : ℝ, ∃ m : ℕ,
      0 < A ∧
      0 < B ∧
      ∀ w : ℂ,
        w.re = 1 →
        1 ≤ ‖w.im‖ →
        ‖(w - 1) * riemannZeta w‖ ≤
          A * Real.exp (B * (1 + ‖w‖) ^ m) := by
  exact Exists.elim hpole
    (fun A hA_tail =>
      Exists.elim hA_tail
        (fun B hB_tail =>
          Exists.elim hB_tail
            (fun m hdata =>
              Exists.intro A
                (Exists.intro B
                  (Exists.intro m
                    (And.intro hdata.left
                      (And.intro hdata.right.left
                        (fun w hw_re hw_im =>
                          let hw_ne_one : w ≠ 1 :=
                            fun hw =>
                              have him_zero : w.im = 0 := by
                                calc
                                  w.im = (1 : ℂ).im := by
                                    exact congrArg Complex.im hw
                                  _ = 0 := by
                                    exact Complex.one_im
                              have him_norm_zero : ‖w.im‖ = 0 := by
                                calc
                                  ‖w.im‖ = ‖(0 : ℝ)‖ := by
                                    exact congrArg norm him_zero
                                  _ = 0 := by
                                    exact norm_zero
                              have hone_le_zero : (1 : ℝ) ≤ 0 :=
                                Eq.subst
                                  (motive := fun x : ℝ => (1 : ℝ) ≤ x)
                                  him_norm_zero
                                  hw_im
                              not_lt_of_ge hone_le_zero zero_lt_one
                          let hpole_eq :
                              poleClearedRiemannZeta w =
                                (w - 1) * riemannZeta w :=
                            poleClearedRiemannZeta_eq_of_ne_one hw_ne_one
                          Eq.subst
                            (motive := fun x : ℂ =>
                              ‖x‖ ≤ A * Real.exp (B * (1 + ‖w‖) ^ m))
                            hpole_eq
                            (hdata.right.right w hw_re hw_im)))))))))

/-- Pole-cleared zeta has finite-order vertical growth on the boundary line `re = 1`.

This is the smallest zeta-side analytic primitive needed on the reflected left boundary:
reflection sends `re z = 0` to `re (1 - z) = 1`, not to the `re = 2`
Dirichlet-series boundary. -/
theorem poleClearedRiemannZeta_boundaryLine_one_growth_bound_standard :
    ∃ A : ℝ, ∃ B : ℝ, ∃ m : ℕ,
      0 < A ∧
      0 < B ∧
      ∀ w : ℂ,
        w.re = 1 →
        1 ≤ ‖w.im‖ →
        boundaryLineOneVerticalTruncationHypotheses w →
        ‖poleClearedRiemannZeta w‖ ≤
          A * Real.exp (B * (1 + ‖w‖) ^ m) := by
  exact Exists.elim riemannZeta_poleCleared_boundaryLine_one_growth_bound_standard
    (fun A hA_tail =>
      Exists.elim hA_tail
        (fun B hB_tail =>
          Exists.elim hB_tail
            (fun m hdata =>
              Exists.intro A
                (Exists.intro B
                  (Exists.intro m
                    (And.intro hdata.left
                      (And.intro hdata.right.left
                        (fun w hw_re hw_im htrunc =>
                          let hw_ne_one : w ≠ 1 :=
                            fun hw =>
                              have him_zero : w.im = 0 := by
                                calc
                                  w.im = (1 : ℂ).im := by
                                    exact congrArg Complex.im hw
                                  _ = 0 := by
                                    exact Complex.one_im
                              have him_norm_zero : ‖w.im‖ = 0 := by
                                calc
                                  ‖w.im‖ = ‖(0 : ℝ)‖ := by
                                    exact congrArg norm him_zero
                                  _ = 0 := by
                                    exact norm_zero
                              have hone_le_zero : (1 : ℝ) ≤ 0 :=
                                Eq.subst
                                  (motive := fun x : ℝ => (1 : ℝ) ≤ x)
                                  him_norm_zero
                                  hw_im
                              not_lt_of_ge hone_le_zero zero_lt_one
                          let hpole_eq :
                              poleClearedRiemannZeta w =
                                (w - 1) * riemannZeta w :=
                            poleClearedRiemannZeta_eq_of_ne_one hw_ne_one
                          Eq.subst
                            (motive := fun x : ℂ =>
                              ‖x‖ ≤ A * Real.exp (B * (1 + ‖w‖) ^ m))
                            hpole_eq.symm
                            (hdata.right.right w hw_re hw_im htrunc)))))))))


end

end LFunctions
end Boundary
