import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ClassicalAnalysis.ZetaEulerMaclaurinBoundary.BoundaryGrowth

/-!
# Pole-cleared Euler-Maclaurin boundary growth

This file owns the boundary-line polynomial growth estimate for
`(s - 1) ζ(s)` exported to completed-normalization consumers.
-/

namespace Boundary
namespace LFunctions

noncomputable section

/-- A logarithmic boundary-line zeta bound gives polynomial growth for the
pole-cleared product `(s - 1)ζ(s)` on `s = 1 + it`. -/
theorem Complex.poleClearedRiemannZeta_boundaryLine_growth_bound_of_zeta_log :
    ∃ A : ℝ, ∃ m : ℕ,
      0 < A ∧
      ∀ t : ℝ,
        1 ≤ ‖t‖ →
          Complex.boundaryLineOnePointRealParam_cutoffPhasePartialSumBound t →
          ‖((Complex.boundaryLineOnePointRealParam t - 1) *
              riemannZeta (Complex.boundaryLineOnePointRealParam t))‖ ≤
            A * (1 + ‖t‖) ^ m := by
  exact
    match Complex.riemannZeta_boundaryLine_log_bound with
    | ⟨A, hA_pos, hzeta⟩ =>
        Exists.intro (2 * A)
          (Exists.intro 2
            (And.intro (mul_pos two_pos hA_pos)
              (fun t ht hphase => by
                let H : ℝ := 1 + ‖t‖
                have hH_nonneg : 0 ≤ H :=
                  le_trans zero_le_one (le_add_of_nonneg_right (norm_nonneg t))
                have ht_nonneg : 0 ≤ ‖t‖ :=
                  norm_nonneg t
                have ht_le_H : ‖t‖ ≤ H :=
                  le_add_of_nonneg_left zero_le_one
                have hpoint_sub :
                    Complex.boundaryLineOnePointRealParam t - 1 = (t : ℂ) * Complex.I := by
                  calc
                    Complex.boundaryLineOnePointRealParam t - 1 =
                        ((1 : ℂ) + (t : ℂ) * Complex.I) - 1 := by
                      rfl
                    _ = (t : ℂ) * Complex.I := by
                      exact add_sub_cancel_left ((t : ℂ) * Complex.I) (1 : ℂ)
                have hpoint_norm :
                    ‖Complex.boundaryLineOnePointRealParam t - 1‖ = ‖t‖ := by
                  calc
                    ‖Complex.boundaryLineOnePointRealParam t - 1‖ =
                        ‖(t : ℂ) * Complex.I‖ := by
                      exact congrArg norm hpoint_sub
                    _ = ‖(t : ℂ)‖ * ‖Complex.I‖ :=
                      norm_mul (t : ℂ) Complex.I
                    _ = ‖(t : ℂ)‖ * 1 := by
                      exact congrArg (fun x : ℝ => ‖(t : ℂ)‖ * x) norm_I
                    _ = ‖(t : ℂ)‖ :=
                      mul_one ‖(t : ℂ)‖
                    _ = ‖t‖ :=
                      RCLike.norm_ofReal t
                have hzeta_bound :
                    ‖riemannZeta (Complex.boundaryLineOnePointRealParam t)‖ ≤
                      A * Real.log (2 + ‖t‖) :=
                  hzeta t ht hphase
                have hlog_arg_pos : 0 < 2 + ‖t‖ :=
                  add_pos_of_pos_of_nonneg two_pos ht_nonneg
                have hlog_le_arg :
                    Real.log (2 + ‖t‖) ≤ 2 + ‖t‖ :=
                  Real.log_le_self hlog_arg_pos.le
                have harg_eq : 2 + ‖t‖ = H + 1 := by
                  calc
                    2 + ‖t‖ = (1 + 1) + ‖t‖ := by
                      rfl
                    _ = 1 + (1 + ‖t‖) := by
                      exact (add_assoc (1 : ℝ) 1 ‖t‖).symm
                    _ = (1 + ‖t‖) + 1 := by
                      exact add_comm (1 : ℝ) (1 + ‖t‖)
                    _ = H + 1 := by
                      rfl
                have harg_le_twoH : 2 + ‖t‖ ≤ 2 * H := by
                  calc
                    2 + ‖t‖ = H + 1 :=
                      harg_eq
                    _ ≤ H + H :=
                      add_le_add_left (by
                        calc
                          (1 : ℝ) ≤ 1 + ‖t‖ :=
                            le_add_of_nonneg_right ht_nonneg
                          _ = H := by
                            rfl) H
                    _ = 2 * H := by
                      exact (two_mul H).symm
                have hlog_le_twoH :
                    Real.log (2 + ‖t‖) ≤ 2 * H :=
                  le_trans hlog_le_arg harg_le_twoH
                have hzeta_le :
                    ‖riemannZeta (Complex.boundaryLineOnePointRealParam t)‖ ≤
                      A * (2 * H) := by
                  exact le_trans hzeta_bound
                    (mul_le_mul_of_nonneg_left hlog_le_twoH (le_of_lt hA_pos))
                have hproduct_norm :
                    ‖(Complex.boundaryLineOnePointRealParam t - 1) *
                        riemannZeta (Complex.boundaryLineOnePointRealParam t)‖ =
                      ‖Complex.boundaryLineOnePointRealParam t - 1‖ *
                        ‖riemannZeta (Complex.boundaryLineOnePointRealParam t)‖ :=
                  norm_mul
                    (Complex.boundaryLineOnePointRealParam t - 1)
                    (riemannZeta (Complex.boundaryLineOnePointRealParam t))
                have hmul_bound :
                    ‖Complex.boundaryLineOnePointRealParam t - 1‖ *
                        ‖riemannZeta (Complex.boundaryLineOnePointRealParam t)‖ ≤
                      H * (A * (2 * H)) := by
                  exact mul_le_mul
                    (le_trans (le_of_eq hpoint_norm) ht_le_H)
                    hzeta_le
                    (mul_nonneg (le_of_lt hA_pos) (mul_nonneg zero_le_two hH_nonneg))
                    hH_nonneg
                have htarget :
                    H * (A * (2 * H)) = (2 * A) * H ^ (2 : ℕ) := by
                  calc
                    H * (A * (2 * H)) = H * ((A * 2) * H) := by
                      exact congrArg (fun x : ℝ => H * x) (mul_assoc A 2 H).symm
                    _ = (H * (A * 2)) * H := by
                      exact mul_assoc H (A * 2) H
                    _ = ((A * 2) * H) * H := by
                      exact congrArg (fun x : ℝ => x * H) (mul_comm H (A * 2))
                    _ = (A * 2) * (H * H) := by
                      exact (mul_assoc (A * 2) H H).symm
                    _ = (2 * A) * (H * H) := by
                      exact congrArg (fun x : ℝ => x * (H * H)) (mul_comm A 2)
                    _ = (2 * A) * H ^ (2 : ℕ) := by
                      rfl
                exact Eq.subst
                  (motive := fun x : ℝ =>
                    ‖(Complex.boundaryLineOnePointRealParam t - 1) *
                        riemannZeta (Complex.boundaryLineOnePointRealParam t)‖ ≤ x)
                  htarget
                  (Eq.subst
                    (motive := fun x : ℝ => x ≤ H * (A * (2 * H)))
                    hproduct_norm.symm
                    hmul_bound))))

/-- Pole-cleared boundary-line polynomial growth in the right critical strip,
as exported to completed normalization. -/
theorem Complex.poleClearedRiemannZeta_boundaryLine_growth_bound :
    ∃ A : ℝ, ∃ m : ℕ,
      0 < A ∧
      ∀ t : ℝ,
        1 ≤ ‖t‖ →
          Complex.boundaryLineOnePointRealParam_cutoffPhasePartialSumBound t →
          ‖((Complex.boundaryLineOnePointRealParam t - 1) *
              riemannZeta (Complex.boundaryLineOnePointRealParam t))‖ ≤
            A * (1 + ‖t‖) ^ m := by
  exact Complex.poleClearedRiemannZeta_boundaryLine_growth_bound_of_zeta_log

end

end LFunctions
end Boundary
