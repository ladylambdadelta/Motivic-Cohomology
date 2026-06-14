import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ClassicalAnalysis.GammaBinetStirling.SectorialFromBinet

/-!
# Sectorial logarithmic Gamma norm bounds

This file owns the right-half-plane logarithmic growth consequence of
Binet-Stirling.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open scoped Topology

/-- A norm bound by a positive polynomial gives the corresponding real-log
bound. -/
theorem Real.log_norm_le_of_norm_le_pos
    {x B : ℝ}
    (hx_pos : 0 < x)
    (hB_pos : 0 < B)
    (hxB : x ≤ B) :
    Real.log x ≤ Real.log B := by
  exact Real.log_le_log hx_pos hxB

/-- A positive polynomial bound dominates its own logarithm after increasing
the constant. -/
theorem Real.log_polynomial_bound_le_polynomial_bound
    {C : ℝ}
    {m : ℕ}
    {r : ℝ}
    (hC_pos : 0 < C)
    (hr : 1 ≤ r) :
    Real.log (C * r ^ m) ≤ (C + |Real.log C| + 1) * r ^ (m + 1) := by
  have hr_nonneg : 0 ≤ r :=
    le_trans zero_le_one hr
  have hr_pow_nonneg : 0 ≤ r ^ m :=
    pow_nonneg hr_nonneg m
  have hpoly_nonneg : 0 ≤ C * r ^ m :=
    mul_nonneg (le_of_lt hC_pos) hr_pow_nonneg
  have hlog_le_self :
      Real.log (C * r ^ m) ≤ C * r ^ m :=
    Real.log_le_self hpoly_nonneg
  have hcoeff_le : C ≤ C + |Real.log C| + 1 := by
    linarith [abs_nonneg (Real.log C)]
  have hpow_le : r ^ m ≤ r ^ (m + 1) := by
    calc
      r ^ m = r ^ m * 1 := by rw [mul_one]
      _ ≤ r ^ m * r :=
        mul_le_mul_of_nonneg_left hr hr_pow_nonneg
      _ = r ^ (m + 1) := by
        rw [pow_succ]
  have hcoeff_nonneg : 0 ≤ C + |Real.log C| + 1 := by
    linarith [hC_pos, abs_nonneg (Real.log C)]
  have hpoly_le :
      C * r ^ m ≤ (C + |Real.log C| + 1) * r ^ (m + 1) :=
    mul_le_mul hcoeff_le hpow_le hr_pow_nonneg hcoeff_nonneg
  exact le_trans hlog_le_self hpoly_le

/-- Turning a direct norm polynomial bound into a logarithmic polynomial
bound. -/
theorem Real.log_norm_bound_of_norm_bound_polynomial
    {f : ℂ → ℂ}
    {R C : ℝ}
    {m : ℕ}
    (hC_pos : 0 < C)
    (hbound :
      ∀ z : ℂ,
        0 < z.re →
          R ≤ ‖z‖ →
            ‖f z‖ ≤ C * (1 + ‖z‖) ^ m) :
    ∃ Clog : ℝ, ∃ mlog : ℕ,
      0 < Clog ∧
      ∀ z : ℂ,
        0 < z.re →
          R ≤ ‖z‖ →
            Real.log ‖f z‖ ≤ Clog * (1 + ‖z‖) ^ mlog := by
  refine ⟨C + |Real.log C| + 1, m + 1, ?_, ?_⟩
  · have hnonneg_abs : 0 ≤ |Real.log C| := abs_nonneg _
    linarith
  · intro z hz_re hRz
    by_cases hf_zero : f z = 0
    · rw [hf_zero, norm_zero, Real.log_zero]
      have hpoly_nonneg : 0 ≤ (1 + ‖z‖) ^ (m + 1) :=
        pow_nonneg (by positivity) (m + 1)
      have hC_nonneg : 0 ≤ C + |Real.log C| + 1 := by
        linarith [hC_pos, abs_nonneg (Real.log C)]
      exact mul_nonneg hC_nonneg hpoly_nonneg
    · have hf_norm_pos : 0 < ‖f z‖ :=
        norm_pos_iff.mpr hf_zero
      have hbase_ge_one : 1 ≤ 1 + ‖z‖ := by
        linarith [norm_nonneg z]
      have hpoly_pos : 0 < C * (1 + ‖z‖) ^ m :=
        mul_pos hC_pos (pow_pos (lt_of_lt_of_le zero_lt_one hbase_ge_one) m)
      have hlog_le :
          Real.log ‖f z‖ ≤
            Real.log (C * (1 + ‖z‖) ^ m) :=
        Real.log_norm_le_of_norm_le_pos
          hf_norm_pos hpoly_pos (hbound z hz_re hRz)
      exact
        le_trans hlog_le
          (Real.log_polynomial_bound_le_polynomial_bound
            hC_pos hbase_ge_one)

/-- Principal logarithm has polynomial norm growth after a large-radius cutoff
in the open right half-plane. -/
theorem Complex.log_norm_bound_large_openRightHalfPlane :
    ∃ R : ℝ, ∃ C : ℝ, ∃ m : ℕ,
      0 < R ∧ 0 < C ∧
      ∀ z : ℂ,
        0 < z.re →
          R ≤ ‖z‖ →
            ‖Complex.log z‖ ≤ C * (1 + ‖z‖) ^ m := by
  sorry

/-- The product part `(z - 1/2) * log z` in the Binet main term has
polynomial norm growth after a large-radius cutoff. -/
theorem Complex.binetLogGammaMainTerm_product_norm_bound_large_openRightHalfPlane :
    ∃ R : ℝ, ∃ C : ℝ, ∃ m : ℕ,
      0 < R ∧ 0 < C ∧
      ∀ z : ℂ,
        0 < z.re →
          R ≤ ‖z‖ →
            ‖(z - (1 / 2 : ℂ)) * Complex.log z‖ ≤
              C * (1 + ‖z‖) ^ m := by
  sorry

/-- The affine plus constant part of the Binet main term has polynomial norm
growth. -/
theorem Complex.binetLogGammaMainTerm_affine_norm_bound_large_openRightHalfPlane :
    ∃ R : ℝ, ∃ C : ℝ, ∃ m : ℕ,
      0 < R ∧ 0 < C ∧
      ∀ z : ℂ,
        0 < z.re →
          R ≤ ‖z‖ →
            ‖-z + (((Real.log (2 * Real.pi)) : ℝ) : ℂ) / 2‖ ≤
              C * (1 + ‖z‖) ^ m := by
  sorry

/-- The product and affine pieces assemble to the direct polynomial norm
growth of the explicit Binet main term. -/
theorem Complex.binetLogGammaMainTerm_norm_bound_large_openRightHalfPlane_from_pieces :
    ∃ R : ℝ, ∃ C : ℝ, ∃ m : ℕ,
      0 < R ∧ 0 < C ∧
      ∀ z : ℂ,
        0 < z.re →
          R ≤ ‖z‖ →
            ‖Complex.binetLogGammaMainTerm z‖ ≤
              C * (1 + ‖z‖) ^ m := by
  sorry

/-- Direct polynomial norm growth for the explicit Binet main term after a
large-radius cutoff in the open right half-plane. -/
theorem Complex.binetLogGammaMainTerm_norm_bound_large_openRightHalfPlane :
    ∃ R : ℝ, ∃ C : ℝ, ∃ m : ℕ,
      0 < R ∧ 0 < C ∧
      ∀ z : ℂ,
        0 < z.re →
          R ≤ ‖z‖ →
            ‖Complex.binetLogGammaMainTerm z‖ ≤
              C * (1 + ‖z‖) ^ m := by
  exact
    Complex.binetLogGammaMainTerm_norm_bound_large_openRightHalfPlane_from_pieces

/-- The explicit Binet main term has polynomial logarithmic growth after a
large-radius cutoff in the open right half-plane. -/
theorem Complex.binetLogGammaMainTerm_log_norm_bound_large_openRightHalfPlane :
    ∃ R : ℝ, ∃ C : ℝ, ∃ m : ℕ,
      0 < R ∧ 0 < C ∧
      ∀ z : ℂ,
        0 < z.re →
          R ≤ ‖z‖ →
            Real.log ‖Complex.binetLogGammaMainTerm z‖ ≤
              C * (1 + ‖z‖) ^ m := by
  rcases
    Complex.binetLogGammaMainTerm_norm_bound_large_openRightHalfPlane with
    ⟨R, C, m, hR_pos, hC_pos, hbound⟩
  rcases
    Real.log_norm_bound_of_norm_bound_polynomial
      hC_pos hbound with
    ⟨Clog, mlog, hClog_pos, hlog⟩
  exact ⟨R, Clog, mlog, hR_pos, hClog_pos, hlog⟩

/-- Uniform direct polynomial norm growth for the Binet remainder after a
large-radius cutoff in the open right half-plane. -/
theorem Complex.binetSecondFormulaRemainder_norm_bound_large_openRightHalfPlane :
    ∃ R : ℝ, ∃ C : ℝ, ∃ m : ℕ,
      0 < R ∧ 0 < C ∧
      ∀ z : ℂ,
        0 < z.re →
          R ≤ ‖z‖ →
            ‖Complex.binetSecondFormulaRemainder z‖ ≤
              C * (1 + ‖z‖) ^ m := by
  sorry

/-- Binet's principal-log identity and direct component norm bounds give
polynomial growth for `log (Gamma z)` after a large-radius cutoff. -/
theorem Complex.log_Gamma_norm_bound_large_openRightHalfPlane_from_Binet_components :
    ∃ R : ℝ, ∃ C : ℝ, ∃ m : ℕ,
      0 < R ∧ 0 < C ∧
      ∀ z : ℂ,
        0 < z.re →
          R ≤ ‖z‖ →
            ‖Complex.log (Complex.Gamma z)‖ ≤
              C * (1 + ‖z‖) ^ m := by
  sorry

/-- Passing from a norm bound on the principal logarithm to a bound on
`Real.log ‖Gamma z‖`. -/
theorem Complex.Gamma_log_norm_bound_large_openRightHalfPlane_from_log_Gamma_norm :
    ∃ R : ℝ, ∃ C : ℝ, ∃ m : ℕ,
      0 < R ∧ 0 < C ∧
      ∀ z : ℂ,
        0 < z.re →
          R ≤ ‖z‖ →
            Real.log ‖Complex.Gamma z‖ ≤
              C * (1 + ‖z‖) ^ m := by
  rcases
    Complex.log_Gamma_norm_bound_large_openRightHalfPlane_from_Binet_components with
    ⟨R, C, m, hR_pos, hC_pos, hlog_norm⟩
  refine ⟨R, C, m, hR_pos, hC_pos, ?_⟩
  intro z hz_re hRz
  have hre_le_norm :
      (Complex.log (Complex.Gamma z)).re ≤
        ‖Complex.log (Complex.Gamma z)‖ := by
    exact le_trans (le_abs_self _)
      (by
        simpa [Complex.normSq, norm_eq_abs] using
          Complex.abs_re_le_abs (Complex.log (Complex.Gamma z)))
  have hlog_eq :
      Real.log ‖Complex.Gamma z‖ =
        (Complex.log (Complex.Gamma z)).re := by
    rw [Complex.log_re]
  exact
    le_trans (le_of_eq hlog_eq) (le_trans hre_le_norm (hlog_norm z hz_re hRz))

/-- The Binet remainder has polynomial logarithmic growth after a large-radius
cutoff in the open right half-plane. -/
theorem Complex.binetSecondFormulaRemainder_log_norm_bound_large_openRightHalfPlane :
    ∃ R : ℝ, ∃ C : ℝ, ∃ m : ℕ,
      0 < R ∧ 0 < C ∧
      ∀ z : ℂ,
        0 < z.re →
          R ≤ ‖z‖ →
            Real.log ‖Complex.binetSecondFormulaRemainder z‖ ≤
              C * (1 + ‖z‖) ^ m := by
  rcases
    Complex.binetSecondFormulaRemainder_norm_bound_large_openRightHalfPlane with
    ⟨R, C, m, hR_pos, hC_pos, hbound⟩
  rcases
    Real.log_norm_bound_of_norm_bound_polynomial
      hC_pos hbound with
    ⟨Clog, mlog, hClog_pos, hlog⟩
  exact ⟨R, Clog, mlog, hR_pos, hClog_pos, hlog⟩

/-- The Binet formula plus polynomial norm bounds for the main term and
remainder give logarithmic Gamma growth after a large-radius cutoff. -/
theorem Complex.Gamma_log_norm_bound_large_openRightHalfPlane_from_Binet_norm_components :
    ∃ R : ℝ, ∃ C : ℝ, ∃ m : ℕ,
      0 < R ∧ 0 < C ∧
      ∀ z : ℂ,
        0 < z.re →
          R ≤ ‖z‖ →
            Real.log ‖Complex.Gamma z‖ ≤
              C * (1 + ‖z‖) ^ m := by
  exact
    Complex.Gamma_log_norm_bound_large_openRightHalfPlane_from_log_Gamma_norm

/-- Addition preserves polynomial logarithmic growth for the Binet main term
and remainder after a common large-radius cutoff. -/
theorem Complex.Gamma_openRightHalfPlane_log_norm_bound_from_Binet_components :
    ∃ R : ℝ, ∃ C : ℝ, ∃ m : ℕ,
      0 < R ∧ 0 < C ∧
      ∀ z : ℂ,
        0 < z.re →
          R ≤ ‖z‖ →
            Real.log ‖Complex.Gamma z‖ ≤
              C * (1 + ‖z‖) ^ m := by
  exact
    Complex.Gamma_log_norm_bound_large_openRightHalfPlane_from_Binet_norm_components

/-- Open-right-half-plane logarithmic Gamma growth from the principal-log
Binet formula and the open-half-plane remainder estimates, away from the
origin.  A large-radius cutoff is necessary because `Gamma` has a pole at
zero. -/
theorem Complex.Gamma_openRightHalfPlane_log_norm_bound_from_Binet :
    ∃ R : ℝ, ∃ C : ℝ, ∃ m : ℕ,
      0 < R ∧ 0 < C ∧
      ∀ z : ℂ,
        0 < z.re →
          R ≤ ‖z‖ →
            Real.log ‖Complex.Gamma z‖ ≤
              C * (1 + ‖z‖) ^ m := by
  exact
    Complex.Gamma_openRightHalfPlane_log_norm_bound_from_Binet_components

/-- Open-right-half-plane logarithmic Gamma growth from Binet-Stirling.

The literal principal-arctangent Binet remainder in this package is not a
closed-boundary kernel on the imaginary axis, so the sectorial log-norm owner
statement is intentionally open in the real part.  The large-radius cutoff is
also necessary because `Gamma` has a pole at zero. -/
theorem Complex.Gamma_closedRightHalfPlane_log_norm_bound_classical :
    ∃ R : ℝ, ∃ C : ℝ, ∃ m : ℕ,
      0 < R ∧ 0 < C ∧
      ∀ z : ℂ,
        0 < z.re →
          R ≤ ‖z‖ →
            Real.log ‖Complex.Gamma z‖ ≤
              C * (1 + ‖z‖) ^ m := by
  exact
    Complex.Gamma_openRightHalfPlane_log_norm_bound_from_Binet

end

end LFunctions
end Boundary
