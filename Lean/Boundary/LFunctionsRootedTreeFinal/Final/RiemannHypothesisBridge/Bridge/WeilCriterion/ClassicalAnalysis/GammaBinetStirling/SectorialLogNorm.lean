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

/-- The shifted norm base is at least one. -/
theorem Real.sectorialLogNorm_one_le_one_add_norm
    (z : ℂ) :
    1 ≤ 1 + ‖z‖ := by
  calc
    1 = 1 + 0 := by
      exact (add_zero 1).symm
    _ ≤ 1 + ‖z‖ := by
      exact add_le_add_left (norm_nonneg z) 1

/-- The shifted norm base is nonnegative. -/
theorem Real.sectorialLogNorm_zero_le_one_add_norm
    (z : ℂ) :
    0 ≤ 1 + ‖z‖ := by
  exact le_trans zero_le_one (Real.sectorialLogNorm_one_le_one_add_norm z)

/-- Adding a nonnegative logarithmic absolute value and `1` increases a
positive coefficient. -/
theorem Real.sectorialLogNorm_coeff_le_augmented
    {C : ℝ} :
    C ≤ C + |Real.log C| + 1 := by
  calc
    C ≤ C + |Real.log C| := by
      exact le_add_of_nonneg_right (abs_nonneg (Real.log C))
    _ ≤ C + |Real.log C| + 1 := by
      exact le_add_of_nonneg_right zero_le_one

/-- The augmented logarithmic coefficient is nonnegative when the original
coefficient is positive. -/
theorem Real.sectorialLogNorm_augmented_coeff_nonneg
    {C : ℝ}
    (hC_pos : 0 < C) :
    0 ≤ C + |Real.log C| + 1 := by
  exact le_trans (le_of_lt hC_pos)
    Real.sectorialLogNorm_coeff_le_augmented

/-- The augmented logarithmic coefficient is positive when the original
coefficient is positive. -/
theorem Real.sectorialLogNorm_augmented_coeff_pos
    {C : ℝ}
    (hC_pos : 0 < C) :
    0 < C + |Real.log C| + 1 :=
  lt_of_lt_of_le hC_pos Real.sectorialLogNorm_coeff_le_augmented

/-- The real number `4` is positive. -/
theorem Real.sectorialLogNorm_four_pos : 0 < (4 : ℝ) := by
  exact Nat.cast_pos.mpr (Nat.succ_pos 3)

/-- The complex norm of `1/2` is bounded by `1`. -/
theorem Complex.norm_half_le_one : ‖(1 / 2 : ℂ)‖ ≤ (1 : ℝ) := by
  have hhalf_nonneg : 0 ≤ (1 / 2 : ℝ) := by
    exact div_nonneg zero_le_one zero_le_two
  have hhalf_le_one : (1 / 2 : ℝ) ≤ 1 := by
    exact div_le_self zero_le_one one_le_two
  calc
    ‖(1 / 2 : ℂ)‖ = ‖((1 / 2 : ℝ) : ℂ)‖ := by
      rfl
    _ = |(1 / 2 : ℝ)| := RCLike.norm_ofReal (1 / 2 : ℝ)
    _ = (1 / 2 : ℝ) := abs_of_nonneg hhalf_nonneg
    _ ≤ 1 := hhalf_le_one

/-- The norm of `z - 1/2` is bounded by the shifted norm base. -/
theorem Complex.norm_sub_half_le_one_add_norm
    (z : ℂ) :
    ‖z - (1 / 2 : ℂ)‖ ≤ 1 + ‖z‖ := by
  calc
    ‖z - (1 / 2 : ℂ)‖ ≤ ‖z‖ + ‖(1 / 2 : ℂ)‖ :=
      norm_sub_le z (1 / 2 : ℂ)
    _ ≤ ‖z‖ + 1 := by
      exact add_le_add_left Complex.norm_half_le_one ‖z‖
    _ = 1 + ‖z‖ := add_comm ‖z‖ 1

/-- Multiplying a polynomial term by the shifted base increases its exponent
by one. -/
theorem Real.sectorialLogNorm_base_mul_power
    (C r : ℝ)
    (m : ℕ) :
    r * (C * r ^ m) = C * r ^ (m + 1) := by
  calc
    r * (C * r ^ m) = C * (r * r ^ m) := by
      exact (mul_left_comm r C (r ^ m)).trans
        (mul_assoc C r (r ^ m)).symm
    _ = C * r ^ (m + 1) := by
      exact congrArg (fun x : ℝ => C * x) (pow_succ r m).symm

/-- `r + 4` is dominated by `4 * (1+r)` for nonnegative `r`. -/
theorem Real.sectorialLogNorm_add_four_le_four_mul_one_add
    {r : ℝ}
    (hr : 0 ≤ r) :
    r + 4 ≤ 4 * (1 + r) := by
  calc
    r + 4 ≤ 4 * r + 4 := by
      have hr_le_four_r : r ≤ 4 * r := by
        calc
          r = 1 * r := by
            exact (one_mul r).symm
          _ ≤ 4 * r := by
            exact mul_le_mul_of_nonneg_right
              (by exact Nat.cast_le.mpr (show (1 : ℕ) ≤ 4 from Nat.succ_le_succ (Nat.zero_le 3)))
              hr
      exact add_le_add_right hr_le_four_r 4
    _ = 4 * (1 + r) := by
      calc
        4 * r + 4 = 4 * r + 4 * 1 := by
          exact congrArg (fun x : ℝ => 4 * r + x) (mul_one 4).symm
        _ = 4 * (r + 1) := by
          exact (mul_add 4 r 1).symm
        _ = 4 * (1 + r) := by
          exact congrArg (fun x : ℝ => 4 * x) (add_comm r 1)

/-- Two polynomial terms with the same base combine by adding coefficients. -/
theorem Real.sectorialLogNorm_add_same_power
    (C D r : ℝ)
    (m : ℕ) :
    C * r ^ m + D * r ^ m = (C + D) * r ^ m := by
  exact (add_mul C D (r ^ m)).symm

/-- A linear-plus-constant term is dominated by `(1+A)*(1+r)`. -/
theorem Real.sectorialLogNorm_norm_add_constant_le_product
    {r A : ℝ}
    (hr : 0 ≤ r)
    (hA : 0 ≤ A) :
    r + A ≤ (1 + A) * (1 + r) := by
  calc
    r + A ≤ r + A + A * r := by
      exact le_add_of_nonneg_right (mul_nonneg hA hr)
    _ = (1 + A) * (1 + r) := by
      calc
        r + A + A * r = 1 * r + A * 1 + A * r := by
          exact congrArg₂ HAdd.hAdd
            (congrArg (fun x : ℝ => x + A) (one_mul r).symm)
            rfl
        _ = (1 + A) * (1 + r) := by
          exact (add_mul 1 A (1 + r)).symm.trans
            (congrArg (fun x : ℝ => x + A * (1 + r))
              (one_mul (1 + r))).symm

/-- Unfolding of the Binet main term into product plus affine part. -/
theorem Complex.binetLogGammaMainTerm_eq_product_add_affine
    (z : ℂ) :
    Complex.binetLogGammaMainTerm z =
      (z - (1 / 2 : ℂ)) * Complex.log z +
        (-z + (((Real.log (2 * Real.pi)) : ℝ) : ℂ) / 2) := by
  rfl

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
    exact Real.sectorialLogNorm_coeff_le_augmented
  have hpow_le : r ^ m ≤ r ^ (m + 1) := by
    calc
      r ^ m = r ^ m * 1 := by exact (mul_one (r ^ m)).symm
      _ ≤ r ^ m * r :=
        mul_le_mul_of_nonneg_left hr hr_pow_nonneg
      _ = r ^ (m + 1) := by
        exact (pow_succ r m).symm
  have hcoeff_nonneg : 0 ≤ C + |Real.log C| + 1 := by
    exact Real.sectorialLogNorm_augmented_coeff_nonneg hC_pos
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
    exact add_nonneg (le_trans (le_of_lt hC_pos) (le_add_of_nonneg_right hnonneg_abs))
      zero_le_one
  · intro z hz_re hRz
    by_cases hf_zero : f z = 0
    · have hnorm_zero : ‖f z‖ = 0 := by
        exact norm_eq_zero.mpr hf_zero
      have hlog_zero : Real.log ‖f z‖ = 0 := by
        cases hnorm_zero
        rfl
      cases hlog_zero
      rfl
      have hpoly_nonneg : 0 ≤ (1 + ‖z‖) ^ (m + 1) :=
        pow_nonneg (Real.sectorialLogNorm_zero_le_one_add_norm z) (m + 1)
      have hC_nonneg : 0 ≤ C + |Real.log C| + 1 := by
        exact Real.sectorialLogNorm_augmented_coeff_nonneg hC_pos
      exact mul_nonneg hC_nonneg hpoly_nonneg
    · have hf_norm_pos : 0 < ‖f z‖ :=
        norm_pos_iff.mpr hf_zero
      have hbase_ge_one : 1 ≤ 1 + ‖z‖ := by
        exact Real.sectorialLogNorm_one_le_one_add_norm z
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
  refine ⟨1, 4, 1, zero_lt_one, Real.sectorialLogNorm_four_pos, ?_⟩
  intro z _hz_re hz_norm
  have hnorm_pos : 0 < ‖z‖ :=
    lt_of_lt_of_le zero_lt_one hz_norm
  have hlog_nonneg : 0 ≤ Real.log ‖z‖ :=
    Real.log_nonneg hz_norm
  have habs_log_le_norm : |Real.log ‖z‖| ≤ ‖z‖ := by
    calc
      |Real.log ‖z‖| = Real.log ‖z‖ := abs_of_nonneg hlog_nonneg
      _ ≤ ‖z‖ := Real.log_le_self (norm_nonneg z)
  have hlog_norm :
      ‖Complex.log z‖ ≤ |Real.log ‖z‖| + Real.pi :=
    Complex.log_norm_le_abs_log_norm_add_pi z
  have hpi_le_four : Real.pi ≤ (4 : ℝ) :=
    le_of_lt Real.pi_lt_four
  calc
    ‖Complex.log z‖ ≤ |Real.log ‖z‖| + Real.pi := hlog_norm
    _ ≤ ‖z‖ + 4 := add_le_add habs_log_le_norm hpi_le_four
    _ ≤ 4 * (1 + ‖z‖) ^ 1 := by
      have hpow1 : (1 + ‖z‖) ^ 1 = (1 + ‖z‖) := by
        exact pow_one (1 + ‖z‖)
      exact hpow1.symm ▸
        Real.sectorialLogNorm_add_four_le_four_mul_one_add
          (norm_nonneg z)

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
  rcases Complex.log_norm_bound_large_openRightHalfPlane with
    ⟨R, C, m, hR_pos, hC_pos, hlog⟩
  refine ⟨R, C, m + 1, hR_pos, hC_pos, ?_⟩
  intro z hz_re hRz
  have hbase_nonneg : 0 ≤ 1 + ‖z‖ := by
    exact Real.sectorialLogNorm_zero_le_one_add_norm z
  have hfactor :
      ‖z - (1 / 2 : ℂ)‖ ≤ 1 + ‖z‖ := by
    exact Complex.norm_sub_half_le_one_add_norm z
  have hmul :
      ‖(z - (1 / 2 : ℂ)) * Complex.log z‖ ≤
        (1 + ‖z‖) * (C * (1 + ‖z‖) ^ m) := by
    calc
      ‖(z - (1 / 2 : ℂ)) * Complex.log z‖ =
          ‖z - (1 / 2 : ℂ)‖ * ‖Complex.log z‖ := norm_mul _ _
      _ ≤ (1 + ‖z‖) * (C * (1 + ‖z‖) ^ m) :=
        mul_le_mul hfactor (hlog z hz_re hRz)
          (norm_nonneg _) hbase_nonneg
  calc
      ‖(z - (1 / 2 : ℂ)) * Complex.log z‖ ≤
        (1 + ‖z‖) * (C * (1 + ‖z‖) ^ m) := hmul
    _ = C * (1 + ‖z‖) ^ (m + 1) := by
      calc
        (1 + ‖z‖) * (C * (1 + ‖z‖) ^ m) =
            C * ((1 + ‖z‖) * (1 + ‖z‖) ^ m) := by
          exact (mul_left_comm (1 + ‖z‖) C ((1 + ‖z‖) ^ m)).trans
            (mul_assoc C (1 + ‖z‖) ((1 + ‖z‖) ^ m)).symm
        _ = C * (1 + ‖z‖) ^ (m + 1) := by
          exact congrArg (fun x => C * x) (pow_succ (1 + ‖z‖) m).symm

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
  let A : ℝ := ‖((((Real.log (2 * Real.pi)) : ℝ) : ℂ) / 2)‖
  refine ⟨1, 1 + A, 1, zero_lt_one, ?_, ?_⟩
  · exact lt_add_of_pos_left A zero_lt_one
  · intro z _hz_re _hz_norm
    have hA_nonneg : 0 ≤ A := norm_nonneg _
    have hbase_nonneg : 0 ≤ 1 + ‖z‖ := by
      exact Real.sectorialLogNorm_zero_le_one_add_norm z
  calc
    ‖-z + (((Real.log (2 * Real.pi)) : ℝ) : ℂ) / 2‖ ≤
        ‖-z‖ + ‖((((Real.log (2 * Real.pi)) : ℝ) : ℂ) / 2)‖ :=
      norm_add_le _ _
    _ = ‖z‖ + A := by
      dsimp [A]
      congr 1
      exact norm_neg z
        _ ≤ (1 + A) * (1 + ‖z‖) ^ 1 := by
          have hpow1 : (1 + ‖z‖) ^ 1 = (1 + ‖z‖) := pow_one (1 + ‖z‖)
          exact hpow1.symm ▸
            Real.sectorialLogNorm_norm_add_constant_le_product
              (norm_nonneg z) hA_nonneg

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
  rcases
    Complex.binetLogGammaMainTerm_product_norm_bound_large_openRightHalfPlane with
    ⟨Rp, Cp, mp, hRp_pos, hCp_pos, hp⟩
  rcases
    Complex.binetLogGammaMainTerm_affine_norm_bound_large_openRightHalfPlane with
    ⟨Ra, Ca, ma, hRa_pos, hCa_pos, ha⟩
  refine ⟨max Rp Ra, Cp + Ca, mp + ma, ?_, ?_, ?_⟩
  · exact lt_max_of_lt_left hRp_pos
  · exact add_pos hCp_pos hCa_pos
  · intro z hz_re hRz
    have hRpz : Rp ≤ ‖z‖ := le_trans (le_max_left Rp Ra) hRz
    have hRaz : Ra ≤ ‖z‖ := le_trans (le_max_right Rp Ra) hRz
    have hbase_ge_one : 1 ≤ 1 + ‖z‖ := by
      exact Real.sectorialLogNorm_one_le_one_add_norm z
    have hbase_nonneg : 0 ≤ 1 + ‖z‖ :=
      le_trans zero_le_one hbase_ge_one
    have hp_bound :
        ‖(z - (1 / 2 : ℂ)) * Complex.log z‖ ≤
          Cp * (1 + ‖z‖) ^ (mp + ma) := by
      have hpow : (1 + ‖z‖) ^ mp ≤ (1 + ‖z‖) ^ (mp + ma) :=
        pow_le_pow_right₀ hbase_ge_one (Nat.le_add_right mp ma)
      exact
        le_trans (hp z hz_re hRpz)
          (mul_le_mul_of_nonneg_left hpow (le_of_lt hCp_pos))
    have ha_bound :
        ‖-z + (((Real.log (2 * Real.pi)) : ℝ) : ℂ) / 2‖ ≤
          Ca * (1 + ‖z‖) ^ (mp + ma) := by
      have hma_le : ma ≤ mp + ma := by
        exact Nat.le_add_left ma mp
      have hpow : (1 + ‖z‖) ^ ma ≤ (1 + ‖z‖) ^ (mp + ma) :=
        pow_le_pow_right₀ hbase_ge_one hma_le
      exact
        le_trans (ha z hz_re hRaz)
          (mul_le_mul_of_nonneg_left hpow (le_of_lt hCa_pos))
    have hsum :
        ‖(z - (1 / 2 : ℂ)) * Complex.log z‖ +
          ‖-z + (((Real.log (2 * Real.pi)) : ℝ) : ℂ) / 2‖ ≤
            (Cp + Ca) * (1 + ‖z‖) ^ (mp + ma) := by
      calc
        ‖(z - (1 / 2 : ℂ)) * Complex.log z‖ +
            ‖-z + (((Real.log (2 * Real.pi)) : ℝ) : ℂ) / 2‖
            ≤ Cp * (1 + ‖z‖) ^ (mp + ma) +
                Ca * (1 + ‖z‖) ^ (mp + ma) :=
          add_le_add hp_bound ha_bound
        _ = (Cp + Ca) * (1 + ‖z‖) ^ (mp + ma) := by
          exact Real.sectorialLogNorm_add_same_power Cp Ca
            (1 + ‖z‖) (mp + ma)
    calc
      ‖Complex.binetLogGammaMainTerm z‖ =
          ‖(z - (1 / 2 : ℂ)) * Complex.log z +
            (-z + (((Real.log (2 * Real.pi)) : ℝ) : ℂ) / 2)‖ := by
        exact congrArg norm
          (Complex.binetLogGammaMainTerm_eq_product_add_affine z)
      _ ≤ ‖(z - (1 / 2 : ℂ)) * Complex.log z‖ +
          ‖-z + (((Real.log (2 * Real.pi)) : ℝ) : ℂ) / 2‖ :=
        norm_add_le _ _
      _ ≤ (Cp + Ca) * (1 + ‖z‖) ^ (mp + ma) := hsum

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
large-radius cutoff in a fixed open wedge of the right half-plane.

The separation hypothesis `ε ≤ z.re / ‖z‖` is necessary: the principal
arctangent kernel has boundary singularities as rays approach the imaginary
axis, and the open-half-plane pointwise remainder bound has constants depending
on this separation. -/
theorem Complex.binetSecondFormulaRemainder_norm_bound_large_sectorSeparated
    (ε : ℝ)
    (hε : 0 < ε) :
    ∃ R : ℝ, ∃ C : ℝ, ∃ m : ℕ,
      0 < R ∧ 0 < C ∧
      ∀ z : ℂ,
        0 < z.re →
          ε ≤ z.re / ‖z‖ →
          R ≤ ‖z‖ →
            ‖Complex.binetSecondFormulaRemainder z‖ ≤
              C * (1 + ‖z‖) ^ m := by
  rcases
      Complex.binetSecondFormulaRemainder_norm_le_sectorSeparated
        ε hε with
    ⟨C, hC_pos, hbound⟩
  refine ⟨1, C, 0, zero_lt_one, hC_pos, ?_⟩
  intro z hz_re hz_sep hz_large
  have hpoly_one : (1 + ‖z‖) ^ (0 : ℕ) = (1 : ℝ) := by
    exact pow_zero (1 + ‖z‖)
  calc
    ‖Complex.binetSecondFormulaRemainder z‖ ≤ C :=
      hbound z hz_re hz_sep hz_large
    _ = C * (1 + ‖z‖) ^ (0 : ℕ) := by
      exact congrArg (fun x => C * x) hpoly_one.symm

/-- Binet's formula plus direct polynomial norm bounds for the main term and
remainder give polynomial growth for `log (Gamma z)` in a fixed right-half
plane wedge. -/
theorem Complex.log_Gamma_norm_bound_large_sectorSeparated_from_Binet_formula_and_norm_bounds
    (ε : ℝ)
    (hε : 0 < ε) :
    ∃ R : ℝ, ∃ C : ℝ, ∃ m : ℕ,
      0 < R ∧ 0 < C ∧
      ∀ z : ℂ,
        0 < z.re →
          ε ≤ z.re / ‖z‖ →
          R ≤ ‖z‖ →
            ‖Complex.log (Complex.Gamma z)‖ ≤
              C * (1 + ‖z‖) ^ m := by
  rcases Complex.Gamma_binetSecondFormula_closedRightHalfPlane with
    ⟨Rb, hRb_pos, hBinet⟩
  rcases Complex.binetLogGammaMainTerm_norm_bound_large_openRightHalfPlane with
    ⟨Rm, Cm, mm, hRm_pos, hCm_pos, hmain⟩
  rcases Complex.binetSecondFormulaRemainder_norm_bound_large_sectorSeparated
      ε hε with
    ⟨Rr, Cr, mr, hRr_pos, hCr_pos, hrem⟩
  let R : ℝ := max Rb (max Rm Rr)
  let C : ℝ := Cm + Cr
  let m : ℕ := mm + mr
  refine ⟨R, C, m, ?_, ?_, ?_⟩
  · exact lt_of_lt_of_le hRb_pos (le_max_left Rb (max Rm Rr))
  · exact add_pos hCm_pos hCr_pos
  · intro z hz_re hz_sep hRz
    have hRbz : Rb ≤ ‖z‖ :=
      le_trans (le_max_left Rb (max Rm Rr)) hRz
    have hRmz : Rm ≤ ‖z‖ :=
      le_trans
        (le_trans (le_max_left Rm Rr) (le_max_right Rb (max Rm Rr)))
        hRz
    have hRrz : Rr ≤ ‖z‖ :=
      le_trans
        (le_trans (le_max_right Rm Rr) (le_max_right Rb (max Rm Rr)))
        hRz
    have hbase_ge_one : 1 ≤ 1 + ‖z‖ := by
      exact Real.sectorialLogNorm_one_le_one_add_norm z
    have hmain_bound :
        ‖Complex.binetLogGammaMainTerm z‖ ≤
          Cm * (1 + ‖z‖) ^ m := by
      have hpow :
          (1 + ‖z‖) ^ mm ≤ (1 + ‖z‖) ^ m :=
        pow_le_pow_right₀ hbase_ge_one (Nat.le_add_right mm mr)
      exact
        le_trans (hmain z hz_re hRmz)
          (mul_le_mul_of_nonneg_left hpow (le_of_lt hCm_pos))
    have hrem_bound :
        ‖Complex.binetSecondFormulaRemainder z‖ ≤
          Cr * (1 + ‖z‖) ^ m := by
      have hmr_le : mr ≤ m := by
        dsimp [m]
        exact Nat.le_add_left mr mm
      have hpow :
          (1 + ‖z‖) ^ mr ≤ (1 + ‖z‖) ^ m :=
        pow_le_pow_right₀ hbase_ge_one hmr_le
      exact
        le_trans (hrem z hz_re hz_sep hRrz)
          (mul_le_mul_of_nonneg_left hpow (le_of_lt hCr_pos))
    have hsum :
        ‖Complex.binetLogGammaMainTerm z‖ +
          ‖Complex.binetSecondFormulaRemainder z‖ ≤
            C * (1 + ‖z‖) ^ m := by
      calc
        ‖Complex.binetLogGammaMainTerm z‖ +
            ‖Complex.binetSecondFormulaRemainder z‖
            ≤ Cm * (1 + ‖z‖) ^ m +
                Cr * (1 + ‖z‖) ^ m :=
          add_le_add hmain_bound hrem_bound
        _ = C * (1 + ‖z‖) ^ m := by
          dsimp [C]
          exact Real.sectorialLogNorm_add_same_power Cm Cr
            (1 + ‖z‖) m
    have hformula :
        Complex.log (Complex.Gamma z) =
          Complex.binetLogGammaMainTerm z +
            Complex.binetSecondFormulaRemainder z :=
      hBinet z hz_re hRbz
    calc
      ‖Complex.log (Complex.Gamma z)‖ =
          ‖Complex.binetLogGammaMainTerm z +
            Complex.binetSecondFormulaRemainder z‖ := by
        exact congrArg norm hformula
      _ ≤ ‖Complex.binetLogGammaMainTerm z‖ +
          ‖Complex.binetSecondFormulaRemainder z‖ :=
        norm_add_le _ _
      _ ≤ C * (1 + ‖z‖) ^ m := hsum

/-- Binet's principal-log identity and direct component norm bounds give
polynomial growth for `log (Gamma z)` after a large-radius cutoff in a fixed
wedge. -/
theorem Complex.log_Gamma_norm_bound_large_sectorSeparated_from_Binet_components
    (ε : ℝ)
    (hε : 0 < ε) :
    ∃ R : ℝ, ∃ C : ℝ, ∃ m : ℕ,
      0 < R ∧ 0 < C ∧
      ∀ z : ℂ,
        0 < z.re →
          ε ≤ z.re / ‖z‖ →
          R ≤ ‖z‖ →
            ‖Complex.log (Complex.Gamma z)‖ ≤
              C * (1 + ‖z‖) ^ m := by
  exact
    Complex.log_Gamma_norm_bound_large_sectorSeparated_from_Binet_formula_and_norm_bounds
      ε hε

/-- Passing from a norm bound on the principal logarithm to a bound on
`Real.log ‖Gamma z‖` in a fixed wedge. -/
theorem Complex.Gamma_log_norm_bound_large_sectorSeparated_from_log_Gamma_norm
    (ε : ℝ)
    (hε : 0 < ε) :
    ∃ R : ℝ, ∃ C : ℝ, ∃ m : ℕ,
      0 < R ∧ 0 < C ∧
      ∀ z : ℂ,
        0 < z.re →
          ε ≤ z.re / ‖z‖ →
          R ≤ ‖z‖ →
            Real.log ‖Complex.Gamma z‖ ≤
              C * (1 + ‖z‖) ^ m := by
  rcases
    Complex.log_Gamma_norm_bound_large_sectorSeparated_from_Binet_components
      ε hε with
    ⟨R, C, m, hR_pos, hC_pos, hlog_norm⟩
  refine ⟨R, C, m, hR_pos, hC_pos, ?_⟩
  intro z hz_re hz_sep hRz
  have hre_le_norm :
      (Complex.log (Complex.Gamma z)).re ≤
        ‖Complex.log (Complex.Gamma z)‖ := by
    exact Complex.abs_re_le_abs (Complex.log (Complex.Gamma z))
  have hlog_eq :
      Real.log ‖Complex.Gamma z‖ =
        (Complex.log (Complex.Gamma z)).re := by
    exact Complex.log_re (Complex.Gamma z)
  exact
    le_trans (le_of_eq hlog_eq)
      (le_trans hre_le_norm (hlog_norm z hz_re hz_sep hRz))

/-- The Binet remainder has polynomial logarithmic growth after a large-radius
cutoff in a fixed right-half-plane wedge. -/
theorem Complex.binetSecondFormulaRemainder_log_norm_bound_large_sectorSeparated
    (ε : ℝ)
    (hε : 0 < ε) :
    ∃ R : ℝ, ∃ C : ℝ, ∃ m : ℕ,
      0 < R ∧ 0 < C ∧
      ∀ z : ℂ,
        0 < z.re →
          ε ≤ z.re / ‖z‖ →
          R ≤ ‖z‖ →
            Real.log ‖Complex.binetSecondFormulaRemainder z‖ ≤
              C * (1 + ‖z‖) ^ m := by
  rcases
    Complex.binetSecondFormulaRemainder_norm_bound_large_sectorSeparated
      ε hε with
    ⟨R, C, m, hR_pos, hC_pos, hbound⟩
  refine ⟨R, C + |Real.log C| + 1, m + 1, hR_pos, ?_, ?_⟩
  · have hnonneg_abs : 0 ≤ |Real.log C| := abs_nonneg _
    exact Real.sectorialLogNorm_augmented_coeff_pos hC_pos
  · intro z hz_re hz_sep hRz
    by_cases hzero : Complex.binetSecondFormulaRemainder z = 0
    · have hnorm_zero : ‖Complex.binetSecondFormulaRemainder z‖ = 0 := by
        exact norm_eq_zero.mpr hzero
      have hlog_zero : Real.log ‖Complex.binetSecondFormulaRemainder z‖ = 0 := by
        cases hnorm_zero
        rfl
      cases hlog_zero
      rfl
      have hpoly_nonneg : 0 ≤ (1 + ‖z‖) ^ (m + 1) :=
        pow_nonneg (Real.sectorialLogNorm_zero_le_one_add_norm z) (m + 1)
      have hC_nonneg : 0 ≤ C + |Real.log C| + 1 := by
        exact Real.sectorialLogNorm_augmented_coeff_nonneg hC_pos
      exact mul_nonneg hC_nonneg hpoly_nonneg
    · have hnorm_pos : 0 < ‖Complex.binetSecondFormulaRemainder z‖ :=
        norm_pos_iff.mpr hzero
      have hbase_ge_one : 1 ≤ 1 + ‖z‖ := by
        exact Real.sectorialLogNorm_one_le_one_add_norm z
      have hpoly_pos : 0 < C * (1 + ‖z‖) ^ m :=
        mul_pos hC_pos
          (pow_pos (lt_of_lt_of_le zero_lt_one hbase_ge_one) m)
      have hlog_le :
          Real.log ‖Complex.binetSecondFormulaRemainder z‖ ≤
            Real.log (C * (1 + ‖z‖) ^ m) :=
        Real.log_norm_le_of_norm_le_pos
          hnorm_pos hpoly_pos (hbound z hz_re hz_sep hRz)
      exact
        le_trans hlog_le
          (Real.log_polynomial_bound_le_polynomial_bound
            hC_pos hbase_ge_one)

/-- The Binet formula plus polynomial norm bounds for the main term and
remainder give logarithmic Gamma growth after a large-radius cutoff in a fixed
wedge. -/
theorem Complex.Gamma_log_norm_bound_large_sectorSeparated_from_Binet_norm_components
    (ε : ℝ)
    (hε : 0 < ε) :
    ∃ R : ℝ, ∃ C : ℝ, ∃ m : ℕ,
      0 < R ∧ 0 < C ∧
      ∀ z : ℂ,
        0 < z.re →
          ε ≤ z.re / ‖z‖ →
          R ≤ ‖z‖ →
            Real.log ‖Complex.Gamma z‖ ≤
              C * (1 + ‖z‖) ^ m := by
  exact
    Complex.Gamma_log_norm_bound_large_sectorSeparated_from_log_Gamma_norm
      ε hε

/-- Addition preserves polynomial logarithmic growth for the Binet main term
and remainder after a common large-radius cutoff in a fixed wedge. -/
theorem Complex.Gamma_sectorSeparated_log_norm_bound_from_Binet_components
    (ε : ℝ)
    (hε : 0 < ε) :
    ∃ R : ℝ, ∃ C : ℝ, ∃ m : ℕ,
      0 < R ∧ 0 < C ∧
      ∀ z : ℂ,
        0 < z.re →
          ε ≤ z.re / ‖z‖ →
          R ≤ ‖z‖ →
            Real.log ‖Complex.Gamma z‖ ≤
              C * (1 + ‖z‖) ^ m := by
  exact
    Complex.Gamma_log_norm_bound_large_sectorSeparated_from_Binet_norm_components
      ε hε

/-- Wedge-separated logarithmic Gamma growth from the principal-log Binet
formula and the wedge-separated remainder estimates, away from the origin. -/
theorem Complex.Gamma_sectorSeparated_log_norm_bound_from_Binet
    (ε : ℝ)
    (hε : 0 < ε) :
    ∃ R : ℝ, ∃ C : ℝ, ∃ m : ℕ,
      0 < R ∧ 0 < C ∧
      ∀ z : ℂ,
        0 < z.re →
          ε ≤ z.re / ‖z‖ →
          R ≤ ‖z‖ →
            Real.log ‖Complex.Gamma z‖ ≤
              C * (1 + ‖z‖) ^ m := by
  exact
    Complex.Gamma_sectorSeparated_log_norm_bound_from_Binet_components
      ε hε

/-- Wedge-separated logarithmic Gamma growth from Binet-Stirling.

The literal principal-arctangent Binet remainder in this package is not a
closed-boundary kernel on the imaginary axis, so the sectorial log-norm owner
statement requires quantitative separation from that boundary. -/
theorem Complex.Gamma_closedRightHalfPlane_log_norm_bound_classical
    (ε : ℝ)
    (hε : 0 < ε) :
    ∃ R : ℝ, ∃ C : ℝ, ∃ m : ℕ,
      0 < R ∧ 0 < C ∧
      ∀ z : ℂ,
        0 < z.re →
          ε ≤ z.re / ‖z‖ →
          R ≤ ‖z‖ →
            Real.log ‖Complex.Gamma z‖ ≤
              C * (1 + ‖z‖) ^ m := by
  exact
    Complex.Gamma_sectorSeparated_log_norm_bound_from_Binet ε hε

end

end LFunctions
end Boundary
