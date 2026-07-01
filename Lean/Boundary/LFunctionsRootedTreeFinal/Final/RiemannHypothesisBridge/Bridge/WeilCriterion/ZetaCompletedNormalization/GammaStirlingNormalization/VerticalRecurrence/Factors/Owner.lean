import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalization.GammaStirlingNormalization.VerticalRecurrence.Recurrence.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalization.GammaStirlingNormalization.VerticalRecurrence.FactorBounds
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalization.GammaStirlingNormalization.SectorialLog.Owner

/-!
# Vertical recurrence: factor bounds

This file owns per-factor analysis on the vertical strip, including
imaginary-coordinate properties, real-part bounds, and two-sided estimates.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open scoped Filter Topology
local notation "π" => Real.pi

theorem Complex.Gamma_norm_eq_shifted_norm_div_gammaRecurrenceProduct_norm
    {z : ℂ}
    (N : ℕ)
    (hfactor_ne :
      ∀ j : ℕ,
        j < N →
          z + (j : ℂ) ≠ 0) :
    ‖Complex.Gamma z‖ =
      ‖Complex.Gamma (z + (N : ℂ))‖ /
        ‖Complex.gammaRecurrenceProduct z N‖ := by
  have hgamma :
      Complex.Gamma z =
        Complex.Gamma (z + (N : ℂ)) /
          Complex.gammaRecurrenceProduct z N :=
    Complex.Gamma_eq_shifted_div_gammaRecurrenceProduct N hfactor_ne
  calc
    ‖Complex.Gamma z‖ =
        ‖Complex.Gamma (z + (N : ℂ)) /
          Complex.gammaRecurrenceProduct z N‖ :=
      congrArg norm hgamma
    _ =
        ‖Complex.Gamma (z + (N : ℂ))‖ /
          ‖Complex.gammaRecurrenceProduct z N‖ :=
      norm_div (Complex.Gamma (z + (N : ℂ)))
        (Complex.gammaRecurrenceProduct z N)

/-- Per-factor two-sided bounds for deterministic recurrence factors on a fixed
vertical strip. -/
theorem Complex.gammaRecurrenceProduct_factor_twoSided_bounds_on_verticalStrip
    (A B : ℝ)
    (N : ℕ) :
    ∃ H : ℝ, ∃ C : ℝ, ∃ c : ℝ,
      0 < H ∧
      0 < C ∧
      0 < c ∧
      ∀ x y : ℝ,
        A ≤ x →
        x ≤ B →
        H ≤ ‖y‖ →
          ∀ j : ℕ,
            j < N →
              ‖Complex.fixedRealPartVerticalPoint x y + (j : ℂ)‖ ≤
                C * (1 + ‖y‖) ∧
              c * (1 + ‖y‖) ≤
                ‖Complex.fixedRealPartVerticalPoint x y + (j : ℂ)‖ := by
  match Complex.gammaRecurrenceProduct_factor_upper_on_verticalStrip A B N with
  | ⟨C, hC_pos, hC⟩ =>
      let c : ℝ := 1 / 2
      have hc_pos : 0 < c :=
        one_div_pos.mpr two_pos
      have hpointwise :
          ∀ x y : ℝ,
            A ≤ x →
            x ≤ B →
            (1 : ℝ) ≤ ‖y‖ →
              ∀ j : ℕ,
                j < N →
                  ‖Complex.fixedRealPartVerticalPoint x y + (j : ℂ)‖ ≤
                    C * (1 + ‖y‖) ∧
                  c * (1 + ‖y‖) ≤
                    ‖Complex.fixedRealPartVerticalPoint x y + (j : ℂ)‖ := by
        intro x y hxA hxB hy j hj
        exact
          ⟨hC x y hxA hxB j hj,
            Complex.gammaRecurrenceProduct_factor_largeHeight_lower j hy⟩
      exact ⟨1, C, c, zero_lt_one, hC_pos, hc_pos, hpointwise⟩

/-- Norm of the deterministic recurrence product as the finite product of
factor norms. -/
theorem Complex.gammaRecurrenceProduct_norm_eq_prod_factor_norms
    (z : ℂ)
    (N : ℕ) :
    ‖Complex.gammaRecurrenceProduct z N‖ =
      Finset.prod (Finset.range N) (fun j : ℕ => ‖z + (j : ℂ)‖) := by
  calc
    ‖Complex.gammaRecurrenceProduct z N‖ =
        Complex.abs (Finset.prod (Finset.range N)
          (fun j : ℕ => z + (j : ℂ))) :=
      Complex.norm_eq_abs (Complex.gammaRecurrenceProduct z N)
    _ = Finset.prod (Finset.range N)
        (fun j : ℕ => Complex.abs (z + (j : ℂ))) :=
      Complex.abs_prod (Finset.range N) (fun j : ℕ => z + (j : ℂ))
    _ = Finset.prod (Finset.range N) (fun j : ℕ => ‖z + (j : ℂ)‖) :=
      Finset.prod_congr rfl
        (fun j hj =>
          (Complex.norm_eq_abs (z + (j : ℂ))).symm)

/-- Uniform finite-product upper estimate from per-factor upper estimates. -/
theorem real_finset_range_prod_upper_of_factor_le
    (N : ℕ)
    {M : ℝ}
    {f : ℕ → ℝ}
    (hM_nonneg : 0 ≤ M)
    (hf_nonneg : ∀ j : ℕ, j < N → 0 ≤ f j)
    (hf_le : ∀ j : ℕ, j < N → f j ≤ M) :
    Finset.prod (Finset.range N) f ≤ M ^ N := by
  have : 0 ≤ M :=
    hM_nonneg
  have hprod_le :
      Finset.prod (Finset.range N) f ≤
        Finset.prod (Finset.range N) (fun _ : ℕ => M) :=
    Finset.prod_le_prod
      (fun j hj => hf_nonneg j (Finset.mem_range.mp hj))
      (fun j hj => hf_le j (Finset.mem_range.mp hj))
  have hconst :
      Finset.prod (Finset.range N) (fun _ : ℕ => M) =
        M ^ (Finset.range N).card :=
    Finset.prod_const M
  have hcard :
      (Finset.range N).card = N :=
    Finset.card_range N
  have hconst_N :
      Finset.prod (Finset.range N) (fun _ : ℕ => M) = M ^ N :=
    Eq.trans hconst (congrArg (fun n : ℕ => M ^ n) hcard)
  exact le_trans hprod_le (le_of_eq hconst_N)

/-- Uniform finite-product lower estimate from per-factor lower estimates. -/
theorem real_finset_range_prod_lower_of_factor_ge
    (N : ℕ)
    {m : ℝ}
    {f : ℕ → ℝ}
    (hm_nonneg : 0 ≤ m)
    (hf_ge : ∀ j : ℕ, j < N → m ≤ f j) :
    m ^ N ≤ Finset.prod (Finset.range N) f := by
  have hprod_le :
      Finset.prod (Finset.range N) (fun _ : ℕ => m) ≤
        Finset.prod (Finset.range N) f :=
    Finset.prod_le_prod
      (fun j hj => hm_nonneg)
      (fun j hj => hf_ge j (Finset.mem_range.mp hj))
  have hconst :
      Finset.prod (Finset.range N) (fun _ : ℕ => m) =
        m ^ (Finset.range N).card :=
    Finset.prod_const m
  have hcard :
      (Finset.range N).card = N :=
    Finset.card_range N
  have hconst_N :
      Finset.prod (Finset.range N) (fun _ : ℕ => m) = m ^ N :=
    Eq.trans hconst (congrArg (fun n : ℕ => m ^ n) hcard)
  calc
    m ^ N = Finset.prod (Finset.range N) (fun _ : ℕ => m) :=
      hconst_N.symm
    _ ≤ Finset.prod (Finset.range N) f :=
      hprod_le

/-- Convert a natural power to the real-power notation used by the Gamma
envelope statements. -/
theorem real_pow_natCast_eq_rpow
    {r : ℝ}
    (hr : 0 ≤ r)
    (N : ℕ) :
    r ^ N = r ^ (N : ℝ) := by
  have : 0 ≤ r :=
    hr
  exact (Real.rpow_natCast r N).symm

/-- Finite products preserve uniform per-factor polynomial upper/lower bounds
for the deterministic Gamma recurrence product. -/
theorem Complex.gammaRecurrenceProduct_verticalStrip_twoSided_bounds_of_factor_bounds
    (A B : ℝ)
    (N : ℕ)
    (hfactor :
      ∃ H : ℝ, ∃ C : ℝ, ∃ c : ℝ,
        0 < H ∧
        0 < C ∧
        0 < c ∧
        ∀ x y : ℝ,
          A ≤ x →
          x ≤ B →
          H ≤ ‖y‖ →
            ∀ j : ℕ,
              j < N →
                ‖Complex.fixedRealPartVerticalPoint x y + (j : ℂ)‖ ≤
                  C * (1 + ‖y‖) ∧
                c * (1 + ‖y‖) ≤
                  ‖Complex.fixedRealPartVerticalPoint x y + (j : ℂ)‖) :
    ∃ H : ℝ, ∃ C : ℝ, ∃ c : ℝ,
      0 < H ∧
      0 < C ∧
      0 < c ∧
      ∀ x y : ℝ,
        A ≤ x →
        x ≤ B →
        H ≤ ‖y‖ →
          ‖Complex.gammaRecurrenceProduct
              (Complex.fixedRealPartVerticalPoint x y) N‖ ≤
            C * (1 + ‖y‖) ^ (N : ℝ) ∧
          c * (1 + ‖y‖) ^ (N : ℝ) ≤
            ‖Complex.gammaRecurrenceProduct
              (Complex.fixedRealPartVerticalPoint x y) N‖ := by
  match hfactor with
  | ⟨H, C, c, hH_pos, hC_pos, hc_pos, hfactor_pointwise⟩ =>
      have hC_pow_pos : 0 < C ^ N :=
        pow_pos hC_pos N
      have hc_pow_pos : 0 < c ^ N :=
        pow_pos hc_pos N
      have hpointwise :
          ∀ x y : ℝ,
            A ≤ x →
            x ≤ B →
            H ≤ ‖y‖ →
              ‖Complex.gammaRecurrenceProduct
                  (Complex.fixedRealPartVerticalPoint x y) N‖ ≤
                C ^ N * (1 + ‖y‖) ^ (N : ℝ) ∧
              c ^ N * (1 + ‖y‖) ^ (N : ℝ) ≤
                ‖Complex.gammaRecurrenceProduct
                  (Complex.fixedRealPartVerticalPoint x y) N‖ := by
        intro x y hxA hxB hy
        let R : ℝ := 1 + ‖y‖
        have hR_nonneg : 0 ≤ R :=
          add_nonneg zero_le_one (norm_nonneg y)
        have hCR_nonneg : 0 ≤ C * R :=
          mul_nonneg (le_of_lt hC_pos) hR_nonneg
        have hcR_nonneg : 0 ≤ c * R :=
          mul_nonneg (le_of_lt hc_pos) hR_nonneg
        have hprod_norm :
            ‖Complex.gammaRecurrenceProduct
                (Complex.fixedRealPartVerticalPoint x y) N‖ =
              Finset.prod (Finset.range N)
                (fun j : ℕ =>
                  ‖Complex.fixedRealPartVerticalPoint x y + (j : ℂ)‖) :=
          Complex.gammaRecurrenceProduct_norm_eq_prod_factor_norms
            (Complex.fixedRealPartVerticalPoint x y) N
        have hupper_prod :
            Finset.prod (Finset.range N)
                (fun j : ℕ =>
                  ‖Complex.fixedRealPartVerticalPoint x y + (j : ℂ)‖) ≤
              (C * R) ^ N :=
          real_finset_range_prod_upper_of_factor_le
            N
            hCR_nonneg
            (fun j hj =>
              norm_nonneg (Complex.fixedRealPartVerticalPoint x y + (j : ℂ)))
            (fun j hj =>
              (hfactor_pointwise x y hxA hxB hy j hj).1)
        have hlower_prod :
            (c * R) ^ N ≤
              Finset.prod (Finset.range N)
                (fun j : ℕ =>
                  ‖Complex.fixedRealPartVerticalPoint x y + (j : ℂ)‖) :=
          real_finset_range_prod_lower_of_factor_ge
            N
            hcR_nonneg
            (fun j hj =>
              (hfactor_pointwise x y hxA hxB hy j hj).2)
        have hupper_target :
            (C * R) ^ N =
              C ^ N * R ^ (N : ℝ) := by
          have hmul_pow : (C * R) ^ N = C ^ N * R ^ N :=
            mul_pow C R N
          have hR_pow : R ^ N = R ^ (N : ℝ) :=
            real_pow_natCast_eq_rpow hR_nonneg N
          exact
            Eq.trans hmul_pow
              (congrArg (fun t : ℝ => C ^ N * t) hR_pow)
        have hlower_target :
            (c * R) ^ N =
              c ^ N * R ^ (N : ℝ) := by
          have hmul_pow : (c * R) ^ N = c ^ N * R ^ N :=
            mul_pow c R N
          have hR_pow : R ^ N = R ^ (N : ℝ) :=
            real_pow_natCast_eq_rpow hR_nonneg N
          exact
            Eq.trans hmul_pow
              (congrArg (fun t : ℝ => c ^ N * t) hR_pow)
        constructor
        · calc
            ‖Complex.gammaRecurrenceProduct
                (Complex.fixedRealPartVerticalPoint x y) N‖ =
                Finset.prod (Finset.range N)
                  (fun j : ℕ =>
                    ‖Complex.fixedRealPartVerticalPoint x y + (j : ℂ)‖) :=
              hprod_norm
            _ ≤ (C * R) ^ N :=
              hupper_prod
            _ = C ^ N * R ^ (N : ℝ) :=
              hupper_target
        · calc
            c ^ N * R ^ (N : ℝ) = (c * R) ^ N :=
              hlower_target.symm
            _ ≤
                Finset.prod (Finset.range N)
                  (fun j : ℕ =>
                    ‖Complex.fixedRealPartVerticalPoint x y + (j : ℂ)‖) :=
              hlower_prod
            _ =
                ‖Complex.gammaRecurrenceProduct
                  (Complex.fixedRealPartVerticalPoint x y) N‖ :=
              hprod_norm.symm
      exact ⟨H, C ^ N, c ^ N, hH_pos, hC_pow_pos, hc_pow_pos, hpointwise⟩

end

end LFunctions
end Boundary
