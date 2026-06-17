import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalization.EulerContinuationTransport.EulerMaclaurinFormula.PoleClearedFormula

/-!
Majorant and growth estimates for the pole-cleared first-order Bernoulli integral
remainder on `1 ≤ Re s ≤ 2`.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open scoped Filter Topology
open Filter MeasureTheory Set
local notation "π" => Real.pi

/-- Bochner norm domination for the Bernoulli-periodic Euler-Maclaurin core by
the scalar real-power tail integral. -/
theorem eulerMaclaurin_firstPeriodicBernoulli_cpow_tail_norm_integral_domination
    (z : ℂ)
    (hz_one : 1 ≤ z.re)
    (_hz_two : z.re ≤ 2) :
    ‖eulerMaclaurinPoleClearedZetaBernoulliIntegralCore z‖ ≤
      ∫ x in Set.Ioi (((eulerMaclaurinPoleClearedZetaCutoff z : ℕ) : ℝ)),
        x ^ (-(z.re + 1)) := by
  let N : ℝ := ((eulerMaclaurinPoleClearedZetaCutoff z : ℕ) : ℝ)
  let s : Set ℝ := Set.Ioi N
  let f : ℝ → ℂ :=
    fun x =>
      ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) *
        (((x : ℝ) : ℂ) ^ (-(z + 1)))
  let g : ℝ → ℝ :=
    fun x => x ^ (-(z.re + 1))
  have hN_one : (1 : ℝ) ≤ N :=
    one_le_eulerMaclaurinPoleClearedZetaCutoff_real z
  have hN_pos : 0 < N :=
    lt_of_lt_of_le zero_lt_one hN_one
  have htwo_le : (2 : ℝ) ≤ z.re + 1 := by
    calc
      (2 : ℝ) = 1 + 1 := by
        exact (one_add_one_eq_two : (1 : ℝ) + 1 = 2).symm
      _ ≤ z.re + 1 :=
        add_le_add hz_one le_rfl
  have hone_lt : (1 : ℝ) < z.re + 1 :=
    lt_of_lt_of_le one_lt_two htwo_le
  have ha : -(z.re + 1) < -(1 : ℝ) :=
    neg_lt_neg hone_lt
  have hg : Integrable g (volume.restrict s) :=
    integrableOn_Ioi_rpow_of_lt ha hN_pos
  have hbound : ∀ᵐ x ∂volume.restrict s, ‖f x‖ ≤ g x := by
    exact (ae_restrict_mem measurableSet_Ioi).mono
      (fun x hx =>
        by
          have hx_pos : 0 < x :=
            lt_trans hN_pos hx
          have hB_abs :
              |eulerMaclaurinFirstPeriodicBernoulli x| ≤ 1 :=
            eulerMaclaurinFirstPeriodicBernoulli_abs_le_one x
          have hB_norm :
              ‖((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ)‖ ≤ 1 := by
            calc
              ‖((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ)‖ =
                  |eulerMaclaurinFirstPeriodicBernoulli x| := by
                exact RCLike.norm_ofReal (eulerMaclaurinFirstPeriodicBernoulli x)
              _ ≤ 1 :=
                hB_abs
          have hcpow :
              ‖((x : ℝ) : ℂ) ^ (-(z + 1))‖ ≤ g x :=
            norm_real_cpow_neg_z_add_one_le_rpow hx_pos z hz_one
          have hg_nonneg : 0 ≤ g x :=
            Real.rpow_nonneg (le_of_lt hx_pos) (-(z.re + 1))
          calc
            ‖f x‖ =
                ‖((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ)‖ *
                  ‖((x : ℝ) : ℂ) ^ (-(z + 1))‖ := by
              exact norm_mul
                ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ)
                (((x : ℝ) : ℂ) ^ (-(z + 1)))
            _ ≤ 1 * g x :=
              mul_le_mul hB_norm hcpow
                (norm_nonneg (((x : ℝ) : ℂ) ^ (-(z + 1))))
                zero_le_one
            _ = g x := by
              exact one_mul (g x)
      )
  exact norm_integral_le_of_norm_le hg hbound

/-- Scalar improper-integral tail estimate for the first periodic Bernoulli
Euler-Maclaurin kernel.

This is the real-variable analytic input behind the zeta remainder bound:
`|B₁({x})| ≤ 1`, the cutoff is strictly positive, the positive-real `cpow` norm
formula, and the tail estimate for `∫_N^∞ x^{-σ-1} dx` with `σ ≥ 1`. -/
theorem eulerMaclaurin_firstPeriodicBernoulli_cpow_tail_integral_norm_le_one_standard
    (z : ℂ)
    (hz_one : 1 ≤ z.re)
    (hz_two : z.re ≤ 2) :
    ‖eulerMaclaurinPoleClearedZetaBernoulliIntegralCore z‖ ≤ 1 := by
  have hdom :
      ‖eulerMaclaurinPoleClearedZetaBernoulliIntegralCore z‖ ≤
        ∫ x in Set.Ioi (((eulerMaclaurinPoleClearedZetaCutoff z : ℕ) : ℝ)),
          x ^ (-(z.re + 1)) :=
    eulerMaclaurin_firstPeriodicBernoulli_cpow_tail_norm_integral_domination
      z hz_one hz_two
  have hcutoff :
      (1 : ℝ) ≤ ((eulerMaclaurinPoleClearedZetaCutoff z : ℕ) : ℝ) :=
    one_le_eulerMaclaurinPoleClearedZetaCutoff_real z
  have htail :
      ∫ x in Set.Ioi (((eulerMaclaurinPoleClearedZetaCutoff z : ℕ) : ℝ)),
          x ^ (-(z.re + 1)) ≤ 1 :=
    integral_Ioi_rpow_neg_re_add_one_le_one_of_one_le_cutoff
      hcutoff hz_one
  exact le_trans hdom htail

/-- Standard Bernoulli-periodic tail majorant for the Euler-Maclaurin zeta
remainder core on the closed strip `1 ≤ Re z ≤ 2`. -/
theorem eulerMaclaurinPoleClearedZetaBernoulliIntegralCore_norm_le_one
    (z : ℂ)
    (hz_one : 1 ≤ z.re)
    (hz_two : z.re ≤ 2) :
    ‖eulerMaclaurinPoleClearedZetaBernoulliIntegralCore z‖ ≤ 1 := by
  exact
    eulerMaclaurin_firstPeriodicBernoulli_cpow_tail_integral_norm_le_one_standard
      z hz_one hz_two

/-- Polynomial bound for the explicit Bernoulli-periodic integral remainder.

The proof is the standard majorization:
`|B₁({x})| ≤ 1`, `‖x^{-z-1}‖ ≤ x^{-Re z-1}` for positive `x`, and
`∫_N^∞ x^{-Re z-1} dx ≤ 1` on `1 ≤ Re z`, followed by the elementary
polynomial bound for `(z - 1) z`. -/
theorem eulerMaclaurinPoleClearedZetaBernoulliIntegralRemainder_polynomial_bound :
    ∃ C : ℝ, ∃ m : ℕ,
      0 < C ∧
      ∀ z : ℂ,
        1 ≤ z.re →
        z.re ≤ 2 →
        ‖eulerMaclaurinPoleClearedZetaBernoulliIntegralRemainder z‖ ≤
          C * (1 + ‖z‖) ^ m := by
  exact ⟨1, 2, zero_lt_one, fun z hz_one hz_two => by
    let H : ℝ := 1 + ‖z‖
    have hH_nonneg : 0 ≤ H :=
      le_trans zero_le_one (le_add_of_nonneg_right (norm_nonneg z))
    have hz_norm : ‖z‖ ≤ H :=
      le_add_of_nonneg_left zero_le_one
    have hz_sub_norm : ‖z - 1‖ ≤ H :=
      eulerMaclaurinPoleClearedZetaFinitePart_poleFactor_norm_le_height z
    have hleft :
        ‖(z - 1) * z‖ ≤ H * H := by
      calc
        ‖(z - 1) * z‖ = ‖z - 1‖ * ‖z‖ := by
          exact norm_mul (z - 1) z
        _ ≤ H * H :=
          mul_le_mul hz_sub_norm hz_norm (norm_nonneg z) hH_nonneg
    have hcore :
        ‖eulerMaclaurinPoleClearedZetaBernoulliIntegralCore z‖ ≤ 1 :=
      eulerMaclaurinPoleClearedZetaBernoulliIntegralCore_norm_le_one z hz_one hz_two
    have hprod :
        ‖-((z - 1) * z) *
            eulerMaclaurinPoleClearedZetaBernoulliIntegralCore z‖ ≤
          (H * H) * 1 := by
      calc
        ‖-((z - 1) * z) *
            eulerMaclaurinPoleClearedZetaBernoulliIntegralCore z‖ =
            ‖-((z - 1) * z)‖ *
              ‖eulerMaclaurinPoleClearedZetaBernoulliIntegralCore z‖ := by
          exact norm_mul (-((z - 1) * z))
            (eulerMaclaurinPoleClearedZetaBernoulliIntegralCore z)
        _ = ‖(z - 1) * z‖ *
              ‖eulerMaclaurinPoleClearedZetaBernoulliIntegralCore z‖ := by
          exact congrArg
            (fun x : ℝ =>
              x * ‖eulerMaclaurinPoleClearedZetaBernoulliIntegralCore z‖)
            (norm_neg ((z - 1) * z))
        _ ≤ (H * H) * 1 :=
          mul_le_mul hleft hcore
            (norm_nonneg (eulerMaclaurinPoleClearedZetaBernoulliIntegralCore z))
            (mul_nonneg hH_nonneg hH_nonneg)
    have hcollapse : (H * H) * 1 = (1 : ℝ) * H ^ (2 : ℕ) := by
      calc
        (H * H) * 1 = H * H := by
          exact mul_one (H * H)
        _ = H ^ (2 : ℕ) := by
          exact (pow_two H).symm
        _ = (1 : ℝ) * H ^ (2 : ℕ) := by
          exact (one_mul (H ^ (2 : ℕ))).symm
    have htarget : (1 : ℝ) * H ^ (2 : ℕ) =
        (1 : ℝ) * (1 + ‖z‖) ^ (2 : ℕ) := rfl
    exact le_trans hprod (le_of_eq (hcollapse.trans htarget))⟩

/-- Standard Euler-Maclaurin Bernoulli-periodic integral estimate for the
pole-cleared remainder on `1 ≤ Re s ≤ 2`.

This is the analytic owner input: after multiplying the usual
Euler-Maclaurin remainder
`s ∫_N^∞ B₁({x}) x^{-s-1} dx` by `s - 1`, the bounded Bernoulli function,
`‖x^{-s-1}‖ ≤ x^{-Re s - 1}`, and
`N = ⌊2 + ‖s‖⌋₊ ≥ 1` give a fixed polynomial envelope in `1 + ‖s‖`. -/
theorem eulerMaclaurinPoleClearedZetaRemainderTerm_bernoulliIntegral_polynomial_bound_standard :
    ∃ C : ℝ, ∃ m : ℕ,
      0 < C ∧
      ∀ z : ℂ,
        1 ≤ z.re →
        z.re ≤ 2 →
        ‖eulerMaclaurinPoleClearedZetaRemainderTerm z‖ ≤ C * (1 + ‖z‖) ^ m := by
  match eulerMaclaurinPoleClearedZetaBernoulliIntegralRemainder_polynomial_bound with
  | Exists.intro C hC_pack =>
      match hC_pack with
      | Exists.intro m hm_pack =>
          match hm_pack with
          | And.intro hC hbound =>
              exact Exists.intro C (Exists.intro m (And.intro hC
                (fun z hz_one hz_two =>
                  have hformula :
                      eulerMaclaurinPoleClearedZetaRemainderTerm z =
                        eulerMaclaurinPoleClearedZetaBernoulliIntegralRemainder z :=
                    eulerMaclaurinPoleClearedZetaRemainderTerm_eq_bernoulliIntegralRemainder
                      z hz_one hz_two
                  Eq.subst
                    (motive := fun w : ℂ => ‖w‖ ≤ C * (1 + ‖z‖) ^ m)
                    hformula.symm
                    (hbound z hz_one hz_two))))

/-- Polynomial control for the pole-cleared Euler-Maclaurin remainder from the
standard Bernoulli-periodic integral majorant.

Analytically this is the estimate for
`(s - 1) · s ∫_N^∞ B₁({x}) x^{-s-1} dx` with
`N = ⌊2 + ‖s‖⌋₊`, using boundedness of `B₁`, `1 ≤ Re s ≤ 2`, and the
height-comparable cutoff. -/
theorem eulerMaclaurinPoleClearedZetaRemainderTerm_integral_majorant_polynomial_bound :
    ∃ C : ℝ, ∃ m : ℕ,
      0 < C ∧
      ∀ z : ℂ,
        1 ≤ z.re →
        z.re ≤ 2 →
        ‖eulerMaclaurinPoleClearedZetaRemainderTerm z‖ ≤ C * (1 + ‖z‖) ^ m := by
  exact eulerMaclaurinPoleClearedZetaRemainderTerm_bernoulliIntegral_polynomial_bound_standard

end
end LFunctions
end Boundary
