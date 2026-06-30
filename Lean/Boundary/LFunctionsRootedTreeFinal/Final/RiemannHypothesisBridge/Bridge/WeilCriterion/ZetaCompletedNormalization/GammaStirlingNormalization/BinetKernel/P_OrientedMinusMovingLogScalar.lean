import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalization.GammaStirlingNormalization.BinetKernel.O_OrientedMovingLogAssembly
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ClassicalAnalysis.GammaBinetStirling.BinetMovingLogFarUpper

/-!
# Oriented minus moving-log scalar estimates

This file owns the BinetKernel-facing scalar absorptions for the oriented
minus moving logarithmic branch-wall spike.  It keeps the transport to the
standard Binet decaying-tail integral in the kernel layer, where that integral
is owned.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open scoped Topology
open Filter
open MeasureTheory

/-- A nonnegative constant pure-exponential bounded-window integral is absorbed
by the standard scaled Binet decaying-tail integral. -/
theorem Complex.binetSecondFormula_constant_expWeighted_scaled_decay
    (K : ℝ)
    (hK_nonneg : 0 ≤ K) :
    ∃ C : ℝ,
      0 < C ∧
      ∀ w : ℂ,
        0 < w.re →
        2 ≤ ‖w‖ →
          2 * ∫ t : ℝ in Set.Ioc (‖w‖ / 2) (2 * ‖w‖),
              K / Real.exp ((2 : ℝ) * Real.pi * t) ≤
            (C / ‖w‖) *
              Complex.binetSecondFormulaDecayingTailIntegral w := by
  match Complex.binetSecondFormula_decayingTailIntegral_expLower_owner with
  | ⟨c, hc_pos, htail_lower⟩ =>
      let A : ℝ := 2 * K + 1
      let C : ℝ := A / c
      have hA_nonneg : 0 ≤ A := by
        exact
          add_nonneg
            (mul_nonneg zero_le_two hK_nonneg)
            zero_le_one
      have hA_pos : 0 < A := by
        exact
          add_pos_of_nonneg_of_pos
            (mul_nonneg zero_le_two hK_nonneg)
            zero_lt_one
      have hC_pos : 0 < C :=
        div_pos hA_pos hc_pos
      exact
        ⟨C, hC_pos,
          fun w _hw_re_pos hw_norm_two =>
            let N : ℝ := ‖w‖
            let E : ℝ := Real.exp (-Real.pi * ‖w‖)
            let J : ℝ := Complex.binetSecondFormulaDecayingTailIntegral w
            have hN_pos : 0 < N :=
              lt_of_lt_of_le zero_lt_two hw_norm_two
            have hE_pos : 0 < E :=
              Real.exp_pos (-Real.pi * ‖w‖)
            have hconst :
                ∫ t : ℝ in Set.Ioc (‖w‖ / 2) (2 * ‖w‖),
                    K / Real.exp ((2 : ℝ) * Real.pi * t) ≤
                  K * E :=
              Complex.binetSecondFormula_constant_expWeighted_integral_le_expScale
                K hK_nonneg w
            have htwice_const :
                2 * ∫ t : ℝ in Set.Ioc (‖w‖ / 2) (2 * ‖w‖),
                    K / Real.exp ((2 : ℝ) * Real.pi * t) ≤
                  2 * (K * E) :=
              mul_le_mul_of_nonneg_left hconst zero_le_two
            have htwice_scale :
                2 * (K * E) = (2 * K) * E := by
              exact (mul_assoc (2 : ℝ) K E).symm
            have htwoK_le_A :
                2 * K ≤ A := by
              have hraw : 2 * K ≤ 2 * K + 1 :=
                le_add_of_nonneg_right zero_le_one
              exact hraw
            have htwoK_E_le_A_E :
                (2 * K) * E ≤ A * E :=
              mul_le_mul_of_nonneg_right htwoK_le_A (le_of_lt hE_pos)
            have hJ_lower :
                c * N * E ≤ J :=
              htail_lower w hw_norm_two
            have hcoeff_nonneg : 0 ≤ C / N :=
              div_nonneg (le_of_lt hC_pos) (le_of_lt hN_pos)
            have hscaled_lower :
                (C / N) * (c * N * E) ≤ (C / N) * J :=
              mul_le_mul_of_nonneg_left hJ_lower hcoeff_nonneg
            have hscaled_left :
                (C / N) * (c * N * E) = A * E := by
              have hc_ne : c ≠ 0 :=
                ne_of_gt hc_pos
              have hN_ne : N ≠ 0 :=
                ne_of_gt hN_pos
              calc
                (C / N) * (c * N * E) =
                    ((A / c) / N) * (c * N * E) := by
                  rfl
                _ = ((A / c) / N) * ((c * N) * E) := by
                  exact Eq.refl (((A / c) / N) * ((c * N) * E))
                _ = (((A / c) / N) * (c * N)) * E := by
                  exact (mul_assoc ((A / c) / N) (c * N) E).symm
                _ = ((A / c) * c) * E := by
                  exact congrArg (fun x : ℝ => x * E)
                    (calc
                      ((A / c) / N) * (c * N) =
                          (((A / c) / N) * N) * c := by
                        calc
                          ((A / c) / N) * (c * N) =
                              ((A / c) / N) * (N * c) := by
                            exact congrArg (fun x : ℝ => ((A / c) / N) * x)
                              (mul_comm c N)
                          _ = (((A / c) / N) * N) * c := by
                            exact (mul_assoc ((A / c) / N) N c).symm
                      _ = (A / c) * c := by
                        exact congrArg (fun x : ℝ => x * c)
                          (div_mul_cancel₀ (A / c) hN_ne))
                _ = A * E := by
                  exact congrArg (fun x : ℝ => x * E)
                    (div_mul_cancel₀ A hc_ne)
            have htarget :
                A * E ≤ (C / ‖w‖) * J :=
              Eq.subst
                (motive := fun x : ℝ => x ≤ (C / ‖w‖) * J)
                hscaled_left
                hscaled_lower
            le_trans htwice_const
              (le_trans
                (le_trans (le_of_eq htwice_scale) htwoK_E_le_A_E)
                htarget)⟩

/-- Moderate upper-center denominator branch-wall logarithmic spikes are
absorbed by the standard scaled Binet decaying-tail integral. -/
theorem Complex.binetSecondFormula_minusMovingLog_moderateUpperCenter_scaled_decay :
    ∃ Cmoderate : ℝ,
      0 < Cmoderate ∧
      ∀ w : ℂ,
        0 < w.re →
        2 ≤ ‖w‖ →
        ‖w‖ / 2 ≤ w.im →
        w.im ≤ (3 * ‖w‖) / 4 →
          2 * ∫ t : ℝ in Set.Ioc (‖w‖ / 2) (2 * ‖w‖),
              (2 * Real.log ((3 * ‖w‖) / max w.re |w.im - t|)) /
                Real.exp ((2 : ℝ) * Real.pi * t) ≤
            (Cmoderate / ‖w‖) *
              Complex.binetSecondFormulaDecayingTailIntegral w := by
  let K : ℝ := 2 * Real.log 12
  have hlog12_nonneg : 0 ≤ Real.log 12 :=
    Real.log_nonneg Real.one_le_twelve_far_upper
  have hK_nonneg : 0 ≤ K :=
    mul_nonneg zero_le_two hlog12_nonneg
  match Complex.binetSecondFormula_constant_expWeighted_scaled_decay K hK_nonneg with
  | ⟨C, hC_pos, hC_bound⟩ =>
      exact
        ⟨C, hC_pos,
          fun w hw_re_pos hw_large hleft hright =>
            have hmoderate :
                ∫ t : ℝ in Set.Ioc (‖w‖ / 2) (2 * ‖w‖),
                    (2 * Real.log ((3 * ‖w‖) / max w.re |w.im - t|)) /
                      Real.exp ((2 : ℝ) * Real.pi * t) ≤
                  ∫ t : ℝ in Set.Ioc (‖w‖ / 2) (2 * ‖w‖),
                    K / Real.exp ((2 : ℝ) * Real.pi * t) :=
              Complex.binetSecondFormula_minusMovingLog_integral_le_log_twelve_of_moderateUpperCenter
                hw_re_pos hleft hright
            have htwice :
                2 * ∫ t : ℝ in Set.Ioc (‖w‖ / 2) (2 * ‖w‖),
                    (2 * Real.log ((3 * ‖w‖) / max w.re |w.im - t|)) /
                      Real.exp ((2 : ℝ) * Real.pi * t) ≤
                  2 * ∫ t : ℝ in Set.Ioc (‖w‖ / 2) (2 * ‖w‖),
                    K / Real.exp ((2 : ℝ) * Real.pi * t) :=
              mul_le_mul_of_nonneg_left hmoderate zero_le_two
            le_trans htwice (hC_bound w hw_re_pos hw_large)⟩

/-- Nonpositive-center lower-side denominator branch-wall logarithmic spikes
are absorbed by the standard scaled Binet decaying-tail integral. -/
theorem Complex.binetSecondFormula_minusMovingLog_nonpositiveCenter_scaled_decay :
    ∃ Cnonpos : ℝ,
      0 < Cnonpos ∧
      ∀ w : ℂ,
        0 < w.re →
        2 ≤ ‖w‖ →
        w.im ≤ 0 →
          2 * ∫ t : ℝ in Set.Ioc (‖w‖ / 2) (2 * ‖w‖),
              (2 * Real.log ((3 * ‖w‖) / max w.re |w.im - t|)) /
                Real.exp ((2 : ℝ) * Real.pi * t) ≤
            (Cnonpos / ‖w‖) *
              Complex.binetSecondFormulaDecayingTailIntegral w := by
  let K : ℝ := 2 * Real.log 12
  have hlog12_nonneg : 0 ≤ Real.log 12 :=
    Real.log_nonneg Real.one_le_twelve_far_upper
  have hK_nonneg : 0 ≤ K :=
    mul_nonneg zero_le_two hlog12_nonneg
  match Complex.binetSecondFormula_constant_expWeighted_scaled_decay K hK_nonneg with
  | ⟨C, hC_pos, hC_bound⟩ =>
      exact
        ⟨C, hC_pos,
          fun w hw_re_pos hw_large hw_im_nonpos =>
            have hnonpos :
                ∫ t : ℝ in Set.Ioc (‖w‖ / 2) (2 * ‖w‖),
                    (2 * Real.log ((3 * ‖w‖) / max w.re |w.im - t|)) /
                      Real.exp ((2 : ℝ) * Real.pi * t) ≤
                  ∫ t : ℝ in Set.Ioc (‖w‖ / 2) (2 * ‖w‖),
                    K / Real.exp ((2 : ℝ) * Real.pi * t) :=
              Complex.binetSecondFormula_minusMovingLog_integral_le_log_twelve_of_im_nonpos
                hw_re_pos hw_im_nonpos
            have htwice :
                2 * ∫ t : ℝ in Set.Ioc (‖w‖ / 2) (2 * ‖w‖),
                    (2 * Real.log ((3 * ‖w‖) / max w.re |w.im - t|)) /
                      Real.exp ((2 : ℝ) * Real.pi * t) ≤
                  2 * ∫ t : ℝ in Set.Ioc (‖w‖ / 2) (2 * ‖w‖),
                    K / Real.exp ((2 : ℝ) * Real.pi * t) :=
              mul_le_mul_of_nonneg_left hnonpos zero_le_two
            le_trans htwice (hC_bound w hw_re_pos hw_large)⟩

/-- Nonnegative lower-center denominator branch-wall logarithmic spikes are
absorbed by the standard scaled Binet decaying-tail integral. -/
theorem Complex.binetSecondFormula_minusMovingLog_nonnegativeLowerCenter_scaled_decay :
    ∃ Clower : ℝ,
      0 < Clower ∧
      ∀ w : ℂ,
        0 < w.re →
        2 ≤ ‖w‖ →
        0 ≤ w.im →
        w.im ≤ ‖w‖ / 2 →
          2 * ∫ t : ℝ in Set.Ioc (‖w‖ / 2) (2 * ‖w‖),
              (2 * Real.log ((3 * ‖w‖) / max w.re |w.im - t|)) /
                Real.exp ((2 : ℝ) * Real.pi * t) ≤
            (Clower / ‖w‖) *
              Complex.binetSecondFormulaDecayingTailIntegral w := by
  let K : ℝ := 2 * Real.log 12
  have hlog12_nonneg : 0 ≤ Real.log 12 :=
    Real.log_nonneg Real.one_le_twelve_far_upper
  have hK_nonneg : 0 ≤ K :=
    mul_nonneg zero_le_two hlog12_nonneg
  match Complex.binetSecondFormula_constant_expWeighted_scaled_decay K hK_nonneg with
  | ⟨C, hC_pos, hC_bound⟩ =>
      exact
        ⟨C, hC_pos,
          fun w hw_re_pos hw_large him_nonneg him_le_half =>
            have hlower :
                ∫ t : ℝ in Set.Ioc (‖w‖ / 2) (2 * ‖w‖),
                    (2 * Real.log ((3 * ‖w‖) / max w.re |w.im - t|)) /
                      Real.exp ((2 : ℝ) * Real.pi * t) ≤
                  ∫ t : ℝ in Set.Ioc (‖w‖ / 2) (2 * ‖w‖),
                    K / Real.exp ((2 : ℝ) * Real.pi * t) :=
              Complex.binetSecondFormula_minusMovingLog_integral_le_log_twelve_of_nonnegativeLowerCenter
                hw_re_pos him_nonneg him_le_half
            have htwice :
                2 * ∫ t : ℝ in Set.Ioc (‖w‖ / 2) (2 * ‖w‖),
                    (2 * Real.log ((3 * ‖w‖) / max w.re |w.im - t|)) /
                      Real.exp ((2 : ℝ) * Real.pi * t) ≤
                  2 * ∫ t : ℝ in Set.Ioc (‖w‖ / 2) (2 * ‖w‖),
                    K / Real.exp ((2 : ℝ) * Real.pi * t) :=
              mul_le_mul_of_nonneg_left hlower zero_le_two
            le_trans htwice (hC_bound w hw_re_pos hw_large)⟩

/-- Far upper-center denominator branch-wall logarithmic spikes are absorbed
by the standard scaled Binet decaying-tail integral. -/
theorem Complex.binetSecondFormula_minusMovingLog_farUpperCenter_scaled_decay :
    ∃ Cfar : ℝ,
      0 < Cfar ∧
      ∀ w : ℂ,
        0 < w.re →
        2 ≤ ‖w‖ →
        (3 * ‖w‖) / 4 ≤ w.im →
          2 * ∫ t : ℝ in Set.Ioc (‖w‖ / 2) (2 * ‖w‖),
              (2 * Real.log ((3 * ‖w‖) / max w.re |w.im - t|)) /
                Real.exp ((2 : ℝ) * Real.pi * t) ≤
            (Cfar / ‖w‖) *
              Complex.binetSecondFormulaDecayingTailIntegral w := by
  match Complex.binetSecondFormula_decayingTailIntegral_expLower_owner with
  | ⟨c, hc_pos, htail_lower⟩ =>
      let K : ℝ := 2 * Real.log 24
      let A : ℝ := 2 * K + 12288 + 1
      let C : ℝ := A / c
      have hlog24_nonneg : 0 ≤ Real.log 24 :=
        Real.log_nonneg Real.one_le_twenty_four
      have hK_nonneg : 0 ≤ K :=
        mul_nonneg zero_le_two hlog24_nonneg
      have hbig_nonneg : (0 : ℝ) ≤ 12288 := by
        exact Real.zero_le_12288
      have hA_nonneg : 0 ≤ A := by
        have htwoK_nonneg : 0 ≤ 2 * K :=
          mul_nonneg zero_le_two hK_nonneg
        exact add_nonneg (add_nonneg htwoK_nonneg hbig_nonneg) zero_le_one
      have hA_pos : 0 < A :=
        add_pos_of_nonneg_of_pos
          (add_nonneg (mul_nonneg zero_le_two hK_nonneg) hbig_nonneg)
          zero_lt_one
      have hC_pos : 0 < C :=
        div_pos hA_pos hc_pos
      exact
        ⟨C, hC_pos,
          fun w hw_re_pos hw_norm_two hfar =>
            let N : ℝ := ‖w‖
            let E : ℝ := Real.exp (-Real.pi * ‖w‖)
            let Q : ℝ := Real.exp (-((5 * Real.pi) / 4) * ‖w‖)
            let J : ℝ := Complex.binetSecondFormulaDecayingTailIntegral w
            have hN_pos : 0 < N :=
              lt_of_lt_of_le zero_lt_two hw_norm_two
            have hE_pos : 0 < E :=
              Real.exp_pos (-Real.pi * ‖w‖)
            have hfar_integral :
                ∫ t : ℝ in Set.Ioc (‖w‖ / 2) (2 * ‖w‖),
                    (2 * Real.log ((3 * ‖w‖) / max w.re |w.im - t|)) /
                      Real.exp ((2 : ℝ) * Real.pi * t) ≤
                  K * E + 96 * ‖w‖ ^ 2 * Q :=
              Complex.binetSecondFormula_farUpperCenter_integral_le_expScale_plus_spike
                hw_re_pos hw_norm_two hfar
            have htwice :
                2 * ∫ t : ℝ in Set.Ioc (‖w‖ / 2) (2 * ‖w‖),
                    (2 * Real.log ((3 * ‖w‖) / max w.re |w.im - t|)) /
                      Real.exp ((2 : ℝ) * Real.pi * t) ≤
                  2 * (K * E + 96 * ‖w‖ ^ 2 * Q) :=
              mul_le_mul_of_nonneg_left hfar_integral zero_le_two
            have hspike_absorb :
                ‖w‖ ^ 2 * Q ≤ 64 * E :=
              Real.sq_mul_exp_neg_five_quarters_pi_le_exp_neg_pi_of_two_le
                hw_norm_two
            have hspike_scaled :
                192 * (‖w‖ ^ 2 * Q) ≤ 192 * (64 * E) :=
              mul_le_mul_of_nonneg_left hspike_absorb
                Real.zero_le_one_ninety_two
            have htwice_scale :
                2 * (K * E + 96 * ‖w‖ ^ 2 * Q) ≤
                  A * E := by
              have hexpand :
                  2 * (K * E + 96 * ‖w‖ ^ 2 * Q) =
                    (2 * K) * E + 192 * (‖w‖ ^ 2 * Q) := by
                calc
                  2 * (K * E + 96 * ‖w‖ ^ 2 * Q) =
                      2 * (K * E) + 2 * (96 * ‖w‖ ^ 2 * Q) := by
                    exact mul_add (2 : ℝ) (K * E) (96 * ‖w‖ ^ 2 * Q)
                  _ = (2 * K) * E + 192 * (‖w‖ ^ 2 * Q) := by
                    exact congrArg₂ HAdd.hAdd
                      (mul_assoc (2 : ℝ) K E).symm
                      (calc
                        2 * (96 * ‖w‖ ^ 2 * Q) =
                            2 * (96 * (‖w‖ ^ 2 * Q)) := by
                          exact congrArg (fun x : ℝ => 2 * x)
                            (mul_assoc (96 : ℝ) (‖w‖ ^ 2) Q)
                        _ = (2 * 96) * (‖w‖ ^ 2 * Q) := by
                          exact (mul_assoc (2 : ℝ) 96 (‖w‖ ^ 2 * Q)).symm
                        _ = 192 * (‖w‖ ^ 2 * Q) := by
                          exact congrArg (fun x : ℝ => x * (‖w‖ ^ 2 * Q))
                            Real.two_mul_ninety_six_eq_one_ninety_two)
              have hspike_to_E :
                  192 * (‖w‖ ^ 2 * Q) ≤ 12288 * E := by
                have hright :
                    192 * (64 * E) = 12288 * E := by
                  calc
                    192 * (64 * E) = (192 * 64) * E := by
                      exact (mul_assoc (192 : ℝ) 64 E).symm
                    _ = 12288 * E := by
                      exact congrArg (fun x : ℝ => x * E)
                        Real.one_ninety_two_mul_sixty_four_eq_12288
                exact le_trans hspike_scaled (le_of_eq hright)
              have hsum :
                  (2 * K) * E + 192 * (‖w‖ ^ 2 * Q) ≤
                    (2 * K) * E + 12288 * E :=
                add_le_add_left hspike_to_E ((2 * K) * E)
              have hcoeff_le :
                  (2 * K) * E + 12288 * E ≤ A * E := by
                have hleft_eq :
                    (2 * K) * E + 12288 * E =
                      (2 * K + 12288) * E := by
                  exact (add_mul (2 * K) 12288 E).symm
                have hcoeff_raw :
                    (2 * K + 12288) * E ≤ A * E := by
                  have hcoeff :
                      2 * K + 12288 ≤ A :=
                    le_add_of_nonneg_right zero_le_one
                  exact mul_le_mul_of_nonneg_right hcoeff (le_of_lt hE_pos)
                exact
                  Eq.subst
                    (motive := fun x : ℝ => x ≤ A * E)
                    hleft_eq.symm
                    hcoeff_raw
              exact
                Eq.subst
                  (motive := fun x : ℝ => x ≤ A * E)
                  hexpand.symm
                  (le_trans hsum hcoeff_le)
            have hJ_lower :
                c * N * E ≤ J :=
              htail_lower w hw_norm_two
            have hcoeff_nonneg : 0 ≤ C / N :=
              div_nonneg (le_of_lt hC_pos) (le_of_lt hN_pos)
            have hscaled_lower :
                (C / N) * (c * N * E) ≤ (C / N) * J :=
              mul_le_mul_of_nonneg_left hJ_lower hcoeff_nonneg
            have hscaled_left :
                (C / N) * (c * N * E) = A * E := by
              have hc_ne : c ≠ 0 :=
                ne_of_gt hc_pos
              have hN_ne : N ≠ 0 :=
                ne_of_gt hN_pos
              calc
                (C / N) * (c * N * E) =
                    ((A / c) / N) * (c * N * E) := by
                  rfl
                _ = ((A / c) / N) * ((c * N) * E) := by
                  exact Eq.refl (((A / c) / N) * ((c * N) * E))
                _ = (((A / c) / N) * (c * N)) * E := by
                  exact (mul_assoc ((A / c) / N) (c * N) E).symm
                _ = ((A / c) * c) * E := by
                  exact congrArg (fun x : ℝ => x * E)
                    (calc
                      ((A / c) / N) * (c * N) =
                          (((A / c) / N) * N) * c := by
                        calc
                          ((A / c) / N) * (c * N) =
                              ((A / c) / N) * (N * c) := by
                            exact congrArg (fun x : ℝ => ((A / c) / N) * x)
                              (mul_comm c N)
                          _ = (((A / c) / N) * N) * c := by
                            exact (mul_assoc ((A / c) / N) N c).symm
                      _ = (A / c) * c := by
                        exact congrArg (fun x : ℝ => x * c)
                          (div_mul_cancel₀ (A / c) hN_ne))
                _ = A * E := by
                  exact congrArg (fun x : ℝ => x * E)
                    (div_mul_cancel₀ A hc_ne)
            have htarget :
                A * E ≤ (C / ‖w‖) * J :=
              Eq.subst
                (motive := fun x : ℝ => x ≤ (C / ‖w‖) * J)
                hscaled_left
                hscaled_lower
            le_trans htwice (le_trans htwice_scale htarget)⟩

/-- The oriented minus moving-log spike estimate, assembled from the
nonpositive, lower, moderate, and far upper-center branches. -/
theorem Complex.binetSecondFormula_orientedMinusMovingLog_scaled_decay_owner :
    ∃ Cminus : ℝ,
      0 < Cminus ∧
      ∀ w : ℂ,
        0 < w.re →
        2 ≤ ‖w‖ →
          2 * ∫ t : ℝ in Set.Ioc (‖w‖ / 2) (2 * ‖w‖),
              (2 * Real.log ((3 * ‖w‖) / max w.re |w.im - t|)) /
                Real.exp ((2 : ℝ) * Real.pi * t) ≤
            (Cminus / ‖w‖) *
              Complex.binetSecondFormulaDecayingTailIntegral w := by
  match
    Complex.binetSecondFormula_minusMovingLog_nonpositiveCenter_scaled_decay,
    Complex.binetSecondFormula_minusMovingLog_nonnegativeLowerCenter_scaled_decay,
    Complex.binetSecondFormula_minusMovingLog_moderateUpperCenter_scaled_decay,
    Complex.binetSecondFormula_minusMovingLog_farUpperCenter_scaled_decay
  with
  | ⟨Cnonpos, hCnonpos_pos, hnonpos⟩,
    ⟨Clower, hClower_pos, hlower⟩,
    ⟨Cmoderate, hCmoderate_pos, hmoderate⟩,
    ⟨Cfar, hCfar_pos, hfar_bound⟩ =>
      let Cbase : ℝ := max (max Cnonpos Clower) (max Cmoderate Cfar)
      let C : ℝ := Cbase + 1
      have hCbase_nonneg : 0 ≤ Cbase := by
        have hCnonpos_nonneg : 0 ≤ Cnonpos :=
          le_of_lt hCnonpos_pos
        have hleft_nonneg : 0 ≤ max Cnonpos Clower :=
          le_trans hCnonpos_nonneg (le_max_left Cnonpos Clower)
        exact le_trans hleft_nonneg
          (le_max_left (max Cnonpos Clower) (max Cmoderate Cfar))
      have hC_pos : 0 < C :=
        add_pos_of_nonneg_of_pos hCbase_nonneg zero_lt_one
      have hCnonpos_le : Cnonpos ≤ C := by
        have hto_base : Cnonpos ≤ Cbase :=
          le_trans (le_max_left Cnonpos Clower)
            (le_max_left (max Cnonpos Clower) (max Cmoderate Cfar))
        exact le_trans hto_base (le_add_of_nonneg_right zero_le_one)
      have hClower_le : Clower ≤ C := by
        have hto_base : Clower ≤ Cbase :=
          le_trans (le_max_right Cnonpos Clower)
            (le_max_left (max Cnonpos Clower) (max Cmoderate Cfar))
        exact le_trans hto_base (le_add_of_nonneg_right zero_le_one)
      have hCmoderate_le : Cmoderate ≤ C := by
        have hto_base : Cmoderate ≤ Cbase :=
          le_trans (le_max_left Cmoderate Cfar)
            (le_max_right (max Cnonpos Clower) (max Cmoderate Cfar))
        exact le_trans hto_base (le_add_of_nonneg_right zero_le_one)
      have hCfar_le : Cfar ≤ C := by
        have hto_base : Cfar ≤ Cbase :=
          le_trans (le_max_right Cmoderate Cfar)
            (le_max_right (max Cnonpos Clower) (max Cmoderate Cfar))
        exact le_trans hto_base (le_add_of_nonneg_right zero_le_one)
      exact
        ⟨C, hC_pos,
          fun w hw_re_pos hw_norm_two =>
            let J : ℝ := Complex.binetSecondFormulaDecayingTailIntegral w
            let N : ℝ := ‖w‖
            have hN_pos : 0 < N :=
              lt_of_lt_of_le zero_lt_two hw_norm_two
            have hJ_nonneg : 0 ≤ J :=
              Complex.binetSecondFormula_decayingTailIntegral_nonneg_of_norm_two
                hw_norm_two
            have htransport :
                ∀ Cbranch : ℝ,
                  Cbranch ≤ C →
                    (Cbranch / N) * J ≤ (C / N) * J := by
              intro Cbranch hbranch_le
              have hdiv_le :
                  Cbranch / N ≤ C / N :=
                div_le_div_of_nonneg_right hbranch_le (le_of_lt hN_pos)
              exact mul_le_mul_of_nonneg_right hdiv_le hJ_nonneg
            match le_total w.im 0 with
            | Or.inl him_nonpos =>
                let hbranch :
                    2 * ∫ t : ℝ in Set.Ioc (‖w‖ / 2) (2 * ‖w‖),
                        (2 * Real.log ((3 * ‖w‖) / max w.re |w.im - t|)) /
                          Real.exp ((2 : ℝ) * Real.pi * t) ≤
                      (Cnonpos / ‖w‖) * J :=
                  hnonpos w hw_re_pos hw_norm_two him_nonpos
                le_trans hbranch (htransport Cnonpos hCnonpos_le)
            | Or.inr him_nonneg =>
                match le_total w.im (‖w‖ / 2) with
                | Or.inl him_le_half =>
                    let hbranch :
                        2 * ∫ t : ℝ in Set.Ioc (‖w‖ / 2) (2 * ‖w‖),
                            (2 * Real.log ((3 * ‖w‖) / max w.re |w.im - t|)) /
                              Real.exp ((2 : ℝ) * Real.pi * t) ≤
                          (Clower / ‖w‖) * J :=
                      hlower w hw_re_pos hw_norm_two him_nonneg him_le_half
                    le_trans hbranch (htransport Clower hClower_le)
                | Or.inr hhalf_le_im =>
                    match le_total w.im ((3 * ‖w‖) / 4) with
                    | Or.inl him_le_three_quarters =>
                        let hbranch :
                            2 * ∫ t : ℝ in Set.Ioc (‖w‖ / 2) (2 * ‖w‖),
                                (2 * Real.log ((3 * ‖w‖) / max w.re |w.im - t|)) /
                                  Real.exp ((2 : ℝ) * Real.pi * t) ≤
                              (Cmoderate / ‖w‖) * J :=
                          hmoderate w hw_re_pos hw_norm_two hhalf_le_im
                            him_le_three_quarters
                        le_trans hbranch (htransport Cmoderate hCmoderate_le)
                    | Or.inr hfar =>
                        let hbranch :
                            2 * ∫ t : ℝ in Set.Ioc (‖w‖ / 2) (2 * ‖w‖),
                                (2 * Real.log ((3 * ‖w‖) / max w.re |w.im - t|)) /
                                  Real.exp ((2 : ℝ) * Real.pi * t) ≤
                              (Cfar / ‖w‖) * J :=
                          hfar_bound w hw_re_pos hw_norm_two hfar
                        le_trans hbranch (htransport Cfar hCfar_le)⟩

end

end LFunctions
end Boundary
