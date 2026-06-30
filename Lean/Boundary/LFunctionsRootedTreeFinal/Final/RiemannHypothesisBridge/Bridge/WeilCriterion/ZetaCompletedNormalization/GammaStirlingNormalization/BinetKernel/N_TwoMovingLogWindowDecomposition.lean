import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalization.GammaStirlingNormalization.BinetKernel.M_BranchWallMovingSpikeAccounting

/-!
# Two-moving-log window decomposition

This file peels the scalar two-moving branch-wall window into the plus spike,
the minus spike, and the constant exponential tail.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open scoped Topology
open Filter
open MeasureTheory

/-- Real numeral product `2 * 2 = 4`, as an explicit cast computation. -/
theorem Real.two_mul_two_eq_four_for_twoMovingLog :
    (2 : ℝ) * 2 = 4 := by
  have hnat : (2 : ℕ) * 2 = 4 := by
    rfl
  calc
    (2 : ℝ) * 2 = (((2 : ℕ) * 2 : ℕ) : ℝ) := by
      exact (Nat.cast_mul 2 2).symm
    _ = 4 := by
      exact congrArg (fun n : ℕ => (n : ℝ)) hnat

/-- The two-moving logarithmic numerator is bounded by the sum of its two
moving log spikes and the constant `π` term. -/
theorem Complex.binetSecondFormula_twoMovingLogWindow_numerator_le_sum
    (w : ℂ)
    (t : ℝ) :
    max
        |Real.log ((max w.re |w.im + t|) / (3 * ‖w‖))|
        |Real.log ((3 * ‖w‖) / max w.re |w.im - t|)| +
        Real.pi ≤
      |Real.log ((max w.re |w.im + t|) / (3 * ‖w‖))| +
        |Real.log ((3 * ‖w‖) / max w.re |w.im - t|)| +
        Real.pi := by
  let A : ℝ :=
    |Real.log ((max w.re |w.im + t|) / (3 * ‖w‖))|
  let B : ℝ :=
    |Real.log ((3 * ‖w‖) / max w.re |w.im - t|)|
  have hmax_le_sum : max A B ≤ A + B :=
    max_le
      (le_add_of_nonneg_right (abs_nonneg (Real.log ((3 * ‖w‖) / max w.re |w.im - t|))))
      (le_add_of_nonneg_left (abs_nonneg (Real.log ((max w.re |w.im + t|) / (3 * ‖w‖)))))
  exact add_le_add_right hmax_le_sum Real.pi

/-- Pointwise decomposition of the weighted two-moving-log window into its
two moving spike terms and the constant exponential tail. -/
theorem Complex.binetSecondFormula_twoMovingLogWindow_weighted_le_sum
    {w : ℂ}
    {t : ℝ} :
    (2 *
      (max
        |Real.log ((max w.re |w.im + t|) / (3 * ‖w‖))|
        |Real.log ((3 * ‖w‖) / max w.re |w.im - t|)| +
        Real.pi)) /
      Real.exp ((2 : ℝ) * Real.pi * t) ≤
    (2 * |Real.log ((max w.re |w.im + t|) / (3 * ‖w‖))|) /
        Real.exp ((2 : ℝ) * Real.pi * t) +
      (2 * |Real.log ((3 * ‖w‖) / max w.re |w.im - t|)|) /
        Real.exp ((2 : ℝ) * Real.pi * t) +
      (2 * Real.pi) / Real.exp ((2 : ℝ) * Real.pi * t) := by
  let A : ℝ :=
    |Real.log ((max w.re |w.im + t|) / (3 * ‖w‖))|
  let B : ℝ :=
    |Real.log ((3 * ‖w‖) / max w.re |w.im - t|)|
  let E : ℝ := Real.exp ((2 : ℝ) * Real.pi * t)
  have hE_pos : 0 < E :=
    Real.exp_pos ((2 : ℝ) * Real.pi * t)
  have hnum :
      2 * (max A B + Real.pi) ≤
        2 * A + 2 * B + 2 * Real.pi := by
    have hbase : max A B + Real.pi ≤ A + B + Real.pi :=
      Complex.binetSecondFormula_twoMovingLogWindow_numerator_le_sum w t
    have hmul :
        2 * (max A B + Real.pi) ≤ 2 * (A + B + Real.pi) :=
      mul_le_mul_of_nonneg_left hbase zero_le_two
    have hdist :
        2 * (A + B + Real.pi) =
          2 * A + 2 * B + 2 * Real.pi := by
      calc
        2 * (A + B + Real.pi) =
            2 * (A + B) + 2 * Real.pi := by
          exact left_distrib (2 : ℝ) (A + B) Real.pi
        _ = (2 * A + 2 * B) + 2 * Real.pi := by
          exact congrArg (fun x : ℝ => x + 2 * Real.pi)
            (left_distrib (2 : ℝ) A B)
        _ = 2 * A + 2 * B + 2 * Real.pi := by
          exact Eq.refl (2 * A + 2 * B + 2 * Real.pi)
    exact le_trans hmul (le_of_eq hdist)
  have hdiv :
      (2 * (max A B + Real.pi)) / E ≤
        (2 * A + 2 * B + 2 * Real.pi) / E :=
    div_le_div_of_nonneg_right hnum (le_of_lt hE_pos)
  have hsum_div :
      (2 * A + 2 * B + 2 * Real.pi) / E =
        (2 * A) / E + (2 * B) / E + (2 * Real.pi) / E := by
    calc
      (2 * A + 2 * B + 2 * Real.pi) / E =
          ((2 * A + 2 * B) + 2 * Real.pi) / E := by
        exact Eq.refl ((2 * A + 2 * B + 2 * Real.pi) / E)
      _ = (2 * A + 2 * B) / E + (2 * Real.pi) / E := by
        exact add_div (2 * A + 2 * B) (2 * Real.pi) E
      _ = ((2 * A) / E + (2 * B) / E) + (2 * Real.pi) / E := by
        exact congrArg (fun x : ℝ => x + (2 * Real.pi) / E)
          (add_div (2 * A) (2 * B) E)
      _ = (2 * A) / E + (2 * B) / E + (2 * Real.pi) / E := by
        exact Eq.refl ((2 * A) / E + (2 * B) / E + (2 * Real.pi) / E)
  exact le_trans hdiv (le_of_eq hsum_div)

/-- Integral decomposition of the weighted two-moving-log window on the
bounded Binet tail window. -/
theorem Complex.binetSecondFormula_twoMovingLogWindow_integral_le_sum
    {w : ℂ}
    (hw_re_pos : 0 < w.re) :
    ∫ t : ℝ in Set.Ioc (‖w‖ / 2) (2 * ‖w‖),
        (2 *
          (max
            |Real.log ((max w.re |w.im + t|) / (3 * ‖w‖))|
            |Real.log ((3 * ‖w‖) / max w.re |w.im - t|)| +
            Real.pi)) /
          Real.exp ((2 : ℝ) * Real.pi * t) ≤
      (∫ t : ℝ in Set.Ioc (‖w‖ / 2) (2 * ‖w‖),
          (2 * |Real.log ((max w.re |w.im + t|) / (3 * ‖w‖))|) /
            Real.exp ((2 : ℝ) * Real.pi * t)) +
      (∫ t : ℝ in Set.Ioc (‖w‖ / 2) (2 * ‖w‖),
          (2 * |Real.log ((3 * ‖w‖) / max w.re |w.im - t|)|) /
            Real.exp ((2 : ℝ) * Real.pi * t)) +
      (∫ t : ℝ in Set.Ioc (‖w‖ / 2) (2 * ‖w‖),
          (2 * Real.pi) / Real.exp ((2 : ℝ) * Real.pi * t)) := by
  let S : Set ℝ := Set.Ioc (‖w‖ / 2) (2 * ‖w‖)
  let G : ℝ → ℝ := fun t : ℝ =>
    (2 *
      (max
        |Real.log ((max w.re |w.im + t|) / (3 * ‖w‖))|
        |Real.log ((3 * ‖w‖) / max w.re |w.im - t|)| +
        Real.pi)) /
      Real.exp ((2 : ℝ) * Real.pi * t)
  let A : ℝ → ℝ := fun t : ℝ =>
    (2 * |Real.log ((max w.re |w.im + t|) / (3 * ‖w‖))|) /
      Real.exp ((2 : ℝ) * Real.pi * t)
  let B : ℝ → ℝ := fun t : ℝ =>
    (2 * |Real.log ((3 * ‖w‖) / max w.re |w.im - t|)|) /
      Real.exp ((2 : ℝ) * Real.pi * t)
  let P : ℝ → ℝ := fun t : ℝ =>
    (2 * Real.pi) / Real.exp ((2 : ℝ) * Real.pi * t)
  have hG_integrable :
      IntegrableOn G S :=
    by
      let Scc : Set ℝ := Set.Icc (‖w‖ / 2) (2 * ‖w‖)
      let Aplus : ℝ → ℝ := fun t : ℝ => max w.re |w.im + t|
      let Aminus : ℝ → ℝ := fun t : ℝ => max w.re |w.im - t|
      let Lplus : ℝ → ℝ := fun t : ℝ =>
        Aplus t / (3 * ‖w‖)
      let Lminus : ℝ → ℝ := fun t : ℝ =>
        (3 * ‖w‖) / Aminus t
      let H : ℝ → ℝ := fun t : ℝ =>
        (2 * (max |Real.log (Lplus t)| |Real.log (Lminus t)| + Real.pi)) /
          Real.exp ((2 : ℝ) * Real.pi * t)
      have hw_norm_pos : 0 < ‖w‖ :=
        Complex.norm_pos_of_re_pos hw_re_pos
      have hthree_norm_pos : 0 < 3 * ‖w‖ :=
        mul_pos Real.zero_lt_three hw_norm_pos
      have hAplus_pos : ∀ t : ℝ, 0 < Aplus t := by
        intro t
        exact lt_of_lt_of_le hw_re_pos (le_max_left w.re |w.im + t|)
      have hAminus_pos : ∀ t : ℝ, 0 < Aminus t := by
        intro t
        exact lt_of_lt_of_le hw_re_pos (le_max_left w.re |w.im - t|)
      have hLplus_pos : ∀ t : ℝ, 0 < Lplus t := by
        intro t
        exact div_pos (hAplus_pos t) hthree_norm_pos
      have hLminus_pos : ∀ t : ℝ, 0 < Lminus t := by
        intro t
        exact div_pos hthree_norm_pos (hAminus_pos t)
      have hplus_dist_cont : Continuous fun t : ℝ => |w.im + t| :=
        (continuous_const.add continuous_id).abs
      have hminus_dist_cont : Continuous fun t : ℝ => |w.im - t| :=
        (continuous_const.sub continuous_id).abs
      have hAplus_cont : Continuous Aplus :=
        continuous_const.sup hplus_dist_cont
      have hAminus_cont : Continuous Aminus :=
        continuous_const.sup hminus_dist_cont
      have hLplus_cont : Continuous Lplus :=
        hAplus_cont.div_const (3 * ‖w‖)
      have hLminus_cont : Continuous Lminus :=
        continuous_const.div hAminus_cont (fun t => (hAminus_pos t).ne')
      have hplus_log_contOn :
          ContinuousOn (fun t : ℝ => Real.log (Lplus t)) Scc :=
        (hLplus_cont.continuousOn).log (fun t _ht => (hLplus_pos t).ne')
      have hminus_log_contOn :
          ContinuousOn (fun t : ℝ => Real.log (Lminus t)) Scc :=
        (hLminus_cont.continuousOn).log (fun t _ht => (hLminus_pos t).ne')
      have hmax_contOn :
          ContinuousOn
            (fun t : ℝ =>
              max |Real.log (Lplus t)| |Real.log (Lminus t)|)
            Scc :=
        hplus_log_contOn.abs.sup hminus_log_contOn.abs
      have hnum_contOn :
          ContinuousOn
            (fun t : ℝ =>
              2 * (max |Real.log (Lplus t)| |Real.log (Lminus t)| +
                Real.pi))
            Scc :=
        continuousOn_const.mul (hmax_contOn.add continuousOn_const)
      have hlinear_cont : Continuous fun t : ℝ => (2 : ℝ) * Real.pi * t :=
        (continuous_const.mul continuous_const).mul continuous_id
      have hden_cont : Continuous fun t : ℝ =>
          Real.exp ((2 : ℝ) * Real.pi * t) :=
        Real.continuous_exp.comp hlinear_cont
      have hden_ne : ∀ t : ℝ, t ∈ Scc →
          Real.exp ((2 : ℝ) * Real.pi * t) ≠ 0 := by
        intro t _ht
        exact (Real.exp_pos ((2 : ℝ) * Real.pi * t)).ne'
      have hH_contOn : ContinuousOn H Scc :=
        hnum_contOn.div hden_cont.continuousOn hden_ne
      have hH_integrable_Icc : IntegrableOn H Scc :=
        hH_contOn.integrableOn_Icc
      exact hH_integrable_Icc.mono_set Set.Ioc_subset_Icc_self
  have hsum_integrable :
      IntegrableOn (fun t : ℝ => A t + B t + P t) S := by
    let Scc : Set ℝ := Set.Icc (‖w‖ / 2) (2 * ‖w‖)
    let Aplus : ℝ → ℝ := fun t : ℝ => max w.re |w.im + t|
    let Aminus : ℝ → ℝ := fun t : ℝ => max w.re |w.im - t|
    let Lplus : ℝ → ℝ := fun t : ℝ =>
      Aplus t / (3 * ‖w‖)
    let Lminus : ℝ → ℝ := fun t : ℝ =>
      (3 * ‖w‖) / Aminus t
    let H : ℝ → ℝ := fun t : ℝ => A t + B t + P t
    have hw_norm_pos : 0 < ‖w‖ :=
      Complex.norm_pos_of_re_pos hw_re_pos
    have hthree_norm_pos : 0 < 3 * ‖w‖ :=
      mul_pos Real.zero_lt_three hw_norm_pos
    have hAplus_pos : ∀ t : ℝ, 0 < Aplus t := by
      intro t
      exact lt_of_lt_of_le hw_re_pos (le_max_left w.re |w.im + t|)
    have hAminus_pos : ∀ t : ℝ, 0 < Aminus t := by
      intro t
      exact lt_of_lt_of_le hw_re_pos (le_max_left w.re |w.im - t|)
    have hLplus_pos : ∀ t : ℝ, 0 < Lplus t := by
      intro t
      exact div_pos (hAplus_pos t) hthree_norm_pos
    have hLminus_pos : ∀ t : ℝ, 0 < Lminus t := by
      intro t
      exact div_pos hthree_norm_pos (hAminus_pos t)
    have hplus_dist_cont : Continuous fun t : ℝ => |w.im + t| :=
      (continuous_const.add continuous_id).abs
    have hminus_dist_cont : Continuous fun t : ℝ => |w.im - t| :=
      (continuous_const.sub continuous_id).abs
    have hAplus_cont : Continuous Aplus :=
      continuous_const.sup hplus_dist_cont
    have hAminus_cont : Continuous Aminus :=
      continuous_const.sup hminus_dist_cont
    have hLplus_cont : Continuous Lplus :=
      hAplus_cont.div_const (3 * ‖w‖)
    have hLminus_cont : Continuous Lminus :=
      continuous_const.div hAminus_cont (fun t => (hAminus_pos t).ne')
    have hplus_log_contOn :
        ContinuousOn (fun t : ℝ => Real.log (Lplus t)) Scc :=
      (hLplus_cont.continuousOn).log (fun t _ht => (hLplus_pos t).ne')
    have hminus_log_contOn :
        ContinuousOn (fun t : ℝ => Real.log (Lminus t)) Scc :=
      (hLminus_cont.continuousOn).log (fun t _ht => (hLminus_pos t).ne')
    have hlinear_cont : Continuous fun t : ℝ => (2 : ℝ) * Real.pi * t :=
      (continuous_const.mul continuous_const).mul continuous_id
    have hden_cont : Continuous fun t : ℝ =>
        Real.exp ((2 : ℝ) * Real.pi * t) :=
      Real.continuous_exp.comp hlinear_cont
    have hden_ne : ∀ t : ℝ, t ∈ Scc →
        Real.exp ((2 : ℝ) * Real.pi * t) ≠ 0 := by
      intro t _ht
      exact (Real.exp_pos ((2 : ℝ) * Real.pi * t)).ne'
    have hA_contOn :
        ContinuousOn A Scc :=
      (continuousOn_const.mul hplus_log_contOn.abs).div
        hden_cont.continuousOn hden_ne
    have hB_contOn :
        ContinuousOn B Scc :=
      (continuousOn_const.mul hminus_log_contOn.abs).div
        hden_cont.continuousOn hden_ne
    have hP_contOn :
        ContinuousOn P Scc :=
      continuousOn_const.div hden_cont.continuousOn hden_ne
    have hH_contOn : ContinuousOn H Scc :=
      (hA_contOn.add hB_contOn).add hP_contOn
    have hH_integrable_Icc : IntegrableOn H Scc :=
      hH_contOn.integrableOn_Icc
    exact hH_integrable_Icc.mono_set Set.Ioc_subset_Icc_self
  have hA_integrable : IntegrableOn A S := by
    let Scc : Set ℝ := Set.Icc (‖w‖ / 2) (2 * ‖w‖)
    let Aplus : ℝ → ℝ := fun t : ℝ => max w.re |w.im + t|
    let Lplus : ℝ → ℝ := fun t : ℝ =>
      Aplus t / (3 * ‖w‖)
    have hw_norm_pos : 0 < ‖w‖ :=
      Complex.norm_pos_of_re_pos hw_re_pos
    have hthree_norm_pos : 0 < 3 * ‖w‖ :=
      mul_pos Real.zero_lt_three hw_norm_pos
    have hAplus_pos : ∀ t : ℝ, 0 < Aplus t := by
      intro t
      exact lt_of_lt_of_le hw_re_pos (le_max_left w.re |w.im + t|)
    have hLplus_pos : ∀ t : ℝ, 0 < Lplus t := by
      intro t
      exact div_pos (hAplus_pos t) hthree_norm_pos
    have hplus_dist_cont : Continuous fun t : ℝ => |w.im + t| :=
      (continuous_const.add continuous_id).abs
    have hAplus_cont : Continuous Aplus :=
      continuous_const.sup hplus_dist_cont
    have hLplus_cont : Continuous Lplus :=
      hAplus_cont.div_const (3 * ‖w‖)
    have hplus_log_contOn :
        ContinuousOn (fun t : ℝ => Real.log (Lplus t)) Scc :=
      (hLplus_cont.continuousOn).log (fun t _ht => (hLplus_pos t).ne')
    have hlinear_cont : Continuous fun t : ℝ => (2 : ℝ) * Real.pi * t :=
      (continuous_const.mul continuous_const).mul continuous_id
    have hden_cont : Continuous fun t : ℝ =>
        Real.exp ((2 : ℝ) * Real.pi * t) :=
      Real.continuous_exp.comp hlinear_cont
    have hden_ne : ∀ t : ℝ, t ∈ Scc →
        Real.exp ((2 : ℝ) * Real.pi * t) ≠ 0 := by
      intro t _ht
      exact (Real.exp_pos ((2 : ℝ) * Real.pi * t)).ne'
    have hA_contOn : ContinuousOn A Scc :=
      (continuousOn_const.mul hplus_log_contOn.abs).div
        hden_cont.continuousOn hden_ne
    have hA_integrable_Icc : IntegrableOn A Scc :=
      hA_contOn.integrableOn_Icc
    exact hA_integrable_Icc.mono_set Set.Ioc_subset_Icc_self
  have hB_integrable : IntegrableOn B S := by
    let Scc : Set ℝ := Set.Icc (‖w‖ / 2) (2 * ‖w‖)
    let Aminus : ℝ → ℝ := fun t : ℝ => max w.re |w.im - t|
    let Lminus : ℝ → ℝ := fun t : ℝ =>
      (3 * ‖w‖) / Aminus t
    have hw_norm_pos : 0 < ‖w‖ :=
      Complex.norm_pos_of_re_pos hw_re_pos
    have hthree_norm_pos : 0 < 3 * ‖w‖ :=
      mul_pos Real.zero_lt_three hw_norm_pos
    have hAminus_pos : ∀ t : ℝ, 0 < Aminus t := by
      intro t
      exact lt_of_lt_of_le hw_re_pos (le_max_left w.re |w.im - t|)
    have hLminus_pos : ∀ t : ℝ, 0 < Lminus t := by
      intro t
      exact div_pos hthree_norm_pos (hAminus_pos t)
    have hminus_dist_cont : Continuous fun t : ℝ => |w.im - t| :=
      (continuous_const.sub continuous_id).abs
    have hAminus_cont : Continuous Aminus :=
      continuous_const.sup hminus_dist_cont
    have hLminus_cont : Continuous Lminus :=
      continuous_const.div hAminus_cont (fun t => (hAminus_pos t).ne')
    have hminus_log_contOn :
        ContinuousOn (fun t : ℝ => Real.log (Lminus t)) Scc :=
      (hLminus_cont.continuousOn).log (fun t _ht => (hLminus_pos t).ne')
    have hlinear_cont : Continuous fun t : ℝ => (2 : ℝ) * Real.pi * t :=
      (continuous_const.mul continuous_const).mul continuous_id
    have hden_cont : Continuous fun t : ℝ =>
        Real.exp ((2 : ℝ) * Real.pi * t) :=
      Real.continuous_exp.comp hlinear_cont
    have hden_ne : ∀ t : ℝ, t ∈ Scc →
        Real.exp ((2 : ℝ) * Real.pi * t) ≠ 0 := by
      intro t _ht
      exact (Real.exp_pos ((2 : ℝ) * Real.pi * t)).ne'
    have hB_contOn : ContinuousOn B Scc :=
      (continuousOn_const.mul hminus_log_contOn.abs).div
        hden_cont.continuousOn hden_ne
    have hB_integrable_Icc : IntegrableOn B Scc :=
      hB_contOn.integrableOn_Icc
    exact hB_integrable_Icc.mono_set Set.Ioc_subset_Icc_self
  have hP_integrable : IntegrableOn P S := by
    let Scc : Set ℝ := Set.Icc (‖w‖ / 2) (2 * ‖w‖)
    have hlinear_cont : Continuous fun t : ℝ => (2 : ℝ) * Real.pi * t :=
      (continuous_const.mul continuous_const).mul continuous_id
    have hden_cont : Continuous fun t : ℝ =>
        Real.exp ((2 : ℝ) * Real.pi * t) :=
      Real.continuous_exp.comp hlinear_cont
    have hden_ne : ∀ t : ℝ, t ∈ Scc →
        Real.exp ((2 : ℝ) * Real.pi * t) ≠ 0 := by
      intro t _ht
      exact (Real.exp_pos ((2 : ℝ) * Real.pi * t)).ne'
    have hP_contOn : ContinuousOn P Scc :=
      continuousOn_const.div hden_cont.continuousOn hden_ne
    have hP_integrable_Icc : IntegrableOn P Scc :=
      hP_contOn.integrableOn_Icc
    exact hP_integrable_Icc.mono_set Set.Ioc_subset_Icc_self
  have hpoint :
      ∀ᵐ t ∂volume.restrict S, G t ≤ A t + B t + P t :=
    (ae_restrict_mem measurableSet_Ioc).mono
      (fun t _ht =>
        Complex.binetSecondFormula_twoMovingLogWindow_weighted_le_sum
          (w := w) (t := t))
  have hintegral :
      ∫ t : ℝ in S, G t ≤
        ∫ t : ℝ in S, A t + B t + P t :=
    setIntegral_mono_ae_restrict hG_integrable hsum_integrable hpoint
  have hsum :
      ∫ t : ℝ in S, A t + B t + P t =
        (∫ t : ℝ in S, A t) +
          (∫ t : ℝ in S, B t) +
          (∫ t : ℝ in S, P t) := by
    have hB_add_P_integrable : IntegrableOn (fun t : ℝ => B t + P t) S :=
      hB_integrable.add hP_integrable
    have hA_add_rest :
        ∫ t : ℝ in S, A t + (B t + P t) =
          (∫ t : ℝ in S, A t) +
            (∫ t : ℝ in S, B t + P t) :=
      integral_add hA_integrable hB_add_P_integrable
    have hB_add_P :
        ∫ t : ℝ in S, B t + P t =
          (∫ t : ℝ in S, B t) + (∫ t : ℝ in S, P t) :=
      integral_add hB_integrable hP_integrable
    calc
      ∫ t : ℝ in S, A t + B t + P t =
          ∫ t : ℝ in S, A t + (B t + P t) := by
        exact
          setIntegral_congr_fun measurableSet_Ioc
            (fun t _ht =>
              add_assoc (A t) (B t) (P t))
      _ = (∫ t : ℝ in S, A t) +
            (∫ t : ℝ in S, B t + P t) := by
        exact hA_add_rest
      _ = (∫ t : ℝ in S, A t) +
            ((∫ t : ℝ in S, B t) + (∫ t : ℝ in S, P t)) := by
        exact congrArg (fun x : ℝ => (∫ t : ℝ in S, A t) + x) hB_add_P
      _ = (∫ t : ℝ in S, A t) +
            (∫ t : ℝ in S, B t) +
            (∫ t : ℝ in S, P t) := by
        exact
          (add_assoc
            (∫ t : ℝ in S, A t)
            (∫ t : ℝ in S, B t)
            (∫ t : ℝ in S, P t)).symm
  exact le_trans hintegral (le_of_eq hsum)

/-- The plus moving spike integral can be written with the oriented negative
logarithm on the bounded tail window. -/
theorem Complex.binetSecondFormula_plusMovingLog_abs_integral_eq_neg_log
    {w : ℂ}
    (hw_re_pos : 0 < w.re) :
    ∫ t : ℝ in Set.Ioc (‖w‖ / 2) (2 * ‖w‖),
        (2 * |Real.log ((max w.re |w.im + t|) / (3 * ‖w‖))|) /
          Real.exp ((2 : ℝ) * Real.pi * t) =
      ∫ t : ℝ in Set.Ioc (‖w‖ / 2) (2 * ‖w‖),
        (2 * (-Real.log ((max w.re |w.im + t|) / (3 * ‖w‖)))) /
          Real.exp ((2 : ℝ) * Real.pi * t) := by
  exact
    setIntegral_congr_fun measurableSet_Ioc
      (fun t ht =>
        have ht_Icc :
            t ∈ Set.Icc (‖w‖ / 2) (2 * ‖w‖) :=
          Set.Ioc_subset_Icc_self ht
        have hlog_abs :
            |Real.log ((max w.re |w.im + t|) / (3 * ‖w‖))| =
              -Real.log ((max w.re |w.im + t|) / (3 * ‖w‖)) :=
          Complex.binetSecondFormula_plusMovingLog_abs_eq_neg
            hw_re_pos ht_Icc
        congrArg
          (fun x : ℝ => (2 * x) / Real.exp ((2 : ℝ) * Real.pi * t))
          hlog_abs)

/-- The minus moving spike integral can be written without an absolute value
on the bounded tail window. -/
theorem Complex.binetSecondFormula_minusMovingLog_abs_integral_eq_log
    {w : ℂ}
    (hw_re_pos : 0 < w.re) :
    ∫ t : ℝ in Set.Ioc (‖w‖ / 2) (2 * ‖w‖),
        (2 * |Real.log ((3 * ‖w‖) / max w.re |w.im - t|)|) /
          Real.exp ((2 : ℝ) * Real.pi * t) =
      ∫ t : ℝ in Set.Ioc (‖w‖ / 2) (2 * ‖w‖),
        (2 * Real.log ((3 * ‖w‖) / max w.re |w.im - t|)) /
          Real.exp ((2 : ℝ) * Real.pi * t) := by
  exact
    setIntegral_congr_fun measurableSet_Ioc
      (fun t ht =>
        have ht_Icc :
            t ∈ Set.Icc (‖w‖ / 2) (2 * ‖w‖) :=
          Set.Ioc_subset_Icc_self ht
        have hlog_abs :
            |Real.log ((3 * ‖w‖) / max w.re |w.im - t|)| =
              Real.log ((3 * ‖w‖) / max w.re |w.im - t|) :=
          Complex.binetSecondFormula_minusMovingLog_abs_eq_self
            hw_re_pos ht_Icc
        congrArg
          (fun x : ℝ => (2 * x) / Real.exp ((2 : ℝ) * Real.pi * t))
          hlog_abs)

/-- Plus-spike scaled decay follows from the oriented negative-log bound. -/
theorem Complex.binetSecondFormula_plusMovingLog_scaled_decay_of_oriented_neg_log
    (hplus :
      ∃ Cplus : ℝ,
        0 < Cplus ∧
        ∀ w : ℂ,
          0 < w.re →
          2 ≤ ‖w‖ →
            2 * ∫ t : ℝ in Set.Ioc (‖w‖ / 2) (2 * ‖w‖),
                (2 * (-Real.log ((max w.re |w.im + t|) / (3 * ‖w‖)))) /
                  Real.exp ((2 : ℝ) * Real.pi * t) ≤
              (Cplus / ‖w‖) *
                Complex.binetSecondFormulaDecayingTailIntegral w) :
    ∃ Cplus : ℝ,
      0 < Cplus ∧
      ∀ w : ℂ,
        0 < w.re →
        2 ≤ ‖w‖ →
          2 * ∫ t : ℝ in Set.Ioc (‖w‖ / 2) (2 * ‖w‖),
              (2 * |Real.log ((max w.re |w.im + t|) / (3 * ‖w‖))|) /
                Real.exp ((2 : ℝ) * Real.pi * t) ≤
            (Cplus / ‖w‖) *
              Complex.binetSecondFormulaDecayingTailIntegral w := by
  match hplus with
  | ⟨Cplus, hCplus_pos, hplus_bound⟩ =>
      exact
        ⟨Cplus, hCplus_pos,
          fun w hw_re_pos hw_large =>
            let Aabs : ℝ → ℝ := fun t : ℝ =>
              (2 * |Real.log ((max w.re |w.im + t|) / (3 * ‖w‖))|) /
                Real.exp ((2 : ℝ) * Real.pi * t)
            let Aneg : ℝ → ℝ := fun t : ℝ =>
              (2 * (-Real.log ((max w.re |w.im + t|) / (3 * ‖w‖)))) /
                Real.exp ((2 : ℝ) * Real.pi * t)
            let S : Set ℝ := Set.Ioc (‖w‖ / 2) (2 * ‖w‖)
            let J : ℝ :=
              Complex.binetSecondFormulaDecayingTailIntegral w
            have hintegral_eq :
                ∫ t : ℝ in S, Aabs t =
                  ∫ t : ℝ in S, Aneg t :=
              Complex.binetSecondFormula_plusMovingLog_abs_integral_eq_neg_log
                hw_re_pos
            have htwice_eq :
                2 * ∫ t : ℝ in S, Aabs t =
                  2 * ∫ t : ℝ in S, Aneg t :=
              congrArg (fun x : ℝ => 2 * x) hintegral_eq
            have htarget :
                2 * ∫ t : ℝ in S, Aneg t ≤
                  (Cplus / ‖w‖) * J :=
              hplus_bound w hw_re_pos hw_large
            Eq.subst
              (motive := fun x : ℝ =>
                x ≤ (Cplus / ‖w‖) * J)
              htwice_eq.symm
              htarget⟩

/-- Minus-spike scaled decay follows from the oriented positive-log bound. -/
theorem Complex.binetSecondFormula_minusMovingLog_scaled_decay_of_oriented_log
    (hminus :
      ∃ Cminus : ℝ,
        0 < Cminus ∧
        ∀ w : ℂ,
          0 < w.re →
          2 ≤ ‖w‖ →
            2 * ∫ t : ℝ in Set.Ioc (‖w‖ / 2) (2 * ‖w‖),
                (2 * Real.log ((3 * ‖w‖) / max w.re |w.im - t|)) /
                  Real.exp ((2 : ℝ) * Real.pi * t) ≤
              (Cminus / ‖w‖) *
                Complex.binetSecondFormulaDecayingTailIntegral w) :
    ∃ Cminus : ℝ,
      0 < Cminus ∧
      ∀ w : ℂ,
        0 < w.re →
        2 ≤ ‖w‖ →
          2 * ∫ t : ℝ in Set.Ioc (‖w‖ / 2) (2 * ‖w‖),
              (2 * |Real.log ((3 * ‖w‖) / max w.re |w.im - t|)|) /
                Real.exp ((2 : ℝ) * Real.pi * t) ≤
            (Cminus / ‖w‖) *
              Complex.binetSecondFormulaDecayingTailIntegral w := by
  match hminus with
  | ⟨Cminus, hCminus_pos, hminus_bound⟩ =>
      exact
        ⟨Cminus, hCminus_pos,
          fun w hw_re_pos hw_large =>
            let Babs : ℝ → ℝ := fun t : ℝ =>
              (2 * |Real.log ((3 * ‖w‖) / max w.re |w.im - t|)|) /
                Real.exp ((2 : ℝ) * Real.pi * t)
            let Blog : ℝ → ℝ := fun t : ℝ =>
              (2 * Real.log ((3 * ‖w‖) / max w.re |w.im - t|)) /
                Real.exp ((2 : ℝ) * Real.pi * t)
            let S : Set ℝ := Set.Ioc (‖w‖ / 2) (2 * ‖w‖)
            let J : ℝ :=
              Complex.binetSecondFormulaDecayingTailIntegral w
            have hintegral_eq :
                ∫ t : ℝ in S, Babs t =
                  ∫ t : ℝ in S, Blog t :=
              Complex.binetSecondFormula_minusMovingLog_abs_integral_eq_log
                hw_re_pos
            have htwice_eq :
                2 * ∫ t : ℝ in S, Babs t =
                  2 * ∫ t : ℝ in S, Blog t :=
              congrArg (fun x : ℝ => 2 * x) hintegral_eq
            have htarget :
                2 * ∫ t : ℝ in S, Blog t ≤
                  (Cminus / ‖w‖) * J :=
              hminus_bound w hw_re_pos hw_large
            Eq.subst
              (motive := fun x : ℝ =>
                x ≤ (Cminus / ‖w‖) * J)
              htwice_eq.symm
              htarget⟩

/-- The constant exponential part of the decomposed two-moving window has the
expected left-endpoint exponential scale. -/
theorem Complex.binetSecondFormula_twoMovingLogWindow_constant_integral_le_exp
    (w : ℂ) :
    ∫ t : ℝ in Set.Ioc (‖w‖ / 2) (2 * ‖w‖),
        (2 * Real.pi) / Real.exp ((2 : ℝ) * Real.pi * t) ≤
      (2 * Real.pi) * Real.exp (-Real.pi * ‖w‖) := by
  let N : ℝ := ‖w‖
  let K : ℝ := 2 * Real.pi
  let F : ℝ → ℝ := fun t : ℝ =>
    Real.exp (-((2 : ℝ) * Real.pi) * t)
  have hK_nonneg : 0 ≤ K :=
    mul_nonneg zero_le_two Real.pi_nonneg
  have htail_integrable :
      IntegrableOn F (Set.Ioi (N / 2)) := by
    have hcoeff_pos : 0 < (2 : ℝ) * Real.pi :=
      mul_pos two_pos Real.pi_pos
    exact exp_neg_integrableOn_Ioi (N / 2) hcoeff_pos
  have htail_nonneg :
      0 ≤ᵐ[volume.restrict (Set.Ioi (N / 2))] F :=
    Filter.Eventually.of_forall
      (fun t => le_of_lt (Real.exp_pos (-((2 : ℝ) * Real.pi) * t)))
  have hsubset :
      Set.Ioc (N / 2) (2 * N) ≤ᵐ[volume] Set.Ioi (N / 2) :=
    Filter.Eventually.of_forall
      (fun t ht => ht.1)
  have hmono :
      ∫ t : ℝ in Set.Ioc (N / 2) (2 * N), F t ≤
        ∫ t : ℝ in Set.Ioi (N / 2), F t :=
    setIntegral_mono_set htail_integrable htail_nonneg hsubset
  have htail_bound :
      ∫ t : ℝ in Set.Ioi (N / 2), F t ≤
        Real.exp (-((2 : ℝ) * Real.pi) * (N / 2)) :=
    Real.exp_neg_two_pi_tail_integral_le_exp (N / 2)
  have hexponent :
      -((2 : ℝ) * Real.pi) * (N / 2) = -Real.pi * ‖w‖ := by
    calc
      -((2 : ℝ) * Real.pi) * (N / 2) =
          -(((2 : ℝ) * Real.pi) * (N / 2)) := by
        exact neg_mul ((2 : ℝ) * Real.pi) (N / 2)
      _ = -(Real.pi * ‖w‖) := by
        have hinside :
            ((2 : ℝ) * Real.pi) * (N / 2) =
              Real.pi * ‖w‖ := by
          calc
            ((2 : ℝ) * Real.pi) * (N / 2) =
                ((2 : ℝ) * Real.pi) * (‖w‖ / 2) := by
              rfl
            _ = (((2 : ℝ) * Real.pi) * ‖w‖) / 2 := by
              exact (mul_div_assoc ((2 : ℝ) * Real.pi) ‖w‖ 2).symm
            _ = ((Real.pi * ‖w‖) * 2) / 2 := by
              exact
                congrArg (fun x : ℝ => x / 2)
                  (calc
                    ((2 : ℝ) * Real.pi) * ‖w‖ =
                        2 * (Real.pi * ‖w‖) := by
                      exact mul_assoc 2 Real.pi ‖w‖
                    _ = (Real.pi * ‖w‖) * 2 := by
                      exact mul_comm 2 (Real.pi * ‖w‖))
            _ = Real.pi * ‖w‖ := by
              exact mul_div_cancel_right₀ (Real.pi * ‖w‖) two_ne_zero
        exact congrArg Neg.neg hinside
      _ = -Real.pi * ‖w‖ := by
        exact (neg_mul Real.pi ‖w‖).symm
  have htail_scale :
      ∫ t : ℝ in Set.Ioi (N / 2), F t ≤
        Real.exp (-Real.pi * ‖w‖) :=
    Eq.subst
      (motive := fun x : ℝ =>
        ∫ t : ℝ in Set.Ioi (N / 2), F t ≤ Real.exp x)
      hexponent
      htail_bound
  have hscaled :
      K * (∫ t : ℝ in Set.Ioc (N / 2) (2 * N), F t) ≤
        K * Real.exp (-Real.pi * ‖w‖) :=
    le_trans
      (mul_le_mul_of_nonneg_left hmono hK_nonneg)
      (mul_le_mul_of_nonneg_left htail_scale hK_nonneg)
  have hintegrand_eq :
      ∫ t : ℝ in Set.Ioc (‖w‖ / 2) (2 * ‖w‖),
          (2 * Real.pi) / Real.exp ((2 : ℝ) * Real.pi * t) =
        K * ∫ t : ℝ in Set.Ioc (N / 2) (2 * N), F t := by
    calc
      ∫ t : ℝ in Set.Ioc (‖w‖ / 2) (2 * ‖w‖),
          (2 * Real.pi) / Real.exp ((2 : ℝ) * Real.pi * t) =
          ∫ t : ℝ in Set.Ioc (N / 2) (2 * N),
            K * F t := by
        exact
          setIntegral_congr_fun measurableSet_Ioc
            (fun t _ht =>
              calc
                (2 * Real.pi) / Real.exp ((2 : ℝ) * Real.pi * t) =
                    K * (Real.exp ((2 : ℝ) * Real.pi * t))⁻¹ := by
                  rfl
                _ = K * Real.exp (-(((2 : ℝ) * Real.pi) * t)) := by
                  exact congrArg (fun x : ℝ => K * x)
                    (Real.exp_neg (((2 : ℝ) * Real.pi) * t)).symm
                _ = K * F t := by
                  exact congrArg (fun x : ℝ => K * Real.exp x)
                    (neg_mul ((2 : ℝ) * Real.pi) t).symm)
      _ = K * ∫ t : ℝ in Set.Ioc (N / 2) (2 * N), F t := by
        exact integral_mul_left K F
  exact
    Eq.subst
      (motive := fun x : ℝ =>
        x ≤ (2 * Real.pi) * Real.exp (-Real.pi * ‖w‖))
      hintegrand_eq.symm
      hscaled

/-- The constant exponential part of the decomposed two-moving window is
absorbed by the standard scaled Binet decaying-tail integral. -/
theorem Complex.binetSecondFormula_twoMovingLogWindow_constant_scaled_decay :
    ∃ Cπ : ℝ,
      0 < Cπ ∧
      ∀ w : ℂ,
        0 < w.re →
        2 ≤ ‖w‖ →
          2 * ∫ t : ℝ in Set.Ioc (‖w‖ / 2) (2 * ‖w‖),
              (2 * Real.pi) / Real.exp ((2 : ℝ) * Real.pi * t) ≤
            (Cπ / ‖w‖) *
              Complex.binetSecondFormulaDecayingTailIntegral w := by
  match Complex.binetSecondFormula_decayingTailIntegral_expLower_owner with
  | ⟨c, hc_pos, htail_lower⟩ =>
      let Cπ : ℝ := (4 * Real.pi) / c
      have hCπ_pos : 0 < Cπ :=
        div_pos (mul_pos zero_lt_four Real.pi_pos) hc_pos
      exact
        ⟨Cπ, hCπ_pos,
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
                    (2 * Real.pi) / Real.exp ((2 : ℝ) * Real.pi * t) ≤
                  (2 * Real.pi) * E :=
              Complex.binetSecondFormula_twoMovingLogWindow_constant_integral_le_exp w
            have htwice_const :
                2 * ∫ t : ℝ in Set.Ioc (‖w‖ / 2) (2 * ‖w‖),
                    (2 * Real.pi) / Real.exp ((2 : ℝ) * Real.pi * t) ≤
                  2 * ((2 * Real.pi) * E) :=
              mul_le_mul_of_nonneg_left hconst zero_le_two
            have htwice_scale :
                2 * ((2 * Real.pi) * E) = (4 * Real.pi) * E := by
              calc
                2 * ((2 * Real.pi) * E) =
                    (2 * (2 * Real.pi)) * E := by
                  exact (mul_assoc (2 : ℝ) (2 * Real.pi) E).symm
                _ = ((2 * 2) * Real.pi) * E := by
                  exact congrArg (fun x : ℝ => x * E)
                    (mul_assoc (2 : ℝ) 2 Real.pi).symm
                _ = (4 * Real.pi) * E := by
                  exact congrArg (fun x : ℝ => (x * Real.pi) * E)
                    Real.two_mul_two_eq_four_for_twoMovingLog
            have hJ_lower :
                c * N * E ≤ J :=
              htail_lower w hw_norm_two
            have hcoeff_nonneg : 0 ≤ Cπ / N :=
              div_nonneg (le_of_lt hCπ_pos) (le_of_lt hN_pos)
            have hscaled_lower :
                (Cπ / N) * (c * N * E) ≤ (Cπ / N) * J :=
              mul_le_mul_of_nonneg_left hJ_lower hcoeff_nonneg
            have hscaled_left :
                (Cπ / N) * (c * N * E) = (4 * Real.pi) * E := by
              have hc_ne : c ≠ 0 :=
                ne_of_gt hc_pos
              have hN_ne : N ≠ 0 :=
                ne_of_gt hN_pos
              calc
                (Cπ / N) * (c * N * E) =
                    (((4 * Real.pi) / c) / N) * (c * N * E) := by
                  rfl
                _ = (((4 * Real.pi) / c) / N) * ((c * N) * E) := by
                  exact Eq.refl ((((4 * Real.pi) / c) / N) * (c * N * E))
                _ = ((((4 * Real.pi) / c) / N) * (c * N)) * E := by
                  exact (mul_assoc (((4 * Real.pi) / c) / N) (c * N) E).symm
                _ = (((4 * Real.pi) / c) * c) * E := by
                  exact congrArg (fun x : ℝ => x * E)
                    (calc
                      (((4 * Real.pi) / c) / N) * (c * N) =
                          ((((4 * Real.pi) / c) / N) * N) * c := by
                        calc
                          (((4 * Real.pi) / c) / N) * (c * N) =
                              (((4 * Real.pi) / c) / N) * (N * c) := by
                            exact congrArg (fun x : ℝ => (((4 * Real.pi) / c) / N) * x)
                              (mul_comm c N)
                          _ = ((((4 * Real.pi) / c) / N) * N) * c := by
                            exact (mul_assoc (((4 * Real.pi) / c) / N) N c).symm
                      _ = ((4 * Real.pi) / c) * c := by
                        exact congrArg (fun x : ℝ => x * c)
                          (div_mul_cancel₀ ((4 * Real.pi) / c) hN_ne))
                _ = (4 * Real.pi) * E := by
                  exact congrArg (fun x : ℝ => x * E)
                    (div_mul_cancel₀ (4 * Real.pi) hc_ne)
            have htarget :
                (4 * Real.pi) * E ≤ (Cπ / ‖w‖) * J :=
              Eq.subst
                (motive := fun x : ℝ => x ≤ (Cπ / ‖w‖) * J)
                hscaled_left
                hscaled_lower
            le_trans htwice_const
              (le_trans (le_of_eq htwice_scale) htarget)⟩

/-- The full two-moving-log scalar decay follows from separate scaled decay
of the plus and minus moving logarithmic spikes. -/
theorem Complex.binetSecondFormula_twoMovingLogWindow_scaled_decay_of_plus_minus
    (hplus :
      ∃ Cplus : ℝ,
        0 < Cplus ∧
        ∀ w : ℂ,
          0 < w.re →
          2 ≤ ‖w‖ →
            2 * ∫ t : ℝ in Set.Ioc (‖w‖ / 2) (2 * ‖w‖),
                (2 * |Real.log ((max w.re |w.im + t|) / (3 * ‖w‖))|) /
                  Real.exp ((2 : ℝ) * Real.pi * t) ≤
              (Cplus / ‖w‖) *
                Complex.binetSecondFormulaDecayingTailIntegral w)
    (hminus :
      ∃ Cminus : ℝ,
        0 < Cminus ∧
        ∀ w : ℂ,
          0 < w.re →
          2 ≤ ‖w‖ →
            2 * ∫ t : ℝ in Set.Ioc (‖w‖ / 2) (2 * ‖w‖),
                (2 * |Real.log ((3 * ‖w‖) / max w.re |w.im - t|)|) /
                  Real.exp ((2 : ℝ) * Real.pi * t) ≤
              (Cminus / ‖w‖) *
                Complex.binetSecondFormulaDecayingTailIntegral w) :
    ∃ Ctwo : ℝ,
      0 < Ctwo ∧
      ∀ w : ℂ,
        0 < w.re →
        2 ≤ ‖w‖ →
          2 * ∫ t : ℝ in Set.Ioc (‖w‖ / 2) (2 * ‖w‖),
              (2 *
                (max
                  |Real.log ((max w.re |w.im + t|) / (3 * ‖w‖))|
                  |Real.log ((3 * ‖w‖) / max w.re |w.im - t|)| +
                  Real.pi)) /
                Real.exp ((2 : ℝ) * Real.pi * t) ≤
            (Ctwo / ‖w‖) *
              Complex.binetSecondFormulaDecayingTailIntegral w := by
  match hplus with
  | ⟨Cplus, hCplus_pos, hplus_bound⟩ =>
      match hminus with
      | ⟨Cminus, hCminus_pos, hminus_bound⟩ =>
          match Complex.binetSecondFormula_twoMovingLogWindow_constant_scaled_decay with
          | ⟨Cπ, hCπ_pos, hπ_bound⟩ =>
              let Ctwo : ℝ := Cplus + Cminus + Cπ
              have hCtwo_pos : 0 < Ctwo :=
                add_pos (add_pos hCplus_pos hCminus_pos) hCπ_pos
              exact
                ⟨Ctwo, hCtwo_pos,
                  fun w hw_re_pos hw_norm_two =>
                    let G : ℝ → ℝ := fun t : ℝ =>
                      (2 *
                        (max
                          |Real.log ((max w.re |w.im + t|) / (3 * ‖w‖))|
                          |Real.log ((3 * ‖w‖) / max w.re |w.im - t|)| +
                          Real.pi)) /
                        Real.exp ((2 : ℝ) * Real.pi * t)
                    let A : ℝ → ℝ := fun t : ℝ =>
                      (2 * |Real.log ((max w.re |w.im + t|) / (3 * ‖w‖))|) /
                        Real.exp ((2 : ℝ) * Real.pi * t)
                    let B : ℝ → ℝ := fun t : ℝ =>
                      (2 * |Real.log ((3 * ‖w‖) / max w.re |w.im - t|)|) /
                        Real.exp ((2 : ℝ) * Real.pi * t)
                    let P : ℝ → ℝ := fun t : ℝ =>
                      (2 * Real.pi) / Real.exp ((2 : ℝ) * Real.pi * t)
                    let S : Set ℝ := Set.Ioc (‖w‖ / 2) (2 * ‖w‖)
                    let J : ℝ :=
                      Complex.binetSecondFormulaDecayingTailIntegral w
                    have hdecomp :=
                      Complex.binetSecondFormula_twoMovingLogWindow_integral_le_sum
                        (w := w) hw_re_pos
                    have htwice_decomp :=
                      mul_le_mul_of_nonneg_left hdecomp zero_le_two
                    have htwice_sum :
                        2 *
                            (((∫ t : ℝ in S, A t) +
                              (∫ t : ℝ in S, B t)) +
                              (∫ t : ℝ in S, P t)) =
                          (2 * (∫ t : ℝ in S, A t) +
                            2 * (∫ t : ℝ in S, B t)) +
                            2 * (∫ t : ℝ in S, P t) := by
                      let IA : ℝ := ∫ t : ℝ in S, A t
                      let IB : ℝ := ∫ t : ℝ in S, B t
                      let IP : ℝ := ∫ t : ℝ in S, P t
                      exact
                        calc
                          2 * ((IA + IB) + IP) =
                              2 * (IA + IB) + 2 * IP := by
                            exact left_distrib (2 : ℝ) (IA + IB) IP
                          _ = (2 * IA + 2 * IB) + 2 * IP := by
                            exact congrArg (fun x : ℝ => x + 2 * IP)
                              (left_distrib (2 : ℝ) IA IB)
                    have hplus_w :
                        2 * (∫ t : ℝ in S, A t) ≤
                          (Cplus / ‖w‖) * J :=
                      hplus_bound w hw_re_pos hw_norm_two
                    have hminus_w :
                        2 * (∫ t : ℝ in S, B t) ≤
                          (Cminus / ‖w‖) * J :=
                      hminus_bound w hw_re_pos hw_norm_two
                    have hπ_w :
                        2 * (∫ t : ℝ in S, P t) ≤
                          (Cπ / ‖w‖) * J :=
                      hπ_bound w hw_re_pos hw_norm_two
                    have hsum_bounds :
                        2 * (∫ t : ℝ in S, A t) +
                            2 * (∫ t : ℝ in S, B t) +
                            2 * (∫ t : ℝ in S, P t) ≤
                          (Cplus / ‖w‖) * J +
                            (Cminus / ‖w‖) * J +
                            (Cπ / ‖w‖) * J :=
                      show
                          (2 * (∫ t : ℝ in S, A t) +
                              2 * (∫ t : ℝ in S, B t)) +
                              2 * (∫ t : ℝ in S, P t) ≤
                            ((Cplus / ‖w‖) * J +
                              (Cminus / ‖w‖) * J) +
                              (Cπ / ‖w‖) * J from
                        add_le_add
                          (add_le_add hplus_w hminus_w)
                          hπ_w
                    have hconstant_sum :
                        (Cplus / ‖w‖) * J +
                            (Cminus / ‖w‖) * J +
                            (Cπ / ‖w‖) * J =
                          (Ctwo / ‖w‖) * J := by
                      calc
                        (Cplus / ‖w‖) * J +
                            (Cminus / ‖w‖) * J +
                            (Cπ / ‖w‖) * J =
                            ((Cplus / ‖w‖) + (Cminus / ‖w‖) +
                              (Cπ / ‖w‖)) * J := by
                          calc
                            (Cplus / ‖w‖) * J +
                                (Cminus / ‖w‖) * J +
                                (Cπ / ‖w‖) * J =
                                ((Cplus / ‖w‖) + (Cminus / ‖w‖)) * J +
                                  (Cπ / ‖w‖) * J := by
                              exact congrArg (fun x : ℝ => x + (Cπ / ‖w‖) * J)
                                (right_distrib (Cplus / ‖w‖) (Cminus / ‖w‖) J).symm
                            _ =
                                (((Cplus / ‖w‖) + (Cminus / ‖w‖)) +
                                  (Cπ / ‖w‖)) * J := by
                              exact
                                (right_distrib
                                  ((Cplus / ‖w‖) + (Cminus / ‖w‖))
                                  (Cπ / ‖w‖) J).symm
                            _ =
                                ((Cplus / ‖w‖) + (Cminus / ‖w‖) +
                                  (Cπ / ‖w‖)) * J := by
                              exact Eq.refl
                                (((Cplus / ‖w‖) + (Cminus / ‖w‖) +
                                  (Cπ / ‖w‖)) * J)
                        _ =
                            (((Cplus + Cminus) / ‖w‖) +
                              (Cπ / ‖w‖)) * J := by
                          exact congrArg (fun x : ℝ => (x + (Cπ / ‖w‖)) * J)
                            (add_div Cplus Cminus ‖w‖).symm
                        _ =
                            ((Cplus + Cminus + Cπ) / ‖w‖) * J := by
                          exact congrArg (fun x : ℝ => x * J)
                            (add_div (Cplus + Cminus) Cπ ‖w‖).symm
                        _ = (Ctwo / ‖w‖) * J := by
                          rfl
                    le_trans htwice_decomp
                      (le_trans (le_of_eq htwice_sum)
                        (le_trans hsum_bounds (le_of_eq hconstant_sum)))⟩

/-- The full two-moving-log scalar decay follows from the oriented plus and
minus moving-log spike estimates. -/
theorem Complex.binetSecondFormula_twoMovingLogWindow_scaled_decay_of_oriented_plus_minus
    (hplus :
      ∃ Cplus : ℝ,
        0 < Cplus ∧
        ∀ w : ℂ,
          0 < w.re →
          2 ≤ ‖w‖ →
            2 * ∫ t : ℝ in Set.Ioc (‖w‖ / 2) (2 * ‖w‖),
                (2 * (-Real.log ((max w.re |w.im + t|) / (3 * ‖w‖)))) /
                  Real.exp ((2 : ℝ) * Real.pi * t) ≤
              (Cplus / ‖w‖) *
                Complex.binetSecondFormulaDecayingTailIntegral w)
    (hminus :
      ∃ Cminus : ℝ,
        0 < Cminus ∧
        ∀ w : ℂ,
          0 < w.re →
          2 ≤ ‖w‖ →
            2 * ∫ t : ℝ in Set.Ioc (‖w‖ / 2) (2 * ‖w‖),
                (2 * Real.log ((3 * ‖w‖) / max w.re |w.im - t|)) /
                  Real.exp ((2 : ℝ) * Real.pi * t) ≤
              (Cminus / ‖w‖) *
                Complex.binetSecondFormulaDecayingTailIntegral w) :
    ∃ Ctwo : ℝ,
      0 < Ctwo ∧
      ∀ w : ℂ,
        0 < w.re →
        2 ≤ ‖w‖ →
          2 * ∫ t : ℝ in Set.Ioc (‖w‖ / 2) (2 * ‖w‖),
              (2 *
                (max
                  |Real.log ((max w.re |w.im + t|) / (3 * ‖w‖))|
                  |Real.log ((3 * ‖w‖) / max w.re |w.im - t|)| +
                  Real.pi)) /
                Real.exp ((2 : ℝ) * Real.pi * t) ≤
            (Ctwo / ‖w‖) *
              Complex.binetSecondFormulaDecayingTailIntegral w := by
  have hplus_abs :
      ∃ Cplus : ℝ,
        0 < Cplus ∧
        ∀ w : ℂ,
          0 < w.re →
          2 ≤ ‖w‖ →
            2 * ∫ t : ℝ in Set.Ioc (‖w‖ / 2) (2 * ‖w‖),
                (2 * |Real.log ((max w.re |w.im + t|) / (3 * ‖w‖))|) /
                  Real.exp ((2 : ℝ) * Real.pi * t) ≤
              (Cplus / ‖w‖) *
                Complex.binetSecondFormulaDecayingTailIntegral w :=
    Complex.binetSecondFormula_plusMovingLog_scaled_decay_of_oriented_neg_log
      hplus
  have hminus_abs :
      ∃ Cminus : ℝ,
        0 < Cminus ∧
        ∀ w : ℂ,
          0 < w.re →
          2 ≤ ‖w‖ →
            2 * ∫ t : ℝ in Set.Ioc (‖w‖ / 2) (2 * ‖w‖),
                (2 * |Real.log ((3 * ‖w‖) / max w.re |w.im - t|)|) /
                  Real.exp ((2 : ℝ) * Real.pi * t) ≤
              (Cminus / ‖w‖) *
                Complex.binetSecondFormulaDecayingTailIntegral w :=
    Complex.binetSecondFormula_minusMovingLog_scaled_decay_of_oriented_log
      hminus
  exact
    Complex.binetSecondFormula_twoMovingLogWindow_scaled_decay_of_plus_minus
      hplus_abs hminus_abs

end

end LFunctions
end Boundary
