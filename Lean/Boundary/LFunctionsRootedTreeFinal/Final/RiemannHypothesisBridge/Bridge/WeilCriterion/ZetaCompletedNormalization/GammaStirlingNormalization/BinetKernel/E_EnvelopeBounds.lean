import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalization.GammaStirlingNormalization.BinetKernel.A_RealAnalysisBounds
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalization.GammaStirlingNormalization.BinetKernel.C_ComplexLogBounds
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalization.GammaStirlingNormalization.BinetKernel.D_PointwiseMajorants
import Mathlib

import Mathlib.Analysis.Complex.PhragmenLindelof
import Mathlib.Data.Complex.Exponential
import Mathlib.Analysis.RCLike.Basic
import Mathlib.NumberTheory.AbelSummation
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.Analysis.SpecialFunctions.Complex.Arctan
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Mathlib.Analysis.SpecialFunctions.Log.Monotone
import Mathlib.Data.Real.Pi.Bounds
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Integral.SetIntegral
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ClassicalAnalysis.GammaBinetStirling.BinetAbelPlanaFiniteFormula
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ClassicalAnalysis.GammaBinetStirling.BinetTailContour
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalization.Core.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalization.FiniteOrderAlgebra.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalization.RightCriticalStripCompact.Owner

/-!
# Binet kernel and sectorial Gamma seed estimates

This file is a sequential owner sublayer split out of
`ZetaCompletedNormalization.GammaStirlingNormalization.Owner`.  Declaration order is preserved.
-/

namespace Boundary
namespace LFunctions

noncomputable section

theorem Complex.binetSecondFormula_branchLocalIndentation_logWindowExpBound_owner :
    Complex.BinetSecondFormulaBranchLocalIndentationLogWindowExpBound := by
  intro δ hδ
  let Lδ : ℝ :=
    max |Real.log (δ / 3)| |Real.log (3 / δ)|
  let C : ℝ := 8 * (Lδ + Real.pi + 1)
  have hLδ_nonneg : 0 ≤ Lδ :=
    le_max_of_le_left (abs_nonneg (Real.log (δ / 3)))
  have hC_pos : 0 < C := by
    have hinside_pos : 0 < Lδ + Real.pi + 1 := by
      exact
        add_pos_of_nonneg_of_pos
          (add_nonneg hLδ_nonneg Real.pi_nonneg)
          zero_lt_one
    have height_pos : 0 < (8 : ℝ) := by
      show 0 < (2 : ℝ) * 4
      exact mul_pos two_pos four_pos
    exact mul_pos height_pos hinside_pos
  exact
    ⟨C, hC_pos,
      fun w hw_sector hw_norm_two =>
        have hw_norm_pos : 0 < ‖w‖ :=
          lt_of_lt_of_le zero_lt_two hw_norm_two
        have hw_re_pos : 0 < w.re :=
          lt_of_lt_of_le (mul_pos hδ hw_norm_pos) hw_sector
        have hre_le_norm : w.re ≤ ‖w‖ := by
          calc
            w.re = |w.re| := Eq.symm (abs_of_pos hw_re_pos)
            _ ≤ ‖w‖ := Complex.abs_re_le_abs w
        let x : ℝ := w.re / (3 * ‖w‖)
        let y : ℝ := (3 * ‖w‖) / w.re
        have hthree_norm_pos : 0 < 3 * ‖w‖ :=
          mul_pos Real.zero_lt_three hw_norm_pos
        have hx_pos : 0 < x :=
          div_pos hw_re_pos hthree_norm_pos
        have hy_pos : 0 < y :=
          div_pos hthree_norm_pos hw_re_pos
        have hx_lower : δ / 3 ≤ x := by
          have hmul :
              δ * ‖w‖ / (3 * ‖w‖) ≤ w.re / (3 * ‖w‖) :=
            div_le_div_of_nonneg_right hw_sector (le_of_lt hthree_norm_pos)
          have hleft : δ * ‖w‖ / (3 * ‖w‖) = δ / 3 := by
            calc
              δ * ‖w‖ / (3 * ‖w‖) =
                  (δ / 3) * (‖w‖ / ‖w‖) := by
                calc
                  δ * ‖w‖ / (3 * ‖w‖) =
                      (δ * ‖w‖) / (3 * ‖w‖) := rfl
                  _ = (δ / 3) * (‖w‖ / ‖w‖) := by
                    exact
                      Eq.symm
                        (div_mul_div_comm δ 3 ‖w‖ ‖w‖)
              _ = (δ / 3) * 1 := by
                exact congrArg (fun z : ℝ => (δ / 3) * z)
                  (div_self (ne_of_gt hw_norm_pos))
              _ = δ / 3 := mul_one (δ / 3)
          Eq.subst
            (motive := fun z : ℝ => z ≤ x)
            hleft
            hmul
        have hx_upper : x ≤ 1 := by
          have hnum_le : w.re ≤ 3 * ‖w‖ := by
            calc
              w.re ≤ ‖w‖ := hre_le_norm
              _ ≤ 3 * ‖w‖ :=
                le_mul_of_one_le_left (le_of_lt hw_norm_pos) Real.one_le_three_real
          exact
            (div_le_one hthree_norm_pos).mpr hnum_le
        have hy_lower : (1 : ℝ) ≤ y := by
          have hden_le : w.re ≤ 3 * ‖w‖ := by
            calc
              w.re ≤ ‖w‖ := hre_le_norm
              _ ≤ 3 * ‖w‖ :=
                le_mul_of_one_le_left (le_of_lt hw_norm_pos) Real.one_le_three_real
          exact (le_div_iff₀ hw_re_pos).mpr
            (Eq.subst
              (motive := fun z : ℝ => z ≤ 3 * ‖w‖)
              (one_mul w.re).symm
              hden_le)
        have hy_upper : y ≤ 3 / δ := by
          have hden_le :
              δ * ‖w‖ ≤ w.re := hw_sector
          have hnum_nonneg : 0 ≤ 3 * ‖w‖ :=
            le_of_lt hthree_norm_pos
          have hdiv_le :
              (3 * ‖w‖) / w.re ≤ (3 * ‖w‖) / (δ * ‖w‖) :=
            div_le_div_of_nonneg_left
              hnum_nonneg
              (mul_pos hδ hw_norm_pos)
              hden_le
          have hright : (3 * ‖w‖) / (δ * ‖w‖) = 3 / δ := by
            calc
              (3 * ‖w‖) / (δ * ‖w‖) =
                  (3 / δ) * (‖w‖ / ‖w‖) := by
                exact
                  Eq.symm
                    (div_mul_div_comm 3 δ ‖w‖ ‖w‖)
              _ = (3 / δ) * 1 := by
                exact congrArg (fun z : ℝ => (3 / δ) * z)
                  (div_self (ne_of_gt hw_norm_pos))
              _ = 3 / δ := mul_one (3 / δ)
          Eq.subst
            (motive := fun z : ℝ => y ≤ z)
            hright
            hdiv_le
        have hδ_div_three_pos : 0 < δ / 3 :=
          div_pos hδ Real.zero_lt_three
        have hthree_div_δ_ge_one : (1 : ℝ) ≤ 3 / δ := by
          le_trans hy_lower hy_upper
        have hx_log_bound :
            |Real.log x| ≤ Lδ :=
          le_trans
            (Real.abs_log_le_max_abs_log_of_bounds
              hδ_div_three_pos
              (le_trans hx_lower hx_upper)
              hx_lower
              hx_upper)
            (le_max_left _ _)
        have hy_log_bound :
            |Real.log y| ≤ Lδ :=
          le_trans
            (Real.abs_log_le_max_abs_log_of_bounds
              zero_lt_one
              hthree_div_δ_ge_one
              hy_lower
              hy_upper)
            (le_max_right _ _)
        have hlog_max_bound :
            max |Real.log x|
              (max |Real.log (1 : ℝ)| |Real.log y|) + Real.pi ≤
              Lδ + Real.pi := by
          have hlog_one : |Real.log (1 : ℝ)| ≤ Lδ :=
            le_trans
              (le_of_eq (congrArg abs Real.log_one))
              hLδ_nonneg
          have hinner :
              max |Real.log (1 : ℝ)| |Real.log y| ≤ Lδ :=
            max_le hlog_one hy_log_bound
          have houter :
              max |Real.log x|
                (max |Real.log (1 : ℝ)| |Real.log y|) ≤ Lδ :=
            max_le hx_log_bound hinner
          exact add_le_add_right houter Real.pi
        have hvolume_bound :
            (volume (Set.Ioc (‖w‖ / 2) (2 * ‖w‖))).toReal ≤
              2 * ‖w‖ := by
          have hvolume :
              volume (Set.Ioc (‖w‖ / 2) (2 * ‖w‖)) =
                ENNReal.ofReal ((2 * ‖w‖) - (‖w‖ / 2)) :=
            Real.volume_Ioc
          have hlength_nonneg :
              0 ≤ (2 * ‖w‖) - (‖w‖ / 2) := by
            exact sub_nonneg.mpr
              ((le_div_iff₀ two_pos).mpr
                (by
                  calc
                    (‖w‖ / 2) * 2 = ‖w‖ := by
                      exact div_mul_cancel₀ ‖w‖ two_ne_zero
                    _ ≤ 2 * ‖w‖ :=
                      le_mul_of_one_le_left (le_of_lt hw_norm_pos) one_le_two))
          have hlength_le :
              (2 * ‖w‖) - (‖w‖ / 2) ≤ 2 * ‖w‖ :=
            sub_le_self (2 * ‖w‖)
              (div_nonneg (norm_nonneg w) zero_le_two)
          calc
            (volume (Set.Ioc (‖w‖ / 2) (2 * ‖w‖))).toReal =
                (ENNReal.ofReal ((2 * ‖w‖) - (‖w‖ / 2))).toReal := by
              exact congrArg ENNReal.toReal hvolume
            _ = (2 * ‖w‖) - (‖w‖ / 2) := by
              exact ENNReal.toReal_ofReal hlength_nonneg
            _ ≤ 2 * ‖w‖ := hlength_le
        have hden_lower :
            Real.exp (Real.pi * ‖w‖) / 2 ≤
              Real.exp (Real.pi * ‖w‖) - 1 := by
          have htwo_le_exp :
              (2 : ℝ) ≤ Real.exp (Real.pi * ‖w‖) := by
            have hlog_two_le_two : Real.log 2 ≤ (2 : ℝ) := by
              exact le_of_lt
                (lt_trans
                  (Real.log_lt_sub_one_of_pos
                    Real.binetMajorant_two_pos
                    Real.binetMajorant_two_ne_one)
                  (sub_one_lt 2))
            have htwo_le_pi_norm :
                (2 : ℝ) ≤ Real.pi * ‖w‖ := by
              calc
                (2 : ℝ) ≤ Real.pi * 2 := by
                  calc
                    (2 : ℝ) = 1 * 2 := (one_mul 2).symm
                    _ ≤ Real.pi * 2 :=
                      mul_le_mul_of_nonneg_right
                        (le_of_lt
                          (lt_trans Real.binetMajorant_one_lt_three Real.pi_gt_three))
                        zero_le_two
                _ ≤ Real.pi * ‖w‖ :=
                  mul_le_mul_of_nonneg_left hw_norm_two
                    (le_of_lt Real.pi_pos)
            have hlog_le : Real.log 2 ≤ Real.pi * ‖w‖ :=
              le_trans hlog_two_le_two htwo_le_pi_norm
            exact (Real.log_le_iff_le_exp Real.binetMajorant_two_pos).mp hlog_le
          exact Real.div_two_le_sub_one_of_two_le htwo_le_exp
        have hden_pos :
            0 < Real.exp (Real.pi * ‖w‖) - 1 := by
          have hpi_norm_pos : 0 < Real.pi * ‖w‖ :=
            mul_pos Real.pi_pos hw_norm_pos
          exact sub_pos.mpr
            (calc
              (1 : ℝ) = Real.exp 0 := Eq.symm Real.exp_zero
              _ < Real.exp (Real.pi * ‖w‖) :=
                Real.exp_lt_exp.mpr hpi_norm_pos)
        have hreciprocal :
            1 / (Real.exp (Real.pi * ‖w‖) - 1) ≤
              2 / Real.exp (Real.pi * ‖w‖) := by
          have hE_pos : 0 < Real.exp (Real.pi * ‖w‖) :=
            Real.exp_pos (Real.pi * ‖w‖)
          have hhalf_pos : 0 < Real.exp (Real.pi * ‖w‖) / 2 :=
            div_pos hE_pos two_pos
          have hdiv :
              (1 : ℝ) / (Real.exp (Real.pi * ‖w‖) - 1) ≤
                1 / (Real.exp (Real.pi * ‖w‖) / 2) :=
            div_le_div_of_nonneg_left zero_le_one hhalf_pos hden_lower
          have hrewrite :
              (1 : ℝ) / (Real.exp (Real.pi * ‖w‖) / 2) =
                2 / Real.exp (Real.pi * ‖w‖) := by
            calc
              (1 : ℝ) / (Real.exp (Real.pi * ‖w‖) / 2) =
                  1 * 2 / Real.exp (Real.pi * ‖w‖) := by
                exact div_div_eq_mul_div 1 (Real.exp (Real.pi * ‖w‖)) 2
              _ = 2 / Real.exp (Real.pi * ‖w‖) := by
                exact congrArg (fun z : ℝ => z / Real.exp (Real.pi * ‖w‖))
                  (one_mul 2)
          le_trans hdiv (le_of_eq hrewrite)
        have hnum_nonneg :
            0 ≤
              max |Real.log x|
                (max |Real.log (1 : ℝ)| |Real.log y|) + Real.pi :=
          add_nonneg
            (le_max_of_le_left (abs_nonneg (Real.log x)))
            Real.pi_nonneg
        have hwindow_nonneg :
            0 ≤
              (max |Real.log x|
                (max |Real.log (1 : ℝ)| |Real.log y|) + Real.pi) /
                (Real.exp (Real.pi * ‖w‖) - 1) :=
          div_nonneg hnum_nonneg (le_of_lt hden_pos)
        have hfraction_bound :
            (max |Real.log x|
                (max |Real.log (1 : ℝ)| |Real.log y|) + Real.pi) /
                (Real.exp (Real.pi * ‖w‖) - 1) ≤
              (Lδ + Real.pi) * (2 / Real.exp (Real.pi * ‖w‖)) := by
          have hstep1 :
              (max |Real.log x|
                  (max |Real.log (1 : ℝ)| |Real.log y|) + Real.pi) /
                  (Real.exp (Real.pi * ‖w‖) - 1) ≤
                (Lδ + Real.pi) /
                  (Real.exp (Real.pi * ‖w‖) - 1) :=
            div_le_div_of_nonneg_right hlog_max_bound (le_of_lt hden_pos)
          have hstep2 :
              (Lδ + Real.pi) /
                  (Real.exp (Real.pi * ‖w‖) - 1) ≤
                (Lδ + Real.pi) * (2 / Real.exp (Real.pi * ‖w‖)) :=
            mul_le_mul_of_nonneg_left
              hreciprocal
              (add_nonneg hLδ_nonneg Real.pi_nonneg)
          le_trans hstep1 hstep2
        have hmain :
            2 *
                (((max |Real.log x|
                    (max |Real.log (1 : ℝ)| |Real.log y|) + Real.pi) /
                  (Real.exp (Real.pi * ‖w‖) - 1)) *
                  (volume (Set.Ioc (‖w‖ / 2) (2 * ‖w‖))).toReal) ≤
              8 * (Lδ + Real.pi) * ‖w‖ *
                Real.exp (-(Real.pi * ‖w‖)) := by
          have hprod :
              ((max |Real.log x|
                    (max |Real.log (1 : ℝ)| |Real.log y|) + Real.pi) /
                  (Real.exp (Real.pi * ‖w‖) - 1)) *
                  (volume (Set.Ioc (‖w‖ / 2) (2 * ‖w‖))).toReal ≤
                ((Lδ + Real.pi) * (2 / Real.exp (Real.pi * ‖w‖))) *
                  (2 * ‖w‖) :=
            mul_le_mul
              hfraction_bound
              hvolume_bound
              (ENNReal.toReal_nonneg)
              (mul_nonneg
                (add_nonneg hLδ_nonneg Real.pi_nonneg)
                (div_nonneg zero_le_two
                  (le_of_lt (Real.exp_pos (Real.pi * ‖w‖)))))
          have hscale :
              2 * (((Lδ + Real.pi) * (2 / Real.exp (Real.pi * ‖w‖))) *
                  (2 * ‖w‖)) =
                8 * (Lδ + Real.pi) * ‖w‖ *
                  Real.exp (-(Real.pi * ‖w‖)) := by
            let A : ℝ := Lδ + Real.pi
            let N : ℝ := ‖w‖
            let E : ℝ := Real.exp (Real.pi * ‖w‖)
            calc
              2 * (((Lδ + Real.pi) * (2 / Real.exp (Real.pi * ‖w‖))) *
                  (2 * ‖w‖)) =
                  2 * ((A * (2 * E⁻¹)) * (2 * N)) := by
                rfl
              _ = 2 * (((A * 2) * E⁻¹) * (2 * N)) := by
                exact congrArg (fun z : ℝ => 2 * (z * (2 * N)))
                  (mul_assoc A 2 E⁻¹)
              _ = 2 * (((2 * A) * E⁻¹) * (2 * N)) := by
                exact congrArg
                  (fun z : ℝ => 2 * ((z * E⁻¹) * (2 * N)))
                  (mul_comm A 2)
              _ = (2 * ((2 * A) * E⁻¹)) * (2 * N) := by
                exact (mul_assoc 2 (((2 * A) * E⁻¹)) (2 * N)).symm
              _ = ((2 * ((2 * A) * E⁻¹)) * 2) * N := by
                exact mul_assoc (2 * ((2 * A) * E⁻¹)) 2 N
              _ = ((2 * 2) * ((2 * A) * E⁻¹)) * N := by
                exact congrArg (fun z : ℝ => z * N)
                  ((mul_assoc 2 2 (((2 * A) * E⁻¹))).symm)
              _ = (4 * ((2 * A) * E⁻¹)) * N := by
                rfl
              _ = ((4 * (2 * A)) * E⁻¹) * N := by
                exact congrArg (fun z : ℝ => z * N)
                  (mul_assoc 4 (2 * A) E⁻¹)
              _ = ((8 * A) * E⁻¹) * N := by
                rfl
              _ = (8 * A * N) * E⁻¹ := by
                calc
                  ((8 * A) * E⁻¹) * N =
                      N * ((8 * A) * E⁻¹) := by
                    exact mul_comm (((8 : ℝ) * A) * E⁻¹) N
                  _ = (N * (8 * A)) * E⁻¹ := by
                    exact mul_assoc N (8 * A) E⁻¹
                  _ = ((8 * A) * N) * E⁻¹ := by
                    exact congrArg (fun z : ℝ => z * E⁻¹)
                      (mul_comm N (8 * A))
                  _ = (8 * A * N) * E⁻¹ := by
                    rfl
              _ = (8 * (Lδ + Real.pi) * ‖w‖) *
                  (Real.exp (Real.pi * ‖w‖))⁻¹ := by
                rfl
              _ = 8 * (Lδ + Real.pi) * ‖w‖ *
                  Real.exp (-(Real.pi * ‖w‖)) := by
                exact congrArg
                  (fun z : ℝ => 8 * (Lδ + Real.pi) * ‖w‖ * z)
                  (Real.exp_neg (Real.pi * ‖w‖)).symm
          le_trans
            (mul_le_mul_of_nonneg_left hprod zero_le_two)
            (le_of_eq hscale)
        have htarget :
            8 * (Lδ + Real.pi) * ‖w‖ *
                Real.exp (-(Real.pi * ‖w‖)) ≤
              C * ‖w‖ * Real.exp (-Real.pi * ‖w‖) := by
          have hcoef :
              8 * (Lδ + Real.pi) ≤ C := by
            calc
              8 * (Lδ + Real.pi) ≤ 8 * (Lδ + Real.pi + 1) := by
                exact mul_le_mul_of_nonneg_left
                  (le_add_of_nonneg_right zero_le_one)
                  (le_of_lt
                    (by
                      show 0 < (2 : ℝ) * 4
                      exact mul_pos two_pos four_pos))
              _ = C := rfl
          have hscale_nonneg :
              0 ≤ ‖w‖ * Real.exp (-Real.pi * ‖w‖) :=
            mul_nonneg (norm_nonneg w)
              (le_of_lt (Real.exp_pos (-Real.pi * ‖w‖)))
          exact
            mul_le_mul_of_nonneg_right hcoef hscale_nonneg
        le_trans
          (Eq.subst
            (motive := fun z : ℝ =>
              z ≤ 8 * (Lδ + Real.pi) * ‖w‖ *
                Real.exp (-(Real.pi * ‖w‖)))
            (by rfl :
              2 *
                  (((max |Real.log (w.re / (3 * ‖w‖))|
                      (max |Real.log (1 : ℝ)|
                        |Real.log ((3 * ‖w‖) / w.re)|) + Real.pi) /
                    (Real.exp (Real.pi * ‖w‖) - 1)) *
                    (volume (Set.Ioc (‖w‖ / 2) (2 * ‖w‖))).toReal) =
                2 *
                  (((max |Real.log x|
                      (max |Real.log (1 : ℝ)| |Real.log y|) + Real.pi) /
                    (Real.exp (Real.pi * ‖w‖) - 1)) *
                    (volume (Set.Ioc (‖w‖ / 2) (2 * ‖w‖))).toReal))
            hmain)
          htarget⟩

/-- Sector-local envelope bound from the explicit logarithmic-window bound. -/
theorem Complex.binetSecondFormula_branchLocalIndentation_sectorEnvelopeExpBound_of_logWindow
    (hlog :
      Complex.BinetSecondFormulaBranchLocalIndentationLogWindowExpBound) :
    Complex.BinetSecondFormulaBranchLocalIndentationSectorEnvelopeExpBound := by
  intro δ hδ
  match hlog δ hδ with
  | ⟨C, hC_pos, hbound⟩ =>
      exact
        ⟨C, hC_pos,
          fun w hw_sector hw_norm_two =>
            hbound w hw_sector hw_norm_two⟩

/-- Owner analytic leaf: sector-local exponential upper bound for the
branch-window envelope. -/
theorem Complex.binetSecondFormula_branchLocalIndentation_sectorEnvelopeExpBound_owner :
    Complex.BinetSecondFormulaBranchLocalIndentationSectorEnvelopeExpBound := by
  exact
    Complex.binetSecondFormula_branchLocalIndentation_sectorEnvelopeExpBound_of_logWindow
      Complex.binetSecondFormula_branchLocalIndentation_logWindowExpBound_owner

/-- Owner real-variable leaf: unit-interval lower bound for the Binet scalar kernel. -/


end
end LFunctions
end Boundary
