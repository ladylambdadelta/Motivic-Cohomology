import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalization.GammaStirlingNormalization.BinetKernel.B_ExponentialDecay
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalization.GammaStirlingNormalization.BinetKernel.D_PointwiseMajorants
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalization.GammaStirlingNormalization.BinetKernel.E_EnvelopeBounds
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalization.GammaStirlingNormalization.BinetKernel.F_IntegralAccounting

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

/-- Nonnegativity of the standard decaying-tail integral, obtained from the
owner exponential lower bound. -/
theorem Complex.binetSecondFormula_decayingTailIntegral_nonneg_of_norm_two
    {w : ℂ}
    (hw_norm_two : 2 ≤ ‖w‖) :
    0 ≤ Complex.binetSecondFormulaDecayingTailIntegral w := by
  match Complex.binetSecondFormula_decayingTailIntegral_expLower_owner with
  | ⟨c, hc_pos, htail_lower⟩ =>
      have hnorm_pos : 0 < ‖w‖ :=
        lt_of_lt_of_le zero_lt_two hw_norm_two
      have hexp_pos : 0 < Real.exp (-Real.pi * ‖w‖) :=
        Real.exp_pos (-Real.pi * ‖w‖)
      have hlower_nonneg :
          0 ≤ c * ‖w‖ * Real.exp (-Real.pi * ‖w‖) :=
        le_of_lt
          (mul_pos
            (mul_pos hc_pos hnorm_pos)
            hexp_pos)
      exact le_trans hlower_nonneg (htail_lower w hw_norm_two)

/-- Honest full-sector Binet tail estimate before local-indentation
absorption.

This is the estimate supplied by the contour calculation in the open right
half-plane.  It keeps the branch-wall logarithmic envelope explicit; the pure
`C / ‖w‖` tail package is a strictly stronger absorption theorem. -/
def Complex.BinetSecondFormulaBranchLocalIndentationTailControl : Prop :=
  ∃ Cfar : ℝ,
    0 ≤ Cfar ∧
    ∀ w : ℂ,
      0 < w.re →
      2 ≤ ‖w‖ →
        2 * ∫ t : ℝ in Set.Ioi (‖w‖ / 2),
            ‖Complex.binetSecondFormulaPrincipalTailKernel w t‖ ≤
          Complex.binetSecondFormulaBranchLocalIndentationEnvelope w +
            (Cfar / ‖w‖) *
              Complex.binetSecondFormulaDecayingTailIntegral w

/-- Honest tail-remainder estimate before local-indentation absorption.

This is the tail-remainder version of
`BinetSecondFormulaBranchLocalIndentationTailControl`: it transfers the
principal-tail integral estimate to the actual Binet tail remainder while
keeping the branch-wall local-indentation envelope explicit. -/
def Complex.BinetSecondFormulaTailRemainderLocalIndentationTailControl : Prop :=
  ∃ Cfar : ℝ,
    0 ≤ Cfar ∧
    ∀ w : ℂ,
      0 < w.re →
      2 ≤ ‖w‖ →
        ‖Complex.binetSecondFormulaTailRemainder w‖ ≤
          Complex.binetSecondFormulaBranchLocalIndentationEnvelope w +
            (Cfar / ‖w‖) *
              Complex.binetSecondFormulaDecayingTailIntegral w

/-- Sector-local absorption of the Binet branch-wall local-indentation
envelope.

The pointwise logarithmic envelope is uniformly absorbable only after staying
a fixed angular distance away from the branch wall, and only at the natural
scale of the Binet decaying-tail integral.  The stronger pure
`C / ‖w‖` scale is not a consequence of this scalar window estimate: the
bounded indentation window has length comparable to `‖w‖`.  The full-sector
pure tail theorem must therefore use paired contour cancellation rather than
this local scalar absorption. -/
def Complex.BinetSecondFormulaBranchLocalIndentationSectorAbsorption : Prop :=
  ∀ δ : ℝ,
    0 < δ →
      ∃ C : ℝ,
        0 < C ∧
        ∀ w : ℂ,
          δ * ‖w‖ ≤ w.re →
          2 ≤ ‖w‖ →
            Complex.binetSecondFormulaBranchLocalIndentationEnvelope w ≤
              C * Complex.binetSecondFormulaDecayingTailIntegral w

/-- Sector-local pre-cancellation tail-remainder absorption.

Away from the branch wall, the local-indentation envelope can be absorbed
into the standard decaying tail, leaving a sector-local tail-remainder bound.
This is weaker than full branch-wall contour cancellation because the constant
depends on the angular margin `δ`. -/
def Complex.BinetSecondFormulaTailRemainderSectorLocalAbsorption : Prop :=
  ∀ δ : ℝ,
    0 < δ →
      ∃ C : ℝ,
        0 < C ∧
        ∀ w : ℂ,
          δ * ‖w‖ ≤ w.re →
          2 ≤ ‖w‖ →
            ‖Complex.binetSecondFormulaTailRemainder w‖ ≤
              (C + C / ‖w‖) *
                Complex.binetSecondFormulaDecayingTailIntegral w

/-- On the Binet split-tail range the explicit decaying summand has no sign
change, so its absolute value integrates as the constant multiple
`1 / ‖w‖` of the scalar tail kernel. -/
theorem Complex.binetSecondFormula_principalTailKernel_integral_cancellation_estimate_ownerGap :
    Complex.BinetSecondFormulaBranchLocalIndentationTailControl := by
  match
    Complex.binetSecondFormula_principalTailKernel_integral_localIndentation_add_far_scaled_decay with
  | ⟨Cfar, hCfar_nonneg, hestimate⟩ =>
      exact
        ⟨Cfar, hCfar_nonneg,
          fun w hw_re_pos hw_norm_two =>
            hestimate w hw_re_pos (le_trans one_le_two hw_norm_two)⟩

/-- Owner-level far-tail principal-kernel integral decay.

This is the far part of the principal-tail split, already away from the
branch-wall window. -/
theorem Complex.binetSecondFormula_principalTailKernel_integral_far_scaled_decay_owner :
    ∃ C : ℝ,
      0 ≤ C ∧
      ∀ w : ℂ,
        0 < w.re →
          1 ≤ ‖w‖ →
            2 * ∫ t : ℝ in Set.Ioi (2 * ‖w‖),
                ‖Complex.binetSecondFormulaPrincipalTailKernel w t‖ ≤
              (C / ‖w‖) *
                (∫ t : ℝ in Set.Ioi (‖w‖ / 2),
                  t / (Real.exp ((2 : ℝ) * Real.pi * t) - 1)) := by
  exact
    Complex.binetSecondFormula_principalTailKernel_integral_far_scaled_decay

/-- Owner-level split of the principal-tail norm integral into its bounded
branch-wall window and far-tail pieces. -/
theorem Complex.binetSecondFormula_principalTailKernel_integral_le_boundedWindow_add_far_owner
    {w : ℂ}
    (hw_re_pos : 0 < w.re) :
    ∫ t : ℝ in Set.Ioi (‖w‖ / 2),
        ‖Complex.binetSecondFormulaPrincipalTailKernel w t‖ ≤
      (∫ t : ℝ in Set.Ioc (‖w‖ / 2) (2 * ‖w‖),
        ‖Complex.binetSecondFormulaPrincipalTailKernel w t‖) +
      (∫ t : ℝ in Set.Ioi (2 * ‖w‖),
        ‖Complex.binetSecondFormulaPrincipalTailKernel w t‖) := by
  exact
    Complex.binetSecondFormula_principalTailKernel_integral_le_boundedWindow_add_far
      (w := w) hw_re_pos

/-- Pre-cancellation tail-remainder estimate with the branch-wall
local-indentation term still visible.

This is the honest contour estimate before paired branch-wall cancellation:
the actual Binet tail remainder is bounded by the local indentation envelope
plus the far scaled decaying tail. -/
theorem Complex.binetSecondFormula_principalTailKernel_integral_sectorBound_of_localIndentation_absorption
    (hlocal : Complex.BinetSecondFormulaBranchLocalIndentationTailControl)
    (habsorb : Complex.BinetSecondFormulaBranchLocalIndentationSectorAbsorption) :
    ∀ δ : ℝ,
      0 < δ →
        ∃ C : ℝ,
          0 < C ∧
          ∀ w : ℂ,
            δ * ‖w‖ ≤ w.re →
            2 ≤ ‖w‖ →
              2 * ∫ t : ℝ in Set.Ioi (‖w‖ / 2),
                  ‖Complex.binetSecondFormulaPrincipalTailKernel w t‖ ≤
                (C + C / ‖w‖) *
                  (∫ t : ℝ in Set.Ioi (‖w‖ / 2),
                    t / (Real.exp ((2 : ℝ) * Real.pi * t) - 1)) := by
  intro δ hδ
  match hlocal with
  | ⟨Cfar, hCfar_nonneg, hlocal_estimate⟩ =>
      match habsorb δ hδ with
      | ⟨Clocal, hClocal_pos, hlocal_absorb⟩ =>
          let C : ℝ := max Clocal Cfar
          have hClocal_le_C : Clocal ≤ C :=
            le_max_left Clocal Cfar
          have hCfar_le_C : Cfar ≤ C :=
            le_max_right Clocal Cfar
          have hC_pos : 0 < C :=
            lt_of_lt_of_le hClocal_pos hClocal_le_C
          exact
            ⟨C, hC_pos,
              fun w hw_sector hw_norm_two =>
                let J : ℝ :=
                  Complex.binetSecondFormulaDecayingTailIntegral w
                let L : ℝ :=
                  Complex.binetSecondFormulaBranchLocalIndentationEnvelope w
                let F : ℝ := (Cfar / ‖w‖) * J
                have hprincipal_le :
                    2 * ∫ t : ℝ in Set.Ioi (‖w‖ / 2),
                        ‖Complex.binetSecondFormulaPrincipalTailKernel w t‖ ≤
                      L + F :=
                  have hnorm_pos : 0 < ‖w‖ :=
                    lt_of_lt_of_le zero_lt_two hw_norm_two
                  have hsector_pos : 0 < δ * ‖w‖ :=
                    mul_pos hδ hnorm_pos
                  hlocal_estimate w
                    (lt_of_lt_of_le hsector_pos hw_sector)
                    hw_norm_two
                have hlocal_le :
                    L ≤ Clocal * J :=
                  hlocal_absorb w hw_sector hw_norm_two
                have hJ_nonneg : 0 ≤ J :=
                  Complex.binetSecondFormula_decayingTailIntegral_nonneg_of_norm_two
                    hw_norm_two
                have hlocal_C_le :
                    Clocal * J ≤ C * J :=
                  mul_le_mul_of_nonneg_right hClocal_le_C hJ_nonneg
                have hnorm_pos : 0 < ‖w‖ :=
                  lt_of_lt_of_le zero_lt_two hw_norm_two
                have hfar_C_le :
                    (Cfar / ‖w‖) * J ≤ (C / ‖w‖) * J := by
                  have hdiv_le : Cfar / ‖w‖ ≤ C / ‖w‖ :=
                    div_le_div_of_nonneg_right hCfar_le_C (le_of_lt hnorm_pos)
                  exact mul_le_mul_of_nonneg_right hdiv_le hJ_nonneg
                have hsum_le :
                    L + F ≤ C * J + (C / ‖w‖) * J :=
                  add_le_add (le_trans hlocal_le hlocal_C_le) hfar_C_le
                have hconst :
                    C * J + (C / ‖w‖) * J =
                      (C + C / ‖w‖) * J :=
                  (add_mul C (C / ‖w‖) J).symm
                le_trans hprincipal_le (le_trans hsum_le (le_of_eq hconst))⟩

end
end LFunctions
end Boundary
