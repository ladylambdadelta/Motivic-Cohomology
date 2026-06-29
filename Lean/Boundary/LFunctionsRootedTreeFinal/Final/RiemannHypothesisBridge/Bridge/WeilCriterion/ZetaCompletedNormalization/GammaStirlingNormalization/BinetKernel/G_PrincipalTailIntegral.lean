import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalization.GammaStirlingNormalization.BinetKernel.B_ExponentialDecay
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalization.GammaStirlingNormalization.BinetKernel.D_PointwiseMajorants
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalization.GammaStirlingNormalization.BinetKernel.E_EnvelopeBounds
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalization.GammaStirlingNormalization.BinetKernel.F_IntegralAccounting
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

theorem Complex.binetSecondFormula_contourTailMajorantKernel_norm_eq_principal_add_decaying
    (w : ℂ)
    (t : ℝ) :
    ‖Complex.binetSecondFormulaContourTailMajorantKernel w t‖ =
      ‖Complex.binetSecondFormulaPrincipalTailKernel w t‖ +
        |((1 : ℝ) / ‖w‖) *
          (t / (Real.exp ((2 : ℝ) * Real.pi * t) - 1))| := by
  let A : ℝ := ‖Complex.binetSecondFormulaPrincipalTailKernel w t‖
  let B : ℝ :=
    |((1 : ℝ) / ‖w‖) *
      (t / (Real.exp ((2 : ℝ) * Real.pi * t) - 1))|
  have hAB_nonneg : 0 ≤ A + B :=
    add_nonneg (norm_nonneg _) (abs_nonneg _)
  have hkernel :
      Complex.binetSecondFormulaContourTailMajorantKernel w t =
        ((A + B : ℝ) : ℂ) := by
    rfl
  calc
    ‖Complex.binetSecondFormulaContourTailMajorantKernel w t‖ =
        ‖((A + B : ℝ) : ℂ)‖ := by
      exact congrArg norm hkernel
    _ = |A + B| := Complex.norm_real (A + B)
    _ = A + B := abs_of_nonneg hAB_nonneg
    _ =
        ‖Complex.binetSecondFormulaPrincipalTailKernel w t‖ +
          |((1 : ℝ) / ‖w‖) *
            (t / (Real.exp ((2 : ℝ) * Real.pi * t) - 1))| := rfl

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
                  integral_nonneg_of_ae
                    ((ae_restrict_mem measurableSet_Ioi).mono
                      (fun t ht =>
                        Real.binetSecondFormula_kernel_majorant_nonneg_on_Ioi t
                          (lt_of_le_of_lt
                            (div_nonneg (norm_nonneg w) Real.zero_le_two_real)
                            ht)))
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
                      (C + C / ‖w‖) * J := by
                  calc
                    C * J + (C / ‖w‖) * J =
                        (C + C / ‖w‖) * J := by
                      exact (add_mul C (C / ‖w‖) J).symm
                le_trans hprincipal_le (le_trans hsum_le (le_of_eq hconst))⟩

/-- Tail absorption obtained from the legacy principal-tail norm estimate.

This theorem is a compatibility bridge: it shows that the older raw-norm
predicate is sufficient for the canonical contour-level tail-absorption target,
but the owner theorem no longer depends on proving the raw-norm predicate. -/


end
end LFunctions
end Boundary
