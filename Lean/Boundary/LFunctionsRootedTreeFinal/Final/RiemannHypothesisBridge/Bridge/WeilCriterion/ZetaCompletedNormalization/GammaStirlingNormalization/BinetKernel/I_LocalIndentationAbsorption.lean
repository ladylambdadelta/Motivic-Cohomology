import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalization.GammaStirlingNormalization.BinetKernel.E_EnvelopeBounds
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalization.GammaStirlingNormalization.BinetKernel.F_IntegralAccounting
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalization.GammaStirlingNormalization.BinetKernel.G_PrincipalTailIntegral

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

theorem Complex.binetSecondFormula_branchLocalIndentation_sectorAbsorption_owner :
    Complex.BinetSecondFormulaBranchLocalIndentationSectorAbsorption :=
  fun δ hδ =>
    match
      Complex.binetSecondFormula_branchLocalIndentation_sectorEnvelopeExpBound_owner
        δ hδ with
    | ⟨Cup, hCup_pos, hupper⟩ =>
        match Complex.binetSecondFormula_decayingTailIntegral_expLower_owner with
        | ⟨clow, hclow_pos, hlower⟩ =>
            let C : ℝ := Cup / clow
            have hC_pos : 0 < C :=
              div_pos hCup_pos hclow_pos
            have hC_nonneg : 0 ≤ C :=
              le_of_lt hC_pos
            ⟨C, hC_pos,
              fun w hw_sector hw_norm_two =>
                have htail_lower : clow * ‖w‖ *
                    Real.exp (-Real.pi * ‖w‖) ≤
                    Complex.binetSecondFormulaDecayingTailIntegral w :=
                  hlower w hw_norm_two
                have hscaled_tail :
                    C * (clow * ‖w‖ *
                        Real.exp (-Real.pi * ‖w‖)) ≤
                      C * Complex.binetSecondFormulaDecayingTailIntegral w :=
                  mul_le_mul_of_nonneg_left htail_lower hC_nonneg
                have hscale_identity :
                    Cup * ‖w‖ * Real.exp (-Real.pi * ‖w‖) =
                      C * (clow * ‖w‖ *
                        Real.exp (-Real.pi * ‖w‖)) := by
                  calc
                    Cup * ‖w‖ * Real.exp (-Real.pi * ‖w‖) =
                        ((Cup / clow) * clow) * ‖w‖ *
                          Real.exp (-Real.pi * ‖w‖) := by
                      exact
                        congrArg
                          (fun y : ℝ =>
                            y * ‖w‖ * Real.exp (-Real.pi * ‖w‖))
                          (div_mul_cancel₀ Cup (ne_of_gt hclow_pos)).symm
                    _ = C * (clow * ‖w‖) *
                        Real.exp (-Real.pi * ‖w‖) := by
                      exact
                        congrArg
                          (fun y : ℝ => y * Real.exp (-Real.pi * ‖w‖))
                          (mul_assoc C clow ‖w‖)
                    _ = C * (clow * ‖w‖ *
                        Real.exp (-Real.pi * ‖w‖)) := by
                      exact
                        mul_assoc C (clow * ‖w‖)
                          (Real.exp (-Real.pi * ‖w‖))
                le_trans
                  (hupper w hw_sector hw_norm_two)
                  (Eq.subst
                    (motive := fun y : ℝ =>
                      y ≤ C * Complex.binetSecondFormulaDecayingTailIntegral w)
                    hscale_identity.symm
                    hscaled_tail)⟩

/- Verification that Cfar ≤ 10 from explicit log evaluation.
Cfar comes from theorem binetSecondFormulaPrincipalTailKernel_norm_le_far_scaled_majorant,
where Cfar = max(|log(1/3)|, |log(3)|) + π.

Numerical verification:
- |log(3)| ≈ 1.0986 < 1.1
- |log(1/3)| = log(3) ≈ 1.0986 < 1.1
- π ≈ 3.14159 < 3.15
- max(1.1, 1.1) + 3.15 = 1.1 + 3.15 = 4.25 < 10 ✓
-/


end
end LFunctions
end Boundary
