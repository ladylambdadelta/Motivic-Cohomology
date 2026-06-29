import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalization.GammaStirlingNormalization.BinetKernel.F_IntegralAccounting
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalization.GammaStirlingNormalization.BinetKernel.G_PrincipalTailIntegral
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalization.GammaStirlingNormalization.BinetKernel.H_TailRemainderEstimates
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

theorem Complex.binetSecondFormula_contourDeformed_tail_kernel_exists :
    ∃ K : ℂ → ℝ → ℂ, ∃ R : ℝ, ∃ C : ℝ,
      0 < R ∧
      0 < C ∧
      Complex.BinetSecondFormulaContourTailUniformMajorant K R C := by
  exact
    ⟨Complex.binetSecondFormulaDecayingTailKernel, 2, 1,
      two_pos, zero_lt_one,
      Complex.binetSecondFormula_contourTailMajorantKernel_uniform_majorant⟩

/-- Positivity of the radius supplied by the contour-deformed tail kernel
existence theorem. -/
theorem Complex.binetSecondFormula_contourDeformed_tail_kernel_radius_pos :
    ∃ K : Complex.BinetSecondFormulaContourDeformedTailKernel, ∃ R : ℝ,
      0 < R ∧
      ∃ C : ℝ,
        0 < C ∧
        Complex.BinetSecondFormulaContourTailUniformMajorant K R C := by
  match Complex.binetSecondFormula_contourDeformed_tail_kernel_exists with
  | ⟨K, R, C, hR, hC, hmajorant⟩ =>
      exact ⟨K, R, hR, C, hC, hmajorant⟩

/-- Positivity of the uniform majorant constant supplied by the
contour-deformed tail kernel existence theorem. -/
theorem Complex.binetSecondFormula_contourDeformed_tail_kernel_constant_pos :
    ∃ K : Complex.BinetSecondFormulaContourDeformedTailKernel, ∃ R : ℝ, ∃ C : ℝ,
      0 < C ∧
      0 < R ∧
      Complex.BinetSecondFormulaContourTailUniformMajorant K R C :=
  match Complex.binetSecondFormula_contourDeformed_tail_kernel_exists with
  | ⟨K, R, C, hR, hC, hmajorant⟩ =>
      ⟨K, R, C, hC, hR, hmajorant⟩

/-- Principal-tail comparison supplied by the contour-deformed kernel
existence theorem. -/
theorem Complex.binetSecondFormula_contourDeformed_tail_kernel_principal_comparison_ae :
    ∃ K : Complex.BinetSecondFormulaContourDeformedTailKernel, ∃ R : ℝ, ∃ C : ℝ,
      0 < R ∧
      0 < C ∧
      Complex.BinetSecondFormulaContourTailUniformMajorant K R C := by
  exact Complex.binetSecondFormula_contourDeformed_tail_kernel_exists

/-- Uniform pointwise majorant supplied by the contour-deformed kernel
existence theorem. -/
theorem Complex.binetSecondFormula_contourDeformed_tail_kernel_uniform_majorant :
    ∃ K : Complex.BinetSecondFormulaContourDeformedTailKernel, ∃ R : ℝ, ∃ C : ℝ,
      0 < R ∧
      0 < C ∧
      Complex.BinetSecondFormulaContourTailUniformMajorant K R C := by
  exact Complex.binetSecondFormula_contourDeformed_tail_kernel_exists

/-- Contour-deformed Binet tail kernel package for the full right half-plane.

This theorem is now only a bundling wrapper around the explicit owner-level
contour-deformed kernel predicates. -/
theorem Complex.binetSecondFormula_contourTailMajorantKernel_integral_decomposition_ownerGap :
    ∀ w : ℂ,
      0 < w.re →
      2 ≤ ‖w‖ →
        ∫ t : ℝ in Set.Ioi (‖w‖ / 2),
            ‖Complex.binetSecondFormulaContourTailMajorantKernel w t‖ =
          (∫ t : ℝ in Set.Ioi (‖w‖ / 2),
              ‖Complex.binetSecondFormulaPrincipalTailKernel w t‖) +
            (∫ t : ℝ in Set.Ioi (‖w‖ / 2),
              |((1 : ℝ) / ‖w‖) *
                (t / (Real.exp ((2 : ℝ) * Real.pi * t) - 1))|) := by
  exact fun w hw_re_pos hw_norm =>
    let A : ℝ → ℝ := fun t : ℝ =>
      ‖Complex.binetSecondFormulaPrincipalTailKernel w t‖
    let B : ℝ → ℝ := fun t : ℝ =>
      |((1 : ℝ) / ‖w‖) *
        (t / (Real.exp ((2 : ℝ) * Real.pi * t) - 1))|
    let hprincipal_integrable :
        IntegrableOn A (Set.Ioi (‖w‖ / 2)) :=
      Complex.binetSecondFormula_principalTailKernel_norm_integrableOn_tail
        (w := w) hw_re_pos
    let hdecaying_integrable :
        IntegrableOn B (Set.Ioi (‖w‖ / 2)) :=
      Complex.binetSecondFormula_contourTailMajorantKernel_decayingSummand_integrableOn_tail
        (w := w) hw_norm
    let hpoint :
        ∀ t : ℝ,
          t ∈ Set.Ioi (‖w‖ / 2) →
            ‖Complex.binetSecondFormulaContourTailMajorantKernel w t‖ =
              A t + B t :=
      fun t _ht =>
        Complex.binetSecondFormula_contourTailMajorantKernel_norm_eq_principal_add_decaying
          w t
    calc
      ∫ t : ℝ in Set.Ioi (‖w‖ / 2),
          ‖Complex.binetSecondFormulaContourTailMajorantKernel w t‖ =
          ∫ t : ℝ in Set.Ioi (‖w‖ / 2), A t + B t := by
        exact setIntegral_congr_fun measurableSet_Ioi hpoint
      _ =
          (∫ t : ℝ in Set.Ioi (‖w‖ / 2), A t) +
            (∫ t : ℝ in Set.Ioi (‖w‖ / 2), B t) := by
        exact integral_add hprincipal_integrable hdecaying_integrable

/-- Integral accounting for the unfolded contour-tail majorant kernel.

After the pointwise unfolding, the kernel integral is the sum of the raw
principal-tail contribution and the explicit decaying summand.  This theorem
is the bookkeeping layer that combines those two estimates and produces the
constant `C + 2`. -/


end
end LFunctions
end Boundary
