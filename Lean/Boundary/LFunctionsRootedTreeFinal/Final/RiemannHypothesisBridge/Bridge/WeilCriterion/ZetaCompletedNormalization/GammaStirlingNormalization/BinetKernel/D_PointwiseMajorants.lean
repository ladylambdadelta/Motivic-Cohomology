import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalization.GammaStirlingNormalization.BinetKernel.B_ExponentialDecay
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalization.GammaStirlingNormalization.BinetKernel.C_ComplexLogBounds
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

theorem Complex.binetSecondFormula_arctan_kernel_norm_le_openRightHalfPlane
    {w : ℂ}
    (hw_re_pos : 0 < w.re) :
    ∀ t : ℝ,
      0 < t →
        ‖(t : ℂ) / w‖ ≤ (1 / 2 : ℝ) →
          ‖Complex.arctan ((t : ℂ) / w) /
              (Complex.exp (((2 : ℝ) * Real.pi * t : ℝ) : ℂ) - 1)‖ ≤
            2 * (t / ‖w‖) /
              (Real.exp ((2 : ℝ) * Real.pi * t) - 1) :=
  fun t ht hsmall =>
    Complex.binetSecondFormula_kernel_norm_le_of_small_argument
      (w := w) hw_re_pos ht hsmall

/-- Open-half-plane form of the Binet-kernel estimate kept under the historical
name used by downstream normalization code.

The literal principal-arctangent kernel has boundary singularities on the
imaginary axis, so this theorem requires `0 < w.re`. -/
theorem Complex.binetSecondFormula_arctan_kernel_norm_le_closedRightHalfPlane
    {w : ℂ}
    (hw_re_pos : 0 < w.re) :
    ∀ t : ℝ,
      0 < t →
        ‖(t : ℂ) / w‖ ≤ (1 / 2 : ℝ) →
          ‖Complex.arctan ((t : ℂ) / w) /
              (Complex.exp (((2 : ℝ) * Real.pi * t : ℝ) : ℂ) - 1)‖ ≤
            2 * (t / ‖w‖) /
              (Real.exp ((2 : ℝ) * Real.pi * t) - 1) := by
  exact Complex.binetSecondFormula_arctan_kernel_norm_le_openRightHalfPlane hw_re_pos

/-- Exponential tail integral bound for the scaled decay `exp (-π t)`.

The exact formula is
`∫ t in Ioi a, exp (-π t) = π⁻¹ * exp (-π a)`; this bound is the only
form needed for the Binet majorant tail estimate. -/
theorem Complex.binetSecondFormula_arctan_tail_contourDeformed_kernel_fullSector_package :
    ∃ K : ℂ → ℝ → ℂ, ∃ R : ℝ, ∃ C : ℝ,
      0 < R ∧
      0 < C ∧
      ∀ w : ℂ,
        0 < w.re →
        R ≤ ‖w‖ →
          ∀ᵐ t ∂volume.restrict (Set.Ioi (‖w‖ / 2)),
            ‖K w t‖ ≤
              (C / ‖w‖) *
                (t / (Real.exp ((2 : ℝ) * Real.pi * t) - 1)) := by
  exact
    ⟨Complex.binetSecondFormulaDecayingTailKernel, 2, 1,
      two_pos, zero_lt_one,
      fun w _hw hRle =>
        Complex.binetSecondFormula_decayingTailKernel_uniform_majorant
          w _hw hRle⟩

/-- Exact branch-coherence hypotheses required by the Binet owner theorem for
the Binet logarithm branch of `Gamma`.

This lives at the Binet-kernel owner level because normalized Stirling consumes
these hypotheses before the sectorial log-norm layer is imported. -/


end
end LFunctions
end Boundary
