import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalization.GammaStirlingNormalization.BinetKernel.F_IntegralAccounting
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalization.GammaStirlingNormalization.BinetKernel.G_PrincipalTailIntegral
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalization.GammaStirlingNormalization.BinetKernel.H_TailRemainderEstimates

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

/-- The canonical decaying tail kernel carries the uniform full-sector
majorant used by contour-kernel assembly lemmas.

This theorem deliberately records only the majorant package.  It does not
assert an integral comparison from the principal branch tail to this decaying
kernel; that comparison is the separate analytic wall-cancellation input. -/
theorem Complex.binetSecondFormula_decaying_tail_kernel_uniform_majorant_package :
    ∃ K : ℂ → ℝ → ℂ, ∃ R : ℝ, ∃ C : ℝ,
      0 < R ∧
      0 < C ∧
      Complex.BinetSecondFormulaContourTailUniformMajorant K R C :=
  ⟨Complex.binetSecondFormulaDecayingTailKernel, 2, 1,
    two_pos, zero_lt_one,
    Complex.binetSecondFormula_contourTailMajorantKernel_uniform_majorant⟩

/-- Compatibility name for the decaying-kernel majorant package.

The package supplies a uniformly majorized kernel, not the missing principal
tail comparison to that kernel. -/
theorem Complex.binetSecondFormula_contourDeformed_tail_kernel_exists :
    ∃ K : ℂ → ℝ → ℂ, ∃ R : ℝ, ∃ C : ℝ,
      0 < R ∧
      0 < C ∧
      Complex.BinetSecondFormulaContourTailUniformMajorant K R C :=
  Complex.binetSecondFormula_decaying_tail_kernel_uniform_majorant_package

/-- The radius supplied by the decaying-kernel majorant package is positive. -/
theorem Complex.binetSecondFormula_contourDeformed_tail_kernel_radius_pos :
    ∃ K : Complex.BinetSecondFormulaContourDeformedTailKernel, ∃ R : ℝ,
      0 < R ∧
      ∃ C : ℝ,
        0 < C ∧
        Complex.BinetSecondFormulaContourTailUniformMajorant K R C := by
  match Complex.binetSecondFormula_contourDeformed_tail_kernel_exists with
  | ⟨K, R, C, hR, hC, hmajorant⟩ =>
      exact ⟨K, R, hR, C, hC, hmajorant⟩

/-- The uniform majorant constant supplied by the
decaying-kernel majorant package. -/
theorem Complex.binetSecondFormula_contourDeformed_tail_kernel_constant_pos :
    ∃ K : Complex.BinetSecondFormulaContourDeformedTailKernel, ∃ R : ℝ, ∃ C : ℝ,
      0 < C ∧
      0 < R ∧
      Complex.BinetSecondFormulaContourTailUniformMajorant K R C :=
  match Complex.binetSecondFormula_contourDeformed_tail_kernel_exists with
  | ⟨K, R, C, hR, hC, hmajorant⟩ =>
      ⟨K, R, C, hC, hR, hmajorant⟩

/-- Compatibility projection of the decaying-kernel majorant package.

Despite the historical name, this theorem does not supply a principal-tail
comparison; it only returns a kernel with its uniform majorant. -/
theorem Complex.binetSecondFormula_contourDeformed_tail_kernel_principal_comparison_ae :
    ∃ K : Complex.BinetSecondFormulaContourDeformedTailKernel, ∃ R : ℝ, ∃ C : ℝ,
      0 < R ∧
      0 < C ∧
      Complex.BinetSecondFormulaContourTailUniformMajorant K R C :=
  Complex.binetSecondFormula_contourDeformed_tail_kernel_exists

/-- Uniform pointwise majorant supplied by the decaying-kernel package. -/
theorem Complex.binetSecondFormula_contourDeformed_tail_kernel_uniform_majorant :
    ∃ K : Complex.BinetSecondFormulaContourDeformedTailKernel, ∃ R : ℝ, ∃ C : ℝ,
      0 < R ∧
      0 < C ∧
      Complex.BinetSecondFormulaContourTailUniformMajorant K R C :=
  Complex.binetSecondFormula_contourDeformed_tail_kernel_exists

end
end LFunctions
end Boundary
