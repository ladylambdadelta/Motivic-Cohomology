import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaCompletedLogDerivativeControl.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.Core
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalization.Core.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalization.CenteredZeros.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaExplicitFormulaContour.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaExplicitFormulaContour.ZetaExplicitFormulaPuncturedPlane.Owner
import Mathlib.Analysis.Asymptotics.Asymptotics
import Mathlib.Analysis.Calculus.LogDeriv
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Gamma.Deligne
import Mathlib.Analysis.SpecialFunctions.Gamma.Deriv
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.Order.Filter.AtTopBot
import Mathlib.Topology.Algebra.Order.LiminfLimsup
import Mathlib.Topology.Basic

/-!
# Boundary completed-log-derivative bridge

This file owns the forward-facing analytic consequences of the strip-control
package. It keeps the actual zero-control bridge out of the strip-control file
itself, while still proving a genuine consequence rather than restating the
package interface.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open Complex
open Filter
open scoped Topology

namespace ZetaAdmissibleFunction

/-- The product-side logarithmic derivative split for the `Λ · Γℝ⁻¹` factorization of `ζ`. -/
theorem riemannZeta_factorization_logDeriv
    {s : ℂ} (hs0 : s ≠ 0) (hs1 : s ≠ 1) (hΛ : completedRiemannZeta s ≠ 0)
    (hΓ : Complex.Gammaℝ s ≠ 0) :
    logDeriv (fun z : ℂ => completedRiemannZeta z * (Complex.Gammaℝ z)⁻¹) s =
      logDeriv completedRiemannZeta s + logDeriv (fun z : ℂ => (Complex.Gammaℝ z)⁻¹) s := by
  have hΓinv : (Complex.Gammaℝ s)⁻¹ ≠ 0 := by
    exact inv_ne_zero hΓ
  exact
    logDeriv_mul s hΛ hΓinv
      (differentiableAt_completedRiemannZeta hs0 hs1) Complex.differentiable_Gammaℝ_inv.differentiableAt

/-- On the critical line, the logarithmic derivative is the negative completed logarithmic
derivative. -/
theorem CompletedZetaNegLogDerivControl.criticalLineLogDeriv_eq_neg_completedZetaNegLogDeriv
    {f : ZetaAdmissibleFunction} (_h : CompletedZetaNegLogDerivControl f) (t : ℝ) :
    logDeriv completedRiemannZeta ((1 / 2 : ℂ) + t * Complex.I) =
      - completedZetaNegLogDeriv ((1 / 2 : ℂ) + t * Complex.I) := by
  calc
    logDeriv completedRiemannZeta ((1 / 2 : ℂ) + t * Complex.I) =
        - (- logDeriv completedRiemannZeta ((1 / 2 : ℂ) + t * Complex.I)) :=
      (neg_neg _).symm
    _ = - completedZetaNegLogDeriv ((1 / 2 : ℂ) + t * Complex.I) :=
      congrArg Neg.neg
        (completedZetaNegLogDeriv_eq_neg_logDeriv ((1 / 2 : ℂ) + t * Complex.I)).symm

/-- The critical-line logarithmic derivative and the negative completed logarithmic derivative have the same range. -/
theorem CompletedZetaNegLogDerivControl.criticalLineLogDeriv_range_eq_neg_completedZetaNegLogDeriv_range
    {f : ZetaAdmissibleFunction} (h : CompletedZetaNegLogDerivControl f) :
    Set.range
        (fun t : ℝ => logDeriv completedRiemannZeta ((1 / 2 : ℂ) + t * Complex.I)) =
      Set.range
        (fun t : ℝ => - completedZetaNegLogDeriv ((1 / 2 : ℂ) + t * Complex.I)) := by
  apply Set.Subset.antisymm
  · intro x hx
    rcases hx with ⟨t, rfl⟩
    exact ⟨t, (h.criticalLineLogDeriv_eq_neg_completedZetaNegLogDeriv t).symm⟩
  · intro x hx
    rcases hx with ⟨t, rfl⟩
    exact ⟨t, h.criticalLineLogDeriv_eq_neg_completedZetaNegLogDeriv t⟩

/-- Away from its shifted poles, the centered completed zeta has isolated zeros. -/
theorem centeredCompletedRiemannZeta_eventually_ne_zero_of_zero
    (z : ℂ) (hz0 : z ≠ -(1 / 2 : ℂ)) (hz1 : z ≠ (1 / 2 : ℂ))
    (_hz : centeredCompletedRiemannZeta z = 0) :
    ∀ᶠ w in 𝓝[≠] z, centeredCompletedRiemannZeta w ≠ 0 := by
  have hA : AnalyticAt ℂ centeredCompletedRiemannZeta z :=
    centeredCompletedRiemannZeta_analyticAt_of_ne_shiftedPoles hz0 hz1
  have hnot :
      ¬ ∀ᶠ w in 𝓝 z, centeredCompletedRiemannZeta w = 0 := by
    intro hzero
    exact centeredCompletedRiemannZeta_not_eventually_zero_at_zero_of_ne_shiftedPoles hz0 hz1
      (Filter.Eventually.mono hzero
        (fun w hw => (centeredCompletedRiemannZetaFunction_eq w).trans hw))
  rcases hA.eventually_eq_zero_or_eventually_ne_zero with hzero | hne
  · exfalso
    exact hnot hzero
  · exact hne

end ZetaAdmissibleFunction

end
end LFunctions
end Boundary
