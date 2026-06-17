import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaCompletedLogDerivativeControl.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalization.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.Owner
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
    (hz : centeredCompletedRiemannZeta z = 0) :
    ∀ᶠ w in 𝓝[≠] z, centeredCompletedRiemannZeta w ≠ 0 := by
  have hz' : completedRiemannZeta ((1 / 2 : ℂ) + z) = 0 := by
    exact by
      unfold centeredCompletedRiemannZeta at hz ⊢
      exact hz
  have hs0 : (1 / 2 : ℂ) + z ≠ 0 := by
    intro h
    have hz_eq : z = -(1 / 2 : ℂ) := by
      have hsum : (1 / 2 : ℂ) + z = (1 / 2 : ℂ) + (-(1 / 2 : ℂ)) := by
        calc
          (1 / 2 : ℂ) + z = 0 := h
          _ = (1 / 2 : ℂ) + (-(1 / 2 : ℂ)) := by norm_num
      exact add_left_cancel hsum
    exact hz0 hz_eq
  have hs1 : (1 / 2 : ℂ) + z ≠ 1 := by
    intro h
    have hz_eq : z = (1 / 2 : ℂ) := by
      have hsum : (1 / 2 : ℂ) + z = (1 / 2 : ℂ) + (1 / 2 : ℂ) := by
        calc
          (1 / 2 : ℂ) + z = 1 := h
          _ = (1 / 2 : ℂ) + (1 / 2 : ℂ) := by norm_num
      exact add_left_cancel hsum
    exact hz1 hz_eq
  have hzero :=
    completedRiemannZeta_eventually_ne_zero_of_zero ((1 / 2 : ℂ) + z) hs0 hs1 hz'
  have ht :
      Tendsto (fun w : ℂ => (1 / 2 : ℂ) + w) (𝓝[≠] z)
        (𝓝[≠] ((1 / 2 : ℂ) + z)) := by
    refine tendsto_nhdsWithin_iff.2 ?_
    refine ⟨
      ((continuous_const.add continuous_id).continuousAt.tendsto).mono_left nhdsWithin_le_nhds,
      ?_⟩
    exact Eventually.mono self_mem_nhdsWithin
      (fun w hw hsum => hw (add_left_cancel hsum))
  have hcomp := ht hzero
  exact by
    unfold centeredCompletedRiemannZeta
    exact hcomp

end ZetaAdmissibleFunction

end
end LFunctions
end Boundary
