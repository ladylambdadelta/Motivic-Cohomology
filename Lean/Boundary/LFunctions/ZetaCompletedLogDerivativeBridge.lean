import Boundary.LFunctions.ZetaCompletedLogDerivativeControl
import Boundary.LFunctions.ZetaExplicitFormulaComplexAnalysis
import Mathlib.Analysis.Asymptotics.Asymptotics

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

namespace ZetaAdmissibleFunction

/-- The product-side logarithmic derivative split for the `Λ · Γℝ⁻¹` factorization of `ζ`. -/
theorem riemannZeta_factorization_logDeriv
    {s : ℂ} (hs0 : s ≠ 0) (hs1 : s ≠ 1) (hΛ : completedRiemannZeta s ≠ 0)
    (hΓ : Gammaℝ s ≠ 0) :
    logDeriv (fun z : ℂ => completedRiemannZeta z * (Gammaℝ z)⁻¹) s =
      logDeriv completedRiemannZeta s + logDeriv (fun z : ℂ => (Gammaℝ z)⁻¹) s := by
  rw [logDeriv_mul s hΛ (by simpa using inv_ne_zero hΓ)
      (differentiableAt_completedZeta hs0 hs1) differentiable_Gammaℝ_inv.differentiableAt]

/-- A critical-line bound for the logarithmic derivative of the completed zeta function. -/
theorem CompletedZetaNegLogDerivControl.criticalLineLogDerivBound
    {f : ZetaAdmissibleFunction} (h : CompletedZetaNegLogDerivControl f)
    (N : ℕ) :
    ∃ C : ℝ,
      0 < C ∧
      ∀ t : ℝ,
        ‖logDeriv completedRiemannZeta ((1 / 2 : ℂ) + t * Complex.I)‖
          ≤ C * (1 + ‖t‖) ^ (-(N : ℤ)) := by
  rcases h.criticalLineBound N with ⟨C, hC, hbound⟩
  refine ⟨C, hC, ?_⟩
  intro t
  have hspec :
      completedZetaNegLogDeriv ((1 / 2 : ℂ) + t * Complex.I) =
        - logDeriv completedRiemannZeta ((1 / 2 : ℂ) + t * Complex.I) := by
    exact completedZetaNegLogDeriv_eq_neg_logDeriv ((1 / 2 : ℂ) + t * Complex.I)
  have hnorm : ‖- logDeriv completedRiemannZeta ((1 / 2 : ℂ) + t * Complex.I)‖ =
      ‖logDeriv completedRiemannZeta ((1 / 2 : ℂ) + t * Complex.I)‖ := by
    simp
  rw [← hspec, hnorm]
  exact hbound t

/-- The completed zeta logarithmic derivative decays to `0` on the critical line. -/
theorem CompletedZetaNegLogDerivControl.criticalLineLogDerivTendstoZero
    {f : ZetaAdmissibleFunction} (h : CompletedZetaNegLogDerivControl f) :
    Tendsto
      (fun t : ℝ => logDeriv completedRiemannZeta ((1 / 2 : ℂ) + t * Complex.I))
      atTop
      (𝓝 (0 : ℝ)) := by
  rcases h.criticalLineLogDerivBound 1 with ⟨C, hC, hbound⟩
  have hpow :
      Tendsto (fun t : ℝ => (1 + ‖t‖) ^ (-(1 : ℤ))) atTop (𝓝 (0 : ℝ)) := by
    simpa using tendsto_one_add_norm_pow_neg_atTop 1
  have hmul :
      Tendsto (fun t : ℝ => C * (1 + ‖t‖) ^ (-(1 : ℤ))) atTop (𝓝 (0 : ℝ)) := by
    simpa using hpow.const_mul C
  have hnorm :
      Tendsto
        (fun t : ℝ => ‖logDeriv completedRiemannZeta ((1 / 2 : ℂ) + t * Complex.I)‖)
        atTop
        (𝓝 (0 : ℝ)) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hmul ?_ ?_
    · exact Eventually.of_forall fun _ => norm_nonneg _
    · exact Eventually.of_forall hbound
  simpa [tendsto_zero_iff_norm_tendsto_zero] using hnorm

/-- The completed negative logarithmic derivative itself tends to `0` on the critical line. -/
theorem CompletedZetaNegLogDerivControl.criticalLineNegLogDerivTendstoZero
    {f : ZetaAdmissibleFunction} (h : CompletedZetaNegLogDerivControl f) :
    Tendsto
      (fun t : ℝ => completedZetaNegLogDeriv ((1 / 2 : ℂ) + t * Complex.I))
      atTop
      (𝓝 (0 : ℂ)) := by
  have hlog := h.criticalLineLogDerivTendstoZero
  have hrewrite :
      (fun t : ℝ => completedZetaNegLogDeriv ((1 / 2 : ℂ) + t * Complex.I)) =
        fun t : ℝ => - logDeriv completedRiemannZeta ((1 / 2 : ℂ) + t * Complex.I) := by
    funext t
    rw [completedZetaNegLogDeriv_eq_neg_logDeriv]
  rw [hrewrite]
  exact hlog.neg

/-- The critical-line negative logarithmic derivative is little-o of `1`. -/
theorem CompletedZetaNegLogDerivControl.criticalLineNegLogDerivIsLittleOOne
    {f : ZetaAdmissibleFunction} (h : CompletedZetaNegLogDerivControl f) :
    (fun t : ℝ => completedZetaNegLogDeriv ((1 / 2 : ℂ) + t * Complex.I)) =o[atTop]
      (fun _ : ℝ => (1 : ℂ)) := by
  rw [Asymptotics.isLittleO_one_iff]
  exact h.criticalLineNegLogDerivTendstoZero

/-- The completed zeta logarithmic derivative is little-o of `1` on the critical line. -/
theorem CompletedZetaNegLogDerivControl.criticalLineLogDerivIsLittleOOne
    {f : ZetaAdmissibleFunction} (h : CompletedZetaNegLogDerivControl f) :
    (fun t : ℝ => logDeriv completedRiemannZeta ((1 / 2 : ℂ) + t * Complex.I)) =o[atTop]
      (fun _ : ℝ => (1 : ℂ)) := by
  rw [Asymptotics.isLittleO_one_iff]
  exact h.criticalLineLogDerivTendstoZero

/-- The completed zeta logarithmic derivative is bounded on the critical line. -/
theorem CompletedZetaNegLogDerivControl.criticalLineLogDerivIsBigOOne
    {f : ZetaAdmissibleFunction} (h : CompletedZetaNegLogDerivControl f) :
    (fun t : ℝ => logDeriv completedRiemannZeta ((1 / 2 : ℂ) + t * Complex.I)) =O[atTop]
      (fun _ : ℝ => (1 : ℂ)) := by
  exact h.criticalLineLogDerivIsLittleOOne.isBigO

/-- The completed negative logarithmic derivative is bounded on the critical line. -/
theorem CompletedZetaNegLogDerivControl.criticalLineNegLogDerivIsBigOOne
    {f : ZetaAdmissibleFunction} (h : CompletedZetaNegLogDerivControl f) :
    (fun t : ℝ => completedZetaNegLogDeriv ((1 / 2 : ℂ) + t * Complex.I)) =O[atTop]
      (fun _ : ℝ => (1 : ℂ)) := by
  exact h.criticalLineNegLogDerivIsLittleOOne.isBigO

/-- The norm of the critical-line logarithmic derivative is eventually bounded. -/
theorem CompletedZetaNegLogDerivControl.criticalLineLogDerivEventuallyBounded
    {f : ZetaAdmissibleFunction} (h : CompletedZetaNegLogDerivControl f) :
    IsBoundedUnder (· ≤ ·) atTop
      (fun t : ℝ => ‖logDeriv completedRiemannZeta ((1 / 2 : ℂ) + t * Complex.I)‖) := by
  rw [← isBigO_one_iff]
  exact h.criticalLineLogDerivIsBigOOne

/-- The range of the critical-line logarithmic derivative norm is bounded above. -/
theorem CompletedZetaNegLogDerivControl.criticalLineLogDerivRange_bddAbove
    {f : ZetaAdmissibleFunction} (h : CompletedZetaNegLogDerivControl f) :
    BddAbove
      (Set.range
        (fun t : ℝ => ‖logDeriv completedRiemannZeta ((1 / 2 : ℂ) + t * Complex.I)‖)) := by
  exact (h.criticalLineLogDerivEventuallyBounded.bddAbove_range)

/-- The range of the critical-line completed negative logarithmic derivative norm is bounded above. -/
theorem CompletedZetaNegLogDerivControl.criticalLineNegLogDerivRange_bddAbove
    {f : ZetaAdmissibleFunction} (h : CompletedZetaNegLogDerivControl f) :
    BddAbove
      (Set.range
        (fun t : ℝ => ‖completedZetaNegLogDeriv ((1 / 2 : ℂ) + t * Complex.I)‖)) := by
  exact (h.criticalLineNegLogDerivIsBigOOne.bddAbove_range)

/-- The critical-line logarithmic derivative admits a global uniform bound. -/
theorem CompletedZetaNegLogDerivControl.criticalLineLogDerivUniformBound
    {f : ZetaAdmissibleFunction} (h : CompletedZetaNegLogDerivControl f) :
    ∃ C : ℝ, 0 < C ∧
      ∀ t : ℝ, ‖logDeriv completedRiemannZeta ((1 / 2 : ℂ) + t * Complex.I)‖ ≤ C := by
  rcases h.criticalLineLogDerivRange_bddAbove with ⟨C, hC⟩
  refine ⟨max C 1, by positivity, ?_⟩
  intro t
  have hmem : ‖logDeriv completedRiemannZeta ((1 / 2 : ℂ) + t * Complex.I)‖ ∈
      Set.range (fun t : ℝ => ‖logDeriv completedRiemannZeta ((1 / 2 : ℂ) + t * Complex.I)‖) := by
    exact ⟨t, rfl⟩
  have hle : ‖logDeriv completedRiemannZeta ((1 / 2 : ℂ) + t * Complex.I)‖ ≤ C := by
    exact hC hmem
  linarith

/-- The critical-line completed negative logarithmic derivative admits a global uniform bound. -/
theorem CompletedZetaNegLogDerivControl.criticalLineNegLogDerivUniformBound
    {f : ZetaAdmissibleFunction} (h : CompletedZetaNegLogDerivControl f) :
    ∃ C : ℝ, 0 < C ∧
      ∀ t : ℝ, ‖completedZetaNegLogDeriv ((1 / 2 : ℂ) + t * Complex.I)‖ ≤ C := by
  rcases h.criticalLineNegLogDerivRange_bddAbove with ⟨C, hC⟩
  refine ⟨max C 1, by positivity, ?_⟩
  intro t
  have hmem : ‖completedZetaNegLogDeriv ((1 / 2 : ℂ) + t * Complex.I)‖ ∈
      Set.range (fun t : ℝ => ‖completedZetaNegLogDeriv ((1 / 2 : ℂ) + t * Complex.I)‖) := by
    exact ⟨t, rfl⟩
  have hle : ‖completedZetaNegLogDeriv ((1 / 2 : ℂ) + t * Complex.I)‖ ≤ C := by
    exact hC hmem
  linarith

/-- The critical-line completed negative logarithmic derivative admits a global uniform bound. -/
theorem CompletedZetaNegLogDerivControl.criticalLineNegLogDerivSup_le
    {f : ZetaAdmissibleFunction} (h : CompletedZetaNegLogDerivControl f) :
    ∃ C : ℝ, 0 < C ∧
      ∀ t : ℝ, ‖completedZetaNegLogDeriv ((1 / 2 : ℂ) + t * Complex.I)‖ ≤ C := by
  exact h.criticalLineNegLogDerivUniformBound

/-- The critical-line completed negative logarithmic derivative has bounded range. -/
theorem CompletedZetaNegLogDerivControl.criticalLineNegLogDeriv_range_bounded
    {f : ZetaAdmissibleFunction} (h : CompletedZetaNegLogDerivControl f) :
    Bornology.IsBounded
      (Set.range
        (fun t : ℝ => completedZetaNegLogDeriv ((1 / 2 : ℂ) + t * Complex.I))) := by
  rcases h.criticalLineNegLogDerivUniformBound with ⟨C, hC, hbound⟩
  refine (Metric.isBounded_range_iff).2 ?_
  refine ⟨2 * C, ?_⟩
  intro x hx y hy
  rcases hx with ⟨t, rfl⟩
  rcases hy with ⟨u, rfl⟩
  calc
    dist (completedZetaNegLogDeriv ((1 / 2 : ℂ) + t * Complex.I))
        (completedZetaNegLogDeriv ((1 / 2 : ℂ) + u * Complex.I))
        ≤ ‖completedZetaNegLogDeriv ((1 / 2 : ℂ) + t * Complex.I)‖ +
            ‖completedZetaNegLogDeriv ((1 / 2 : ℂ) + u * Complex.I)‖ := by
            simpa [dist_eq_norm] using norm_sub_le
    _ ≤ C + C := by gcongr <;> exact hbound _
    _ = 2 * C := by ring

/-- The critical-line logarithmic derivative has bounded range. -/
theorem CompletedZetaNegLogDerivControl.criticalLineLogDeriv_range_bounded
    {f : ZetaAdmissibleFunction} (h : CompletedZetaNegLogDerivControl f) :
    Bornology.IsBounded
      (Set.range
        (fun t : ℝ => logDeriv completedRiemannZeta ((1 / 2 : ℂ) + t * Complex.I))) := by
  have h' := h.criticalLineNegLogDeriv_range_bounded
  simpa [completedZetaNegLogDeriv_eq_neg_logDeriv] using h'

/-- The critical-line logarithmic derivative has bounded range as a complex set. -/
theorem CompletedZetaNegLogDerivControl.criticalLineLogDeriv_range_bounded_complex
    {f : ZetaAdmissibleFunction} (h : CompletedZetaNegLogDerivControl f) :
    Bornology.IsBounded
      (Set.range
        (fun t : ℝ => logDeriv completedRiemannZeta ((1 / 2 : ℂ) + t * Complex.I))) := by
  exact h.criticalLineLogDeriv_range_bounded

/-- Away from its shifted poles, the centered completed zeta has isolated zeros. -/
theorem centeredCompletedRiemannZeta_eventually_ne_zero_of_zero
    (z : ℂ) (hz0 : z ≠ -(1 / 2 : ℂ)) (hz1 : z ≠ (1 / 2 : ℂ))
    (hz : centeredCompletedRiemannZeta z = 0) :
    ∀ᶠ w in 𝓝[≠] z, centeredCompletedRiemannZeta w ≠ 0 := by
  have hz' : completedRiemannZeta ((1 / 2 : ℂ) + z) = 0 := by
    simpa [centeredCompletedRiemannZeta, add_comm, add_left_comm, add_assoc] using hz
  have hs0 : (1 / 2 : ℂ) + z ≠ 0 := by
    intro h
    apply hz0
    linarith
  have hs1 : (1 / 2 : ℂ) + z ≠ 1 := by
    intro h
    apply hz1
    linarith
  have hzero :=
    completedRiemannZeta_eventually_ne_zero_of_zero ((1 / 2 : ℂ) + z) hs0 hs1 hz'
  have ht :
      Tendsto (fun w : ℂ => (1 / 2 : ℂ) + w) (𝓝[≠] z)
        (𝓝[≠] ((1 / 2 : ℂ) + z)) := by
    simpa using ((Homeomorph.addLeft (1 / 2 : ℂ)).continuous.tendsto)
  have hcomp := hzero.comp ht
  simpa [centeredCompletedRiemannZeta, add_comm, add_left_comm, add_assoc] using hcomp

end ZetaAdmissibleFunction

end
end LFunctions
end Boundary
