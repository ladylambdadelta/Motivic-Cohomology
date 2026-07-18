import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.OwnerParts.CutoffData
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.OwnerParts.FiniteTomographyParts.CenteredTailControl

namespace Boundary
namespace LFunctions
noncomputable section
namespace ZetaAdmissibleFunction

/-- Direct finite-window selector for the already-centered completed-zero
coordinates used by the raw autocorrelation tail. -/
theorem autocorrelationSpectralEvalFiber_directCentered_forcedDaggerTailWindow
    (S P : Finset ℂ)
    (f₀ : ZetaAdmissibleFunction)
    (ε : ℝ)
    (hε : 0 < ε)
    (T₀ : Finset ℂ)
    (hT₀ : ∀ ρ : ℂ, ρ ∈ T₀ →
      zetaCenteredZero ρ ∉ daggerClosedSpectralSampleFinset P)
    (A : ℝ)
    (k : ℕ)
    (hA : 0 ≤ A)
    (hsum :
      Summable
        (fun ρ : {ρ : ℂ // ZetaCompletedZero ρ} =>
          A * zetaCompletedZeroCenteredHeight ρ ^ (-(k + 3 : ℤ))))
    (hforced :
      ∀ f : ZetaAdmissibleFunction,
        f ∈ AutocorrelationSpectralEvalFiberOf P f₀ →
          ∀ ρ : ℂ, ZetaCompletedZero ρ → ρ ∉ S →
            zetaCenteredZero ρ ∈ daggerClosedSpectralSampleFinset P →
              zetaZeroSideContribution ρ (convolutionAutocorrelation f) = 0)
    (henv :
      ∀ f : ZetaAdmissibleFunction,
        f ∈ AutocorrelationSpectralEvalFiberOf P f₀ →
          (∀ ρ : ℂ, ρ ∈ T₀ →
            zetaSpectralEval (convolutionAutocorrelation f) ρ = 0) →
          ∀ ρ : {ρ : ℂ // ZetaCompletedZero ρ ∧ ρ ∉ S ∧ ρ ∉ T₀},
            ‖zetaZeroSideContribution (ρ : ℂ)
                (convolutionAutocorrelation f)‖ ≤
              A * zetaCompletedZeroCenteredHeight
                (⟨(ρ : ℂ), ρ.2.1⟩ : {ρ : ℂ // ZetaCompletedZero ρ}) ^
                  (-(k + 3 : ℤ))) :
    ∃ T : Finset ℂ,
      T₀ ⊆ T ∧
        (∀ ρ : ℂ, ρ ∈ T →
          zetaCenteredZero ρ ∉ daggerClosedSpectralSampleFinset P) ∧
        ∀ f : ZetaAdmissibleFunction,
          f ∈ AutocorrelationSpectralEvalFiberOf P f₀ →
            (∀ ρ : ℂ, ρ ∈ T →
              zetaSpectralEval (convolutionAutocorrelation f) ρ = 0) →
              autocorrelationZeroTailRealAbs S f < ε := by
  match
      exists_commonPolynomialEnvelope_completedZeroTailCutoff_nonDagger_supported
        S P T₀ hT₀ ε hε A k hsum with
  | ⟨T, hT₀T, hT, htail⟩ =>
      exact
        ⟨T, hT₀T, hT,
          fun f hfFiber hfT =>
            autocorrelationZeroTailRealAbs_lt_of_zetaZeroTail_norm_lt
              S f ε
              (lt_of_le_of_lt
                (zetaZeroTail_norm_le_commonPolynomialEnvelope_nonDagger_complement_tsum
                  S P T A k hA hsum f
                  (zetaZeroSideContribution_eq_zero_of_window_spectralEval_zero
                    S T f hfT)
                  (fun ρ hρDagger =>
                    hforced f hfFiber (ρ : ℂ) ρ.2.1 ρ.2.2.1 hρDagger)
                  (fun ρ =>
                    henv f hfFiber
                      (autocorrelationSpectralEvalFiber_baseWindowVanishes_of_enlargedWindowVanishes
                        P T₀ T hT₀T f hfT)
                      (⟨(ρ : ℂ), ρ.2.1, ρ.2.2.1,
                        fun hρT₀ => ρ.2.2.2.1 (hT₀T hρT₀)⟩ :
                        {ρ : ℂ // ZetaCompletedZero ρ ∧ ρ ∉ S ∧ ρ ∉ T₀})))
                htail)⟩

end ZetaAdmissibleFunction
end
end LFunctions
end Boundary
