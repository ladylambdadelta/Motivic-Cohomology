import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.OwnerParts.ForcedDaggerTailParts.Core

namespace Boundary
namespace LFunctions
noncomputable section
namespace ZetaAdmissibleFunction

/-- The finite-window tail theorem is the centered coordinate-transport theorem. -/
theorem autocorrelationSpectralEvalFiber_polynomialEnvelopeFiniteTailControl
    (S : Finset ℂ)
    (P : Finset ℂ)
    (f₀ : ZetaAdmissibleFunction)
    (ε : ℝ)
    (hε : 0 < ε)
    (T₀ : Finset ℂ)
    (hT₀ :
      ∀ ρ : ℂ, ρ ∈ T₀ →
        zetaCenteredZero ρ ∉ daggerClosedSpectralSampleFinset P)
    (A : ℝ)
    (k : ℕ)
    (hA : 0 ≤ A)
    (hsum :
      Summable
        (fun ρ : {ρ : ℂ // ZetaCompletedZero ρ} =>
          A * zetaCompletedZeroCenteredHeight ρ ^ (-(k + 3 : ℤ))))
    (hpositiveForced :
      ∀ f : ZetaAdmissibleFunction,
        f ∈ AutocorrelationSpectralEvalFiberOfShifted
          (translatedSpectralSampleFinset P (1 / 2 : ℝ))
          (1 / 2 : ℝ) f₀ →
          ∀ ρ : ℂ, ZetaCompletedZero ρ → ρ ∉ S →
            zetaCenteredZero ρ ∈ daggerClosedSpectralSampleFinset P →
              zetaCenteredZeroSideContribution ρ
                (convolutionAutocorrelationShifted (1 / 2 : ℝ) f) = 0)
    (hpositiveEnv :
      ∀ f : ZetaAdmissibleFunction,
        f ∈ AutocorrelationSpectralEvalFiberOfShifted
          (translatedSpectralSampleFinset P (1 / 2 : ℝ))
          (1 / 2 : ℝ) f₀ →
          (∀ ρ : ℂ, ρ ∈ T₀ →
            zetaSpectralEval (convolutionAutocorrelationShifted (1 / 2 : ℝ) f)
              (zetaCenteredZero ρ) = 0) →
          ∀ ρ : {ρ : ℂ // ZetaCompletedZero ρ ∧ ρ ∉ S ∧ ρ ∉ T₀},
            ‖zetaCenteredZeroSideContribution (ρ : ℂ)
                (convolutionAutocorrelationShifted (1 / 2 : ℝ) f)‖ ≤
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
                autocorrelationZeroTailRealAbs S f < ε :=
  autocorrelationSpectralEvalFiber_commonPolynomialEnvelope_forcedDaggerTailWindow_owner
    S P f₀ ε hε T₀ hT₀ A k hA hsum
      hpositiveForced hpositiveEnv

end ZetaAdmissibleFunction
end
end LFunctions
end Boundary
