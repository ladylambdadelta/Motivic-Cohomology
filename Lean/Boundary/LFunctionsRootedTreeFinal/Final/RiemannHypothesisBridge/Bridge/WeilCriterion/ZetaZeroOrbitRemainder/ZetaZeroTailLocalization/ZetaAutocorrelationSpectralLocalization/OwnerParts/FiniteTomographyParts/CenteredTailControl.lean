import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.OwnerParts.FiniteTomographyParts.Part01_FiniteGeometry

namespace Boundary
namespace LFunctions
noncomputable section
namespace ZetaAdmissibleFunction

def AutocorrelationSpectralEvalFiberCenteredFiniteWindowTailControl
    (S : Finset ℂ)
    (P : Finset ℂ)
    (f₀ : ZetaAdmissibleFunction)
    (ε : ℝ)
    (T : Finset ℂ) : Prop :=
  (∀ ρ : ℂ, ρ ∈ T →
    ρ ∉ daggerClosedSpectralSampleFinset P) ∧
    ∀ f : ZetaAdmissibleFunction,
      f ∈ AutocorrelationSpectralEvalFiberOf P f₀ →
        (∀ ρ : ℂ, ρ ∈ T →
          zetaSpectralEval (convolutionAutocorrelation f)
            ρ = 0) →
          autocorrelationZeroTailRealAbs S f < ε

theorem autocorrelationSpectralEvalFiberCenteredFiniteWindowTailControl.elim
    (S : Finset ℂ)
    (P : Finset ℂ)
    (f₀ : ZetaAdmissibleFunction)
    (ε : ℝ)
    (T : Finset ℂ)
    (hT : AutocorrelationSpectralEvalFiberCenteredFiniteWindowTailControl S P f₀ ε T) :
    (∀ ρ : ℂ, ρ ∈ T →
      ρ ∉ daggerClosedSpectralSampleFinset P) ∧
      ∀ f : ZetaAdmissibleFunction,
        f ∈ AutocorrelationSpectralEvalFiberOf P f₀ →
          (∀ ρ : ℂ, ρ ∈ T →
            zetaSpectralEval (convolutionAutocorrelation f)
              ρ = 0) →
            autocorrelationZeroTailRealAbs S f < ε :=
  hT

theorem autocorrelationSpectralEvalFiberCenteredFiniteWindowTailControl.intro
    (S : Finset ℂ)
    (P : Finset ℂ)
    (f₀ : ZetaAdmissibleFunction)
    (ε : ℝ)
    (T : Finset ℂ)
    (hT : ∀ ρ : ℂ, ρ ∈ T →
      ρ ∉ daggerClosedSpectralSampleFinset P)
    (htail : ∀ f : ZetaAdmissibleFunction,
      f ∈ AutocorrelationSpectralEvalFiberOf P f₀ →
        (∀ ρ : ℂ, ρ ∈ T →
          zetaSpectralEval (convolutionAutocorrelation f)
            ρ = 0) →
          autocorrelationZeroTailRealAbs S f < ε) :
    AutocorrelationSpectralEvalFiberCenteredFiniteWindowTailControl S P f₀ ε T :=
  ⟨hT, htail⟩

def AutocorrelationSpectralEvalFiberCenteredFiniteWindowTailControlRunge : Prop :=
  ∀ S : Finset ℂ, ∀ P : Finset ℂ, ∀ f₀ : ZetaAdmissibleFunction,
    ∀ ε : ℝ, 0 < ε →
      ∃ T : Finset ℂ,
        AutocorrelationSpectralEvalFiberCenteredFiniteWindowTailControl S P f₀ ε T

def AutocorrelationSpectralEvalFiberCenteredSeparatedFiniteWindowTailControlRunge : Prop :=
  ∀ S : Finset ℂ, ∀ P : Finset ℂ, ∀ f₀ : ZetaAdmissibleFunction,
    (∀ ρ : ℂ,
      ZetaCompletedZero ρ →
        ρ ∉ S →
          ρ ∉ daggerClosedSpectralSampleFinset P) →
      ∀ ε : ℝ, 0 < ε →
        ∃ T : Finset ℂ,
          AutocorrelationSpectralEvalFiberCenteredFiniteWindowTailControl S P f₀ ε T

end ZetaAdmissibleFunction
end
end LFunctions
end Boundary
