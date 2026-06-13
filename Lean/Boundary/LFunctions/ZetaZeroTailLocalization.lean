import Boundary.LFunctions.ZetaZeroTail

/-!
# Zero-tail localization

This file owns the localization step that keeps a fixed finite-orbit negative
margin while making the complementary zero-tail contribution arbitrarily small.
-/

namespace Boundary
namespace LFunctions

noncomputable section

/-- If two probes have the same spectral evaluations on the centered zero orbit, then their
finite orbit contributions agree. -/
theorem zetaZeroOrbitContributionRe_eq_of_spectralEval_eq_on_orbit
    (ρ : ℂ) (φ ψ : ZetaAdmissibleFunction)
    (hsample :
      ∀ η : ℂ, η ∈ zetaZeroOrbitFinset ρ →
        zetaSpectralEval φ (zetaCenteredZero η) =
          zetaSpectralEval ψ (zetaCenteredZero η)) :
    zetaZeroOrbitContributionRe ρ φ =
      zetaZeroOrbitContributionRe ρ ψ := by
  unfold zetaZeroOrbitContributionRe
  unfold zetaZeroOrbitContribution
  unfold zetaZeroSideContribution
  exact congrArg Complex.re
    (Finset.sum_congr rfl
      (fun η hη =>
        congrArg
          (fun z : ℂ => - (zetaZeroMultiplicity η : ℂ) * z)
          (hsample η hη)))

/-- Localizing around a finite orbit preserves every individual orbit spectral sample while
making the complementary orbit tail arbitrarily small. -/
theorem exists_zeroOrbit_autocorrelation_tail_small_preserving_orbitSpectralSamples_owner
    (ρ : ℂ)
    (f₀ : ZetaAdmissibleFunction) :
    ∀ ε : ℝ, 0 < ε →
      ∃ f : ZetaAdmissibleFunction,
        (∀ η : ℂ, η ∈ zetaZeroOrbitFinset ρ →
          zetaSpectralEval (ZetaAdmissibleFunction.convolutionAutocorrelation f)
              (zetaCenteredZero η) =
            zetaSpectralEval (ZetaAdmissibleFunction.convolutionAutocorrelation f₀)
              (zetaCenteredZero η)) ∧
          |
            zetaZeroOrbitRemainderRe ρ
              (ZetaAdmissibleFunction.convolutionAutocorrelation f)
          | < ε := by
  sorry

/-- Localizing around a finite orbit preserves its autocorrelation contribution exactly while
making the complementary orbit tail arbitrarily small. -/
theorem exists_zeroOrbit_autocorrelation_tail_small_preserving_orbitContribution_owner
    (ρ : ℂ)
    (f₀ : ZetaAdmissibleFunction) :
    ∀ ε : ℝ, 0 < ε →
      ∃ f : ZetaAdmissibleFunction,
        zetaZeroOrbitContributionRe ρ
            (ZetaAdmissibleFunction.convolutionAutocorrelation f) =
          zetaZeroOrbitContributionRe ρ
            (ZetaAdmissibleFunction.convolutionAutocorrelation f₀) ∧
          |
            zetaZeroOrbitRemainderRe ρ
              (ZetaAdmissibleFunction.convolutionAutocorrelation f)
          | < ε := by
  intro ε hε
  rcases
    exists_zeroOrbit_autocorrelation_tail_small_preserving_orbitSpectralSamples_owner
      ρ f₀ ε hε with
    ⟨f, hsample, htail⟩
  have hcontribution :
      zetaZeroOrbitContributionRe ρ
          (ZetaAdmissibleFunction.convolutionAutocorrelation f) =
        zetaZeroOrbitContributionRe ρ
          (ZetaAdmissibleFunction.convolutionAutocorrelation f₀) :=
    zetaZeroOrbitContributionRe_eq_of_spectralEval_eq_on_orbit
      ρ
      (ZetaAdmissibleFunction.convolutionAutocorrelation f)
      (ZetaAdmissibleFunction.convolutionAutocorrelation f₀)
      hsample
  exact ⟨f, hcontribution, htail⟩

/-- Localizing around a finite-orbit negative-margin autocorrelation probe
preserves that margin and makes the orbit remainder arbitrarily small. -/
theorem exists_zeroOrbit_autocorrelation_remainder_small_near_margin_probe_owner
    (ρ : ℂ)
    (δ : ℝ)
    (hδ : 0 < δ)
    (f₀ : ZetaAdmissibleFunction)
    (hmargin :
      zetaZeroOrbitContributionRe ρ
          (ZetaAdmissibleFunction.convolutionAutocorrelation f₀) ≤ -δ) :
    ∀ ε : ℝ, 0 < ε →
      ∃ f : ZetaAdmissibleFunction,
        zetaZeroOrbitContributionRe ρ
            (ZetaAdmissibleFunction.convolutionAutocorrelation f) ≤ -δ ∧
          |
            zetaZeroOrbitRemainderRe ρ
              (ZetaAdmissibleFunction.convolutionAutocorrelation f)
          | < ε := by
  intro ε hε
  rcases
    exists_zeroOrbit_autocorrelation_tail_small_preserving_orbitContribution_owner
      ρ f₀ ε hε with
    ⟨f, hcontribution, htail⟩
  have hmargin_f :
      zetaZeroOrbitContributionRe ρ
          (ZetaAdmissibleFunction.convolutionAutocorrelation f) ≤ -δ := by
    calc
      zetaZeroOrbitContributionRe ρ
          (ZetaAdmissibleFunction.convolutionAutocorrelation f) =
          zetaZeroOrbitContributionRe ρ
            (ZetaAdmissibleFunction.convolutionAutocorrelation f₀) := by
        exact hcontribution
      _ ≤ -δ := by
        exact hmargin
  exact ⟨f, hmargin_f, htail⟩

end

end LFunctions
end Boundary
