import Boundary.LFunctions.ZetaZeroTail

/-!
# Zero-tail localization

This file owns the localization step that keeps a fixed finite-orbit negative
margin while making the complementary zero-tail contribution arbitrarily small.
-/

namespace Boundary
namespace LFunctions

noncomputable section

/-- If two probes have the same spectral evaluation at one centered zero coordinate, then
their single zero-side contributions at that zero agree. -/
theorem zetaZeroSideContribution_eq_of_spectralEval_eq
    (η : ℂ) (φ ψ : ZetaAdmissibleFunction)
    (hsample :
      zetaSpectralEval φ (zetaCenteredZero η) =
        zetaSpectralEval ψ (zetaCenteredZero η)) :
    zetaZeroSideContribution η φ =
      zetaZeroSideContribution η ψ := by
  calc
    zetaZeroSideContribution η φ =
        - (zetaZeroMultiplicity η : ℂ) *
          zetaSpectralEval φ (zetaCenteredZero η) := by
      exact zetaZeroSideContribution_def η φ
    _ =
        - (zetaZeroMultiplicity η : ℂ) *
          zetaSpectralEval ψ (zetaCenteredZero η) := by
      exact congrArg
        (fun z : ℂ => - (zetaZeroMultiplicity η : ℂ) * z)
        hsample
    _ = zetaZeroSideContribution η ψ := by
      exact (zetaZeroSideContribution_def η ψ).symm

/-- If two probes have the same spectral evaluations on the centered zero orbit, then their
complex finite orbit contributions agree. -/
theorem zetaZeroOrbitContribution_eq_of_spectralEval_eq_on_orbit
    (ρ : ℂ) (φ ψ : ZetaAdmissibleFunction)
    (hsample :
      ∀ η : ℂ, η ∈ zetaZeroOrbitFinset ρ →
        zetaSpectralEval φ (zetaCenteredZero η) =
          zetaSpectralEval ψ (zetaCenteredZero η)) :
    zetaZeroOrbitContribution ρ φ =
      zetaZeroOrbitContribution ρ ψ := by
  unfold zetaZeroOrbitContribution
  exact Finset.sum_congr rfl
    (fun η hη =>
      zetaZeroSideContribution_eq_of_spectralEval_eq
        η φ ψ (hsample η hη))

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
  exact congrArg Complex.re
    (zetaZeroOrbitContribution_eq_of_spectralEval_eq_on_orbit
      ρ φ ψ hsample)

/-- The finite spectral sample set attached to a finite set of completed-zero coordinates. -/
def zetaZeroTailSpectralSampleFinset
    (S : Finset ℂ) : Finset ℂ :=
  S.image zetaCenteredZero

/-- A zero coordinate in the finite tail-exclusion set contributes its centered spectral
coordinate to the associated finite spectral sample set. -/
theorem zetaCenteredZero_mem_zeroTailSpectralSampleFinset
    (S : Finset ℂ) (η : ℂ) (hη : η ∈ S) :
    zetaCenteredZero η ∈ zetaZeroTailSpectralSampleFinset S := by
  unfold zetaZeroTailSpectralSampleFinset
  exact Finset.mem_image.mpr ⟨η, hη, rfl⟩

/-- Equality on the finite centered spectral sample set gives equality on the original
zero-coordinate sample set. -/
theorem zeroTailSpectralSample_eq_on_zeroSet_of_eq_on_sampleFinset
    (S : Finset ℂ) (φ ψ : ZetaAdmissibleFunction)
    (hsample :
      ∀ z : ℂ, z ∈ zetaZeroTailSpectralSampleFinset S →
        zetaSpectralEval φ z = zetaSpectralEval ψ z) :
    ∀ η : ℂ, η ∈ S →
      zetaSpectralEval φ (zetaCenteredZero η) =
        zetaSpectralEval ψ (zetaCenteredZero η) := by
  intro η hη
  exact hsample
    (zetaCenteredZero η)
    (zetaCenteredZero_mem_zeroTailSpectralSampleFinset S η hη)

/-- Finite spectral localization for the completed zero tail.

This is the genuine localization input: preserve the prescribed finite spectral
samples while driving the complementary completed-zero tail below an arbitrary
positive tolerance. -/
theorem exists_autocorrelation_zeroTail_small_preserving_spectralSampleFinset_owner
    (S : Finset ℂ)
    (P : Finset ℂ)
    (f₀ : ZetaAdmissibleFunction) :
    ∀ ε : ℝ, 0 < ε →
      ∃ f : ZetaAdmissibleFunction,
        (∀ z : ℂ, z ∈ P →
          zetaSpectralEval (ZetaAdmissibleFunction.convolutionAutocorrelation f)
              z =
            zetaSpectralEval (ZetaAdmissibleFunction.convolutionAutocorrelation f₀)
              z) ∧
          |Complex.re
            (zetaZeroTail S
              (ZetaAdmissibleFunction.convolutionAutocorrelation f))| < ε := by
  sorry

/-- Finite zero-set localization preserves each zero spectral sample while making the
complementary zero-side tail arbitrarily small. -/
theorem exists_autocorrelation_zeroTail_small_preserving_finiteSpectralSamples_owner
    (S : Finset ℂ)
    (f₀ : ZetaAdmissibleFunction) :
    ∀ ε : ℝ, 0 < ε →
      ∃ f : ZetaAdmissibleFunction,
        (∀ η : ℂ, η ∈ S →
          zetaSpectralEval (ZetaAdmissibleFunction.convolutionAutocorrelation f)
              (zetaCenteredZero η) =
            zetaSpectralEval (ZetaAdmissibleFunction.convolutionAutocorrelation f₀)
              (zetaCenteredZero η)) ∧
          |Complex.re
            (zetaZeroTail S
              (ZetaAdmissibleFunction.convolutionAutocorrelation f))| < ε := by
  intro ε hε
  rcases
    exists_autocorrelation_zeroTail_small_preserving_spectralSampleFinset_owner
      S (zetaZeroTailSpectralSampleFinset S) f₀ ε hε with
    ⟨f, hsample, htail⟩
  exact ⟨f,
    zeroTailSpectralSample_eq_on_zeroSet_of_eq_on_sampleFinset
      S
      (ZetaAdmissibleFunction.convolutionAutocorrelation f)
      (ZetaAdmissibleFunction.convolutionAutocorrelation f₀)
      hsample,
    htail⟩

/-- The real orbit remainder is the real part of the zero-tail outside the orbit. -/
theorem zetaZeroOrbitRemainderRe_eq_zeroTail_re
    (ρ : ℂ) (φ : ZetaAdmissibleFunction) :
    zetaZeroOrbitRemainderRe ρ φ =
      Complex.re (zetaZeroTail (zetaZeroOrbitFinset ρ) φ) := by
  rfl

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
  intro ε hε
  rcases
    exists_autocorrelation_zeroTail_small_preserving_finiteSpectralSamples_owner
      (zetaZeroOrbitFinset ρ) f₀ ε hε with
    ⟨f, hsample, htail⟩
  have htail_orbit :
      |
        zetaZeroOrbitRemainderRe ρ
          (ZetaAdmissibleFunction.convolutionAutocorrelation f)
      | < ε := by
    exact Eq.subst
      (motive := fun x : ℝ => |x| < ε)
      (zetaZeroOrbitRemainderRe_eq_zeroTail_re
        ρ (ZetaAdmissibleFunction.convolutionAutocorrelation f)).symm
      htail
  exact ⟨f, hsample, htail_orbit⟩

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

/-- Exact preservation of the finite orbit contribution transports a fixed negative
margin to the localized probe. -/
theorem zetaZeroOrbitContributionRe_le_margin_of_eq_reference
    (ρ : ℂ) (δ : ℝ)
    (f f₀ : ZetaAdmissibleFunction)
    (hcontribution :
      zetaZeroOrbitContributionRe ρ
          (ZetaAdmissibleFunction.convolutionAutocorrelation f) =
        zetaZeroOrbitContributionRe ρ
          (ZetaAdmissibleFunction.convolutionAutocorrelation f₀))
    (hmargin :
      zetaZeroOrbitContributionRe ρ
          (ZetaAdmissibleFunction.convolutionAutocorrelation f₀) ≤ -δ) :
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
    exact zetaZeroOrbitContributionRe_le_margin_of_eq_reference
      ρ δ f f₀ hcontribution hmargin
  exact ⟨f, hmargin_f, htail⟩

end

end LFunctions
end Boundary
