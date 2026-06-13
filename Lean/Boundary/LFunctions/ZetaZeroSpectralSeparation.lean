import Boundary.LFunctions.ZetaZeroSideContribution
import Boundary.LFunctions.ZetaAdmissibleSpectralInterpolation

/-!
# Finite spectral separation on zero orbits

This file owns the finite spectral interpolation step used to separate an
off-critical completed-zero orbit by an admissible autocorrelation probe.
-/

namespace Boundary
namespace LFunctions

noncomputable section

/-- The finite spectral sample set attached to a centered zero orbit. -/
def zetaZeroOrbitSpectralSampleFinset (ρ : ℂ) : Finset ℂ :=
  (zetaZeroOrbitFinset ρ).image zetaCenteredZero

/-- Membership in the centered zero orbit gives membership of the centered coordinate in the
finite spectral sample set. -/
theorem zetaCenteredZero_mem_zeroOrbitSpectralSampleFinset
    (ρ η : ℂ) (hη : η ∈ zetaZeroOrbitFinset ρ) :
    zetaCenteredZero η ∈ zetaZeroOrbitSpectralSampleFinset ρ := by
  unfold zetaZeroOrbitSpectralSampleFinset
  exact Finset.mem_image.mpr ⟨η, hη, rfl⟩

/-- The finite spectral interpolation layer supplies an autocorrelation probe whose
spectral samples are one on the centered zero orbit. -/
theorem exists_zeroOrbit_autocorrelation_unitSpectralSamples
    (ρ : ℂ) :
    ∃ f : ZetaAdmissibleFunction,
      ∀ η : ℂ, η ∈ zetaZeroOrbitFinset ρ →
        zetaSpectralEval (ZetaAdmissibleFunction.convolutionAutocorrelation f)
          (zetaCenteredZero η) = 1 := by
  rcases
    ZetaAdmissibleFunction.exists_autocorrelation_spectralEval_one_on_finset
      (zetaZeroOrbitSpectralSampleFinset ρ) with
    ⟨f, hf⟩
  exact ⟨f, fun η hη =>
    hf (zetaCenteredZero η)
      (zetaCenteredZero_mem_zeroOrbitSpectralSampleFinset ρ η hη)⟩

/-- Unit spectral samples on an off-critical completed-zero orbit force the signed
multiplicity-weighted orbit contribution to be strictly negative. -/
theorem zetaZeroOrbitContributionRe_lt_zero_of_unitSpectralSamples
    (ρ : ℂ)
    (hρ : ZetaCompletedZero ρ)
    (hρre : ρ.re ≠ 0)
    (horbit : ∀ η : ℂ, η ∈ zetaZeroOrbitFinset ρ → ZetaCompletedZero η)
    (φ : ZetaAdmissibleFunction)
    (hsample :
      ∀ η : ℂ, η ∈ zetaZeroOrbitFinset ρ →
        zetaSpectralEval φ (zetaCenteredZero η) = 1) :
    zetaZeroOrbitContributionRe ρ φ < 0 := by
  sorry

/-- Finite spectral orbit separation at an off-critical centered completed zero.

The spectral interpolation layer supplies a seed whose completed autocorrelation
has a strictly negative signed multiplicity-weighted contribution on the
two-point centered zero orbit. -/
theorem exists_zeroOrbit_autocorrelation_finiteSpectralSeparator_owner
    (ρ : ℂ)
    (hρ : ZetaCompletedZero ρ)
    (hρre : ρ.re ≠ 0)
    (horbit : ∀ η : ℂ, η ∈ zetaZeroOrbitFinset ρ → ZetaCompletedZero η) :
    ∃ f : ZetaAdmissibleFunction,
      zetaZeroOrbitContributionRe ρ
          (ZetaAdmissibleFunction.convolutionAutocorrelation f) < 0 := by
  rcases exists_zeroOrbit_autocorrelation_unitSpectralSamples ρ with
    ⟨f, hsample⟩
  exact ⟨f,
    zetaZeroOrbitContributionRe_lt_zero_of_unitSpectralSamples
      ρ hρ hρre horbit
      (ZetaAdmissibleFunction.convolutionAutocorrelation f)
      hsample⟩

end

end LFunctions
end Boundary
