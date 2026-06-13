import Boundary.LFunctions.ZetaZeroSpectralSeparation

/-!
# Boundary zero-side orbit contribution

This file packages the orbit-level contribution as a consumer of the single
zero-side contribution definitions.
-/

namespace Boundary
namespace LFunctions

noncomputable section

/-- The orbit contribution is the finite sum over the reflection orbit. -/
theorem zetaZeroOrbitContribution_eq
    (ρ : ℂ) (φ : ZetaAdmissibleFunction) :
    zetaZeroOrbitContribution ρ φ =
      Finset.sum (zetaZeroOrbitFinset ρ) (fun η => zetaZeroSideContribution η φ) := by
  rfl

/-- The real-valued orbit contribution is the real part of the complex one. -/
theorem zetaZeroOrbitContributionRe_eq
    (ρ : ℂ) (φ : ZetaAdmissibleFunction) :
    zetaZeroOrbitContributionRe ρ φ =
      Complex.re (zetaZeroOrbitContribution ρ φ) := by
  rfl

/-- A strictly negative real value determines its own positive negative margin. -/
theorem exists_positive_margin_of_lt_zero
    {A : ℝ} (hA : A < 0) :
    ∃ δ : ℝ, 0 < δ ∧ A ≤ -δ := by
  exact ⟨-A, neg_pos.mpr hA, le_of_eq (neg_neg A).symm⟩

/-- Finite spectral orbit separation at an off-critical centered completed zero.

The autocorrelation/interpolation owner layer supplies a seed whose spectral samples on the
two-point centered zero orbit make the signed multiplicity-weighted orbit contribution
strictly negative. -/
theorem exists_zeroOrbit_autocorrelation_finiteSpectralSeparator
    (ρ : ℂ)
    (hρ : ZetaCompletedZero ρ)
    (hρre : ρ.re ≠ 0)
    (horbit : ∀ η : ℂ, η ∈ zetaZeroOrbitFinset ρ → ZetaCompletedZero η) :
    ∃ f : ZetaAdmissibleFunction,
      zetaZeroOrbitContributionRe ρ
          (ZetaAdmissibleFunction.convolutionAutocorrelation f) < 0 := by
  exact exists_zeroOrbit_autocorrelation_finiteSpectralSeparator_owner
    ρ hρ hρre horbit

/-- A strictly negative finite-orbit probe determines a positive finite-orbit margin. -/
theorem exists_zeroOrbit_autocorrelation_negative_margin_probe_of_negative_probe
    (ρ : ℂ)
    (hprobe :
      ∃ f : ZetaAdmissibleFunction,
        zetaZeroOrbitContributionRe ρ
            (ZetaAdmissibleFunction.convolutionAutocorrelation f) < 0) :
    ∃ δ : ℝ, 0 < δ ∧
      ∃ f : ZetaAdmissibleFunction,
        zetaZeroOrbitContributionRe ρ
            (ZetaAdmissibleFunction.convolutionAutocorrelation f) ≤ -δ := by
  rcases hprobe with ⟨f, hf⟩
  rcases exists_positive_margin_of_lt_zero hf with ⟨δ, hδ, hmargin⟩
  exact ⟨δ, hδ, f, hmargin⟩

/-- Off-critical completed zeros admit one autocorrelation probe with a fixed negative
finite-orbit margin. -/
theorem exists_zeroOrbit_autocorrelation_negative_margin_probe
    (ρ : ℂ)
    (hρ : ZetaCompletedZero ρ)
    (hρre : ρ.re ≠ 0)
    (horbit : ∀ η : ℂ, η ∈ zetaZeroOrbitFinset ρ → ZetaCompletedZero η) :
    ∃ δ : ℝ, 0 < δ ∧
      ∃ f : ZetaAdmissibleFunction,
        zetaZeroOrbitContributionRe ρ
            (ZetaAdmissibleFunction.convolutionAutocorrelation f) ≤ -δ := by
  exact exists_zeroOrbit_autocorrelation_negative_margin_probe_of_negative_probe
    ρ
    (exists_zeroOrbit_autocorrelation_finiteSpectralSeparator
      ρ hρ hρre horbit)

/-- A single finite-orbit negative-margin probe gives a constant negative-margin family. -/
theorem exists_zeroOrbit_autocorrelation_negative_margin_family_of_probe
    (ρ : ℂ)
    (δ : ℝ)
    (hprobe :
      ∃ f : ZetaAdmissibleFunction,
        zetaZeroOrbitContributionRe ρ
            (ZetaAdmissibleFunction.convolutionAutocorrelation f) ≤ -δ) :
    ∀ ε : ℝ, 0 < ε →
      ∃ f : ZetaAdmissibleFunction,
        zetaZeroOrbitContributionRe ρ
            (ZetaAdmissibleFunction.convolutionAutocorrelation f) ≤ -δ := by
  intro _ε _hε
  exact hprobe

/-- Off-critical completed zeros admit a fixed negative finite-orbit margin along a probe
family. -/
theorem exists_zeroOrbit_autocorrelation_negative_margin_family
    (ρ : ℂ)
    (hρ : ZetaCompletedZero ρ)
    (hρre : ρ.re ≠ 0)
    (horbit : ∀ η : ℂ, η ∈ zetaZeroOrbitFinset ρ → ZetaCompletedZero η) :
    ∃ δ : ℝ, 0 < δ ∧
      ∀ ε : ℝ, 0 < ε →
        ∃ f : ZetaAdmissibleFunction,
          zetaZeroOrbitContributionRe ρ
              (ZetaAdmissibleFunction.convolutionAutocorrelation f) ≤ -δ := by
  rcases
    exists_zeroOrbit_autocorrelation_negative_margin_probe ρ hρ hρre horbit with
    ⟨δ, hδ, hprobe⟩
  exact ⟨δ, hδ,
    exists_zeroOrbit_autocorrelation_negative_margin_family_of_probe
      ρ δ hprobe⟩

end
end LFunctions
end Boundary
