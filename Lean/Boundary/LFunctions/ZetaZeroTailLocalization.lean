import Boundary.LFunctions.ZetaZeroTail

/-!
# Zero-tail localization

This file owns the localization step that keeps a fixed finite-orbit negative
margin while making the complementary zero-tail contribution arbitrarily small.
-/

namespace Boundary
namespace LFunctions

noncomputable section

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
  sorry

end

end LFunctions
end Boundary
