import Boundary.LFunctions.ZetaZeroSideContribution
import Boundary.LFunctions.ZetaAdmissibleInterpolation

/-!
# Finite spectral separation on zero orbits

This file owns the finite spectral interpolation step used to separate an
off-critical completed-zero orbit by an admissible autocorrelation probe.
-/

namespace Boundary
namespace LFunctions

noncomputable section

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
  sorry

end

end LFunctions
end Boundary
