import Boundary.LFunctions.ZetaAdmissibleSpectralInterpolation
import Boundary.LFunctions.ZetaZeroTail

/-!
# Autocorrelation spectral localization

This file owns the Runge/Paley-Wiener spectral localization theorem for completed
autocorrelation probes. It is the point where finite spectral interpolation and
the completed zero-tail functional meet.
-/

namespace Boundary
namespace LFunctions

noncomputable section

namespace ZetaAdmissibleFunction

/-- Autocorrelation spectral localization with zero-tail control.

This is the analytic Runge/Paley-Wiener localization input: while preserving a
finite set of completed autocorrelation spectral samples, one can drive the real
part of the complementary completed zero-tail functional below any positive
tolerance. -/
theorem exists_autocorrelation_spectralEval_preserved_zeroTail_small_ownerRunge
    (S : Finset ℂ)
    (P : Finset ℂ)
    (f₀ : ZetaAdmissibleFunction) :
    ∀ ε : ℝ, 0 < ε →
      ∃ f : ZetaAdmissibleFunction,
        (∀ z : ℂ, z ∈ P →
          zetaSpectralEval (convolutionAutocorrelation f) z =
            zetaSpectralEval (convolutionAutocorrelation f₀) z) ∧
          |Complex.re
            (zetaZeroTail S (convolutionAutocorrelation f))| < ε := by
  sorry

end ZetaAdmissibleFunction

end
end LFunctions
end Boundary
