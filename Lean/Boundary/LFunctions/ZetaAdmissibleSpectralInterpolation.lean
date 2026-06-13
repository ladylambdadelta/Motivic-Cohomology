import Boundary.LFunctions.ZetaAdmissibleInterpolation
import Boundary.LFunctions.ZetaZeroSideDefinitions

/-!
# Admissible spectral interpolation

This file owns finite interpolation for spectral evaluations of completed
autocorrelation probes.  It sits above the physical interpolation package and
the zero-side spectral-evaluation definitions.
-/

namespace Boundary
namespace LFunctions

noncomputable section

namespace ZetaAdmissibleFunction

/-- Finite spectral samples can be realized by completed convolution-autocorrelation probes.

This is the spectral interpolation theorem needed by zero-orbit separation: it interpolates
the Laplace/spectral evaluation of the completed autocorrelation probe, not the pointwise
physical values of the seed. -/
theorem exists_autocorrelation_spectralEval_sample_on_finset
    (S : Finset ℂ) (a : ℂ → ℂ) :
    ∃ f : ZetaAdmissibleFunction,
      ∀ z : ℂ, z ∈ S →
        zetaSpectralEval (convolutionAutocorrelation f) z = a z := by
  sorry

/-- A finite set of spectral points admits a completed convolution-autocorrelation probe
with unit spectral samples on that finite set. -/
theorem exists_autocorrelation_spectralEval_one_on_finset
    (S : Finset ℂ) :
    ∃ f : ZetaAdmissibleFunction,
      ∀ z : ℂ, z ∈ S →
        zetaSpectralEval (convolutionAutocorrelation f) z = 1 := by
  exact exists_autocorrelation_spectralEval_sample_on_finset
    S (fun _z : ℂ => 1)

end ZetaAdmissibleFunction

end
end LFunctions
end Boundary
