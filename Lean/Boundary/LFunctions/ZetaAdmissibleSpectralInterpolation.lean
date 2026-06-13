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

/-- Spectral evaluation of a completed convolution-autocorrelation probe factors through the
seed transform and its dagger-reflected transform. -/
theorem zetaSpectralEval_convolutionAutocorrelation_eq_seed_daggerProduct
    (f : ZetaAdmissibleFunction) (z : ℂ) :
    zetaSpectralEval (convolutionAutocorrelation f) z =
      zetaSpectralEval f z * star (zetaSpectralEval f (-star z)) := by
  change
    Boundary.zetaLaplaceTransform
        (convolutionAutocorrelation f).toZetaTestFunction' z =
      Boundary.zetaLaplaceTransform f.toZetaTestFunction' z *
        star (Boundary.zetaLaplaceTransform f.toZetaTestFunction' (-star z))
  exact Boundary.zetaLaplaceTransform_convolutionAutocorrelation f z

/-- A finite set of spectral points admits a seed whose dagger-product spectral samples are
unit on that finite set. -/
theorem exists_seed_spectralEval_daggerProduct_one_on_finset
    (S : Finset ℂ) :
    ∃ f : ZetaAdmissibleFunction,
      ∀ z : ℂ, z ∈ S →
        zetaSpectralEval f z * star (zetaSpectralEval f (-star z)) = 1 := by
  sorry

/-- A finite set of spectral points admits a completed convolution-autocorrelation probe
with unit spectral samples on that finite set. -/
theorem exists_autocorrelation_spectralEval_one_on_finset
    (S : Finset ℂ) :
    ∃ f : ZetaAdmissibleFunction,
      ∀ z : ℂ, z ∈ S →
        zetaSpectralEval (convolutionAutocorrelation f) z = 1 := by
  rcases exists_seed_spectralEval_daggerProduct_one_on_finset S with
    ⟨f, hf⟩
  exact ⟨f, fun z hz =>
    (zetaSpectralEval_convolutionAutocorrelation_eq_seed_daggerProduct
      f z).trans
      (hf z hz)⟩

end ZetaAdmissibleFunction

end
end LFunctions
end Boundary
