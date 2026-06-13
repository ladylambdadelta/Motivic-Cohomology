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

/-- A finite set of spectral points admits a seed whose spectral transform is `1` both on
the sample set and on its dagger-reflected sample set.

This is the genuine finite Paley-Wiener interpolation input for the unit autocorrelation
probe.  The autocorrelation statement below is only algebra after this seed-level theorem. -/
theorem exists_seed_spectralEval_one_on_finset_and_reflection
    (S : Finset ℂ) :
    ∃ f : ZetaAdmissibleFunction,
      (∀ z : ℂ, z ∈ S → zetaSpectralEval f z = 1) ∧
        (∀ z : ℂ, z ∈ S → zetaSpectralEval f (-star z) = 1) := by
  sorry

/-- Unit seed values at a sample and its dagger-reflected sample give a unit dagger product
at the original sample. -/
theorem zetaSpectralEval_daggerProduct_eq_one_of_seed_and_reflection_one
    (f : ZetaAdmissibleFunction) (z : ℂ)
    (hleft : zetaSpectralEval f z = 1)
    (hright : zetaSpectralEval f (-star z) = 1) :
    zetaSpectralEval f z * star (zetaSpectralEval f (-star z)) = 1 := by
  calc
    zetaSpectralEval f z * star (zetaSpectralEval f (-star z)) =
        1 * star (zetaSpectralEval f (-star z)) := by
      exact congrArg
        (fun w : ℂ => w * star (zetaSpectralEval f (-star z)))
        hleft
    _ = 1 * star 1 := by
      exact congrArg
        (fun w : ℂ => 1 * star w)
        hright
    _ = 1 * 1 := by
      exact congrArg (fun w : ℂ => 1 * w) star_one
    _ = 1 := by
      exact one_mul 1

/-- A finite set of spectral points admits a seed whose dagger-product spectral samples are
unit on that finite set. -/
theorem exists_seed_spectralEval_daggerProduct_one_on_finset
    (S : Finset ℂ) :
    ∃ f : ZetaAdmissibleFunction,
      ∀ z : ℂ, z ∈ S →
        zetaSpectralEval f z * star (zetaSpectralEval f (-star z)) = 1 := by
  rcases exists_seed_spectralEval_one_on_finset_and_reflection S with
    ⟨f, hleft, hright⟩
  exact ⟨f, fun z hz =>
    zetaSpectralEval_daggerProduct_eq_one_of_seed_and_reflection_one
      f z (hleft z hz) (hright z hz)⟩

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
