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

/-- The finite autocorrelation spectral sample vector of an admissible seed. -/
def autocorrelationSpectralFiniteSample
    (P : Finset ℂ) (f : ZetaAdmissibleFunction) :
    P → ℂ :=
  fun z : P =>
    zetaSpectralEval (convolutionAutocorrelation f) (z : ℂ)

/-- The finite target vector induced by a function on the ambient spectral plane. -/
def autocorrelationSpectralFiniteTarget
    (P : Finset ℂ) (a : ℂ → ℂ) :
    P → ℂ :=
  fun z : P => a (z : ℂ)

/-- Runge/Paley-Wiener localization for finite autocorrelation spectral sample vectors,
with zero-tail control. -/
theorem exists_autocorrelation_spectralFiniteSample_zeroTail_small_ownerRunge
    (S : Finset ℂ)
    (P : Finset ℂ)
    (aP : P → ℂ) :
    ∀ ε : ℝ, 0 < ε →
      ∃ f : ZetaAdmissibleFunction,
        autocorrelationSpectralFiniteSample P f = aP ∧
          |Complex.re
            (zetaZeroTail S (convolutionAutocorrelation f))| < ε := by
  sorry

/-- Autocorrelation spectral localization with arbitrary finite prescribed samples and
zero-tail control. -/
theorem exists_autocorrelation_spectralEval_sample_zeroTail_small_ownerRunge
    (S : Finset ℂ)
    (P : Finset ℂ)
    (a : ℂ → ℂ) :
    ∀ ε : ℝ, 0 < ε →
      ∃ f : ZetaAdmissibleFunction,
        (∀ z : ℂ, z ∈ P →
          zetaSpectralEval (convolutionAutocorrelation f) z = a z) ∧
          |Complex.re
            (zetaZeroTail S (convolutionAutocorrelation f))| < ε := by
  intro ε hε
  rcases exists_autocorrelation_spectralFiniteSample_zeroTail_small_ownerRunge
      S P (autocorrelationSpectralFiniteTarget P a) ε hε with
    ⟨f, hfSample, hfTail⟩
  exact ⟨f, fun z hz => congrFun hfSample ⟨z, hz⟩, hfTail⟩

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
  exact exists_autocorrelation_spectralEval_sample_zeroTail_small_ownerRunge
    S P
    (fun z : ℂ => zetaSpectralEval (convolutionAutocorrelation f₀) z)

end ZetaAdmissibleFunction

end
end LFunctions
end Boundary
