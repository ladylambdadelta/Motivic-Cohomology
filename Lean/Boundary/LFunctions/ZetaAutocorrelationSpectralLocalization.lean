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
    SpectralSampleVector P :=
  fun z : P =>
    zetaSpectralEval (convolutionAutocorrelation f) (z : ℂ)

/-- The finite autocorrelation spectral-sample fiber over a target vector. -/
def AutocorrelationSampleFiber
    (P : Finset ℂ) (aP : SpectralSampleVector P) :
    Set ZetaAdmissibleFunction :=
  fun f : ZetaAdmissibleFunction =>
    autocorrelationSpectralFiniteSample P f = aP

/-- The finite autocorrelation spectral-sample fiber of a source probe. -/
def AutocorrelationSampleFiberOf
    (P : Finset ℂ) (f₀ : ZetaAdmissibleFunction) :
    Set ZetaAdmissibleFunction :=
  AutocorrelationSampleFiber P (autocorrelationSpectralFiniteSample P f₀)

/-- The absolute real completed zero-tail functional for an autocorrelation probe. -/
def autocorrelationZeroTailRealAbs
    (S : Finset ℂ) (f : ZetaAdmissibleFunction) : ℝ :=
  |Complex.re (zetaZeroTail S (convolutionAutocorrelation f))|

/-- Membership in the source fiber is exactly preservation of that source's finite
autocorrelation spectral-sample vector. -/
theorem mem_autocorrelationSampleFiberOf_iff
    (P : Finset ℂ) (f₀ f : ZetaAdmissibleFunction) :
    f ∈ AutocorrelationSampleFiberOf P f₀ ↔
      autocorrelationSpectralFiniteSample P f =
        autocorrelationSpectralFiniteSample P f₀ := by
  exact Iff.rfl

/-- Runge localization inside the finite autocorrelation spectral-sample fiber of a source,
stated against the named real zero-tail functional.

This is the true analytic Runge root in this lane: it does not prescribe an arbitrary
autocorrelation target vector. It stays inside the already-realized finite sample fiber of
`f₀` while shrinking the complementary zero-tail functional. -/
theorem exists_mem_autocorrelationSampleFiberOf_zeroTailRealAbs_small_ownerRunge
    (S : Finset ℂ)
    (P : Finset ℂ)
    (f₀ : ZetaAdmissibleFunction) :
    ∀ ε : ℝ, 0 < ε →
      ∃ f : ZetaAdmissibleFunction,
        f ∈ AutocorrelationSampleFiberOf P f₀ ∧
          autocorrelationZeroTailRealAbs S f < ε := by
  sorry

/-- Runge localization inside the finite autocorrelation spectral-sample fiber of a source. -/
theorem exists_mem_autocorrelationSampleFiberOf_zeroTail_small_ownerRunge
    (S : Finset ℂ)
    (P : Finset ℂ)
    (f₀ : ZetaAdmissibleFunction) :
    ∀ ε : ℝ, 0 < ε →
      ∃ f : ZetaAdmissibleFunction,
        f ∈ AutocorrelationSampleFiberOf P f₀ ∧
          |Complex.re
            (zetaZeroTail S (convolutionAutocorrelation f))| < ε := by
  intro ε hε
  rcases exists_mem_autocorrelationSampleFiberOf_zeroTailRealAbs_small_ownerRunge
      S P f₀ ε hε with
    ⟨f, hfFiber, hfTail⟩
  exact ⟨f, hfFiber, hfTail⟩

/-- Runge localization preserving the finite autocorrelation spectral-sample vector of a
given source. -/
theorem exists_autocorrelation_spectralFiniteSample_preserved_zeroTail_small_ownerRunge
    (S : Finset ℂ)
    (P : Finset ℂ)
    (f₀ : ZetaAdmissibleFunction) :
    ∀ ε : ℝ, 0 < ε →
      ∃ f : ZetaAdmissibleFunction,
        autocorrelationSpectralFiniteSample P f =
            autocorrelationSpectralFiniteSample P f₀ ∧
          |Complex.re
            (zetaZeroTail S (convolutionAutocorrelation f))| < ε := by
  intro ε hε
  rcases exists_mem_autocorrelationSampleFiberOf_zeroTail_small_ownerRunge
      S P f₀ ε hε with
    ⟨f, hfFiber, hfTail⟩
  exact ⟨f, hfFiber, hfTail⟩

/-- The canonical unit autocorrelation sample vector on a finite spectral sample set. -/
def autocorrelationSpectralFiniteUnitTarget
    (P : Finset ℂ) : SpectralSampleVector P :=
  fun _z : P => 1

/-- Membership in the unit autocorrelation sample fiber is exactly unit finite-sample
realization. -/
theorem mem_autocorrelationSampleFiber_unit_iff
    (P : Finset ℂ) (f : ZetaAdmissibleFunction) :
    f ∈ AutocorrelationSampleFiber P (autocorrelationSpectralFiniteUnitTarget P) ↔
      autocorrelationSpectralFiniteSample P f =
        autocorrelationSpectralFiniteUnitTarget P := by
  exact Iff.rfl

/-- The existing finite autocorrelation interpolation theorem realizes the unit finite
sample vector. -/
theorem exists_autocorrelation_spectralFiniteSample_eq_unitTarget
    (P : Finset ℂ) :
    ∃ f : ZetaAdmissibleFunction,
      autocorrelationSpectralFiniteSample P f =
        autocorrelationSpectralFiniteUnitTarget P := by
  rcases exists_autocorrelation_spectralEval_one_on_finset P with
    ⟨f, hf⟩
  exact ⟨f, by
    funext z
    exact hf (z : ℂ) z.property⟩

/-- The unit finite autocorrelation spectral-sample fiber is nonempty. -/
theorem exists_mem_autocorrelationSampleFiber_unit
    (P : Finset ℂ) :
    ∃ f : ZetaAdmissibleFunction,
      f ∈ AutocorrelationSampleFiber P (autocorrelationSpectralFiniteUnitTarget P) := by
  exact exists_autocorrelation_spectralFiniteSample_eq_unitTarget P

/-- Runge localization with the canonical unit finite autocorrelation spectral samples. -/
theorem exists_autocorrelation_spectralFiniteSample_unit_zeroTail_small_ownerRunge
    (S : Finset ℂ)
    (P : Finset ℂ) :
    ∀ ε : ℝ, 0 < ε →
      ∃ f : ZetaAdmissibleFunction,
        autocorrelationSpectralFiniteSample P f =
            autocorrelationSpectralFiniteUnitTarget P ∧
          |Complex.re
            (zetaZeroTail S (convolutionAutocorrelation f))| < ε := by
  rcases exists_mem_autocorrelationSampleFiber_unit P with
    ⟨f₀, hf₀⟩
  intro ε hε
  rcases exists_mem_autocorrelationSampleFiberOf_zeroTail_small_ownerRunge
      S P f₀ ε hε with
    ⟨f, hfSample, hfTail⟩
  exact ⟨f, hfSample.trans hf₀, hfTail⟩

/-- Pointwise form of Runge localization with unit finite autocorrelation spectral samples. -/
theorem exists_autocorrelation_spectralEval_unit_zeroTail_small_ownerRunge
    (S : Finset ℂ)
    (P : Finset ℂ) :
    ∀ ε : ℝ, 0 < ε →
      ∃ f : ZetaAdmissibleFunction,
        (∀ z : ℂ, z ∈ P →
          zetaSpectralEval (convolutionAutocorrelation f) z = 1) ∧
          |Complex.re
            (zetaZeroTail S (convolutionAutocorrelation f))| < ε := by
  intro ε hε
  rcases exists_autocorrelation_spectralFiniteSample_unit_zeroTail_small_ownerRunge
      S P ε hε with
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
  intro ε hε
  rcases exists_autocorrelation_spectralFiniteSample_preserved_zeroTail_small_ownerRunge
      S P f₀ ε hε with
    ⟨f, hfSample, hfTail⟩
  exact ⟨f, fun z hz => congrFun hfSample ⟨z, hz⟩, hfTail⟩

end ZetaAdmissibleFunction

end
end LFunctions
end Boundary
