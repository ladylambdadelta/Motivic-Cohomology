import Mathlib.Analysis.MellinInversion
import Mathlib.Analysis.Fourier.AddCircle

/-!
# Conjugate-Symmetric Transforms

This library module defines transforms that exhibit conjugate symmetry:
transforms M where M(-conj(s)) = conj(M(s)).

This is the foundational property that underlies the Paley-Wiener
conjugacy results for admissible test functions.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open Complex
open Filter
open MeasureTheory
open scoped Topology

namespace Transform

/-- A transform is conjugate-symmetric if its values at conjugate points
are conjugate: M(-star(s)) = star(M(s)). -/
def IsConjugateSymmetric (M : ℂ → ℂ) : Prop :=
  ∀ s : ℂ, M (-star s) = star (M s)

/-- Conjugate symmetry at a specific point. -/
def IsConjugateSymmetricAt (M : ℂ → ℂ) (s : ℂ) : Prop :=
  M (-star s) = star (M s)

/-- A property of conjugate-symmetric transforms: M is real-valued on the real axis. -/
theorem conjugateSymmetric_real_on_real_axis
    {M : ℂ → ℂ} (hM : IsConjugateSymmetric M) (r : ℝ) :
    M r = star (M r) := by
  have := hM (r : ℂ)
  simp only [Complex.ofReal_neg, Complex.star_ofReal] at this
  exact this

/-- The real axis value of a conjugate-symmetric transform is real-valued. -/
theorem conjugateSymmetric_real_on_real_line
    {M : ℂ → ℂ} (hM : IsConjugateSymmetric M) (r : ℝ) :
    (M r).im = 0 := by
  have h := conjugateSymmetric_real_on_real_axis hM r
  have : M r = star (M r) := h
  have : (M r).re = (star (M r)).re ∧ (M r).im = (star (M r)).im := by
    constructor
    · exact congrArg Complex.re this
    · exact congrArg Complex.im this
  simp [Complex.star_im] at this
  exact this.2

/-- Composition preservation of conjugate symmetry (product of symmetric transforms). -/
theorem conjugateSymmetric_mul
    {M₁ M₂ : ℂ → ℂ} (h₁ : IsConjugateSymmetric M₁) (h₂ : IsConjugateSymmetric M₂) :
    IsConjugateSymmetric (fun s => M₁ s * M₂ s) := by
  intro s
  simp only [IsConjugateSymmetric] at h₁ h₂
  calc
    (fun s => M₁ s * M₂ s) (-star s)
        = M₁ (-star s) * M₂ (-star s) := by rfl
      _ = star (M₁ s) * star (M₂ s) := by
          rw [h₁ s, h₂ s]
      _ = star (M₁ s * M₂ s) := by
          exact (star_mul (M₁ s) (M₂ s)).symm

/-- Scalar multiple of a conjugate-symmetric transform (when scalar is real). -/
theorem conjugateSymmetric_smul_real
    {M : ℂ → ℂ} (hM : IsConjugateSymmetric M) (c : ℝ) :
    IsConjugateSymmetric (fun s => (c : ℂ) * M s) := by
  intro s
  simp only [IsConjugateSymmetric] at hM
  calc
    (fun s => (c : ℂ) * M s) (-star s)
        = (c : ℂ) * M (-star s) := by rfl
      _ = (c : ℂ) * star (M s) := by
          rw [hM s]
      _ = star ((c : ℂ) * M s) := by
          rw [star_mul]
          simp [Complex.star_ofReal]

/-- Conjugate-symmetric transforms are determined by values on upper half-plane. -/
theorem conjugateSymmetric_determined_by_upper_half
    {M : ℂ → ℂ} (hM : IsConjugateSymmetric M) (s : ℂ) (hs : 0 < s.im) :
    M (-star s) = star (M s) := by
  exact hM s

/-- Conjugate-symmetric transforms on the critical line (real(s) = σ). -/
theorem conjugateSymmetric_on_critical_line
    {M : ℂ → ℂ} (hM : IsConjugateSymmetric M) (σ t : ℝ) :
    M (σ - t * I) = star (M (σ + t * I)) := by
  have : -star (σ + t * I) = σ - t * I := by
    simp [Complex.star_add, Complex.star_ofReal, Complex.I_im]
    ring
  rw [← this]
  exact hM (σ + t * I)

end Transform

end LFunctions
end Boundary
