import Mathlib.Analysis.MellinInversion
import Mathlib.Analysis.Fourier.AddCircle
import Mathlib.Analysis.Complex.Basic

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

/-- A conjugate-symmetric transform reflects negative real values to conjugates. -/
theorem conjugateSymmetric_neg_real_axis
    {M : ℂ → ℂ} (hM : IsConjugateSymmetric M) (r : ℝ) :
    M (-(r : ℂ)) = star (M (r : ℂ)) := by
  have hpoint : M (-star (r : ℂ)) = star (M (r : ℂ)) := hM (r : ℂ)
  have harg : -star (r : ℂ) = -(r : ℂ) :=
    congrArg Neg.neg (Complex.conj_ofReal r)
  exact Eq.subst
    (motive := fun z : ℂ => M z = star (M (r : ℂ)))
    harg
    hpoint

/-- The imaginary parts at opposite real inputs are negatives of each other. -/
theorem conjugateSymmetric_neg_real_axis_im
    {M : ℂ → ℂ} (hM : IsConjugateSymmetric M) (r : ℝ) :
    (M (-(r : ℂ))).im = -((M (r : ℂ)).im) := by
  have hvalue : M (-(r : ℂ)) = star (M (r : ℂ)) :=
    conjugateSymmetric_neg_real_axis hM r
  exact Eq.trans
    (congrArg Complex.im hvalue)
    (Complex.conj_im (M (r : ℂ)))

/-- Composition preservation of conjugate symmetry (product of symmetric transforms). -/
theorem conjugateSymmetric_mul
    {M₁ M₂ : ℂ → ℂ} (h₁ : IsConjugateSymmetric M₁) (h₂ : IsConjugateSymmetric M₂) :
    IsConjugateSymmetric (fun s => M₁ s * M₂ s) := by
  intro s
  calc
    (fun s => M₁ s * M₂ s) (-star s)
        = M₁ (-star s) * M₂ (-star s) := by
          exact Eq.refl _
      _ = star (M₁ s) * star (M₂ s) := by
          exact congrArg₂ HMul.hMul (h₁ s) (h₂ s)
      _ = star (M₁ s * M₂ s) := by
          exact Eq.trans
            (mul_comm (star (M₁ s)) (star (M₂ s)))
            (star_mul (M₁ s) (M₂ s)).symm

/-- Scalar multiple of a conjugate-symmetric transform (when scalar is real). -/
theorem conjugateSymmetric_smul_real
    {M : ℂ → ℂ} (hM : IsConjugateSymmetric M) (c : ℝ) :
    IsConjugateSymmetric (fun s => (c : ℂ) * M s) := by
  intro s
  calc
    (fun s => (c : ℂ) * M s) (-star s)
        = (c : ℂ) * M (-star s) := by
          exact Eq.refl _
      _ = (c : ℂ) * star (M s) := by
          exact congrArg (fun z : ℂ => (c : ℂ) * z) (hM s)
      _ = star ((c : ℂ) * M s) := by
          calc
            (c : ℂ) * star (M s) = star (M s) * (c : ℂ) := by
              exact mul_comm (c : ℂ) (star (M s))
            _ = star (M s) * star (c : ℂ) := by
              exact congrArg (fun z : ℂ => star (M s) * z)
                (Complex.conj_ofReal c).symm
            _ = star ((c : ℂ) * M s) := by
              exact (star_mul (c : ℂ) (M s)).symm

/-- Conjugate-symmetric transforms are determined by values on upper half-plane. -/
theorem conjugateSymmetric_determined_by_upper_half
    {M : ℂ → ℂ} (hM : IsConjugateSymmetric M) (s : ℂ) (_ : 0 < s.im) :
    M (-star s) = star (M s) := by
  exact hM s

/-- Conjugate-symmetric transforms on the line reflected by `s ↦ -star s`. -/
theorem conjugateSymmetric_on_reflected_vertical_line
    {M : ℂ → ℂ} (hM : IsConjugateSymmetric M) (σ t : ℝ) :
    M (-star ((σ : ℂ) + t * I)) = star (M ((σ : ℂ) + t * I)) := by
  exact hM ((σ : ℂ) + t * I)

end Transform

end LFunctions
end Boundary
