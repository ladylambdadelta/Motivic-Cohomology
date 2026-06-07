import Mathlib.Analysis.Fourier.AddCircle
import Mathlib.Analysis.MellinInversion
import Mathlib.NumberTheory.LSeries.RiemannZeta

/-!
# Boundary zeta transform calculus

This file exposes the classical Mellin/Fourier and zeta-normalization lemmas
that the explicit-formula route needs as upstream transform calculus.

The statements here are not the RH theorem itself. They are the precise
transform and normalization lemmas that later owner files will consume.
-/

namespace Boundary

open scoped FourierTransform
open Real Complex Set MeasureTheory
open AddCircle

noncomputable section

section Mellin

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- Boundary name for mathlib's Mellin/Fourier bridge. -/
theorem boundary_mellin_eq_fourierIntegral (f : ℝ → E) {s : ℂ} :
    mellin f s =
      𝓕 (fun (u : ℝ) ↦ (Real.exp (-s.re * u) • f (Real.exp (-u)))) (s.im / (2 * π)) := by
  exact mellin_eq_fourierIntegral (f := f) (s := s)

/-- Boundary name for the inverse Mellin/Fourier bridge. -/
theorem boundary_mellinInv_eq_fourierIntegralInv (σ : ℝ) (f : ℂ → E) {x : ℝ} (hx : 0 < x) :
    mellinInv σ f x =
      (x : ℂ) ^ (-σ : ℂ) • 𝓕⁻ (fun (y : ℝ) ↦ f (σ + 2 * π * y * I)) (-Real.log x) := by
  exact mellinInv_eq_fourierIntegralInv (σ := σ) (f := f) (x := x) hx

/-- Boundary name for Mellin inversion. -/
theorem boundary_mellin_inversion (σ : ℝ) (f : ℝ → E) {x : ℝ} (hx : 0 < x)
    [CompleteSpace E] (hf : MellinConvergent f σ) (hFf : Complex.VerticalIntegrable (mellin f) σ)
    (hfx : ContinuousAt f x) :
    mellinInv σ (mellin f) x = f x := by
  exact mellin_inversion (σ := σ) (f := f) (x := x) hx hf hFf hfx

end Mellin

section FourierInterval

theorem boundary_fourierCoeffOn_of_hasDerivAt {a b : ℝ} (hab : a < b) {f f' : ℝ → ℂ}
    {n : ℤ} (hn : n ≠ 0)
    (hf : ∀ x, x ∈ Set.uIcc a b → HasDerivAt f (f' x) x)
    (hf' : IntervalIntegrable f' volume a b) :
    fourierCoeffOn hab f n =
      1 / (-2 * π * I * n) *
        (fourier (-n) (a : AddCircle (b - a)) * (f b - f a) -
          (b - a) * fourierCoeffOn hab f' n) := by
  exact fourierCoeffOn_of_hasDerivAt (a := a) (b := b)
    (f := f) (f' := f') hab hn hf hf'

/-- Boundary name for the interval version of the Fourier derivative identity. -/
theorem boundary_fourierCoeffOn_of_hasDerivAt_Ioo {a b : ℝ} (hab : a < b) {f f' : ℝ → ℂ}
    {n : ℤ} (hn : n ≠ 0)
    (hf : ContinuousOn f (Set.uIcc a b))
    (hff' : ∀ x, x ∈ Set.Ioo (min a b) (max a b) → HasDerivAt f (f' x) x)
    (hf' : IntervalIntegrable f' volume a b) :
    fourierCoeffOn hab f n =
      1 / (-2 * π * I * n) *
        (fourier (-n) (a : AddCircle (b - a)) * (f b - f a) -
          (b - a) * fourierCoeffOn hab f' n) := by
  exact fourierCoeffOn_of_hasDerivAt_Ioo (a := a) (b := b)
    (f := f) (f' := f') hab hn hf hff' hf'

end FourierInterval

section Zeta

/-- Boundary name for the completed zeta decomposition. -/
theorem boundary_completedRiemannZeta_eq (s : ℂ) :
    completedRiemannZeta s = completedRiemannZeta₀ s - 1 / s - 1 / (1 - s) := by
  exact completedRiemannZeta_eq s

/-- Boundary name for the symmetry of the completed zeta function. -/
theorem boundary_completedRiemannZeta_one_sub (s : ℂ) :
    completedRiemannZeta (1 - s) = completedRiemannZeta s := by
  exact completedRiemannZeta_one_sub s

/-- Boundary name for zeta's functional equation identity in mathlib. -/
theorem boundary_riemannZeta_one_sub {s : ℂ} (hs : ∀ n : ℕ, s ≠ -n) (hs' : s ≠ 1) :
    riemannZeta (1 - s) = 2 * (2 * π) ^ (-s) * Gamma s * cos (π * s / 2) * riemannZeta s := by
  exact riemannZeta_one_sub (s := s) hs hs'

/-- Boundary name for the Dirichlet-series expansion of zeta. -/
theorem boundary_riemannZeta_eq_tsum_one_div_nat_cpow {s : ℂ} (hs : 1 < s.re) :
    riemannZeta s = ∑' n : ℕ, 1 / (n : ℂ) ^ s := by
  exact zeta_eq_tsum_one_div_nat_cpow (s := s) hs

end Zeta
