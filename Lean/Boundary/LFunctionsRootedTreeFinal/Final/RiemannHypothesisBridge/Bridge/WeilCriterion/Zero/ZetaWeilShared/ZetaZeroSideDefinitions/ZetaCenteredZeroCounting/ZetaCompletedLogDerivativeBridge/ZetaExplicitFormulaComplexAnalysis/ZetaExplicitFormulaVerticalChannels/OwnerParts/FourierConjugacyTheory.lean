import Mathlib.Analysis.Fourier.AddCircle

/-!
# Fourier Transform Conjugacy Theory

Establishes the fundamental conjugacy property of Fourier transforms:
the Fourier transform at opposite frequencies is the conjugate of the value.

This is the foundation for all Mellin-Fourier conjugacy results.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open Complex
open MeasureTheory
open scoped Topology

namespace FourierConjugacy

/-- At real frequencies, the Fourier transform kernel satisfies exponential conjugacy. -/
lemma fourierKernel_conjugacy (ξ : ℝ) (t : ℝ) :
    Complex.exp (2 * π * I * ((-ξ : ℝ) : ℂ) * t) =
    star (Complex.exp (-(2 * π * I * (ξ : ℝ) : ℂ) * t)) := by
  have h_neg : (2 * π * I * ((-ξ : ℝ) : ℂ) * t : ℂ) =
               -(2 * π * I * (ξ : ℝ) : ℂ) * t := by ring
  rw [h_neg]
  exact (Complex.exp_conj _).symm

/-- Fourier transform multiplication by kernel conjugacy. -/
lemma fourierIntegrand_conjugacy (φ : ℝ → ℂ) (ξ : ℝ) (t : ℝ) :
    φ t * Complex.exp (2 * π * I * ((-ξ : ℝ) : ℂ) * t) =
    star (φ t * Complex.exp (-(2 * π * I * (ξ : ℝ) : ℂ) * t)) := by
  have h_kernel := fourierKernel_conjugacy ξ t
  calc φ t * Complex.exp (2 * π * I * ((-ξ : ℝ) : ℂ) * t)
      = φ t * star (Complex.exp (-(2 * π * I * (ξ : ℝ) : ℂ) * t)) := by
          rw [h_kernel]
    _ = star (star (φ t) * star (Complex.exp (-(2 * π * I * (ξ : ℝ) : ℂ) * t))) := by
          rw [← star_star (φ t)]
          exact (star_mul _ _).symm
    _ = star (φ t * Complex.exp (-(2 * π * I * (ξ : ℝ) : ℂ) * t)) := by
          rw [star_mul]

/-- The Fourier integral decomposes under conjugacy at opposite frequencies. -/
theorem fourierIntegral_conjugacy (φ : ℝ → ℂ) (ξ : ℝ) :
    (∫ t : ℝ, φ t * Complex.exp (2 * π * I * ((-ξ : ℝ) : ℂ) * t) : ℂ) =
    star (∫ t : ℝ, φ t * Complex.exp (-(2 * π * I * (ξ : ℝ) : ℂ) * t)) := by
  have h_integrand : ∀ t : ℝ,
      φ t * Complex.exp (2 * π * I * ((-ξ : ℝ) : ℂ) * t) =
      star (φ t * Complex.exp (-(2 * π * I * (ξ : ℝ) : ℂ) * t)) :=
    fun t => fourierIntegrand_conjugacy φ ξ t

  calc (∫ t : ℝ, φ t * Complex.exp (2 * π * I * ((-ξ : ℝ) : ℂ) * t) : ℂ)
      = ∫ t : ℝ, star (φ t * Complex.exp (-(2 * π * I * (ξ : ℝ) : ℂ) * t)) := by
          apply integral_congr_ae
          exact Filter.Eventually.of_forall h_integrand
    _ = star (∫ t : ℝ, φ t * Complex.exp (-(2 * π * I * (ξ : ℝ) : ℂ) * t)) := by
          exact integral_conj

/-- Fourier transform conjugacy: F(-ξ) = conj(F(ξ)) -/
theorem fourierTransform_conjugacy (φ : ℝ → ℂ) (ξ : ℝ) :
    (𝓕 φ (-ξ : ℝ) : ℂ) = star (𝓕 φ ξ) := by
  show (∫ t : ℝ, φ t * Complex.exp (2 * π * I * ((-ξ : ℝ) : ℂ) * t) : ℂ) =
       star (∫ t : ℝ, φ t * Complex.exp (-(2 * π * I * (ξ : ℝ) : ℂ) * t))
  exact fourierIntegral_conjugacy φ ξ

end FourierConjugacy

end LFunctions
end Boundary
