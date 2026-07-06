import Mathlib.Analysis.Fourier.AddCircle
import Mathlib.Analysis.MellinInversion

/-!
# Fourier Transform Conjugacy Theory

Establishes the fundamental conjugacy property of Fourier transforms for
real-valued inputs: the Fourier transform at opposite frequencies is the
conjugate of the value.

This is the foundation for all Mellin-Fourier conjugacy results.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open Complex
open MeasureTheory
open scoped FourierTransform Real Topology

namespace FourierConjugacy

/-- The complex coefficient in the Fourier kernel is real after conjugating twice. -/
lemma two_pi_conj_fixed : star (2 * (Real.pi : ℂ)) = 2 * (Real.pi : ℂ) := by
  have hreal :
      star (((2 * Real.pi : ℝ) : ℂ)) =
        (((2 * Real.pi : ℝ) : ℂ)) :=
    Complex.conj_ofReal (2 * Real.pi)
  have hcast :
      (((2 * Real.pi : ℝ) : ℂ)) = 2 * (Real.pi : ℂ) :=
    Complex.ofReal_mul 2 Real.pi
  exact Eq.trans (congrArg star hcast.symm) (Eq.trans hreal hcast)

/-- The real scalar in the Fourier exponent changes sign at the opposite frequency. -/
lemma fourier_real_exponent_neg (ξ : ℝ) (t : ℝ) :
    -2 * Real.pi * t * (-ξ) = -(-2 * Real.pi * t * ξ) := by
  calc
    -2 * Real.pi * t * (-ξ) = (-2 * Real.pi * t) * (-ξ) := by
      exact Eq.refl ((-2 * Real.pi * t) * (-ξ))
    _ = -((-2 * Real.pi * t) * ξ) := by
      exact mul_neg (-2 * Real.pi * t) ξ
    _ = -(-2 * Real.pi * t * ξ) := by
      exact Eq.refl (-((-2 * Real.pi * t) * ξ))

/-- The canonical Fourier kernel exponent at `-ξ` is the conjugate exponent at `ξ`. -/
lemma fourierKernel_exponent_conjugacy (ξ : ℝ) (t : ℝ) :
    ((↑(-2 * Real.pi * t * (-ξ)) : ℂ) * Complex.I) =
      star (((↑(-2 * Real.pi * t * ξ) : ℂ) * Complex.I)) := by
  let A : ℝ := -2 * Real.pi * t * ξ
  have hneg : -2 * Real.pi * t * (-ξ) = -A := by
    show -2 * Real.pi * t * (-ξ) = -(-2 * Real.pi * t * ξ)
    exact fourier_real_exponent_neg ξ t
  have hcast_neg : ((↑(-A) : ℂ)) = -((A : ℂ)) :=
    map_neg (algebraMap ℝ ℂ) A
  have hA : star (A : ℂ) = (A : ℂ) := by
    exact Complex.conj_ofReal A
  have hI : star Complex.I = -Complex.I := by
    exact Complex.conj_I
  calc
    ((↑(-2 * Real.pi * t * (-ξ)) : ℂ) * Complex.I)
        = ((↑(-A) : ℂ) * Complex.I) := by
          exact congrArg (fun r : ℝ => ((r : ℂ) * Complex.I)) hneg
    _ = (-(A : ℂ)) * Complex.I := by
          exact congrArg (fun z : ℂ => z * Complex.I) hcast_neg
    _ = -((A : ℂ) * Complex.I) := by
          exact neg_mul (A : ℂ) Complex.I
    _ = (-Complex.I) * (A : ℂ) := by
          exact Eq.trans
            (congrArg Neg.neg (mul_comm (A : ℂ) Complex.I))
            (neg_mul Complex.I (A : ℂ)).symm
    _ = star ((A : ℂ) * Complex.I) := by
          exact (Eq.trans
            (star_mul (A : ℂ) Complex.I)
            (congrArg₂ HMul.hMul hI hA)).symm

/-- At real frequencies, the Fourier transform kernel satisfies exponential conjugacy. -/
lemma fourierKernel_conjugacy (ξ : ℝ) (t : ℝ) :
    Complex.exp ((↑(-2 * Real.pi * t * (-ξ)) : ℂ) * Complex.I) =
    star (Complex.exp ((↑(-2 * Real.pi * t * ξ) : ℂ) * Complex.I)) := by
  let b : ℂ := ((↑(-2 * Real.pi * t * ξ) : ℂ) * Complex.I)
  have h_arg :
      ((↑(-2 * Real.pi * t * (-ξ)) : ℂ) * Complex.I) =
        star b := by
    exact fourierKernel_exponent_conjugacy ξ t
  exact Eq.trans
    (congrArg Complex.exp h_arg)
    (Complex.exp_conj b)

/-- Fourier transform multiplication by kernel conjugacy. -/
lemma fourierIntegrand_conjugacy
    (φ : ℝ → ℂ) (hφ_real : ∀ t : ℝ, φ t = star (φ t)) (ξ : ℝ) (t : ℝ) :
    Complex.exp ((↑(-2 * Real.pi * t * (-ξ)) : ℂ) * Complex.I) * φ t =
    star (Complex.exp ((↑(-2 * Real.pi * t * ξ) : ℂ) * Complex.I) * φ t) := by
  have h_kernel := fourierKernel_conjugacy ξ t
  calc
    Complex.exp ((↑(-2 * Real.pi * t * (-ξ)) : ℂ) * Complex.I) * φ t
      = star (Complex.exp ((↑(-2 * Real.pi * t * ξ) : ℂ) * Complex.I)) * φ t := by
          exact congrArg (fun z : ℂ => z * φ t) h_kernel
    _ = star (Complex.exp ((↑(-2 * Real.pi * t * ξ) : ℂ) * Complex.I)) * star (φ t) := by
          exact congrArg
            (fun z : ℂ =>
              star (Complex.exp ((↑(-2 * Real.pi * t * ξ) : ℂ) * Complex.I)) * z)
            (hφ_real t)
    _ = star (φ t) * star (Complex.exp ((↑(-2 * Real.pi * t * ξ) : ℂ) * Complex.I)) := by
          exact mul_comm
            (star (Complex.exp ((↑(-2 * Real.pi * t * ξ) : ℂ) * Complex.I)))
            (star (φ t))
    _ = star (Complex.exp ((↑(-2 * Real.pi * t * ξ) : ℂ) * Complex.I) * φ t) := by
          exact (star_mul
            (Complex.exp ((↑(-2 * Real.pi * t * ξ) : ℂ) * Complex.I))
            (φ t)).symm

/-- The Fourier integral decomposes under conjugacy at opposite frequencies. -/
theorem fourierIntegral_conjugacy
    (φ : ℝ → ℂ) (hφ_real : ∀ t : ℝ, φ t = star (φ t)) (ξ : ℝ) :
    (∫ t : ℝ, Complex.exp ((↑(-2 * Real.pi * t * (-ξ)) : ℂ) * Complex.I) * φ t : ℂ) =
    star (∫ t : ℝ, Complex.exp ((↑(-2 * Real.pi * t * ξ) : ℂ) * Complex.I) * φ t) := by
  have h_integrand : ∀ t : ℝ,
      Complex.exp ((↑(-2 * Real.pi * t * (-ξ)) : ℂ) * Complex.I) * φ t =
      star (Complex.exp ((↑(-2 * Real.pi * t * ξ) : ℂ) * Complex.I) * φ t) :=
    fun t => fourierIntegrand_conjugacy φ hφ_real ξ t

  calc (∫ t : ℝ, Complex.exp ((↑(-2 * Real.pi * t * (-ξ)) : ℂ) * Complex.I) * φ t : ℂ)
      = ∫ t : ℝ, star (Complex.exp ((↑(-2 * Real.pi * t * ξ) : ℂ) * Complex.I) * φ t) := by
          exact integral_congr_ae (Filter.Eventually.of_forall h_integrand)
    _ = star (∫ t : ℝ, Complex.exp ((↑(-2 * Real.pi * t * ξ) : ℂ) * Complex.I) * φ t) := by
          exact integral_conj

/-- The complex scalar action in the Fourier kernel is multiplication. -/
lemma fourierKernel_smul_eq_mul (φ : ℝ → ℂ) (ξ : ℝ) (t : ℝ) :
    Complex.exp ((↑(-2 * Real.pi * t * ξ) : ℂ) * Complex.I) • φ t =
      Complex.exp ((↑(-2 * Real.pi * t * ξ) : ℂ) * Complex.I) * φ t := by
  exact Algebra.id.smul_eq_mul
    (Complex.exp ((↑(-2 * Real.pi * t * ξ) : ℂ) * Complex.I))
    (φ t)

/-- The Fourier kernel integral may be written with multiplication instead of scalar action. -/
lemma fourierKernel_integral_smul_eq_mul (φ : ℝ → ℂ) (ξ : ℝ) :
    (∫ t : ℝ,
      Complex.exp ((↑(-2 * Real.pi * t * ξ) : ℂ) * Complex.I) • φ t : ℂ) =
    ∫ t : ℝ,
      Complex.exp ((↑(-2 * Real.pi * t * ξ) : ℂ) * Complex.I) * φ t := by
  exact integral_congr_ae
    (Filter.Eventually.of_forall
      (fun t : ℝ => fourierKernel_smul_eq_mul φ ξ t))

/-- Fourier transform conjugacy for real-valued inputs: `F(-ξ) = conj(F(ξ))`. -/
theorem fourierTransform_conjugacy
    (φ : ℝ → ℂ) (hφ_real : ∀ t : ℝ, φ t = star (φ t)) (ξ : ℝ) :
    (𝓕 φ (-ξ : ℝ) : ℂ) = star (𝓕 φ ξ) := by
  have hleft :
      (𝓕 φ (-ξ : ℝ) : ℂ) =
        ∫ t : ℝ,
          Complex.exp ((↑(-2 * Real.pi * t * (-ξ : ℝ)) : ℂ) * Complex.I) • φ t :=
    Real.fourierIntegral_real_eq_integral_exp_smul φ (-ξ)
  have hright :
      (𝓕 φ ξ : ℂ) =
        ∫ t : ℝ,
          Complex.exp ((↑(-2 * Real.pi * t * ξ) : ℂ) * Complex.I) • φ t :=
    Real.fourierIntegral_real_eq_integral_exp_smul φ ξ
  have hleft_mul :
      (∫ t : ℝ,
          Complex.exp ((↑(-2 * Real.pi * t * (-ξ : ℝ)) : ℂ) * Complex.I) • φ t : ℂ) =
        ∫ t : ℝ,
          Complex.exp ((↑(-2 * Real.pi * t * (-ξ : ℝ)) : ℂ) * Complex.I) * φ t :=
    fourierKernel_integral_smul_eq_mul φ (-ξ)
  have hright_star :
      star (∫ t : ℝ,
          Complex.exp ((↑(-2 * Real.pi * t * ξ) : ℂ) * Complex.I) * φ t) =
        star (𝓕 φ ξ) := by
    exact congrArg star
      ((Eq.trans hright (fourierKernel_integral_smul_eq_mul φ ξ)).symm)
  exact Eq.trans hleft
    (Eq.trans
      hleft_mul
      (Eq.trans
        (fourierIntegral_conjugacy φ hφ_real ξ)
        hright_star))

end FourierConjugacy
