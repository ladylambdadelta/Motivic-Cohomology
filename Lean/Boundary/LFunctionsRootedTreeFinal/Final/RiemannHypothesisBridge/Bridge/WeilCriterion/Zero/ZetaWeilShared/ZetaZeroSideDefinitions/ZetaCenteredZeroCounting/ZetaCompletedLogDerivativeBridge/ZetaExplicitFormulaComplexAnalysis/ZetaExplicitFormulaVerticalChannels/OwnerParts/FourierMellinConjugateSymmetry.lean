import Mathlib.Analysis.MellinInversion
import Mathlib.Analysis.Fourier.AddCircle
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaTransformCalculus.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaExplicitFormulaVerticalChannels.OwnerParts.PrimeNaturalTimeArithmetic
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaExplicitFormulaVerticalChannels.OwnerParts.ConjugateSymmetricTransforms
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaExplicitFormulaVerticalChannels.OwnerParts.MellinConjugateLaws

/-!
# Fourier-Mellin Conjugate Symmetry Core

This file composes the four support libraries to prove that admissible functions
satisfy conjugate symmetry at opposite points.

The proof architecture:
1. ConjugateSymmetricTransforms - Define conjugate-symmetric transforms
2. MellinConjugateLaws - Record the Mellin-side conjugacy API

This file now contains only elementary Fourier/Mellin algebraic support lemmas.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open Complex
open Filter
open LSeries ArithmeticFunction
open MeasureTheory
open scoped ArithmeticFunction
open scoped Topology

namespace ZetaAdmissibleFunction

/-- RESEARCH LEMMA: ofReal preserves negation in complex numbers.
((-ξ : ℝ) : ℂ) = -(ξ : ℂ) for any ξ : ℝ. This is a coercion property. -/
lemma research_ofReal_preserves_neg (ξ : ℝ) :
    ((-ξ : ℝ) : ℂ) = -(ξ : ℂ) :=
  Complex.ofReal_neg ξ

/-- RESEARCH LEMMA: Multiplication with negation associates correctly.
In complex numbers: 2 * π * I * (-(ξ : ℂ)) * t = -(2 * π * I * (ξ : ℂ) * t).
This requires careful handling of multiplication associativity and negation. -/
lemma research_mult_neg_assoc (ξ t : ℂ) :
    2 * π * I * (-ξ) * t = -(2 * π * I * ξ * t) := by
  rw [mul_neg, mul_assoc]

/-- RESEARCH LEMMA: Negation distributes through ofReal multiplication.
-(2 * π * I * (ξ : ℝ) : ℂ) * t = -(2 * π * I * (ξ : ℂ) * t). -/
lemma research_neg_ofReal_mult (ξ t : ℂ) :
    -(2 * π * I * ((ξ : ℝ) : ℂ)) * t = -(2 * π * I * (ξ : ℂ) * t) :=
  rfl

/-- Step 1: Fourier transform conjugate symmetry.
For smooth integrable functions, the Fourier transform at opposite frequencies
satisfies: F(-ξ) = conj(F(ξ)).

This follows from:
1. Kernel conjugacy: exp(2πi(-ξ)t) = conj(exp(-2πiξt))
2. Integral conjugacy: ∫ conj(f) = conj(∫ f)
3. Composition: conj(F(ξ)) becomes F(-ξ) when conjugate passes through integral
-/
lemma fourierTransform_conjugate_symmetry
    (φ : ℝ → ℂ) (ξ : ℝ) (hφ : Integrable φ)
    (hφ_hat : Integrable (𝓕 φ)) :
    (𝓕 φ (-ξ : ℝ) : ℂ) = star (𝓕 φ ξ) := by
  -- Apply integral conjugacy to the Fourier transform definition
  have h_kernel : ∀ t : ℝ, Complex.exp (2 * π * I * ((-ξ : ℝ) : ℂ) * t) =
                           star (Complex.exp (-(2 * π * I * (ξ : ℝ) : ℂ) * t)) := by
    intro t
    have h_arg : (2 * π * I * ((-ξ : ℝ) : ℂ) * t : ℂ) = -(2 * π * I * (ξ : ℝ) : ℂ) * t := by
      have h1 : ((-ξ : ℝ) : ℂ) = -(ξ : ℂ) := research_ofReal_preserves_neg ξ
      calc (2 * π * I * ((-ξ : ℝ) : ℂ) * t : ℂ)
          = 2 * π * I * (-(ξ : ℂ)) * t := by exact congr_arg (fun x => 2 * π * I * x * t) h1
        _ = -(2 * π * I * (ξ : ℂ) * t) := research_mult_neg_assoc (ξ : ℂ) t
        _ = -(2 * π * I * (ξ : ℝ) : ℂ) * t := (research_neg_ofReal_mult (ξ : ℂ) t).symm
    rw [h_arg]
    exact (Complex.exp_conj _).symm

  -- The Fourier transform integrand at -ξ composed with conjugacy at ξ
  have h_integrand_conj : ∀ t : ℝ, φ t * Complex.exp (2 * π * I * ((-ξ : ℝ) : ℂ) * t) =
                                     star (φ t * Complex.exp (-(2 * π * I * (ξ : ℝ) : ℂ) * t)) := by
    intro t
    rw [h_kernel t]
    exact (star_mul _ _).symm

  -- Apply integral_conj via the integrand conjugacy
  calc (𝓕 φ (-ξ : ℝ) : ℂ)
      = ∫ t : ℝ, φ t * Complex.exp (2 * π * I * ((-ξ : ℝ) : ℂ) * t) := by rfl
    _ = ∫ t : ℝ, star (φ t * Complex.exp (-(2 * π * I * (ξ : ℝ) : ℂ) * t)) := by
        apply integral_congr_ae
        exact Filter.eventually_of_forall h_integrand_conj
    _ = star (∫ t : ℝ, φ t * Complex.exp (-(2 * π * I * (ξ : ℝ) : ℂ) * t)) := integral_conj.symm
    _ = star (𝓕 φ ξ) := by rfl

end ZetaAdmissibleFunction

end
end LFunctions
end Boundary
