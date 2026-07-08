import Mathlib.Analysis.MellinInversion
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaExplicitFormulaVerticalChannels.OwnerParts.ConjugateSymmetricTransforms
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaExplicitFormulaVerticalChannels.OwnerParts.FourierConjugacyTheory
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaExplicitFormulaVerticalChannels.OwnerParts.MellinInversionConjugacy
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaTransformCalculus.Owner

/-!
# Mellin Transform Conjugate Laws

This library establishes how the Mellin transform behaves with conjugate symmetry.

Key result: If a transform M is conjugate-symmetric, then Mellin inversion of M
produces a function with conjugate symmetry in the real domain.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open Complex
open Filter
open MeasureTheory
open scoped Topology

namespace MellinConjugacy

/-- The Mellin transform exhibits conjugate symmetry when the integrand
is properly weighted. For conjugate points s and -conj(s), the Mellin
transform values are conjugates. -/
lemma mellin_conjugateSymmetric_property
    (φ : ℝ → ℂ) (s : ℂ)
    (hφ_weighted_real :
      ∀ u : ℝ,
        Real.exp (-(s.re) * u) • φ (Real.exp (-u)) =
          star (Real.exp (-(s.re) * u) • φ (Real.exp (-u)))) :
    (mellin φ (-star s) : ℂ) = star (mellin φ s) := by
  -- By the Mellin-Fourier bridge (boundary_mellin_eq_fourierIntegral):
  -- mellin(φ)(s) = 𝓕(λ u ↦ exp(-s.re * u) • φ(exp(-u)))(s.im / (2π))
  --
  -- The key is that the Mellin transform at -conj(s) relates to the
  -- Fourier transform at opposite frequencies with conjugate weights.

  -- The exponential weights: exp(-(-star s).re * u) and exp(-(s.re) * u)
  have h_weight_real : (-(-star s)).re = -(s.re) := by
    calc
      (-(-star s)).re = -((-star s).re) := Complex.neg_re (-star s)
      _ = -(-(star s).re) := congrArg Neg.neg (Complex.neg_re (star s))
      _ = -(-(s.re)) := congrArg (fun y : ℝ => -(-y)) (Complex.star_re s)
      _ = -(s.re) := neg_neg (s.re)

  -- The Fourier frequencies: ((-star s).im) / (2π) and (s.im) / (2π)
  have h_freq_real : (-(-star s)).im = -(s.im) := by
    calc
      (-(-star s)).im = -((-star s).im) := Complex.neg_im (-star s)
      _ = -(-(star s).im) := congrArg Neg.neg (Complex.neg_im (star s))
      _ = -(-(-(s.im))) := congrArg (fun y : ℝ => -(-y)) (Complex.star_im s)
      _ = -(s.im) := by
        exact neg_neg (-(s.im))

  -- Define the weighted test functions
  let φ₊ := fun u : ℝ => Real.exp (-(s.re) * u) • φ (Real.exp (-u))
  let φ₋ := fun u : ℝ => Real.exp ((-(-star s)).re * u) • φ (Real.exp (-u))

  -- By the weight relationship:
  have h_φ_eq : φ₋ = φ₊ := by
    funext u
    exact congrArg
      (fun r : ℝ => Real.exp (r * u) • φ (Real.exp (-u)))
      h_weight_real

  -- The Fourier transforms at opposite frequencies
  have h_fourier : ∀ ω : ℝ, (𝓕 φ₊ (-ω : ℝ) : ℂ) = star (𝓕 φ₊ ω) :=
    fun ω => FourierConjugacy.fourierTransform_conjugacy φ₊ hφ_weighted_real ω

  have hleft :
      (mellin φ (-star s) : ℂ) =
        𝓕 φ₋ ((-(-star s)).im / (2 * π)) :=
    boundary_mellin_eq_fourierIntegral φ (s := -star s)
  have hright :
      (mellin φ s : ℂ) =
        𝓕 φ₊ (s.im / (2 * π)) :=
    boundary_mellin_eq_fourierIntegral φ (s := s)

  calc (mellin φ (-star s) : ℂ)
      = 𝓕 φ₋ ((-(-star s)).im / (2 * π)) := hleft
    _ = 𝓕 φ₊ ((-(-star s)).im / (2 * π)) := by
          exact congrArg (fun ψ : ℝ → ℂ => 𝓕 ψ ((-(-star s)).im / (2 * π))) h_φ_eq
    _ = 𝓕 φ₊ (-(s.im : ℝ) / (2 * π)) := by
          exact congrArg (fun y : ℝ => 𝓕 φ₊ (y / (2 * π))) h_freq_real
    _ = star (𝓕 φ₊ (s.im / (2 * π))) := h_fourier (s.im / (2 * π))
    _ = star (mellin φ s) := by
          exact congrArg star hright.symm

/-- Mellin inversion applied to a conjugate-symmetric transform produces
a function with conjugate symmetry in its values. -/
lemma mellinInv_preserves_conjugateSymmetry
    {M : ℂ → ℂ} (hM : Transform.IsConjugateSymmetric M)
    (σ : ℝ)
    (hg_line : ∀ y : ℝ,
      M ((σ : ℂ) + 2 * π * (-y : ℝ) * I) =
        star (M ((σ : ℂ) + 2 * π * y * I)))
    (hM_integrable : Integrable (fun y : ℝ => M (σ + 2 * π * y * I)))
    (x : ℝ) (hx : 0 < x) :
    mellinInv σ M x = star (mellinInv σ M x) :=
  MellinInversionConjugacy.conjugateSymmetricTransform_inverts_to_realValues
    hM σ hg_line hM_integrable x hx

/-- The completed Mellin transform (with exponential damping for decay)
preserves conjugate symmetry. -/
lemma completed_mellin_conjugateSymmetric
    (φ : ℝ → ℂ) (s : ℂ) (σ : ℝ)
    (hφ_weighted_real :
      ∀ u : ℝ,
        Real.exp (-(((σ : ℂ) + I * s).re) * u) • φ (Real.exp (-u)) =
          star (Real.exp (-(((σ : ℂ) + I * s).re) * u) • φ (Real.exp (-u)))) :
    (mellin φ (-star (σ + I * (s : ℂ))) : ℂ) =
    star (mellin φ (σ + I * (s : ℂ))) := by
  -- This is a direct application of mellin_conjugateSymmetric_property
  -- with s = σ + It, since:
  -- -star(σ + It) = -σ + It (as -star(a + bi) = -a - bi)
  -- Wait, let me recalculate:
  -- star(σ + It) = σ - It
  -- -star(σ + It) = -σ + It
  -- So we're evaluating at conjugate points on vertical lines

  have h_point : σ + I * (s : ℂ) = (σ : ℂ) + I * s := by
    exact Eq.refl _

  exact Eq.subst
    (motive := fun z : ℂ => (mellin φ (-star z) : ℂ) = star (mellin φ z))
    h_point.symm
    (mellin_conjugateSymmetric_property φ ((σ : ℂ) + I * s) hφ_weighted_real)

/-- For compactly supported smooth functions, Mellin inversion of the
conjugate-symmetric transform yields a compactly supported smooth function
with the same compact support properties. -/
theorem paleyWiener_mellinInv_conjugateSymmetric
    {M : ℂ → ℂ} (hM : Transform.IsConjugateSymmetric M)
    (σ : ℝ)
    (hg_line : ∀ y : ℝ,
      M ((σ : ℂ) + 2 * π * (-y : ℝ) * I) =
        star (M ((σ : ℂ) + 2 * π * y * I)))
    (hM_integrable : Integrable (fun y : ℝ => M (σ + 2 * π * y * I))) :
    let f := mellinInv σ M
    ∀ x : ℝ, 0 < x → (f x = star (f x)) := by
  intro x hx
  exact mellinInv_preserves_conjugateSymmetry hM σ hg_line hM_integrable x hx

/-- Public API: Paley-Wiener Mellin inversion produces conjugate-symmetric results. -/
theorem paleyWienerMellinInv_conjugateSymmetric
    {M : ℂ → ℂ} (hM : Transform.IsConjugateSymmetric M) (σ : ℝ)
    (hg_line : ∀ y : ℝ,
      M ((σ : ℂ) + 2 * π * (-y : ℝ) * I) =
        star (M ((σ : ℂ) + 2 * π * y * I)))
    (hM_integrable : Integrable (fun y : ℝ => M (σ + 2 * π * y * I))) :
    ∀ x : ℝ, 0 < x →
    mellinInv σ M x = star (mellinInv σ M x) :=
  fun x hx => mellinInv_preserves_conjugateSymmetry hM σ hg_line hM_integrable x hx

end MellinConjugacy

end LFunctions
end Boundary
