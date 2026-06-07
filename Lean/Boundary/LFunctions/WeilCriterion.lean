import Boundary.LFunctions.ZetaTestFunction
import Boundary.LFunctions.ZetaCompletedNormalization
import Boundary.LFunctions.ProbeInterface
import Boundary.LFunctions.AutocorrelationInterface
import Boundary.LFunctions.ZetaZeroSideDefinitions
import Mathlib.NumberTheory.LSeries.RiemannZeta

/-!
# Boundary exposure of mathlib's Riemann zeta and RH statement

This file now owns the centered completed-zeta normalization used by the
explicit-formula route, while still re-exporting the public mathlib zeta
objects and theorem names into the Boundary L-function namespace so later
Boundary files can target the official `RiemannHypothesis` statement directly.

The explicit-formula packet route will live alongside this file, but this file
itself does not introduce a new criterion or a bespoke analytic package.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open Real Complex

/-- The additive-line test functions used by the explicit-formula route. -/
abbrev ZetaAdditiveTestFunction := ZetaTestFunction

/-- The admissible test functions for the Weil criterion route. -/
abbrev ZetaAdmissible := ZetaAdditiveTestFunction

/-- Boundary alias for mathlib's Riemann zeta function. -/
abbrev boundaryRiemannZeta := riemannZeta

/-- Boundary alias for mathlib's completed Riemann zeta function. -/
abbrev boundaryCompletedRiemannZeta := completedRiemannZeta

/-- Boundary alias for mathlib's Riemann hypothesis statement. -/
abbrev boundaryRiemannHypothesis := RiemannHypothesis

/-- Unfolded form of the boundary RH statement, matching mathlib exactly. -/
theorem boundaryRiemannHypothesis_iff :
    boundaryRiemannHypothesis ↔
      ∀ (s : ℂ) (_ : riemannZeta s = 0)
        (_ : ¬ ∃ n : ℕ, s = -2 * (n + 1)) (_ : s ≠ 1), s.re = 1 / 2 := by
  rfl

/-
Concrete bridge DAG, in the exact shape this owner file exposes:

`zetaWeilForm`
  ↔ `centeredCompletedRiemannZeta`
  ↔ `completedRiemannZeta (1 / 2 + s)`
  ↔ completed-zeta decomposition `Λ₀ - pole terms`
  ↔ functional equation symmetry `s ↔ 1 - s`
  ↔ completed-zeta zero criterion
  ↔ mathlib `RiemannHypothesis`

The packet and Weil positivity layers are upstream of this file and should
feed the completed-zeta zero criterion, not replace it.
-/

/-- The centered completed zeta function used by the Weil-form normalization. -/
def zetaWeilForm (s : ℂ) : ℂ :=
  centeredCompletedRiemannZeta s

@[simp]
theorem zetaWeilForm_eq_centeredCompletedRiemannZeta (s : ℂ) :
    zetaWeilForm s = centeredCompletedRiemannZeta s := rfl

@[simp]
theorem zetaWeilForm_eq_completedRiemannZeta (s : ℂ) :
    zetaWeilForm s = completedRiemannZeta (1 / 2 + s) := rfl

/-- The centered completed zeta expanded into entire and pole terms. -/
theorem zetaWeilForm_eq_centeredCompletedRiemannZeta_decomposition (s : ℂ) :
    zetaWeilForm s =
      centeredCompletedRiemannZeta₀ s -
        1 / (1 / 2 + s) - 1 / (1 - (1 / 2 + s)) := by
  rw [zetaWeilForm_eq_centeredCompletedRiemannZeta, centeredCompletedRiemannZeta_eq]

/-- The centered completed zeta expanded as the entire term minus pole terms. -/
theorem zetaWeilForm_eq_centeredCompletedRiemannZeta₀_minus_poles (s : ℂ) :
    zetaWeilForm s =
      centeredCompletedRiemannZeta₀ s -
        1 / (1 / 2 + s) - 1 / (1 - (1 / 2 + s)) := by
  exact zetaWeilForm_eq_centeredCompletedRiemannZeta_decomposition s

/-- The main completed-zeta term in the centered Weil normalization. -/
def zetaWeilMainTerm (s : ℂ) : ℂ :=
  centeredCompletedRiemannZeta₀ s

/-- The centered completed zeta itself. -/
def zetaWeilCompletedPart (s : ℂ) : ℂ :=
  completedRiemannZeta (1 / 2 + s)

@[simp]
theorem zetaWeilCompletedPart_eq_completedRiemannZeta (s : ℂ) :
    zetaWeilCompletedPart s = completedRiemannZeta (1 / 2 + s) := rfl

/-- The pole correction term in the centered Weil normalization. -/
def zetaWeilCorrection (s : ℂ) : ℂ :=
  1 / (1 / 2 + s) + 1 / (1 - (1 / 2 + s))

/-- The Dirichlet-series part of the centered completed zeta. -/
def zetaWeilDirichletPart (s : ℂ) : ℂ :=
  riemannZeta (1 / 2 + s)

/-- The gamma-factor part of the centered completed zeta. -/
def zetaWeilGammaPart (s : ℂ) : ℂ :=
  Gammaℝ (1 / 2 + s)

theorem zetaWeilForm_eq_main_minus_correction (s : ℂ) :
    zetaWeilForm s = zetaWeilMainTerm s - zetaWeilCorrection s := by
  unfold zetaWeilForm zetaWeilMainTerm zetaWeilCorrection
  rw [centeredCompletedRiemannZeta_eq]
  rw [sub_sub]

/-- The Weil-form decomposition rewritten as the main term minus correction. -/
theorem zetaWeilForm_eq_main_minus_correction_expanded (s : ℂ) :
    zetaWeilForm s = zetaWeilMainTerm s - zetaWeilCorrection s := by
  exact zetaWeilForm_eq_main_minus_correction s

/-- The centered completed zeta decomposition in the public criterion file. -/
theorem zetaWeilForm_eq_prime_add_archimedean_add_correction (s : ℂ) :
    zetaWeilForm s =
      zetaWeilMainTerm s - zetaWeilCorrection s := by
  exact zetaWeilForm_eq_main_minus_correction s

theorem zetaWeilForm_neg (s : ℂ) :
    zetaWeilForm (-s) = zetaWeilForm s := by
  unfold zetaWeilForm
  exact centeredCompletedRiemannZeta_neg s

theorem zetaWeilMainTerm_neg (s : ℂ) :
    zetaWeilMainTerm (-s) = zetaWeilMainTerm s := by
  unfold zetaWeilMainTerm
  exact centeredCompletedRiemannZeta₀_neg s

theorem zetaWeilCorrection_neg (s : ℂ) :
    zetaWeilCorrection (-s) = zetaWeilCorrection s := by
  unfold zetaWeilCorrection
  exact centeredCompletedRiemannZeta_correction_symm s

theorem zetaWeilCompletedPart_eq_dirichlet_mul_gamma (s : ℂ)
    (hs : (1 / 2 : ℂ) + s ≠ 0) (hΓ : Gammaℝ (1 / 2 + s) ≠ 0) :
    zetaWeilCompletedPart s = zetaWeilDirichletPart s * zetaWeilGammaPart s := by
  unfold zetaWeilCompletedPart zetaWeilDirichletPart zetaWeilGammaPart
  have h := riemannZeta_def_of_ne_zero (s := (1 / 2 : ℂ) + s) hs
  exact (div_eq_iff hΓ).mp h.symm

theorem completedRiemannZeta_eq_riemannZeta_mul_gamma {s : ℂ}
    (hs : s ≠ 0) (hΓ : Gammaℝ s ≠ 0) :
    completedRiemannZeta s = riemannZeta s * Gammaℝ s := by
  have h := riemannZeta_def_of_ne_zero hs
  exact (div_eq_iff hΓ).mp h.symm

/-- Criterion-facing form of the centered completed zeta, expressed in the
mathlib normalization. -/
theorem zetaWeilForm_eq_completedRiemannZeta_centered (s : ℂ) :
    zetaWeilForm s = completedRiemannZeta (1 / 2 + s) := by
  rfl

/-- Criterion-facing form of the centered completed zeta decomposition. -/
theorem zetaWeilForm_eq_boundaryMainMinusCorrection (s : ℂ) :
    zetaWeilForm s =
      zetaWeilMainTerm s - zetaWeilCorrection s := by
  exact zetaWeilForm_eq_prime_add_archimedean_add_correction s

/-- Criterion-facing form of the centered completed zeta symmetry. -/
theorem zetaWeilForm_boundary_neg (s : ℂ) :
    zetaWeilForm (-s) = zetaWeilForm s := by
  exact zetaWeilForm_neg s

/-- The centered completed zeta has the expected reflection symmetry in the
owner criterion file. -/
theorem zetaWeilForm_centered_reflection_symmetry (s : ℂ) :
    zetaWeilForm (-s) = zetaWeilForm s := by
  exact zetaWeilForm_neg s

/-- The centered completed zeta symmetry rewritten through the centered form. -/
theorem zetaWeilForm_eq_centeredCompletedRiemannZeta_neg_centered (s : ℂ) :
    zetaWeilForm (-s) = centeredCompletedRiemannZeta s := by
  rw [zetaWeilForm_eq_centeredCompletedRiemannZeta, centeredCompletedRiemannZeta_neg]

/-- The centered completed zeta normalization rewritten in the public owner file. -/
theorem zetaWeilForm_eq_centeredCompletedRiemannZeta_centered (s : ℂ) :
    zetaWeilForm s = centeredCompletedRiemannZeta s := by
  rfl

/-- The centered completed zeta symmetry rewritten in the public owner file. -/
theorem zetaWeilForm_eq_centeredCompletedRiemannZeta_neg (s : ℂ) :
    zetaWeilForm (-s) = centeredCompletedRiemannZeta s := by
  rw [zetaWeilForm_eq_centeredCompletedRiemannZeta, centeredCompletedRiemannZeta_neg]

/-- The centered pole correction symmetry rewritten in the public owner file. -/
theorem zetaWeilCorrection_centered_reflection (s : ℂ) :
    zetaWeilCorrection (-s) = zetaWeilCorrection s := by
  exact zetaWeilCorrection_neg s

/-- The completed zero-side sum in real-valued form. -/
noncomputable def zetaCompletedZeroSideRe
    (φ : ZetaProbe) : ℝ :=
  Complex.re <|
    ∑' ρ : {ρ : ℂ // ZetaCompletedZero ρ},
      zetaZeroSideContribution (ρ : ℂ) φ

/-- The completed spectral Weil form on the zero side. -/
noncomputable def zetaCompletedSpectralWeilForm
    (φ : ZetaProbe) : ℝ :=
  zetaCompletedZeroSideRe φ

/-- The completed Weil form on the probe class. -/
noncomputable def zetaWeilFormCompleted (φ : ZetaProbe) : ℝ :=
  zetaCompletedSpectralWeilForm φ

/-- Positivity restricted to autocorrelation-generated probes. -/
def ZetaAutocorrelationWeilPositivity : Prop :=
  ∀ φ : ZetaProbe,
    IsZetaAutocorrelationProbe φ →
      0 ≤ zetaWeilFormCompleted φ

/-- Weil positivity on the probe class. -/
def ZetaWeilPositivity : Prop :=
  ∀ φ : ZetaProbe, 0 ≤ zetaWeilFormCompleted φ

/-- The completed spectral Weil form is definitionally the completed zero-side sum. -/
theorem zetaCompletedSpectralWeilForm_def
    (φ : ZetaProbe) :
    zetaCompletedSpectralWeilForm φ = zetaCompletedZeroSideRe φ := by
  rfl

/-- The completed Weil form is definitionally the completed spectral form. -/
theorem zetaWeilFormCompleted_def
    (φ : ZetaProbe) :
    zetaWeilFormCompleted φ = zetaCompletedSpectralWeilForm φ := by
  rfl

end

end LFunctions
end Boundary
