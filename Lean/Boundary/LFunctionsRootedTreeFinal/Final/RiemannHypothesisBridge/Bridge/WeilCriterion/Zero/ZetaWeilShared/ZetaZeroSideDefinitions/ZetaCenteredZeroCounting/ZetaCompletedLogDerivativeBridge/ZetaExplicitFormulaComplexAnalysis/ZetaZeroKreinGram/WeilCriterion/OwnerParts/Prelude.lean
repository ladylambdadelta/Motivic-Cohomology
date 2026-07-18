import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ProbeInterface.ZetaAdmissibleFunction.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalization.CenteredZeros.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalizationBridge.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.WeilCorrectionCore.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaZeroKreinGram.Owner
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

theorem zetaWeilForm_eq_centeredCompletedRiemannZeta (s : ℂ) :
    zetaWeilForm s = centeredCompletedRiemannZeta s := rfl

theorem zetaWeilForm_eq_completedRiemannZeta (s : ℂ) :
    zetaWeilForm s = completedRiemannZeta (1 / 2 + s) := rfl

/-- The centered completed zeta expanded into entire and pole terms. -/
theorem zetaWeilForm_eq_centeredCompletedRiemannZeta_decomposition (s : ℂ) :
    zetaWeilForm s =
      centeredCompletedRiemannZeta₀ s -
        1 / (1 / 2 + s) - 1 / (1 - (1 / 2 + s)) := by
  exact (zetaWeilForm_eq_centeredCompletedRiemannZeta s).trans
    (centeredCompletedRiemannZeta_eq s)

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

theorem zetaWeilCompletedPart_eq_completedRiemannZeta (s : ℂ) :
    zetaWeilCompletedPart s = completedRiemannZeta (1 / 2 + s) := rfl

/-- The Dirichlet-series part of the centered completed zeta. -/
def zetaWeilDirichletPart (s : ℂ) : ℂ :=
  riemannZeta (1 / 2 + s)

/-- The gamma-factor part of the centered completed zeta. -/
def zetaWeilGammaPart (s : ℂ) : ℂ :=
  Complex.Gammaℝ (1 / 2 + s)

theorem zetaWeilForm_eq_main_minus_correction (s : ℂ) :
    zetaWeilForm s = zetaWeilMainTerm s - zetaWeilCorrection s := by
  calc
    zetaWeilForm s = centeredCompletedRiemannZeta s := rfl
    _ =
        centeredCompletedRiemannZeta₀ s -
          1 / (1 / 2 + s) - 1 / (1 - (1 / 2 + s)) :=
      centeredCompletedRiemannZeta_eq s
    _ =
        zetaWeilMainTerm s -
          (1 / (1 / 2 + s) + 1 / (1 - (1 / 2 + s))) := by
      exact sub_sub
        (centeredCompletedRiemannZeta₀ s)
        (1 / (1 / 2 + s))
        (1 / (1 - (1 / 2 + s)))
    _ = zetaWeilMainTerm s - zetaWeilCorrection s := rfl

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
  calc
    zetaWeilForm (-s) = centeredCompletedRiemannZeta (-s) := rfl
    _ = centeredCompletedRiemannZeta s := centeredCompletedRiemannZeta_neg s
    _ = zetaWeilForm s := rfl

theorem zetaWeilMainTerm_neg (s : ℂ) :
    zetaWeilMainTerm (-s) = zetaWeilMainTerm s := by
  calc
    zetaWeilMainTerm (-s) = centeredCompletedRiemannZeta₀ (-s) := rfl
    _ = centeredCompletedRiemannZeta₀ s := centeredCompletedRiemannZeta₀_neg s
    _ = zetaWeilMainTerm s := rfl

theorem zetaWeilCompletedPart_eq_dirichlet_mul_gamma (s : ℂ)
    (hs : (1 / 2 : ℂ) + s ≠ 0) (hΓ : Complex.Gammaℝ (1 / 2 + s) ≠ 0) :
    zetaWeilCompletedPart s = zetaWeilDirichletPart s * zetaWeilGammaPart s := by
  have h := riemannZeta_def_of_ne_zero (s := (1 / 2 : ℂ) + s) hs
  have hcompleted :
      completedRiemannZeta (1 / 2 + s) =
        riemannZeta (1 / 2 + s) * Complex.Gammaℝ (1 / 2 + s) :=
    (div_eq_iff hΓ).mp h.symm
  calc
    zetaWeilCompletedPart s = completedRiemannZeta (1 / 2 + s) := rfl
    _ = riemannZeta (1 / 2 + s) * Complex.Gammaℝ (1 / 2 + s) := hcompleted
    _ = zetaWeilDirichletPart s * zetaWeilGammaPart s := rfl

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
  exact (zetaWeilForm_eq_centeredCompletedRiemannZeta (-s)).trans
    (centeredCompletedRiemannZeta_neg s)

/-- The centered completed zeta normalization rewritten in the public owner file. -/
theorem zetaWeilForm_eq_centeredCompletedRiemannZeta_centered (s : ℂ) :
    zetaWeilForm s = centeredCompletedRiemannZeta s := by
  rfl

/-- The centered completed zeta symmetry rewritten in the public owner file. -/
theorem zetaWeilForm_eq_centeredCompletedRiemannZeta_neg (s : ℂ) :
    zetaWeilForm (-s) = centeredCompletedRiemannZeta s := by
  exact zetaWeilForm_eq_centeredCompletedRiemannZeta_neg_centered s

/-- The centered shift used in the RH transport theorem. -/
theorem boundaryRiemannHypothesis_shift_eq (z : ℂ) :
    1 / 2 + (z - 1 / 2) = z := by
  calc
    1 / 2 + (z - 1 / 2) = z - 1 / 2 + 1 / 2 := by
      exact add_comm (1 / 2 : ℂ) (z - 1 / 2)
    _ = z := by
      exact sub_add_cancel z (1 / 2 : ℂ)

/-- The centered zero-criterion transport preserves the trivial-line exclusion. -/
theorem boundaryRiemannHypothesis_nontrivial_shift
    (z : ℂ) (htriv : ¬ ∃ n : ℕ, z = -2 * (n + 1)) :
    ¬ ∃ n : ℕ, 1 / 2 + (z - 1 / 2) = -2 * (n + 1) := by
  intro hx
  exact
    match hx with
    | ⟨n, hn⟩ =>
        htriv ⟨n, (boundaryRiemannHypothesis_shift_eq z).symm.trans hn⟩

/-- The centered zero-criterion transport preserves the pole exclusion. -/
theorem boundaryRiemannHypothesis_pole_shift
    (z : ℂ) (hpole : z ≠ 1) :
    (1 / 2 + (z - 1 / 2)) ≠ 1 := by
  intro h1
  exact hpole ((boundaryRiemannHypothesis_shift_eq z).symm.trans h1)

/-- The real part of the complex half is the real half, with the coercion path exposed. -/
theorem complex_half_re_eq_real_half :
    ((1 / 2 : ℂ).re : ℝ) = (1 / 2 : ℝ) := by
  have hcoerce : ((↑(1 / 2 : ℝ) : ℂ) : ℂ) = (1 / 2 : ℂ) :=
    Complex.ofReal_div (1 : ℝ) (2 : ℝ)
  have hre : ((↑(1 / 2 : ℝ) : ℂ).re : ℝ) = (1 / 2 : ℝ) :=
    Complex.ofReal_re (1 / 2 : ℝ)
  exact (congrArg Complex.re hcoerce).symm.trans hre

/-- The centered zero-criterion transport rewrites the real part conclusion. -/
theorem boundaryRiemannHypothesis_realPart_of_centered
    (z : ℂ) (hsre : (z - 1 / 2).re = 0) :
    z.re = 1 / 2 := by
  have hsre' : z.re - 1 / 2 = 0 := by
    have hcomplex' : (z - 1 / 2 : ℂ).re = z.re - (1 / 2 : ℂ).re := by
      exact Complex.sub_re z (1 / 2 : ℂ)
    have hhalf : ((1 / 2 : ℂ).re : ℝ) = (1 / 2 : ℝ) :=
      complex_half_re_eq_real_half
    have hcomplex : (z - 1 / 2 : ℂ).re = z.re - 1 / 2 := by
      exact hcomplex'.trans (congrArg (fun x : ℝ => z.re - x) hhalf)
    exact hcomplex.symm.trans hsre
  exact sub_eq_zero.mp hsre'

/-- A centered zero-criterion theorem implies the Boundary RH statement. -/
theorem boundaryRiemannHypothesis_of_centeredZeroCriterion
    (h :
      ∀ s : ℂ,
        riemannZeta (1 / 2 + s) = 0 →
          (¬ ∃ n : ℕ, 1 / 2 + s = -2 * (n + 1)) →
          (1 / 2 + s) ≠ 1 →
          s.re = 0) :
    boundaryRiemannHypothesis := by
  intro z hz htriv hpole
  let s : ℂ := z - 1 / 2
  have hs : 1 / 2 + s = z := by
    exact boundaryRiemannHypothesis_shift_eq z
  have hz' : riemannZeta (1 / 2 + s) = 0 := by
    exact hs ▸ hz
  have htriv' : ¬ ∃ n : ℕ, 1 / 2 + s = -2 * (n + 1) :=
    boundaryRiemannHypothesis_nontrivial_shift z htriv
  have hpole' : (1 / 2 + s) ≠ 1 :=
    boundaryRiemannHypothesis_pole_shift z hpole
  have hsre : s.re = 0 := h s hz' htriv' hpole'
  exact boundaryRiemannHypothesis_realPart_of_centered z hsre


end
end LFunctions
end Boundary
