import Boundary.LFunctionsRootedTreeCanonicalAll.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaTestFunction.ZetaTestFunction
import Boundary.LFunctionsRootedTreeCanonicalAll.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalization.ZetaCompletedNormalization
import Boundary.LFunctionsRootedTreeCanonicalAll.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalizationBridge.ZetaCompletedNormalizationBridge
import Boundary.LFunctionsRootedTreeCanonicalAll.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaWeilShared
import Boundary.LFunctionsRootedTreeCanonicalAll.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroOrbitRemainder
import Boundary.LFunctionsRootedTreeCanonicalAll.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ProbeInterface.ProbeInterface
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
  exact centeredCompletedRiemannZeta_eq s ▸ by
    exact sub_sub _ _ _

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

/-- The centered pole correction symmetry rewritten in the public owner file. -/
theorem zetaWeilCorrection_centered_reflection (s : ℂ) :
    zetaWeilCorrection (-s) = zetaWeilCorrection s := by
  exact zetaWeilCorrection_neg s

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
  rcases hx with ⟨n, hn⟩
  apply htriv
  refine ⟨n, ?_⟩
  exact boundaryRiemannHypothesis_shift_eq z ▸ hn

/-- The centered zero-criterion transport preserves the pole exclusion. -/
theorem boundaryRiemannHypothesis_pole_shift
    (z : ℂ) (hpole : z ≠ 1) :
    (1 / 2 + (z - 1 / 2)) ≠ 1 := by
  intro h1
  apply hpole
  exact boundaryRiemannHypothesis_shift_eq z ▸ h1

/-- The centered zero-criterion transport rewrites the real part conclusion. -/
theorem boundaryRiemannHypothesis_realPart_of_centered
    (z : ℂ) (hsre : (z - 1 / 2).re = 0) :
    z.re = 1 / 2 := by
  have hsre' : z.re - 1 / 2 = 0 := by
    have hcomplex' : (z - 1 / 2 : ℂ).re = z.re - (1 / 2 : ℂ).re := by
      exact Complex.sub_re z (1 / 2 : ℂ)
    have hhalf : (1 / 2 : ℂ).re = (1 / 2 : ℝ) := by
      norm_num
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
    change 1 / 2 + (z - 1 / 2) = z
    exact boundaryRiemannHypothesis_shift_eq z
  have hz' : riemannZeta (1 / 2 + s) = 0 := by
    exact hs ▸ hz
  have htriv' : ¬ ∃ n : ℕ, 1 / 2 + s = -2 * (n + 1) :=
    boundaryRiemannHypothesis_nontrivial_shift z htriv
  have hpole' : (1 / 2 + s) ≠ 1 :=
    boundaryRiemannHypothesis_pole_shift z hpole
  have hsre : s.re = 0 := h s hz' htriv' hpole'
	  exact boundaryRiemannHypothesis_realPart_of_centered z hsre

/-- A nontrivial centered zeta zero that is off the critical centered line. -/
structure OffCriticalCenteredZetaZero where
  point : ℂ
  zeta_zero : riemannZeta (1 / 2 + point) = 0
  nontrivial : ¬ ∃ n : ℕ, 1 / 2 + point = -2 * (n + 1)
  not_pole : (1 / 2 + point) ≠ 1
  offCritical : point.re ≠ 0

/-- The point carried by an off-critical centered zero is off the centered critical line. -/
theorem OffCriticalCenteredZetaZero.point_re_ne_zero
    (z : OffCriticalCenteredZetaZero) :
    z.point.re ≠ 0 :=
  z.offCritical

/-- The point carried by an off-critical centered zero is a nontrivial centered zero. -/
theorem OffCriticalCenteredZetaZero.point_zeta_zero
    (z : OffCriticalCenteredZetaZero) :
    riemannZeta (1 / 2 + z.point) = 0 :=
  z.zeta_zero

/-- Off-critical zero separation with the finite orbit and tail margin exposed.

The first inequality says the chosen finite centered zero orbit is a genuinely negative
direction. The second says the complementary zero tail is dominated by that negative margin
for the same autocorrelation probe. -/
theorem exists_negative_zeroOrbit_with_dominated_remainder_autocorrelation_of_offCriticalCenteredZero
    (z : OffCriticalCenteredZetaZero)
    (hcompleted : ZetaCompletedZero z.point)
    (horbit : ∀ η : ℂ, η ∈ zetaZeroOrbitFinset z.point → ZetaCompletedZero η) :
    ∃ f : ZetaAdmissibleFunction,
      zetaZeroOrbitContributionRe z.point
          (ZetaAdmissibleFunction.convolutionAutocorrelation f) < 0 ∧
        zetaZeroOrbitRemainderRe z.point
          (ZetaAdmissibleFunction.convolutionAutocorrelation f) <
            - zetaZeroOrbitContributionRe z.point
              (ZetaAdmissibleFunction.convolutionAutocorrelation f) := by
  exact exists_negative_zeroOrbit_with_dominated_remainder_autocorrelation
    z.point
    (exists_uniform_zeroOrbit_autocorrelation_separator
      z.point hcompleted z.offCritical horbit)

/-- Off-critical zero separation after isolating the finite zero orbit.

The finite orbit is the controlled negative direction; the orbit remainder is the tail that
must be made small by the separating admissible autocorrelation probe. -/
theorem exists_negative_zeroOrbit_plus_remainder_autocorrelation_of_offCriticalCenteredZero
    (z : OffCriticalCenteredZetaZero)
    (hcompleted : ZetaCompletedZero z.point)
    (horbit : ∀ η : ℂ, η ∈ zetaZeroOrbitFinset z.point → ZetaCompletedZero η) :
    ∃ f : ZetaAdmissibleFunction,
      zetaZeroOrbitContributionRe z.point
          (ZetaAdmissibleFunction.convolutionAutocorrelation f) +
        zetaZeroOrbitRemainderRe z.point
          (ZetaAdmissibleFunction.convolutionAutocorrelation f) < 0 := by
  rcases
    exists_negative_zeroOrbit_with_dominated_remainder_autocorrelation_of_offCriticalCenteredZero
      z hcompleted horbit with
    ⟨f, _hfinite_negative, hremainder_dominated⟩
  exact ⟨f, zeroOrbit_add_remainder_lt_zero_of_remainder_lt_neg
    hremainder_dominated⟩

/-- The shifted coordinate of an off-critical centered zero avoids the completed
normalization singularity. -/
theorem offCriticalCenteredZero_shift_ne_zero
    (z : OffCriticalCenteredZetaZero) :
    (1 / 2 : ℂ) + z.point ≠ 0 := by
  intro hzero
  have hzeta_at_zero : riemannZeta (0 : ℂ) = 0 := by
    calc
      riemannZeta (0 : ℂ) =
          riemannZeta ((1 / 2 : ℂ) + z.point) := by
        exact congrArg riemannZeta hzero.symm
      _ = 0 := z.zeta_zero
  exact riemannZeta_zero_ne_zero hzeta_at_zero

/-- The completed Gamma factor is nonzero at a nontrivial centered zeta zero. -/
theorem offCriticalCenteredZero_gamma_ne_zero
    (z : OffCriticalCenteredZetaZero) :
    Gammaℝ ((1 / 2 : ℂ) + z.point) ≠ 0 := by
  exact Gammaℝ_ne_zero_of_ne_zero_and_not_negative_even
    (offCriticalCenteredZero_shift_ne_zero z)
    z.nontrivial

/-- An off-critical centered ordinary zeta zero is a centered completed-zeta zero. -/
theorem offCriticalCenteredZero_completedZero
    (z : OffCriticalCenteredZetaZero) :
    ZetaCompletedZero z.point := by
  refine zetaCompletedZero_mk ?_ ?_ ?_
  · intro hpoint
    exact offCriticalCenteredZero_shift_ne_zero z
      (by
        calc
          (1 / 2 : ℂ) + z.point =
              (1 / 2 : ℂ) + (-(1 / 2 : ℂ)) := by
            exact congrArg (fun w : ℂ => (1 / 2 : ℂ) + w) hpoint
          _ = 0 := by ring)
  · intro hpoint
    exact z.not_pole
      (by
        calc
          (1 / 2 : ℂ) + z.point =
              (1 / 2 : ℂ) + (1 / 2 : ℂ) := by
            exact congrArg (fun w : ℂ => (1 / 2 : ℂ) + w) hpoint
          _ = 1 := by ring)
  · exact centeredCompletedRiemannZeta_eq_zero_of_riemannZeta_eq_zero
      (offCriticalCenteredZero_shift_ne_zero z)
      (offCriticalCenteredZero_gamma_ne_zero z)
      z.zeta_zero

/-- The centered reflection orbit of an off-critical centered zero lies in the centered
completed-zero locus. -/
theorem offCriticalCenteredZero_orbit_completedZero
    (z : OffCriticalCenteredZetaZero) :
    ∀ η : ℂ, η ∈ zetaZeroOrbitFinset z.point → ZetaCompletedZero η := by
  intro η hη
  have hcompleted : ZetaCompletedZero z.point :=
    offCriticalCenteredZero_completedZero z
  have hfaces : η = z.point ∨ η = -z.point :=
    (zetaZeroOrbitFinset_mem_iff z.point η).1 hη
  rcases hfaces with hpos | hneg
  · exact Eq.subst
      (motive := fun x : ℂ => ZetaCompletedZero x)
      hpos.symm
      hcompleted
  · have hnegzero : ZetaCompletedZero (-z.point) := by
      exact zetaCompletedZero_neg hcompleted
    exact Eq.subst
      (motive := fun x : ℂ => ZetaCompletedZero x)
      hneg.symm
      hnegzero

/-- An off-critical centered Riemann-zeta zero is a centered completed-zeta zero, and its
functional-equation orbit remains in the centered completed zero locus. -/
theorem offCriticalCenteredZero_completedZero_and_orbit
    (z : OffCriticalCenteredZetaZero) :
    ZetaCompletedZero z.point ∧
      ∀ η : ℂ, η ∈ zetaZeroOrbitFinset z.point → ZetaCompletedZero η := by
  exact ⟨offCriticalCenteredZero_completedZero z,
    offCriticalCenteredZero_orbit_completedZero z⟩

/-- Zero-side separation for an off-critical centered zeta zero.

This is the real analytic separation step in Weil's criterion: an off-critical centered
zero produces an admissible autocorrelation seed whose zero-side quadratic form is negative. -/
theorem exists_negative_zeroSide_autocorrelation_of_offCriticalCenteredZero
    (z : OffCriticalCenteredZetaZero) :
    ∃ f : ZetaAdmissibleFunction,
      zetaCompletedZeroSideRe (ZetaAdmissibleFunction.convolutionAutocorrelation f) < 0 := by
  rcases offCriticalCenteredZero_completedZero_and_orbit z with
    ⟨hcompleted, horbit⟩
  rcases exists_negative_zeroOrbit_plus_remainder_autocorrelation_of_offCriticalCenteredZero
      z hcompleted horbit with
    ⟨f, hf⟩
  exact ⟨f,
    zetaCompletedZeroSideRe_lt_zero_of_orbitContribution_add_remainderRe_lt_zero
      z.point
      (ZetaAdmissibleFunction.convolutionAutocorrelation f)
      hcompleted
      horbit
      (summable_zetaZeroSideContribution
        (ZetaAdmissibleFunction.convolutionAutocorrelation f))
      hf⟩

/-- The zero-detecting direction of Weil's criterion.

An off-critical nontrivial centered zero can be separated by an admissible
autocorrelation seed whose completed Weil quadratic form is strictly negative.
This theorem is now only the Weil-form transport of the zero-side separation theorem above. -/
theorem exists_negative_autocorrelation_quadraticForm_of_offCriticalCenteredZero
    (z : OffCriticalCenteredZetaZero) :
    ∃ f : ZetaAdmissibleFunction,
      zetaWeilFormCompleted (ZetaAdmissibleFunction.convolutionAutocorrelation f) < 0 := by
  rcases exists_negative_zeroSide_autocorrelation_of_offCriticalCenteredZero z with
    ⟨f, hf⟩
  refine ⟨f, ?_⟩
  calc
    zetaWeilFormCompleted (ZetaAdmissibleFunction.convolutionAutocorrelation f) =
        zetaCompletedZeroSideRe (ZetaAdmissibleFunction.convolutionAutocorrelation f) := by
      exact zetaWeilFormCompleted_convolutionAutocorrelation_eq_zeroSide f
    _ < 0 := hf

/-- Parameter-facing wrapper for the zero-detecting direction of Weil's criterion. -/
theorem exists_negative_autocorrelation_quadraticForm_of_offCritical_centeredZero
    (s : ℂ)
    (hz : riemannZeta (1 / 2 + s) = 0)
    (htriv : ¬ ∃ n : ℕ, 1 / 2 + s = -2 * (n + 1))
    (hpole : (1 / 2 + s) ≠ 1)
    (hoff : s.re ≠ 0) :
    ∃ f : ZetaAdmissibleFunction,
      zetaWeilFormCompleted (ZetaAdmissibleFunction.convolutionAutocorrelation f) < 0 := by
  exact exists_negative_autocorrelation_quadraticForm_of_offCriticalCenteredZero
    ⟨s, hz, htriv, hpole, hoff⟩

/-- Quadratic Weil positivity gives the centered zero criterion.

This is the standard Weil-criterion formalization point: once the completed Weil quadratic
form is nonnegative on all autocorrelation seeds, every nontrivial centered zero lies on the
critical line. -/
theorem centeredZeroCriterion_of_zetaWeilQuadraticPositivity
    (h : ZetaWeilQuadraticPositivity) :
    ∀ s : ℂ,
	      riemannZeta (1 / 2 + s) = 0 →
	        (¬ ∃ n : ℕ, 1 / 2 + s = -2 * (n + 1)) →
	          (1 / 2 + s) ≠ 1 →
	            s.re = 0 := by
  intro s hz htriv hpole
  by_contra hoff
  rcases exists_negative_autocorrelation_quadraticForm_of_offCritical_centeredZero
      s hz htriv hpole hoff with ⟨f, hfneg⟩
  exact (not_lt_of_ge (h f)) hfneg

/-- The standard Weil criterion in the quadratic/autocorrelation form. -/
theorem boundaryRiemannHypothesis_of_zetaWeilQuadraticPositivity
    (h : ZetaWeilQuadraticPositivity) :
    boundaryRiemannHypothesis := by
  exact boundaryRiemannHypothesis_of_centeredZeroCriterion
    (centeredZeroCriterion_of_zetaWeilQuadraticPositivity h)

end

end LFunctions
end Boundary
