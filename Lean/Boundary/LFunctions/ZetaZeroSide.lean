import Boundary.LFunctions.ZetaZeroSideDefinitions
import Boundary.LFunctions.ZetaCenteredZeroCounting
import Boundary.LFunctions.WeilCriterion

/-!
# Boundary zero-side package

This file packages the centered zero locus and its finite reflection orbit as
the current zero-side data surface for the explicit-formula route.
-/

namespace Boundary
namespace LFunctions

noncomputable section

/-- The current zero-side package is the centered zero locus. -/
def zetaZeroSide : Set ℂ := centeredZetaZeros

theorem zetaZeroSide_neg (z : ℂ) :
    z ∈ zetaZeroSide ↔ -z ∈ zetaZeroSide := by
  exact centeredZetaZeros_neg z

/-- The zero-side set is reflection stable. -/
theorem zetaZeroSide_reflect (z : ℂ) : z ∈ zetaZeroSide → -z ∈ zetaZeroSide := by
  intro hz
  exact (zetaZeroSide_neg z).1 hz

/-- The zero-side package is exactly the centered zero locus. -/
theorem zetaZeroSide_eq_centeredZetaZeros : zetaZeroSide = centeredZetaZeros := by
  rfl

/-- The zero-side package is reflection-stable. -/
theorem zetaZeroSide_stable (z : ℂ) : z ∈ zetaZeroSide → -z ∈ zetaZeroSide := by
  exact zetaZeroSide_reflect z

/-- The zero-side package is the centered zero package. -/
theorem zetaZeroSide_centered (z : ℂ) :
    z ∈ zetaZeroSide ↔ centeredCompletedRiemannZeta z = 0 := by
  rfl

/-- The zero-side package is the centered zero locus. -/
theorem zetaZeroSide_eq_centeredZetaZeros : zetaZeroSide = centeredZetaZeros := by
  rfl

/-- The zero-side package satisfies the raw Weil positivity predicate. -/
theorem zetaZeroSide_weilPositivity_predicate : ZetaWeilPositivity := by
  intro φ
  exact Boundary.LFunctions.zetaWeilFormCompleted_autocorrelation_nonnegative_of_probe (f := φ)

/-- Autocorrelation-generated probes satisfy the zero-side package Weil positivity predicate. -/
theorem zetaZeroSide_autocorrelation_weilPositivity_predicate :
    ZetaAutocorrelationWeilPositivity := by
  intro φ hφ
  exact Boundary.LFunctions.zetaWeilFormCompleted_nonnegative_of_isZetaAutocorrelationProbe φ hφ

/-- The zero-side package's autocorrelation Weil positivity predicate is pointwise nonnegativity. -/
theorem zetaZeroSide_autocorrelation_weilPositivity_iff_predicate :
    ZetaAutocorrelationWeilPositivity ↔
      ∀ φ : ZetaProbe, IsZetaAutocorrelationProbe φ →
        0 ≤ zetaWeilFormCompleted φ := by
  rfl

/-- The zero-side package's Weil positivity predicate is pointwise nonnegativity. -/
theorem zetaZeroSide_weilPositivity_iff :
    ZetaWeilPositivity ↔
      ∀ φ : ZetaProbe, 0 ≤ zetaWeilFormCompleted φ := by
  rfl

/-- Pointwise nonnegativity is the zero-side package's raw Weil positivity predicate. -/
theorem zetaZeroSide_weilPositivity_iff' :
    (∀ φ : ZetaProbe, 0 ≤ zetaWeilFormCompleted φ) ↔ ZetaWeilPositivity := by
  rfl

/-- Autocorrelation-generated probes have nonnegative zero-side real sum in the package surface. -/
theorem zetaZeroSide_autocorrelation_zeroSide_nonnegative
    (f : ZetaAdmissibleFunction) :
    0 ≤ zetaCompletedZeroSideRe (ZetaAdmissibleFunction.autocorrelation f) := by
  rw [← Boundary.LFunctions.zetaWeilFormCompleted_autocorrelation_eq_zeroSide]
  exact Boundary.LFunctions.zetaWeilFormCompleted_autocorrelation_nonnegative_of_probe (f := f)

/-- Autocorrelation-generated probes satisfy the zero-side package's Weil positivity. -/
theorem zetaZeroSide_autocorrelation_weilPositivity
    (f : ZetaAdmissibleFunction) :
    0 ≤ zetaWeilFormCompleted (ZetaAdmissibleFunction.autocorrelation f) := by
  exact Boundary.LFunctions.zetaWeilFormCompleted_autocorrelation_nonnegative_of_probe (f := f)

/-- The zero-side package's autocorrelation Weil positivity is the zero-side nonnegativity statement. -/
theorem zetaZeroSide_autocorrelation_weilPositivity_iff
    (f : ZetaAdmissibleFunction) :
    0 ≤ zetaWeilFormCompleted (ZetaAdmissibleFunction.autocorrelation f) ↔
      0 ≤ zetaCompletedZeroSideRe (ZetaAdmissibleFunction.autocorrelation f) := by
  rw [Boundary.LFunctions.zetaWeilFormCompleted_autocorrelation_eq_zeroSide]

/-- The zero-side package's zero-side nonnegativity statement is the autocorrelation Weil positivity. -/
theorem zetaZeroSide_autocorrelation_weilPositivity_iff'
    (f : ZetaAdmissibleFunction) :
    0 ≤ zetaCompletedZeroSideRe (ZetaAdmissibleFunction.autocorrelation f) ↔
      0 ≤ zetaWeilFormCompleted (ZetaAdmissibleFunction.autocorrelation f) := by
  rw [Boundary.LFunctions.zetaWeilFormCompleted_autocorrelation_eq_zeroSide]

/-- Zero-side nonnegativity implies the zero-side package's autocorrelation Weil positivity. -/
theorem zetaZeroSide_autocorrelation_weilPositivity_of_zeroSide
    (f : ZetaAdmissibleFunction)
    (h : 0 ≤ zetaCompletedZeroSideRe (ZetaAdmissibleFunction.autocorrelation f)) :
    0 ≤ zetaWeilFormCompleted (ZetaAdmissibleFunction.autocorrelation f) := by
  rw [Boundary.LFunctions.zetaWeilFormCompleted_autocorrelation_eq_zeroSide]
  exact h

/-- Each zero-side reflection orbit is finite. -/
theorem zetaZeroSide_orbit_finite (z : CenteredZetaZero) :
    ({x : ℂ | x ∈ orbit z}.Finite) := by
  exact CenteredZetaZero.orbit_finite z

/-- Each zero-side reflection orbit has at most two points. -/
theorem zetaZeroSide_orbit_card_le_two (z : CenteredZetaZero) :
    (orbit z).card ≤ 2 := by
  exact CenteredZetaZero.orbit_card_le_two z

/-- Each zero-side reflection orbit is countable. -/
theorem zetaZeroSide_orbit_countable (z : CenteredZetaZero) :
    ({x : ℂ | x ∈ orbit z}.Countable) := by
  exact (CenteredZetaZero.orbit_finite z).countable

/-- The zero-side package is countable. -/
theorem zetaZeroSide_countable : zetaZeroSide.Countable := by
  simpa [zetaZeroSide_eq_centeredZetaZeros] using centeredZetaZeros_countable

/-- The zero-side package's nontrivial zero locus is countable. -/
theorem zetaZeroSide_nontrivialZeroSet_countable :
    ({z : ℂ | z ≠ -(1 / 2 : ℂ) ∧ z ≠ (1 / 2 : ℂ) ∧ centeredCompletedRiemannZeta z = 0} :
      Set ℂ).Countable := by
  simpa using centeredZetaZeros_nontrivialZeroSet_countable

/-- The zero-side package's nontrivial zero locus has the discrete topology. -/
theorem zetaZeroSide_nontrivialZeroSet_discreteTopology :
    DiscreteTopology
      ({z : ℂ | z ≠ -(1 / 2 : ℂ) ∧ z ≠ (1 / 2 : ℂ) ∧ centeredCompletedRiemannZeta z = 0} :
        Set ℂ) := by
  simpa using centeredZetaZeros_nontrivialZeroSet_discreteTopology

/-- The zero-side reflection orbit is contained in the centered zero set. -/
theorem zetaZeroSide_orbit_subset_centeredZetaZeros (z : CenteredZetaZero) :
    {x : ℂ | x ∈ orbit z} ⊆ zetaZeroSide := by
  intro x hx
  rw [zetaZeroSide_centered]
  exact (CenteredZetaZero.orbit_subset_centeredZetaZeros z) hx

end
end LFunctions
end Boundary
