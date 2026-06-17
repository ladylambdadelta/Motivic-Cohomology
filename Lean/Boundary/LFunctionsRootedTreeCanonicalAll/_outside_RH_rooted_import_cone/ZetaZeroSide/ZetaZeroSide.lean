import Boundary.LFunctionsRootedTreeCanonicalAll.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaZeroSideDefinitions
import Boundary.LFunctionsRootedTreeCanonicalAll.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCenteredZeroCounting
import Boundary.LFunctionsRootedTreeCanonicalAll.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroLocalFiniteness.ZetaZeroOrbitIsolation.ZetaZeroOrbitIsolation
import Boundary.LFunctionsRootedTreeCanonicalAll.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaZeroKreinGram.WeilCriterion.WeilCriterion
import Boundary.LFunctionsRootedTreeCanonicalAll._outside_RH_rooted_import_cone.ZetaCriterion.ZetaCriterion

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

/-- The zero-side package's Weil positivity on the convolution-autocorrelation surface is the
zero-side real part statement. -/
theorem zetaZeroSide_autocorrelation_zeroSide_eq_weil
    (f : ZetaAdmissibleFunction) :
    zetaWeilFormCompleted (ZetaAdmissibleFunction.convolutionAutocorrelation f) =
      zetaCompletedZeroSideRe (ZetaAdmissibleFunction.convolutionAutocorrelation f) := by
  exact Boundary.LFunctions.zetaWeilFormCompleted_convolutionAutocorrelation_eq_zeroSide f

/-- Convolution-autocorrelation-generated probes satisfy the zero-side package Weil positivity
predicate, assuming real boundary nonnegativity on autocorrelation seeds. -/
theorem zetaZeroSide_autocorrelation_weilPositivity_predicate :
    (∀ f : ZetaAdmissibleFunction,
      0 ≤
        ZetaAdmissibleFunction.zetaCompletedExplicitFormulaAutocorrelationBoundaryKreinSum
          f) →
    ZetaAutocorrelationWeilPositivity := by
  intro hboundaryAll
  exact zetaCriterion_autocorrelation_weilPositivity_predicate hboundaryAll

/-- The zero-side package's convolution-autocorrelation Weil positivity predicate is pointwise
nonnegativity. -/
theorem zetaZeroSide_autocorrelation_weilPositivity_iff_predicate :
    ZetaAutocorrelationWeilPositivity ↔
      ∀ φ : ZetaProbe, IsZetaAutocorrelationProbe φ →
        0 ≤ zetaWeilFormCompleted φ := by
  rfl

/-- The raw zero-side Weil positivity predicate is pointwise nonnegativity. This is only the
definition of the raw predicate, not a proof that the predicate holds for all probes. -/
theorem zetaZeroSide_weilPositivity_iff :
    ZetaWeilPositivity ↔
      ∀ φ : ZetaProbe, 0 ≤ zetaWeilFormCompleted φ := by
  rfl

/-- Pointwise nonnegativity is the raw zero-side Weil positivity predicate. This records the
predicate shape without asserting raw all-probe positivity. -/
theorem zetaZeroSide_weilPositivity_iff' :
    (∀ φ : ZetaProbe, 0 ≤ zetaWeilFormCompleted φ) ↔ ZetaWeilPositivity := by
  rfl

/-- Convolution-autocorrelation-generated probes have nonnegative zero-side real sum in the
package surface. -/
theorem zetaZeroSide_autocorrelation_zeroSide_nonnegative
    (f : ZetaAdmissibleFunction)
    (hboundary :
      0 ≤
        ZetaAdmissibleFunction.zetaCompletedExplicitFormulaAutocorrelationBoundaryKreinSum
          f) :
    0 ≤ zetaCompletedZeroSideRe (ZetaAdmissibleFunction.convolutionAutocorrelation f) := by
  exact zetaCriterion_convolutionAutocorrelation_zeroSide_nonnegative f hboundary

/-- Convolution-autocorrelation-generated probes satisfy the zero-side package's Weil positivity. -/
theorem zetaZeroSide_autocorrelation_weilPositivity
    (f : ZetaAdmissibleFunction)
    (hboundary :
      0 ≤
        ZetaAdmissibleFunction.zetaCompletedExplicitFormulaAutocorrelationBoundaryKreinSum
          f) :
    0 ≤ zetaWeilFormCompleted (ZetaAdmissibleFunction.convolutionAutocorrelation f) := by
  exact zetaCriterion_autocorrelation_weilPositivity f hboundary

/-- The zero-side package's convolution-autocorrelation Weil positivity is the zero-side
nonnegativity statement. -/
theorem zetaZeroSide_autocorrelation_weilPositivity_iff
    (f : ZetaAdmissibleFunction) :
    0 ≤ zetaWeilFormCompleted (ZetaAdmissibleFunction.convolutionAutocorrelation f) ↔
      0 ≤ zetaCompletedZeroSideRe (ZetaAdmissibleFunction.convolutionAutocorrelation f) := by
  exact
    (zetaZeroSide_autocorrelation_zeroSide_eq_weil f).symm ▸ Iff.rfl

/-- The zero-side package's zero-side nonnegativity statement is the convolution-autocorrelation
Weil positivity. -/
theorem zetaZeroSide_autocorrelation_weilPositivity_iff'
    (f : ZetaAdmissibleFunction) :
    0 ≤ zetaCompletedZeroSideRe (ZetaAdmissibleFunction.convolutionAutocorrelation f) ↔
      0 ≤ zetaWeilFormCompleted (ZetaAdmissibleFunction.convolutionAutocorrelation f) := by
  exact
    (zetaZeroSide_autocorrelation_zeroSide_eq_weil f) ▸ Iff.rfl

/-- Zero-side nonnegativity implies the zero-side package's convolution-autocorrelation Weil
positivity. -/
theorem zetaZeroSide_autocorrelation_weilPositivity_of_zeroSide
    (f : ZetaAdmissibleFunction)
    (h : 0 ≤ zetaCompletedZeroSideRe (ZetaAdmissibleFunction.convolutionAutocorrelation f)) :
    0 ≤ zetaWeilFormCompleted (ZetaAdmissibleFunction.convolutionAutocorrelation f) := by
  exact (zetaZeroSide_autocorrelation_zeroSide_eq_weil f).symm ▸ h

/-- Each zero-side reflection orbit is finite. -/
theorem zetaZeroSide_orbit_finite (z : CenteredZetaZero) :
    ({x : ℂ | x ∈ CenteredZetaZero.orbit z}.Finite) := by
  exact CenteredZetaZero.orbit_finite z

/-- Each zero-side reflection orbit has at most two points. -/
theorem zetaZeroSide_orbit_card_le_two (z : CenteredZetaZero) :
    (CenteredZetaZero.orbit z).card ≤ 2 := by
  exact CenteredZetaZero.orbit_card_le_two z

/-- Each zero-side reflection orbit is countable. -/
theorem zetaZeroSide_orbit_countable (z : CenteredZetaZero) :
    ({x : ℂ | x ∈ CenteredZetaZero.orbit z}.Countable) := by
  exact (CenteredZetaZero.orbit_finite z).countable

/-- The zero-side package is countable. -/
theorem zetaZeroSide_countable : zetaZeroSide.Countable := by
  exact centeredZetaZeros_countable

/-- The zero-side package's nontrivial zero locus is countable. -/
theorem zetaZeroSide_nontrivialZeroSet_countable :
    ({z : ℂ | z ≠ -(1 / 2 : ℂ) ∧ z ≠ (1 / 2 : ℂ) ∧ centeredCompletedRiemannZeta z = 0} :
      Set ℂ).Countable := by
  exact centeredZetaZeros_nontrivialZeroSet_countable

/-- The zero-side package's nontrivial zero locus has the discrete topology. -/
theorem zetaZeroSide_nontrivialZeroSet_discreteTopology :
    DiscreteTopology
      ({z : ℂ | z ≠ -(1 / 2 : ℂ) ∧ z ≠ (1 / 2 : ℂ) ∧ centeredCompletedRiemannZeta z = 0} :
        Set ℂ) := by
  exact centeredZetaZeros_nontrivialZeroSet_discreteTopology_of_subset

/-- The zero-side reflection orbit is contained in the centered zero set. -/
theorem zetaZeroSide_orbit_subset_centeredZetaZeros (z : CenteredZetaZero) :
    {x : ℂ | x ∈ CenteredZetaZero.orbit z} ⊆ zetaZeroSide := by
  intro x hx
  exact (CenteredZetaZero.orbit_subset_centeredZetaZeros z) hx

end
end LFunctions
end Boundary
