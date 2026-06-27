import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaExplicitFormulaVerticalChannels.OwnerParts.MellinConjugateLaws
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaExplicitFormulaVerticalChannels.OwnerParts.MellinInversionConjugacy
import Boundary.LFunctions.ZetaTransformCalculus

/-!
# Conditional admissible function conjugacy

This file records the local transport from a Hermitian symmetry hypothesis on
the time-side test function to the corresponding admissible-function statement.
The symmetry is not a property of an arbitrary complex-valued admissible test
function; analytic owner files must provide it when the chosen test class has
that normalization.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open Complex
open Filter
open MeasureTheory
open scoped Topology

namespace AdmissibleConjugacyComposition

/-- A Hermitian time-side hypothesis gives the admissible conjugacy statement. -/
theorem admissible_conjugateSymmetric_composition
    (f : ZetaAdmissibleFunction)
    (hconj : ∀ c : ℝ,
      f.toZetaTestFunction (-c) = star (f.toZetaTestFunction c))
    (c : ℝ) :
    f.toZetaTestFunction (-c) = star (f.toZetaTestFunction c) :=
  hconj c

end AdmissibleConjugacyComposition

end LFunctions
end Boundary
