import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaExplicitFormulaVerticalChannels.OwnerParts.PrimeNaturalTimeArithmetic
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaExplicitFormulaVerticalChannels.OwnerParts.ReflectionDaggerDerivation

/-!
# Conditional reflection-dagger property for boundary values

This file re-exports the local transport from a supplied Hermitian test-function
symmetry to the boundary-value reflection property at natural prime centers.
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

/-- Functional equation property: completed zeta boundary values at natural prime centers
satisfy conjugate symmetry under negation. This follows from Paley-Wiener hermitian
properties of the explicit formula's contour integrals and their Mellin inversions. -/
theorem zetaCompletedTimeBoundaryValue_primeNaturalCenter_reflectionDagger
    (f : ZetaAdmissibleFunction)
    (hconj : ∀ c : ℝ,
      f.toZetaTestFunction (-c) = star (f.toZetaTestFunction c))
    {n : ℕ} (hn : n ≠ 0) :
    zetaCompletedTimeBoundaryValue f
      (-(zetaCompletedExplicitFormulaPrimeNaturalCenter n)) =
      star (zetaCompletedTimeBoundaryValue f
        (zetaCompletedExplicitFormulaPrimeNaturalCenter n)) :=
  zetaCompletedTimeBoundaryValue_primeNaturalCenter_reflectionDagger_of_conj
    f hconj hn

end ZetaAdmissibleFunction

end
end LFunctions
end Boundary
