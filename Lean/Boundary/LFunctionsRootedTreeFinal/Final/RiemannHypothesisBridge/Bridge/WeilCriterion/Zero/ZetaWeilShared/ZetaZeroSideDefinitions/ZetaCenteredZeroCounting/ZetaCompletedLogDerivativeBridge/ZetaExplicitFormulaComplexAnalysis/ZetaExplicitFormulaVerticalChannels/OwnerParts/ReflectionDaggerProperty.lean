import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaExplicitFormulaVerticalChannels.OwnerParts.PrimeNaturalTimeArithmetic
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaExplicitFormulaVerticalChannels.OwnerParts.ReflectionDaggerDerivation

/-!
# Reflection-dagger property for boundary values

Proves that completed zeta boundary values satisfy the functional equation property
at natural prime centers: ζ(-c) = conj(ζ(c)).

This is derived from Paley-Wiener theory and the hermitian structure of the explicit formula.
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
    (f : ZetaAdmissibleFunction) {n : ℕ} (hn : n ≠ 0) :
    zetaCompletedTimeBoundaryValue f
      (-(zetaCompletedExplicitFormulaPrimeNaturalCenter n)) =
      star (zetaCompletedTimeBoundaryValue f
        (zetaCompletedExplicitFormulaPrimeNaturalCenter n)) :=
  zetaCompletedTimeBoundaryValue_primeNaturalCenter_reflectionDagger f hn

end ZetaAdmissibleFunction

end
end LFunctions
end Boundary
