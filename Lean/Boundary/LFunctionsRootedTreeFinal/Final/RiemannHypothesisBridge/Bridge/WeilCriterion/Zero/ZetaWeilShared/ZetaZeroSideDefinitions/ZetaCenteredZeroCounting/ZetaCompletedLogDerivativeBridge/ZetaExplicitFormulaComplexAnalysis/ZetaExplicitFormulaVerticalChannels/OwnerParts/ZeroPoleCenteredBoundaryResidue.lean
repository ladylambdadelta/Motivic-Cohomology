import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaExplicitFormulaVerticalChannels.OwnerParts.ZeroPoleCenteredCauchyValue

/-!
# Shifted and centered zero-pole values

This file records the normalization boundary between the shifted local
zero-pole residue stack and the centered right zero-pole inversion value.

The existing project rectangle boundary is built from the shifted integrand
`(-1 / s) * Φ_f (s - 1 / 2)`, so its local residue at `s = 0` samples
`Φ_f (-1/2)`.  The centered vertical-inversion value is a different target,
normalized at `Φ_f 0`, and is owned by `ZeroPoleCenteredCauchyValue`.
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

/-- Compatibility name for unfolding the centered right zero-pole inversion
value.  This is not a statement about the shifted project rectangle boundary. -/
theorem zetaCompletedExplicitFormulaCorrectionCenteredZeroPoleBoundaryValue_eq
    (f : ZetaAdmissibleFunction) :
    zetaCompletedExplicitFormulaCorrectionCenteredZeroPoleBoundaryValue f =
      1 / (1 / 2 : ℂ) * zetaCompletedExplicitFormulaPhi f 0 := by
  exact
    zetaCompletedExplicitFormulaCorrectionCenteredZeroPoleBoundaryValue_eq_centeredPolePhi
      f

end ZetaAdmissibleFunction

end
end LFunctions
end Boundary
