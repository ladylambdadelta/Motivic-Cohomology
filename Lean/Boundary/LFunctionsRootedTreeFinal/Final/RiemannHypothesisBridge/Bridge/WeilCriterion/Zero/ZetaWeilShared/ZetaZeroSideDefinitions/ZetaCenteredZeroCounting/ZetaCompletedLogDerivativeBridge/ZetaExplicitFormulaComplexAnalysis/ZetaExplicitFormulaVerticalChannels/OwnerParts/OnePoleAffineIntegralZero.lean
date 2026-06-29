import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaExplicitFormulaVerticalChannels.OwnerParts.OnePoleAffineVerticalTransport
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaExplicitFormulaVerticalChannels.OwnerParts.ScheduledKernelLimitTransport

/-!
# Right one-pole affine zero value

This file owns the non-circular analytic input needed before the one-pole
residue-tail estimate: the right `s = 1` correction affine kernel has
whole-line integral `0`.

The zero value is a contour-shift/Cauchy theorem for the isolated right
one-pole correction kernel.  It must not be derived from
`OnePoleResidueTailEstimate`, `OnePoleResidueTransport`, or
`RightOnePoleOffPoleDecayEstimate`; those files consume this value.
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

/-- The right `s = 1` correction affine kernel has zero whole-line value.

The analytic input is the scheduled residue-free Cauchy value owned in
`OnePoleResidueFreeCauchyValue`; this theorem only transports that scheduled
value to the whole-line affine integral by integrability and exhaustion. -/
theorem zetaCompletedExplicitFormulaCorrectionRightOnePoleAffineKernel_integral_eq_zero_ownerOnePoleAffine
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) :
    (∫ t : ℝ,
      zetaCompletedExplicitFormulaCorrectionRightOnePoleAffineKernel f F t) =
      0 := by
  exact
    explicitFormulaScheduledRectangleWindowIntegral_eq_of_tendsto_value
      F
      h.height_schedule.height
      (zetaCompletedExplicitFormulaCorrectionRightOnePoleAffineKernel f F)
      0
      h.height_schedule.cofinal
      (zetaCompletedExplicitFormulaCorrectionRightOnePoleAffineKernel_integrable_ownerBounds
        f F h)
      (zetaCompletedExplicitFormulaCorrectionRightOnePoleAffineKernel_scheduledWindow_tendsto_zero_ownerResidueFreeCauchy
        f F h)

end ZetaAdmissibleFunction

end
end LFunctions
end Boundary
