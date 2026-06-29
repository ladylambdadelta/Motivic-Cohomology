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

This is the independent Cauchy/Laplace analytic leaf for the one-pole branch.
It must be proved directly from the right off-pole affine kernel and contour
shift, not from the downstream residue-free scheduled value. -/
theorem zetaCompletedExplicitFormulaCorrectionRightOnePoleAffineKernel_integral_eq_zero_ownerOnePoleAffine
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) :
    (∫ t : ℝ,
      zetaCompletedExplicitFormulaCorrectionRightOnePoleAffineKernel f F t) =
      0 := by
  sorry

end ZetaAdmissibleFunction

end
end LFunctions
end Boundary
