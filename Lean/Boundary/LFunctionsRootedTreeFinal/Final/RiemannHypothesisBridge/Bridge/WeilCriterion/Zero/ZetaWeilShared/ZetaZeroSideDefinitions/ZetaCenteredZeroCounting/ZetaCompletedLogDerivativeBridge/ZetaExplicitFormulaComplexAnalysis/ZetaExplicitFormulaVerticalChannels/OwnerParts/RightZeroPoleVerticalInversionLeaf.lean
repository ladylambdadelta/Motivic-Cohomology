import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaExplicitFormulaVerticalChannels.OwnerParts.RightZeroPoleAffineInversionTransport
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaExplicitFormulaVerticalChannels.OwnerParts.PoleCauchyInversion

/-!
# Right zero-pole vertical inversion leaf

This file specializes the scheduled Cauchy/Laplace inversion value for the
isolated right `s = 0` pole kernel from `PoleCauchyInversion`.  The whole-line
affine-kernel value is then derived from symmetric-window exhaustion and
uniqueness of limits.
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

/-- Scheduled Cauchy/Laplace inversion for the isolated right `s = 0` pole
kernel, delegated to the pole Cauchy inversion owner. -/
theorem zetaCompletedExplicitFormulaCorrectionRightZeroPoleScheduledVerticalInversion_tendsto_value_direct_ownerInversion
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) :
    Tendsto
      (fun u : ℝ =>
        zetaCompletedExplicitFormulaCorrectionRightZeroPoleScheduledVerticalInversion
          f F h u)
      atTop
      (𝓝 (zetaCompletedExplicitFormulaCorrectionRightZeroPoleVerticalInversionValue f)) := by
  exact
    zetaCompletedExplicitFormulaCorrectionRightZeroPoleScheduledVerticalInversion_tendsto_value_ownerCauchyInversion
      f F h

/-- Owner transport leaf: whole-line Cauchy/Laplace inversion value for the
isolated right `s = 0` affine pole kernel. -/
theorem zetaCompletedExplicitFormulaCorrectionRightZeroPoleAffineKernel_integral_eq_value_direct_ownerInversion
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) :
    (∫ t : ℝ,
      zetaCompletedExplicitFormulaCorrectionRightZeroPoleAffineKernel f F t) =
      zetaCompletedExplicitFormulaCorrectionRightZeroPoleVerticalInversionValue f := by
  exact
    zetaCompletedExplicitFormulaCorrectionRightZeroPoleAffineKernel_integral_eq_value_of_scheduledVerticalInversion_tendsto_value_ownerTransport
      f F h
      (zetaCompletedExplicitFormulaCorrectionRightZeroPoleScheduledVerticalInversion_tendsto_value_direct_ownerInversion
        f F h)

/-- Owner transport leaf: whole-line Cauchy/Laplace inversion value for the
isolated right `s = 0` affine pole kernel. -/
theorem zetaCompletedExplicitFormulaCorrectionRightZeroPoleAffineKernel_integral_eq_value_ownerInversion
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) :
    (∫ t : ℝ,
      zetaCompletedExplicitFormulaCorrectionRightZeroPoleAffineKernel f F t) =
      zetaCompletedExplicitFormulaCorrectionRightZeroPoleVerticalInversionValue f := by
  exact
    zetaCompletedExplicitFormulaCorrectionRightZeroPoleAffineKernel_integral_eq_value_direct_ownerInversion
      f F h

/-- Owner scheduled Cauchy/Laplace inversion for the isolated right `s = 0`
pole kernel. -/
theorem zetaCompletedExplicitFormulaCorrectionRightZeroPoleScheduledVerticalInversion_tendsto_value_ownerInversion
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) :
    Tendsto
      (fun u : ℝ =>
        zetaCompletedExplicitFormulaCorrectionRightZeroPoleScheduledVerticalInversion
          f F h u)
      atTop
      (𝓝 (zetaCompletedExplicitFormulaCorrectionRightZeroPoleVerticalInversionValue f)) := by
  exact
    zetaCompletedExplicitFormulaCorrectionRightZeroPoleScheduledVerticalInversion_tendsto_value_direct_ownerInversion
      f F h

end ZetaAdmissibleFunction

end
end LFunctions
end Boundary
