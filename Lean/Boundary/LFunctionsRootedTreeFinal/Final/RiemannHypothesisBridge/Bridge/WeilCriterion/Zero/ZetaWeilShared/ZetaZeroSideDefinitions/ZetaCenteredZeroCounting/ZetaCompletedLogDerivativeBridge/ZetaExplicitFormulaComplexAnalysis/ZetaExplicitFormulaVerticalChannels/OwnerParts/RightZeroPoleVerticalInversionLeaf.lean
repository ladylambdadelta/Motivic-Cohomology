import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaExplicitFormulaVerticalChannels.OwnerParts.RightZeroPoleAffineInversionTransport
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaExplicitFormulaVerticalChannels.OwnerParts.RightZeroPoleLocalCauchyValue

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
kernel in the one-sided projection normalization. -/
theorem zetaCompletedExplicitFormulaCorrectionRightZeroPoleScheduledVerticalInversion_tendsto_projection_direct_ownerInversion
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) :
    Tendsto
      (fun u : ℝ =>
        zetaCompletedExplicitFormulaCorrectionRightZeroPoleScheduledVerticalInversion
          f F h u)
      atTop
      (𝓝
        (Boundary.zetaLaplaceTransform_rightZeroPoleCauchyProjectionValue
          f.toZetaTestFunction' F.c)) := by
  exact
    zetaCompletedExplicitFormulaCorrectionRightZeroPoleScheduledVerticalInversion_tendsto_projection_directOffPoleCauchy
      f F h

/-- Whole-line Cauchy/Laplace inversion value for the isolated right `s = 0`
affine pole kernel in the one-sided projection normalization. -/
theorem zetaCompletedExplicitFormulaCorrectionRightZeroPoleAffineKernel_integral_eq_projection_direct_ownerInversion
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily) :
    (∫ t : ℝ,
      zetaCompletedExplicitFormulaCorrectionRightZeroPoleAffineKernel f F t) =
      Boundary.zetaLaplaceTransform_rightZeroPoleCauchyProjectionValue
        f.toZetaTestFunction' F.c := by
  exact
    zetaCompletedExplicitFormulaCorrectionRightZeroPoleAffineKernel_integral_eq_projection_directOffPoleCauchy
      f F

end ZetaAdmissibleFunction

end
end LFunctions
end Boundary
