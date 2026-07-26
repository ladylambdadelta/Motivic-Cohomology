import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaExplicitFormulaVerticalChannels.OwnerParts.AffineKernelMajorantPackage
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaExplicitFormulaVerticalChannels.OwnerParts.AffineLineMeasurability
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaExplicitFormulaVerticalChannels.OwnerParts.AffinePhiDecay
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaExplicitFormulaVerticalChannels.OwnerParts.InverseGammaFactorBounds
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaExplicitFormulaVerticalChannels.OwnerParts.ScheduledKernelLimitTransport
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaExplicitFormulaVerticalChannels.OwnerParts.SymmetricIntegralExhaustion
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ClassicalAnalysis.GammaBinetStirling.Owner

/-!
# Inverse-Gamma affine-kernel estimate

This file owns the analytic convergence of the right-minus-left inverse-Gamma
completion affine-kernel integrals.
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

/-- Pointwise bridge from the project `zpow` convention for third-order
Japanese brackets to mathlib's `rpow` convention. -/
theorem realLine_one_add_norm_zpow_three_eq_rpow_three
    (t : ℝ) :
    (1 + ‖t‖) ^ (-(3 : ℤ)) =
      (1 + ‖t‖) ^ (-(3 : ℝ)) := by
  have hexp :
      ((-(3 : ℤ) : ℤ) : ℝ) = -(3 : ℝ) :=
    Int.cast_neg 3
  exact
    Eq.trans
      (Real.rpow_intCast (1 + ‖t‖) (-(3 : ℤ))).symm
      (congrArg (fun r : ℝ => (1 + ‖t‖) ^ r) hexp)

/-- Strong measurability of the right inverse-Gamma affine kernel. -/
theorem zetaCompletedExplicitFormulaInverseGammaRightAffineKernel_aestronglyMeasurable
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) :
    AEStronglyMeasurable
      (zetaCompletedExplicitFormulaInverseGammaRightAffineKernel f F)
      (volume : Measure ℝ) :=
  (zetaCompletedExplicitFormulaInverseGammaLogDeriv_rightAffineLine_aestronglyMeasurable
    F).mul
    (zetaCompletedExplicitFormulaPhi_rightCenteredAffineLine_aestronglyMeasurable
      f F h)

/-- Under the parameter-level Gamma-regularity condition, the left
inverse-Gamma affine kernel is strongly measurable. -/
theorem zetaCompletedExplicitFormulaInverseGammaLeftAffineKernel_aestronglyMeasurable_of_gammaRegular
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F)
    (hregular : zetaCompletedExplicitFormulaLeftAffineLineGammaRegular F) :
    AEStronglyMeasurable
      (zetaCompletedExplicitFormulaInverseGammaLeftAffineKernel f F)
      (volume : Measure ℝ) :=
  (zetaCompletedExplicitFormulaInverseGammaLogDeriv_leftAffineLine_aestronglyMeasurable_of_gammaRegular
    F hregular).mul
    (zetaCompletedExplicitFormulaPhi_leftCenteredAffineLine_aestronglyMeasurable
      f F h)

end ZetaAdmissibleFunction

end
end LFunctions
end Boundary
