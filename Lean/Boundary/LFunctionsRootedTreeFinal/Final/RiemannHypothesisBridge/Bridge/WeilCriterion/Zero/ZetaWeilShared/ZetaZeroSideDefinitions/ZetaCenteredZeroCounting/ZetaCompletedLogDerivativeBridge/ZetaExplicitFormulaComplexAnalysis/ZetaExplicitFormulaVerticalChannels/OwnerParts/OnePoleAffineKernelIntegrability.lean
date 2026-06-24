import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaExplicitFormulaVerticalChannels.OwnerParts.AffineKernelMajorantPackage
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaExplicitFormulaVerticalChannels.OwnerParts.OnePoleAffineKernelBounds

/-!
# Integrability of isolated one-pole affine kernels
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

theorem zetaCompletedExplicitFormulaCorrectionRightOnePoleAffineKernel_integrable_ownerBounds
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) :
    Integrable
      (zetaCompletedExplicitFormulaCorrectionRightOnePoleAffineKernel f F)
      (volume : Measure ℝ) :=
  ({
      majorant :=
        fun t : ℝ =>
          zetaCompletedExplicitFormulaCorrectionRightOnePoleAffineKernelMajorant
            f F h 2 t
      integrable_majorant :=
        zetaCompletedExplicitFormulaCorrectionRightOnePoleAffineKernelMajorant_two_integrable
          f F h
      stronglyMeasurable_kernel :=
        zetaCompletedExplicitFormulaCorrectionRightOnePoleAffineKernel_aestronglyMeasurable
          f F h
      norm_le_majorant :=
        Filter.Eventually.of_forall
          (fun t : ℝ =>
            zetaCompletedExplicitFormulaCorrectionRightOnePoleAffineKernel_norm_le_majorant
              f F h 2 t)
    } :
      ExplicitFormulaAffineKernelMajorantPackage
        (zetaCompletedExplicitFormulaCorrectionRightOnePoleAffineKernel f F)).integrable

theorem zetaCompletedExplicitFormulaCorrectionLeftOnePoleAffineKernel_integrable_ownerBounds
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) :
    Integrable
      (zetaCompletedExplicitFormulaCorrectionLeftOnePoleAffineKernel f F)
      (volume : Measure ℝ) :=
  ({
      majorant :=
        fun t : ℝ =>
          zetaCompletedExplicitFormulaCorrectionLeftOnePoleAffineKernelMajorant
            f F h 2 t
      integrable_majorant :=
        zetaCompletedExplicitFormulaCorrectionLeftOnePoleAffineKernelMajorant_two_integrable
          f F h
      stronglyMeasurable_kernel :=
        zetaCompletedExplicitFormulaCorrectionLeftOnePoleAffineKernel_aestronglyMeasurable
          f F h
      norm_le_majorant :=
        Filter.Eventually.of_forall
          (fun t : ℝ =>
            zetaCompletedExplicitFormulaCorrectionLeftOnePoleAffineKernel_norm_le_majorant
              f F h 2 t)
    } :
      ExplicitFormulaAffineKernelMajorantPackage
        (zetaCompletedExplicitFormulaCorrectionLeftOnePoleAffineKernel f F)).integrable

end ZetaAdmissibleFunction

end
end LFunctions
end Boundary
