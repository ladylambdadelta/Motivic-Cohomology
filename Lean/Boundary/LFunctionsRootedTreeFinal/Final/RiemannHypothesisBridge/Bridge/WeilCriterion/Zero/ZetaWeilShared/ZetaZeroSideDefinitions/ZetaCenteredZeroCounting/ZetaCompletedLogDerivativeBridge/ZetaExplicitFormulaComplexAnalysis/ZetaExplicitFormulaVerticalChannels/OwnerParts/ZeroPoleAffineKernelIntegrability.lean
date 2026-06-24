import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaExplicitFormulaVerticalChannels.OwnerParts.AffineKernelMajorantPackage
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaExplicitFormulaVerticalChannels.OwnerParts.ZeroPoleAffineKernelBounds

/-!
# Integrability of isolated zero-pole affine kernels

This file owns the measure-theoretic transport from the left and right
zero-pole affine majorants to whole-line integrability of the kernels.
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

/-- Integrability of the isolated right zero-pole affine kernel. -/
theorem zetaCompletedExplicitFormulaCorrectionRightZeroPoleAffineKernel_integrable_ownerBounds
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) :
    Integrable
      (zetaCompletedExplicitFormulaCorrectionRightZeroPoleAffineKernel f F)
      (volume : Measure ℝ) :=
  ({
      majorant :=
        fun t : ℝ =>
          zetaCompletedExplicitFormulaCorrectionRightZeroPoleAffineKernelMajorant
            f F h 2 t
      integrable_majorant :=
        zetaCompletedExplicitFormulaCorrectionRightZeroPoleAffineKernelMajorant_two_integrable
          f F h
      stronglyMeasurable_kernel :=
        zetaCompletedExplicitFormulaCorrectionRightZeroPoleAffineKernel_aestronglyMeasurable
          f F h
      norm_le_majorant :=
        Filter.Eventually.of_forall
          (fun t : ℝ =>
            zetaCompletedExplicitFormulaCorrectionRightZeroPoleAffineKernel_norm_le_majorant
              f F h 2 t)
    } :
      ExplicitFormulaAffineKernelMajorantPackage
        (zetaCompletedExplicitFormulaCorrectionRightZeroPoleAffineKernel f F)).integrable

/-- Integrability of the isolated left zero-pole affine kernel. -/
theorem zetaCompletedExplicitFormulaCorrectionLeftZeroPoleAffineKernel_integrable_ownerBounds
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) :
    Integrable
      (zetaCompletedExplicitFormulaCorrectionLeftZeroPoleAffineKernel f F)
      (volume : Measure ℝ) :=
  ({
      majorant :=
        fun t : ℝ =>
          zetaCompletedExplicitFormulaCorrectionLeftZeroPoleAffineKernelMajorant
            f F h 2 t
      integrable_majorant :=
        zetaCompletedExplicitFormulaCorrectionLeftZeroPoleAffineKernelMajorant_two_integrable
          f F h
      stronglyMeasurable_kernel :=
        zetaCompletedExplicitFormulaCorrectionLeftZeroPoleAffineKernel_aestronglyMeasurable
          f F h
      norm_le_majorant :=
        Filter.Eventually.of_forall
          (fun t : ℝ =>
            zetaCompletedExplicitFormulaCorrectionLeftZeroPoleAffineKernel_norm_le_majorant
              f F h 2 t)
    } :
      ExplicitFormulaAffineKernelMajorantPackage
        (zetaCompletedExplicitFormulaCorrectionLeftZeroPoleAffineKernel f F)).integrable

end ZetaAdmissibleFunction

end
end LFunctions
end Boundary
