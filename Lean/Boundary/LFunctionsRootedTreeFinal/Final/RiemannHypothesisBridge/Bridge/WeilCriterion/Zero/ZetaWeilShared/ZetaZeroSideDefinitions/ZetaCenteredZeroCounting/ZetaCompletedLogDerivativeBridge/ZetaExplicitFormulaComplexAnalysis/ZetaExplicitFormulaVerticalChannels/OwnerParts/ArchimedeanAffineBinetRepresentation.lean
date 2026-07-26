import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaExplicitFormulaVerticalChannels.OwnerParts.ArchimedeanGammaBinetTransport
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaExplicitFormulaVerticalChannels.OwnerParts.ArchimedeanWeilFunctional

/-!
# Affine Binet representations

The Binet main and differentiated remainder are kept coupled.  Their sum is
the affine Gamma-factor functional; neither summand is assigned a separate
closed value.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open Complex
open MeasureTheory

namespace ZetaAdmissibleFunction

/-- The coupled right Binet transform is exactly the right affine
archimedean functional. -/
theorem zetaCompletedArchimedeanRightBinetFullTransform_eq_affineFunctional
    (f : ZetaAdmissibleFunction)
    (F : ExplicitFormulaVerticallyRegularContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F.toContourFamily) :
    zetaCompletedExplicitFormulaArchimedeanRightBinetFullTransformIntegral
        f F.toContourFamily =
      zetaCompletedArchimedeanRightAffineFunctional f F.toContourFamily := by
  have mainIntegrable :
      Integrable
        (zetaCompletedExplicitFormulaArchimedeanRightBinetMainKernel
          f F.toContourFamily)
        (volume : Measure ℝ) :=
    zetaCompletedExplicitFormulaArchimedeanRightBinetMainKernel_integrable
      f F.toContourFamily h
  have remainderIntegrable :
      Integrable
        (zetaCompletedExplicitFormulaArchimedeanRightBinetRemainderKernel
          f F.toContourFamily)
        (volume : Measure ℝ) :=
    zetaCompletedExplicitFormulaArchimedeanRightBinetRemainderKernel_integrable
      f F.toContourFamily h
  have splitIntegral :
      (∫ t : ℝ,
          zetaCompletedExplicitFormulaArchimedeanRightBinetMainKernel
              f F.toContourFamily t +
            zetaCompletedExplicitFormulaArchimedeanRightBinetRemainderKernel
              f F.toContourFamily t) =
        zetaCompletedExplicitFormulaArchimedeanRightBinetFullTransformIntegral
          f F.toContourFamily := by
    exact Eq.trans
      (integral_add mainIntegrable remainderIntegrable)
      (zetaCompletedExplicitFormulaArchimedeanRightBinetFullTransformIntegral_eq
        f F.toContourFamily).symm
  have affineIntegral :
      zetaCompletedArchimedeanRightAffineFunctional f F.toContourFamily =
        ∫ t : ℝ,
          zetaCompletedExplicitFormulaArchimedeanRightBinetMainKernel
              f F.toContourFamily t +
            zetaCompletedExplicitFormulaArchimedeanRightBinetRemainderKernel
              f F.toContourFamily t := by
    exact integral_congr_ae
      (Filter.Eventually.of_forall
        (fun t : ℝ =>
          zetaCompletedExplicitFormulaArchimedeanRightAffineKernel_eq_binetMain_add_remainder
            f F.toContourFamily t))
  exact Eq.trans splitIntegral.symm affineIntegral.symm

/-- The coupled left Binet transform is exactly the left affine
archimedean functional. -/
theorem zetaCompletedArchimedeanLeftBinetFullTransform_eq_affineFunctional
    (f : ZetaAdmissibleFunction)
    (F : ExplicitFormulaVerticallyRegularContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F.toContourFamily) :
    zetaCompletedExplicitFormulaArchimedeanLeftBinetFullTransformIntegral
        f F.toContourFamily =
      zetaCompletedArchimedeanLeftAffineFunctional f F.toContourFamily := by
  have gammaRegular :
      zetaCompletedExplicitFormulaLeftAffineLineGammaRegular F.toContourFamily :=
    zetaCompletedExplicitFormulaLeftAffineLineGammaRegular_of_verticallyRegular F
  have mainIntegrable :
      Integrable
        (zetaCompletedExplicitFormulaArchimedeanLeftBinetMainKernel
          f F.toContourFamily)
        (volume : Measure ℝ) :=
    zetaCompletedExplicitFormulaArchimedeanLeftBinetMainKernel_integrable
      f F.toContourFamily h gammaRegular
  have remainderIntegrable :
      Integrable
        (zetaCompletedExplicitFormulaArchimedeanLeftBinetRemainderKernel
          f F.toContourFamily)
        (volume : Measure ℝ) :=
    zetaCompletedExplicitFormulaArchimedeanLeftBinetRemainderKernel_integrable
      f F.toContourFamily h gammaRegular
  have splitIntegral :
      (∫ t : ℝ,
          zetaCompletedExplicitFormulaArchimedeanLeftBinetMainKernel
              f F.toContourFamily t +
            zetaCompletedExplicitFormulaArchimedeanLeftBinetRemainderKernel
              f F.toContourFamily t) =
        zetaCompletedExplicitFormulaArchimedeanLeftBinetFullTransformIntegral
          f F.toContourFamily := by
    exact Eq.trans
      (integral_add mainIntegrable remainderIntegrable)
      (zetaCompletedExplicitFormulaArchimedeanLeftBinetFullTransformIntegral_eq
        f F.toContourFamily).symm
  have affineIntegral :
      zetaCompletedArchimedeanLeftAffineFunctional f F.toContourFamily =
        ∫ t : ℝ,
          zetaCompletedExplicitFormulaArchimedeanLeftBinetMainKernel
              f F.toContourFamily t +
            zetaCompletedExplicitFormulaArchimedeanLeftBinetRemainderKernel
              f F.toContourFamily t := by
    exact integral_congr_ae
      (Filter.Eventually.of_forall
        (fun t : ℝ =>
          zetaCompletedExplicitFormulaArchimedeanLeftAffineKernel_eq_binetMain_add_remainder
            f F.toContourFamily gammaRegular t))
  exact Eq.trans splitIntegral.symm affineIntegral.symm

end ZetaAdmissibleFunction

end
end LFunctions
end Boundary
