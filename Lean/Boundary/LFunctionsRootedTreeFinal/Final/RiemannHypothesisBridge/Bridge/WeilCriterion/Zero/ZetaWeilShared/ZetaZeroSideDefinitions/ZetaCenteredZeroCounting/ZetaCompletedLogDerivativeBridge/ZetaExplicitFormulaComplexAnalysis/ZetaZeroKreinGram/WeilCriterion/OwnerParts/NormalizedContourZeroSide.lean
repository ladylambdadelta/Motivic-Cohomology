import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaZeroKreinGram.WeilCriterion.OwnerParts.CanonicalAnalyticInputs
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaZeroKreinGram.WeilCriterion.OwnerParts.AutocorrelationAnalyticPackage
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaExplicitFormulaVerticalChannels.Owner

/-!
# Normalized contour to completed zero side
-/

namespace Boundary
namespace LFunctions

noncomputable section

open Filter
open scoped Topology

/-- A scheduled standard vertical limit and the normalized residue limit identify
the residue-normalized standard contour boundary with the completed zero side. -/
theorem zetaCompletedExplicitFormulaResidueNormalizedStandardContourBoundarySum_eq_zeroSide_of_verticalLimit
    (f : ZetaAdmissibleFunction)
    (hPhi : ZetaAdmissibleFunction.ZetaPhiAnalyticControl
      (ZetaAdmissibleFunction.convolutionAutocorrelation f))
    (hLog : ZetaAdmissibleFunction.CompletedZetaNegLogDerivControl
      (ZetaAdmissibleFunction.convolutionAutocorrelation f))
    (zeroSideSummable :
      Summable
        (fun rho : {rho : ℂ // ZetaCompletedZero rho} =>
          zetaZeroSideContribution (rho : ℂ)
            (ZetaAdmissibleFunction.convolutionAutocorrelation f)))
    (verticalLimit :
      let probe : ZetaAdmissibleFunction :=
        ZetaAdmissibleFunction.convolutionAutocorrelation f
      let family : ZetaAdmissibleFunction.ExplicitFormulaContourFamily :=
        ZetaAdmissibleFunction.zetaCompletedExplicitFormula_autocorrelation_contourFamily f
      let analyticPackage :
          ZetaAdmissibleFunction.ExplicitFormulaFamilyAnalyticPackage probe family :=
          ZetaAdmissibleFunction.CleanAutocorrelationAnalyticPackage.zetaCompletedExplicitFormula_autocorrelation_familyAnalyticPackage
          f
          (ZetaAdmissibleFunction.zetaCompletedExplicitFormulaAutocorrelationHorizontalAvoidingSchedule f)
          hPhi
          hLog
      Tendsto
        (fun u : ℝ =>
          ZetaAdmissibleFunction.zetaCompletedExplicitFormulaRightLineIntegral probe
              (family.rectangle (analyticPackage.height_schedule.height u)) -
            ZetaAdmissibleFunction.zetaCompletedExplicitFormulaLeftLineIntegral probe
              (family.rectangle (analyticPackage.height_schedule.height u)))
        atTop
        (𝓝
          (ZetaAdmissibleFunction.zetaCompletedExplicitFormulaStandardContourBoundarySum
            probe))) :
    ZetaAdmissibleFunction.zetaCompletedExplicitFormulaResidueNormalizedStandardContourBoundarySum
        (ZetaAdmissibleFunction.convolutionAutocorrelation f) =
      ZetaAdmissibleFunction.zetaCompletedZeroSideComplex
        (ZetaAdmissibleFunction.convolutionAutocorrelation f) :=
  let probe : ZetaAdmissibleFunction :=
    ZetaAdmissibleFunction.convolutionAutocorrelation f
  let family : ZetaAdmissibleFunction.ExplicitFormulaContourFamily :=
    ZetaAdmissibleFunction.zetaCompletedExplicitFormula_autocorrelation_contourFamily f
  let analyticPackage :
      ZetaAdmissibleFunction.ExplicitFormulaFamilyAnalyticPackage probe family :=
    ZetaAdmissibleFunction.CleanAutocorrelationAnalyticPackage.zetaCompletedExplicitFormula_autocorrelation_familyAnalyticPackage
      f
      (ZetaAdmissibleFunction.zetaCompletedExplicitFormulaAutocorrelationHorizontalAvoidingSchedule f)
      hPhi
      hLog
  let stripData := analyticPackage.scheduled_horizontalFamilyZeroExcisedStrip
  match stripData with
  | ⟨carrier, stripSpec⟩ =>
      ZetaAdmissibleFunction.zetaCompletedExplicitFormulaResidueNormalizedStandardContourBoundarySum_eq_zeroSideComplex
        probe family analyticPackage carrier stripSpec.1 stripSpec.2 zeroSideSummable verticalLimit

end

end LFunctions
end Boundary
