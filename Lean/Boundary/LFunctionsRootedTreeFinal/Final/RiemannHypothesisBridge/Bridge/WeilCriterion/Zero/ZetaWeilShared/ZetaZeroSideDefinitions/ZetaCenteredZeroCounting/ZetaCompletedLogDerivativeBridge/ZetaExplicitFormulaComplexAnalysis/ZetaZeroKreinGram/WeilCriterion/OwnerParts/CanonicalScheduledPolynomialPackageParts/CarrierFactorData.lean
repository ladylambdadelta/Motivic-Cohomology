import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaZeroKreinGram.WeilCriterion.OwnerParts.CanonicalScheduledAnalyticPackage
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaZeroKreinGram.WeilCriterion.OwnerParts.CanonicalScheduledPointwiseSeparation
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaExplicitFormulaHorizontalEdgeBounds.ScheduledPolynomialGrowth

/-!
# Canonical scheduled polynomial package from carrier factor data

This file owns the fixed-degree polynomial package obtained from concrete
factor bounds on the canonical scheduled horizontal carrier.
-/

namespace Boundary
namespace LFunctions

noncomputable section

namespace ZetaAdmissibleFunction

def zetaCompletedExplicitFormulaAutocorrelationScheduledPolynomialFamilyAnalyticPackage_of_cofinalScheduleCarrierFactorData
    (f : ZetaAdmissibleFunction)
    (schedule :
      ExplicitFormulaCofinalHeightSchedule
        (zetaCompletedExplicitFormula_autocorrelation_contourFamily f))
    (hPhi :
      ZetaPhiAnalyticControl
        (convolutionAutocorrelation f))
    (factorData :
      CompletedZetaZeroExcisedStrip.FactorBoundData
        (zetaCompletedExplicitFormulaAutocorrelationScheduledHorizontalCarrier_of_cofinalSchedule
          f schedule)) :
    ExplicitFormulaScheduledPolynomialFamilyAnalyticPackage
      (convolutionAutocorrelation f)
      (zetaCompletedExplicitFormula_autocorrelation_contourFamily f) :=
  (zetaCompletedExplicitFormulaAutocorrelationScheduledFamilyAnalyticPackage_of_cofinalScheduleCarrierFactorData
    f
    schedule
    hPhi
    factorData).toPolynomialGrowthAtDegree 0

def zetaCompletedExplicitFormulaAutocorrelationScheduledPolynomialFamilyAnalyticPackage_of_carrierFactorData
    (f : ZetaAdmissibleFunction)
    (hPhi :
      ZetaPhiAnalyticControl
        (convolutionAutocorrelation f))
    (factorData :
      CompletedZetaZeroExcisedStrip.FactorBoundData
        (zetaCompletedExplicitFormulaAutocorrelationScheduledHorizontalCarrier f)) :
    ExplicitFormulaScheduledPolynomialFamilyAnalyticPackage
      (convolutionAutocorrelation f)
      (zetaCompletedExplicitFormula_autocorrelation_contourFamily f) :=
  zetaCompletedExplicitFormulaAutocorrelationScheduledPolynomialFamilyAnalyticPackage_of_cofinalScheduleCarrierFactorData
    f
    (zetaCompletedExplicitFormulaAutocorrelationCofinalHeightSchedule f)
    hPhi
    factorData

def zetaCompletedExplicitFormulaAutocorrelationScheduledPolynomialFamilyAnalyticPackage_of_cofinalScheduleCarrierBoundData
    (f : ZetaAdmissibleFunction)
    (schedule :
      ExplicitFormulaCofinalHeightSchedule
        (zetaCompletedExplicitFormula_autocorrelation_contourFamily f))
    (hPhi :
      ZetaPhiAnalyticControl
        (convolutionAutocorrelation f))
    (zetaData :
      CompletedZetaZeroExcisedStrip.ZetaSideBoundData
        (zetaCompletedExplicitFormulaAutocorrelationScheduledHorizontalCarrier_of_cofinalSchedule
          f schedule))
    (gammaData :
      CompletedZetaZeroExcisedStrip.InverseGammaBoundData
        (zetaCompletedExplicitFormulaAutocorrelationScheduledHorizontalCarrier_of_cofinalSchedule
          f schedule)) :
    ExplicitFormulaScheduledPolynomialFamilyAnalyticPackage
      (convolutionAutocorrelation f)
      (zetaCompletedExplicitFormula_autocorrelation_contourFamily f) :=
  zetaCompletedExplicitFormulaAutocorrelationScheduledPolynomialFamilyAnalyticPackage_of_cofinalScheduleCarrierFactorData
    f
    schedule
    hPhi
    (zetaCompletedExplicitFormulaAutocorrelationScheduledHorizontalCarrier_factorData_of_parts_of_cofinalSchedule
      f
      schedule
      zetaData
      gammaData)

def zetaCompletedExplicitFormulaAutocorrelationScheduledPolynomialFamilyAnalyticPackage_of_carrierBoundData
    (f : ZetaAdmissibleFunction)
    (hPhi :
      ZetaPhiAnalyticControl
        (convolutionAutocorrelation f))
    (zetaData :
      CompletedZetaZeroExcisedStrip.ZetaSideBoundData
        (zetaCompletedExplicitFormulaAutocorrelationScheduledHorizontalCarrier f))
    (gammaData :
      CompletedZetaZeroExcisedStrip.InverseGammaBoundData
        (zetaCompletedExplicitFormulaAutocorrelationScheduledHorizontalCarrier f)) :
    ExplicitFormulaScheduledPolynomialFamilyAnalyticPackage
      (convolutionAutocorrelation f)
      (zetaCompletedExplicitFormula_autocorrelation_contourFamily f) :=
  zetaCompletedExplicitFormulaAutocorrelationScheduledPolynomialFamilyAnalyticPackage_of_carrierFactorData
    f
    hPhi
    (zetaCompletedExplicitFormulaAutocorrelationScheduledHorizontalCarrier_factorData_of_parts
      f
      zetaData
      gammaData)

end ZetaAdmissibleFunction

end
end LFunctions
end Boundary
