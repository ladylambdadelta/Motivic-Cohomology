import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaZeroKreinGram.WeilCriterion.OwnerParts.AutocorrelationVerticalRegularity
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaZeroKreinGram.WeilCriterion.OwnerParts.CanonicalAnalyticInputs

/-!
# Autocorrelation analytic package

This owner part constructs the explicit-formula analytic package for the
autocorrelation contour from the clean vertical-regularity owner and a supplied
horizontal avoiding schedule.
-/

namespace Boundary
namespace LFunctions

noncomputable section

namespace ZetaAdmissibleFunction

namespace CleanAutocorrelationAnalyticPackage

/-- The analytic package for the autocorrelation contour family, from an
explicitly supplied horizontal-bad-height avoiding schedule. -/
def zetaCompletedExplicitFormula_autocorrelation_familyAnalyticPackage
    (f : ZetaAdmissibleFunction)
    (schedule :
      ExplicitFormulaHorizontalAvoidingHeightSchedule
        (zetaCompletedExplicitFormula_autocorrelation_contourFamily f))
    (hPhi : ZetaPhiAnalyticControl (convolutionAutocorrelation f))
    (hLog : CompletedZetaNegLogDerivControl (convolutionAutocorrelation f)) :
    ExplicitFormulaFamilyAnalyticPackage
      (convolutionAutocorrelation f)
      (zetaCompletedExplicitFormula_autocorrelation_contourFamily f) :=
  ExplicitFormulaFamilyAnalyticPackage.of_horizontalAvoidingSchedule
    (CleanAutocorrelationVerticalRegularity.zetaCompletedExplicitFormula_autocorrelation_verticallyRegularContourFamily f)
    schedule
    hPhi
    hLog

end CleanAutocorrelationAnalyticPackage

end ZetaAdmissibleFunction

end
end LFunctions
end Boundary
