import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaZeroKreinGram.WeilCriterion.OwnerParts.CanonicalScheduledHorizontalBounds
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaZeroKreinGram.WeilCriterion.OwnerParts.SuppliedScheduleCarrierDataPackage

/-!
# Canonical horizontal bounds from supplied-schedule carrier data

This file owns the schedule-specialization adapter from a supplied quantitative
carrier package to the canonical scheduled horizontal-bound package.
-/

namespace Boundary
namespace LFunctions

noncomputable section

namespace ZetaAdmissibleFunction

def canonicalScheduledPolynomialHorizontalBounds_of_suppliedScheduleCarrierCauchyFamily_owner
    (data : SuppliedScheduleCarrierCauchyFamily)
    (heightEq :
      ∀ f : ZetaAdmissibleFunction,
        data.schedule f =
          zetaCompletedExplicitFormulaAutocorrelationCofinalHeightSchedule f) :
    ∀ f : ZetaAdmissibleFunction,
      CanonicalScheduledPolynomialHorizontalBounds f :=
  fun f =>
    canonicalScheduledPolynomialHorizontalBounds_of_polynomialPackage_owner
      f
      (data.scheduledPolynomialPackage f)
      (heightEq f)

end ZetaAdmissibleFunction

end

end LFunctions
end Boundary
