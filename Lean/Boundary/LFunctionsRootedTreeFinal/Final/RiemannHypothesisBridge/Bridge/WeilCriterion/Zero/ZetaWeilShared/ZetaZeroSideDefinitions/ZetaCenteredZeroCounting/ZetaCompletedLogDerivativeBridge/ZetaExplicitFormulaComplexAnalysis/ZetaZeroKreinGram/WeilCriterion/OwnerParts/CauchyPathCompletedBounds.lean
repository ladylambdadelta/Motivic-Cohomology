import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaZeroKreinGram.WeilCriterion.OwnerParts.CanonicalScheduledPolynomialPackageParts.FactorPathBounds
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaZeroKreinGram.WeilCriterion.OwnerParts.CanonicalScheduledPolynomialPackageParts.PackagePathBounds

/-!
# Completed bounds from canonical Cauchy path data

This file owns the explicit fixed-degree completed-log-derivative bounds
extracted from the zeta-side and inverse-Gamma Cauchy path data.
-/

namespace Boundary
namespace LFunctions

noncomputable section

namespace ZetaAdmissibleFunction

/-- The completed-log-derivative bound constant supplied from the two factor
Cauchy path data packages. -/
def canonicalScheduledCauchyPathDataCompletedBoundConstant
    {f : ZetaAdmissibleFunction} {K : ℕ}
    (zetaData : CanonicalScheduledZetaSideCauchyPathData f K)
    (gammaData : CanonicalScheduledInverseGammaCauchyPathData f K) : ℝ :=
  zetaData.boundConstant + gammaData.boundConstant

/-- The completed bound constant extracted from the two factor Cauchy packages
is positive. -/
theorem canonicalScheduledCauchyPathDataCompletedBoundConstant_pos
    {f : ZetaAdmissibleFunction} {K : ℕ}
    (zetaData : CanonicalScheduledZetaSideCauchyPathData f K)
    (gammaData : CanonicalScheduledInverseGammaCauchyPathData f K) :
    0 <
      canonicalScheduledCauchyPathDataCompletedBoundConstant
        zetaData gammaData :=
  add_pos
    zetaData.boundConstant_pos
    gammaData.boundConstant_pos

/-- The zeta-side and inverse-Gamma Cauchy path data give the completed
top-edge logarithmic-derivative bound. -/
theorem completedZetaNegLogDeriv_top_bound_of_canonicalScheduledCauchyPathData
    {f : ZetaAdmissibleFunction} {K : ℕ}
    (zetaData : CanonicalScheduledZetaSideCauchyPathData f K)
    (gammaData : CanonicalScheduledInverseGammaCauchyPathData f K) :
    ∀ u x : ℝ,
      x ∈ Set.uIcc
        (zetaCompletedExplicitFormula_autocorrelation_contourFamily f).c
        (1 - (zetaCompletedExplicitFormula_autocorrelation_contourFamily f).c) →
      ‖completedZetaNegLogDeriv
        (zetaCompletedExplicitFormulaTopPath
          ((zetaCompletedExplicitFormula_autocorrelation_contourFamily f).rectangle
            ((zetaCompletedExplicitFormulaAutocorrelationCofinalHeightSchedule f).height u))
          x)‖ ≤
        canonicalScheduledCauchyPathDataCompletedBoundConstant
          zetaData gammaData *
          (1 +
            ‖(zetaCompletedExplicitFormulaAutocorrelationCofinalHeightSchedule f).height u‖) ^ K :=
  let h :
      ExplicitFormulaScheduledPolynomialFamilyAnalyticPackage
        (convolutionAutocorrelation f)
        (zetaCompletedExplicitFormula_autocorrelation_contourFamily f) :=
    zetaCompletedExplicitFormulaAutocorrelationScheduledPolynomialFamilyAnalyticPackage_of_cauchyPathData
      f K zetaData gammaData
  fun u x hx =>
    h.topPath_completedZetaNegLogDeriv_bound u x hx

/-- The zeta-side and inverse-Gamma Cauchy path data give the completed
bottom-edge logarithmic-derivative bound. -/
theorem completedZetaNegLogDeriv_bottom_bound_of_canonicalScheduledCauchyPathData
    {f : ZetaAdmissibleFunction} {K : ℕ}
    (zetaData : CanonicalScheduledZetaSideCauchyPathData f K)
    (gammaData : CanonicalScheduledInverseGammaCauchyPathData f K) :
    ∀ u x : ℝ,
      x ∈ Set.uIcc
        (zetaCompletedExplicitFormula_autocorrelation_contourFamily f).c
        (1 - (zetaCompletedExplicitFormula_autocorrelation_contourFamily f).c) →
      ‖completedZetaNegLogDeriv
        (zetaCompletedExplicitFormulaBottomPath
          ((zetaCompletedExplicitFormula_autocorrelation_contourFamily f).rectangle
            ((zetaCompletedExplicitFormulaAutocorrelationCofinalHeightSchedule f).height u))
          x)‖ ≤
        canonicalScheduledCauchyPathDataCompletedBoundConstant
          zetaData gammaData *
          (1 +
            ‖(zetaCompletedExplicitFormulaAutocorrelationCofinalHeightSchedule f).height u‖) ^ K :=
  let h :
      ExplicitFormulaScheduledPolynomialFamilyAnalyticPackage
        (convolutionAutocorrelation f)
        (zetaCompletedExplicitFormula_autocorrelation_contourFamily f) :=
    zetaCompletedExplicitFormulaAutocorrelationScheduledPolynomialFamilyAnalyticPackage_of_cauchyPathData
      f K zetaData gammaData
  fun u x hx =>
    h.bottomPath_completedZetaNegLogDeriv_bound u x hx

end ZetaAdmissibleFunction

end
end LFunctions
end Boundary
