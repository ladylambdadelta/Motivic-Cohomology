import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaZeroKreinGram.WeilCriterion.OwnerParts.PositiveAssembly
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaZeroKreinGram.WeilCriterion.OwnerParts.CanonicalScheduledHorizontalBounds

/-!
# Completed-Weil positivity from affine packet data

This owner part gives the narrow positivity surface: scheduled horizontal
polynomial bounds plus completed affine packet data.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open MeasureTheory

/-- Completed-Weil positivity from polynomial scheduled horizontal bounds and
completed affine packet data. -/
theorem zetaWeilQuadraticPositivity_of_canonicalScheduledPolynomialPathBounds_packetData_traceBessel_owner
    (K : ZetaAdmissibleFunction → ℕ)
    (C : ZetaAdmissibleFunction → ℝ)
    (C_pos : ∀ f : ZetaAdmissibleFunction, 0 < C f)
    (topBound :
      ∀ f : ZetaAdmissibleFunction,
        ∀ u x : ℝ,
          x ∈ Set.uIcc
            (ZetaAdmissibleFunction.zetaCompletedExplicitFormula_autocorrelation_contourFamily f).c
            (1 -
              (ZetaAdmissibleFunction.zetaCompletedExplicitFormula_autocorrelation_contourFamily f).c) →
          ‖completedZetaNegLogDeriv
            (ZetaAdmissibleFunction.zetaCompletedExplicitFormulaTopPath
              ((ZetaAdmissibleFunction.zetaCompletedExplicitFormula_autocorrelation_contourFamily f).rectangle
                ((ZetaAdmissibleFunction.zetaCompletedExplicitFormulaAutocorrelationCofinalHeightSchedule f).height u))
              x)‖ ≤
            C f *
              (1 +
                ‖(ZetaAdmissibleFunction.zetaCompletedExplicitFormulaAutocorrelationCofinalHeightSchedule f).height u‖) ^
                K f)
    (bottomBound :
      ∀ f : ZetaAdmissibleFunction,
        ∀ u x : ℝ,
          x ∈ Set.uIcc
            (ZetaAdmissibleFunction.zetaCompletedExplicitFormula_autocorrelation_contourFamily f).c
            (1 -
              (ZetaAdmissibleFunction.zetaCompletedExplicitFormula_autocorrelation_contourFamily f).c) →
          ‖completedZetaNegLogDeriv
            (ZetaAdmissibleFunction.zetaCompletedExplicitFormulaBottomPath
              ((ZetaAdmissibleFunction.zetaCompletedExplicitFormula_autocorrelation_contourFamily f).rectangle
                ((ZetaAdmissibleFunction.zetaCompletedExplicitFormulaAutocorrelationCofinalHeightSchedule f).height u))
              x)‖ ≤
            C f *
              (1 +
                ‖(ZetaAdmissibleFunction.zetaCompletedExplicitFormulaAutocorrelationCofinalHeightSchedule f).height u‖) ^
                K f)
    (packetData :
      ∀ f : ZetaAdmissibleFunction,
        ZetaAdmissibleFunction.ZetaCompletedAutocorrelationAffinePacketData f) :
    ZetaWeilQuadraticPositivity :=
  zetaWeilQuadraticPositivity_of_canonicalScheduledPolynomialPathBounds_packetExchange_traceBessel_owner
    K
    C
    C_pos
    topBound
    bottomBound
    (fun f => (packetData f).right_prime_integrable)
    (fun f => (packetData f).right_inverse_gamma_integrable)
    (fun f => (packetData f).left_reflected_integrable)
    (fun f => (packetData f).left_inverse_gamma_integrable)
    (fun f => (packetData f).left_arithmetic_integral_exchange)
    (fun f => (packetData f).arithmetic_equality)
    (fun f => (packetData f).inverse_gamma_difference_integral)
    (fun f => (packetData f).archimedean_value)

/-- Completed-Weil positivity from packaged scheduled horizontal bounds and
completed affine packet data. -/
theorem zetaWeilQuadraticPositivity_of_canonicalScheduledHorizontalBounds_packetData_traceBessel_owner
    (horizontalBounds :
      ∀ f : ZetaAdmissibleFunction,
        ZetaAdmissibleFunction.CanonicalScheduledPolynomialHorizontalBounds f)
    (packetData :
      ∀ f : ZetaAdmissibleFunction,
        ZetaAdmissibleFunction.ZetaCompletedAutocorrelationAffinePacketData f) :
    ZetaWeilQuadraticPositivity :=
  zetaWeilQuadraticPositivity_of_canonicalScheduledPolynomialPathBounds_packetData_traceBessel_owner
    (fun f => (horizontalBounds f).degree)
    (fun f => (horizontalBounds f).constant)
    (fun f => (horizontalBounds f).constant_pos)
    (fun f => (horizontalBounds f).top_bound)
    (fun f => (horizontalBounds f).bottom_bound)
    packetData

theorem zetaWeilQuadraticPositivity_of_canonicalScheduledCauchyPathData_packetData_traceBessel_owner
    (K : ZetaAdmissibleFunction → ℕ)
    (zetaData :
      ∀ f : ZetaAdmissibleFunction,
        ZetaAdmissibleFunction.CanonicalScheduledZetaSideCauchyPathData
          f (K f))
    (gammaData :
      ∀ f : ZetaAdmissibleFunction,
        ZetaAdmissibleFunction.CanonicalScheduledInverseGammaCauchyPathData
          f (K f))
    (packetData :
      ∀ f : ZetaAdmissibleFunction,
        ZetaAdmissibleFunction.ZetaCompletedAutocorrelationAffinePacketData f) :
    ZetaWeilQuadraticPositivity :=
  zetaWeilQuadraticPositivity_of_canonicalScheduledHorizontalBounds_packetData_traceBessel_owner
    (fun f =>
      ZetaAdmissibleFunction.CanonicalScheduledPolynomialHorizontalBounds.of_cauchyPathData
        f
        (K f)
        (zetaData f)
        (gammaData f))
    packetData

theorem zetaWeilQuadraticPositivity_of_canonicalScheduledVariableCauchyPathData_packetData_traceBessel_owner
    (K : ZetaAdmissibleFunction → ℕ)
    (zetaData :
      ∀ f : ZetaAdmissibleFunction,
        ZetaAdmissibleFunction.CanonicalScheduledZetaSideVariableCauchyPathData
          f (K f))
    (gammaData :
      ∀ f : ZetaAdmissibleFunction,
        ZetaAdmissibleFunction.CanonicalScheduledInverseGammaVariableCauchyPathData
          f (K f))
    (packetData :
      ∀ f : ZetaAdmissibleFunction,
        ZetaAdmissibleFunction.ZetaCompletedAutocorrelationAffinePacketData f) :
    ZetaWeilQuadraticPositivity :=
  zetaWeilQuadraticPositivity_of_canonicalScheduledHorizontalBounds_packetData_traceBessel_owner
    (fun f =>
      ZetaAdmissibleFunction.CanonicalScheduledPolynomialHorizontalBounds.of_variableCauchyPathData
        f
        (K f)
        (zetaData f)
        (gammaData f))
    packetData

/-- Completed-Weil positivity from canonical scheduled Cauchy path data and
explicit affine analytic packages.

This peels the affine packet data sink to the analytic-package surface: the
scheduled path data owns the horizontal bounds, while the analytic and regular
analytic packages own the affine packet component facts. -/
theorem zetaWeilQuadraticPositivity_of_canonicalScheduledCauchyPathData_analyticPackages_traceBessel_owner
    (K : ZetaAdmissibleFunction → ℕ)
    (zetaData :
      ∀ f : ZetaAdmissibleFunction,
        ZetaAdmissibleFunction.CanonicalScheduledZetaSideCauchyPathData
          f (K f))
    (gammaData :
      ∀ f : ZetaAdmissibleFunction,
        ZetaAdmissibleFunction.CanonicalScheduledInverseGammaCauchyPathData
          f (K f))
    (analyticPackage :
      ∀ f : ZetaAdmissibleFunction,
        ZetaAdmissibleFunction.ExplicitFormulaFamilyAnalyticPackage
          (ZetaAdmissibleFunction.convolutionAutocorrelation f)
          (ZetaAdmissibleFunction.zetaCompletedExplicitFormula_autocorrelation_contourFamily f))
    (regularAnalyticPackage :
      ∀ f : ZetaAdmissibleFunction,
        ZetaAdmissibleFunction.ExplicitFormulaFamilyAnalyticPackage
          (ZetaAdmissibleFunction.convolutionAutocorrelation f)
          (ZetaAdmissibleFunction.zetaCompletedAutocorrelationRegularFamily f).toContourFamily) :
    ZetaWeilQuadraticPositivity :=
  zetaWeilQuadraticPositivity_of_canonicalScheduledPolynomialPathBounds_analyticPackages_traceBessel_owner
    K
    (fun f =>
      ZetaAdmissibleFunction.canonicalScheduledCauchyPathDataCompletedBoundConstant
        (zetaData f)
        (gammaData f))
    (fun f =>
      ZetaAdmissibleFunction.canonicalScheduledCauchyPathDataCompletedBoundConstant_pos
        (zetaData f)
        (gammaData f))
    (fun f =>
      ZetaAdmissibleFunction.completedZetaNegLogDeriv_top_bound_of_canonicalScheduledCauchyPathData
        (zetaData f)
        (gammaData f))
    (fun f =>
      ZetaAdmissibleFunction.completedZetaNegLogDeriv_bottom_bound_of_canonicalScheduledCauchyPathData
        (zetaData f)
        (gammaData f))
    analyticPackage
    regularAnalyticPackage

end

end LFunctions
end Boundary
