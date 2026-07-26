import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaZeroKreinGram.WeilCriterion.OwnerParts.CanonicalScheduledPolynomialPackageParts.PackagePathBounds
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaZeroKreinGram.WeilCriterion.OwnerParts.CanonicalScheduledPolynomialPackageParts.VariableCauchyPathBounds
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaCompletedLogDerivativeControl.PolynomialGrowthControl

/-!
# Canonical scheduled horizontal polynomial bounds

This owner part packages the exact horizontal completed-log-derivative bounds
for the final completed-Weil positivity assembly.
-/

namespace Boundary
namespace LFunctions

noncomputable section

namespace ZetaAdmissibleFunction

structure CanonicalScheduledPolynomialHorizontalBounds
    (f : ZetaAdmissibleFunction) where
  degree : ℕ
  constant : ℝ
  constant_pos : 0 < constant
  top_bound :
    ∀ u x : ℝ,
      x ∈ Set.uIcc
        (zetaCompletedExplicitFormula_autocorrelation_contourFamily f).c
        (1 - (zetaCompletedExplicitFormula_autocorrelation_contourFamily f).c) →
      ‖completedZetaNegLogDeriv
        (zetaCompletedExplicitFormulaTopPath
          ((zetaCompletedExplicitFormula_autocorrelation_contourFamily f).rectangle
            ((zetaCompletedExplicitFormulaAutocorrelationCofinalHeightSchedule f).height u))
          x)‖ ≤
        constant *
          (1 +
            ‖(zetaCompletedExplicitFormulaAutocorrelationCofinalHeightSchedule f).height u‖) ^
            degree
  bottom_bound :
    ∀ u x : ℝ,
      x ∈ Set.uIcc
        (zetaCompletedExplicitFormula_autocorrelation_contourFamily f).c
        (1 - (zetaCompletedExplicitFormula_autocorrelation_contourFamily f).c) →
      ‖completedZetaNegLogDeriv
        (zetaCompletedExplicitFormulaBottomPath
          ((zetaCompletedExplicitFormula_autocorrelation_contourFamily f).rectangle
            ((zetaCompletedExplicitFormulaAutocorrelationCofinalHeightSchedule f).height u))
          x)‖ ≤
        constant *
          (1 +
            ‖(zetaCompletedExplicitFormulaAutocorrelationCofinalHeightSchedule f).height u‖) ^
            degree

def CanonicalScheduledPolynomialHorizontalBounds.of_pathBounds
    (f : ZetaAdmissibleFunction)
    (degree : ℕ)
    (constant : ℝ)
    (constant_pos : 0 < constant)
    (topBound :
      ∀ u x : ℝ,
        x ∈ Set.uIcc
          (zetaCompletedExplicitFormula_autocorrelation_contourFamily f).c
          (1 - (zetaCompletedExplicitFormula_autocorrelation_contourFamily f).c) →
        ‖completedZetaNegLogDeriv
          (zetaCompletedExplicitFormulaTopPath
            ((zetaCompletedExplicitFormula_autocorrelation_contourFamily f).rectangle
              ((zetaCompletedExplicitFormulaAutocorrelationCofinalHeightSchedule f).height u))
            x)‖ ≤
          constant *
            (1 +
              ‖(zetaCompletedExplicitFormulaAutocorrelationCofinalHeightSchedule f).height u‖) ^
              degree)
    (bottomBound :
      ∀ u x : ℝ,
        x ∈ Set.uIcc
          (zetaCompletedExplicitFormula_autocorrelation_contourFamily f).c
          (1 - (zetaCompletedExplicitFormula_autocorrelation_contourFamily f).c) →
        ‖completedZetaNegLogDeriv
          (zetaCompletedExplicitFormulaBottomPath
            ((zetaCompletedExplicitFormula_autocorrelation_contourFamily f).rectangle
              ((zetaCompletedExplicitFormulaAutocorrelationCofinalHeightSchedule f).height u))
            x)‖ ≤
          constant *
            (1 +
              ‖(zetaCompletedExplicitFormulaAutocorrelationCofinalHeightSchedule f).height u‖) ^
              degree) :
    CanonicalScheduledPolynomialHorizontalBounds f :=
  { degree := degree
    constant := constant
    constant_pos := constant_pos
    top_bound := topBound
    bottom_bound := bottomBound }

def CanonicalScheduledPolynomialHorizontalBounds.of_factorPathBounds
    (f : ZetaAdmissibleFunction) (K : ℕ) (Czeta Cgamma : ℝ)
    (Czeta_pos : 0 < Czeta)
    (Cgamma_pos : 0 < Cgamma)
    (topZetaBound :
      ∀ u x : ℝ,
        x ∈ Set.uIcc
          (zetaCompletedExplicitFormula_autocorrelation_contourFamily f).c
          (1 - (zetaCompletedExplicitFormula_autocorrelation_contourFamily f).c) →
        ‖zetaSideNegLogDeriv
          (zetaCompletedExplicitFormulaTopPath
            ((zetaCompletedExplicitFormula_autocorrelation_contourFamily f).rectangle
              ((zetaCompletedExplicitFormulaAutocorrelationCofinalHeightSchedule f).height u))
            x)‖ ≤
          Czeta *
            (1 +
              ‖(zetaCompletedExplicitFormulaAutocorrelationCofinalHeightSchedule f).height u‖) ^ K)
    (bottomZetaBound :
      ∀ u x : ℝ,
        x ∈ Set.uIcc
          (zetaCompletedExplicitFormula_autocorrelation_contourFamily f).c
          (1 - (zetaCompletedExplicitFormula_autocorrelation_contourFamily f).c) →
        ‖zetaSideNegLogDeriv
          (zetaCompletedExplicitFormulaBottomPath
            ((zetaCompletedExplicitFormula_autocorrelation_contourFamily f).rectangle
              ((zetaCompletedExplicitFormulaAutocorrelationCofinalHeightSchedule f).height u))
            x)‖ ≤
          Czeta *
            (1 +
              ‖(zetaCompletedExplicitFormulaAutocorrelationCofinalHeightSchedule f).height u‖) ^ K)
    (topGammaBound :
      ∀ u x : ℝ,
        x ∈ Set.uIcc
          (zetaCompletedExplicitFormula_autocorrelation_contourFamily f).c
          (1 - (zetaCompletedExplicitFormula_autocorrelation_contourFamily f).c) →
        ‖deriv (fun w : ℂ => (Complex.Gammaℝ w)⁻¹)
            (zetaCompletedExplicitFormulaTopPath
              ((zetaCompletedExplicitFormula_autocorrelation_contourFamily f).rectangle
                ((zetaCompletedExplicitFormulaAutocorrelationCofinalHeightSchedule f).height u))
              x) /
            (Complex.Gammaℝ
              (zetaCompletedExplicitFormulaTopPath
                ((zetaCompletedExplicitFormula_autocorrelation_contourFamily f).rectangle
                  ((zetaCompletedExplicitFormulaAutocorrelationCofinalHeightSchedule f).height u))
                x))⁻¹‖ ≤
          Cgamma *
            (1 +
              ‖(zetaCompletedExplicitFormulaAutocorrelationCofinalHeightSchedule f).height u‖) ^ K)
    (bottomGammaBound :
      ∀ u x : ℝ,
        x ∈ Set.uIcc
          (zetaCompletedExplicitFormula_autocorrelation_contourFamily f).c
          (1 - (zetaCompletedExplicitFormula_autocorrelation_contourFamily f).c) →
        ‖deriv (fun w : ℂ => (Complex.Gammaℝ w)⁻¹)
            (zetaCompletedExplicitFormulaBottomPath
              ((zetaCompletedExplicitFormula_autocorrelation_contourFamily f).rectangle
                ((zetaCompletedExplicitFormulaAutocorrelationCofinalHeightSchedule f).height u))
              x) /
            (Complex.Gammaℝ
              (zetaCompletedExplicitFormulaBottomPath
                ((zetaCompletedExplicitFormula_autocorrelation_contourFamily f).rectangle
                  ((zetaCompletedExplicitFormulaAutocorrelationCofinalHeightSchedule f).height u))
                x))⁻¹‖ ≤
          Cgamma *
            (1 +
              ‖(zetaCompletedExplicitFormulaAutocorrelationCofinalHeightSchedule f).height u‖) ^ K) :
    CanonicalScheduledPolynomialHorizontalBounds f :=
  let package :
      ExplicitFormulaScheduledPolynomialFamilyAnalyticPackage
        (convolutionAutocorrelation f)
        (zetaCompletedExplicitFormula_autocorrelation_contourFamily f) :=
    zetaCompletedExplicitFormulaAutocorrelationScheduledPolynomialFamilyAnalyticPackage_of_factorPathBounds
      f K Czeta Cgamma Czeta_pos Cgamma_pos
      topZetaBound bottomZetaBound topGammaBound bottomGammaBound
  { degree := package.horizontal_logderiv_control.growth_degree
    constant := package.horizontal_logderiv_control.bound_constant
    constant_pos := package.horizontal_logderiv_control.bound_constant_pos
    top_bound :=
      package.topPath_completedZetaNegLogDeriv_bound
    bottom_bound :=
      package.bottomPath_completedZetaNegLogDeriv_bound }

def CanonicalScheduledPolynomialHorizontalBounds.of_cauchyPathData
    (f : ZetaAdmissibleFunction) (K : ℕ)
    (zetaData : CanonicalScheduledZetaSideCauchyPathData f K)
    (gammaData : CanonicalScheduledInverseGammaCauchyPathData f K) :
    CanonicalScheduledPolynomialHorizontalBounds f :=
  CanonicalScheduledPolynomialHorizontalBounds.of_factorPathBounds
    f K
    zetaData.boundConstant
    gammaData.boundConstant
    zetaData.boundConstant_pos
    gammaData.boundConstant_pos
    zetaData.top_bound
    zetaData.bottom_bound
    gammaData.top_bound
    gammaData.bottom_bound

def CanonicalScheduledPolynomialHorizontalBounds.of_variableCauchyPathData
    (f : ZetaAdmissibleFunction) (K : ℕ)
    (zetaData : CanonicalScheduledZetaSideVariableCauchyPathData f K)
    (gammaData : CanonicalScheduledInverseGammaVariableCauchyPathData f K) :
    CanonicalScheduledPolynomialHorizontalBounds f :=
  CanonicalScheduledPolynomialHorizontalBounds.of_factorPathBounds
    f K
    zetaData.boundConstant
    gammaData.boundConstant
    zetaData.boundConstant_pos
    gammaData.boundConstant_pos
    zetaData.top_bound
    zetaData.bottom_bound
    gammaData.top_bound
    gammaData.bottom_bound

def CanonicalScheduledPolynomialHorizontalBounds.polynomialPackage
    (f : ZetaAdmissibleFunction)
    (bounds : CanonicalScheduledPolynomialHorizontalBounds f) :
    ExplicitFormulaScheduledPolynomialFamilyAnalyticPackage
      (convolutionAutocorrelation f)
      (zetaCompletedExplicitFormula_autocorrelation_contourFamily f) :=
  zetaCompletedExplicitFormulaAutocorrelationScheduledPolynomialFamilyAnalyticPackage_of_pathBounds
    f
    bounds.degree
    bounds.constant
    bounds.constant_pos
    bounds.top_bound
    bounds.bottom_bound

def CanonicalScheduledPolynomialHorizontalBounds.of_polynomialPackage
    (f : ZetaAdmissibleFunction)
    (package :
      ExplicitFormulaScheduledPolynomialFamilyAnalyticPackage
        (convolutionAutocorrelation f)
        (zetaCompletedExplicitFormula_autocorrelation_contourFamily f))
    (heightEq :
      package.height_schedule =
        zetaCompletedExplicitFormulaAutocorrelationCofinalHeightSchedule f) :
    CanonicalScheduledPolynomialHorizontalBounds f :=
  { degree := package.horizontal_logderiv_control.growth_degree
    constant := package.horizontal_logderiv_control.bound_constant
    constant_pos := package.horizontal_logderiv_control.bound_constant_pos
    top_bound :=
      fun u x hx =>
        Eq.subst
          (motive := fun schedule :
              ExplicitFormulaCofinalHeightSchedule
                (zetaCompletedExplicitFormula_autocorrelation_contourFamily f) =>
            ‖completedZetaNegLogDeriv
              (zetaCompletedExplicitFormulaTopPath
                ((zetaCompletedExplicitFormula_autocorrelation_contourFamily f).rectangle
                  (schedule.height u))
                x)‖ ≤
                  package.horizontal_logderiv_control.bound_constant *
                (1 + ‖schedule.height u‖) ^
                  package.horizontal_logderiv_control.growth_degree)
          heightEq
          (package.topPath_completedZetaNegLogDeriv_bound u x hx)
    bottom_bound :=
      fun u x hx =>
        Eq.subst
          (motive := fun schedule :
              ExplicitFormulaCofinalHeightSchedule
                (zetaCompletedExplicitFormula_autocorrelation_contourFamily f) =>
            ‖completedZetaNegLogDeriv
              (zetaCompletedExplicitFormulaBottomPath
                ((zetaCompletedExplicitFormula_autocorrelation_contourFamily f).rectangle
                  (schedule.height u))
                x)‖ ≤
                  package.horizontal_logderiv_control.bound_constant *
                (1 + ‖schedule.height u‖) ^
                  package.horizontal_logderiv_control.growth_degree)
          heightEq
          (package.bottomPath_completedZetaNegLogDeriv_bound u x hx) }

def CanonicalScheduledPolynomialHorizontalBounds.of_commonDegreeFactorControl
    (f : ZetaAdmissibleFunction)
    (growthControl : CompletedZetaNegLogDerivCommonDegreeFactorControl) :
    CanonicalScheduledPolynomialHorizontalBounds f :=
  let leftEdge : ℝ :=
    min (zetaCompletedExplicitFormula_autocorrelation_contourFamily f).c
      (1 - (zetaCompletedExplicitFormula_autocorrelation_contourFamily f).c)
  let rightEdge : ℝ :=
    max (zetaCompletedExplicitFormula_autocorrelation_contourFamily f).c
      (1 - (zetaCompletedExplicitFormula_autocorrelation_contourFamily f).c)
  let carrier :
      CompletedZetaZeroExcisedStrip leftEdge rightEdge :=
    zetaCompletedExplicitFormulaAutocorrelationScheduledHorizontalCarrier f
  let degree : ℕ := growthControl.K leftEdge rightEdge carrier
  let zetaConstant : ℝ := growthControl.Czeta leftEdge rightEdge carrier
  let gammaConstant : ℝ := growthControl.Cgamma leftEdge rightEdge carrier
  { degree := degree
    constant := zetaConstant + gammaConstant
    constant_pos :=
      add_pos
        (growthControl.Czeta_pos leftEdge rightEdge carrier)
        (growthControl.Cgamma_pos leftEdge rightEdge carrier)
    top_bound :=
      fun u x hx =>
        let z : ℂ :=
          zetaCompletedExplicitFormulaTopPath
            ((zetaCompletedExplicitFormula_autocorrelation_contourFamily f).rectangle
              ((zetaCompletedExplicitFormulaAutocorrelationCofinalHeightSchedule f).height u))
            x
        let hz :
            z ∈ carrier.carrier :=
          zetaCompletedExplicitFormulaAutocorrelationScheduledHorizontalCarrier_top_mem
            f u x hx
        let rawBound :
            ‖completedZetaNegLogDeriv z‖ ≤
              (zetaConstant + gammaConstant) * (1 + ‖z.im‖) ^ degree :=
          completedZetaNegLogDeriv_norm_bound_of_factor_bounds
            carrier degree zetaConstant gammaConstant z hz
            (growthControl.Czeta_bound leftEdge rightEdge carrier)
            (growthControl.Cgamma_bound leftEdge rightEdge carrier)
        let heightEq :
            ‖z.im‖ =
              ‖(zetaCompletedExplicitFormulaAutocorrelationCofinalHeightSchedule f).height u‖ :=
          zetaCompletedExplicitFormulaTopPath_im_norm
            ((zetaCompletedExplicitFormula_autocorrelation_contourFamily f).rectangle
              ((zetaCompletedExplicitFormulaAutocorrelationCofinalHeightSchedule f).height u))
            x
        let targetEq :
            (zetaConstant + gammaConstant) * (1 + ‖z.im‖) ^ degree =
              (zetaConstant + gammaConstant) *
                (1 +
                  ‖(zetaCompletedExplicitFormulaAutocorrelationCofinalHeightSchedule f).height u‖) ^
                degree :=
          congrArg
            (fun value : ℝ => (zetaConstant + gammaConstant) * (1 + value) ^ degree)
            heightEq
        rawBound.trans_eq targetEq
    bottom_bound :=
      fun u x hx =>
        let z : ℂ :=
          zetaCompletedExplicitFormulaBottomPath
            ((zetaCompletedExplicitFormula_autocorrelation_contourFamily f).rectangle
              ((zetaCompletedExplicitFormulaAutocorrelationCofinalHeightSchedule f).height u))
            x
        let hz :
            z ∈ carrier.carrier :=
          zetaCompletedExplicitFormulaAutocorrelationScheduledHorizontalCarrier_bottom_mem
            f u x hx
        let rawBound :
            ‖completedZetaNegLogDeriv z‖ ≤
              (zetaConstant + gammaConstant) * (1 + ‖z.im‖) ^ degree :=
          completedZetaNegLogDeriv_norm_bound_of_factor_bounds
            carrier degree zetaConstant gammaConstant z hz
            (growthControl.Czeta_bound leftEdge rightEdge carrier)
            (growthControl.Cgamma_bound leftEdge rightEdge carrier)
        let heightEq :
            ‖z.im‖ =
              ‖(zetaCompletedExplicitFormulaAutocorrelationCofinalHeightSchedule f).height u‖ :=
          zetaCompletedExplicitFormulaBottomPath_im_norm
            ((zetaCompletedExplicitFormula_autocorrelation_contourFamily f).rectangle
              ((zetaCompletedExplicitFormulaAutocorrelationCofinalHeightSchedule f).height u))
            x
        let targetEq :
            (zetaConstant + gammaConstant) * (1 + ‖z.im‖) ^ degree =
              (zetaConstant + gammaConstant) *
                (1 +
                  ‖(zetaCompletedExplicitFormulaAutocorrelationCofinalHeightSchedule f).height u‖) ^
                degree :=
          congrArg
            (fun value : ℝ => (zetaConstant + gammaConstant) * (1 + value) ^ degree)
            heightEq
        rawBound.trans_eq targetEq }

def CanonicalScheduledPolynomialHorizontalBounds.of_autocorrelationCommonDegreeFactorControl
    (f : ZetaAdmissibleFunction)
    (growthControl : CompletedZetaNegLogDerivAutocorrelationCommonDegreeFactorControl) :
    CanonicalScheduledPolynomialHorizontalBounds f :=
  CanonicalScheduledPolynomialHorizontalBounds.of_commonDegreeFactorControl
    f
    (growthControl.atSeed f)

def CanonicalScheduledPolynomialHorizontalBounds.of_concreteControl
    (f : ZetaAdmissibleFunction)
    (growthControl : CompletedZetaNegLogDerivAutocorrelationConcreteControl) :
    CanonicalScheduledPolynomialHorizontalBounds f :=
  CanonicalScheduledPolynomialHorizontalBounds.of_autocorrelationCommonDegreeFactorControl
    f
    (completedZetaNegLogDerivAutocorrelationCommonDegreeFactorControl_of_concreteControl
      growthControl)

def canonicalScheduledPolynomialPackage_of_horizontalBounds
    (horizontalBounds :
      ∀ f : ZetaAdmissibleFunction,
        CanonicalScheduledPolynomialHorizontalBounds f) :
    ∀ f : ZetaAdmissibleFunction,
      ExplicitFormulaScheduledPolynomialFamilyAnalyticPackage
        (convolutionAutocorrelation f)
        (zetaCompletedExplicitFormula_autocorrelation_contourFamily f) :=
  fun f =>
    CanonicalScheduledPolynomialHorizontalBounds.polynomialPackage
      f
      (horizontalBounds f)

/-- Canonical scheduled horizontal polynomial bounds. -/
def canonicalScheduledPolynomialHorizontalBounds_owner
    (f : ZetaAdmissibleFunction)
    (degree : ℕ)
    (zetaData :
      CanonicalScheduledZetaSideVariableCauchyPathData f degree)
    (gammaData :
      CanonicalScheduledInverseGammaVariableCauchyPathData f degree) :
    CanonicalScheduledPolynomialHorizontalBounds f :=
  CanonicalScheduledPolynomialHorizontalBounds.of_variableCauchyPathData
    f
    degree
    zetaData
    gammaData

/-- The fixed-radius path package is the owner-level source of the same
horizontal bounds.  Keeping this theorem separate makes the Cauchy sink
explicit: first form each factor's logarithmic-derivative bound, then combine
the two factors through the scheduled polynomial package. -/
def canonicalScheduledPolynomialHorizontalBounds_of_cauchyPathData_owner
    (f : ZetaAdmissibleFunction)
    (degree : ℕ)
    (zetaData : CanonicalScheduledZetaSideCauchyPathData f degree)
    (gammaData : CanonicalScheduledInverseGammaCauchyPathData f degree) :
    CanonicalScheduledPolynomialHorizontalBounds f :=
  CanonicalScheduledPolynomialHorizontalBounds.of_cauchyPathData
    f
    degree
    zetaData
    gammaData

def canonicalScheduledPolynomialHorizontalBounds_of_polynomialPackage_owner
    (f : ZetaAdmissibleFunction)
    (package :
      ExplicitFormulaScheduledPolynomialFamilyAnalyticPackage
        (convolutionAutocorrelation f)
        (zetaCompletedExplicitFormula_autocorrelation_contourFamily f))
    (heightEq :
      package.height_schedule =
        zetaCompletedExplicitFormulaAutocorrelationCofinalHeightSchedule f) :
    CanonicalScheduledPolynomialHorizontalBounds f :=
  CanonicalScheduledPolynomialHorizontalBounds.of_polynomialPackage
    f
    package
    heightEq

def canonicalScheduledPolynomialHorizontalBounds_of_commonDegreeFactorControl_owner
    (f : ZetaAdmissibleFunction)
    (growthControl : CompletedZetaNegLogDerivCommonDegreeFactorControl) :
    CanonicalScheduledPolynomialHorizontalBounds f :=
  CanonicalScheduledPolynomialHorizontalBounds.of_commonDegreeFactorControl
    f
    growthControl

def canonicalScheduledPolynomialHorizontalBounds_of_autocorrelationCommonDegreeFactorControl_family_owner
    (growthControl :
      CompletedZetaNegLogDerivAutocorrelationCommonDegreeFactorControl) :
    ∀ f : ZetaAdmissibleFunction,
      CanonicalScheduledPolynomialHorizontalBounds f :=
  fun f =>
    CanonicalScheduledPolynomialHorizontalBounds.of_autocorrelationCommonDegreeFactorControl
      f
      growthControl

def canonicalScheduledPolynomialHorizontalBounds_of_concreteControl_family_owner
    (hLogConcrete :
      CompletedZetaNegLogDerivAutocorrelationConcreteControl) :
    ∀ f : ZetaAdmissibleFunction,
      CanonicalScheduledPolynomialHorizontalBounds f :=
  canonicalScheduledPolynomialHorizontalBounds_of_autocorrelationCommonDegreeFactorControl_family_owner
    (completedZetaNegLogDerivAutocorrelationCommonDegreeFactorControl_of_concreteControl
      hLogConcrete)

end ZetaAdmissibleFunction

end

end LFunctions
end Boundary
