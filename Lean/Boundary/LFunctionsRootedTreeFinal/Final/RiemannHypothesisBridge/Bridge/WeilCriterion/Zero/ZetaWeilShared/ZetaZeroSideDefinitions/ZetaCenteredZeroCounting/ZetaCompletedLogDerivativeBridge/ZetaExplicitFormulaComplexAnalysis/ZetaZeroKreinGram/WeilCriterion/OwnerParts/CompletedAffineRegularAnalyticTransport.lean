import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaZeroKreinGram.WeilCriterion.OwnerParts.CompletedAffineRegularContourTransport

/-!
# Regular inverse-Gamma analytic-package transport

This owner part exposes the regular inverse-Gamma contour transport from an
explicit analytic package, rather than reconstructing that package from a
global completed-log-derivative control theorem.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open MeasureTheory

namespace ZetaAdmissibleFunction

theorem zetaCompletedAffineInverseGamma_oneSided_integral_eq_critical_of_analyticPackage_owner
    (f : ZetaAdmissibleFunction)
    (analyticPackage :
      ExplicitFormulaFamilyAnalyticPackage
        (convolutionAutocorrelation f)
        (zetaCompletedExplicitFormula_autocorrelation_contourFamily f)) :
    let probe : ZetaAdmissibleFunction := convolutionAutocorrelation f
    let family : ExplicitFormulaContourFamily :=
      zetaCompletedExplicitFormula_autocorrelation_contourFamily f
    (∫ t : ℝ,
      zetaCompletedExplicitFormulaInverseGammaRightAffineKernel
        probe family t) =
      ∫ t : ℝ,
        zetaCompletedCriticalInverseGammaSeedKernel f t :=
  let probe : ZetaAdmissibleFunction := convolutionAutocorrelation f
  let family : ExplicitFormulaContourFamily :=
    zetaCompletedExplicitFormula_autocorrelation_contourFamily f
  let rightKernel : ℝ → ℂ :=
    zetaCompletedExplicitFormulaInverseGammaRightAffineKernel
      probe family
  let criticalKernel : ℝ → ℂ :=
    zetaCompletedCriticalInverseGammaSeedKernel f
  let error : ℝ → ℂ :=
    zetaCompletedRegularInverseGammaHorizontalDefect f
  let rightIntegrable :
      Integrable rightKernel (volume : Measure ℝ) :=
    zetaCompletedExplicitFormulaInverseGammaRightAffineKernel_integrable
      probe family analyticPackage
  let criticalIntegrable :
      Integrable criticalKernel (volume : Measure ℝ) :=
    zetaCompletedCriticalInverseGammaSeedKernel_integrable f
  let finiteEquality :
      ∀ T : ℝ,
        0 ≤ T →
        (∫ t in Set.Icc (-T) T, rightKernel t) =
          (∫ t in Set.Icc (-T) T, criticalKernel t) + error T :=
    fun T : ℝ => fun heightNonnegative : 0 ≤ T =>
      zetaCompletedRegularInverseGamma_finiteWindow_eq_critical_add_horizontal
        f analyticPackage.phi_control T heightNonnegative
  let errorLimit : Tendsto error atTop (𝓝 0) :=
    zetaCompletedRegularInverseGammaHorizontalDefect_tendsto_zero f
  integral_eq_of_symmetric_windows_eq_add_vanishing_error
    rightKernel criticalKernel error
    rightIntegrable criticalIntegrable finiteEquality errorLimit

theorem zetaCompletedAffineInverseGamma_oneSided_integral_eq_critical_of_phiControl_gammaBinet_owner
    (f : ZetaAdmissibleFunction)
    (hPhi : ZetaPhiAnalyticControl (convolutionAutocorrelation f)) :
    let probe : ZetaAdmissibleFunction := convolutionAutocorrelation f
    let family : ExplicitFormulaContourFamily :=
      zetaCompletedExplicitFormula_autocorrelation_contourFamily f
    (∫ t : ℝ,
      zetaCompletedExplicitFormulaInverseGammaRightAffineKernel
        probe family t) =
      ∫ t : ℝ,
        zetaCompletedCriticalInverseGammaSeedKernel f t :=
  let probe : ZetaAdmissibleFunction := convolutionAutocorrelation f
  let family : ExplicitFormulaContourFamily :=
    zetaCompletedExplicitFormula_autocorrelation_contourFamily f
  let rightKernel : ℝ → ℂ :=
    zetaCompletedExplicitFormulaInverseGammaRightAffineKernel
      probe family
  let criticalKernel : ℝ → ℂ :=
    zetaCompletedCriticalInverseGammaSeedKernel f
  let error : ℝ → ℂ :=
    zetaCompletedRegularInverseGammaHorizontalDefect f
  let rightIntegrable :
      Integrable rightKernel (volume : Measure ℝ) :=
    zetaCompletedExplicitFormulaInverseGammaRightAffineKernel_integrable_of_phiControl_gammaBinet
      probe family hPhi
  let criticalIntegrable :
      Integrable criticalKernel (volume : Measure ℝ) :=
    zetaCompletedCriticalInverseGammaSeedKernel_integrable f
  let finiteEquality :
      ∀ T : ℝ,
        0 ≤ T →
        (∫ t in Set.Icc (-T) T, rightKernel t) =
          (∫ t in Set.Icc (-T) T, criticalKernel t) + error T :=
    fun T : ℝ => fun heightNonnegative : 0 ≤ T =>
      zetaCompletedRegularInverseGamma_finiteWindow_eq_critical_add_horizontal
        f hPhi T heightNonnegative
  let errorLimit : Tendsto error atTop (𝓝 0) :=
    zetaCompletedRegularInverseGammaHorizontalDefect_tendsto_zero f
  integral_eq_of_symmetric_windows_eq_add_vanishing_error
    rightKernel criticalKernel error
    rightIntegrable criticalIntegrable finiteEquality errorLimit

theorem zetaCompletedAffineRegularInverseGamma_integral_eq_critical_of_analyticPackage_owner
    (f : ZetaAdmissibleFunction)
    (analyticPackage :
      ExplicitFormulaFamilyAnalyticPackage
        (convolutionAutocorrelation f)
        (zetaCompletedExplicitFormula_autocorrelation_contourFamily f)) :
    let probe : ZetaAdmissibleFunction := convolutionAutocorrelation f
    let family : ExplicitFormulaContourFamily :=
      zetaCompletedExplicitFormula_autocorrelation_contourFamily f
    (∫ t : ℝ,
      zetaCompletedAffineInverseGammaRightReflectedDifferenceKernel
        probe family t) =
      ∫ t : ℝ,
        zetaCompletedHermitianInverseGammaIntegrand probe t :=
  let probe : ZetaAdmissibleFunction := convolutionAutocorrelation f
  let family : ExplicitFormulaContourFamily :=
    zetaCompletedExplicitFormula_autocorrelation_contourFamily f
  let rightKernel : ℝ → ℂ :=
    zetaCompletedExplicitFormulaInverseGammaRightAffineKernel
      probe family
  let criticalKernel : ℝ → ℂ :=
    zetaCompletedCriticalInverseGammaSeedKernel f
  let rightIntegrable :
      Integrable rightKernel (volume : Measure ℝ) :=
    zetaCompletedExplicitFormulaInverseGammaRightAffineKernel_integrable
      probe family analyticPackage
  let rightStarIntegrable :
      Integrable (fun t : ℝ => star (rightKernel t))
        (volume : Measure ℝ) :=
    Complex.conjLIE.toLinearIsometry.integrable_comp rightIntegrable
  let criticalIntegrable :
      Integrable criticalKernel (volume : Measure ℝ) :=
    zetaCompletedCriticalInverseGammaSeedKernel_integrable f
  let criticalStarIntegrable :
      Integrable (fun t : ℝ => star (criticalKernel t))
        (volume : Measure ℝ) :=
    Complex.conjLIE.toLinearIsometry.integrable_comp criticalIntegrable
  let affineFunctionEquality :
      zetaCompletedAffineInverseGammaRightReflectedDifferenceKernel
          probe family =
        fun t : ℝ => rightKernel t + star (rightKernel t) :=
    funext
      (fun t : ℝ =>
        zetaCompletedAffineInverseGamma_convolutionAutocorrelation_eq_right_add_star
          f family t)
  let criticalFunctionEquality :
      zetaCompletedHermitianInverseGammaIntegrand probe =
        fun t : ℝ => criticalKernel t + star (criticalKernel t) :=
    funext
      (fun t : ℝ =>
        zetaCompletedHermitianInverseGamma_convolutionAutocorrelation_eq_seed_add_star
          f t)
  let affineIntegralEquality :
      (∫ t : ℝ,
        zetaCompletedAffineInverseGammaRightReflectedDifferenceKernel
          probe family t) =
        (∫ t : ℝ, rightKernel t) +
          star (∫ t : ℝ, rightKernel t) :=
    Eq.trans
      (congrArg
        (fun candidate : ℝ → ℂ => ∫ t : ℝ, candidate t)
        affineFunctionEquality)
      (Eq.trans
        (integral_add rightIntegrable rightStarIntegrable)
        (congrArg
          (fun value : ℂ => (∫ t : ℝ, rightKernel t) + value)
          integral_conj))
  let criticalIntegralEquality :
      (∫ t : ℝ,
        zetaCompletedHermitianInverseGammaIntegrand probe t) =
        (∫ t : ℝ, criticalKernel t) +
          star (∫ t : ℝ, criticalKernel t) :=
    Eq.trans
      (congrArg
        (fun candidate : ℝ → ℂ => ∫ t : ℝ, candidate t)
        criticalFunctionEquality)
      (Eq.trans
        (integral_add criticalIntegrable criticalStarIntegrable)
        (congrArg
          (fun value : ℂ => (∫ t : ℝ, criticalKernel t) + value)
          integral_conj))
  let oneSidedEquality :
      (∫ t : ℝ, rightKernel t) =
        ∫ t : ℝ, criticalKernel t :=
    zetaCompletedAffineInverseGamma_oneSided_integral_eq_critical_of_analyticPackage_owner
      f analyticPackage
  Eq.trans affineIntegralEquality
    (Eq.trans
      (congrArg₂ HAdd.hAdd oneSidedEquality
        (congrArg star oneSidedEquality))
      criticalIntegralEquality.symm)

theorem zetaCompletedAffineRegularInverseGamma_integral_eq_critical_of_phiControl_gammaBinet_owner
    (f : ZetaAdmissibleFunction)
    (hPhi : ZetaPhiAnalyticControl (convolutionAutocorrelation f)) :
    let probe : ZetaAdmissibleFunction := convolutionAutocorrelation f
    let family : ExplicitFormulaContourFamily :=
      zetaCompletedExplicitFormula_autocorrelation_contourFamily f
    (∫ t : ℝ,
      zetaCompletedAffineInverseGammaRightReflectedDifferenceKernel
        probe family t) =
      ∫ t : ℝ,
        zetaCompletedHermitianInverseGammaIntegrand probe t :=
  let probe : ZetaAdmissibleFunction := convolutionAutocorrelation f
  let family : ExplicitFormulaContourFamily :=
    zetaCompletedExplicitFormula_autocorrelation_contourFamily f
  let rightKernel : ℝ → ℂ :=
    zetaCompletedExplicitFormulaInverseGammaRightAffineKernel
      probe family
  let criticalKernel : ℝ → ℂ :=
    zetaCompletedCriticalInverseGammaSeedKernel f
  let rightIntegrable :
      Integrable rightKernel (volume : Measure ℝ) :=
    zetaCompletedExplicitFormulaInverseGammaRightAffineKernel_integrable_of_phiControl_gammaBinet
      probe family hPhi
  let rightStarIntegrable :
      Integrable (fun t : ℝ => star (rightKernel t))
        (volume : Measure ℝ) :=
    Complex.conjLIE.toLinearIsometry.integrable_comp rightIntegrable
  let criticalIntegrable :
      Integrable criticalKernel (volume : Measure ℝ) :=
    zetaCompletedCriticalInverseGammaSeedKernel_integrable f
  let criticalStarIntegrable :
      Integrable (fun t : ℝ => star (criticalKernel t))
        (volume : Measure ℝ) :=
    Complex.conjLIE.toLinearIsometry.integrable_comp criticalIntegrable
  let affineFunctionEquality :
      zetaCompletedAffineInverseGammaRightReflectedDifferenceKernel
          probe family =
        fun t : ℝ => rightKernel t + star (rightKernel t) :=
    funext
      (fun t : ℝ =>
        zetaCompletedAffineInverseGamma_convolutionAutocorrelation_eq_right_add_star
          f family t)
  let criticalFunctionEquality :
      zetaCompletedHermitianInverseGammaIntegrand probe =
        fun t : ℝ => criticalKernel t + star (criticalKernel t) :=
    funext
      (fun t : ℝ =>
        zetaCompletedHermitianInverseGamma_convolutionAutocorrelation_eq_seed_add_star
          f t)
  let affineIntegralEquality :
      (∫ t : ℝ,
        zetaCompletedAffineInverseGammaRightReflectedDifferenceKernel
          probe family t) =
        (∫ t : ℝ, rightKernel t) +
          star (∫ t : ℝ, rightKernel t) :=
    Eq.trans
      (congrArg
        (fun candidate : ℝ → ℂ => ∫ t : ℝ, candidate t)
        affineFunctionEquality)
      (Eq.trans
        (integral_add rightIntegrable rightStarIntegrable)
        (congrArg
          (fun value : ℂ => (∫ t : ℝ, rightKernel t) + value)
          integral_conj))
  let criticalIntegralEquality :
      (∫ t : ℝ,
        zetaCompletedHermitianInverseGammaIntegrand probe t) =
        (∫ t : ℝ, criticalKernel t) +
          star (∫ t : ℝ, criticalKernel t) :=
    Eq.trans
      (congrArg
        (fun candidate : ℝ → ℂ => ∫ t : ℝ, candidate t)
        criticalFunctionEquality)
      (Eq.trans
        (integral_add criticalIntegrable criticalStarIntegrable)
        (congrArg
          (fun value : ℂ => (∫ t : ℝ, criticalKernel t) + value)
          integral_conj))
  let oneSidedEquality :
      (∫ t : ℝ, rightKernel t) =
        ∫ t : ℝ, criticalKernel t :=
    zetaCompletedAffineInverseGamma_oneSided_integral_eq_critical_of_phiControl_gammaBinet_owner
      f hPhi
  Eq.trans affineIntegralEquality
    (Eq.trans
      (congrArg₂ HAdd.hAdd oneSidedEquality
        (congrArg star oneSidedEquality))
      criticalIntegralEquality.symm)

end ZetaAdmissibleFunction

end

end LFunctions
end Boundary
