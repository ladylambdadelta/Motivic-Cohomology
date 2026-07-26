import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaZeroKreinGram.WeilCriterion.OwnerParts.CanonicalScheduledPolynomialPackageParts.VariableCauchyPathBounds
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaCompletedLogDerivativeControl.CauchyBoundData
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaZeroKreinGram.WeilCriterion.OwnerParts.CauchyPathCarrierDataPackage

/-!
# Canonical carrier separation structures

This file owns the finite-local carrier-bound records and their conversion
into the variable Cauchy path data consumed by the final RH lane.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open scoped Topology

namespace ZetaAdmissibleFunction

/-- Explicit local zeta-side Cauchy bounds on the canonical scheduled paths,
with one quotient constant controlling all local choices. -/
structure CanonicalScheduledZetaSideCarrierSeparationConstantBounds
    (f : ZetaAdmissibleFunction) (K : ℕ) where
  boundConstant : ℝ
  boundConstant_pos : 0 < boundConstant
  topRadius : ℝ → ℝ → ℝ
  topAmplitude : ℝ → ℝ → ℝ
  topValueLower : ℝ → ℝ → ℝ
  bottomRadius : ℝ → ℝ → ℝ
  bottomAmplitude : ℝ → ℝ → ℝ
  bottomValueLower : ℝ → ℝ → ℝ
  topRadius_pos : ∀ u x : ℝ, 0 < topRadius u x
  topValueLower_pos : ∀ u x : ℝ, 0 < topValueLower u x
  bottomRadius_pos : ∀ u x : ℝ, 0 < bottomRadius u x
  bottomValueLower_pos : ∀ u x : ℝ, 0 < bottomValueLower u x
  topDiffCont :
    ∀ u x : ℝ,
      x ∈ Set.uIcc
        (zetaCompletedExplicitFormula_autocorrelation_contourFamily f).c
        (1 - (zetaCompletedExplicitFormula_autocorrelation_contourFamily f).c) →
      DiffContOnCl ℂ zetaSideFactor
        (Metric.ball
          (zetaCompletedExplicitFormulaTopPath
            ((zetaCompletedExplicitFormula_autocorrelation_contourFamily f).rectangle
              ((zetaCompletedExplicitFormulaAutocorrelationCofinalHeightSchedule f).height u))
            x)
          (topRadius u x))
  bottomDiffCont :
    ∀ u x : ℝ,
      x ∈ Set.uIcc
        (zetaCompletedExplicitFormula_autocorrelation_contourFamily f).c
        (1 - (zetaCompletedExplicitFormula_autocorrelation_contourFamily f).c) →
      DiffContOnCl ℂ zetaSideFactor
        (Metric.ball
          (zetaCompletedExplicitFormulaBottomPath
            ((zetaCompletedExplicitFormula_autocorrelation_contourFamily f).rectangle
              ((zetaCompletedExplicitFormulaAutocorrelationCofinalHeightSchedule f).height u))
            x)
          (bottomRadius u x))
  topSphereBound :
    ∀ u x : ℝ,
      x ∈ Set.uIcc
        (zetaCompletedExplicitFormula_autocorrelation_contourFamily f).c
        (1 - (zetaCompletedExplicitFormula_autocorrelation_contourFamily f).c) →
      ∀ w : ℂ,
        w ∈
          Metric.sphere
            (zetaCompletedExplicitFormulaTopPath
              ((zetaCompletedExplicitFormula_autocorrelation_contourFamily f).rectangle
                ((zetaCompletedExplicitFormulaAutocorrelationCofinalHeightSchedule f).height u))
              x)
            (topRadius u x) →
        ‖zetaSideFactor w‖ ≤
          topAmplitude u x *
            (1 +
              ‖(zetaCompletedExplicitFormulaAutocorrelationCofinalHeightSchedule f).height u‖) ^ K
  bottomSphereBound :
    ∀ u x : ℝ,
      x ∈ Set.uIcc
        (zetaCompletedExplicitFormula_autocorrelation_contourFamily f).c
        (1 - (zetaCompletedExplicitFormula_autocorrelation_contourFamily f).c) →
      ∀ w : ℂ,
        w ∈
          Metric.sphere
            (zetaCompletedExplicitFormulaBottomPath
              ((zetaCompletedExplicitFormula_autocorrelation_contourFamily f).rectangle
                ((zetaCompletedExplicitFormulaAutocorrelationCofinalHeightSchedule f).height u))
              x)
            (bottomRadius u x) →
        ‖zetaSideFactor w‖ ≤
          bottomAmplitude u x *
            (1 +
              ‖(zetaCompletedExplicitFormulaAutocorrelationCofinalHeightSchedule f).height u‖) ^ K
  topValueLower_bound :
    ∀ u x : ℝ,
      x ∈ Set.uIcc
        (zetaCompletedExplicitFormula_autocorrelation_contourFamily f).c
        (1 - (zetaCompletedExplicitFormula_autocorrelation_contourFamily f).c) →
      topValueLower u x ≤
        ‖zetaSideFactor
          (zetaCompletedExplicitFormulaTopPath
            ((zetaCompletedExplicitFormula_autocorrelation_contourFamily f).rectangle
              ((zetaCompletedExplicitFormulaAutocorrelationCofinalHeightSchedule f).height u))
            x)‖
  bottomValueLower_bound :
    ∀ u x : ℝ,
      x ∈ Set.uIcc
        (zetaCompletedExplicitFormula_autocorrelation_contourFamily f).c
        (1 - (zetaCompletedExplicitFormula_autocorrelation_contourFamily f).c) →
      bottomValueLower u x ≤
        ‖zetaSideFactor
          (zetaCompletedExplicitFormulaBottomPath
            ((zetaCompletedExplicitFormula_autocorrelation_contourFamily f).rectangle
              ((zetaCompletedExplicitFormulaAutocorrelationCofinalHeightSchedule f).height u))
            x)‖
  topQuotientBound :
    ∀ u x : ℝ,
      x ∈ Set.uIcc
        (zetaCompletedExplicitFormula_autocorrelation_contourFamily f).c
        (1 - (zetaCompletedExplicitFormula_autocorrelation_contourFamily f).c) →
      ((topAmplitude u x / topRadius u x) / topValueLower u x) ≤ boundConstant
  bottomQuotientBound :
    ∀ u x : ℝ,
      x ∈ Set.uIcc
        (zetaCompletedExplicitFormula_autocorrelation_contourFamily f).c
        (1 - (zetaCompletedExplicitFormula_autocorrelation_contourFamily f).c) →
      ((bottomAmplitude u x / bottomRadius u x) / bottomValueLower u x) ≤ boundConstant

/-- Explicit local inverse-Gamma Cauchy bounds on the canonical scheduled paths,
with one quotient constant controlling all local choices. -/
structure CanonicalScheduledInverseGammaCarrierSeparationConstantBounds
    (f : ZetaAdmissibleFunction) (K : ℕ) where
  boundConstant : ℝ
  boundConstant_pos : 0 < boundConstant
  topRadius : ℝ → ℝ → ℝ
  topAmplitude : ℝ → ℝ → ℝ
  topValueLower : ℝ → ℝ → ℝ
  bottomRadius : ℝ → ℝ → ℝ
  bottomAmplitude : ℝ → ℝ → ℝ
  bottomValueLower : ℝ → ℝ → ℝ
  topRadius_pos : ∀ u x : ℝ, 0 < topRadius u x
  topValueLower_pos : ∀ u x : ℝ, 0 < topValueLower u x
  bottomRadius_pos : ∀ u x : ℝ, 0 < bottomRadius u x
  bottomValueLower_pos : ∀ u x : ℝ, 0 < bottomValueLower u x
  topDiffCont :
    ∀ u x : ℝ,
      x ∈ Set.uIcc
        (zetaCompletedExplicitFormula_autocorrelation_contourFamily f).c
        (1 - (zetaCompletedExplicitFormula_autocorrelation_contourFamily f).c) →
      DiffContOnCl ℂ
        (fun w : ℂ => (Complex.Gammaℝ w)⁻¹)
        (Metric.ball
          (zetaCompletedExplicitFormulaTopPath
            ((zetaCompletedExplicitFormula_autocorrelation_contourFamily f).rectangle
              ((zetaCompletedExplicitFormulaAutocorrelationCofinalHeightSchedule f).height u))
            x)
          (topRadius u x))
  bottomDiffCont :
    ∀ u x : ℝ,
      x ∈ Set.uIcc
        (zetaCompletedExplicitFormula_autocorrelation_contourFamily f).c
        (1 - (zetaCompletedExplicitFormula_autocorrelation_contourFamily f).c) →
      DiffContOnCl ℂ
        (fun w : ℂ => (Complex.Gammaℝ w)⁻¹)
        (Metric.ball
          (zetaCompletedExplicitFormulaBottomPath
            ((zetaCompletedExplicitFormula_autocorrelation_contourFamily f).rectangle
              ((zetaCompletedExplicitFormulaAutocorrelationCofinalHeightSchedule f).height u))
            x)
          (bottomRadius u x))
  topSphereBound :
    ∀ u x : ℝ,
      x ∈ Set.uIcc
        (zetaCompletedExplicitFormula_autocorrelation_contourFamily f).c
        (1 - (zetaCompletedExplicitFormula_autocorrelation_contourFamily f).c) →
      ∀ w : ℂ,
        w ∈
          Metric.sphere
            (zetaCompletedExplicitFormulaTopPath
              ((zetaCompletedExplicitFormula_autocorrelation_contourFamily f).rectangle
                ((zetaCompletedExplicitFormulaAutocorrelationCofinalHeightSchedule f).height u))
              x)
            (topRadius u x) →
        ‖(Complex.Gammaℝ w)⁻¹‖ ≤
          topAmplitude u x *
            (1 +
              ‖(zetaCompletedExplicitFormulaAutocorrelationCofinalHeightSchedule f).height u‖) ^ K
  bottomSphereBound :
    ∀ u x : ℝ,
      x ∈ Set.uIcc
        (zetaCompletedExplicitFormula_autocorrelation_contourFamily f).c
        (1 - (zetaCompletedExplicitFormula_autocorrelation_contourFamily f).c) →
      ∀ w : ℂ,
        w ∈
          Metric.sphere
            (zetaCompletedExplicitFormulaBottomPath
              ((zetaCompletedExplicitFormula_autocorrelation_contourFamily f).rectangle
                ((zetaCompletedExplicitFormulaAutocorrelationCofinalHeightSchedule f).height u))
              x)
            (bottomRadius u x) →
        ‖(Complex.Gammaℝ w)⁻¹‖ ≤
          bottomAmplitude u x *
            (1 +
              ‖(zetaCompletedExplicitFormulaAutocorrelationCofinalHeightSchedule f).height u‖) ^ K
  topValueLower_bound :
    ∀ u x : ℝ,
      x ∈ Set.uIcc
        (zetaCompletedExplicitFormula_autocorrelation_contourFamily f).c
        (1 - (zetaCompletedExplicitFormula_autocorrelation_contourFamily f).c) →
      topValueLower u x ≤
        ‖(Complex.Gammaℝ
          (zetaCompletedExplicitFormulaTopPath
            ((zetaCompletedExplicitFormula_autocorrelation_contourFamily f).rectangle
              ((zetaCompletedExplicitFormulaAutocorrelationCofinalHeightSchedule f).height u))
            x))⁻¹‖
  bottomValueLower_bound :
    ∀ u x : ℝ,
      x ∈ Set.uIcc
        (zetaCompletedExplicitFormula_autocorrelation_contourFamily f).c
        (1 - (zetaCompletedExplicitFormula_autocorrelation_contourFamily f).c) →
      bottomValueLower u x ≤
        ‖(Complex.Gammaℝ
          (zetaCompletedExplicitFormulaBottomPath
            ((zetaCompletedExplicitFormula_autocorrelation_contourFamily f).rectangle
              ((zetaCompletedExplicitFormulaAutocorrelationCofinalHeightSchedule f).height u))
            x))⁻¹‖
  topQuotientBound :
    ∀ u x : ℝ,
      x ∈ Set.uIcc
        (zetaCompletedExplicitFormula_autocorrelation_contourFamily f).c
        (1 - (zetaCompletedExplicitFormula_autocorrelation_contourFamily f).c) →
      ((topAmplitude u x / topRadius u x) / topValueLower u x) ≤ boundConstant
  bottomQuotientBound :
    ∀ u x : ℝ,
      x ∈ Set.uIcc
        (zetaCompletedExplicitFormula_autocorrelation_contourFamily f).c
        (1 - (zetaCompletedExplicitFormula_autocorrelation_contourFamily f).c) →
      ((bottomAmplitude u x / bottomRadius u x) / bottomValueLower u x) ≤ boundConstant

def canonicalScheduledCarrierCommonBound
    {f : ZetaAdmissibleFunction} {K : ℕ}
    (zetaData : CanonicalScheduledZetaSideCarrierSeparationConstantBounds f K)
    (gammaData : CanonicalScheduledInverseGammaCarrierSeparationConstantBounds f K) :
    ℝ := max zetaData.boundConstant gammaData.boundConstant

theorem canonicalScheduledCarrierCommonBound_pos
    {f : ZetaAdmissibleFunction} {K : ℕ}
    (zetaData : CanonicalScheduledZetaSideCarrierSeparationConstantBounds f K)
    (gammaData : CanonicalScheduledInverseGammaCarrierSeparationConstantBounds f K) :
    0 < canonicalScheduledCarrierCommonBound zetaData gammaData := by
  exact lt_max zetaData.boundConstant_pos gammaData.boundConstant_pos

theorem canonicalScheduledCarrierCommonBound_dominates_zeta
    {f : ZetaAdmissibleFunction} {K : ℕ}
    (zetaData : CanonicalScheduledZetaSideCarrierSeparationConstantBounds f K)
    (gammaData : CanonicalScheduledInverseGammaCarrierSeparationConstantBounds f K) :
    zetaData.boundConstant ≤ canonicalScheduledCarrierCommonBound zetaData gammaData :=
  le_max_left zetaData.boundConstant gammaData.boundConstant

theorem canonicalScheduledCarrierCommonBound_dominates_inverseGamma
    {f : ZetaAdmissibleFunction} {K : ℕ}
    (zetaData : CanonicalScheduledZetaSideCarrierSeparationConstantBounds f K)
    (gammaData : CanonicalScheduledInverseGammaCarrierSeparationConstantBounds f K) :
    gammaData.boundConstant ≤ canonicalScheduledCarrierCommonBound zetaData gammaData :=
  le_max_right zetaData.boundConstant gammaData.boundConstant

def CanonicalScheduledZetaSideCarrierSeparationConstantBounds.toVariableCauchyPathData
    {f : ZetaAdmissibleFunction} {K : ℕ}
    (data : CanonicalScheduledZetaSideCarrierSeparationConstantBounds f K) :
    CanonicalScheduledZetaSideVariableCauchyPathData f K :=
  { boundConstant := data.boundConstant
    boundConstant_pos := data.boundConstant_pos
    topRadius := data.topRadius
    topAmplitude := data.topAmplitude
    topValueLower := data.topValueLower
    bottomRadius := data.bottomRadius
    bottomAmplitude := data.bottomAmplitude
    bottomValueLower := data.bottomValueLower
    topRadius_pos := data.topRadius_pos
    topValueLower_pos := data.topValueLower_pos
    bottomRadius_pos := data.bottomRadius_pos
    bottomValueLower_pos := data.bottomValueLower_pos
    topDiffCont := data.topDiffCont
    bottomDiffCont := data.bottomDiffCont
    topSphereBound := data.topSphereBound
    bottomSphereBound := data.bottomSphereBound
    topValueLower_bound := data.topValueLower_bound
    bottomValueLower_bound := data.bottomValueLower_bound
    topQuotientBound := fun u x hx =>
      (data.topQuotientBound u x hx).trans
        (le_mul_of_one_le_right (le_of_lt data.boundConstant_pos)
          (one_le_one_add_norm_pow
            ((zetaCompletedExplicitFormulaAutocorrelationCofinalHeightSchedule f).height u) K))
    bottomQuotientBound := fun u x hx =>
      (data.bottomQuotientBound u x hx).trans
        (le_mul_of_one_le_right (le_of_lt data.boundConstant_pos)
          (one_le_one_add_norm_pow
            ((zetaCompletedExplicitFormulaAutocorrelationCofinalHeightSchedule f).height u) K)) }

def CanonicalScheduledZetaSideCarrierSeparationConstantBounds.toVariableCauchyPathData_with_common_bound
    {f : ZetaAdmissibleFunction} {K : ℕ}
    (data : CanonicalScheduledZetaSideCarrierSeparationConstantBounds f K)
    (gammaData : CanonicalScheduledInverseGammaCarrierSeparationConstantBounds f K) :
    CanonicalScheduledZetaSideVariableCauchyPathData f K := by
  let base := data.toVariableCauchyPathData
  let Q := canonicalScheduledCarrierCommonBound data gammaData
  have hQ : data.boundConstant ≤ Q :=
    canonicalScheduledCarrierCommonBound_dominates_zeta data gammaData
  { base with
    boundConstant := Q
    boundConstant_pos := canonicalScheduledCarrierCommonBound_pos data gammaData
    topQuotientBound := fun u x hx =>
      (base.topQuotientBound u x hx).trans
      (mul_le_mul_of_nonneg_right hQ
        (pow_nonneg
          (add_nonneg (by exact zero_le_one)
            (norm_nonneg
              ((zetaCompletedExplicitFormulaAutocorrelationCofinalHeightSchedule f).height u))) K))
    bottomQuotientBound := fun u x hx =>
      (base.bottomQuotientBound u x hx).trans
      (mul_le_mul_of_nonneg_right hQ
        (pow_nonneg
          (add_nonneg (by exact zero_le_one)
            (norm_nonneg
              ((zetaCompletedExplicitFormulaAutocorrelationCofinalHeightSchedule f).height u))) K)) }

def CanonicalScheduledInverseGammaCarrierSeparationConstantBounds.toVariableCauchyPathData
    {f : ZetaAdmissibleFunction} {K : ℕ}
    (data : CanonicalScheduledInverseGammaCarrierSeparationConstantBounds f K) :
    CanonicalScheduledInverseGammaVariableCauchyPathData f K :=
  { boundConstant := data.boundConstant
    boundConstant_pos := data.boundConstant_pos
    topRadius := data.topRadius
    topAmplitude := data.topAmplitude
    topValueLower := data.topValueLower
    bottomRadius := data.bottomRadius
    bottomAmplitude := data.bottomAmplitude
    bottomValueLower := data.bottomValueLower
    topRadius_pos := data.topRadius_pos
    topValueLower_pos := data.topValueLower_pos
    bottomRadius_pos := data.bottomRadius_pos
    bottomValueLower_pos := data.bottomValueLower_pos
    topDiffCont := data.topDiffCont
    bottomDiffCont := data.bottomDiffCont
    topSphereBound := data.topSphereBound
    bottomSphereBound := data.bottomSphereBound
    topValueLower_bound := data.topValueLower_bound
    bottomValueLower_bound := data.bottomValueLower_bound
    topQuotientBound := fun u x hx =>
      (data.topQuotientBound u x hx).trans
        (le_mul_of_one_le_right (le_of_lt data.boundConstant_pos)
          (one_le_one_add_norm_pow
            ((zetaCompletedExplicitFormulaAutocorrelationCofinalHeightSchedule f).height u) K))
    bottomQuotientBound := fun u x hx =>
      (data.bottomQuotientBound u x hx).trans
        (le_mul_of_one_le_right (le_of_lt data.boundConstant_pos)
          (one_le_one_add_norm_pow
            ((zetaCompletedExplicitFormulaAutocorrelationCofinalHeightSchedule f).height u) K)) }

def CanonicalScheduledInverseGammaCarrierSeparationConstantBounds.toVariableCauchyPathData_with_common_bound
    {f : ZetaAdmissibleFunction} {K : ℕ}
    (data : CanonicalScheduledInverseGammaCarrierSeparationConstantBounds f K)
    (zetaData : CanonicalScheduledZetaSideCarrierSeparationConstantBounds f K) :
    CanonicalScheduledInverseGammaVariableCauchyPathData f K := by
  let base := data.toVariableCauchyPathData
  let Q := canonicalScheduledCarrierCommonBound zetaData data
  have hQ : data.boundConstant ≤ Q :=
    canonicalScheduledCarrierCommonBound_dominates_inverseGamma zetaData data
  { base with
    boundConstant := Q
    boundConstant_pos := canonicalScheduledCarrierCommonBound_pos zetaData data
    topQuotientBound := fun u x hx =>
      (base.topQuotientBound u x hx).trans
      (mul_le_mul_of_nonneg_right hQ
        (pow_nonneg
          (add_nonneg (by exact zero_le_one)
            (norm_nonneg
              ((zetaCompletedExplicitFormulaAutocorrelationCofinalHeightSchedule f).height u))) K))
    bottomQuotientBound := fun u x hx =>
      (base.bottomQuotientBound u x hx).trans
      (mul_le_mul_of_nonneg_right hQ
        (pow_nonneg
          (add_nonneg (by exact zero_le_one)
            (norm_nonneg
              ((zetaCompletedExplicitFormulaAutocorrelationCofinalHeightSchedule f).height u))) K)) }

def CanonicalScheduledZetaSideCauchyPathData.toSeparationBounds
    {f : ZetaAdmissibleFunction} {K : ℕ}
    (data : CanonicalScheduledZetaSideCauchyPathData f K) :
    CanonicalScheduledZetaSideCarrierSeparationConstantBounds f K := by
  let quotient : ℝ := (data.amplitude / data.radius) / data.valueLower
  refine
    { boundConstant := quotient
      boundConstant_pos :=
        div_pos (div_pos data.amplitude_pos data.radius_pos)
          data.valueLower_pos
      topRadius := fun u x => data.radius
      topAmplitude := fun u x => data.amplitude
      topValueLower := fun u x => data.valueLower
      bottomRadius := fun u x => data.radius
      bottomAmplitude := fun u x => data.amplitude
      bottomValueLower := fun u x => data.valueLower
      topRadius_pos := fun u x => data.radius_pos
      topValueLower_pos := fun u x => data.valueLower_pos
      bottomRadius_pos := fun u x => data.radius_pos
      bottomValueLower_pos := fun u x => data.valueLower_pos
      topDiffCont := data.top_diffCont
      bottomDiffCont := data.bottom_diffCont
      topSphereBound := data.top_sphereBound
      bottomSphereBound := data.bottom_sphereBound
      topValueLower_bound := data.top_valueLower
      bottomValueLower_bound := data.bottom_valueLower
      topQuotientBound := fun u x hx => le_rfl
      bottomQuotientBound := fun u x hx => le_rfl }

def CanonicalScheduledInverseGammaCauchyPathData.toSeparationBounds
    {f : ZetaAdmissibleFunction} {K : ℕ}
    (data : CanonicalScheduledInverseGammaCauchyPathData f K) :
    CanonicalScheduledInverseGammaCarrierSeparationConstantBounds f K := by
  let quotient : ℝ := (data.amplitude / data.radius) / data.valueLower
  refine
    { boundConstant := quotient
      boundConstant_pos :=
        div_pos (div_pos data.amplitude_pos data.radius_pos)
          data.valueLower_pos
      topRadius := fun u x => data.radius
      topAmplitude := fun u x => data.amplitude
      topValueLower := fun u x => data.valueLower
      bottomRadius := fun u x => data.radius
      bottomAmplitude := fun u x => data.amplitude
      bottomValueLower := fun u x => data.valueLower
      topRadius_pos := fun u x => data.radius_pos
      topValueLower_pos := fun u x => data.valueLower_pos
      bottomRadius_pos := fun u x => data.radius_pos
      bottomValueLower_pos := fun u x => data.valueLower_pos
      topDiffCont := data.top_diffCont
      bottomDiffCont := data.bottom_diffCont
      topSphereBound := data.top_sphereBound
      bottomSphereBound := data.bottom_sphereBound
      topValueLower_bound := data.top_valueLower
      bottomValueLower_bound := data.bottom_valueLower
      topQuotientBound := fun u x hx => le_rfl
      bottomQuotientBound := fun u x hx => le_rfl }

def canonicalScheduledZetaSideCarrierSeparationConstantBounds_of_pathData_owner
    (K : ZetaAdmissibleFunction → ℕ)
    (data : ∀ f : ZetaAdmissibleFunction,
      CanonicalScheduledZetaSideCauchyPathData f (K f)) :
    ∀ f : ZetaAdmissibleFunction,
      CanonicalScheduledZetaSideCarrierSeparationConstantBounds f (K f) :=
  fun f => (data f).toSeparationBounds

def canonicalScheduledInverseGammaCarrierSeparationConstantBounds_of_pathData_owner
    (K : ZetaAdmissibleFunction → ℕ)
    (data : ∀ f : ZetaAdmissibleFunction,
      CanonicalScheduledInverseGammaCauchyPathData f (K f)) :
    ∀ f : ZetaAdmissibleFunction,
      CanonicalScheduledInverseGammaCarrierSeparationConstantBounds f (K f) :=
  fun f => (data f).toSeparationBounds

def canonicalScheduledCarrierSeparationConstantBounds_of_pathData_owner
    (K : ZetaAdmissibleFunction → ℕ)
    (zetaData : ∀ f : ZetaAdmissibleFunction,
      CanonicalScheduledZetaSideCauchyPathData f (K f))
    (gammaData : ∀ f : ZetaAdmissibleFunction,
      CanonicalScheduledInverseGammaCauchyPathData f (K f)) :
    (∀ f : ZetaAdmissibleFunction,
      CanonicalScheduledZetaSideCarrierSeparationConstantBounds f (K f)) ×
    (∀ f : ZetaAdmissibleFunction,
      CanonicalScheduledInverseGammaCarrierSeparationConstantBounds f (K f)) :=
  (canonicalScheduledZetaSideCarrierSeparationConstantBounds_of_pathData_owner
      K zetaData,
    canonicalScheduledInverseGammaCarrierSeparationConstantBounds_of_pathData_owner
      K gammaData)

def canonicalScheduledCarrierCauchyData_of_pathData_owner
    (K : ZetaAdmissibleFunction → ℕ)
    (zetaData : ∀ f : ZetaAdmissibleFunction,
      CanonicalScheduledZetaSideCauchyPathData f (K f))
    (gammaData : ∀ f : ZetaAdmissibleFunction,
      CanonicalScheduledInverseGammaCauchyPathData f (K f)) :
    CanonicalScheduledCarrierCauchyData K :=
  CanonicalScheduledCarrierCauchyData.of_pathData zetaData gammaData

/-- Zeta-side carrier separation constants for every probe assemble into the
variable Cauchy family. -/
def canonicalScheduledZetaSideVariableCauchyPathData_of_carrierSeparationConstantBounds_owner
    (K : ZetaAdmissibleFunction → ℕ)
    (bounds :
      ∀ f : ZetaAdmissibleFunction,
        CanonicalScheduledZetaSideCarrierSeparationConstantBounds f (K f)) :
    ∀ f : ZetaAdmissibleFunction,
      CanonicalScheduledZetaSideVariableCauchyPathData f (K f) :=
  fun f =>
    (bounds f).toVariableCauchyPathData

/-- Inverse-Gamma carrier separation constants for every probe assemble into
the variable Cauchy family. -/
def canonicalScheduledInverseGammaVariableCauchyPathData_of_carrierSeparationConstantBounds_owner
    (K : ZetaAdmissibleFunction → ℕ)
    (bounds :
      ∀ f : ZetaAdmissibleFunction,
        CanonicalScheduledInverseGammaCarrierSeparationConstantBounds f (K f)) :
    ∀ f : ZetaAdmissibleFunction,
      CanonicalScheduledInverseGammaVariableCauchyPathData f (K f) :=
  fun f =>
    (bounds f).toVariableCauchyPathData

/-- The paired carrier-separation owners assemble the complete variable Cauchy
data consumed by the final RH route. -/
def canonicalScheduledVariableCauchyPathData_of_carrierSeparationConstantBounds_owner
    (K : ZetaAdmissibleFunction → ℕ)
    (zetaBounds :
      ∀ f : ZetaAdmissibleFunction,
        CanonicalScheduledZetaSideCarrierSeparationConstantBounds f (K f))
    (gammaBounds :
      ∀ f : ZetaAdmissibleFunction,
        CanonicalScheduledInverseGammaCarrierSeparationConstantBounds f (K f)) :
    ∀ f : ZetaAdmissibleFunction,
      CanonicalScheduledZetaSideVariableCauchyPathData f (K f) ×
        CanonicalScheduledInverseGammaVariableCauchyPathData f (K f) :=
  fun f =>
    ⟨(zetaBounds f).toVariableCauchyPathData,
      (gammaBounds f).toVariableCauchyPathData⟩

def canonicalScheduledCommonBoundPolynomialAnalyticPackage_owner
    (f : ZetaAdmissibleFunction) (K : ℕ)
    (zetaData : CanonicalScheduledZetaSideCarrierSeparationConstantBounds f K)
    (gammaData : CanonicalScheduledInverseGammaCarrierSeparationConstantBounds f K) :
    ExplicitFormulaScheduledPolynomialFamilyAnalyticPackage
      (convolutionAutocorrelation f)
      (zetaCompletedExplicitFormula_autocorrelation_contourFamily f) :=
  zetaCompletedExplicitFormulaAutocorrelationScheduledPolynomialFamilyAnalyticPackage_of_variableCauchyPathData
    f K
    (zetaData.toVariableCauchyPathData_with_common_bound gammaData)
    (gammaData.toVariableCauchyPathData_with_common_bound zetaData)

end ZetaAdmissibleFunction

end
end LFunctions
end Boundary
