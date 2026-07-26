import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaZeroKreinGram.WeilCriterion.OwnerParts.CanonicalScheduledPolynomialPackageParts.FactorPathBounds

/-! 
# Canonical scheduled polynomial package from variable local Cauchy data

This file owns the local-radius replacement for the too-strong uniform Cauchy
path-data surface.  The downstream horizontal package only needs a polynomial
bound for the Cauchy quotient, not a single radius or lower bound shared by the
whole infinite scheduled carrier.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open scoped Topology

namespace ZetaAdmissibleFunction

structure CanonicalScheduledZetaSideVariableCauchyPathData
    (f : ZetaAdmissibleFunction) (K : ℕ) where
  boundConstant : ℝ
  boundConstant_pos : 0 < boundConstant
  topRadius : ℝ → ℝ → ℝ
  topAmplitude : ℝ → ℝ → ℝ
  topValueLower : ℝ → ℝ → ℝ
  bottomRadius : ℝ → ℝ → ℝ
  bottomAmplitude : ℝ → ℝ → ℝ
  bottomValueLower : ℝ → ℝ → ℝ
  topRadius_pos :
    ∀ u x : ℝ, 0 < topRadius u x
  topValueLower_pos :
    ∀ u x : ℝ, 0 < topValueLower u x
  bottomRadius_pos :
    ∀ u x : ℝ, 0 < bottomRadius u x
  bottomValueLower_pos :
    ∀ u x : ℝ, 0 < bottomValueLower u x
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
      ((topAmplitude u x / topRadius u x) / topValueLower u x) ≤
        boundConstant *
          (1 + ‖(zetaCompletedExplicitFormulaAutocorrelationCofinalHeightSchedule f).height u‖) ^ K
  bottomQuotientBound :
    ∀ u x : ℝ,
      x ∈ Set.uIcc
        (zetaCompletedExplicitFormula_autocorrelation_contourFamily f).c
        (1 - (zetaCompletedExplicitFormula_autocorrelation_contourFamily f).c) →
      ((bottomAmplitude u x / bottomRadius u x) / bottomValueLower u x) ≤
        boundConstant *
          (1 + ‖(zetaCompletedExplicitFormulaAutocorrelationCofinalHeightSchedule f).height u‖) ^ K

structure CanonicalScheduledInverseGammaVariableCauchyPathData
    (f : ZetaAdmissibleFunction) (K : ℕ) where
  boundConstant : ℝ
  boundConstant_pos : 0 < boundConstant
  topRadius : ℝ → ℝ → ℝ
  topAmplitude : ℝ → ℝ → ℝ
  topValueLower : ℝ → ℝ → ℝ
  bottomRadius : ℝ → ℝ → ℝ
  bottomAmplitude : ℝ → ℝ → ℝ
  bottomValueLower : ℝ → ℝ → ℝ
  topRadius_pos :
    ∀ u x : ℝ, 0 < topRadius u x
  topValueLower_pos :
    ∀ u x : ℝ, 0 < topValueLower u x
  bottomRadius_pos :
    ∀ u x : ℝ, 0 < bottomRadius u x
  bottomValueLower_pos :
    ∀ u x : ℝ, 0 < bottomValueLower u x
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
      ((topAmplitude u x / topRadius u x) / topValueLower u x) ≤
        boundConstant *
          (1 + ‖(zetaCompletedExplicitFormulaAutocorrelationCofinalHeightSchedule f).height u‖) ^ K
  bottomQuotientBound :
    ∀ u x : ℝ,
      x ∈ Set.uIcc
        (zetaCompletedExplicitFormula_autocorrelation_contourFamily f).c
        (1 - (zetaCompletedExplicitFormula_autocorrelation_contourFamily f).c) →
      ((bottomAmplitude u x / bottomRadius u x) / bottomValueLower u x) ≤
        boundConstant *
          (1 + ‖(zetaCompletedExplicitFormulaAutocorrelationCofinalHeightSchedule f).height u‖) ^ K

theorem CanonicalScheduledZetaSideVariableCauchyPathData.topQuotientBound_of_common_constant
    {f : ZetaAdmissibleFunction} {K : ℕ}
    (data : CanonicalScheduledZetaSideVariableCauchyPathData f K)
    (Q : ℝ) (hQ : data.boundConstant ≤ Q) (u x : ℝ)
    (hx : x ∈ Set.uIcc
      (zetaCompletedExplicitFormula_autocorrelation_contourFamily f).c
      (1 - (zetaCompletedExplicitFormula_autocorrelation_contourFamily f).c)) :
    ((data.topAmplitude u x / data.topRadius u x) /
      data.topValueLower u x) ≤
      Q * (1 + ‖(zetaCompletedExplicitFormulaAutocorrelationCofinalHeightSchedule f).height u‖) ^ K := by
  exact (data.topQuotientBound u x hx).trans
    (mul_le_mul_of_nonneg_right hQ
      (pow_nonneg
        (add_nonneg (by exact zero_le_one) (norm_nonneg _)) K))

theorem CanonicalScheduledZetaSideVariableCauchyPathData.bottomQuotientBound_of_common_constant
    {f : ZetaAdmissibleFunction} {K : ℕ}
    (data : CanonicalScheduledZetaSideVariableCauchyPathData f K)
    (Q : ℝ) (hQ : data.boundConstant ≤ Q) (u x : ℝ)
    (hx : x ∈ Set.uIcc
      (zetaCompletedExplicitFormula_autocorrelation_contourFamily f).c
      (1 - (zetaCompletedExplicitFormula_autocorrelation_contourFamily f).c)) :
    ((data.bottomAmplitude u x / data.bottomRadius u x) /
      data.bottomValueLower u x) ≤
      Q * (1 + ‖(zetaCompletedExplicitFormulaAutocorrelationCofinalHeightSchedule f).height u‖) ^ K := by
  exact (data.bottomQuotientBound u x hx).trans
    (mul_le_mul_of_nonneg_right hQ
      (pow_nonneg
        (add_nonneg (by exact zero_le_one) (norm_nonneg _)) K))

def CanonicalScheduledZetaSideVariableCauchyPathData.of_uniform
    {f : ZetaAdmissibleFunction} {K : ℕ}
    (data : CanonicalScheduledZetaSideCauchyPathData f K) :
    CanonicalScheduledZetaSideVariableCauchyPathData f K :=
  { boundConstant := data.boundConstant
    boundConstant_pos := data.boundConstant_pos
    topRadius := fun _ _ => data.radius
    topAmplitude := fun _ _ => data.amplitude
    topValueLower := fun _ _ => data.valueLower
    bottomRadius := fun _ _ => data.radius
    bottomAmplitude := fun _ _ => data.amplitude
    bottomValueLower := fun _ _ => data.valueLower
    topRadius_pos := fun _ _ => data.radius_pos
    topValueLower_pos := fun _ _ => data.valueLower_pos
    bottomRadius_pos := fun _ _ => data.radius_pos
    bottomValueLower_pos := fun _ _ => data.valueLower_pos
    topDiffCont := fun u x hx => data.top_diffCont u x hx
    bottomDiffCont := fun u x hx => data.bottom_diffCont u x hx
    topSphereBound := fun u x hx w hw => data.top_sphereBound u x hx w hw
    bottomSphereBound := fun u x hx w hw => data.bottom_sphereBound u x hx w hw
    topValueLower_bound := fun u x hx => data.top_valueLower u x hx
    bottomValueLower_bound := fun u x hx => data.bottom_valueLower u x hx
    topQuotientBound := fun u _ _ =>
      le_mul_of_one_le_right (le_of_lt data.boundConstant_pos)
        (one_le_one_add_norm_pow
          ((zetaCompletedExplicitFormulaAutocorrelationCofinalHeightSchedule f).height u) K)
    bottomQuotientBound := fun u _ _ =>
      le_mul_of_one_le_right (le_of_lt data.boundConstant_pos)
        (one_le_one_add_norm_pow
          ((zetaCompletedExplicitFormulaAutocorrelationCofinalHeightSchedule f).height u) K) }

theorem CanonicalScheduledInverseGammaVariableCauchyPathData.topQuotientBound_of_common_constant
    {f : ZetaAdmissibleFunction} {K : ℕ}
    (data : CanonicalScheduledInverseGammaVariableCauchyPathData f K)
    (Q : ℝ) (hQ : data.boundConstant ≤ Q) (u x : ℝ)
    (hx : x ∈ Set.uIcc
      (zetaCompletedExplicitFormula_autocorrelation_contourFamily f).c
      (1 - (zetaCompletedExplicitFormula_autocorrelation_contourFamily f).c)) :
    ((data.topAmplitude u x / data.topRadius u x) /
      data.topValueLower u x) ≤
      Q * (1 + ‖(zetaCompletedExplicitFormulaAutocorrelationCofinalHeightSchedule f).height u‖) ^ K := by
  exact (data.topQuotientBound u x hx).trans
    (mul_le_mul_of_nonneg_right hQ
      (pow_nonneg
        (add_nonneg (by exact zero_le_one) (norm_nonneg _)) K))

theorem CanonicalScheduledInverseGammaVariableCauchyPathData.bottomQuotientBound_of_common_constant
    {f : ZetaAdmissibleFunction} {K : ℕ}
    (data : CanonicalScheduledInverseGammaVariableCauchyPathData f K)
    (Q : ℝ) (hQ : data.boundConstant ≤ Q) (u x : ℝ)
    (hx : x ∈ Set.uIcc
      (zetaCompletedExplicitFormula_autocorrelation_contourFamily f).c
      (1 - (zetaCompletedExplicitFormula_autocorrelation_contourFamily f).c)) :
    ((data.bottomAmplitude u x / data.bottomRadius u x) /
      data.bottomValueLower u x) ≤
      Q * (1 + ‖(zetaCompletedExplicitFormulaAutocorrelationCofinalHeightSchedule f).height u‖) ^ K := by
  exact (data.bottomQuotientBound u x hx).trans
    (mul_le_mul_of_nonneg_right hQ
      (pow_nonneg
        (add_nonneg (by exact zero_le_one) (norm_nonneg _)) K))

theorem canonicalScheduledVariableCauchyPathData_common_boundConstant_pos
    {f : ZetaAdmissibleFunction} {K : ℕ}
    (zetaData : CanonicalScheduledZetaSideVariableCauchyPathData f K)
    (gammaData : CanonicalScheduledInverseGammaVariableCauchyPathData f K) :
    0 < max zetaData.boundConstant gammaData.boundConstant := by
  exact lt_of_lt_of_le zetaData.boundConstant_pos (le_max_left _ _)

theorem canonicalScheduledVariableCauchyPathData_common_top_quotient_bound
    {f : ZetaAdmissibleFunction} {K : ℕ}
    (zetaData : CanonicalScheduledZetaSideVariableCauchyPathData f K)
    (gammaData : CanonicalScheduledInverseGammaVariableCauchyPathData f K)
    (u x : ℝ)
    (hx : x ∈ Set.uIcc
      (zetaCompletedExplicitFormula_autocorrelation_contourFamily f).c
      (1 - (zetaCompletedExplicitFormula_autocorrelation_contourFamily f).c)) :
    ((zetaData.topAmplitude u x / zetaData.topRadius u x) /
      zetaData.topValueLower u x) ≤
      max zetaData.boundConstant gammaData.boundConstant *
        (1 + ‖(zetaCompletedExplicitFormulaAutocorrelationCofinalHeightSchedule f).height u‖) ^ K := by
  exact zetaData.topQuotientBound_of_common_constant
    (max zetaData.boundConstant gammaData.boundConstant)
    (le_max_left _ _) u x hx

theorem canonicalScheduledVariableCauchyPathData_common_bottom_quotient_bound
    {f : ZetaAdmissibleFunction} {K : ℕ}
    (zetaData : CanonicalScheduledZetaSideVariableCauchyPathData f K)
    (gammaData : CanonicalScheduledInverseGammaVariableCauchyPathData f K)
    (u x : ℝ)
    (hx : x ∈ Set.uIcc
      (zetaCompletedExplicitFormula_autocorrelation_contourFamily f).c
      (1 - (zetaCompletedExplicitFormula_autocorrelation_contourFamily f).c)) :
    ((zetaData.bottomAmplitude u x / zetaData.bottomRadius u x) /
      zetaData.bottomValueLower u x) ≤
      max zetaData.boundConstant gammaData.boundConstant *
        (1 + ‖(zetaCompletedExplicitFormulaAutocorrelationCofinalHeightSchedule f).height u‖) ^ K := by
  exact zetaData.bottomQuotientBound_of_common_constant
    (max zetaData.boundConstant gammaData.boundConstant)
    (le_max_left _ _) u x hx

theorem canonicalScheduledVariableCauchyPathData_common_top_inverseGamma_quotient_bound
    {f : ZetaAdmissibleFunction} {K : ℕ}
    (zetaData : CanonicalScheduledZetaSideVariableCauchyPathData f K)
    (gammaData : CanonicalScheduledInverseGammaVariableCauchyPathData f K)
    (u x : ℝ)
    (hx : x ∈ Set.uIcc
      (zetaCompletedExplicitFormula_autocorrelation_contourFamily f).c
      (1 - (zetaCompletedExplicitFormula_autocorrelation_contourFamily f).c)) :
    ((gammaData.topAmplitude u x / gammaData.topRadius u x) /
      gammaData.topValueLower u x) ≤
      max zetaData.boundConstant gammaData.boundConstant *
        (1 + ‖(zetaCompletedExplicitFormulaAutocorrelationCofinalHeightSchedule f).height u‖) ^ K := by
  exact gammaData.topQuotientBound_of_common_constant
    (max zetaData.boundConstant gammaData.boundConstant)
    (le_max_right _ _) u x hx

theorem canonicalScheduledVariableCauchyPathData_common_bottom_inverseGamma_quotient_bound
    {f : ZetaAdmissibleFunction} {K : ℕ}
    (zetaData : CanonicalScheduledZetaSideVariableCauchyPathData f K)
    (gammaData : CanonicalScheduledInverseGammaVariableCauchyPathData f K)
    (u x : ℝ)
    (hx : x ∈ Set.uIcc
      (zetaCompletedExplicitFormula_autocorrelation_contourFamily f).c
      (1 - (zetaCompletedExplicitFormula_autocorrelation_contourFamily f).c)) :
    ((gammaData.bottomAmplitude u x / gammaData.bottomRadius u x) /
      gammaData.bottomValueLower u x) ≤
      max zetaData.boundConstant gammaData.boundConstant *
        (1 + ‖(zetaCompletedExplicitFormulaAutocorrelationCofinalHeightSchedule f).height u‖) ^ K := by
  exact gammaData.bottomQuotientBound_of_common_constant
    (max zetaData.boundConstant gammaData.boundConstant)
    (le_max_right _ _) u x hx

def CanonicalScheduledInverseGammaVariableCauchyPathData.of_uniform
    {f : ZetaAdmissibleFunction} {K : ℕ}
    (data : CanonicalScheduledInverseGammaCauchyPathData f K) :
    CanonicalScheduledInverseGammaVariableCauchyPathData f K :=
  { boundConstant := data.boundConstant
    boundConstant_pos := data.boundConstant_pos
    topRadius := fun _ _ => data.radius
    topAmplitude := fun _ _ => data.amplitude
    topValueLower := fun _ _ => data.valueLower
    bottomRadius := fun _ _ => data.radius
    bottomAmplitude := fun _ _ => data.amplitude
    bottomValueLower := fun _ _ => data.valueLower
    topRadius_pos := fun _ _ => data.radius_pos
    topValueLower_pos := fun _ _ => data.valueLower_pos
    bottomRadius_pos := fun _ _ => data.radius_pos
    bottomValueLower_pos := fun _ _ => data.valueLower_pos
    topDiffCont := fun u x hx => data.top_diffCont u x hx
    bottomDiffCont := fun u x hx => data.bottom_diffCont u x hx
    topSphereBound := fun u x hx w hw => data.top_sphereBound u x hx w hw
    bottomSphereBound := fun u x hx w hw => data.bottom_sphereBound u x hx w hw
    topValueLower_bound := fun u x hx => data.top_valueLower u x hx
    bottomValueLower_bound := fun u x hx => data.bottom_valueLower u x hx
    topQuotientBound := fun u _ _ =>
      le_mul_of_one_le_right (le_of_lt data.boundConstant_pos)
        (one_le_one_add_norm_pow
          ((zetaCompletedExplicitFormulaAutocorrelationCofinalHeightSchedule f).height u) K)
    bottomQuotientBound := fun u _ _ =>
      le_mul_of_one_le_right (le_of_lt data.boundConstant_pos)
        (one_le_one_add_norm_pow
          ((zetaCompletedExplicitFormulaAutocorrelationCofinalHeightSchedule f).height u) K) }

def canonicalScheduledZetaSideVariableCauchyPathData_of_uniform_family
    (K : ZetaAdmissibleFunction → ℕ)
    (data : ∀ f : ZetaAdmissibleFunction,
      CanonicalScheduledZetaSideCauchyPathData f (K f)) :
    ∀ f : ZetaAdmissibleFunction,
      CanonicalScheduledZetaSideVariableCauchyPathData f (K f) :=
  fun f => CanonicalScheduledZetaSideVariableCauchyPathData.of_uniform (data f)

def canonicalScheduledInverseGammaVariableCauchyPathData_of_uniform_family
    (K : ZetaAdmissibleFunction → ℕ)
    (data : ∀ f : ZetaAdmissibleFunction,
      CanonicalScheduledInverseGammaCauchyPathData f (K f)) :
    ∀ f : ZetaAdmissibleFunction,
      CanonicalScheduledInverseGammaVariableCauchyPathData f (K f) :=
  fun f => CanonicalScheduledInverseGammaVariableCauchyPathData.of_uniform (data f)

theorem canonicalScheduledHeightPolynomial_nonneg
    (f : ZetaAdmissibleFunction) (K : ℕ) (u : ℝ) :
    0 ≤
      (1 +
        ‖(zetaCompletedExplicitFormulaAutocorrelationCofinalHeightSchedule f).height u‖) ^ K :=
  pow_nonneg
    (add_nonneg zero_le_one
      (norm_nonneg
        ((zetaCompletedExplicitFormulaAutocorrelationCofinalHeightSchedule f).height u)))
    K

theorem CanonicalScheduledZetaSideVariableCauchyPathData.top_bound
    {f : ZetaAdmissibleFunction} {K : ℕ}
    (data : CanonicalScheduledZetaSideVariableCauchyPathData f K) :
    ∀ u x : ℝ,
      x ∈ Set.uIcc
        (zetaCompletedExplicitFormula_autocorrelation_contourFamily f).c
        (1 - (zetaCompletedExplicitFormula_autocorrelation_contourFamily f).c) →
      ‖zetaSideNegLogDeriv
        (zetaCompletedExplicitFormulaTopPath
          ((zetaCompletedExplicitFormula_autocorrelation_contourFamily f).rectangle
            ((zetaCompletedExplicitFormulaAutocorrelationCofinalHeightSchedule f).height u))
          x)‖ ≤
        data.boundConstant *
          (1 +
            ‖(zetaCompletedExplicitFormulaAutocorrelationCofinalHeightSchedule f).height u‖) ^ K :=
  fun u x hx =>
    let z : ℂ :=
      zetaCompletedExplicitFormulaTopPath
        ((zetaCompletedExplicitFormula_autocorrelation_contourFamily f).rectangle
          ((zetaCompletedExplicitFormulaAutocorrelationCofinalHeightSchedule f).height u))
        x
    let height : ℝ :=
      (zetaCompletedExplicitFormulaAutocorrelationCofinalHeightSchedule f).height u
    let rawBound :
        ‖zetaSideNegLogDeriv z‖ ≤
          (((data.topAmplitude u x / data.topRadius u x) /
              data.topValueLower u x) *
            (1 + ‖height‖) ^ K) :=
      zetaSideNegLogDeriv_path_bound_of_cauchyLogDerivative
        z
        K
        height
        (data.topRadius u x)
        (data.topAmplitude u x)
        (data.topValueLower u x)
        (data.topRadius_pos u x)
        (data.topValueLower_pos u x)
        (data.topDiffCont u x hx)
        (data.topSphereBound u x hx)
        (data.topValueLower_bound u x hx)
    let quotientBound :
        (((data.topAmplitude u x / data.topRadius u x) /
              data.topValueLower u x) *
            (1 + ‖height‖) ^ K) ≤
          data.boundConstant * (1 + ‖height‖) ^ K :=
      data.topQuotientBound u x hx
    rawBound.trans quotientBound

theorem CanonicalScheduledZetaSideVariableCauchyPathData.bottom_bound
    {f : ZetaAdmissibleFunction} {K : ℕ}
    (data : CanonicalScheduledZetaSideVariableCauchyPathData f K) :
    ∀ u x : ℝ,
      x ∈ Set.uIcc
        (zetaCompletedExplicitFormula_autocorrelation_contourFamily f).c
        (1 - (zetaCompletedExplicitFormula_autocorrelation_contourFamily f).c) →
      ‖zetaSideNegLogDeriv
        (zetaCompletedExplicitFormulaBottomPath
          ((zetaCompletedExplicitFormula_autocorrelation_contourFamily f).rectangle
            ((zetaCompletedExplicitFormulaAutocorrelationCofinalHeightSchedule f).height u))
          x)‖ ≤
        data.boundConstant *
          (1 +
            ‖(zetaCompletedExplicitFormulaAutocorrelationCofinalHeightSchedule f).height u‖) ^ K :=
  fun u x hx =>
    let z : ℂ :=
      zetaCompletedExplicitFormulaBottomPath
        ((zetaCompletedExplicitFormula_autocorrelation_contourFamily f).rectangle
          ((zetaCompletedExplicitFormulaAutocorrelationCofinalHeightSchedule f).height u))
        x
    let height : ℝ :=
      (zetaCompletedExplicitFormulaAutocorrelationCofinalHeightSchedule f).height u
    let rawBound :
        ‖zetaSideNegLogDeriv z‖ ≤
          (((data.bottomAmplitude u x / data.bottomRadius u x) /
              data.bottomValueLower u x) *
            (1 + ‖height‖) ^ K) :=
      zetaSideNegLogDeriv_path_bound_of_cauchyLogDerivative
        z
        K
        height
        (data.bottomRadius u x)
        (data.bottomAmplitude u x)
        (data.bottomValueLower u x)
        (data.bottomRadius_pos u x)
        (data.bottomValueLower_pos u x)
        (data.bottomDiffCont u x hx)
        (data.bottomSphereBound u x hx)
        (data.bottomValueLower_bound u x hx)
    let quotientBound :
        (((data.bottomAmplitude u x / data.bottomRadius u x) /
              data.bottomValueLower u x) *
            (1 + ‖height‖) ^ K) ≤
          data.boundConstant * (1 + ‖height‖) ^ K :=
      data.bottomQuotientBound u x hx
    rawBound.trans quotientBound

theorem CanonicalScheduledInverseGammaVariableCauchyPathData.top_bound
    {f : ZetaAdmissibleFunction} {K : ℕ}
    (data : CanonicalScheduledInverseGammaVariableCauchyPathData f K) :
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
        data.boundConstant *
          (1 +
            ‖(zetaCompletedExplicitFormulaAutocorrelationCofinalHeightSchedule f).height u‖) ^ K :=
  fun u x hx =>
    let z : ℂ :=
      zetaCompletedExplicitFormulaTopPath
        ((zetaCompletedExplicitFormula_autocorrelation_contourFamily f).rectangle
          ((zetaCompletedExplicitFormulaAutocorrelationCofinalHeightSchedule f).height u))
        x
    let height : ℝ :=
      (zetaCompletedExplicitFormulaAutocorrelationCofinalHeightSchedule f).height u
    let rawBound :
        ‖deriv (fun w : ℂ => (Complex.Gammaℝ w)⁻¹) z /
            (Complex.Gammaℝ z)⁻¹‖ ≤
          (((data.topAmplitude u x / data.topRadius u x) /
              data.topValueLower u x) *
            (1 + ‖height‖) ^ K) :=
      inverseGammaLogDeriv_path_bound_of_cauchyLogDerivative
        z
        K
        height
        (data.topRadius u x)
        (data.topAmplitude u x)
        (data.topValueLower u x)
        (data.topRadius_pos u x)
        (data.topValueLower_pos u x)
        (data.topDiffCont u x hx)
        (data.topSphereBound u x hx)
        (data.topValueLower_bound u x hx)
    let quotientBound :
        (((data.topAmplitude u x / data.topRadius u x) /
              data.topValueLower u x) *
            (1 + ‖height‖) ^ K) ≤
          data.boundConstant * (1 + ‖height‖) ^ K :=
      data.topQuotientBound u x hx
    rawBound.trans quotientBound

theorem CanonicalScheduledInverseGammaVariableCauchyPathData.bottom_bound
    {f : ZetaAdmissibleFunction} {K : ℕ}
    (data : CanonicalScheduledInverseGammaVariableCauchyPathData f K) :
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
        data.boundConstant *
          (1 +
            ‖(zetaCompletedExplicitFormulaAutocorrelationCofinalHeightSchedule f).height u‖) ^ K :=
  fun u x hx =>
    let z : ℂ :=
      zetaCompletedExplicitFormulaBottomPath
        ((zetaCompletedExplicitFormula_autocorrelation_contourFamily f).rectangle
          ((zetaCompletedExplicitFormulaAutocorrelationCofinalHeightSchedule f).height u))
        x
    let height : ℝ :=
      (zetaCompletedExplicitFormulaAutocorrelationCofinalHeightSchedule f).height u
    let rawBound :
        ‖deriv (fun w : ℂ => (Complex.Gammaℝ w)⁻¹) z /
            (Complex.Gammaℝ z)⁻¹‖ ≤
          (((data.bottomAmplitude u x / data.bottomRadius u x) /
              data.bottomValueLower u x) *
            (1 + ‖height‖) ^ K) :=
      inverseGammaLogDeriv_path_bound_of_cauchyLogDerivative
        z
        K
        height
        (data.bottomRadius u x)
        (data.bottomAmplitude u x)
        (data.bottomValueLower u x)
        (data.bottomRadius_pos u x)
        (data.bottomValueLower_pos u x)
        (data.bottomDiffCont u x hx)
        (data.bottomSphereBound u x hx)
        (data.bottomValueLower_bound u x hx)
    let quotientBound :
        (((data.bottomAmplitude u x / data.bottomRadius u x) /
              data.bottomValueLower u x) *
            (1 + ‖height‖) ^ K) ≤
          data.boundConstant * (1 + ‖height‖) ^ K :=
      data.bottomQuotientBound u x hx
    rawBound.trans quotientBound

def zetaCompletedExplicitFormulaAutocorrelationScheduledPolynomialFamilyAnalyticPackage_of_variableCauchyPathData
    (f : ZetaAdmissibleFunction) (K : ℕ)
    (zetaData : CanonicalScheduledZetaSideVariableCauchyPathData f K)
    (gammaData : CanonicalScheduledInverseGammaVariableCauchyPathData f K) :
    ExplicitFormulaScheduledPolynomialFamilyAnalyticPackage
      (convolutionAutocorrelation f)
      (zetaCompletedExplicitFormula_autocorrelation_contourFamily f) :=
  zetaCompletedExplicitFormulaAutocorrelationScheduledPolynomialFamilyAnalyticPackage_of_factorPathBounds
    f K
    zetaData.boundConstant
    gammaData.boundConstant
    zetaData.boundConstant_pos
    gammaData.boundConstant_pos
    zetaData.top_bound
    zetaData.bottom_bound
    gammaData.top_bound
    gammaData.bottom_bound

end ZetaAdmissibleFunction

end
end LFunctions
end Boundary
