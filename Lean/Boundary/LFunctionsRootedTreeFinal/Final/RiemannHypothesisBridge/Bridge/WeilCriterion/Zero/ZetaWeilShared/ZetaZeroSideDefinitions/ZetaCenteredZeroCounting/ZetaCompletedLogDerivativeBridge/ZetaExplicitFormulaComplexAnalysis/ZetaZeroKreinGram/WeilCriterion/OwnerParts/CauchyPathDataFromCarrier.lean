import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaZeroKreinGram.WeilCriterion.OwnerParts.CanonicalScheduledPolynomialPackageParts.FactorPathBounds

/-!
# Cauchy path data from scheduled carrier data

This file owns the restriction of carrier-level Cauchy data to the canonical
top and bottom scheduled horizontal paths.
-/

namespace Boundary
namespace LFunctions

noncomputable section

namespace ZetaAdmissibleFunction

/-- Carrier zeta-side regularity restricts to the top canonical path. -/
theorem zetaSideCarrierCauchy_top_diffCont
    (f : ZetaAdmissibleFunction) (radius : ℝ)
    (diffCont :
      ∀ z : ℂ,
        z ∈ (zetaCompletedExplicitFormulaAutocorrelationScheduledHorizontalCarrier f).carrier →
        DiffContOnCl ℂ zetaSideFactor (Metric.ball z radius))
    (u x : ℝ)
    (hx :
      x ∈ Set.uIcc
        (zetaCompletedExplicitFormula_autocorrelation_contourFamily f).c
        (1 - (zetaCompletedExplicitFormula_autocorrelation_contourFamily f).c)) :
    DiffContOnCl ℂ zetaSideFactor
      (Metric.ball
        (zetaCompletedExplicitFormulaTopPath
          ((zetaCompletedExplicitFormula_autocorrelation_contourFamily f).rectangle
            ((zetaCompletedExplicitFormulaAutocorrelationCofinalHeightSchedule f).height u))
          x)
        radius) :=
  diffCont
    (zetaCompletedExplicitFormulaTopPath
      ((zetaCompletedExplicitFormula_autocorrelation_contourFamily f).rectangle
        ((zetaCompletedExplicitFormulaAutocorrelationCofinalHeightSchedule f).height u))
      x)
    (zetaCompletedExplicitFormulaAutocorrelationScheduledHorizontalCarrier_top_mem
      f u x hx)

/-- Carrier zeta-side regularity restricts to the bottom canonical path. -/
theorem zetaSideCarrierCauchy_bottom_diffCont
    (f : ZetaAdmissibleFunction) (radius : ℝ)
    (diffCont :
      ∀ z : ℂ,
        z ∈ (zetaCompletedExplicitFormulaAutocorrelationScheduledHorizontalCarrier f).carrier →
        DiffContOnCl ℂ zetaSideFactor (Metric.ball z radius))
    (u x : ℝ)
    (hx :
      x ∈ Set.uIcc
        (zetaCompletedExplicitFormula_autocorrelation_contourFamily f).c
        (1 - (zetaCompletedExplicitFormula_autocorrelation_contourFamily f).c)) :
    DiffContOnCl ℂ zetaSideFactor
      (Metric.ball
        (zetaCompletedExplicitFormulaBottomPath
          ((zetaCompletedExplicitFormula_autocorrelation_contourFamily f).rectangle
            ((zetaCompletedExplicitFormulaAutocorrelationCofinalHeightSchedule f).height u))
          x)
        radius) :=
  diffCont
    (zetaCompletedExplicitFormulaBottomPath
      ((zetaCompletedExplicitFormula_autocorrelation_contourFamily f).rectangle
        ((zetaCompletedExplicitFormulaAutocorrelationCofinalHeightSchedule f).height u))
      x)
    (zetaCompletedExplicitFormulaAutocorrelationScheduledHorizontalCarrier_bottom_mem
      f u x hx)

/-- Carrier zeta-side sphere bounds restrict to the top canonical path. -/
theorem zetaSideCarrierCauchy_top_sphereBound
    (f : ZetaAdmissibleFunction) (K : ℕ)
    (radius amplitude : ℝ)
    (sphereBound :
      ∀ z : ℂ,
        z ∈ (zetaCompletedExplicitFormulaAutocorrelationScheduledHorizontalCarrier f).carrier →
        ∀ w : ℂ,
          w ∈ Metric.sphere z radius →
          ‖zetaSideFactor w‖ ≤ amplitude * (1 + ‖z.im‖) ^ K)
    (u x : ℝ)
    (hx :
      x ∈ Set.uIcc
        (zetaCompletedExplicitFormula_autocorrelation_contourFamily f).c
        (1 - (zetaCompletedExplicitFormula_autocorrelation_contourFamily f).c))
    (w : ℂ)
    (hw :
      w ∈
        Metric.sphere
          (zetaCompletedExplicitFormulaTopPath
            ((zetaCompletedExplicitFormula_autocorrelation_contourFamily f).rectangle
              ((zetaCompletedExplicitFormulaAutocorrelationCofinalHeightSchedule f).height u))
            x)
          radius) :
    ‖zetaSideFactor w‖ ≤
      amplitude *
        (1 +
          ‖(zetaCompletedExplicitFormulaAutocorrelationCofinalHeightSchedule f).height u‖) ^ K :=
  let z : ℂ :=
    zetaCompletedExplicitFormulaTopPath
      ((zetaCompletedExplicitFormula_autocorrelation_contourFamily f).rectangle
        ((zetaCompletedExplicitFormulaAutocorrelationCofinalHeightSchedule f).height u))
      x
  let hz :
      z ∈ (zetaCompletedExplicitFormulaAutocorrelationScheduledHorizontalCarrier f).carrier :=
    zetaCompletedExplicitFormulaAutocorrelationScheduledHorizontalCarrier_top_mem
      f u x hx
  let hraw :
      ‖zetaSideFactor w‖ ≤ amplitude * (1 + ‖z.im‖) ^ K :=
    sphereBound z hz w hw
  let him :
      ‖z.im‖ =
        ‖(zetaCompletedExplicitFormulaAutocorrelationCofinalHeightSchedule f).height u‖ :=
    zetaCompletedExplicitFormulaTopPath_im_norm
      ((zetaCompletedExplicitFormula_autocorrelation_contourFamily f).rectangle
        ((zetaCompletedExplicitFormulaAutocorrelationCofinalHeightSchedule f).height u))
      x
  let hshape :
      amplitude * (1 + ‖z.im‖) ^ K =
        amplitude *
          (1 +
            ‖(zetaCompletedExplicitFormulaAutocorrelationCofinalHeightSchedule f).height u‖) ^
            K :=
    congrArg (fun value : ℝ => amplitude * (1 + value) ^ K) him
  hraw.trans_eq hshape

/-- Carrier zeta-side sphere bounds restrict to the bottom canonical path. -/
theorem zetaSideCarrierCauchy_bottom_sphereBound
    (f : ZetaAdmissibleFunction) (K : ℕ)
    (radius amplitude : ℝ)
    (sphereBound :
      ∀ z : ℂ,
        z ∈ (zetaCompletedExplicitFormulaAutocorrelationScheduledHorizontalCarrier f).carrier →
        ∀ w : ℂ,
          w ∈ Metric.sphere z radius →
          ‖zetaSideFactor w‖ ≤ amplitude * (1 + ‖z.im‖) ^ K)
    (u x : ℝ)
    (hx :
      x ∈ Set.uIcc
        (zetaCompletedExplicitFormula_autocorrelation_contourFamily f).c
        (1 - (zetaCompletedExplicitFormula_autocorrelation_contourFamily f).c))
    (w : ℂ)
    (hw :
      w ∈
        Metric.sphere
          (zetaCompletedExplicitFormulaBottomPath
            ((zetaCompletedExplicitFormula_autocorrelation_contourFamily f).rectangle
              ((zetaCompletedExplicitFormulaAutocorrelationCofinalHeightSchedule f).height u))
            x)
          radius) :
    ‖zetaSideFactor w‖ ≤
      amplitude *
        (1 +
          ‖(zetaCompletedExplicitFormulaAutocorrelationCofinalHeightSchedule f).height u‖) ^ K :=
  let z : ℂ :=
    zetaCompletedExplicitFormulaBottomPath
      ((zetaCompletedExplicitFormula_autocorrelation_contourFamily f).rectangle
        ((zetaCompletedExplicitFormulaAutocorrelationCofinalHeightSchedule f).height u))
      x
  let hz :
      z ∈ (zetaCompletedExplicitFormulaAutocorrelationScheduledHorizontalCarrier f).carrier :=
    zetaCompletedExplicitFormulaAutocorrelationScheduledHorizontalCarrier_bottom_mem
      f u x hx
  let hraw :
      ‖zetaSideFactor w‖ ≤ amplitude * (1 + ‖z.im‖) ^ K :=
    sphereBound z hz w hw
  let him :
      ‖z.im‖ =
        ‖(zetaCompletedExplicitFormulaAutocorrelationCofinalHeightSchedule f).height u‖ :=
    zetaCompletedExplicitFormulaBottomPath_im_norm
      ((zetaCompletedExplicitFormula_autocorrelation_contourFamily f).rectangle
        ((zetaCompletedExplicitFormulaAutocorrelationCofinalHeightSchedule f).height u))
      x
  let hshape :
      amplitude * (1 + ‖z.im‖) ^ K =
        amplitude *
          (1 +
            ‖(zetaCompletedExplicitFormulaAutocorrelationCofinalHeightSchedule f).height u‖) ^
            K :=
    congrArg (fun value : ℝ => amplitude * (1 + value) ^ K) him
  hraw.trans_eq hshape

/-- Carrier zeta-side value lower bounds restrict to the top canonical path. -/
theorem zetaSideCarrierCauchy_top_valueLower
    (f : ZetaAdmissibleFunction) (valueLower : ℝ)
    (valueLower_bound :
      ∀ z : ℂ,
        z ∈ (zetaCompletedExplicitFormulaAutocorrelationScheduledHorizontalCarrier f).carrier →
        valueLower ≤ ‖zetaSideFactor z‖)
    (u x : ℝ)
    (hx :
      x ∈ Set.uIcc
        (zetaCompletedExplicitFormula_autocorrelation_contourFamily f).c
        (1 - (zetaCompletedExplicitFormula_autocorrelation_contourFamily f).c)) :
    valueLower ≤
      ‖zetaSideFactor
        (zetaCompletedExplicitFormulaTopPath
          ((zetaCompletedExplicitFormula_autocorrelation_contourFamily f).rectangle
            ((zetaCompletedExplicitFormulaAutocorrelationCofinalHeightSchedule f).height u))
          x)‖ :=
  valueLower_bound
    (zetaCompletedExplicitFormulaTopPath
      ((zetaCompletedExplicitFormula_autocorrelation_contourFamily f).rectangle
        ((zetaCompletedExplicitFormulaAutocorrelationCofinalHeightSchedule f).height u))
      x)
    (zetaCompletedExplicitFormulaAutocorrelationScheduledHorizontalCarrier_top_mem
      f u x hx)

/-- Carrier zeta-side value lower bounds restrict to the bottom canonical path. -/
theorem zetaSideCarrierCauchy_bottom_valueLower
    (f : ZetaAdmissibleFunction) (valueLower : ℝ)
    (valueLower_bound :
      ∀ z : ℂ,
        z ∈ (zetaCompletedExplicitFormulaAutocorrelationScheduledHorizontalCarrier f).carrier →
        valueLower ≤ ‖zetaSideFactor z‖)
    (u x : ℝ)
    (hx :
      x ∈ Set.uIcc
        (zetaCompletedExplicitFormula_autocorrelation_contourFamily f).c
        (1 - (zetaCompletedExplicitFormula_autocorrelation_contourFamily f).c)) :
    valueLower ≤
      ‖zetaSideFactor
        (zetaCompletedExplicitFormulaBottomPath
          ((zetaCompletedExplicitFormula_autocorrelation_contourFamily f).rectangle
            ((zetaCompletedExplicitFormulaAutocorrelationCofinalHeightSchedule f).height u))
          x)‖ :=
  valueLower_bound
    (zetaCompletedExplicitFormulaBottomPath
      ((zetaCompletedExplicitFormula_autocorrelation_contourFamily f).rectangle
        ((zetaCompletedExplicitFormulaAutocorrelationCofinalHeightSchedule f).height u))
      x)
    (zetaCompletedExplicitFormulaAutocorrelationScheduledHorizontalCarrier_bottom_mem
      f u x hx)

/-- Carrier-level zeta-side Cauchy data restricts to canonical scheduled path
data. -/
def CanonicalScheduledZetaSideCauchyPathData.ofCarrierCauchyData
    (f : ZetaAdmissibleFunction) (K : ℕ)
    (radius amplitude valueLower : ℝ)
    (radius_pos : 0 < radius)
    (amplitude_pos : 0 < amplitude)
    (valueLower_pos : 0 < valueLower)
    (diffCont :
      ∀ z : ℂ,
        z ∈ (zetaCompletedExplicitFormulaAutocorrelationScheduledHorizontalCarrier f).carrier →
        DiffContOnCl ℂ zetaSideFactor (Metric.ball z radius))
    (sphereBound :
      ∀ z : ℂ,
        z ∈ (zetaCompletedExplicitFormulaAutocorrelationScheduledHorizontalCarrier f).carrier →
        ∀ w : ℂ,
          w ∈ Metric.sphere z radius →
          ‖zetaSideFactor w‖ ≤ amplitude * (1 + ‖z.im‖) ^ K)
    (valueLower_bound :
      ∀ z : ℂ,
        z ∈ (zetaCompletedExplicitFormulaAutocorrelationScheduledHorizontalCarrier f).carrier →
        valueLower ≤ ‖zetaSideFactor z‖) :
    CanonicalScheduledZetaSideCauchyPathData f K :=
  { radius := radius
    amplitude := amplitude
    valueLower := valueLower
    radius_pos := radius_pos
    amplitude_pos := amplitude_pos
    valueLower_pos := valueLower_pos
    top_diffCont :=
      zetaSideCarrierCauchy_top_diffCont f radius diffCont
    bottom_diffCont :=
      zetaSideCarrierCauchy_bottom_diffCont f radius diffCont
    top_sphereBound :=
      zetaSideCarrierCauchy_top_sphereBound f K radius amplitude sphereBound
    bottom_sphereBound :=
      zetaSideCarrierCauchy_bottom_sphereBound f K radius amplitude sphereBound
    top_valueLower :=
      zetaSideCarrierCauchy_top_valueLower f valueLower valueLower_bound
    bottom_valueLower :=
      zetaSideCarrierCauchy_bottom_valueLower f valueLower valueLower_bound }

def CanonicalScheduledZetaSideCauchyPathData.ofCarrierPointwiseSphereBound
    (f : ZetaAdmissibleFunction) (K : ℕ)
    (radius amplitude valueLower : ℝ)
    (radius_pos : 0 < radius) (radius_le_two : radius ≤ 2)
    (amplitude_pos : 0 < amplitude)
    (valueLower_pos : 0 < valueLower)
    (diffCont :
      ∀ z : ℂ,
        z ∈ (zetaCompletedExplicitFormulaAutocorrelationScheduledHorizontalCarrier f).carrier →
        DiffContOnCl ℂ zetaSideFactor (Metric.ball z radius))
    (sphereBound :
      ∀ z : ℂ,
        z ∈ (zetaCompletedExplicitFormulaAutocorrelationScheduledHorizontalCarrier f).carrier →
        ∀ w : ℂ,
          w ∈ Metric.sphere z radius →
          ‖zetaSideFactor w‖ ≤ amplitude * (1 + ‖w.im‖) ^ K)
    (valueLower_bound :
      ∀ z : ℂ,
        z ∈ (zetaCompletedExplicitFormulaAutocorrelationScheduledHorizontalCarrier f).carrier →
        valueLower ≤ ‖zetaSideFactor z‖) :
    CanonicalScheduledZetaSideCauchyPathData f K :=
  CanonicalScheduledZetaSideCauchyPathData.ofCarrierCauchyData
    f K radius (amplitude * 3 ^ K) valueLower radius_pos
    (mul_pos amplitude_pos (pow_pos zero_lt_three K)) valueLower_pos diffCont
    (fun z hz w hw =>
      sphere_bound_of_center_height_polynomial_bound
        (G := zetaSideFactor) z w radius amplitude K
        (le_of_lt amplitude_pos)
        (le_add_of_nonneg_right (norm_nonneg z.im))
        (le_of_lt radius_pos) radius_le_two
        (sphereBound z hz w hw))
    valueLower_bound

/-- Carrier inverse-Gamma regularity restricts to the top canonical path. -/
theorem inverseGammaCarrierCauchy_top_diffCont
    (f : ZetaAdmissibleFunction) (radius : ℝ)
    (diffCont :
      ∀ z : ℂ,
        z ∈ (zetaCompletedExplicitFormulaAutocorrelationScheduledHorizontalCarrier f).carrier →
        DiffContOnCl ℂ (fun w : ℂ => (Complex.Gammaℝ w)⁻¹)
          (Metric.ball z radius))
    (u x : ℝ)
    (hx :
      x ∈ Set.uIcc
        (zetaCompletedExplicitFormula_autocorrelation_contourFamily f).c
        (1 - (zetaCompletedExplicitFormula_autocorrelation_contourFamily f).c)) :
    DiffContOnCl ℂ (fun w : ℂ => (Complex.Gammaℝ w)⁻¹)
      (Metric.ball
        (zetaCompletedExplicitFormulaTopPath
          ((zetaCompletedExplicitFormula_autocorrelation_contourFamily f).rectangle
            ((zetaCompletedExplicitFormulaAutocorrelationCofinalHeightSchedule f).height u))
          x)
        radius) :=
  diffCont
    (zetaCompletedExplicitFormulaTopPath
      ((zetaCompletedExplicitFormula_autocorrelation_contourFamily f).rectangle
        ((zetaCompletedExplicitFormulaAutocorrelationCofinalHeightSchedule f).height u))
      x)
    (zetaCompletedExplicitFormulaAutocorrelationScheduledHorizontalCarrier_top_mem
      f u x hx)

/-- Carrier inverse-Gamma regularity restricts to the bottom canonical path. -/
theorem inverseGammaCarrierCauchy_bottom_diffCont
    (f : ZetaAdmissibleFunction) (radius : ℝ)
    (diffCont :
      ∀ z : ℂ,
        z ∈ (zetaCompletedExplicitFormulaAutocorrelationScheduledHorizontalCarrier f).carrier →
        DiffContOnCl ℂ (fun w : ℂ => (Complex.Gammaℝ w)⁻¹)
          (Metric.ball z radius))
    (u x : ℝ)
    (hx :
      x ∈ Set.uIcc
        (zetaCompletedExplicitFormula_autocorrelation_contourFamily f).c
        (1 - (zetaCompletedExplicitFormula_autocorrelation_contourFamily f).c)) :
    DiffContOnCl ℂ (fun w : ℂ => (Complex.Gammaℝ w)⁻¹)
      (Metric.ball
        (zetaCompletedExplicitFormulaBottomPath
          ((zetaCompletedExplicitFormula_autocorrelation_contourFamily f).rectangle
            ((zetaCompletedExplicitFormulaAutocorrelationCofinalHeightSchedule f).height u))
          x)
        radius) :=
  diffCont
    (zetaCompletedExplicitFormulaBottomPath
      ((zetaCompletedExplicitFormula_autocorrelation_contourFamily f).rectangle
        ((zetaCompletedExplicitFormulaAutocorrelationCofinalHeightSchedule f).height u))
      x)
    (zetaCompletedExplicitFormulaAutocorrelationScheduledHorizontalCarrier_bottom_mem
      f u x hx)

/-- Carrier inverse-Gamma sphere bounds restrict to the top canonical path. -/
theorem inverseGammaCarrierCauchy_top_sphereBound
    (f : ZetaAdmissibleFunction) (K : ℕ)
    (radius amplitude : ℝ)
    (sphereBound :
      ∀ z : ℂ,
        z ∈ (zetaCompletedExplicitFormulaAutocorrelationScheduledHorizontalCarrier f).carrier →
        ∀ w : ℂ,
          w ∈ Metric.sphere z radius →
          ‖(Complex.Gammaℝ w)⁻¹‖ ≤ amplitude * (1 + ‖z.im‖) ^ K)
    (u x : ℝ)
    (hx :
      x ∈ Set.uIcc
        (zetaCompletedExplicitFormula_autocorrelation_contourFamily f).c
        (1 - (zetaCompletedExplicitFormula_autocorrelation_contourFamily f).c))
    (w : ℂ)
    (hw :
      w ∈
        Metric.sphere
          (zetaCompletedExplicitFormulaTopPath
            ((zetaCompletedExplicitFormula_autocorrelation_contourFamily f).rectangle
              ((zetaCompletedExplicitFormulaAutocorrelationCofinalHeightSchedule f).height u))
            x)
          radius) :
    ‖(Complex.Gammaℝ w)⁻¹‖ ≤
      amplitude *
        (1 +
          ‖(zetaCompletedExplicitFormulaAutocorrelationCofinalHeightSchedule f).height u‖) ^ K :=
  let z : ℂ :=
    zetaCompletedExplicitFormulaTopPath
      ((zetaCompletedExplicitFormula_autocorrelation_contourFamily f).rectangle
        ((zetaCompletedExplicitFormulaAutocorrelationCofinalHeightSchedule f).height u))
      x
  let hz :
      z ∈ (zetaCompletedExplicitFormulaAutocorrelationScheduledHorizontalCarrier f).carrier :=
    zetaCompletedExplicitFormulaAutocorrelationScheduledHorizontalCarrier_top_mem
      f u x hx
  let hraw :
      ‖(Complex.Gammaℝ w)⁻¹‖ ≤ amplitude * (1 + ‖z.im‖) ^ K :=
    sphereBound z hz w hw
  let him :
      ‖z.im‖ =
        ‖(zetaCompletedExplicitFormulaAutocorrelationCofinalHeightSchedule f).height u‖ :=
    zetaCompletedExplicitFormulaTopPath_im_norm
      ((zetaCompletedExplicitFormula_autocorrelation_contourFamily f).rectangle
        ((zetaCompletedExplicitFormulaAutocorrelationCofinalHeightSchedule f).height u))
      x
  let hshape :
      amplitude * (1 + ‖z.im‖) ^ K =
        amplitude *
          (1 +
            ‖(zetaCompletedExplicitFormulaAutocorrelationCofinalHeightSchedule f).height u‖) ^
            K :=
    congrArg (fun value : ℝ => amplitude * (1 + value) ^ K) him
  hraw.trans_eq hshape

/-- Carrier inverse-Gamma sphere bounds restrict to the bottom canonical path. -/
theorem inverseGammaCarrierCauchy_bottom_sphereBound
    (f : ZetaAdmissibleFunction) (K : ℕ)
    (radius amplitude : ℝ)
    (sphereBound :
      ∀ z : ℂ,
        z ∈ (zetaCompletedExplicitFormulaAutocorrelationScheduledHorizontalCarrier f).carrier →
        ∀ w : ℂ,
          w ∈ Metric.sphere z radius →
          ‖(Complex.Gammaℝ w)⁻¹‖ ≤ amplitude * (1 + ‖z.im‖) ^ K)
    (u x : ℝ)
    (hx :
      x ∈ Set.uIcc
        (zetaCompletedExplicitFormula_autocorrelation_contourFamily f).c
        (1 - (zetaCompletedExplicitFormula_autocorrelation_contourFamily f).c))
    (w : ℂ)
    (hw :
      w ∈
        Metric.sphere
          (zetaCompletedExplicitFormulaBottomPath
            ((zetaCompletedExplicitFormula_autocorrelation_contourFamily f).rectangle
              ((zetaCompletedExplicitFormulaAutocorrelationCofinalHeightSchedule f).height u))
            x)
          radius) :
    ‖(Complex.Gammaℝ w)⁻¹‖ ≤
      amplitude *
        (1 +
          ‖(zetaCompletedExplicitFormulaAutocorrelationCofinalHeightSchedule f).height u‖) ^ K :=
  let z : ℂ :=
    zetaCompletedExplicitFormulaBottomPath
      ((zetaCompletedExplicitFormula_autocorrelation_contourFamily f).rectangle
        ((zetaCompletedExplicitFormulaAutocorrelationCofinalHeightSchedule f).height u))
      x
  let hz :
      z ∈ (zetaCompletedExplicitFormulaAutocorrelationScheduledHorizontalCarrier f).carrier :=
    zetaCompletedExplicitFormulaAutocorrelationScheduledHorizontalCarrier_bottom_mem
      f u x hx
  let hraw :
      ‖(Complex.Gammaℝ w)⁻¹‖ ≤ amplitude * (1 + ‖z.im‖) ^ K :=
    sphereBound z hz w hw
  let him :
      ‖z.im‖ =
        ‖(zetaCompletedExplicitFormulaAutocorrelationCofinalHeightSchedule f).height u‖ :=
    zetaCompletedExplicitFormulaBottomPath_im_norm
      ((zetaCompletedExplicitFormula_autocorrelation_contourFamily f).rectangle
        ((zetaCompletedExplicitFormulaAutocorrelationCofinalHeightSchedule f).height u))
      x
  let hshape :
      amplitude * (1 + ‖z.im‖) ^ K =
        amplitude *
          (1 +
            ‖(zetaCompletedExplicitFormulaAutocorrelationCofinalHeightSchedule f).height u‖) ^
            K :=
    congrArg (fun value : ℝ => amplitude * (1 + value) ^ K) him
  hraw.trans_eq hshape

/-- Carrier inverse-Gamma value lower bounds restrict to the top canonical path. -/
theorem inverseGammaCarrierCauchy_top_valueLower
    (f : ZetaAdmissibleFunction) (valueLower : ℝ)
    (valueLower_bound :
      ∀ z : ℂ,
        z ∈ (zetaCompletedExplicitFormulaAutocorrelationScheduledHorizontalCarrier f).carrier →
        valueLower ≤ ‖(Complex.Gammaℝ z)⁻¹‖)
    (u x : ℝ)
    (hx :
      x ∈ Set.uIcc
        (zetaCompletedExplicitFormula_autocorrelation_contourFamily f).c
        (1 - (zetaCompletedExplicitFormula_autocorrelation_contourFamily f).c)) :
    valueLower ≤
      ‖(Complex.Gammaℝ
        (zetaCompletedExplicitFormulaTopPath
          ((zetaCompletedExplicitFormula_autocorrelation_contourFamily f).rectangle
            ((zetaCompletedExplicitFormulaAutocorrelationCofinalHeightSchedule f).height u))
          x))⁻¹‖ :=
  valueLower_bound
    (zetaCompletedExplicitFormulaTopPath
      ((zetaCompletedExplicitFormula_autocorrelation_contourFamily f).rectangle
        ((zetaCompletedExplicitFormulaAutocorrelationCofinalHeightSchedule f).height u))
      x)
    (zetaCompletedExplicitFormulaAutocorrelationScheduledHorizontalCarrier_top_mem
      f u x hx)

/-- Carrier inverse-Gamma value lower bounds restrict to the bottom canonical path. -/
theorem inverseGammaCarrierCauchy_bottom_valueLower
    (f : ZetaAdmissibleFunction) (valueLower : ℝ)
    (valueLower_bound :
      ∀ z : ℂ,
        z ∈ (zetaCompletedExplicitFormulaAutocorrelationScheduledHorizontalCarrier f).carrier →
        valueLower ≤ ‖(Complex.Gammaℝ z)⁻¹‖)
    (u x : ℝ)
    (hx :
      x ∈ Set.uIcc
        (zetaCompletedExplicitFormula_autocorrelation_contourFamily f).c
        (1 - (zetaCompletedExplicitFormula_autocorrelation_contourFamily f).c)) :
    valueLower ≤
      ‖(Complex.Gammaℝ
        (zetaCompletedExplicitFormulaBottomPath
          ((zetaCompletedExplicitFormula_autocorrelation_contourFamily f).rectangle
            ((zetaCompletedExplicitFormulaAutocorrelationCofinalHeightSchedule f).height u))
          x))⁻¹‖ :=
  valueLower_bound
    (zetaCompletedExplicitFormulaBottomPath
      ((zetaCompletedExplicitFormula_autocorrelation_contourFamily f).rectangle
        ((zetaCompletedExplicitFormulaAutocorrelationCofinalHeightSchedule f).height u))
      x)
    (zetaCompletedExplicitFormulaAutocorrelationScheduledHorizontalCarrier_bottom_mem
      f u x hx)

/-- Carrier-level inverse-Gamma Cauchy data restricts to canonical scheduled
path data. -/
def CanonicalScheduledInverseGammaCauchyPathData.ofCarrierCauchyData
    (f : ZetaAdmissibleFunction) (K : ℕ)
    (radius amplitude valueLower : ℝ)
    (radius_pos : 0 < radius)
    (amplitude_pos : 0 < amplitude)
    (valueLower_pos : 0 < valueLower)
    (diffCont :
      ∀ z : ℂ,
        z ∈ (zetaCompletedExplicitFormulaAutocorrelationScheduledHorizontalCarrier f).carrier →
        DiffContOnCl ℂ (fun w : ℂ => (Complex.Gammaℝ w)⁻¹)
          (Metric.ball z radius))
    (sphereBound :
      ∀ z : ℂ,
        z ∈ (zetaCompletedExplicitFormulaAutocorrelationScheduledHorizontalCarrier f).carrier →
        ∀ w : ℂ,
          w ∈ Metric.sphere z radius →
          ‖(Complex.Gammaℝ w)⁻¹‖ ≤ amplitude * (1 + ‖z.im‖) ^ K)
    (valueLower_bound :
      ∀ z : ℂ,
        z ∈ (zetaCompletedExplicitFormulaAutocorrelationScheduledHorizontalCarrier f).carrier →
        valueLower ≤ ‖(Complex.Gammaℝ z)⁻¹‖) :
    CanonicalScheduledInverseGammaCauchyPathData f K :=
  { radius := radius
    amplitude := amplitude
    valueLower := valueLower
    radius_pos := radius_pos
    amplitude_pos := amplitude_pos
    valueLower_pos := valueLower_pos
    top_diffCont :=
      inverseGammaCarrierCauchy_top_diffCont f radius diffCont
    bottom_diffCont :=
      inverseGammaCarrierCauchy_bottom_diffCont f radius diffCont
    top_sphereBound :=
      inverseGammaCarrierCauchy_top_sphereBound f K radius amplitude sphereBound
    bottom_sphereBound :=
      inverseGammaCarrierCauchy_bottom_sphereBound f K radius amplitude sphereBound
    top_valueLower :=
      inverseGammaCarrierCauchy_top_valueLower f valueLower valueLower_bound
    bottom_valueLower :=
      inverseGammaCarrierCauchy_bottom_valueLower f valueLower valueLower_bound }

def CanonicalScheduledInverseGammaCauchyPathData.ofCarrierPointwiseSphereBound
    (f : ZetaAdmissibleFunction) (K : ℕ)
    (radius amplitude valueLower : ℝ)
    (radius_pos : 0 < radius) (radius_le_two : radius ≤ 2)
    (amplitude_pos : 0 < amplitude)
    (valueLower_pos : 0 < valueLower)
    (diffCont :
      ∀ z : ℂ,
        z ∈ (zetaCompletedExplicitFormulaAutocorrelationScheduledHorizontalCarrier f).carrier →
        DiffContOnCl ℂ (fun w : ℂ => (Complex.Gammaℝ w)⁻¹)
          (Metric.ball z radius))
    (sphereBound :
      ∀ z : ℂ,
        z ∈ (zetaCompletedExplicitFormulaAutocorrelationScheduledHorizontalCarrier f).carrier →
        ∀ w : ℂ,
          w ∈ Metric.sphere z radius →
          ‖(Complex.Gammaℝ w)⁻¹‖ ≤ amplitude * (1 + ‖w.im‖) ^ K)
    (valueLower_bound :
      ∀ z : ℂ,
        z ∈ (zetaCompletedExplicitFormulaAutocorrelationScheduledHorizontalCarrier f).carrier →
        valueLower ≤ ‖(Complex.Gammaℝ z)⁻¹‖) :
    CanonicalScheduledInverseGammaCauchyPathData f K :=
  CanonicalScheduledInverseGammaCauchyPathData.ofCarrierCauchyData
    f K radius (amplitude * 3 ^ K) valueLower radius_pos
    (mul_pos amplitude_pos (pow_pos zero_lt_three K)) valueLower_pos diffCont
    (fun z hz w hw =>
      sphere_bound_of_center_height_polynomial_bound
        (G := fun w : ℂ => (Complex.Gammaℝ w)⁻¹)
        z w radius amplitude K
        (le_of_lt amplitude_pos)
        (le_add_of_nonneg_right (norm_nonneg z.im))
        (le_of_lt radius_pos) radius_le_two
        (sphereBound z hz w hw))
    valueLower_bound

end ZetaAdmissibleFunction

end
end LFunctions
end Boundary
