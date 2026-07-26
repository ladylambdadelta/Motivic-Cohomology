import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaZeroKreinGram.WeilCriterion.OwnerParts.CanonicalScheduledPolynomialPackageParts.PathBounds
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaZeroKreinGram.WeilCriterion.OwnerParts.CanonicalScheduledPointwiseSeparation
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaCompletedLogDerivativeControl.CauchyLogDerivative

/-!
# Canonical scheduled polynomial package from factor path bounds

This file peels the scheduled horizontal path-bound sink into the two analytic
factors of the completed logarithmic derivative: the zeta-side factor and the
inverse-Gamma factor.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open scoped Topology

namespace ZetaAdmissibleFunction

structure CanonicalScheduledZetaSideCauchyPathData
    (f : ZetaAdmissibleFunction) (K : ℕ) where
  radius : ℝ
  amplitude : ℝ
  valueLower : ℝ
  radius_pos : 0 < radius
  amplitude_pos : 0 < amplitude
  valueLower_pos : 0 < valueLower
  top_diffCont :
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
          radius)
  bottom_diffCont :
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
          radius)
  top_sphereBound :
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
            radius →
        ‖zetaSideFactor w‖ ≤
          amplitude *
            (1 +
              ‖(zetaCompletedExplicitFormulaAutocorrelationCofinalHeightSchedule f).height u‖) ^ K
  bottom_sphereBound :
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
            radius →
        ‖zetaSideFactor w‖ ≤
          amplitude *
            (1 +
              ‖(zetaCompletedExplicitFormulaAutocorrelationCofinalHeightSchedule f).height u‖) ^ K
  top_valueLower :
    ∀ u x : ℝ,
      x ∈ Set.uIcc
        (zetaCompletedExplicitFormula_autocorrelation_contourFamily f).c
        (1 - (zetaCompletedExplicitFormula_autocorrelation_contourFamily f).c) →
      valueLower ≤
        ‖zetaSideFactor
          (zetaCompletedExplicitFormulaTopPath
            ((zetaCompletedExplicitFormula_autocorrelation_contourFamily f).rectangle
              ((zetaCompletedExplicitFormulaAutocorrelationCofinalHeightSchedule f).height u))
            x)‖
  bottom_valueLower :
    ∀ u x : ℝ,
      x ∈ Set.uIcc
        (zetaCompletedExplicitFormula_autocorrelation_contourFamily f).c
        (1 - (zetaCompletedExplicitFormula_autocorrelation_contourFamily f).c) →
      valueLower ≤
        ‖zetaSideFactor
          (zetaCompletedExplicitFormulaBottomPath
            ((zetaCompletedExplicitFormula_autocorrelation_contourFamily f).rectangle
              ((zetaCompletedExplicitFormulaAutocorrelationCofinalHeightSchedule f).height u))
            x)‖

structure CanonicalScheduledInverseGammaCauchyPathData
    (f : ZetaAdmissibleFunction) (K : ℕ) where
  radius : ℝ
  amplitude : ℝ
  valueLower : ℝ
  radius_pos : 0 < radius
  amplitude_pos : 0 < amplitude
  valueLower_pos : 0 < valueLower
  top_diffCont :
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
          radius)
  bottom_diffCont :
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
          radius)
  top_sphereBound :
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
            radius →
        ‖(Complex.Gammaℝ w)⁻¹‖ ≤
          amplitude *
            (1 +
              ‖(zetaCompletedExplicitFormulaAutocorrelationCofinalHeightSchedule f).height u‖) ^ K
  bottom_sphereBound :
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
            radius →
        ‖(Complex.Gammaℝ w)⁻¹‖ ≤
          amplitude *
            (1 +
              ‖(zetaCompletedExplicitFormulaAutocorrelationCofinalHeightSchedule f).height u‖) ^ K
  top_valueLower :
    ∀ u x : ℝ,
      x ∈ Set.uIcc
        (zetaCompletedExplicitFormula_autocorrelation_contourFamily f).c
        (1 - (zetaCompletedExplicitFormula_autocorrelation_contourFamily f).c) →
      valueLower ≤
        ‖(Complex.Gammaℝ
          (zetaCompletedExplicitFormulaTopPath
            ((zetaCompletedExplicitFormula_autocorrelation_contourFamily f).rectangle
              ((zetaCompletedExplicitFormulaAutocorrelationCofinalHeightSchedule f).height u))
            x))⁻¹‖
  bottom_valueLower :
    ∀ u x : ℝ,
      x ∈ Set.uIcc
        (zetaCompletedExplicitFormula_autocorrelation_contourFamily f).c
        (1 - (zetaCompletedExplicitFormula_autocorrelation_contourFamily f).c) →
      valueLower ≤
        ‖(Complex.Gammaℝ
          (zetaCompletedExplicitFormulaBottomPath
            ((zetaCompletedExplicitFormula_autocorrelation_contourFamily f).rectangle
              ((zetaCompletedExplicitFormulaAutocorrelationCofinalHeightSchedule f).height u))
            x))⁻¹‖

def CanonicalScheduledZetaSideCauchyPathData.boundConstant
    {f : ZetaAdmissibleFunction} {K : ℕ}
    (data : CanonicalScheduledZetaSideCauchyPathData f K) : ℝ :=
  (data.amplitude / data.radius) / data.valueLower

def CanonicalScheduledInverseGammaCauchyPathData.boundConstant
    {f : ZetaAdmissibleFunction} {K : ℕ}
    (data : CanonicalScheduledInverseGammaCauchyPathData f K) : ℝ :=
  (data.amplitude / data.radius) / data.valueLower

theorem CanonicalScheduledZetaSideCauchyPathData.boundConstant_pos
    {f : ZetaAdmissibleFunction} {K : ℕ}
    (data : CanonicalScheduledZetaSideCauchyPathData f K) :
    0 < data.boundConstant :=
  div_pos
    (div_pos data.amplitude_pos data.radius_pos)
    data.valueLower_pos

theorem CanonicalScheduledInverseGammaCauchyPathData.boundConstant_pos
    {f : ZetaAdmissibleFunction} {K : ℕ}
    (data : CanonicalScheduledInverseGammaCauchyPathData f K) :
    0 < data.boundConstant :=
  div_pos
    (div_pos data.amplitude_pos data.radius_pos)
    data.valueLower_pos

theorem zetaSideNegLogDeriv_path_bound_of_cauchyLogDerivative
    (z : ℂ) (K : ℕ) (height R A δ : ℝ)
    (R_pos : 0 < R)
    (δ_pos : 0 < δ)
    (diffCont :
      DiffContOnCl ℂ zetaSideFactor (Metric.ball z R))
    (sphereBound :
      ∀ w : ℂ,
        w ∈ Metric.sphere z R →
        ‖zetaSideFactor w‖ ≤ A * (1 + ‖height‖) ^ K)
    (valueLower : δ ≤ ‖zetaSideFactor z‖) :
    ‖zetaSideNegLogDeriv z‖ ≤
      ((A / R) / δ) * (1 + ‖height‖) ^ K :=
  let q : ℝ := (1 + ‖height‖) ^ K
  let rawBound :
      ‖deriv zetaSideFactor z / zetaSideFactor z‖ ≤
        ((A / R) / δ) * q :=
    cauchy_logDeriv_polynomial_norm_le_of_sphere_bound
      (f := zetaSideFactor)
      (z := z)
      (R := R)
      (A := A)
      (δ := δ)
      (q := q)
      R_pos
      diffCont
      sphereBound
      δ_pos
      valueLower
  let definitionEquality :
      ‖zetaSideNegLogDeriv z‖ =
        ‖-deriv zetaSideFactor z / zetaSideFactor z‖ :=
    congrArg (fun value : ℂ => ‖value‖)
      (zetaSideNegLogDeriv_eq_def z)
  let negEquality :
      ‖-deriv zetaSideFactor z / zetaSideFactor z‖ =
        ‖deriv zetaSideFactor z / zetaSideFactor z‖ :=
    norm_neg_div_eq_norm_div
      (deriv zetaSideFactor z)
      (zetaSideFactor z)
  let normEquality :
      ‖zetaSideNegLogDeriv z‖ =
        ‖deriv zetaSideFactor z / zetaSideFactor z‖ :=
    Eq.trans definitionEquality negEquality
  Eq.subst
    (motive := fun value : ℝ =>
      value ≤ ((A / R) / δ) * q)
    normEquality.symm
    rawBound

theorem zetaSideNegLogDeriv_path_bound_of_scaled_sphere_polynomial_bound
    (z : ℂ) (K : ℕ) (height R A δ : ℝ)
    (R_pos : 0 < R)
    (δ_pos : 0 < δ)
    (diffCont :
      DiffContOnCl ℂ zetaSideFactor (Metric.ball z R))
    (sphereBound :
      ∀ w : ℂ,
        w ∈ Metric.sphere z R →
        ‖zetaSideFactor w‖ ≤ A * (3 * (1 + ‖height‖)) ^ K)
    (valueLower : δ ≤ ‖zetaSideFactor z‖) :
    ‖zetaSideNegLogDeriv z‖ ≤
      ((A * 3 ^ K / R) / δ) * (1 + ‖height‖) ^ K := by
  have normalizedSphereBound :
      ∀ w : ℂ,
        w ∈ Metric.sphere z R →
        ‖zetaSideFactor w‖ ≤
          (A * 3 ^ K) * (1 + ‖height‖) ^ K := by
    intro w hw
    have hbound := sphereBound w hw
    calc
      ‖zetaSideFactor w‖ ≤ A * (3 * (1 + ‖height‖)) ^ K := hbound
      _ = (A * 3 ^ K) * (1 + ‖height‖) ^ K := by
        calc
          A * (3 * (1 + ‖height‖)) ^ K =
              A * (3 ^ K * (1 + ‖height‖) ^ K) := by
            exact congrArg (fun q : ℝ => A * q)
              (mul_pow 3 (1 + ‖height‖) K)
          _ = (A * 3 ^ K) * (1 + ‖height‖) ^ K := by
            exact (mul_assoc A (3 ^ K) ((1 + ‖height‖) ^ K)).symm
  have rawBound :=
    zetaSideNegLogDeriv_path_bound_of_cauchyLogDerivative
      z K height R (A * 3 ^ K) δ R_pos δ_pos diffCont
      normalizedSphereBound valueLower
  exact rawBound

theorem zetaSideNegLogDeriv_path_bound_of_center_height_sphere_polynomial_bound
    (z : ℂ) (K : ℕ) (height R A δ : ℝ)
    (R_pos : 0 < R) (R_le_two : R ≤ 2) (A_nonneg : 0 ≤ A)
    (δ_pos : 0 < δ)
    (diffCont : DiffContOnCl ℂ zetaSideFactor (Metric.ball z R))
    (sphereBound :
      ∀ w : ℂ,
        w ∈ Metric.sphere z R →
        ‖zetaSideFactor w‖ ≤ A * (1 + ‖w.im‖) ^ K)
    (valueLower : δ ≤ ‖zetaSideFactor z‖) :
    ‖zetaSideNegLogDeriv z‖ ≤
      (A * 3 ^ K / R) / δ * (1 + ‖z.im‖) ^ K := by
  have normalizedSphereBound :
      ∀ w : ℂ,
        w ∈ Metric.sphere z R →
        ‖zetaSideFactor w‖ ≤
          (A * 3 ^ K) * (1 + ‖z.im‖) ^ K :=
    sphere_bound_of_center_height_polynomial_bound
      (G := zetaSideFactor)
      z R A K A_nonneg
      (le_add_of_nonneg_right (norm_nonneg z.im))
      (le_of_lt R_pos) R_le_two sphereBound
  exact zetaSideNegLogDeriv_path_bound_of_cauchyLogDerivative
    z K height R (A * 3 ^ K) δ R_pos δ_pos diffCont
    normalizedSphereBound valueLower

theorem zetaSideNegLogDeriv_path_bound_of_center_height_sphere_polynomial_bound_add_radius
    (z : ℂ) (K : ℕ) (height R A δ : ℝ)
    (R_pos : 0 < R) (A_nonneg : 0 ≤ A) (δ_pos : 0 < δ)
    (diffCont : DiffContOnCl ℂ zetaSideFactor (Metric.ball z R))
    (sphereBound :
      ∀ w : ℂ,
        w ∈ Metric.sphere z R →
        ‖zetaSideFactor w‖ ≤ A * (1 + ‖w.im‖) ^ K)
    (valueLower : δ ≤ ‖zetaSideFactor z‖) :
    ‖zetaSideNegLogDeriv z‖ ≤
      (A / R / δ) * (1 + ‖z.im‖ + R) ^ K := by
  have normalizedSphereBound :
      ∀ w : ℂ,
        w ∈ Metric.sphere z R →
        ‖zetaSideFactor w‖ ≤ A * (1 + ‖z.im‖ + R) ^ K :=
    sphere_bound_of_center_height_polynomial_bound_add_radius
      (G := zetaSideFactor) z R A K A_nonneg
      (le_of_lt R_pos) sphereBound
  exact zetaSideNegLogDeriv_path_bound_of_cauchyLogDerivative
    z K height R A δ R_pos δ_pos diffCont normalizedSphereBound valueLower

theorem zetaSideNegLogDeriv_path_bound_of_exponential_sphere_bound
    (z : ℂ) (m : ℕ) (height R A B δ : ℝ)
    (R_pos : 0 < R)
    (δ_pos : 0 < δ)
    (diffCont : DiffContOnCl ℂ zetaSideFactor (Metric.ball z R))
    (sphereBound :
      ∀ w : ℂ, w ∈ Metric.sphere z R →
        ‖zetaSideFactor w‖ ≤ A * Real.exp (B * (1 + ‖height‖) ^ m))
    (valueLower : δ ≤ ‖zetaSideFactor z‖) :
    ‖zetaSideNegLogDeriv z‖ ≤
      ((A / R) / δ) * Real.exp (B * (1 + ‖height‖) ^ m) := by
  let q : ℝ := Real.exp (B * (1 + ‖height‖) ^ m)
  have hraw : ‖deriv zetaSideFactor z / zetaSideFactor z‖ ≤
      ((A / R) / δ) * q :=
    cauchy_logDeriv_polynomial_norm_le_of_sphere_bound
      (f := zetaSideFactor) (z := z) (R := R) (A := A) (δ := δ)
      (q := q) R_pos diffCont
      (fun w hw => sphereBound w hw)
      δ_pos valueLower
  have hdefinition : ‖zetaSideNegLogDeriv z‖ =
      ‖-deriv zetaSideFactor z / zetaSideFactor z‖ :=
    congrArg (fun value : ℂ => ‖value‖) (zetaSideNegLogDeriv_eq_def z)
  have hneg : ‖-deriv zetaSideFactor z / zetaSideFactor z‖ =
      ‖deriv zetaSideFactor z / zetaSideFactor z‖ :=
    norm_neg_div_eq_norm_div (deriv zetaSideFactor z) (zetaSideFactor z)
  have hnorm : ‖zetaSideNegLogDeriv z‖ =
      ‖deriv zetaSideFactor z / zetaSideFactor z‖ :=
    Eq.trans hdefinition hneg
  have hbound : ‖zetaSideNegLogDeriv z‖ ≤
      ((A / R) / δ) * q :=
    Eq.subst (motive := fun value : ℝ => value ≤ ((A / R) / δ) * q)
      hnorm.symm hraw
  exact hbound

theorem inverseGammaLogDeriv_path_bound_of_cauchyLogDerivative
    (z : ℂ) (K : ℕ) (height R A δ : ℝ)
    (R_pos : 0 < R)
    (δ_pos : 0 < δ)
    (diffCont :
      DiffContOnCl ℂ
        (fun w : ℂ => (Complex.Gammaℝ w)⁻¹)
        (Metric.ball z R))
    (sphereBound :
      ∀ w : ℂ,
        w ∈ Metric.sphere z R →
        ‖(Complex.Gammaℝ w)⁻¹‖ ≤ A * (1 + ‖height‖) ^ K)
    (valueLower : δ ≤ ‖(Complex.Gammaℝ z)⁻¹‖) :
    ‖deriv (fun w : ℂ => (Complex.Gammaℝ w)⁻¹) z /
        (Complex.Gammaℝ z)⁻¹‖ ≤
      ((A / R) / δ) * (1 + ‖height‖) ^ K :=
  cauchy_logDeriv_polynomial_norm_le_of_sphere_bound
    (f := fun w : ℂ => (Complex.Gammaℝ w)⁻¹)
    (z := z)
    (R := R)
    (A := A)
    (δ := δ)
    (q := (1 + ‖height‖) ^ K)
    R_pos
    diffCont
    sphereBound
    δ_pos
    valueLower

theorem inverseGammaLogDeriv_path_bound_of_exponential_sphere_bound
    (z : ℂ) (m : ℕ) (height R A B δ : ℝ)
    (R_pos : 0 < R)
    (δ_pos : 0 < δ)
    (diffCont :
      DiffContOnCl ℂ
        (fun w : ℂ => (Complex.Gammaℝ w)⁻¹)
        (Metric.ball z R))
    (sphereBound :
      ∀ w : ℂ,
        w ∈ Metric.sphere z R →
          ‖(Complex.Gammaℝ w)⁻¹‖ ≤
            A * Real.exp (B * (1 + ‖height‖) ^ m))
    (valueLower : δ ≤ ‖(Complex.Gammaℝ z)⁻¹‖) :
    ‖deriv (fun w : ℂ => (Complex.Gammaℝ w)⁻¹) z /
        (Complex.Gammaℝ z)⁻¹‖ ≤
      ((A / R) / δ) * Real.exp (B * (1 + ‖height‖) ^ m) :=
  cauchy_logDeriv_polynomial_norm_le_of_sphere_bound
    (f := fun w : ℂ => (Complex.Gammaℝ w)⁻¹)
    (z := z)
    (R := R)
    (A := A)
    (δ := δ)
    (q := Real.exp (B * (1 + ‖height‖) ^ m))
    R_pos
    diffCont
    sphereBound
    δ_pos
    valueLower

theorem inverseGamma_sphere_exponential_bound_of_strip_envelope
    (z : ℂ) (m : ℕ) (height R A B : ℝ)
    (hA_nonneg : 0 ≤ A) (hB_nonneg : 0 ≤ B)
    (sphereGeometry :
      ∀ w : ℂ, w ∈ Metric.sphere z R →
        0 ≤ w.re ∧ w.re ≤ 1 ∧
          (1 + ‖w‖) ^ m ≤ (1 + ‖height‖) ^ m)
    (globalEnvelope :
      ∀ w : ℂ, 0 ≤ w.re → w.re ≤ 1 →
        ‖(Complex.Gammaℝ w)⁻¹‖ ≤
          A * Real.exp (B * (1 + ‖w‖) ^ m)) :
    ∀ w : ℂ, w ∈ Metric.sphere z R →
      ‖(Complex.Gammaℝ w)⁻¹‖ ≤
        A * Real.exp (B * (1 + ‖height‖) ^ m) := by
  intro w hw
  obtain ⟨hw_left, hw_right, hw_norm⟩ := sphereGeometry w hw
  have hraw := globalEnvelope w hw_left hw_right
  have hexp_mono :
      Real.exp (B * (1 + ‖w‖) ^ m) ≤
        Real.exp (B * (1 + ‖height‖) ^ m) := by
    exact Real.exp_le_exp.mpr
      (mul_le_mul_of_nonneg_left hw_norm hB_nonneg)
  exact hraw.trans (mul_le_mul_of_nonneg_left hexp_mono hA_nonneg)

theorem complex_sphere_mem_rightCriticalStrip_of_center_margin
    (z w : ℂ) (R : ℝ)
    (hR : 0 ≤ R)
    (hz_left : R ≤ z.re)
    (hz_right : z.re + R ≤ 1)
    (hw : w ∈ Metric.sphere z R) :
    0 ≤ w.re ∧ w.re ≤ 1 := by
  have hdist : ‖w - z‖ = R := by
    calc
      ‖w - z‖ = dist w z := (dist_eq_norm w z).symm
      _ = R := Metric.mem_sphere.mp hw
  have hreal : |w.re - z.re| ≤ R := by
    calc
      |w.re - z.re| = |(w - z).re| := by rfl
      _ ≤ Complex.abs (w - z) := abs_re_le_abs (w - z)
      _ = ‖w - z‖ := (Complex.norm_eq_abs (w - z)).symm
      _ = R := hdist
  have hreal_bounds : -R ≤ w.re - z.re ∧ w.re - z.re ≤ R :=
    abs_le.mp hreal
  have hlow : z.re - R ≤ w.re := by
    calc
      z.re - R = z.re + -R := sub_eq_add_neg z.re R
      _ ≤ (w.re - z.re) + z.re := add_le_add_right hreal_bounds.1 z.re
      _ = w.re := sub_add_cancel w.re z.re
  have hupp : w.re ≤ z.re + R := by
    calc
      w.re = (w.re - z.re) + z.re := (sub_add_cancel w.re z.re).symm
      _ ≤ R + z.re := add_le_add_right hreal_bounds.2 z.re
      _ = z.re + R := add_comm R z.re
  exact
    ⟨(le_trans (sub_nonneg.mpr hz_left) hlow),
      le_trans hupp hz_right⟩

theorem complex_sphere_norm_le_center_add_radius
    (z w : ℂ) (R : ℝ)
    (hw : w ∈ Metric.sphere z R) :
    ‖w‖ ≤ ‖z‖ + R := by
  have hdist : ‖w - z‖ = R := by
    exact (dist_eq_norm w z).symm.trans (Metric.mem_sphere.mp hw)
  calc
    ‖w‖ = ‖(w - z) + z‖ := by
      exact congrArg norm (sub_add_cancel w z).symm
    _ ≤ ‖w - z‖ + ‖z‖ := norm_add_le _ _
    _ = R + ‖z‖ := congrArg (fun t : ℝ => t + ‖z‖) hdist
    _ = ‖z‖ + R := add_comm R ‖z‖

theorem complex_sphere_strip_and_power_geometry
    (z w : ℂ) (R height : ℝ) (m : ℕ)
    (hR : 0 ≤ R)
    (hz_left : R ≤ z.re)
    (hz_right : z.re + R ≤ 1)
    (hz_norm : ‖z‖ + R ≤ ‖height‖)
    (hw : w ∈ Metric.sphere z R) :
    0 ≤ w.re ∧ w.re ≤ 1 ∧
      (1 + ‖w‖) ^ m ≤ (1 + ‖height‖) ^ m := by
  have hstrip :=
    complex_sphere_mem_rightCriticalStrip_of_center_margin
      z w R hR hz_left hz_right hw
  have hnorm := complex_sphere_norm_le_center_add_radius z w R hw
  have hbase : 1 + ‖w‖ ≤ 1 + ‖height‖ := by
    exact (add_le_add_left hnorm 1).trans (add_le_add_left hz_norm 1)
  have hpow : (1 + ‖w‖) ^ m ≤ (1 + ‖height‖) ^ m := by
    exact pow_le_pow_left₀ (add_nonneg zero_le_one (norm_nonneg w)) hbase m
  exact ⟨hstrip.1, hstrip.2, hpow⟩

theorem inverseGamma_sphere_exponential_bound_of_center_geometry
    (z : ℂ) (m : ℕ) (height R A B : ℝ)
    (hA_nonneg : 0 ≤ A) (hB_nonneg : 0 ≤ B)
    (hR : 0 ≤ R)
    (hz_left : R ≤ z.re)
    (hz_right : z.re + R ≤ 1)
    (hz_norm : ‖z‖ + R ≤ ‖height‖)
    (globalEnvelope :
      ∀ w : ℂ, 0 ≤ w.re → w.re ≤ 1 →
        ‖(Complex.Gammaℝ w)⁻¹‖ ≤
          A * Real.exp (B * (1 + ‖w‖) ^ m)) :
    ∀ w : ℂ, w ∈ Metric.sphere z R →
      ‖(Complex.Gammaℝ w)⁻¹‖ ≤
        A * Real.exp (B * (1 + ‖height‖) ^ m) := by
  intro w hw
  exact inverseGamma_sphere_exponential_bound_of_strip_envelope
    z m height R A B hA_nonneg hB_nonneg
    (fun v hv =>
      complex_sphere_strip_and_power_geometry
        z v R height m hR hz_left hz_right hz_norm hv)
    globalEnvelope w hw

theorem topPath_sphere_rightCriticalStrip_geometry
    (x T R : ℝ)
    (hR : 0 ≤ R)
    (hx_lower : R ≤ x)
    (hx_upper : x + R ≤ 1) :
    ∀ w : ℂ, w ∈ Metric.sphere ((x : ℂ) + (T : ℂ) * Complex.I) R →
      0 ≤ w.re ∧ w.re ≤ 1 := by
  intro w hw
  exact complex_sphere_mem_rightCriticalStrip_of_center_margin
    ((x : ℂ) + (T : ℂ) * Complex.I) w R hR
    (by
      change R ≤ x
      exact hx_lower)
    (by
      change x + R ≤ 1
      exact hx_upper)
    hw

theorem bottomPath_sphere_rightCriticalStrip_geometry
    (x T R : ℝ)
    (hR : 0 ≤ R)
    (hx_lower : R ≤ x)
    (hx_upper : x + R ≤ 1) :
    ∀ w : ℂ, w ∈ Metric.sphere ((x : ℂ) - (T : ℂ) * Complex.I) R →
      0 ≤ w.re ∧ w.re ≤ 1 := by
  intro w hw
  exact complex_sphere_mem_rightCriticalStrip_of_center_margin
    ((x : ℂ) - (T : ℂ) * Complex.I) w R hR
    (by
      change R ≤ x
      exact hx_lower)
    (by
      change x + R ≤ 1
      exact hx_upper)
    hw

theorem topPath_sphere_polynomial_height_geometry
    (x T R height : ℝ) (m : ℕ)
    (hR : 0 ≤ R)
    (hx_lower : R ≤ x)
    (hx_upper : x + R ≤ 1)
    (hheight : ‖((x : ℂ) + (T : ℂ) * Complex.I)‖ + R ≤ ‖height‖) :
    ∀ w : ℂ, w ∈ Metric.sphere ((x : ℂ) + (T : ℂ) * Complex.I) R →
      0 ≤ w.re ∧ w.re ≤ 1 ∧
        (1 + ‖w‖) ^ m ≤ (1 + ‖height‖) ^ m := by
  intro w hw
  exact complex_sphere_strip_and_power_geometry
    ((x : ℂ) + (T : ℂ) * Complex.I) w R height m hR
    (by
      change R ≤ x
      exact hx_lower)
    (by
      change x + R ≤ 1
      exact hx_upper)
    hheight hw

theorem bottomPath_sphere_polynomial_height_geometry
    (x T R height : ℝ) (m : ℕ)
    (hR : 0 ≤ R)
    (hx_lower : R ≤ x)
    (hx_upper : x + R ≤ 1)
    (hheight : ‖((x : ℂ) - (T : ℂ) * Complex.I)‖ + R ≤ ‖height‖) :
    ∀ w : ℂ, w ∈ Metric.sphere ((x : ℂ) - (T : ℂ) * Complex.I) R →
      0 ≤ w.re ∧ w.re ≤ 1 ∧
        (1 + ‖w‖) ^ m ≤ (1 + ‖height‖) ^ m := by
  intro w hw
  exact complex_sphere_strip_and_power_geometry
    ((x : ℂ) - (T : ℂ) * Complex.I) w R height m hR
    (by
      change R ≤ x
      exact hx_lower)
    (by
      change x + R ≤ 1
      exact hx_upper)
    hheight hw

theorem topPath_zetaSideFactor_sphere_bound_of_geometry
    (x T R height : ℝ) (m : ℕ) (A B : ℝ)
    (hA_nonneg : 0 ≤ A) (hB_nonneg : 0 ≤ B)
    (hR : 0 ≤ R)
    (hx_lower : R ≤ x)
    (hx_upper : x + R ≤ 1)
    (hheight : ‖((x : ℂ) + (T : ℂ) * Complex.I)‖ + R ≤ ‖height‖)
    (globalEnvelope :
      ∀ w : ℂ, 0 ≤ w.re → w.re ≤ 1 →
        ‖zetaSideFactor w‖ ≤
          A * Real.exp (B * (1 + ‖w‖) ^ m)) :
    ∀ w : ℂ, w ∈ Metric.sphere ((x : ℂ) + (T : ℂ) * Complex.I) R →
      ‖zetaSideFactor w‖ ≤
        A * Real.exp (B * (1 + ‖height‖) ^ m) := by
  intro w hw
  have hgeometry := topPath_sphere_polynomial_height_geometry
    x T R height m hR hx_lower hx_upper hheight w hw
  exact (globalEnvelope w hgeometry.1 hgeometry.2.1).trans
    (mul_le_mul_of_nonneg_left
      (Real.exp_le_exp.mpr
        (mul_le_mul_of_nonneg_left hgeometry.2.2 hB_nonneg))
      hA_nonneg)

theorem bottomPath_zetaSideFactor_sphere_bound_of_geometry
    (x T R height : ℝ) (m : ℕ) (A B : ℝ)
    (hA_nonneg : 0 ≤ A) (hB_nonneg : 0 ≤ B)
    (hR : 0 ≤ R)
    (hx_lower : R ≤ x)
    (hx_upper : x + R ≤ 1)
    (hheight : ‖((x : ℂ) - (T : ℂ) * Complex.I)‖ + R ≤ ‖height‖)
    (globalEnvelope :
      ∀ w : ℂ, 0 ≤ w.re → w.re ≤ 1 →
        ‖zetaSideFactor w‖ ≤
          A * Real.exp (B * (1 + ‖w‖) ^ m)) :
    ∀ w : ℂ, w ∈ Metric.sphere ((x : ℂ) - (T : ℂ) * Complex.I) R →
      ‖zetaSideFactor w‖ ≤
        A * Real.exp (B * (1 + ‖height‖) ^ m) := by
  intro w hw
  have hgeometry := bottomPath_sphere_polynomial_height_geometry
    x T R height m hR hx_lower hx_upper hheight w hw
  exact (globalEnvelope w hgeometry.1 hgeometry.2.1).trans
    (mul_le_mul_of_nonneg_left
      (Real.exp_le_exp.mpr
        (mul_le_mul_of_nonneg_left hgeometry.2.2 hB_nonneg))
      hA_nonneg)

theorem topPath_inverseGamma_sphere_bound_of_geometry
    (x T R height : ℝ) (m : ℕ) (A B : ℝ)
    (hA_nonneg : 0 ≤ A) (hB_nonneg : 0 ≤ B)
    (hR : 0 ≤ R)
    (hx_lower : R ≤ x)
    (hx_upper : x + R ≤ 1)
    (hheight : ‖((x : ℂ) + (T : ℂ) * Complex.I)‖ + R ≤ ‖height‖)
    (globalEnvelope :
      ∀ w : ℂ, 0 ≤ w.re → w.re ≤ 1 →
        ‖(Complex.Gammaℝ w)⁻¹‖ ≤
          A * Real.exp (B * (1 + ‖w‖) ^ m)) :
    ∀ w : ℂ, w ∈ Metric.sphere ((x : ℂ) + (T : ℂ) * Complex.I) R →
      ‖(Complex.Gammaℝ w)⁻¹‖ ≤
        A * Real.exp (B * (1 + ‖height‖) ^ m) := by
  exact inverseGamma_sphere_exponential_bound_of_center_geometry
    ((x : ℂ) + (T : ℂ) * Complex.I) m height R A B
    hA_nonneg hB_nonneg hR
    (by exact hx_lower)
    (by exact hx_upper)
    hheight globalEnvelope

theorem bottomPath_inverseGamma_sphere_bound_of_geometry
    (x T R height : ℝ) (m : ℕ) (A B : ℝ)
    (hA_nonneg : 0 ≤ A) (hB_nonneg : 0 ≤ B)
    (hR : 0 ≤ R)
    (hx_lower : R ≤ x)
    (hx_upper : x + R ≤ 1)
    (hheight : ‖((x : ℂ) - (T : ℂ) * Complex.I)‖ + R ≤ ‖height‖)
    (globalEnvelope :
      ∀ w : ℂ, 0 ≤ w.re → w.re ≤ 1 →
        ‖(Complex.Gammaℝ w)⁻¹‖ ≤
          A * Real.exp (B * (1 + ‖w‖) ^ m)) :
    ∀ w : ℂ, w ∈ Metric.sphere ((x : ℂ) - (T : ℂ) * Complex.I) R →
      ‖(Complex.Gammaℝ w)⁻¹‖ ≤
        A * Real.exp (B * (1 + ‖height‖) ^ m) := by
  exact inverseGamma_sphere_exponential_bound_of_center_geometry
    ((x : ℂ) - (T : ℂ) * Complex.I) m height R A B
    hA_nonneg hB_nonneg hR
    (by exact hx_lower)
    (by exact hx_upper)
    hheight globalEnvelope

theorem horizontalPaths_zetaSideFactor_sphere_bounds_of_geometry
    (x T R height : ℝ) (m : ℕ) (A B : ℝ)
    (hA_nonneg : 0 ≤ A) (hB_nonneg : 0 ≤ B)
    (hR : 0 ≤ R)
    (hx_lower : R ≤ x)
    (hx_upper : x + R ≤ 1)
    (topHeight : ‖((x : ℂ) + (T : ℂ) * Complex.I)‖ + R ≤ ‖height‖)
    (bottomHeight : ‖((x : ℂ) - (T : ℂ) * Complex.I)‖ + R ≤ ‖height‖)
    (globalEnvelope :
      ∀ w : ℂ, 0 ≤ w.re → w.re ≤ 1 →
        ‖zetaSideFactor w‖ ≤
          A * Real.exp (B * (1 + ‖w‖) ^ m)) :
    (∀ w : ℂ,
      w ∈ Metric.sphere ((x : ℂ) + (T : ℂ) * Complex.I) R →
        ‖zetaSideFactor w‖ ≤
          A * Real.exp (B * (1 + ‖height‖) ^ m)) ∧
    (∀ w : ℂ,
      w ∈ Metric.sphere ((x : ℂ) - (T : ℂ) * Complex.I) R →
        ‖zetaSideFactor w‖ ≤
          A * Real.exp (B * (1 + ‖height‖) ^ m)) := by
  exact ⟨
    topPath_zetaSideFactor_sphere_bound_of_geometry
      x T R height m A B hA_nonneg hB_nonneg hR hx_lower hx_upper
      topHeight globalEnvelope,
    bottomPath_zetaSideFactor_sphere_bound_of_geometry
      x T R height m A B hA_nonneg hB_nonneg hR hx_lower hx_upper
      bottomHeight globalEnvelope⟩

/- The two horizontal carrier estimates use the same strip envelope and the
   same geometric radius hypotheses.  Exporting them as one owner package
   keeps downstream scheduled-carrier constructors from reintroducing the
   two sphere obligations independently. -/
theorem horizontalPaths_inverseGamma_sphere_bounds_of_geometry
    (x T R height : ℝ) (m : ℕ) (A B : ℝ)
    (hA_nonneg : 0 ≤ A) (hB_nonneg : 0 ≤ B)
    (hR : 0 ≤ R)
    (hx_lower : R ≤ x)
    (hx_upper : x + R ≤ 1)
    (topHeight : ‖((x : ℂ) + (T : ℂ) * Complex.I)‖ + R ≤ ‖height‖)
    (bottomHeight : ‖((x : ℂ) - (T : ℂ) * Complex.I)‖ + R ≤ ‖height‖)
    (globalEnvelope :
      ∀ w : ℂ, 0 ≤ w.re → w.re ≤ 1 →
        ‖(Complex.Gammaℝ w)⁻¹‖ ≤
          A * Real.exp (B * (1 + ‖w‖) ^ m)) :
    (∀ w : ℂ,
      w ∈ Metric.sphere ((x : ℂ) + (T : ℂ) * Complex.I) R →
        ‖(Complex.Gammaℝ w)⁻¹‖ ≤
          A * Real.exp (B * (1 + ‖height‖) ^ m)) ∧
    (∀ w : ℂ,
      w ∈ Metric.sphere ((x : ℂ) - (T : ℂ) * Complex.I) R →
        ‖(Complex.Gammaℝ w)⁻¹‖ ≤
          A * Real.exp (B * (1 + ‖height‖) ^ m)) := by
  exact ⟨
    topPath_inverseGamma_sphere_bound_of_geometry
      x T R height m A B hA_nonneg hB_nonneg hR hx_lower hx_upper
      topHeight globalEnvelope,
    bottomPath_inverseGamma_sphere_bound_of_geometry
      x T R height m A B hA_nonneg hB_nonneg hR hx_lower hx_upper
      bottomHeight globalEnvelope⟩

theorem topPath_inverseGamma_logDeriv_bound_of_sphere_geometry
    (x T R height : ℝ) (K m : ℕ) (A B δ : ℝ)
    (hR : 0 < R) (hδ : 0 < δ)
    (diffCont :
      DiffContOnCl ℂ (fun w : ℂ => (Complex.Gammaℝ w)⁻¹)
        (Metric.ball ((x : ℂ) + (T : ℂ) * Complex.I) R))
    (sphereBound :
      ∀ w : ℂ, w ∈ Metric.sphere ((x : ℂ) + (T : ℂ) * Complex.I) R →
        ‖(Complex.Gammaℝ w)⁻¹‖ ≤ A * (3 * (1 + ‖height‖)) ^ K)
    (valueLower :
      δ ≤ ‖(Complex.Gammaℝ ((x : ℂ) + (T : ℂ) * Complex.I))⁻¹‖) :
    ‖deriv (fun w : ℂ => (Complex.Gammaℝ w)⁻¹)
        ((x : ℂ) + (T : ℂ) * Complex.I) /
        (Complex.Gammaℝ ((x : ℂ) + (T : ℂ) * Complex.I))⁻¹‖ ≤
      ((A * 3 ^ K / R) / δ) * (1 + ‖height‖) ^ K := by
  apply cauchy_logDeriv_polynomial_norm_le_of_sphere_bound hR diffCont
  · intro w hw
    have hraw := sphereBound w hw
    let q : ℝ := 1 + ‖height‖
    have hpow : (3 * q) ^ K = 3 ^ K * q ^ K := mul_pow 3 q K
    exact hraw.trans_eq
      (Eq.trans
        (congrArg (fun v : ℝ => A * v) hpow)
        (mul_assoc A (3 ^ K) (q ^ K)).symm)
  · exact hδ
  · exact valueLower

theorem bottomPath_inverseGamma_logDeriv_bound_of_sphere_geometry
    (x T R height : ℝ) (K m : ℕ) (A B δ : ℝ)
    (hR : 0 < R) (hδ : 0 < δ)
    (diffCont :
      DiffContOnCl ℂ (fun w : ℂ => (Complex.Gammaℝ w)⁻¹)
        (Metric.ball ((x : ℂ) - (T : ℂ) * Complex.I) R))
    (sphereBound :
      ∀ w : ℂ, w ∈ Metric.sphere ((x : ℂ) - (T : ℂ) * Complex.I) R →
        ‖(Complex.Gammaℝ w)⁻¹‖ ≤ A * (3 * (1 + ‖height‖)) ^ K)
    (valueLower :
      δ ≤ ‖(Complex.Gammaℝ ((x : ℂ) - (T : ℂ) * Complex.I))⁻¹‖) :
    ‖deriv (fun w : ℂ => (Complex.Gammaℝ w)⁻¹)
        ((x : ℂ) - (T : ℂ) * Complex.I) /
        (Complex.Gammaℝ ((x : ℂ) - (T : ℂ) * Complex.I))⁻¹‖ ≤
      ((A * 3 ^ K / R) / δ) * (1 + ‖height‖) ^ K := by
  apply cauchy_logDeriv_polynomial_norm_le_of_sphere_bound hR diffCont
  · intro w hw
    have hraw := sphereBound w hw
    let q : ℝ := 1 + ‖height‖
    have hpow : (3 * q) ^ K = 3 ^ K * q ^ K := mul_pow 3 q K
    exact hraw.trans_eq
      (Eq.trans
        (congrArg (fun v : ℝ => A * v) hpow)
        (mul_assoc A (3 ^ K) (q ^ K)).symm)
  · exact hδ
  · exact valueLower

/- The paired form is the owner-level interface used when the completed
   logarithmic derivative is split into its top and bottom horizontal paths. -/
theorem horizontalPaths_inverseGamma_logDeriv_bounds_of_sphere_geometry
    (x T R height : ℝ) (K m : ℕ) (A δTop δBottom : ℝ)
    (hR : 0 < R) (hδTop : 0 < δTop) (hδBottom : 0 < δBottom)
    (topDiffCont :
      DiffContOnCl ℂ
        (fun w : ℂ => (Complex.Gammaℝ w)⁻¹)
        (Metric.ball ((x : ℂ) + (T : ℂ) * Complex.I) R))
    (bottomDiffCont :
      DiffContOnCl ℂ
        (fun w : ℂ => (Complex.Gammaℝ w)⁻¹)
        (Metric.ball ((x : ℂ) - (T : ℂ) * Complex.I) R))
    (topSphereBound :
      ∀ w : ℂ,
        w ∈ Metric.sphere ((x : ℂ) + (T : ℂ) * Complex.I) R →
          ‖(Complex.Gammaℝ w)⁻¹‖ ≤
            A * (3 * (1 + ‖height‖)) ^ K)
    (bottomSphereBound :
      ∀ w : ℂ,
        w ∈ Metric.sphere ((x : ℂ) - (T : ℂ) * Complex.I) R →
          ‖(Complex.Gammaℝ w)⁻¹‖ ≤
            A * (3 * (1 + ‖height‖)) ^ K)
    (topValueLower :
      δTop ≤ ‖(Complex.Gammaℝ ((x : ℂ) + (T : ℂ) * Complex.I))⁻¹‖)
    (bottomValueLower :
      δBottom ≤ ‖(Complex.Gammaℝ ((x : ℂ) - (T : ℂ) * Complex.I))⁻¹‖) :
    (‖deriv (fun w : ℂ => (Complex.Gammaℝ w)⁻¹)
        ((x : ℂ) + (T : ℂ) * Complex.I) /
        (Complex.Gammaℝ ((x : ℂ) + (T : ℂ) * Complex.I))⁻¹‖ ≤
      ((A * 3 ^ K / R) / δTop) * (1 + ‖height‖) ^ K) ∧
    (‖deriv (fun w : ℂ => (Complex.Gammaℝ w)⁻¹)
        ((x : ℂ) - (T : ℂ) * Complex.I) /
        (Complex.Gammaℝ ((x : ℂ) - (T : ℂ) * Complex.I))⁻¹‖ ≤
      ((A * 3 ^ K / R) / δBottom) * (1 + ‖height‖) ^ K) := by
  exact ⟨
    topPath_inverseGamma_logDeriv_bound_of_sphere_geometry
      x T R height K m A δTop hR hδTop topDiffCont topSphereBound topValueLower,
    bottomPath_inverseGamma_logDeriv_bound_of_sphere_geometry
      x T R height K m A δBottom hR hδBottom bottomDiffCont bottomSphereBound
      bottomValueLower⟩

theorem inverseGammaLogDeriv_path_bound_of_scaled_sphere_polynomial_bound
    (z : ℂ) (K : ℕ) (height R A δ : ℝ)
    (R_pos : 0 < R)
    (δ_pos : 0 < δ)
    (diffCont :
      DiffContOnCl ℂ
        (fun w : ℂ => (Complex.Gammaℝ w)⁻¹)
        (Metric.ball z R))
    (sphereBound :
      ∀ w : ℂ,
        w ∈ Metric.sphere z R →
        ‖(Complex.Gammaℝ w)⁻¹‖ ≤ A * (3 * (1 + ‖height‖)) ^ K)
    (valueLower : δ ≤ ‖(Complex.Gammaℝ z)⁻¹‖) :
    ‖deriv (fun w : ℂ => (Complex.Gammaℝ w)⁻¹) z /
        (Complex.Gammaℝ z)⁻¹‖ ≤
      ((A * 3 ^ K / R) / δ) * (1 + ‖height‖) ^ K := by
  have normalizedSphereBound :
      ∀ w : ℂ,
        w ∈ Metric.sphere z R →
        ‖(Complex.Gammaℝ w)⁻¹‖ ≤
          (A * 3 ^ K) * (1 + ‖height‖) ^ K := by
    intro w hw
    have hbound := sphereBound w hw
    calc
      ‖(Complex.Gammaℝ w)⁻¹‖ ≤ A * (3 * (1 + ‖height‖)) ^ K := hbound
      _ = (A * 3 ^ K) * (1 + ‖height‖) ^ K := by
        calc
          A * (3 * (1 + ‖height‖)) ^ K =
              A * (3 ^ K * (1 + ‖height‖) ^ K) := by
            exact congrArg (fun q : ℝ => A * q)
              (mul_pow 3 (1 + ‖height‖) K)
          _ = (A * 3 ^ K) * (1 + ‖height‖) ^ K := by
            exact (mul_assoc A (3 ^ K) ((1 + ‖height‖) ^ K)).symm
  have rawBound :=
    inverseGammaLogDeriv_path_bound_of_cauchyLogDerivative
      z K height R (A * 3 ^ K) δ R_pos δ_pos diffCont
      normalizedSphereBound valueLower
  exact rawBound

theorem inverseGammaLogDeriv_path_bound_of_center_height_sphere_polynomial_bound
    (z : ℂ) (K : ℕ) (height R A δ : ℝ)
    (R_pos : 0 < R) (R_le_two : R ≤ 2) (A_nonneg : 0 ≤ A)
    (δ_pos : 0 < δ)
    (diffCont :
      DiffContOnCl ℂ
        (fun w : ℂ => (Complex.Gammaℝ w)⁻¹)
        (Metric.ball z R))
    (sphereBound :
      ∀ w : ℂ,
        w ∈ Metric.sphere z R →
        ‖(Complex.Gammaℝ w)⁻¹‖ ≤ A * (1 + ‖w.im‖) ^ K)
    (valueLower : δ ≤ ‖(Complex.Gammaℝ z)⁻¹‖) :
    ‖deriv (fun w : ℂ => (Complex.Gammaℝ w)⁻¹) z /
        (Complex.Gammaℝ z)⁻¹‖ ≤
      (A * 3 ^ K / R) / δ * (1 + ‖z.im‖) ^ K := by
  have normalizedSphereBound :
      ∀ w : ℂ,
        w ∈ Metric.sphere z R →
        ‖(Complex.Gammaℝ w)⁻¹‖ ≤
          (A * 3 ^ K) * (1 + ‖z.im‖) ^ K :=
    sphere_bound_of_center_height_polynomial_bound
      (G := fun w : ℂ => (Complex.Gammaℝ w)⁻¹)
      z R A K A_nonneg
      (le_add_of_nonneg_right (norm_nonneg z.im))
      (le_of_lt R_pos) R_le_two sphereBound
  exact inverseGammaLogDeriv_path_bound_of_cauchyLogDerivative
    z K height R (A * 3 ^ K) δ R_pos δ_pos diffCont
    normalizedSphereBound valueLower

theorem inverseGammaLogDeriv_path_bound_of_center_height_sphere_polynomial_bound_add_radius
    (z : ℂ) (K : ℕ) (height R A δ : ℝ)
    (R_pos : 0 < R) (A_nonneg : 0 ≤ A) (δ_pos : 0 < δ)
    (diffCont :
      DiffContOnCl ℂ
        (fun w : ℂ => (Complex.Gammaℝ w)⁻¹)
        (Metric.ball z R))
    (sphereBound :
      ∀ w : ℂ,
        w ∈ Metric.sphere z R →
        ‖(Complex.Gammaℝ w)⁻¹‖ ≤ A * (1 + ‖w.im‖) ^ K)
    (valueLower : δ ≤ ‖(Complex.Gammaℝ z)⁻¹‖) :
    ‖deriv (fun w : ℂ => (Complex.Gammaℝ w)⁻¹) z /
        (Complex.Gammaℝ z)⁻¹‖ ≤
      (A / R / δ) * (1 + ‖z.im‖ + R) ^ K := by
  have normalizedSphereBound :
      ∀ w : ℂ,
        w ∈ Metric.sphere z R →
        ‖(Complex.Gammaℝ w)⁻¹‖ ≤ A * (1 + ‖z.im‖ + R) ^ K :=
    sphere_bound_of_center_height_polynomial_bound_add_radius
      (G := fun w : ℂ => (Complex.Gammaℝ w)⁻¹)
      z R A K A_nonneg (le_of_lt R_pos) sphereBound
  exact inverseGammaLogDeriv_path_bound_of_cauchyLogDerivative
    z K height R A δ R_pos δ_pos diffCont normalizedSphereBound valueLower

theorem ExplicitFormulaCofinalHeightSchedule.topPath_zetaSideNegLogDeriv_bound_of_cauchy_data
    {F : ExplicitFormulaContourFamily}
    (schedule : ExplicitFormulaCofinalHeightSchedule F) (u : ℝ) (K : ℕ)
    (R A : ℝ) (hR : 0 < R) (hR_two : R ≤ 2) (hA : 0 ≤ A)
    (diffCont : ∀ x : ℝ, x ∈ Set.uIcc F.c (1 - F.c) →
      DiffContOnCl ℂ zetaSideFactor
        (Metric.ball
          (zetaCompletedExplicitFormulaTopPath
            (F.rectangle (schedule.height u)) x) R))
    (sphereBound : ∀ x : ℝ, x ∈ Set.uIcc F.c (1 - F.c) →
      ∀ w : ℂ,
        w ∈ Metric.sphere
          (zetaCompletedExplicitFormulaTopPath
            (F.rectangle (schedule.height u)) x) R →
        ‖zetaSideFactor w‖ ≤ A * (1 + ‖w.im‖) ^ K) :
    ∃ δ : ℝ, 0 < δ ∧
      ∀ x : ℝ, x ∈ Set.uIcc F.c (1 - F.c) →
        ‖zetaSideNegLogDeriv
          (zetaCompletedExplicitFormulaTopPath
            (F.rectangle (schedule.height u)) x)‖ ≤
          (A * 3 ^ K / R) / δ *
            (1 + ‖(zetaCompletedExplicitFormulaTopPath
              (F.rectangle (schedule.height u)) x).im) ^ K := by
  obtain ⟨δ, hδ, hδx⟩ :=
    schedule.topPath_zetaSideFactor_uniform_lower_bound u
  refine ⟨δ, hδ, ?_⟩
  intro x hx
  exact zetaSideNegLogDeriv_path_bound_of_center_height_sphere_polynomial_bound
    (zetaCompletedExplicitFormulaTopPath
      (F.rectangle (schedule.height u)) x)
    K (schedule.height u) R A hR hR_two hA hδ
    (diffCont x hx) (sphereBound x hx) (hδx x hx)

theorem ExplicitFormulaCofinalHeightSchedule.bottomPath_zetaSideNegLogDeriv_bound_of_cauchy_data
    {F : ExplicitFormulaContourFamily}
    (schedule : ExplicitFormulaCofinalHeightSchedule F) (u : ℝ) (K : ℕ)
    (R A : ℝ) (hR : 0 < R) (hR_two : R ≤ 2) (hA : 0 ≤ A)
    (diffCont : ∀ x : ℝ, x ∈ Set.uIcc F.c (1 - F.c) →
      DiffContOnCl ℂ zetaSideFactor
        (Metric.ball
          (zetaCompletedExplicitFormulaBottomPath
            (F.rectangle (schedule.height u)) x) R))
    (sphereBound : ∀ x : ℝ, x ∈ Set.uIcc F.c (1 - F.c) →
      ∀ w : ℂ,
        w ∈ Metric.sphere
          (zetaCompletedExplicitFormulaBottomPath
            (F.rectangle (schedule.height u)) x) R →
        ‖zetaSideFactor w‖ ≤ A * (1 + ‖w.im‖) ^ K) :
    ∃ δ : ℝ, 0 < δ ∧
      ∀ x : ℝ, x ∈ Set.uIcc F.c (1 - F.c) →
        ‖zetaSideNegLogDeriv
          (zetaCompletedExplicitFormulaBottomPath
            (F.rectangle (schedule.height u)) x)‖ ≤
          (A * 3 ^ K / R) / δ *
            (1 + ‖(zetaCompletedExplicitFormulaBottomPath
              (F.rectangle (schedule.height u)) x).im) ^ K := by
  obtain ⟨δ, hδ, hδx⟩ :=
    schedule.bottomPath_zetaSideFactor_uniform_lower_bound u
  refine ⟨δ, hδ, ?_⟩
  intro x hx
  exact zetaSideNegLogDeriv_path_bound_of_center_height_sphere_polynomial_bound
    (zetaCompletedExplicitFormulaBottomPath
      (F.rectangle (schedule.height u)) x)
    K (schedule.height u) R A hR hR_two hA hδ
    (diffCont x hx) (sphereBound x hx) (hδx x hx)

theorem ExplicitFormulaCofinalHeightSchedule.horizontalPaths_zetaSideNegLogDeriv_bounds_of_cauchy_data
    {F : ExplicitFormulaContourFamily}
    (schedule : ExplicitFormulaCofinalHeightSchedule F) (u : ℝ) (K : ℕ)
    (R A : ℝ) (hR : 0 < R) (hR_two : R ≤ 2) (hA : 0 ≤ A)
    (topDiffCont : ∀ x : ℝ, x ∈ Set.uIcc F.c (1 - F.c) →
      DiffContOnCl ℂ zetaSideFactor
        (Metric.ball
          (zetaCompletedExplicitFormulaTopPath
            (F.rectangle (schedule.height u)) x) R))
    (bottomDiffCont : ∀ x : ℝ, x ∈ Set.uIcc F.c (1 - F.c) →
      DiffContOnCl ℂ zetaSideFactor
        (Metric.ball
          (zetaCompletedExplicitFormulaBottomPath
            (F.rectangle (schedule.height u)) x) R))
    (topSphereBound : ∀ x : ℝ, x ∈ Set.uIcc F.c (1 - F.c) →
      ∀ w : ℂ,
        w ∈ Metric.sphere
          (zetaCompletedExplicitFormulaTopPath
            (F.rectangle (schedule.height u)) x) R →
        ‖zetaSideFactor w‖ ≤ A * (1 + ‖w.im‖) ^ K)
    (bottomSphereBound : ∀ x : ℝ, x ∈ Set.uIcc F.c (1 - F.c) →
      ∀ w : ℂ,
        w ∈ Metric.sphere
          (zetaCompletedExplicitFormulaBottomPath
            (F.rectangle (schedule.height u)) x) R →
        ‖zetaSideFactor w‖ ≤ A * (1 + ‖w.im‖) ^ K) :
    (∃ δTop : ℝ, 0 < δTop ∧
      ∀ x : ℝ, x ∈ Set.uIcc F.c (1 - F.c) →
        ‖zetaSideNegLogDeriv
          (zetaCompletedExplicitFormulaTopPath
            (F.rectangle (schedule.height u)) x)‖ ≤
          (A * 3 ^ K / R) / δTop *
            (1 + ‖(zetaCompletedExplicitFormulaTopPath
              (F.rectangle (schedule.height u)) x).im) ^ K) ∧
    (∃ δBottom : ℝ, 0 < δBottom ∧
      ∀ x : ℝ, x ∈ Set.uIcc F.c (1 - F.c) →
        ‖zetaSideNegLogDeriv
          (zetaCompletedExplicitFormulaBottomPath
            (F.rectangle (schedule.height u)) x)‖ ≤
          (A * 3 ^ K / R) / δBottom *
            (1 + ‖(zetaCompletedExplicitFormulaBottomPath
              (F.rectangle (schedule.height u)) x).im) ^ K) := by
  exact ⟨
    schedule.topPath_zetaSideNegLogDeriv_bound_of_cauchy_data u K R A hR hR_two hA
      topDiffCont topSphereBound,
    schedule.bottomPath_zetaSideNegLogDeriv_bound_of_cauchy_data u K R A hR hR_two hA
      bottomDiffCont bottomSphereBound⟩

theorem CanonicalScheduledZetaSideCauchyPathData.top_bound
    {f : ZetaAdmissibleFunction} {K : ℕ}
    (data : CanonicalScheduledZetaSideCauchyPathData f K) :
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
    zetaSideNegLogDeriv_path_bound_of_cauchyLogDerivative
      (zetaCompletedExplicitFormulaTopPath
        ((zetaCompletedExplicitFormula_autocorrelation_contourFamily f).rectangle
          ((zetaCompletedExplicitFormulaAutocorrelationCofinalHeightSchedule f).height u))
        x)
      K
      ((zetaCompletedExplicitFormulaAutocorrelationCofinalHeightSchedule f).height u)
      data.radius
      data.amplitude
      data.valueLower
      data.radius_pos
      data.valueLower_pos
      (data.top_diffCont u x hx)
      (data.top_sphereBound u x hx)
      (data.top_valueLower u x hx)

theorem CanonicalScheduledZetaSideCauchyPathData.bottom_bound
    {f : ZetaAdmissibleFunction} {K : ℕ}
    (data : CanonicalScheduledZetaSideCauchyPathData f K) :
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
    zetaSideNegLogDeriv_path_bound_of_cauchyLogDerivative
      (zetaCompletedExplicitFormulaBottomPath
        ((zetaCompletedExplicitFormula_autocorrelation_contourFamily f).rectangle
          ((zetaCompletedExplicitFormulaAutocorrelationCofinalHeightSchedule f).height u))
        x)
      K
      ((zetaCompletedExplicitFormulaAutocorrelationCofinalHeightSchedule f).height u)
      data.radius
      data.amplitude
      data.valueLower
      data.radius_pos
      data.valueLower_pos
      (data.bottom_diffCont u x hx)
      (data.bottom_sphereBound u x hx)
      (data.bottom_valueLower u x hx)

theorem CanonicalScheduledInverseGammaCauchyPathData.top_bound
    {f : ZetaAdmissibleFunction} {K : ℕ}
    (data : CanonicalScheduledInverseGammaCauchyPathData f K) :
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
    inverseGammaLogDeriv_path_bound_of_cauchyLogDerivative
      (zetaCompletedExplicitFormulaTopPath
        ((zetaCompletedExplicitFormula_autocorrelation_contourFamily f).rectangle
          ((zetaCompletedExplicitFormulaAutocorrelationCofinalHeightSchedule f).height u))
        x)
      K
      ((zetaCompletedExplicitFormulaAutocorrelationCofinalHeightSchedule f).height u)
      data.radius
      data.amplitude
      data.valueLower
      data.radius_pos
      data.valueLower_pos
      (data.top_diffCont u x hx)
      (data.top_sphereBound u x hx)
      (data.top_valueLower u x hx)

theorem CanonicalScheduledInverseGammaCauchyPathData.bottom_bound
    {f : ZetaAdmissibleFunction} {K : ℕ}
    (data : CanonicalScheduledInverseGammaCauchyPathData f K) :
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
    inverseGammaLogDeriv_path_bound_of_cauchyLogDerivative
      (zetaCompletedExplicitFormulaBottomPath
        ((zetaCompletedExplicitFormula_autocorrelation_contourFamily f).rectangle
          ((zetaCompletedExplicitFormulaAutocorrelationCofinalHeightSchedule f).height u))
        x)
      K
      ((zetaCompletedExplicitFormulaAutocorrelationCofinalHeightSchedule f).height u)
      data.radius
      data.amplitude
      data.valueLower
      data.radius_pos
      data.valueLower_pos
      (data.bottom_diffCont u x hx)
      (data.bottom_sphereBound u x hx)
      (data.bottom_valueLower u x hx)

def zetaCompletedExplicitFormulaAutocorrelationScheduledPolynomialFamilyAnalyticPackage_of_factorPathBounds
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
    ExplicitFormulaScheduledPolynomialFamilyAnalyticPackage
      (convolutionAutocorrelation f)
      (zetaCompletedExplicitFormula_autocorrelation_contourFamily f) :=
  let carrier : CompletedZetaZeroExcisedStrip
      (min (zetaCompletedExplicitFormula_autocorrelation_contourFamily f).c
        (1 - (zetaCompletedExplicitFormula_autocorrelation_contourFamily f).c))
      (max (zetaCompletedExplicitFormula_autocorrelation_contourFamily f).c
        (1 - (zetaCompletedExplicitFormula_autocorrelation_contourFamily f).c)) :=
    zetaCompletedExplicitFormulaAutocorrelationScheduledHorizontalCarrier f
  let zetaCarrierBound :
      ∀ z : ℂ,
        z ∈ carrier.carrier →
        ‖zetaSideNegLogDeriv z‖ ≤
          Czeta * (1 + ‖z.im‖) ^ K :=
    zetaCompletedExplicitFormulaAutocorrelationScheduledHorizontalCarrier_norm_bound_of_pathBounds
      f zetaSideNegLogDeriv K Czeta topZetaBound bottomZetaBound
  let gammaCarrierBound :
      ∀ z : ℂ,
        z ∈ carrier.carrier →
        ‖deriv (fun w : ℂ => (Complex.Gammaℝ w)⁻¹) z /
            (Complex.Gammaℝ z)⁻¹‖ ≤
          Cgamma * (1 + ‖z.im‖) ^ K :=
    zetaCompletedExplicitFormulaAutocorrelationScheduledHorizontalCarrier_norm_bound_of_pathBounds
      f
      (fun z : ℂ =>
        deriv (fun w : ℂ => (Complex.Gammaℝ w)⁻¹) z /
          (Complex.Gammaℝ z)⁻¹)
      K Cgamma topGammaBound bottomGammaBound
  let completedCarrierBound :
      ∀ z : ℂ,
        z ∈ carrier.carrier →
        ‖completedZetaNegLogDeriv z‖ ≤
          (Czeta + Cgamma) * (1 + ‖z.im‖) ^ K :=
    fun z hz =>
      completedZetaNegLogDeriv_bound_of_concrete_zetaSide_and_gamma
        (min (zetaCompletedExplicitFormula_autocorrelation_contourFamily f).c
          (1 - (zetaCompletedExplicitFormula_autocorrelation_contourFamily f).c))
        (max (zetaCompletedExplicitFormula_autocorrelation_contourFamily f).c
          (1 - (zetaCompletedExplicitFormula_autocorrelation_contourFamily f).c))
        carrier K Czeta Cgamma zetaCarrierBound gammaCarrierBound z hz
  { phi_control :=
      (zetaPhiAnalyticControl_autocorrelation_of_concreteControl
        zetaPhiAutocorrelationConcreteControl_owner) f
    height_schedule :=
      zetaCompletedExplicitFormulaAutocorrelationCofinalHeightSchedule f
    horizontal_logderiv_control :=
      { carrier := carrier
        top_mem :=
          zetaCompletedExplicitFormulaAutocorrelationScheduledHorizontalCarrier_top_mem
            f
        bottom_mem :=
          zetaCompletedExplicitFormulaAutocorrelationScheduledHorizontalCarrier_bottom_mem
            f
        growth_degree := K
        bound_constant := Czeta + Cgamma
        bound_constant_pos := add_pos Czeta_pos Cgamma_pos
        bound := completedCarrierBound } }

def zetaCompletedExplicitFormulaAutocorrelationScheduledPolynomialFamilyAnalyticPackage_of_cauchyPathData
    (f : ZetaAdmissibleFunction) (K : ℕ)
    (zetaData : CanonicalScheduledZetaSideCauchyPathData f K)
    (gammaData : CanonicalScheduledInverseGammaCauchyPathData f K) :
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

theorem norm_mul_le_polynomialExponential_product_owner
    {x y A₁ A₂ B₁ B₂ H : ℝ} {m : ℕ}
    (hy : 0 ≤ y)
    (hA₁ : 0 ≤ A₁)
    (h₁ : x ≤ A₁ * Real.exp (B₁ * H ^ m))
    (h₂ : y ≤ A₂ * Real.exp (B₂ * H ^ m)) :
    x * y ≤ (A₁ * A₂) * Real.exp ((B₁ + B₂) * H ^ m) := by
  have hright₁ : 0 ≤ A₁ * Real.exp (B₁ * H ^ m) :=
    mul_nonneg hA₁ (le_of_lt (Real.exp_pos _))
  have hmul := mul_le_mul h₁ h₂ hy hright₁
  exact hmul.trans_eq (by
    calc
      (A₁ * Real.exp (B₁ * H ^ m)) *
          (A₂ * Real.exp (B₂ * H ^ m)) =
          (A₁ * A₂) *
            (Real.exp (B₁ * H ^ m) * Real.exp (B₂ * H ^ m) : ℝ) := by
              exact mul_mul_mul_comm A₁ (Real.exp (B₁ * H ^ m)) A₂
                (Real.exp (B₂ * H ^ m))
      _ = (A₁ * A₂) * Real.exp ((B₁ + B₂) * H ^ m) := by
        exact congrArg (fun t : ℝ => (A₁ * A₂) * t)
          (Eq.trans (Real.exp_add (B₁ * H ^ m) (B₂ * H ^ m)).symm
            (congrArg Real.exp
              (add_mul B₁ B₂ (H ^ m)).symm))

theorem zetaSideFactor_norm_le_polynomialExponential_product_owner
    (P : ℂ → Prop) (A₁ A₂ B₁ B₂ H : ℝ) (m : ℕ)
    (hA₁ : 0 ≤ A₁) (hy : ∀ w : ℂ, P w → 0 ≤ ‖(Complex.Gammaℝ w)⁻¹‖)
    (hζ : ∀ w : ℂ, P w →
      ‖completedRiemannZeta w‖ ≤ A₁ * Real.exp (B₁ * H ^ m))
    (hΓ : ∀ w : ℂ, P w →
      ‖(Complex.Gammaℝ w)⁻¹‖ ≤ A₂ * Real.exp (B₂ * H ^ m)) :
    ∀ w : ℂ, P w →
      ‖zetaSideFactor w‖ ≤ A₁ * A₂ * Real.exp ((B₁ + B₂) * H ^ m) := by
  intro w hw
  calc
    ‖zetaSideFactor w‖ =
        ‖completedRiemannZeta w * (Complex.Gammaℝ w)⁻¹‖ := by
      exact congrArg norm (zetaSideFactor_eq w)
    _ = ‖completedRiemannZeta w‖ * ‖(Complex.Gammaℝ w)⁻¹‖ :=
      norm_mul _ _
    _ ≤ A₁ * A₂ * Real.exp ((B₁ + B₂) * H ^ m) :=
      norm_mul_le_polynomialExponential_product_owner
        (hy w hw)
        hA₁
        (hζ w hw)
        (hΓ w hw)

theorem zetaSideFactor_norm_le_polynomialExponential_of_component_global_bounds_owner
    (P : ℂ → Prop) (A₁ A₂ B₁ B₂ : ℝ) (m : ℕ)
    (hA₁ : 0 ≤ A₁)
    (hy : ∀ w : ℂ, P w → 0 ≤ ‖(Complex.Gammaℝ w)⁻¹‖)
    (hζ : ∀ w : ℂ, P w →
      ‖completedRiemannZeta w‖ ≤
        A₁ * Real.exp (B₁ * (1 + ‖w‖) ^ m))
    (hΓ : ∀ w : ℂ, P w →
      ‖(Complex.Gammaℝ w)⁻¹‖ ≤
        A₂ * Real.exp (B₂ * (1 + ‖w‖) ^ m)) :
    ∀ w : ℂ, P w →
      ‖zetaSideFactor w‖ ≤
        A₁ * A₂ * Real.exp ((B₁ + B₂) * (1 + ‖w‖) ^ m) := by
  intro w hw
  exact zetaSideFactor_norm_le_polynomialExponential_product_owner
    P A₁ A₂ B₁ B₂ (1 + ‖w‖) m hA₁ (hy w hw) (hζ w hw) (hΓ w hw)

theorem zetaSideFactor_norm_le_polynomialExponential_of_component_global_bounds_canonical_owner
    (P : ℂ → Prop) (A₁ A₂ B₁ B₂ : ℝ) (m : ℕ)
    (hA₁ : 0 ≤ A₁)
    (hζ : ∀ w : ℂ, P w →
      ‖completedRiemannZeta w‖ ≤
        A₁ * Real.exp (B₁ * (1 + ‖w‖) ^ m))
    (hΓ : ∀ w : ℂ, P w →
      ‖(Complex.Gammaℝ w)⁻¹‖ ≤
        A₂ * Real.exp (B₂ * (1 + ‖w‖) ^ m)) :
    ∀ w : ℂ, P w →
      ‖zetaSideFactor w‖ ≤
        A₁ * A₂ * Real.exp ((B₁ + B₂) * (1 + ‖w‖) ^ m) := by
  exact zetaSideFactor_norm_le_polynomialExponential_of_component_global_bounds_owner
    P A₁ A₂ B₁ B₂ m hA₁
    (fun w hw => norm_nonneg ((Complex.Gammaℝ w)⁻¹))
    hζ hΓ

theorem zetaSideFactor_norm_le_polynomialExponential_on_zero_one_strip_owner
    (A₁ A₂ B₁ B₂ : ℝ) (m : ℕ) (hA₁ : 0 ≤ A₁)
    (hζ : ∀ w : ℂ, 0 ≤ w.re → w.re ≤ 1 →
      ‖completedRiemannZeta w‖ ≤
        A₁ * Real.exp (B₁ * (1 + ‖w‖) ^ m))
    (hΓ : ∀ w : ℂ, 0 ≤ w.re → w.re ≤ 1 →
      ‖(Complex.Gammaℝ w)⁻¹‖ ≤
        A₂ * Real.exp (B₂ * (1 + ‖w‖) ^ m)) :
    ∀ w : ℂ, 0 ≤ w.re → w.re ≤ 1 →
      ‖zetaSideFactor w‖ ≤
        A₁ * A₂ * Real.exp ((B₁ + B₂) * (1 + ‖w‖) ^ m) := by
  intro w hw_lower hw_upper
  exact zetaSideFactor_norm_le_polynomialExponential_of_component_global_bounds_owner
    (fun z : ℂ => 0 ≤ z.re ∧ z.re ≤ 1)
    A₁ A₂ B₁ B₂ m hA₁
    (fun z hz => norm_nonneg ((Complex.Gammaℝ z)⁻¹))
    (fun z hz => hζ z hz.1 hz.2)
    (fun z hz => hΓ z hz.1 hz.2)
    w ⟨hw_lower, hw_upper⟩

theorem zetaSideFactor_norm_le_polynomialExponential_on_zero_one_strip_canonical_owner
    (A₁ A₂ B₁ B₂ : ℝ) (m : ℕ) (hA₁ : 0 ≤ A₁)
    (hζ : ∀ w : ℂ, 0 ≤ w.re → w.re ≤ 1 →
      ‖completedRiemannZeta w‖ ≤
        A₁ * Real.exp (B₁ * (1 + ‖w‖) ^ m))
    (hΓ : ∀ w : ℂ, 0 ≤ w.re → w.re ≤ 1 →
      ‖(Complex.Gammaℝ w)⁻¹‖ ≤
        A₂ * Real.exp (B₂ * (1 + ‖w‖) ^ m)) :
    ∀ w : ℂ, 0 ≤ w.re → w.re ≤ 1 →
      ‖zetaSideFactor w‖ ≤
        A₁ * A₂ * Real.exp ((B₁ + B₂) * (1 + ‖w‖) ^ m) := by
  exact zetaSideFactor_norm_le_polynomialExponential_of_component_global_bounds_canonical_owner
    (fun w : ℂ => 0 ≤ w.re ∧ w.re ≤ 1)
    A₁ A₂ B₁ B₂ m hA₁
    (fun w hw => hζ w hw.1 hw.2)
    (fun w hw => hΓ w hw.1 hw.2)

theorem horizontalPaths_zetaSideFactor_sphere_bounds_of_component_global_envelopes_owner
    (x T R height : ℝ) (m : ℕ) (A₁ A₂ B₁ B₂ : ℝ)
    (hA₁ : 0 ≤ A₁) (hA₂ : 0 ≤ A₂)
    (hB₁ : 0 ≤ B₁) (hB₂ : 0 ≤ B₂)
    (hR : 0 ≤ R) (hx_lower : R ≤ x) (hx_upper : x + R ≤ 1)
    (topHeight : ‖((x : ℂ) + (T : ℂ) * Complex.I)‖ + R ≤ ‖height‖)
    (bottomHeight : ‖((x : ℂ) - (T : ℂ) * Complex.I)‖ + R ≤ ‖height‖)
    (hζ : ∀ w : ℂ, 0 ≤ w.re → w.re ≤ 1 →
      ‖completedRiemannZeta w‖ ≤
        A₁ * Real.exp (B₁ * (1 + ‖w‖) ^ m))
    (hΓ : ∀ w : ℂ, 0 ≤ w.re → w.re ≤ 1 →
      ‖(Complex.Gammaℝ w)⁻¹‖ ≤
        A₂ * Real.exp (B₂ * (1 + ‖w‖) ^ m)) :
    (∀ w : ℂ, w ∈ Metric.sphere ((x : ℂ) + (T : ℂ) * Complex.I) R →
      ‖zetaSideFactor w‖ ≤
        A₁ * A₂ * Real.exp ((B₁ + B₂) * (1 + ‖height‖) ^ m)) ∧
    (∀ w : ℂ, w ∈ Metric.sphere ((x : ℂ) - (T : ℂ) * Complex.I) R →
      ‖zetaSideFactor w‖ ≤
        A₁ * A₂ * Real.exp ((B₁ + B₂) * (1 + ‖height‖) ^ m)) := by
  exact horizontalPaths_zetaSideFactor_sphere_bounds_of_geometry
    x T R height m (A₁ * A₂) (B₁ + B₂)
    (mul_nonneg hA₁ hA₂)
    (add_nonneg hB₁ hB₂)
    hR hx_lower hx_upper topHeight bottomHeight
    (fun w hw_lower hw_upper =>
      zetaSideFactor_norm_le_polynomialExponential_on_zero_one_strip_canonical_owner
        A₁ A₂ B₁ B₂ m hA₁ hζ hΓ w hw_lower hw_upper)

theorem horizontalPaths_zetaSideFactor_sphere_bounds_of_component_global_envelopes_canonical_owner
    (x T R height : ℝ) (m : ℕ) (A₁ A₂ B₁ B₂ : ℝ)
    (hA₁ : 0 ≤ A₁) (hA₂ : 0 ≤ A₂)
    (hB₁ : 0 ≤ B₁) (hB₂ : 0 ≤ B₂)
    (hR : 0 ≤ R) (hx_lower : R ≤ x) (hx_upper : x + R ≤ 1)
    (topHeight : ‖((x : ℂ) + (T : ℂ) * Complex.I)‖ + R ≤ ‖height‖)
    (bottomHeight : ‖((x : ℂ) - (T : ℂ) * Complex.I)‖ + R ≤ ‖height‖)
    (hζ : ∀ w : ℂ, 0 ≤ w.re → w.re ≤ 1 →
      ‖completedRiemannZeta w‖ ≤
        A₁ * Real.exp (B₁ * (1 + ‖w‖) ^ m))
    (hΓ : ∀ w : ℂ, 0 ≤ w.re → w.re ≤ 1 →
      ‖(Complex.Gammaℝ w)⁻¹‖ ≤
        A₂ * Real.exp (B₂ * (1 + ‖w‖) ^ m)) :
    (∀ w : ℂ, w ∈ Metric.sphere ((x : ℂ) + (T : ℂ) * Complex.I) R →
      ‖zetaSideFactor w‖ ≤
        A₁ * A₂ * Real.exp ((B₁ + B₂) * (1 + ‖height‖) ^ m)) ∧
    (∀ w : ℂ, w ∈ Metric.sphere ((x : ℂ) - (T : ℂ) * Complex.I) R →
      ‖zetaSideFactor w‖ ≤
        A₁ * A₂ * Real.exp ((B₁ + B₂) * (1 + ‖height‖) ^ m)) := by
  exact horizontalPaths_zetaSideFactor_sphere_bounds_of_component_global_envelopes_owner
    x T R height m A₁ A₂ B₁ B₂ hA₁ hA₂ hB₁ hB₂ hR hx_lower hx_upper
    topHeight bottomHeight
    hζ hΓ

theorem horizontalPaths_inverseGamma_sphere_bounds_of_global_envelope_owner
    (x T R height : ℝ) (m : ℕ) (A B : ℝ)
    (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hR : 0 ≤ R) (hx_lower : R ≤ x) (hx_upper : x + R ≤ 1)
    (topHeight : ‖((x : ℂ) + (T : ℂ) * Complex.I)‖ + R ≤ ‖height‖)
    (bottomHeight : ‖((x : ℂ) - (T : ℂ) * Complex.I)‖ + R ≤ ‖height‖)
    (globalEnvelope : ∀ w : ℂ, 0 ≤ w.re → w.re ≤ 1 →
      ‖(Complex.Gammaℝ w)⁻¹‖ ≤ A * Real.exp (B * (1 + ‖w‖) ^ m)) :
    (∀ w : ℂ, w ∈ Metric.sphere ((x : ℂ) + (T : ℂ) * Complex.I) R →
      ‖(Complex.Gammaℝ w)⁻¹‖ ≤ A * Real.exp (B * (1 + ‖height‖) ^ m)) ∧
    (∀ w : ℂ, w ∈ Metric.sphere ((x : ℂ) - (T : ℂ) * Complex.I) R →
      ‖(Complex.Gammaℝ w)⁻¹‖ ≤ A * Real.exp (B * (1 + ‖height‖) ^ m)) :=
  horizontalPaths_inverseGamma_sphere_bounds_of_geometry
    x T R height m A B hA hB hR hx_lower hx_upper topHeight bottomHeight
      globalEnvelope

theorem horizontalPaths_inverseGamma_logDeriv_bounds_of_global_envelope_owner
    (x T R height : ℝ) (m : ℕ) (A B δTop δBottom : ℝ)
    (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hR : 0 < R) (hδTop : 0 < δTop) (hδBottom : 0 < δBottom)
    (hx_lower : R ≤ x) (hx_upper : x + R ≤ 1)
    (topHeight : ‖((x : ℂ) + (T : ℂ) * Complex.I)‖ + R ≤ ‖height‖)
    (bottomHeight : ‖((x : ℂ) - (T : ℂ) * Complex.I)‖ + R ≤ ‖height‖)
    (topDiffCont :
      DiffContOnCl ℂ
        (fun w : ℂ => (Complex.Gammaℝ w)⁻¹)
        (Metric.ball ((x : ℂ) + (T : ℂ) * Complex.I) R))
    (bottomDiffCont :
      DiffContOnCl ℂ
        (fun w : ℂ => (Complex.Gammaℝ w)⁻¹)
        (Metric.ball ((x : ℂ) - (T : ℂ) * Complex.I) R))
    (globalEnvelope : ∀ w : ℂ, 0 ≤ w.re → w.re ≤ 1 →
      ‖(Complex.Gammaℝ w)⁻¹‖ ≤ A * Real.exp (B * (1 + ‖w‖) ^ m))
    (topValueLower :
      δTop ≤ ‖(Complex.Gammaℝ ((x : ℂ) + (T : ℂ) * Complex.I))⁻¹‖)
    (bottomValueLower :
      δBottom ≤ ‖(Complex.Gammaℝ ((x : ℂ) - (T : ℂ) * Complex.I))⁻¹‖) :
    (‖deriv (fun w : ℂ => (Complex.Gammaℝ w)⁻¹)
        ((x : ℂ) + (T : ℂ) * Complex.I) /
        (Complex.Gammaℝ ((x : ℂ) + (T : ℂ) * Complex.I))⁻¹‖ ≤
      ((A / R) / δTop) * Real.exp (B * (1 + ‖height‖) ^ m)) ∧
    (‖deriv (fun w : ℂ => (Complex.Gammaℝ w)⁻¹)
        ((x : ℂ) - (T : ℂ) * Complex.I) /
        (Complex.Gammaℝ ((x : ℂ) - (T : ℂ) * Complex.I))⁻¹‖ ≤
      ((A / R) / δBottom) * Real.exp (B * (1 + ‖height‖) ^ m)) := by
  have hSphere := horizontalPaths_inverseGamma_sphere_bounds_of_geometry
    x T R height m A B hA hB (le_of_lt hR) hx_lower hx_upper
      topHeight bottomHeight globalEnvelope
  exact ⟨
    inverseGammaLogDeriv_path_bound_of_exponential_sphere_bound
      ((x : ℂ) + (T : ℂ) * Complex.I) m height R A B δTop hR hδTop
      topDiffCont hSphere.1 topValueLower,
    inverseGammaLogDeriv_path_bound_of_exponential_sphere_bound
      ((x : ℂ) - (T : ℂ) * Complex.I) m height R A B δBottom hR hδBottom
      bottomDiffCont hSphere.2 bottomValueLower⟩

end ZetaAdmissibleFunction

end
end LFunctions
end Boundary
