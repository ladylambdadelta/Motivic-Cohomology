import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaExplicitFormulaVerticalChannels.OwnerParts.PrimeLeftReflectedTermKernelAlgebra
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaExplicitFormulaVerticalChannels.OwnerParts.AffineCauchyKernelBounds
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaExplicitFormulaVerticalChannels.OwnerParts.ArchimedeanGammaBinetLineCore

/-!
# Reflected inverse-Gamma component integrability

This file is downstream of both the reflected prime kernel algebra and the
Gamma/Binet line estimates.  It supplies the reflected correction and
archimedean integrability facts needed before the reflected inverse-Gamma
scalar value can be evaluated.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open Complex
open LSeries ArithmeticFunction
open MeasureTheory
open scoped ArithmeticFunction

namespace ZetaAdmissibleFunction

/-- Reflected zero-pole correction kernel in the left reflected inverse-Gamma
component.

The pole is evaluated on the reflected right affine line, while the test
transform remains on the left-centered line. -/
noncomputable def zetaCompletedExplicitFormulaPrimeLeftReflectedCorrectionZeroPoleKernel
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (t : ℝ) : ℂ :=
  (1 / zetaCompletedExplicitFormulaRightAffineLine F (-t)) *
    zetaCompletedExplicitFormulaPhi f
      (zetaCompletedExplicitFormulaLeftCenteredAffineLine F t)

/-- Reflected one-pole correction kernel in the left reflected inverse-Gamma
component. -/
noncomputable def zetaCompletedExplicitFormulaPrimeLeftReflectedCorrectionOnePoleKernel
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (t : ℝ) : ℂ :=
  (1 / (zetaCompletedExplicitFormulaRightAffineLine F (-t) - 1)) *
    zetaCompletedExplicitFormulaPhi f
      (zetaCompletedExplicitFormulaLeftCenteredAffineLine F t)

/-- Strong measurability of the reflected zero-pole factor. -/
theorem zetaCompletedExplicitFormulaPrimeLeftReflectedCorrectionZeroPoleFactor_aestronglyMeasurable
    (F : ExplicitFormulaContourFamily) :
    AEStronglyMeasurable
      (fun t : ℝ => 1 / zetaCompletedExplicitFormulaRightAffineLine F (-t))
      (volume : Measure ℝ) := by
  have hline :
      Measurable
        (fun t : ℝ => zetaCompletedExplicitFormulaRightAffineLine F (-t)) :=
    ((zetaCompletedExplicitFormulaRightAffineLine_continuous F).comp
      continuous_neg).measurable
  exact (measurable_const.div hline).aestronglyMeasurable

/-- Strong measurability of the reflected one-pole factor. -/
theorem zetaCompletedExplicitFormulaPrimeLeftReflectedCorrectionOnePoleFactor_aestronglyMeasurable
    (F : ExplicitFormulaContourFamily) :
    AEStronglyMeasurable
      (fun t : ℝ =>
        1 / (zetaCompletedExplicitFormulaRightAffineLine F (-t) - 1))
      (volume : Measure ℝ) := by
  have hline :
      Measurable
        (fun t : ℝ => zetaCompletedExplicitFormulaRightAffineLine F (-t)) :=
    ((zetaCompletedExplicitFormulaRightAffineLine_continuous F).comp
      continuous_neg).measurable
  exact (measurable_const.div (hline.sub measurable_const)).aestronglyMeasurable

/-- Uniform linear bound for the reflected zero-pole factor. -/
theorem zetaCompletedExplicitFormulaPrimeLeftReflectedCorrectionZeroPoleFactor_linear_bound
    (F : ExplicitFormulaContourFamily) :
    ∀ t : ℝ,
      ‖1 / zetaCompletedExplicitFormulaRightAffineLine F (-t)‖ ≤
        ((1 : ℝ) / F.c) * (1 + ‖t‖) := by
  intro t
  have hcoeff :
      ‖-1 / zetaCompletedExplicitFormulaRightAffineLine F (-t)‖ ≤
        (1 : ℝ) / F.c :=
    zetaCompletedExplicitFormulaRightAffineLine_zeroPoleCoefficient_norm_le
      F (-t)
  have hnorm :
      ‖1 / zetaCompletedExplicitFormulaRightAffineLine F (-t)‖ =
        ‖-1 / zetaCompletedExplicitFormulaRightAffineLine F (-t)‖ := by
    let z : ℂ := zetaCompletedExplicitFormulaRightAffineLine F (-t)
    have hneg_div : -1 / z = -(1 / z) :=
      (neg_div z (1 : ℂ)).symm
    have hnorm_neg_div : ‖-1 / z‖ = ‖-(1 / z)‖ :=
      congrArg (fun w : ℂ => ‖w‖) hneg_div
    have hnorm_neg : ‖-(1 / z)‖ = ‖1 / z‖ :=
      norm_neg (1 / z)
    calc
      ‖1 / zetaCompletedExplicitFormulaRightAffineLine F (-t)‖ =
          ‖1 / z‖ := by
        rfl
      _ = ‖-(1 / z)‖ := by
        exact hnorm_neg.symm
      _ = ‖-1 / z‖ := by
        exact hnorm_neg_div.symm
      _ = ‖-1 / zetaCompletedExplicitFormulaRightAffineLine F (-t)‖ := by
        rfl
  have hscale :
      (1 : ℝ) / F.c ≤ ((1 : ℝ) / F.c) * (1 + ‖t‖) := by
    have hnonneg : 0 ≤ (1 : ℝ) / F.c :=
      div_nonneg zero_le_one F.c_pos.le
    have hone_le : 1 ≤ 1 + ‖t‖ :=
      Real.one_le_one_add_norm t
    exact
      Eq.subst
        (motive := fun x : ℝ => x ≤ ((1 : ℝ) / F.c) * (1 + ‖t‖))
        (mul_one ((1 : ℝ) / F.c)).symm
        (mul_le_mul_of_nonneg_left hone_le hnonneg)
  exact
    Eq.subst
      (motive := fun x : ℝ => x ≤ ((1 : ℝ) / F.c) * (1 + ‖t‖))
      hnorm.symm
      (hcoeff.trans hscale)

/-- Uniform linear bound for the reflected one-pole factor. -/
theorem zetaCompletedExplicitFormulaPrimeLeftReflectedCorrectionOnePoleFactor_linear_bound
    (F : ExplicitFormulaContourFamily) :
    ∀ t : ℝ,
      ‖1 / (zetaCompletedExplicitFormulaRightAffineLine F (-t) - 1)‖ ≤
        ((1 : ℝ) / (F.c - 1)) * (1 + ‖t‖) := by
  intro t
  have hcoeff :
      ‖-(1 / (zetaCompletedExplicitFormulaRightAffineLine F (-t) - 1))‖ ≤
        (1 : ℝ) / (F.c - 1) :=
    zetaCompletedExplicitFormulaRightAffineLine_onePoleCoefficient_norm_le
      F (-t)
  have hnorm :
      ‖1 / (zetaCompletedExplicitFormulaRightAffineLine F (-t) - 1)‖ =
        ‖-(1 / (zetaCompletedExplicitFormulaRightAffineLine F (-t) - 1))‖ := by
    exact
      (norm_neg
        (1 / (zetaCompletedExplicitFormulaRightAffineLine F (-t) - 1))).symm
  have hscale :
      (1 : ℝ) / (F.c - 1) ≤
        ((1 : ℝ) / (F.c - 1)) * (1 + ‖t‖) := by
    have hden_nonneg : 0 ≤ F.c - 1 :=
      (sub_pos.mpr F.c_gt_one).le
    have hnonneg : 0 ≤ (1 : ℝ) / (F.c - 1) :=
      div_nonneg zero_le_one hden_nonneg
    have hone_le : 1 ≤ 1 + ‖t‖ :=
      Real.one_le_one_add_norm t
    exact
      Eq.subst
        (motive := fun x : ℝ =>
          x ≤ ((1 : ℝ) / (F.c - 1)) * (1 + ‖t‖))
        (mul_one ((1 : ℝ) / (F.c - 1))).symm
        (mul_le_mul_of_nonneg_left hone_le hnonneg)
  exact
    Eq.subst
      (motive := fun x : ℝ =>
        x ≤ ((1 : ℝ) / (F.c - 1)) * (1 + ‖t‖))
      hnorm.symm
      (hcoeff.trans hscale)

/-- Majorant package for the reflected zero-pole correction kernel. -/
theorem zetaCompletedExplicitFormulaPrimeLeftReflectedCorrectionZeroPoleKernel_majorantPackage
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) :
    ExplicitFormulaAffineKernelMajorantPackage
      (zetaCompletedExplicitFormulaPrimeLeftReflectedCorrectionZeroPoleKernel
        f F) := by
  let A : ℝ → ℂ := fun t : ℝ =>
    1 / zetaCompletedExplicitFormulaRightAffineLine F (-t)
  let B : ℝ := (1 : ℝ) / F.c
  have hB_nonneg : 0 ≤ B :=
    div_nonneg zero_le_one F.c_pos.le
  have hpackage :
      ExplicitFormulaAffineKernelMajorantPackage
        (fun t : ℝ =>
          A t *
            zetaCompletedExplicitFormulaPhi f
              (zetaCompletedExplicitFormulaLeftCenteredAffineLine F t)) :=
    zetaCompletedExplicitFormulaLeftCenteredAffineProduct_majorantPackage_of_linear_factor_bound_common
      f F h A B hB_nonneg
      (zetaCompletedExplicitFormulaPrimeLeftReflectedCorrectionZeroPoleFactor_aestronglyMeasurable
        F)
      (zetaCompletedExplicitFormulaPrimeLeftReflectedCorrectionZeroPoleFactor_linear_bound
        F)
  have hfun :
      (fun t : ℝ =>
        A t *
          zetaCompletedExplicitFormulaPhi f
            (zetaCompletedExplicitFormulaLeftCenteredAffineLine F t)) =
        zetaCompletedExplicitFormulaPrimeLeftReflectedCorrectionZeroPoleKernel
          f F := by
    funext t
    exact Eq.refl _
  exact
    Eq.subst
      (motive := fun φ : ℝ → ℂ =>
        ExplicitFormulaAffineKernelMajorantPackage φ)
      hfun
      hpackage

/-- Integrability of the reflected zero-pole correction kernel. -/
theorem zetaCompletedExplicitFormulaPrimeLeftReflectedCorrectionZeroPoleKernel_integrable
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) :
    Integrable
      (zetaCompletedExplicitFormulaPrimeLeftReflectedCorrectionZeroPoleKernel
        f F)
      (volume : Measure ℝ) :=
  (zetaCompletedExplicitFormulaPrimeLeftReflectedCorrectionZeroPoleKernel_majorantPackage
    f F h).integrable

/-- Majorant package for the reflected one-pole correction kernel. -/
theorem zetaCompletedExplicitFormulaPrimeLeftReflectedCorrectionOnePoleKernel_majorantPackage
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) :
    ExplicitFormulaAffineKernelMajorantPackage
      (zetaCompletedExplicitFormulaPrimeLeftReflectedCorrectionOnePoleKernel
        f F) := by
  let A : ℝ → ℂ := fun t : ℝ =>
    1 / (zetaCompletedExplicitFormulaRightAffineLine F (-t) - 1)
  let B : ℝ := (1 : ℝ) / (F.c - 1)
  have hB_nonneg : 0 ≤ B :=
    div_nonneg zero_le_one (sub_pos.mpr F.c_gt_one).le
  have hpackage :
      ExplicitFormulaAffineKernelMajorantPackage
        (fun t : ℝ =>
          A t *
            zetaCompletedExplicitFormulaPhi f
              (zetaCompletedExplicitFormulaLeftCenteredAffineLine F t)) :=
    zetaCompletedExplicitFormulaLeftCenteredAffineProduct_majorantPackage_of_linear_factor_bound_common
      f F h A B hB_nonneg
      (zetaCompletedExplicitFormulaPrimeLeftReflectedCorrectionOnePoleFactor_aestronglyMeasurable
        F)
      (zetaCompletedExplicitFormulaPrimeLeftReflectedCorrectionOnePoleFactor_linear_bound
        F)
  have hfun :
      (fun t : ℝ =>
        A t *
          zetaCompletedExplicitFormulaPhi f
            (zetaCompletedExplicitFormulaLeftCenteredAffineLine F t)) =
        zetaCompletedExplicitFormulaPrimeLeftReflectedCorrectionOnePoleKernel
          f F := by
    funext t
    exact Eq.refl _
  exact
    Eq.subst
      (motive := fun φ : ℝ → ℂ =>
        ExplicitFormulaAffineKernelMajorantPackage φ)
      hfun
      hpackage

/-- Integrability of the reflected one-pole correction kernel. -/
theorem zetaCompletedExplicitFormulaPrimeLeftReflectedCorrectionOnePoleKernel_integrable
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) :
    Integrable
      (zetaCompletedExplicitFormulaPrimeLeftReflectedCorrectionOnePoleKernel
        f F)
      (volume : Measure ℝ) :=
  (zetaCompletedExplicitFormulaPrimeLeftReflectedCorrectionOnePoleKernel_majorantPackage
    f F h).integrable

/-- The reflected correction kernel splits into its zero-pole and one-pole
pieces. -/
theorem zetaCompletedExplicitFormulaPrimeLeftReflectedCorrectionKernel_eq_zeroPole_add_onePole
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (t : ℝ) :
    zetaCompletedExplicitFormulaPrimeLeftReflectedCorrectionKernel f F t =
      zetaCompletedExplicitFormulaPrimeLeftReflectedCorrectionZeroPoleKernel
          f F t +
        zetaCompletedExplicitFormulaPrimeLeftReflectedCorrectionOnePoleKernel
          f F t := by
  let s : ℂ := zetaCompletedExplicitFormulaRightAffineLine F (-t)
  let Φ : ℂ :=
    zetaCompletedExplicitFormulaPhi f
      (zetaCompletedExplicitFormulaLeftCenteredAffineLine F t)
  let Z : ℂ := 1 / s
  let Zneg : ℂ := (-1 : ℂ) / s
  let O : ℂ := 1 / (s - 1)
  let C : ℂ := explicitFormulaCorrectionLogDerivative s
  have hC : C = Zneg - O := by
    exact explicitFormulaCorrectionLogDerivative_eq_poleCorrection s
  have hZneg : -Zneg = Z := by
    calc
      -Zneg = -((-1 : ℂ) / s) := by
        rfl
      _ = -(-(1 / s)) := by
        exact congrArg Neg.neg ((neg_div s (1 : ℂ)).symm)
      _ = 1 / s := by
        exact neg_neg (1 / s)
      _ = Z := by
        rfl
  have hnegC : -C = Z + O := by
    calc
      -C = -(Zneg - O) := by
        exact congrArg Neg.neg hC
      _ = -Zneg + O := by
        exact neg_sub Zneg O
      _ = Z + O := by
        exact congrArg (fun z : ℂ => z + O) hZneg
  calc
    zetaCompletedExplicitFormulaPrimeLeftReflectedCorrectionKernel f F t =
        (-C) * Φ := by
      rfl
    _ = (Z + O) * Φ := by
      exact congrArg (fun z : ℂ => z * Φ) hnegC
    _ = Z * Φ + O * Φ := by
      exact add_mul Z O Φ
    _ =
        zetaCompletedExplicitFormulaPrimeLeftReflectedCorrectionZeroPoleKernel
            f F t +
          zetaCompletedExplicitFormulaPrimeLeftReflectedCorrectionOnePoleKernel
            f F t := by
      rfl

/-- Integral recombination for the reflected correction kernel from its
zero-pole and one-pole reflected pieces. -/
theorem zetaCompletedExplicitFormulaPrimeLeftReflectedCorrectionKernel_integral_eq_zeroPole_add_onePole_integrals
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (hzero :
      Integrable
        (zetaCompletedExplicitFormulaPrimeLeftReflectedCorrectionZeroPoleKernel
          f F)
        (volume : Measure ℝ))
    (hone :
      Integrable
        (zetaCompletedExplicitFormulaPrimeLeftReflectedCorrectionOnePoleKernel
          f F)
        (volume : Measure ℝ)) :
    (∫ t : ℝ,
      zetaCompletedExplicitFormulaPrimeLeftReflectedCorrectionKernel f F t) =
      (∫ t : ℝ,
        zetaCompletedExplicitFormulaPrimeLeftReflectedCorrectionZeroPoleKernel
          f F t) +
        ∫ t : ℝ,
          zetaCompletedExplicitFormulaPrimeLeftReflectedCorrectionOnePoleKernel
            f F t := by
  have hsum :
      (∫ t : ℝ,
        zetaCompletedExplicitFormulaPrimeLeftReflectedCorrectionZeroPoleKernel
            f F t +
          zetaCompletedExplicitFormulaPrimeLeftReflectedCorrectionOnePoleKernel
            f F t) =
        (∫ t : ℝ,
          zetaCompletedExplicitFormulaPrimeLeftReflectedCorrectionZeroPoleKernel
            f F t) +
          ∫ t : ℝ,
            zetaCompletedExplicitFormulaPrimeLeftReflectedCorrectionOnePoleKernel
              f F t :=
    integral_add hzero hone
  have hpoint :
      (fun t : ℝ =>
        zetaCompletedExplicitFormulaPrimeLeftReflectedCorrectionKernel f F t)
        =ᵐ[volume]
      fun t : ℝ =>
        zetaCompletedExplicitFormulaPrimeLeftReflectedCorrectionZeroPoleKernel
            f F t +
          zetaCompletedExplicitFormulaPrimeLeftReflectedCorrectionOnePoleKernel
            f F t :=
    Filter.Eventually.of_forall
      (fun t =>
        zetaCompletedExplicitFormulaPrimeLeftReflectedCorrectionKernel_eq_zeroPole_add_onePole
          f F t)
  calc
    (∫ t : ℝ,
      zetaCompletedExplicitFormulaPrimeLeftReflectedCorrectionKernel f F t) =
        ∫ t : ℝ,
          zetaCompletedExplicitFormulaPrimeLeftReflectedCorrectionZeroPoleKernel
              f F t +
            zetaCompletedExplicitFormulaPrimeLeftReflectedCorrectionOnePoleKernel
              f F t := by
      exact integral_congr_ae hpoint
    _ =
        (∫ t : ℝ,
          zetaCompletedExplicitFormulaPrimeLeftReflectedCorrectionZeroPoleKernel
            f F t) +
          ∫ t : ℝ,
            zetaCompletedExplicitFormulaPrimeLeftReflectedCorrectionOnePoleKernel
              f F t := by
      exact hsum

/-- Reflected correction scalar value from its reflected zero-pole and one-pole
component values.

This is scalar assembly only.  The two component values are the actual
Cauchy/Laplace inversion targets for the reflected correction branch. -/
theorem zetaCompletedExplicitFormulaPrimeLeftReflectedCorrectionKernel_integral_eq_standardResidue_of_zeroPole_onePole_values
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (hzero_int :
      Integrable
        (zetaCompletedExplicitFormulaPrimeLeftReflectedCorrectionZeroPoleKernel
          f F)
        (volume : Measure ℝ))
    (hone_int :
      Integrable
        (zetaCompletedExplicitFormulaPrimeLeftReflectedCorrectionOnePoleKernel
          f F)
        (volume : Measure ℝ))
    (hzero_value :
      (∫ t : ℝ,
        zetaCompletedExplicitFormulaPrimeLeftReflectedCorrectionZeroPoleKernel
          f F t) =
        0)
    (hone_value :
      (∫ t : ℝ,
        zetaCompletedExplicitFormulaPrimeLeftReflectedCorrectionOnePoleKernel
          f F t) =
        (((2 * (Real.pi : ℂ) * Complex.I) *
          (-zetaCompletedExplicitFormulaPhi f (1 / 2))) * Complex.I)) :
    (∫ t : ℝ,
      zetaCompletedExplicitFormulaPrimeLeftReflectedCorrectionKernel f F t) =
        (((2 * (Real.pi : ℂ) * Complex.I) *
          (-zetaCompletedExplicitFormulaPhi f (1 / 2))) * Complex.I) := by
  let B : ℂ :=
    (((2 * (Real.pi : ℂ) * Complex.I) *
      (-zetaCompletedExplicitFormulaPhi f (1 / 2))) * Complex.I)
  have hsum :
      (∫ t : ℝ,
        zetaCompletedExplicitFormulaPrimeLeftReflectedCorrectionKernel f F t) =
        (∫ t : ℝ,
          zetaCompletedExplicitFormulaPrimeLeftReflectedCorrectionZeroPoleKernel
            f F t) +
          ∫ t : ℝ,
            zetaCompletedExplicitFormulaPrimeLeftReflectedCorrectionOnePoleKernel
              f F t :=
    zetaCompletedExplicitFormulaPrimeLeftReflectedCorrectionKernel_integral_eq_zeroPole_add_onePole_integrals
      f F hzero_int hone_int
  calc
    (∫ t : ℝ,
      zetaCompletedExplicitFormulaPrimeLeftReflectedCorrectionKernel f F t) =
        (∫ t : ℝ,
          zetaCompletedExplicitFormulaPrimeLeftReflectedCorrectionZeroPoleKernel
            f F t) +
          ∫ t : ℝ,
            zetaCompletedExplicitFormulaPrimeLeftReflectedCorrectionOnePoleKernel
              f F t := by
      exact hsum
    _ =
        0 +
          ∫ t : ℝ,
            zetaCompletedExplicitFormulaPrimeLeftReflectedCorrectionOnePoleKernel
              f F t := by
      exact congrArg
        (fun z : ℂ =>
          z +
            ∫ t : ℝ,
              zetaCompletedExplicitFormulaPrimeLeftReflectedCorrectionOnePoleKernel
                f F t)
        hzero_value
    _ = 0 + B := by
      exact congrArg (fun z : ℂ => 0 + z) hone_value
    _ = B := by
      exact zero_add B
    _ =
        (((2 * (Real.pi : ℂ) * Complex.I) *
          (-zetaCompletedExplicitFormulaPhi f (1 / 2))) * Complex.I) := by
      rfl

/-- Owner-component reflected correction scalar value from the two reflected
pole scalar values.  Integrability is supplied by the pole-factor majorants
above. -/
theorem zetaCompletedExplicitFormulaPrimeLeftReflectedCorrectionKernel_integral_eq_standardResidue_of_zeroPole_onePole_values_ownerComponents
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F)
    (hzero_value :
      (∫ t : ℝ,
        zetaCompletedExplicitFormulaPrimeLeftReflectedCorrectionZeroPoleKernel
          f F t) =
        0)
    (hone_value :
      (∫ t : ℝ,
        zetaCompletedExplicitFormulaPrimeLeftReflectedCorrectionOnePoleKernel
          f F t) =
        (((2 * (Real.pi : ℂ) * Complex.I) *
          (-zetaCompletedExplicitFormulaPhi f (1 / 2))) * Complex.I)) :
    (∫ t : ℝ,
      zetaCompletedExplicitFormulaPrimeLeftReflectedCorrectionKernel f F t) =
        (((2 * (Real.pi : ℂ) * Complex.I) *
          (-zetaCompletedExplicitFormulaPhi f (1 / 2))) * Complex.I) :=
  zetaCompletedExplicitFormulaPrimeLeftReflectedCorrectionKernel_integral_eq_standardResidue_of_zeroPole_onePole_values
    f F
    (zetaCompletedExplicitFormulaPrimeLeftReflectedCorrectionZeroPoleKernel_integrable
      f F h)
    (zetaCompletedExplicitFormulaPrimeLeftReflectedCorrectionOnePoleKernel_integrable
      f F h)
    hzero_value
    hone_value

/-- Strong measurability of the reflected right-line correction factor. -/
theorem zetaCompletedExplicitFormulaPrimeLeftReflectedCorrectionFactor_aestronglyMeasurable
    (F : ExplicitFormulaContourFamily) :
    AEStronglyMeasurable
      (fun t : ℝ =>
        -(explicitFormulaCorrectionLogDerivative
          (zetaCompletedExplicitFormulaRightAffineLine F (-t))))
      (volume : Measure ℝ) := by
  let line : ℝ → ℂ := fun t : ℝ =>
    zetaCompletedExplicitFormulaRightAffineLine F (-t)
  have hline : Measurable line :=
    ((zetaCompletedExplicitFormulaRightAffineLine_continuous F).comp
      continuous_neg).measurable
  have hzero :
      Measurable (fun t : ℝ => (-1 : ℂ) / line t) :=
    measurable_const.div hline
  have hone :
      Measurable (fun t : ℝ => (1 : ℂ) / (line t - 1)) :=
    measurable_const.div (hline.sub measurable_const)
  have hpole :
      (fun t : ℝ =>
        explicitFormulaCorrectionLogDerivative (line t)) =
        fun t : ℝ => (-1 : ℂ) / line t - (1 : ℂ) / (line t - 1) := by
    funext t
    exact explicitFormulaCorrectionLogDerivative_eq_poleCorrection (line t)
  have hmeas :
      Measurable
        (fun t : ℝ => (-1 : ℂ) / line t - (1 : ℂ) / (line t - 1)) :=
    hzero.sub hone
  have hraw :
      AEStronglyMeasurable
        (fun t : ℝ =>
          explicitFormulaCorrectionLogDerivative (line t))
        (volume : Measure ℝ) :=
    Eq.subst
      (motive := fun φ : ℝ → ℂ =>
        AEStronglyMeasurable φ (volume : Measure ℝ))
      hpole.symm
      hmeas.aestronglyMeasurable
  exact hraw.neg

/-- Reflected correction-kernel majorant from the right-line correction
linear bound. -/
theorem zetaCompletedExplicitFormulaPrimeLeftReflectedCorrectionKernel_majorantPackage_ownerComponents
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) :
    ExplicitFormulaAffineKernelMajorantPackage
      (zetaCompletedExplicitFormulaPrimeLeftReflectedCorrectionKernel
        f F) := by
  let B : ℝ := (1 : ℝ) / F.c + (1 : ℝ) / (F.c - 1)
  have hB_nonneg : 0 ≤ B := by
    exact add_nonneg
      (div_nonneg zero_le_one F.c_pos.le)
      (div_nonneg zero_le_one (sub_pos.mpr F.c_gt_one).le)
  exact
    zetaCompletedExplicitFormulaPrimeLeftReflectedCorrectionKernel_majorantPackage_of_right_factor_bound
      f F h B hB_nonneg
      (zetaCompletedExplicitFormulaPrimeLeftReflectedCorrectionFactor_aestronglyMeasurable
        F)
      (zetaCompletedExplicitFormulaCorrectionLogDerivative_rightAffineLine_linear_bound
        F)

/-- Integrability of the reflected correction kernel from the Gamma/Binet
line-core correction bound. -/
theorem zetaCompletedExplicitFormulaPrimeLeftReflectedCorrectionKernel_integrable_ownerComponents
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) :
    Integrable
      (zetaCompletedExplicitFormulaPrimeLeftReflectedCorrectionKernel
        f F)
      (volume : Measure ℝ) :=
  (zetaCompletedExplicitFormulaPrimeLeftReflectedCorrectionKernel_majorantPackage_ownerComponents
    f F h).integrable

/-- Integrability of the reflected archimedean kernel from the reflected
inverse-Gamma bound and the reflected correction bound. -/
theorem zetaCompletedExplicitFormulaPrimeLeftReflectedArchimedeanKernel_integrable_of_gammaBinetCoherence_ownerComponents
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F)
    (hcoh : Complex.gammaBinetPrincipalLogCoherence) :
    Integrable
      (zetaCompletedExplicitFormulaPrimeLeftReflectedArchimedeanKernel
        f F)
      (volume : Measure ℝ) :=
  zetaCompletedExplicitFormulaPrimeLeftReflectedArchimedeanKernel_integrable_of_inverseGamma_and_correction
    f F
    (zetaCompletedExplicitFormulaPrimeLeftReflectedInverseGammaKernel_integrable_of_gammaBinetCoherence
      f F h hcoh)
    (zetaCompletedExplicitFormulaPrimeLeftReflectedCorrectionKernel_integrable_ownerComponents
      f F h)

/-- Reflected inverse-Gamma whole-line integral decomposes into reflected
archimedean and correction whole-line integrals under Gamma/Binet coherence. -/
theorem zetaCompletedExplicitFormulaPrimeLeftReflectedInverseGammaKernel_integral_eq_archimedean_add_correction_integrals_of_gammaBinetCoherence
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F)
    (hcoh : Complex.gammaBinetPrincipalLogCoherence) :
    (∫ t : ℝ,
      zetaCompletedExplicitFormulaPrimeLeftReflectedInverseGammaKernel
        f F t) =
      (∫ t : ℝ,
        zetaCompletedExplicitFormulaPrimeLeftReflectedArchimedeanKernel
          f F t) +
        ∫ t : ℝ,
          zetaCompletedExplicitFormulaPrimeLeftReflectedCorrectionKernel
            f F t :=
  zetaCompletedExplicitFormulaPrimeLeftReflectedInverseGammaKernel_integral_eq_archimedean_add_correction_integrals
    f F
    (zetaCompletedExplicitFormulaPrimeLeftReflectedArchimedeanKernel_integrable_of_gammaBinetCoherence_ownerComponents
      f F h hcoh)
    (zetaCompletedExplicitFormulaPrimeLeftReflectedCorrectionKernel_integrable_ownerComponents
      f F h)

end ZetaAdmissibleFunction

end
end LFunctions
end Boundary
