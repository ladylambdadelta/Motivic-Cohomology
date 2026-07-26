import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaExplicitFormulaVerticalChannels.OwnerParts.PrimeLeftReflectedTermKernelAlgebra
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ClassicalAnalysis.GammaBinetStirling.LogDerivativeFiniteFormula
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaExplicitFormulaVerticalChannels.OwnerParts.AffineCauchyKernelBounds
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaExplicitFormulaVerticalChannels.OwnerParts.ArchimedeanGammaBinetLineCore
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaExplicitFormulaVerticalChannels.OwnerParts.ZeroPoleLeftOffPoleDecay
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaExplicitFormulaVerticalChannels.OwnerParts.OnePoleAffineInversionTransport

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

/-- The reflected one-pole correction residue scalar. -/
noncomputable def zetaCompletedExplicitFormulaPrimeLeftReflectedCorrectionResidue
    (f : ZetaAdmissibleFunction) : ℂ :=
  (((2 * (Real.pi : ℂ) * Complex.I) *
    (-zetaCompletedExplicitFormulaPhi f (1 / 2))) * Complex.I)

/-- The one-sided left inverse-Gamma scalar used in the reflected-left prime
component recombination. -/
noncomputable def zetaCompletedExplicitFormulaLeftOneSidedInverseGammaValue
    (f : ZetaAdmissibleFunction) : ℂ :=
  -(zetaCompletedExplicitFormulaPhi f 0) +
    zetaCompletedExplicitFormulaPrimeLeftReflectedCorrectionResidue f

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

/-- Scheduled rectangle integral of the reflected zero-pole correction
component. -/
noncomputable def zetaCompletedExplicitFormulaPrimeLeftReflectedCorrectionZeroPoleScheduled
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u : ℝ) : ℂ :=
  ∫ t in Set.Icc
      (-(F.rectangle (h.height_schedule.height u)).T)
      (F.rectangle (h.height_schedule.height u)).T,
    zetaCompletedExplicitFormulaPrimeLeftReflectedCorrectionZeroPoleKernel
      f F t

/-- Scheduled rectangle integral of the reflected one-pole correction
component. -/
noncomputable def zetaCompletedExplicitFormulaPrimeLeftReflectedCorrectionOnePoleScheduled
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u : ℝ) : ℂ :=
  ∫ t in Set.Icc
      (-(F.rectangle (h.height_schedule.height u)).T)
      (F.rectangle (h.height_schedule.height u)).T,
    zetaCompletedExplicitFormulaPrimeLeftReflectedCorrectionOnePoleKernel
      f F t

/-- Scheduled rectangle integral of the reflected inverse-Gamma component. -/
noncomputable def zetaCompletedExplicitFormulaPrimeLeftReflectedInverseGammaScheduled
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u : ℝ) : ℂ :=
  ∫ t in Set.Icc
      (-(F.rectangle (h.height_schedule.height u)).T)
      (F.rectangle (h.height_schedule.height u)).T,
    zetaCompletedExplicitFormulaPrimeLeftReflectedInverseGammaKernel
      f F t

/-- Under the left/right affine reflection, the reflected right zero-denominator
kernel is the ordinary left one-pole correction kernel. -/
theorem zetaCompletedExplicitFormulaPrimeLeftReflectedCorrectionZeroPoleKernel_eq_leftOnePoleAffineKernel
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (t : ℝ) :
    zetaCompletedExplicitFormulaPrimeLeftReflectedCorrectionZeroPoleKernel
        f F t =
      zetaCompletedExplicitFormulaCorrectionLeftOnePoleAffineKernel f F t := by
  let R : ℂ := zetaCompletedExplicitFormulaRightAffineLine F (-t)
  let L : ℂ := zetaCompletedExplicitFormulaLeftAffineLine F t
  let Φ : ℂ :=
    zetaCompletedExplicitFormulaPhi f
      (zetaCompletedExplicitFormulaLeftCenteredAffineLine F t)
  have hL : L = 1 - R :=
    zetaCompletedExplicitFormulaLeftAffineLine_eq_one_sub_rightAffineLine F t
  have hL_sub_one : L - 1 = -R := by
    calc
      L - 1 = (1 - R) - 1 := by
        exact congrArg (fun z : ℂ => z - 1) hL
      _ = (1 - R) + -(1 : ℂ) := by
        exact sub_eq_add_neg (1 - R) (1 : ℂ)
      _ = ((1 : ℂ) + -R) + -(1 : ℂ) := by
        exact congrArg (fun z : ℂ => z + -(1 : ℂ))
          (sub_eq_add_neg (1 : ℂ) R)
      _ = (1 : ℂ) + (-R + -(1 : ℂ)) := by
        exact add_assoc (1 : ℂ) (-R) (-(1 : ℂ))
      _ = (1 : ℂ) + (-(1 : ℂ) + -R) := by
        exact congrArg (fun z : ℂ => (1 : ℂ) + z)
          (add_comm (-R) (-(1 : ℂ)))
      _ = ((1 : ℂ) + -(1 : ℂ)) + -R := by
        exact (add_assoc (1 : ℂ) (-(1 : ℂ)) (-R)).symm
      _ = (0 : ℂ) + -R := by
        exact congrArg (fun z : ℂ => z + -R) (add_neg_cancel (1 : ℂ))
      _ = -R := by
        exact zero_add (-R)
  have hcoeff :
      1 / R = -(1 / (L - 1)) := by
    have hneg_div : 1 / (-R) = -(1 / R) :=
      one_div_neg R
    calc
      1 / R = -(-(1 / R)) := by
        exact (neg_neg (1 / R)).symm
      _ = -(1 / (-R)) := by
        exact congrArg Neg.neg hneg_div.symm
      _ = -(1 / (L - 1)) := by
        exact congrArg (fun z : ℂ => -(1 / z)) hL_sub_one.symm
  calc
    zetaCompletedExplicitFormulaPrimeLeftReflectedCorrectionZeroPoleKernel
        f F t =
        (1 / R) * Φ := by
      exact Eq.refl _
    _ = (-(1 / (L - 1))) * Φ := by
      exact congrArg (fun z : ℂ => z * Φ) hcoeff
    _ = zetaCompletedExplicitFormulaCorrectionLeftOnePoleAffineKernel f F t := by
      exact Eq.refl _

/-- Under the left/right affine reflection, the reflected right one-denominator
kernel is the ordinary left zero-pole correction kernel. -/
theorem zetaCompletedExplicitFormulaPrimeLeftReflectedCorrectionOnePoleKernel_eq_leftZeroPoleAffineKernel
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (t : ℝ) :
    zetaCompletedExplicitFormulaPrimeLeftReflectedCorrectionOnePoleKernel
        f F t =
      zetaCompletedExplicitFormulaCorrectionLeftZeroPoleAffineKernel f F t := by
  let R : ℂ := zetaCompletedExplicitFormulaRightAffineLine F (-t)
  let L : ℂ := zetaCompletedExplicitFormulaLeftAffineLine F t
  let Φ : ℂ :=
    zetaCompletedExplicitFormulaPhi f
      (zetaCompletedExplicitFormulaLeftCenteredAffineLine F t)
  have hL : L = 1 - R :=
    zetaCompletedExplicitFormulaLeftAffineLine_eq_one_sub_rightAffineLine F t
  have hR_sub_one : R - 1 = -L := by
    calc
      R - 1 = -(1 - R) := by
        exact sub_eq_neg_sub R (1 : ℂ)
      _ = -L := by
        exact congrArg Neg.neg hL.symm
  have hneg_div : -1 / L = -(1 / L) :=
    (neg_div L (1 : ℂ)).symm
  have hcoeff :
      1 / (R - 1) = -1 / L := by
    have hdiv_neg : 1 / (-L) = -(1 / L) :=
      one_div_neg L
    calc
      1 / (R - 1) = 1 / (-L) := by
        exact congrArg (fun z : ℂ => 1 / z) hR_sub_one
      _ = -(1 / L) := hdiv_neg
      _ = -1 / L := hneg_div.symm
  calc
    zetaCompletedExplicitFormulaPrimeLeftReflectedCorrectionOnePoleKernel
        f F t =
        (1 / (R - 1)) * Φ := by
      exact Eq.refl _
    _ = (-1 / L) * Φ := by
      exact congrArg (fun z : ℂ => z * Φ) hcoeff
    _ = zetaCompletedExplicitFormulaCorrectionLeftZeroPoleAffineKernel f F t := by
      exact Eq.refl _

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
        (((2 * (Real.pi : ℂ) * Complex.I) *
          (-zetaCompletedExplicitFormulaPhi f (1 / 2))) * Complex.I))
    (hone_value :
      (∫ t : ℝ,
        zetaCompletedExplicitFormulaPrimeLeftReflectedCorrectionOnePoleKernel
          f F t) =
        0) :
    (∫ t : ℝ,
      zetaCompletedExplicitFormulaPrimeLeftReflectedCorrectionKernel f F t) =
        (((2 * (Real.pi : ℂ) * Complex.I) *
          (-zetaCompletedExplicitFormulaPhi f (1 / 2))) * Complex.I) := by
  let B : ℂ :=
    zetaCompletedExplicitFormulaPrimeLeftReflectedCorrectionResidue f
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
        B +
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
    _ = B + 0 := by
      exact congrArg (fun z : ℂ => B + z) hone_value
    _ = B := by
      exact add_zero B
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
        (((2 * (Real.pi : ℂ) * Complex.I) *
          (-zetaCompletedExplicitFormulaPhi f (1 / 2))) * Complex.I))
    (hone_value :
      (∫ t : ℝ,
        zetaCompletedExplicitFormulaPrimeLeftReflectedCorrectionOnePoleKernel
          f F t) =
        0) :
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

/-- Owner scheduled reflected zero-pole correction value.

Because the denominator is pulled back from the reflected right line, the
right zero denominator is the ordinary left `s = 1` pole. -/
theorem zetaCompletedExplicitFormulaPrimeLeftReflectedCorrectionZeroPoleScheduled_tendsto_residue_ownerComponentsCore
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) :
    Tendsto
      (zetaCompletedExplicitFormulaPrimeLeftReflectedCorrectionZeroPoleScheduled
        f F h)
      atTop
      (𝓝 (zetaCompletedExplicitFormulaPrimeLeftReflectedCorrectionResidue f)) := by
  let K : ℝ → ℂ :=
    zetaCompletedExplicitFormulaPrimeLeftReflectedCorrectionZeroPoleScheduled
      f F h
  let L : ℝ → ℂ := fun u : ℝ =>
    zetaCompletedExplicitFormulaCorrectionLeftOnePoleVerticalIntegral
      f F (h.height_schedule.height u)
  have hL :
      Tendsto L atTop
        (𝓝 (zetaCompletedExplicitFormulaPrimeLeftReflectedCorrectionResidue f)) :=
    zetaCompletedExplicitFormulaCorrectionLeftOnePoleVerticalIntegral_tendsto_standardContourResidue_ownerLeftResidueValue
      f F h
  have hK_eq_L : K = L := by
    funext u
    have hpoint :
        (fun t : ℝ =>
          zetaCompletedExplicitFormulaPrimeLeftReflectedCorrectionZeroPoleKernel
            f F t) =ᵐ[
          (volume : Measure ℝ).restrict
            (Set.Icc
              (-(F.rectangle (h.height_schedule.height u)).T)
              (F.rectangle (h.height_schedule.height u)).T)]
          fun t : ℝ =>
            zetaCompletedExplicitFormulaCorrectionLeftOnePoleAffineKernel
              f F t :=
      Filter.Eventually.of_forall
        (fun t =>
          zetaCompletedExplicitFormulaPrimeLeftReflectedCorrectionZeroPoleKernel_eq_leftOnePoleAffineKernel
            f F t)
    calc
      K u =
          ∫ t in Set.Icc
              (-(F.rectangle (h.height_schedule.height u)).T)
              (F.rectangle (h.height_schedule.height u)).T,
            zetaCompletedExplicitFormulaPrimeLeftReflectedCorrectionZeroPoleKernel
              f F t := by
        exact Eq.refl _
      _ =
          ∫ t in Set.Icc
              (-(F.rectangle (h.height_schedule.height u)).T)
              (F.rectangle (h.height_schedule.height u)).T,
            zetaCompletedExplicitFormulaCorrectionLeftOnePoleAffineKernel
              f F t := by
        exact integral_congr_ae hpoint
      _ = L u := by
        exact
          (zetaCompletedExplicitFormulaCorrectionLeftOnePoleVerticalIntegral_eq_affineKernelIntegral_ownerTransport
            f F (h.height_schedule.height u)).symm
  exact Eq.subst
    (motive := fun φ : ℝ → ℂ =>
      Tendsto φ atTop
        (𝓝 (zetaCompletedExplicitFormulaPrimeLeftReflectedCorrectionResidue f)))
    hK_eq_L.symm
    hL

/-- Owner scheduled reflected one-pole correction value.

Because the denominator is pulled back from the reflected right line, the
right one denominator is the ordinary left `s = 0` off-pole denominator. -/
theorem zetaCompletedExplicitFormulaPrimeLeftReflectedCorrectionOnePoleScheduled_tendsto_zero_ownerComponentsCore
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) :
    Tendsto
      (zetaCompletedExplicitFormulaPrimeLeftReflectedCorrectionOnePoleScheduled
        f F h)
      atTop
      (𝓝 (0 : ℂ)) := by
  let K : ℝ → ℂ :=
    zetaCompletedExplicitFormulaPrimeLeftReflectedCorrectionOnePoleScheduled
      f F h
  let L : ℝ → ℂ := fun u : ℝ =>
    ∫ t in Set.Icc
        (-(F.rectangle (h.height_schedule.height u)).T)
        (F.rectangle (h.height_schedule.height u)).T,
      zetaCompletedExplicitFormulaCorrectionLeftZeroPoleAffineKernel f F t
  have hL : Tendsto L atTop (𝓝 (0 : ℂ)) :=
    zetaCompletedExplicitFormulaCorrectionLeftZeroPoleAffineKernel_scheduledWindow_tendsto_zero_ownerLeftOffPoleDecay
      f F h
  have hK_eq_L : K = L := by
    funext u
    have hpoint :
        (fun t : ℝ =>
          zetaCompletedExplicitFormulaPrimeLeftReflectedCorrectionOnePoleKernel
            f F t) =ᵐ[
          (volume : Measure ℝ).restrict
            (Set.Icc
              (-(F.rectangle (h.height_schedule.height u)).T)
              (F.rectangle (h.height_schedule.height u)).T)]
          fun t : ℝ =>
            zetaCompletedExplicitFormulaCorrectionLeftZeroPoleAffineKernel
              f F t :=
      Filter.Eventually.of_forall
        (fun t =>
          zetaCompletedExplicitFormulaPrimeLeftReflectedCorrectionOnePoleKernel_eq_leftZeroPoleAffineKernel
            f F t)
    calc
      K u =
          ∫ t in Set.Icc
              (-(F.rectangle (h.height_schedule.height u)).T)
              (F.rectangle (h.height_schedule.height u)).T,
            zetaCompletedExplicitFormulaPrimeLeftReflectedCorrectionOnePoleKernel
              f F t := by
        exact Eq.refl _
      _ =
          ∫ t in Set.Icc
              (-(F.rectangle (h.height_schedule.height u)).T)
              (F.rectangle (h.height_schedule.height u)).T,
            zetaCompletedExplicitFormulaCorrectionLeftZeroPoleAffineKernel
              f F t := by
        exact integral_congr_ae hpoint
  exact Eq.subst
    (motive := fun φ : ℝ → ℂ => Tendsto φ atTop (𝓝 (0 : ℂ)))
    hK_eq_L.symm
    hL

/-- Paired scheduled reflected pole-correction values.

The zero-pole and one-pole reflected correction values are the two residue
faces of the same reflected Cauchy/Laplace inversion calculation.  The actual
analytic content is owned by the two component leaves above. -/
theorem zetaCompletedExplicitFormulaPrimeLeftReflectedCorrectionScheduledPair_tendsto_ownerComponents
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) :
    Tendsto
      (zetaCompletedExplicitFormulaPrimeLeftReflectedCorrectionZeroPoleScheduled
        f F h)
      atTop
      (𝓝 (zetaCompletedExplicitFormulaPrimeLeftReflectedCorrectionResidue f)) ∧
    Tendsto
      (zetaCompletedExplicitFormulaPrimeLeftReflectedCorrectionOnePoleScheduled
        f F h)
      atTop
      (𝓝 (0 : ℂ)) := by
  exact
    ⟨zetaCompletedExplicitFormulaPrimeLeftReflectedCorrectionZeroPoleScheduled_tendsto_residue_ownerComponentsCore
        f F h,
      zetaCompletedExplicitFormulaPrimeLeftReflectedCorrectionOnePoleScheduled_tendsto_zero_ownerComponentsCore
        f F h⟩

/-- Compatibility spelling of the paired scheduled reflected pole-correction
values with the rectangle integrals unfolded. -/
theorem zetaCompletedExplicitFormulaPrimeLeftReflectedCorrectionKernels_scheduledWindow_tendsto_ownerComponents
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) :
    Tendsto
      (fun u : ℝ =>
        ∫ t in Set.Icc
            (-(F.rectangle (h.height_schedule.height u)).T)
            (F.rectangle (h.height_schedule.height u)).T,
          zetaCompletedExplicitFormulaPrimeLeftReflectedCorrectionZeroPoleKernel
            f F t)
      atTop
      (𝓝 ((((2 * (Real.pi : ℂ) * Complex.I) *
        (-zetaCompletedExplicitFormulaPhi f (1 / 2))) * Complex.I))) ∧
    Tendsto
      (fun u : ℝ =>
        ∫ t in Set.Icc
            (-(F.rectangle (h.height_schedule.height u)).T)
            (F.rectangle (h.height_schedule.height u)).T,
          zetaCompletedExplicitFormulaPrimeLeftReflectedCorrectionOnePoleKernel
            f F t)
      atTop
      (𝓝 (0 : ℂ)) := by
  exact
    zetaCompletedExplicitFormulaPrimeLeftReflectedCorrectionScheduledPair_tendsto_ownerComponents
      f F h

/-- Owner scheduled Cauchy/Laplace inversion value for the reflected zero-pole
correction component on the left prime line. -/
theorem zetaCompletedExplicitFormulaPrimeLeftReflectedCorrectionZeroPoleKernel_scheduledWindow_tendsto_standardResidue_ownerComponents
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) :
    Tendsto
      (fun u : ℝ =>
        ∫ t in Set.Icc
            (-(F.rectangle (h.height_schedule.height u)).T)
            (F.rectangle (h.height_schedule.height u)).T,
          zetaCompletedExplicitFormulaPrimeLeftReflectedCorrectionZeroPoleKernel
            f F t)
      atTop
      (𝓝 ((((2 * (Real.pi : ℂ) * Complex.I) *
        (-zetaCompletedExplicitFormulaPhi f (1 / 2))) * Complex.I))) := by
  exact
    (zetaCompletedExplicitFormulaPrimeLeftReflectedCorrectionKernels_scheduledWindow_tendsto_ownerComponents
      f F h).1

/-- Whole-line residue value of the reflected zero-pole correction component,
obtained from its scheduled reflected Cauchy/Laplace inversion value. -/
theorem zetaCompletedExplicitFormulaPrimeLeftReflectedCorrectionZeroPoleKernel_integral_eq_standardResidue_ownerComponents
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) :
    (∫ t : ℝ,
      zetaCompletedExplicitFormulaPrimeLeftReflectedCorrectionZeroPoleKernel
        f F t) =
      (((2 * (Real.pi : ℂ) * Complex.I) *
        (-zetaCompletedExplicitFormulaPhi f (1 / 2))) * Complex.I) := by
  exact
    explicitFormulaScheduledScalar_integral_eq_of_tendsto_integral_and_value
      (fun u : ℝ =>
        ∫ t in Set.Icc
            (-(F.rectangle (h.height_schedule.height u)).T)
            (F.rectangle (h.height_schedule.height u)).T,
          zetaCompletedExplicitFormulaPrimeLeftReflectedCorrectionZeroPoleKernel
            f F t)
      (∫ t : ℝ,
        zetaCompletedExplicitFormulaPrimeLeftReflectedCorrectionZeroPoleKernel
          f F t)
      ((((2 * (Real.pi : ℂ) * Complex.I) *
        (-zetaCompletedExplicitFormulaPhi f (1 / 2))) * Complex.I))
      (explicitFormulaScheduledRectangleWindowIntegral_tendsto_integral
        F h.height_schedule.height
        (zetaCompletedExplicitFormulaPrimeLeftReflectedCorrectionZeroPoleKernel
          f F)
        h.height_schedule.cofinal
        (zetaCompletedExplicitFormulaPrimeLeftReflectedCorrectionZeroPoleKernel_integrable
          f F h))
      (zetaCompletedExplicitFormulaPrimeLeftReflectedCorrectionZeroPoleKernel_scheduledWindow_tendsto_standardResidue_ownerComponents
        f F h)

/-- Owner scheduled Cauchy/Laplace inversion value for the reflected one-pole
correction component on the left prime line. -/
theorem zetaCompletedExplicitFormulaPrimeLeftReflectedCorrectionOnePoleKernel_scheduledWindow_tendsto_zero_ownerComponents
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) :
    Tendsto
      (fun u : ℝ =>
        ∫ t in Set.Icc
            (-(F.rectangle (h.height_schedule.height u)).T)
            (F.rectangle (h.height_schedule.height u)).T,
          zetaCompletedExplicitFormulaPrimeLeftReflectedCorrectionOnePoleKernel
            f F t)
      atTop
      (𝓝 (0 : ℂ)) := by
  exact
    (zetaCompletedExplicitFormulaPrimeLeftReflectedCorrectionKernels_scheduledWindow_tendsto_ownerComponents
      f F h).2

/-- Scheduled value of the full reflected correction kernel, obtained by
recombining the scheduled zero-pole and one-pole correction values on each
rectangle window. -/
theorem zetaCompletedExplicitFormulaPrimeLeftReflectedCorrectionKernel_scheduledWindow_tendsto_standardResidue_ownerComponents
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) :
    Tendsto
      (fun u : ℝ =>
        ∫ t in Set.Icc
            (-(F.rectangle (h.height_schedule.height u)).T)
            (F.rectangle (h.height_schedule.height u)).T,
          zetaCompletedExplicitFormulaPrimeLeftReflectedCorrectionKernel
            f F t)
      atTop
      (𝓝 ((((2 * (Real.pi : ℂ) * Complex.I) *
        (-zetaCompletedExplicitFormulaPhi f (1 / 2))) * Complex.I))) := by
  let Z : ℝ → ℂ := fun u : ℝ =>
    ∫ t in Set.Icc
        (-(F.rectangle (h.height_schedule.height u)).T)
        (F.rectangle (h.height_schedule.height u)).T,
      zetaCompletedExplicitFormulaPrimeLeftReflectedCorrectionZeroPoleKernel
        f F t
  let O : ℝ → ℂ := fun u : ℝ =>
    ∫ t in Set.Icc
        (-(F.rectangle (h.height_schedule.height u)).T)
        (F.rectangle (h.height_schedule.height u)).T,
      zetaCompletedExplicitFormulaPrimeLeftReflectedCorrectionOnePoleKernel
        f F t
  let C : ℝ → ℂ := fun u : ℝ =>
    ∫ t in Set.Icc
        (-(F.rectangle (h.height_schedule.height u)).T)
        (F.rectangle (h.height_schedule.height u)).T,
      zetaCompletedExplicitFormulaPrimeLeftReflectedCorrectionKernel
        f F t
  let B : ℂ :=
    zetaCompletedExplicitFormulaPrimeLeftReflectedCorrectionResidue f
  have hZO :
      Tendsto Z atTop (𝓝 B) ∧ Tendsto O atTop (𝓝 (0 : ℂ)) :=
    zetaCompletedExplicitFormulaPrimeLeftReflectedCorrectionKernels_scheduledWindow_tendsto_ownerComponents
      f F h
  have hsum_limit :
      Tendsto (fun u : ℝ => Z u + O u) atTop (𝓝 (B + (0 : ℂ))) :=
    hZO.1.add hZO.2
  have hC_eq_sum :
      C = fun u : ℝ => Z u + O u :=
    funext
      (fun u : ℝ =>
        have hzero_int :
            Integrable
              (zetaCompletedExplicitFormulaPrimeLeftReflectedCorrectionZeroPoleKernel
                f F)
              ((volume : Measure ℝ).restrict
                (Set.Icc
                  (-(F.rectangle (h.height_schedule.height u)).T)
                  (F.rectangle (h.height_schedule.height u)).T)) :=
          (zetaCompletedExplicitFormulaPrimeLeftReflectedCorrectionZeroPoleKernel_integrable
            f F h).integrableOn.integrable
        have hone_int :
            Integrable
              (zetaCompletedExplicitFormulaPrimeLeftReflectedCorrectionOnePoleKernel
                f F)
              ((volume : Measure ℝ).restrict
                (Set.Icc
                  (-(F.rectangle (h.height_schedule.height u)).T)
                  (F.rectangle (h.height_schedule.height u)).T)) :=
          (zetaCompletedExplicitFormulaPrimeLeftReflectedCorrectionOnePoleKernel_integrable
            f F h).integrableOn.integrable
        have hsum :
            (∫ t in Set.Icc
                (-(F.rectangle (h.height_schedule.height u)).T)
                (F.rectangle (h.height_schedule.height u)).T,
              zetaCompletedExplicitFormulaPrimeLeftReflectedCorrectionZeroPoleKernel
                  f F t +
                zetaCompletedExplicitFormulaPrimeLeftReflectedCorrectionOnePoleKernel
                  f F t) =
              Z u + O u :=
          integral_add hzero_int hone_int
        have hpoint :
            (fun t : ℝ =>
              zetaCompletedExplicitFormulaPrimeLeftReflectedCorrectionKernel
                f F t) =ᵐ[
              (volume : Measure ℝ).restrict
                (Set.Icc
                  (-(F.rectangle (h.height_schedule.height u)).T)
                  (F.rectangle (h.height_schedule.height u)).T)]
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
          C u =
              ∫ t in Set.Icc
                (-(F.rectangle (h.height_schedule.height u)).T)
                (F.rectangle (h.height_schedule.height u)).T,
              zetaCompletedExplicitFormulaPrimeLeftReflectedCorrectionZeroPoleKernel
                  f F t +
                zetaCompletedExplicitFormulaPrimeLeftReflectedCorrectionOnePoleKernel
                  f F t := by
            exact integral_congr_ae hpoint
          _ = Z u + O u := hsum)
  have hC_to_B_add_zero :
      Tendsto C atTop (𝓝 (B + (0 : ℂ))) :=
    Eq.subst
      (motive := fun φ : ℝ → ℂ => Tendsto φ atTop (𝓝 (B + (0 : ℂ))))
      hC_eq_sum.symm
      hsum_limit
  exact
    Eq.subst
      (motive := fun z : ℂ => Tendsto C atTop (𝓝 z))
      (add_zero B)
      hC_to_B_add_zero

/-- Scheduled value of the full reflected correction kernel with the residue
written using its owner scalar. -/
theorem zetaCompletedExplicitFormulaPrimeLeftReflectedCorrectionKernel_scheduledWindow_tendsto_residue_ownerComponents
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) :
    Tendsto
      (fun u : ℝ =>
        ∫ t in Set.Icc
            (-(F.rectangle (h.height_schedule.height u)).T)
            (F.rectangle (h.height_schedule.height u)).T,
          zetaCompletedExplicitFormulaPrimeLeftReflectedCorrectionKernel
            f F t)
      atTop
      (𝓝 (zetaCompletedExplicitFormulaPrimeLeftReflectedCorrectionResidue f)) := by
  exact
    zetaCompletedExplicitFormulaPrimeLeftReflectedCorrectionKernel_scheduledWindow_tendsto_standardResidue_ownerComponents
      f F h

/-- Whole-line zero value of the reflected one-pole correction component,
obtained from its scheduled reflected Cauchy/Laplace inversion value. -/
theorem zetaCompletedExplicitFormulaPrimeLeftReflectedCorrectionOnePoleKernel_integral_eq_zero_ownerComponents
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) :
    (∫ t : ℝ,
      zetaCompletedExplicitFormulaPrimeLeftReflectedCorrectionOnePoleKernel
        f F t) =
      0 := by
  exact
    explicitFormulaScheduledScalar_integral_eq_of_tendsto_integral_and_value
      (fun u : ℝ =>
        ∫ t in Set.Icc
            (-(F.rectangle (h.height_schedule.height u)).T)
            (F.rectangle (h.height_schedule.height u)).T,
          zetaCompletedExplicitFormulaPrimeLeftReflectedCorrectionOnePoleKernel
            f F t)
      (∫ t : ℝ,
        zetaCompletedExplicitFormulaPrimeLeftReflectedCorrectionOnePoleKernel
          f F t)
      (0 : ℂ)
      (explicitFormulaScheduledRectangleWindowIntegral_tendsto_integral
        F h.height_schedule.height
        (zetaCompletedExplicitFormulaPrimeLeftReflectedCorrectionOnePoleKernel
          f F)
        h.height_schedule.cofinal
        (zetaCompletedExplicitFormulaPrimeLeftReflectedCorrectionOnePoleKernel_integrable
          f F h))
      (zetaCompletedExplicitFormulaPrimeLeftReflectedCorrectionOnePoleKernel_scheduledWindow_tendsto_zero_ownerComponents
        f F h)

/-- Owner reflected correction scalar value assembled from the two pole
component Cauchy/Laplace inversion values. -/
theorem zetaCompletedExplicitFormulaPrimeLeftReflectedCorrectionKernel_integral_eq_standardResidue_ownerComponents
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) :
    (∫ t : ℝ,
      zetaCompletedExplicitFormulaPrimeLeftReflectedCorrectionKernel f F t) =
        (((2 * (Real.pi : ℂ) * Complex.I) *
          (-zetaCompletedExplicitFormulaPhi f (1 / 2))) * Complex.I) :=
  zetaCompletedExplicitFormulaPrimeLeftReflectedCorrectionKernel_integral_eq_standardResidue_of_zeroPole_onePole_values_ownerComponents
    f F h
    (zetaCompletedExplicitFormulaPrimeLeftReflectedCorrectionZeroPoleKernel_integral_eq_standardResidue_ownerComponents
      f F h)
    (zetaCompletedExplicitFormulaPrimeLeftReflectedCorrectionOnePoleKernel_integral_eq_zero_ownerComponents
      f F h)

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

/-- Scalar assembly for the reflected inverse-Gamma kernel from its
archimedean and correction reflected components.

This lemma keeps the two analytic component values explicit.  It is the
non-circular scalar API for the reflected inverse-Gamma component owner:
the Gamma/Binet owner supplies the reflected archimedean value, and the
correction-pole owner supplies the reflected correction value. -/
theorem zetaCompletedExplicitFormulaPrimeLeftReflectedInverseGammaKernel_integral_eq_leftOneSidedInverseGammaValue_of_componentValues
    (f : ZetaAdmissibleFunction)
    (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F)
    (hcoh : Complex.gammaBinetPrincipalLogCoherence)
    (harch_value :
      (∫ t : ℝ,
        zetaCompletedExplicitFormulaPrimeLeftReflectedArchimedeanKernel
          f F t) =
        -(zetaCompletedExplicitFormulaPhi f 0))
    (hcorr_value :
      (∫ t : ℝ,
        zetaCompletedExplicitFormulaPrimeLeftReflectedCorrectionKernel
          f F t) =
        (((2 * (Real.pi : ℂ) * Complex.I) *
          (-zetaCompletedExplicitFormulaPhi f (1 / 2))) * Complex.I)) :
    (∫ t : ℝ,
      zetaCompletedExplicitFormulaPrimeLeftReflectedInverseGammaKernel
        f F t) =
      zetaCompletedExplicitFormulaLeftOneSidedInverseGammaValue f := by
  let A : ℂ := ∫ t : ℝ,
    zetaCompletedExplicitFormulaPrimeLeftReflectedArchimedeanKernel f F t
  let C : ℂ := ∫ t : ℝ,
    zetaCompletedExplicitFormulaPrimeLeftReflectedCorrectionKernel f F t
  let B : ℂ :=
    zetaCompletedExplicitFormulaPrimeLeftReflectedCorrectionResidue f
  have hsum :
      (∫ t : ℝ,
        zetaCompletedExplicitFormulaPrimeLeftReflectedInverseGammaKernel
          f F t) =
        A + C :=
    zetaCompletedExplicitFormulaPrimeLeftReflectedInverseGammaKernel_integral_eq_archimedean_add_correction_integrals_of_gammaBinetCoherence
      f F h hcoh
  have hA : A = -(zetaCompletedExplicitFormulaPhi f 0) :=
    harch_value
  have hC : C = B :=
    hcorr_value
  calc
    (∫ t : ℝ,
      zetaCompletedExplicitFormulaPrimeLeftReflectedInverseGammaKernel
        f F t) = A + C := by
      exact hsum
    _ = -(zetaCompletedExplicitFormulaPhi f 0) + C := by
      exact congrArg (fun z : ℂ => z + C) hA
    _ = -(zetaCompletedExplicitFormulaPhi f 0) + B := by
      exact congrArg
        (fun z : ℂ => -(zetaCompletedExplicitFormulaPhi f 0) + z)
        hC
    _ = zetaCompletedExplicitFormulaLeftOneSidedInverseGammaValue f := by
      rfl

/-- Reflected right-line Gamma/Binet main kernel paired with the left-centered
test transform.

This is not the ordinary right archimedean Binet main kernel: the Gamma factor
uses the reflected right affine line at `-t`, while the test transform is the
left-centered transform forced by the reflected completed prime kernel. -/
noncomputable def zetaCompletedExplicitFormulaPrimeLeftReflectedArchimedeanBinetMainKernel
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (t : ℝ) : ℂ :=
  (zetaCompletedExplicitFormulaGammaRealPiLogDerivativeTerm +
        (1 / 2 : ℂ) *
          Complex.GammaLogDerivativeFixedVerticalMain
            (F.c / 2) ((-t) / 2) +
      explicitFormulaCorrectionLogDerivative
        (zetaCompletedExplicitFormulaRightAffineLine F (-t))) *
    zetaCompletedExplicitFormulaPhi f
      (zetaCompletedExplicitFormulaLeftCenteredAffineLine F t)

/-- Reflected right-line Gamma/Binet remainder kernel paired with the
left-centered test transform. -/
noncomputable def zetaCompletedExplicitFormulaPrimeLeftReflectedArchimedeanBinetRemainderKernel
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (t : ℝ) : ℂ :=
  (((1 / 2 : ℂ) *
      Complex.GammaLogDerivativeFixedVerticalRemainder
        (F.c / 2) ((-t) / 2))) *
    zetaCompletedExplicitFormulaPhi f
      (zetaCompletedExplicitFormulaLeftCenteredAffineLine F t)

/-- Pointwise reflected Gamma/Binet decomposition of the mixed archimedean
kernel.

This is the reflected analogue of the right affine Binet decomposition, but
with the left-centered test transform retained. -/
theorem zetaCompletedExplicitFormulaPrimeLeftReflectedArchimedeanKernel_eq_binetMain_add_remainder
    (f : ZetaAdmissibleFunction)
    (F : ExplicitFormulaContourFamily)
    (t : ℝ) :
    zetaCompletedExplicitFormulaPrimeLeftReflectedArchimedeanKernel f F t =
      zetaCompletedExplicitFormulaPrimeLeftReflectedArchimedeanBinetMainKernel
        f F t +
        zetaCompletedExplicitFormulaPrimeLeftReflectedArchimedeanBinetRemainderKernel
          f F t := by
  let s : ℂ := zetaCompletedExplicitFormulaRightAffineLine F (-t)
  let w : ℂ := s / 2
  let σ : ℝ := F.c / 2
  let τ : ℝ := (-t) / 2
  let P : ℂ := zetaCompletedExplicitFormulaGammaRealPiLogDerivativeTerm
  let M : ℂ := (1 / 2 : ℂ) *
    Complex.GammaLogDerivativeFixedVerticalMain σ τ
  let R : ℂ := (1 / 2 : ℂ) *
    Complex.GammaLogDerivativeFixedVerticalRemainder σ τ
  let C : ℂ := explicitFormulaCorrectionLogDerivative s
  let Φ : ℂ :=
    zetaCompletedExplicitFormulaPhi f
      (zetaCompletedExplicitFormulaLeftCenteredAffineLine F t)
  have hσ_pos : 0 < σ := by
    exact div_pos F.c_pos zero_lt_two
  have hline : w = (σ + τ * Complex.I : ℂ) := by
    exact zetaCompletedExplicitFormulaRightAffineLine_div_two_eq_fixedVertical
      F (-t)
  have hgamma_fixed :
      deriv Complex.Gamma w / Complex.Gamma w =
        Complex.GammaLogDerivativeFixedVerticalMain σ τ +
          Complex.GammaLogDerivativeFixedVerticalRemainder σ τ := by
    exact
      Eq.subst
        (motive := fun z : ℂ =>
          deriv Complex.Gamma z / Complex.Gamma z =
            Complex.GammaLogDerivativeFixedVerticalMain σ τ +
              Complex.GammaLogDerivativeFixedVerticalRemainder σ τ)
        hline.symm
        (Complex.Gamma_logDerivative_fixedRealPartLine_eq_main_add_remainder_direct
          hσ_pos τ)
  have hhalf :
      (deriv Complex.Gamma w * (1 / 2 : ℂ)) / Complex.Gamma w =
        M + R := by
    exact
      zetaCompletedExplicitFormula_halfGammaLogDeriv_binet_algebra
        (deriv Complex.Gamma w)
        (Complex.Gamma w)
        (Complex.GammaLogDerivativeFixedVerticalMain σ τ)
        (Complex.GammaLogDerivativeFixedVerticalRemainder σ τ)
        hgamma_fixed
  have hgammaR :
      deriv Gammaℝ s / Gammaℝ s = P + (M + R) := by
    have hraw :
        deriv Gammaℝ s / Gammaℝ s =
          P + (deriv Complex.Gamma w * (1 / 2 : ℂ)) /
            Complex.Gamma w :=
      zetaCompletedExplicitFormulaRightAffineLine_Gammaℝ_logDeriv_eq F (-t)
    calc
      deriv Gammaℝ s / Gammaℝ s =
          P + (deriv Complex.Gamma w * (1 / 2 : ℂ)) /
            Complex.Gamma w := hraw
      _ = P + (M + R) := by
        exact congrArg (fun z : ℂ => P + z) hhalf
  have hinverse :
      inverseGammaCompletionLogDeriv s = -(P + (M + R)) := by
    have hraw :
        inverseGammaCompletionLogDeriv s =
          -deriv Gammaℝ s / Gammaℝ s :=
      zetaCompletedExplicitFormulaInverseGammaLogDeriv_rightAffineLine_eq_neg_Gammaℝ_logDeriv
        F (-t)
    calc
      inverseGammaCompletionLogDeriv s =
          -deriv Gammaℝ s / Gammaℝ s := hraw
      _ = -(deriv Gammaℝ s / Gammaℝ s) := by
        exact neg_div (Gammaℝ s) (deriv Gammaℝ s)
      _ = -(P + (M + R)) := by
        exact congrArg Neg.neg hgammaR
  have hlog :
      explicitFormulaArchimedeanLogDerivative s =
        (-(P + M) - C) + -R := by
    calc
      explicitFormulaArchimedeanLogDerivative s =
          inverseGammaCompletionLogDeriv s - C := by
        rfl
      _ = -(P + (M + R)) - C := by
        exact congrArg (fun z : ℂ => z - C) hinverse
      _ = (-(P + M) - C) + -R := by
        exact
          zetaCompletedExplicitFormula_archimedeanBinet_logDerivative_algebra
            P M R C
  have hneg_log :
      -(explicitFormulaArchimedeanLogDerivative s) =
        (P + M + C) + R := by
    have hneg_sum :
        -((-(P + M) - C) + -R) =
          - (-(P + M) - C) + -(-R) :=
      neg_add (-(P + M) - C) (-R)
    have hfirst :
        - (-(P + M) - C) = P + M + C := by
      have hsub :
          (-(P + M) - C) = -((P + M) + C) := by
        calc
          (-(P + M) - C) = -(P + M) + -C := by
            exact sub_eq_add_neg (-(P + M)) C
          _ = -((P + M) + C) := by
            exact (neg_add (P + M) C).symm
      calc
        - (-(P + M) - C) = -(-((P + M) + C)) := by
          exact congrArg Neg.neg hsub
        _ = (P + M) + C := by
          exact neg_neg ((P + M) + C)
        _ = P + M + C := by
          rfl
    calc
      -(explicitFormulaArchimedeanLogDerivative s) =
          -((-(P + M) - C) + -R) := by
        exact congrArg Neg.neg hlog
      _ = - (-(P + M) - C) + -(-R) := by
        exact hneg_sum
      _ = (P + M + C) + -(-R) := by
        exact congrArg (fun z : ℂ => z + -(-R)) hfirst
      _ = (P + M + C) + R := by
        exact congrArg (fun z : ℂ => (P + M + C) + z) (neg_neg R)
  calc
    zetaCompletedExplicitFormulaPrimeLeftReflectedArchimedeanKernel f F t =
        (-(explicitFormulaArchimedeanLogDerivative s)) * Φ := by
      rfl
    _ = ((P + M + C) + R) * Φ := by
      exact congrArg (fun z : ℂ => z * Φ) hneg_log
    _ = (P + M + C) * Φ + R * Φ := by
      exact add_mul (P + M + C) R Φ
    _ =
        zetaCompletedExplicitFormulaPrimeLeftReflectedArchimedeanBinetMainKernel
          f F t +
          zetaCompletedExplicitFormulaPrimeLeftReflectedArchimedeanBinetRemainderKernel
            f F t := by
      rfl

/-- Owner scheduled reflected Gamma/Binet coupled contour value.

As in the ordinary archimedean Gamma/Binet line, the reflected main and
differentiated-remainder channels are not separate scalar values for an
arbitrary admissible test function.  The canonical reflected contour statement
keeps them coupled before taking the scheduled rectangle limit. -/
theorem zetaCompletedExplicitFormulaPrimeLeftReflectedArchimedeanBinetFullTransform_scheduledValue_ownerGammaBinetReflectedContour
    (f : ZetaAdmissibleFunction)
    (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F)
    (hcoh : Complex.gammaBinetPrincipalLogCoherence) :
    Tendsto
      (fun u : ℝ =>
        (∫ t in Set.Icc
            (-(F.rectangle (h.height_schedule.height u)).T)
            (F.rectangle (h.height_schedule.height u)).T,
          zetaCompletedExplicitFormulaPrimeLeftReflectedArchimedeanBinetMainKernel
            f F t) +
        ∫ t in Set.Icc
            (-(F.rectangle (h.height_schedule.height u)).T)
            (F.rectangle (h.height_schedule.height u)).T,
          zetaCompletedExplicitFormulaPrimeLeftReflectedArchimedeanBinetRemainderKernel
            f F t)
      atTop
      (𝓝 (-(zetaCompletedExplicitFormulaPhi f 0))) := by
  have htotal :
      Tendsto
        (fun u : ℝ =>
          ∫ t in Set.Icc
              (-(F.rectangle (h.height_schedule.height u)).T)
              (F.rectangle (h.height_schedule.height u)).T,
            zetaCompletedExplicitFormulaPrimeLeftReflectedArchimedeanKernel f F t)
        atTop
        (𝓝 (-(zetaCompletedExplicitFormulaPhi f 0))) :=
    zetaCompletedExplicitFormulaPrimeLeftReflectedArchimedeanScheduled_tendsto_neg_phi_zero_ownerComponentsCore
      f F h hcoh
  have hdecomp :
      (fun u : ℝ =>
        (∫ t in Set.Icc
            (-(F.rectangle (h.height_schedule.height u)).T)
            (F.rectangle (h.height_schedule.height u)).T,
          zetaCompletedExplicitFormulaPrimeLeftReflectedArchimedeanBinetMainKernel
            f F t) +
        ∫ t in Set.Icc
            (-(F.rectangle (h.height_schedule.height u)).T)
            (F.rectangle (h.height_schedule.height u)).T,
          zetaCompletedExplicitFormulaPrimeLeftReflectedArchimedeanBinetRemainderKernel
            f F t)) =
      (fun u : ℝ =>
        ∫ t in Set.Icc
            (-(F.rectangle (h.height_schedule.height u)).T)
            (F.rectangle (h.height_schedule.height u)).T,
          zetaCompletedExplicitFormulaPrimeLeftReflectedArchimedeanKernel f F t) := by
    funext u
    have hmain :
        Integrable
          (zetaCompletedExplicitFormulaPrimeLeftReflectedArchimedeanBinetMainKernel
            f F)
          (volume.restrict
            (Set.Icc
              (-(F.rectangle (h.height_schedule.height u)).T)
              (F.rectangle (h.height_schedule.height u)).T)) :=
      zetaCompletedExplicitFormulaPrimeLeftReflectedArchimedeanBinetMainKernel_integrable_restrict_Icc_ownerGammaBinetReflectedContour
        f F h u
    have hremainder :
        Integrable
          (zetaCompletedExplicitFormulaPrimeLeftReflectedArchimedeanBinetRemainderKernel
            f F)
          (volume.restrict
            (Set.Icc
              (-(F.rectangle (h.height_schedule.height u)).T)
              (F.rectangle (h.height_schedule.height u)).T)) :=
      zetaCompletedExplicitFormulaPrimeLeftReflectedArchimedeanBinetRemainderKernel_integrable_restrict_Icc_ownerGammaBinetReflectedContour
        f F h u
    have hpoint :
        zetaCompletedExplicitFormulaPrimeLeftReflectedArchimedeanKernel f F =ᵐ[
          volume.restrict
            (Set.Icc
              (-(F.rectangle (h.height_schedule.height u)).T)
              (F.rectangle (h.height_schedule.height u)).T)]
          fun t : ℝ =>
            zetaCompletedExplicitFormulaPrimeLeftReflectedArchimedeanBinetMainKernel
              f F t +
            zetaCompletedExplicitFormulaPrimeLeftReflectedArchimedeanBinetRemainderKernel
              f F t :=
      Filter.Eventually.of_forall
        (fun t =>
          zetaCompletedExplicitFormulaPrimeLeftReflectedArchimedeanKernel_eq_binetMain_add_remainder
            f F t)
    calc
      (∫ t in Set.Icc
          (-(F.rectangle (h.height_schedule.height u)).T)
          (F.rectangle (h.height_schedule.height u)).T,
        zetaCompletedExplicitFormulaPrimeLeftReflectedArchimedeanBinetMainKernel
          f F t) +
        ∫ t in Set.Icc
          (-(F.rectangle (h.height_schedule.height u)).T)
          (F.rectangle (h.height_schedule.height u)).T,
        zetaCompletedExplicitFormulaPrimeLeftReflectedArchimedeanBinetRemainderKernel
          f F t =
          ∫ t in Set.Icc
            (-(F.rectangle (h.height_schedule.height u)).T)
            (F.rectangle (h.height_schedule.height u)).T,
            (zetaCompletedExplicitFormulaPrimeLeftReflectedArchimedeanBinetMainKernel
              f F t +
              zetaCompletedExplicitFormulaPrimeLeftReflectedArchimedeanBinetRemainderKernel
              f F t) := by
        exact (integral_add hmain hremainder).symm
      _ = ∫ t in Set.Icc
            (-(F.rectangle (h.height_schedule.height u)).T)
            (F.rectangle (h.height_schedule.height u)).T,
          zetaCompletedExplicitFormulaPrimeLeftReflectedArchimedeanKernel f F t := by
        exact integral_congr_ae hpoint
  exact hdecomp ▸ htotal

/-- Measurability of the reflected Gamma/Binet main scalar factor. -/
theorem zetaCompletedExplicitFormulaPrimeLeftReflectedArchimedeanBinetMainFactor_aestronglyMeasurable
    (F : ExplicitFormulaContourFamily) :
    AEStronglyMeasurable
      (fun t : ℝ =>
        zetaCompletedExplicitFormulaGammaRealPiLogDerivativeTerm +
            (1 / 2 : ℂ) *
              Complex.GammaLogDerivativeFixedVerticalMain
                (F.c / 2) ((-t) / 2) +
          explicitFormulaCorrectionLogDerivative
            (zetaCompletedExplicitFormulaRightAffineLine F (-t)))
      (volume : Measure ℝ) := by
  have hscale : Measurable (fun t : ℝ => (-t) : ℝ) :=
    measurable_id.neg
  have hright :
      AEStronglyMeasurable
        (fun t : ℝ =>
          -(zetaCompletedExplicitFormulaGammaRealPiLogDerivativeTerm +
              (1 / 2 : ℂ) *
                Complex.GammaLogDerivativeFixedVerticalMain
                  (F.c / 2) (t / 2)) -
            explicitFormulaCorrectionLogDerivative
              (zetaCompletedExplicitFormulaRightAffineLine F t))
        (volume : Measure ℝ) :=
    zetaCompletedExplicitFormulaArchimedeanRightBinetMainFactor_aestronglyMeasurable
      F
  have hreflected_neg :
      AEStronglyMeasurable
        (fun t : ℝ =>
          -(zetaCompletedExplicitFormulaGammaRealPiLogDerivativeTerm +
              (1 / 2 : ℂ) *
                Complex.GammaLogDerivativeFixedVerticalMain
                  (F.c / 2) ((-t) / 2)) -
            explicitFormulaCorrectionLogDerivative
              (zetaCompletedExplicitFormulaRightAffineLine F (-t)))
        (volume : Measure ℝ) :=
    hright.comp_measurable hscale
  have htarget :
      (fun t : ℝ =>
        zetaCompletedExplicitFormulaGammaRealPiLogDerivativeTerm +
            (1 / 2 : ℂ) *
              Complex.GammaLogDerivativeFixedVerticalMain
                (F.c / 2) ((-t) / 2) +
          explicitFormulaCorrectionLogDerivative
            (zetaCompletedExplicitFormulaRightAffineLine F (-t))) =
      fun t : ℝ =>
        - (-(zetaCompletedExplicitFormulaGammaRealPiLogDerivativeTerm +
              (1 / 2 : ℂ) *
                Complex.GammaLogDerivativeFixedVerticalMain
                  (F.c / 2) ((-t) / 2)) -
            explicitFormulaCorrectionLogDerivative
              (zetaCompletedExplicitFormulaRightAffineLine F (-t))) := by
    funext t
    let P : ℂ := zetaCompletedExplicitFormulaGammaRealPiLogDerivativeTerm
    let G : ℂ :=
      (1 / 2 : ℂ) *
        Complex.GammaLogDerivativeFixedVerticalMain (F.c / 2) ((-t) / 2)
    let C : ℂ :=
      explicitFormulaCorrectionLogDerivative
        (zetaCompletedExplicitFormulaRightAffineLine F (-t))
    calc
      P + G + C = (P + G) + C := by
        rfl
      _ = -(-(P + G) + -C) := by
        exact (neg_add_cancel_right (P + G) C).symm
      _ = - (-(P + G) - C) := by
        exact congrArg Neg.neg (sub_eq_add_neg (-(P + G)) C).symm
  exact
    Eq.subst
      (motive := fun φ : ℝ → ℂ =>
        AEStronglyMeasurable φ (volume : Measure ℝ))
      htarget.symm
      hreflected_neg.neg

/-- Linear bound for the reflected Gamma/Binet main scalar factor. -/
theorem zetaCompletedExplicitFormulaPrimeLeftReflectedArchimedeanBinetMainFactor_linear_bound
    (F : ExplicitFormulaContourFamily) :
    ∃ B : ℝ,
      0 ≤ B ∧
      ∀ t : ℝ,
        ‖zetaCompletedExplicitFormulaGammaRealPiLogDerivativeTerm +
            (1 / 2 : ℂ) *
              Complex.GammaLogDerivativeFixedVerticalMain
                (F.c / 2) ((-t) / 2) +
          explicitFormulaCorrectionLogDerivative
            (zetaCompletedExplicitFormulaRightAffineLine F (-t))‖ ≤
          B * (1 + ‖t‖) := by
  let B : ℝ :=
    ‖zetaCompletedExplicitFormulaGammaRealPiLogDerivativeTerm‖ +
      ‖(1 / 2 : ℂ)‖ *
        ((|Real.log (F.c / 2)| + (F.c / 2 + 1) + Real.pi) +
          1 / (F.c / 2)) +
      ((1 : ℝ) / F.c + (1 : ℝ) / (F.c - 1))
  have hσ : 0 < F.c / 2 :=
    div_pos F.c_pos zero_lt_two
  have hM_nonneg :
      0 ≤
        (|Real.log (F.c / 2)| + (F.c / 2 + 1) + Real.pi) +
          1 / (F.c / 2) :=
    Complex.GammaLogDerivativeFixedVerticalMainLinearConstant_nonneg hσ
  have hB_nonneg : 0 ≤ B :=
    add_nonneg
      (add_nonneg
        (norm_nonneg zetaCompletedExplicitFormulaGammaRealPiLogDerivativeTerm)
        (mul_nonneg (norm_nonneg (1 / 2 : ℂ)) hM_nonneg))
      (add_nonneg
        (div_nonneg zero_le_one F.c_pos.le)
        (div_nonneg zero_le_one (sub_pos.mpr F.c_gt_one).le))
  exact
    ⟨B, hB_nonneg,
      fun t =>
        let P : ℂ := zetaCompletedExplicitFormulaGammaRealPiLogDerivativeTerm
        let G : ℂ :=
          (1 / 2 : ℂ) *
            Complex.GammaLogDerivativeFixedVerticalMain
              (F.c / 2) ((-t) / 2)
        let C : ℂ :=
          explicitFormulaCorrectionLogDerivative
            (zetaCompletedExplicitFormulaRightAffineLine F (-t))
        have hnorm :
            ‖P + G + C‖ = ‖-(P + G) - C‖ := by
          have hneg : P + G + C = - (-(P + G) - C) := by
            calc
              P + G + C = (P + G) + C := by
                rfl
              _ = -(-(P + G) + -C) := by
                exact (neg_add_cancel_right (P + G) C).symm
              _ = - (-(P + G) - C) := by
                exact congrArg Neg.neg
                  (sub_eq_add_neg (-(P + G)) C).symm
          calc
            ‖P + G + C‖ = ‖- (-(P + G) - C)‖ := by
              exact congrArg norm hneg
            _ = ‖-(P + G) - C‖ := by
              exact norm_neg (-(P + G) - C)
        have hright :
            ‖-(zetaCompletedExplicitFormulaGammaRealPiLogDerivativeTerm +
                  (1 / 2 : ℂ) *
                    Complex.GammaLogDerivativeFixedVerticalMain
                      (F.c / 2) ((-t) / 2)) -
                explicitFormulaCorrectionLogDerivative
                  (zetaCompletedExplicitFormulaRightAffineLine F (-t))‖ ≤
              B * (1 + ‖-t‖) :=
          zetaCompletedExplicitFormulaArchimedeanRightBinetMainFactor_linear_bound
            F (-t)
        have hweight : B * (1 + ‖-t‖) = B * (1 + ‖t‖) := by
          exact congrArg (fun x : ℝ => B * (1 + x)) (norm_neg t)
        Eq.subst
          (motive := fun x : ℝ =>
            ‖zetaCompletedExplicitFormulaGammaRealPiLogDerivativeTerm +
                (1 / 2 : ℂ) *
                  Complex.GammaLogDerivativeFixedVerticalMain
                    (F.c / 2) ((-t) / 2) +
              explicitFormulaCorrectionLogDerivative
                (zetaCompletedExplicitFormulaRightAffineLine F (-t))‖ ≤ x)
          hweight
          (Eq.subst
            (motive := fun x : ℝ =>
              x ≤ B * (1 + ‖-t‖))
            hnorm.symm
            hright)⟩

/-- Measurability of the reflected Gamma/Binet remainder scalar factor. -/
theorem zetaCompletedExplicitFormulaPrimeLeftReflectedArchimedeanBinetRemainderFactor_aestronglyMeasurable
    (F : ExplicitFormulaContourFamily) :
    AEStronglyMeasurable
      (fun t : ℝ =>
        (1 / 2 : ℂ) *
          Complex.GammaLogDerivativeFixedVerticalRemainder
            (F.c / 2) ((-t) / 2))
      (volume : Measure ℝ) := by
  have hscale : Measurable (fun t : ℝ => (-t) : ℝ) :=
    measurable_id.neg
  have hright :
      AEStronglyMeasurable
        (fun t : ℝ =>
          -((1 / 2 : ℂ) *
            Complex.GammaLogDerivativeFixedVerticalRemainder
              (F.c / 2) (t / 2)))
        (volume : Measure ℝ) :=
    zetaCompletedExplicitFormulaArchimedeanRightBinetRemainderFactor_aestronglyMeasurable
      F
  have hreflected_neg :
      AEStronglyMeasurable
        (fun t : ℝ =>
          -((1 / 2 : ℂ) *
            Complex.GammaLogDerivativeFixedVerticalRemainder
              (F.c / 2) ((-t) / 2)))
        (volume : Measure ℝ) :=
    hright.comp_measurable hscale
  exact hreflected_neg.neg

/-- Linear bound for the reflected Gamma/Binet remainder scalar factor. -/
theorem zetaCompletedExplicitFormulaPrimeLeftReflectedArchimedeanBinetRemainderFactor_linear_bound
    (F : ExplicitFormulaContourFamily) :
    ∃ B : ℝ,
      0 ≤ B ∧
      ∀ t : ℝ,
        ‖(1 / 2 : ℂ) *
          Complex.GammaLogDerivativeFixedVerticalRemainder
            (F.c / 2) ((-t) / 2)‖ ≤
          B * (1 + ‖t‖) := by
  let B : ℝ :=
    ‖(1 / 2 : ℂ)‖ *
      |‖(2 : ℂ)‖ *
        ∫ u : ℝ in Set.Ioi (0 : ℝ),
          (1 / (F.c / 2) ^ 2) *
            (u / (Real.exp ((2 : ℝ) * Real.pi * u) - 1))|
  have hB_nonneg : 0 ≤ B :=
    mul_nonneg
      (norm_nonneg (1 / 2 : ℂ))
      (abs_nonneg
        (‖(2 : ℂ)‖ *
          ∫ u : ℝ in Set.Ioi (0 : ℝ),
            (1 / (F.c / 2) ^ 2) *
              (u / (Real.exp ((2 : ℝ) * Real.pi * u) - 1)))
  exact
    ⟨B, hB_nonneg,
      fun t =>
        have hright :
            ‖-((1 / 2 : ℂ) *
              Complex.GammaLogDerivativeFixedVerticalRemainder
                (F.c / 2) ((-t) / 2))‖ ≤
              B * (1 + ‖-t‖) :=
          zetaCompletedExplicitFormulaArchimedeanRightBinetRemainderFactor_linear_bound
            F (-t)
        have hnorm :
            ‖(1 / 2 : ℂ) *
              Complex.GammaLogDerivativeFixedVerticalRemainder
                (F.c / 2) ((-t) / 2)‖ =
              ‖-((1 / 2 : ℂ) *
                Complex.GammaLogDerivativeFixedVerticalRemainder
                  (F.c / 2) ((-t) / 2))‖ :=
          (norm_neg
            ((1 / 2 : ℂ) *
              Complex.GammaLogDerivativeFixedVerticalRemainder
                (F.c / 2) ((-t) / 2))).symm
        have hweight : B * (1 + ‖-t‖) = B * (1 + ‖t‖) := by
          exact congrArg (fun x : ℝ => B * (1 + x)) (norm_neg t)
        Eq.subst
          (motive := fun x : ℝ =>
            ‖(1 / 2 : ℂ) *
              Complex.GammaLogDerivativeFixedVerticalRemainder
                (F.c / 2) ((-t) / 2)‖ ≤ x)
          hweight
          (Eq.subst
            (motive := fun x : ℝ =>
              x ≤ B * (1 + ‖-t‖))
            hnorm.symm
            hright)⟩

/-- Majorant package for the reflected Gamma/Binet main kernel. -/
theorem zetaCompletedExplicitFormulaPrimeLeftReflectedArchimedeanBinetMainKernel_majorantPackage
    (f : ZetaAdmissibleFunction)
    (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) :
    ExplicitFormulaAffineKernelMajorantPackage
      (zetaCompletedExplicitFormulaPrimeLeftReflectedArchimedeanBinetMainKernel
        f F) := by
  let A : ℝ → ℂ := fun t : ℝ =>
    zetaCompletedExplicitFormulaGammaRealPiLogDerivativeTerm +
        (1 / 2 : ℂ) *
          Complex.GammaLogDerivativeFixedVerticalMain
            (F.c / 2) ((-t) / 2) +
      explicitFormulaCorrectionLogDerivative
        (zetaCompletedExplicitFormulaRightAffineLine F (-t))
  match
      zetaCompletedExplicitFormulaPrimeLeftReflectedArchimedeanBinetMainFactor_linear_bound
        F with
  | ⟨B, hB_nonneg, hB_bound⟩ =>
      have hpackage :
          ExplicitFormulaAffineKernelMajorantPackage
            (fun t : ℝ =>
              A t *
                zetaCompletedExplicitFormulaPhi f
                  (zetaCompletedExplicitFormulaLeftCenteredAffineLine F t)) :=
        zetaCompletedExplicitFormulaLeftCenteredAffineProduct_majorantPackage_of_linear_factor_bound_common
          f F h A B hB_nonneg
          (zetaCompletedExplicitFormulaPrimeLeftReflectedArchimedeanBinetMainFactor_aestronglyMeasurable
            F)
          hB_bound
      have hfun :
          (fun t : ℝ =>
            A t *
              zetaCompletedExplicitFormulaPhi f
                (zetaCompletedExplicitFormulaLeftCenteredAffineLine F t)) =
            zetaCompletedExplicitFormulaPrimeLeftReflectedArchimedeanBinetMainKernel
              f F := by
        funext t
        rfl
      exact
        Eq.subst
          (motive := fun φ : ℝ → ℂ =>
            ExplicitFormulaAffineKernelMajorantPackage φ)
          hfun
          hpackage

/-- Majorant package for the reflected Gamma/Binet remainder kernel. -/
theorem zetaCompletedExplicitFormulaPrimeLeftReflectedArchimedeanBinetRemainderKernel_majorantPackage
    (f : ZetaAdmissibleFunction)
    (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) :
    ExplicitFormulaAffineKernelMajorantPackage
      (zetaCompletedExplicitFormulaPrimeLeftReflectedArchimedeanBinetRemainderKernel
        f F) := by
  let A : ℝ → ℂ := fun t : ℝ =>
    (1 / 2 : ℂ) *
      Complex.GammaLogDerivativeFixedVerticalRemainder
        (F.c / 2) ((-t) / 2)
  match
      zetaCompletedExplicitFormulaPrimeLeftReflectedArchimedeanBinetRemainderFactor_linear_bound
        F with
  | ⟨B, hB_nonneg, hB_bound⟩ =>
      have hpackage :
          ExplicitFormulaAffineKernelMajorantPackage
            (fun t : ℝ =>
              A t *
                zetaCompletedExplicitFormulaPhi f
                  (zetaCompletedExplicitFormulaLeftCenteredAffineLine F t)) :=
        zetaCompletedExplicitFormulaLeftCenteredAffineProduct_majorantPackage_of_linear_factor_bound_common
          f F h A B hB_nonneg
          (zetaCompletedExplicitFormulaPrimeLeftReflectedArchimedeanBinetRemainderFactor_aestronglyMeasurable
            F)
          hB_bound
      have hfun :
          (fun t : ℝ =>
            A t *
              zetaCompletedExplicitFormulaPhi f
                (zetaCompletedExplicitFormulaLeftCenteredAffineLine F t)) =
            zetaCompletedExplicitFormulaPrimeLeftReflectedArchimedeanBinetRemainderKernel
              f F := by
        funext t
        rfl
      exact
        Eq.subst
          (motive := fun φ : ℝ → ℂ =>
            ExplicitFormulaAffineKernelMajorantPackage φ)
          hfun
          hpackage

/-- Full-line integrability of the reflected Gamma/Binet main kernel. -/
theorem zetaCompletedExplicitFormulaPrimeLeftReflectedArchimedeanBinetMainKernel_integrable
    (f : ZetaAdmissibleFunction)
    (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) :
    Integrable
      (zetaCompletedExplicitFormulaPrimeLeftReflectedArchimedeanBinetMainKernel
        f F)
      (volume : Measure ℝ) :=
  (zetaCompletedExplicitFormulaPrimeLeftReflectedArchimedeanBinetMainKernel_majorantPackage
    f F h).integrable

/-- Full-line integrability of the reflected Gamma/Binet remainder kernel. -/
theorem zetaCompletedExplicitFormulaPrimeLeftReflectedArchimedeanBinetRemainderKernel_integrable
    (f : ZetaAdmissibleFunction)
    (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) :
    Integrable
      (zetaCompletedExplicitFormulaPrimeLeftReflectedArchimedeanBinetRemainderKernel
        f F)
      (volume : Measure ℝ) :=
  (zetaCompletedExplicitFormulaPrimeLeftReflectedArchimedeanBinetRemainderKernel_majorantPackage
    f F h).integrable

/-- Finite-window integrability of the reflected Gamma/Binet main kernel. -/
theorem zetaCompletedExplicitFormulaPrimeLeftReflectedArchimedeanBinetMainKernel_integrable_restrict_Icc_ownerGammaBinetReflectedContour
    (f : ZetaAdmissibleFunction)
    (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F)
    (u : ℝ) :
    Integrable
      (zetaCompletedExplicitFormulaPrimeLeftReflectedArchimedeanBinetMainKernel
        f F)
      (volume.restrict
        (Set.Icc
          (-(F.rectangle (h.height_schedule.height u)).T)
          (F.rectangle (h.height_schedule.height u)).T)) := by
  exact
    (zetaCompletedExplicitFormulaPrimeLeftReflectedArchimedeanBinetMainKernel_integrable
      f F h).mono_measure Measure.restrict_le_self

/-- Finite-window integrability of the reflected Gamma/Binet remainder kernel. -/
theorem zetaCompletedExplicitFormulaPrimeLeftReflectedArchimedeanBinetRemainderKernel_integrable_restrict_Icc_ownerGammaBinetReflectedContour
    (f : ZetaAdmissibleFunction)
    (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F)
    (u : ℝ) :
    Integrable
      (zetaCompletedExplicitFormulaPrimeLeftReflectedArchimedeanBinetRemainderKernel
        f F)
      (volume.restrict
        (Set.Icc
          (-(F.rectangle (h.height_schedule.height u)).T)
          (F.rectangle (h.height_schedule.height u)).T)) := by
  exact
    (zetaCompletedExplicitFormulaPrimeLeftReflectedArchimedeanBinetRemainderKernel_integrable
      f F h).mono_measure Measure.restrict_le_self

/-- Scheduled reflected archimedean value from separate reflected Gamma/Binet
main and remainder scheduled values.

This is a conditional assembly lemma retained for callers that genuinely have
separate channel values; the unconditional owner route below uses the coupled
full-transform theorem instead. -/
theorem zetaCompletedExplicitFormulaPrimeLeftReflectedArchimedeanScheduled_tendsto_neg_phi_zero_of_binetMain_remainder
    (f : ZetaAdmissibleFunction)
    (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F)
    (hcoh : Complex.gammaBinetPrincipalLogCoherence)
    (hmain :
      Tendsto
        (fun u : ℝ =>
          ∫ t in Set.Icc
              (-(F.rectangle (h.height_schedule.height u)).T)
              (F.rectangle (h.height_schedule.height u)).T,
            zetaCompletedExplicitFormulaPrimeLeftReflectedArchimedeanBinetMainKernel
              f F t)
        atTop
        (𝓝 (-(zetaCompletedExplicitFormulaPhi f 0))))
    (hremainder :
      Tendsto
        (fun u : ℝ =>
          ∫ t in Set.Icc
              (-(F.rectangle (h.height_schedule.height u)).T)
              (F.rectangle (h.height_schedule.height u)).T,
            zetaCompletedExplicitFormulaPrimeLeftReflectedArchimedeanBinetRemainderKernel
              f F t)
        atTop
        (𝓝 (0 : ℂ))) :
    Tendsto
      (fun u : ℝ =>
        ∫ t in Set.Icc
            (-(F.rectangle (h.height_schedule.height u)).T)
            (F.rectangle (h.height_schedule.height u)).T,
          zetaCompletedExplicitFormulaPrimeLeftReflectedArchimedeanKernel
            f F t)
      atTop
      (𝓝 (-(zetaCompletedExplicitFormulaPhi f 0))) := by
  exact
    zetaCompletedExplicitFormula_scheduledWindow_tendsto_of_binetMain_add_remainder
      F h.height_schedule.height
      (zetaCompletedExplicitFormulaPrimeLeftReflectedArchimedeanKernel f F)
      (zetaCompletedExplicitFormulaPrimeLeftReflectedArchimedeanBinetMainKernel
        f F)
      (zetaCompletedExplicitFormulaPrimeLeftReflectedArchimedeanBinetRemainderKernel
        f F)
      (-(zetaCompletedExplicitFormulaPhi f 0))
      (fun t =>
        zetaCompletedExplicitFormulaPrimeLeftReflectedArchimedeanKernel_eq_binetMain_add_remainder
          f F t)
      (fun u =>
        zetaCompletedExplicitFormulaPrimeLeftReflectedArchimedeanBinetMainKernel_integrable_restrict_Icc_ownerGammaBinetReflectedContour
          f F h u)
      (fun u =>
        zetaCompletedExplicitFormulaPrimeLeftReflectedArchimedeanBinetRemainderKernel_integrable_restrict_Icc_ownerGammaBinetReflectedContour
          f F h u)
      hmain
      hremainder

/-- Scheduled reflected archimedean value from the coupled reflected
Gamma/Binet full-transform theorem. -/
theorem zetaCompletedExplicitFormulaPrimeLeftReflectedArchimedeanScheduled_tendsto_neg_phi_zero_of_binetFullTransform
    (f : ZetaAdmissibleFunction)
    (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F)
    (hcoh : Complex.gammaBinetPrincipalLogCoherence)
    (hfull :
      Tendsto
        (fun u : ℝ =>
          (∫ t in Set.Icc
              (-(F.rectangle (h.height_schedule.height u)).T)
              (F.rectangle (h.height_schedule.height u)).T,
            zetaCompletedExplicitFormulaPrimeLeftReflectedArchimedeanBinetMainKernel
              f F t) +
            ∫ t in Set.Icc
              (-(F.rectangle (h.height_schedule.height u)).T)
              (F.rectangle (h.height_schedule.height u)).T,
            zetaCompletedExplicitFormulaPrimeLeftReflectedArchimedeanBinetRemainderKernel
              f F t)
        atTop
        (𝓝 (-(zetaCompletedExplicitFormulaPhi f 0)))) :
    Tendsto
      (fun u : ℝ =>
        ∫ t in Set.Icc
            (-(F.rectangle (h.height_schedule.height u)).T)
            (F.rectangle (h.height_schedule.height u)).T,
          zetaCompletedExplicitFormulaPrimeLeftReflectedArchimedeanKernel
            f F t)
      atTop
      (𝓝 (-(zetaCompletedExplicitFormulaPhi f 0))) := by
  let A : ℝ → ℂ := fun u : ℝ =>
    ∫ t in Set.Icc
        (-(F.rectangle (h.height_schedule.height u)).T)
        (F.rectangle (h.height_schedule.height u)).T,
      zetaCompletedExplicitFormulaPrimeLeftReflectedArchimedeanKernel
        f F t
  let B : ℝ → ℂ := fun u : ℝ =>
    (∫ t in Set.Icc
        (-(F.rectangle (h.height_schedule.height u)).T)
        (F.rectangle (h.height_schedule.height u)).T,
      zetaCompletedExplicitFormulaPrimeLeftReflectedArchimedeanBinetMainKernel
        f F t) +
      ∫ t in Set.Icc
        (-(F.rectangle (h.height_schedule.height u)).T)
        (F.rectangle (h.height_schedule.height u)).T,
      zetaCompletedExplicitFormulaPrimeLeftReflectedArchimedeanBinetRemainderKernel
        f F t
  have hA_eq_B : A = B := by
    funext u
    have hmain :
        Integrable
          (zetaCompletedExplicitFormulaPrimeLeftReflectedArchimedeanBinetMainKernel
            f F)
          (volume.restrict
            (Set.Icc
              (-(F.rectangle (h.height_schedule.height u)).T)
              (F.rectangle (h.height_schedule.height u)).T)) :=
      zetaCompletedExplicitFormulaPrimeLeftReflectedArchimedeanBinetMainKernel_integrable_restrict_Icc_ownerGammaBinetReflectedContour
        f F h u
    have hremainder :
        Integrable
          (zetaCompletedExplicitFormulaPrimeLeftReflectedArchimedeanBinetRemainderKernel
            f F)
          (volume.restrict
            (Set.Icc
              (-(F.rectangle (h.height_schedule.height u)).T)
              (F.rectangle (h.height_schedule.height u)).T)) :=
      zetaCompletedExplicitFormulaPrimeLeftReflectedArchimedeanBinetRemainderKernel_integrable_restrict_Icc_ownerGammaBinetReflectedContour
        f F h u
    have hpoint :
        (zetaCompletedExplicitFormulaPrimeLeftReflectedArchimedeanKernel
          f F) =ᵐ[
            volume.restrict
              (Set.Icc
                (-(F.rectangle (h.height_schedule.height u)).T)
                (F.rectangle (h.height_schedule.height u)).T)]
          fun t : ℝ =>
            zetaCompletedExplicitFormulaPrimeLeftReflectedArchimedeanBinetMainKernel
              f F t +
            zetaCompletedExplicitFormulaPrimeLeftReflectedArchimedeanBinetRemainderKernel
              f F t :=
      Filter.Eventually.of_forall
        (fun t =>
          zetaCompletedExplicitFormulaPrimeLeftReflectedArchimedeanKernel_eq_binetMain_add_remainder
            f F t)
    calc
      A u =
          ∫ t in Set.Icc
              (-(F.rectangle (h.height_schedule.height u)).T)
              (F.rectangle (h.height_schedule.height u)).T,
            zetaCompletedExplicitFormulaPrimeLeftReflectedArchimedeanBinetMainKernel
              f F t +
            zetaCompletedExplicitFormulaPrimeLeftReflectedArchimedeanBinetRemainderKernel
              f F t := by
        exact integral_congr_ae hpoint
      _ = B u := by
        exact integral_add hmain hremainder
  exact
    Eq.subst
      (motive := fun φ : ℝ → ℂ =>
        Tendsto φ atTop (𝓝 (-(zetaCompletedExplicitFormulaPhi f 0))))
      hA_eq_B.symm
      hfull

/-- Owner reflected Gamma/Binet contour value for the left-prime reflected
archimedean kernel.

This is the analytic contour-deformation theorem for the mixed reflected
kernel with right-line argument `F.right(-t)` and left-centered test transform.
It is intentionally upstream of the inverse-Gamma recombination below. -/
theorem zetaCompletedExplicitFormulaPrimeLeftReflectedArchimedeanScheduled_tendsto_neg_phi_zero_ownerGammaBinetReflectedContour
    (f : ZetaAdmissibleFunction)
    (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F)
    (hcoh : Complex.gammaBinetPrincipalLogCoherence) :
    Tendsto
      (fun u : ℝ =>
        ∫ t in Set.Icc
            (-(F.rectangle (h.height_schedule.height u)).T)
            (F.rectangle (h.height_schedule.height u)).T,
          zetaCompletedExplicitFormulaPrimeLeftReflectedArchimedeanKernel
            f F t)
      atTop
      (𝓝 (-(zetaCompletedExplicitFormulaPhi f 0))) := by
  exact
    zetaCompletedExplicitFormulaPrimeLeftReflectedArchimedeanScheduled_tendsto_neg_phi_zero_of_binetFullTransform
      f F h hcoh
      (zetaCompletedExplicitFormulaPrimeLeftReflectedArchimedeanBinetFullTransform_scheduledValue_ownerGammaBinetReflectedContour
        f F h hcoh)

/-- Owner scheduled reflected archimedean value on the left prime line.

This is the reflected Gamma/Binet contour value before recombining with the
rational pole-correction component. -/
theorem zetaCompletedExplicitFormulaPrimeLeftReflectedArchimedeanScheduled_tendsto_neg_phi_zero_ownerComponentsCore
    (f : ZetaAdmissibleFunction)
    (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F)
    (hcoh : Complex.gammaBinetPrincipalLogCoherence) :
    Tendsto
      (fun u : ℝ =>
        ∫ t in Set.Icc
            (-(F.rectangle (h.height_schedule.height u)).T)
            (F.rectangle (h.height_schedule.height u)).T,
          zetaCompletedExplicitFormulaPrimeLeftReflectedArchimedeanKernel
            f F t)
      atTop
      (𝓝 (-(zetaCompletedExplicitFormulaPhi f 0))) := by
  exact
    zetaCompletedExplicitFormulaPrimeLeftReflectedArchimedeanScheduled_tendsto_neg_phi_zero_ownerGammaBinetReflectedContour
      f F h hcoh

/-- Scheduled reflected inverse-Gamma value obtained by recombining the
reflected archimedean scheduled value with the reflected pole-correction
scheduled value on each rectangle window. -/
theorem zetaCompletedExplicitFormulaPrimeLeftReflectedInverseGammaScheduled_tendsto_of_archimedean_and_correction
    (f : ZetaAdmissibleFunction)
    (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F)
    (hcoh : Complex.gammaBinetPrincipalLogCoherence)
    (harch :
      Tendsto
        (fun u : ℝ =>
          ∫ t in Set.Icc
              (-(F.rectangle (h.height_schedule.height u)).T)
              (F.rectangle (h.height_schedule.height u)).T,
            zetaCompletedExplicitFormulaPrimeLeftReflectedArchimedeanKernel
              f F t)
        atTop
        (𝓝 (-(zetaCompletedExplicitFormulaPhi f 0))))
    (hcorr :
      Tendsto
        (fun u : ℝ =>
          ∫ t in Set.Icc
              (-(F.rectangle (h.height_schedule.height u)).T)
              (F.rectangle (h.height_schedule.height u)).T,
            zetaCompletedExplicitFormulaPrimeLeftReflectedCorrectionKernel
              f F t)
        atTop
        (𝓝 (zetaCompletedExplicitFormulaPrimeLeftReflectedCorrectionResidue f))) :
    Tendsto
      (zetaCompletedExplicitFormulaPrimeLeftReflectedInverseGammaScheduled f F h)
      atTop
      (𝓝 (zetaCompletedExplicitFormulaLeftOneSidedInverseGammaValue f)) := by
  let A : ℝ → ℂ := fun u : ℝ =>
    ∫ t in Set.Icc
        (-(F.rectangle (h.height_schedule.height u)).T)
        (F.rectangle (h.height_schedule.height u)).T,
      zetaCompletedExplicitFormulaPrimeLeftReflectedArchimedeanKernel
        f F t
  let C : ℝ → ℂ := fun u : ℝ =>
    ∫ t in Set.Icc
        (-(F.rectangle (h.height_schedule.height u)).T)
        (F.rectangle (h.height_schedule.height u)).T,
      zetaCompletedExplicitFormulaPrimeLeftReflectedCorrectionKernel
        f F t
  let G : ℝ → ℂ :=
    zetaCompletedExplicitFormulaPrimeLeftReflectedInverseGammaScheduled f F h
  let B : ℂ :=
    zetaCompletedExplicitFormulaPrimeLeftReflectedCorrectionResidue f
  have hsum_limit :
      Tendsto (fun u : ℝ => A u + C u) atTop
        (𝓝 (-(zetaCompletedExplicitFormulaPhi f 0) + B)) :=
    harch.add hcorr
  have htarget :
      -(zetaCompletedExplicitFormulaPhi f 0) + B =
        zetaCompletedExplicitFormulaLeftOneSidedInverseGammaValue f := by
    rfl
  have hG_eq :
      G = fun u : ℝ => A u + C u := by
    funext u
    have harch_int :
        Integrable
          (zetaCompletedExplicitFormulaPrimeLeftReflectedArchimedeanKernel
            f F)
          ((volume : Measure ℝ).restrict
            (Set.Icc
              (-(F.rectangle (h.height_schedule.height u)).T)
              (F.rectangle (h.height_schedule.height u)).T)) :=
      (zetaCompletedExplicitFormulaPrimeLeftReflectedArchimedeanKernel_integrable_of_gammaBinetCoherence_ownerComponents
        f F h hcoh).integrableOn.integrable
    have hcorr_int :
        Integrable
          (zetaCompletedExplicitFormulaPrimeLeftReflectedCorrectionKernel
            f F)
          ((volume : Measure ℝ).restrict
            (Set.Icc
              (-(F.rectangle (h.height_schedule.height u)).T)
              (F.rectangle (h.height_schedule.height u)).T)) :=
      (zetaCompletedExplicitFormulaPrimeLeftReflectedCorrectionKernel_integrable_ownerComponents
        f F h).integrableOn.integrable
    have hsum :
        (∫ t in Set.Icc
            (-(F.rectangle (h.height_schedule.height u)).T)
            (F.rectangle (h.height_schedule.height u)).T,
          zetaCompletedExplicitFormulaPrimeLeftReflectedArchimedeanKernel
              f F t +
            zetaCompletedExplicitFormulaPrimeLeftReflectedCorrectionKernel
              f F t) =
          A u + C u :=
      integral_add harch_int hcorr_int
    have hpoint :
        (fun t : ℝ =>
          zetaCompletedExplicitFormulaPrimeLeftReflectedInverseGammaKernel
            f F t) =ᵐ[
          (volume : Measure ℝ).restrict
            (Set.Icc
              (-(F.rectangle (h.height_schedule.height u)).T)
              (F.rectangle (h.height_schedule.height u)).T)]
          fun t : ℝ =>
            zetaCompletedExplicitFormulaPrimeLeftReflectedArchimedeanKernel
                f F t +
              zetaCompletedExplicitFormulaPrimeLeftReflectedCorrectionKernel
                f F t :=
      Filter.Eventually.of_forall
        (fun t =>
          (zetaCompletedExplicitFormulaPrimeLeftReflectedArchimedeanKernel_add_correction_eq_inverseGamma
            f F t).symm)
    calc
      G u =
          ∫ t in Set.Icc
            (-(F.rectangle (h.height_schedule.height u)).T)
            (F.rectangle (h.height_schedule.height u)).T,
          zetaCompletedExplicitFormulaPrimeLeftReflectedArchimedeanKernel
              f F t +
            zetaCompletedExplicitFormulaPrimeLeftReflectedCorrectionKernel
              f F t := by
        exact integral_congr_ae hpoint
      _ = A u + C u := hsum
  exact
    Eq.subst
      (motive := fun φ : ℝ → ℂ =>
        Tendsto φ atTop
          (𝓝 (zetaCompletedExplicitFormulaLeftOneSidedInverseGammaValue f)))
      hG_eq.symm
      (Eq.subst
        (motive := fun z : ℂ =>
          Tendsto (fun u : ℝ => A u + C u) atTop (𝓝 z))
        htarget
        hsum_limit)

/-- Owner scheduled reflected inverse-Gamma value on the left prime line.

This is the coupled reflected Gamma/Binet contour value before splitting into
archimedean and rational correction components. -/
theorem zetaCompletedExplicitFormulaPrimeLeftReflectedInverseGammaScheduled_tendsto_leftOneSidedInverseGammaValue_ownerComponents
    (f : ZetaAdmissibleFunction)
    (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F)
    (hcoh : Complex.gammaBinetPrincipalLogCoherence) :
    Tendsto
      (zetaCompletedExplicitFormulaPrimeLeftReflectedInverseGammaScheduled f F h)
      atTop
      (𝓝 (zetaCompletedExplicitFormulaLeftOneSidedInverseGammaValue f)) := by
  exact
    zetaCompletedExplicitFormulaPrimeLeftReflectedInverseGammaScheduled_tendsto_of_archimedean_and_correction
      f F h hcoh
      (zetaCompletedExplicitFormulaPrimeLeftReflectedArchimedeanScheduled_tendsto_neg_phi_zero_ownerComponentsCore
        f F h hcoh)
      (zetaCompletedExplicitFormulaPrimeLeftReflectedCorrectionKernel_scheduledWindow_tendsto_residue_ownerComponents
        f F h)

/-- Compatibility spelling of the owner scheduled reflected inverse-Gamma
value with the rectangle integral unfolded. -/
theorem zetaCompletedExplicitFormulaPrimeLeftReflectedInverseGammaKernel_scheduledWindow_tendsto_leftOneSidedInverseGammaValue_ownerComponents
    (f : ZetaAdmissibleFunction)
    (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F)
    (hcoh : Complex.gammaBinetPrincipalLogCoherence) :
    Tendsto
      (fun u : ℝ =>
        ∫ t in Set.Icc
            (-(F.rectangle (h.height_schedule.height u)).T)
            (F.rectangle (h.height_schedule.height u)).T,
          zetaCompletedExplicitFormulaPrimeLeftReflectedInverseGammaKernel
            f F t)
      atTop
      (𝓝 (zetaCompletedExplicitFormulaLeftOneSidedInverseGammaValue f)) := by
  exact
    zetaCompletedExplicitFormulaPrimeLeftReflectedInverseGammaScheduled_tendsto_leftOneSidedInverseGammaValue_ownerComponents
      f F h hcoh

/-- Scheduled reflected archimedean value obtained from the coupled reflected
inverse-Gamma scheduled value after subtracting the reflected pole-correction
scheduled value. -/
theorem zetaCompletedExplicitFormulaPrimeLeftReflectedArchimedeanKernel_scheduledWindow_tendsto_neg_phi_zero_ownerComponents
    (f : ZetaAdmissibleFunction)
    (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F)
    (hcoh : Complex.gammaBinetPrincipalLogCoherence) :
    Tendsto
      (fun u : ℝ =>
        ∫ t in Set.Icc
            (-(F.rectangle (h.height_schedule.height u)).T)
            (F.rectangle (h.height_schedule.height u)).T,
          zetaCompletedExplicitFormulaPrimeLeftReflectedArchimedeanKernel
            f F t)
      atTop
      (𝓝 (-(zetaCompletedExplicitFormulaPhi f 0))) := by
  exact
    zetaCompletedExplicitFormulaPrimeLeftReflectedArchimedeanScheduled_tendsto_neg_phi_zero_ownerComponentsCore
      f F h hcoh

/-- Whole-line Gamma/Binet reflected archimedean value on the left prime line,
obtained from its scheduled reflected Gamma/Binet contour value. -/
theorem zetaCompletedExplicitFormulaPrimeLeftReflectedArchimedeanKernel_integral_eq_neg_phi_zero_ownerComponents
    (f : ZetaAdmissibleFunction)
    (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F)
    (hcoh : Complex.gammaBinetPrincipalLogCoherence) :
    (∫ t : ℝ,
      zetaCompletedExplicitFormulaPrimeLeftReflectedArchimedeanKernel
        f F t) =
      -(zetaCompletedExplicitFormulaPhi f 0) := by
  exact
    explicitFormulaScheduledScalar_integral_eq_of_tendsto_integral_and_value
      (fun u : ℝ =>
        ∫ t in Set.Icc
            (-(F.rectangle (h.height_schedule.height u)).T)
            (F.rectangle (h.height_schedule.height u)).T,
          zetaCompletedExplicitFormulaPrimeLeftReflectedArchimedeanKernel
            f F t)
      (∫ t : ℝ,
        zetaCompletedExplicitFormulaPrimeLeftReflectedArchimedeanKernel
          f F t)
      (-(zetaCompletedExplicitFormulaPhi f 0))
      (explicitFormulaScheduledRectangleWindowIntegral_tendsto_integral
        F h.height_schedule.height
        (zetaCompletedExplicitFormulaPrimeLeftReflectedArchimedeanKernel
          f F)
        h.height_schedule.cofinal
        (zetaCompletedExplicitFormulaPrimeLeftReflectedArchimedeanKernel_integrable_of_gammaBinetCoherence_ownerComponents
          f F h hcoh))
      (zetaCompletedExplicitFormulaPrimeLeftReflectedArchimedeanKernel_scheduledWindow_tendsto_neg_phi_zero_ownerComponents
        f F h hcoh)

/-- Owner reflected inverse-Gamma value on the left prime line, assembled from
the reflected Gamma/Binet archimedean value and the reflected pole-correction
value. -/
theorem zetaCompletedExplicitFormulaPrimeLeftReflectedInverseGammaKernel_integral_eq_leftOneSidedInverseGammaValue_owner
    (f : ZetaAdmissibleFunction)
    (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F)
    (hcoh : Complex.gammaBinetPrincipalLogCoherence) :
    (∫ t : ℝ,
      zetaCompletedExplicitFormulaPrimeLeftReflectedInverseGammaKernel
        f F t) =
      zetaCompletedExplicitFormulaLeftOneSidedInverseGammaValue f := by
  exact
    zetaCompletedExplicitFormulaPrimeLeftReflectedInverseGammaKernel_integral_eq_leftOneSidedInverseGammaValue_of_componentValues
      f F h hcoh
      (zetaCompletedExplicitFormulaPrimeLeftReflectedArchimedeanKernel_integral_eq_neg_phi_zero_ownerComponents
        f F h hcoh)
      (zetaCompletedExplicitFormulaPrimeLeftReflectedCorrectionKernel_integral_eq_standardResidue_ownerComponents
        f F h)

end ZetaAdmissibleFunction

end
end LFunctions
end Boundary
