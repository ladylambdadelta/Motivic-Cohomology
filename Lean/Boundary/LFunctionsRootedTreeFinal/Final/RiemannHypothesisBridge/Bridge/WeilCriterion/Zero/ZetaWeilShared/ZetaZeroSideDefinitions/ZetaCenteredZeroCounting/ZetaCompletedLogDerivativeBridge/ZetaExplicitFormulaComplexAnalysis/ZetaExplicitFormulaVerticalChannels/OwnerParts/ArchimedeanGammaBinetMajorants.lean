import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaExplicitFormulaVerticalChannels.OwnerParts.ArchimedeanGammaBinetKernels

/-!
# Archimedean Gamma/Binet majorants

This file owns measurability, linear growth, majorant, and integrability facts
for the archimedean Gamma/Binet kernels.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open Complex
open Filter
open LSeries ArithmeticFunction
open MeasureTheory
open scoped ArithmeticFunction
open scoped Topology

namespace ZetaAdmissibleFunction

/-- A linearly bounded factor times the right centered test transform has an
integrable majorant.  The Gamma/Binet owner layer supplies the factor
measurability and the factor bound; this theorem owns only the reusable
Paley-Wiener multiplication step. -/
theorem zetaCompletedExplicitFormulaRightCenteredAffineProduct_majorantPackage_of_linear_factor_bound
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F)
    (A : ℝ → ℂ) (B : ℝ)
    (hB_nonneg : 0 ≤ B)
    (hA_meas : AEStronglyMeasurable A (volume : Measure ℝ))
    (hA_bound : ∀ t : ℝ, ‖A t‖ ≤ B * (1 + ‖t‖)) :
    ExplicitFormulaAffineKernelMajorantPackage
      (fun t : ℝ =>
        A t *
          zetaCompletedExplicitFormulaPhi f
            (zetaCompletedExplicitFormulaRightCenteredAffineLine F t)) := by
  let C : ℝ :=
    h.phi_control.verticalStripRapidDecayConstant
      (F.c - (1 / 2 : ℝ)) (F.c - (1 / 2 : ℝ)) 4
  let majorant : ℝ → ℝ := fun t : ℝ => B * C * (1 + ‖t‖) ^ (-(3 : ℤ))
  have hC_nonneg : 0 ≤ C :=
    h.phi_control.verticalStripRapidDecayConstant_nonneg
      (F.c - (1 / 2 : ℝ)) (F.c - (1 / 2 : ℝ)) 4
  have hintegrable :
      Integrable majorant (volume : Measure ℝ) := by
    have hfinrank : finrank ℝ ℝ = 1 :=
      Module.finrank_self ℝ
    have hfinrank_cast : ((finrank ℝ ℝ : ℕ) : ℝ) = 1 :=
      congrArg (fun n : ℕ => (n : ℝ)) hfinrank
    have hdim : (finrank ℝ ℝ : ℝ) < 3 :=
      Eq.subst
        (motive := fun x : ℝ => x < 3)
        hfinrank_cast.symm
        (one_lt_of_lt two_lt_three)
    have hbase :
        Integrable
          (fun t : ℝ => (1 + ‖t‖) ^ (-(3 : ℝ)))
          (volume : Measure ℝ) :=
      integrable_one_add_norm (E := ℝ) (μ := volume) hdim
    have hscaled :
        Integrable
          (fun t : ℝ => B * C * (1 + ‖t‖) ^ (-(3 : ℝ)))
          (volume : Measure ℝ) :=
      (hbase.const_mul C).const_mul B
    have hfun :
        majorant =
          (fun t : ℝ => B * C * (1 + ‖t‖) ^ (-(3 : ℝ))) := by
      funext t
      have hpow :
          (1 + ‖t‖) ^ (-(3 : ℤ)) =
            (1 + ‖t‖) ^ (-(3 : ℝ)) :=
        (Real.rpow_intCast (1 + ‖t‖) (-(3 : ℤ))).symm
      exact congrArg (fun x : ℝ => B * C * x) hpow
    exact
      Eq.subst
        (motive := fun φ : ℝ → ℝ => Integrable φ (volume : Measure ℝ))
        hfun.symm
        hscaled
  have hphi_meas :
      AEStronglyMeasurable
        (fun t : ℝ =>
          zetaCompletedExplicitFormulaPhi f
            (zetaCompletedExplicitFormulaRightCenteredAffineLine F t))
        (volume : Measure ℝ) :=
    zetaCompletedExplicitFormulaPhi_rightCenteredAffineLine_aestronglyMeasurable
      f F h
  have hbound :
      ∀ᵐ t ∂(volume : Measure ℝ),
        ‖A t‖ *
            ‖zetaCompletedExplicitFormulaPhi f
              (zetaCompletedExplicitFormulaRightCenteredAffineLine F t)‖ ≤
          majorant t :=
    Filter.Eventually.of_forall
      (fun t : ℝ =>
        have hfactor : ‖A t‖ ≤ B * (1 + ‖t‖) :=
          hA_bound t
        have hphi :
            ‖zetaCompletedExplicitFormulaPhi f
                (zetaCompletedExplicitFormulaRightCenteredAffineLine F t)‖ ≤
              C * (1 + ‖t‖) ^ (-(4 : ℤ)) :=
          zetaCompletedExplicitFormulaPhi_rightCenteredAffineLine_decay_bound
            f F h 4 t
        have hphi_nonneg :
            0 ≤ ‖zetaCompletedExplicitFormulaPhi f
              (zetaCompletedExplicitFormulaRightCenteredAffineLine F t)‖ :=
          norm_nonneg
            (zetaCompletedExplicitFormulaPhi f
              (zetaCompletedExplicitFormulaRightCenteredAffineLine F t))
        have hfactor_rhs_nonneg : 0 ≤ B * (1 + ‖t‖) :=
          mul_nonneg hB_nonneg (Real.zero_le_one_add_norm t)
        have hprod :
            ‖A t‖ *
                ‖zetaCompletedExplicitFormulaPhi f
                  (zetaCompletedExplicitFormulaRightCenteredAffineLine F t)‖ ≤
              (B * (1 + ‖t‖)) *
                (C * (1 + ‖t‖) ^ (-(4 : ℤ))) :=
          mul_le_mul hfactor hphi hphi_nonneg hfactor_rhs_nonneg
        have hbase_nonzero : (1 + ‖t‖ : ℝ) ≠ 0 :=
          ne_of_gt (lt_of_lt_of_le zero_lt_one (Real.one_le_one_add_norm t))
        have hweight :
            (1 + ‖t‖) * (1 + ‖t‖) ^ (-(4 : ℤ)) =
              (1 + ‖t‖) ^ (-(3 : ℤ)) := by
          calc
            (1 + ‖t‖) * (1 + ‖t‖) ^ (-(4 : ℤ)) =
                (1 + ‖t‖) ^ ((1 : ℤ) + (-(4 : ℤ))) := by
              exact (zpow_add₀ hbase_nonzero (1 : ℤ) (-(4 : ℤ))).symm
            _ = (1 + ‖t‖) ^ (-(3 : ℤ)) := by
              rfl
        have hassoc :
            (B * (1 + ‖t‖)) *
                (C * (1 + ‖t‖) ^ (-(4 : ℤ))) =
              B * C * (1 + ‖t‖) ^ (-(3 : ℤ)) := by
          let a : ℝ := 1 + ‖t‖
          let b : ℝ := (1 + ‖t‖) ^ (-(4 : ℤ))
          have hscalar :
              (B * a) * (C * b) = B * C * (a * b) := by
            calc
              (B * a) * (C * b) = B * (a * (C * b)) :=
                mul_assoc B a (C * b)
              _ = B * ((a * C) * b) := by
                exact congrArg (fun x : ℝ => B * x) (mul_assoc a C b).symm
              _ = B * ((C * a) * b) := by
                exact congrArg (fun x : ℝ => B * (x * b)) (mul_comm a C)
              _ = B * (C * (a * b)) := by
                exact congrArg (fun x : ℝ => B * x) (mul_assoc C a b)
              _ = B * C * (a * b) := by
                exact (mul_assoc B C (a * b)).symm
          have hrewrite : a * b = (1 + ‖t‖) ^ (-(3 : ℤ)) :=
            hweight
          exact
            Eq.trans hscalar
              (congrArg (fun x : ℝ => B * C * x) hrewrite)
        hprod.trans_eq hassoc)
  exact
    ExplicitFormulaAffineKernelMajorantPackage.of_mul_le
      majorant hintegrable hA_meas hphi_meas hbound

/-- A linearly bounded factor times the left centered test transform has an
integrable majorant. -/
theorem zetaCompletedExplicitFormulaLeftCenteredAffineProduct_majorantPackage_of_linear_factor_bound
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F)
    (A : ℝ → ℂ) (B : ℝ)
    (hB_nonneg : 0 ≤ B)
    (hA_meas : AEStronglyMeasurable A (volume : Measure ℝ))
    (hA_bound : ∀ t : ℝ, ‖A t‖ ≤ B * (1 + ‖t‖)) :
    ExplicitFormulaAffineKernelMajorantPackage
      (fun t : ℝ =>
        A t *
          zetaCompletedExplicitFormulaPhi f
            (zetaCompletedExplicitFormulaLeftCenteredAffineLine F t)) := by
  let C : ℝ :=
    h.phi_control.verticalStripRapidDecayConstant
      ((1 : ℝ) - F.c - (1 / 2 : ℝ))
      ((1 : ℝ) - F.c - (1 / 2 : ℝ)) 4
  let majorant : ℝ → ℝ := fun t : ℝ => B * C * (1 + ‖t‖) ^ (-(3 : ℤ))
  have hC_nonneg : 0 ≤ C :=
    h.phi_control.verticalStripRapidDecayConstant_nonneg
      ((1 : ℝ) - F.c - (1 / 2 : ℝ))
      ((1 : ℝ) - F.c - (1 / 2 : ℝ)) 4
  have hintegrable :
      Integrable majorant (volume : Measure ℝ) := by
    have hfinrank : finrank ℝ ℝ = 1 :=
      Module.finrank_self ℝ
    have hfinrank_cast : ((finrank ℝ ℝ : ℕ) : ℝ) = 1 :=
      congrArg (fun n : ℕ => (n : ℝ)) hfinrank
    have hdim : (finrank ℝ ℝ : ℝ) < 3 :=
      Eq.subst
        (motive := fun x : ℝ => x < 3)
        hfinrank_cast.symm
        (one_lt_of_lt two_lt_three)
    have hbase :
        Integrable
          (fun t : ℝ => (1 + ‖t‖) ^ (-(3 : ℝ)))
          (volume : Measure ℝ) :=
      integrable_one_add_norm (E := ℝ) (μ := volume) hdim
    have hscaled :
        Integrable
          (fun t : ℝ => B * C * (1 + ‖t‖) ^ (-(3 : ℝ)))
          (volume : Measure ℝ) :=
      (hbase.const_mul C).const_mul B
    have hfun :
        majorant =
          (fun t : ℝ => B * C * (1 + ‖t‖) ^ (-(3 : ℝ))) := by
      funext t
      have hpow :
          (1 + ‖t‖) ^ (-(3 : ℤ)) =
            (1 + ‖t‖) ^ (-(3 : ℝ)) :=
        (Real.rpow_intCast (1 + ‖t‖) (-(3 : ℤ))).symm
      exact congrArg (fun x : ℝ => B * C * x) hpow
    exact
      Eq.subst
        (motive := fun φ : ℝ → ℝ => Integrable φ (volume : Measure ℝ))
        hfun.symm
        hscaled
  have hphi_meas :
      AEStronglyMeasurable
        (fun t : ℝ =>
          zetaCompletedExplicitFormulaPhi f
            (zetaCompletedExplicitFormulaLeftCenteredAffineLine F t))
        (volume : Measure ℝ) :=
    zetaCompletedExplicitFormulaPhi_leftCenteredAffineLine_aestronglyMeasurable
      f F h
  have hbound :
      ∀ᵐ t ∂(volume : Measure ℝ),
        ‖A t‖ *
            ‖zetaCompletedExplicitFormulaPhi f
              (zetaCompletedExplicitFormulaLeftCenteredAffineLine F t)‖ ≤
          majorant t :=
    Filter.Eventually.of_forall
      (fun t : ℝ =>
        have hfactor : ‖A t‖ ≤ B * (1 + ‖t‖) :=
          hA_bound t
        have hphi :
            ‖zetaCompletedExplicitFormulaPhi f
                (zetaCompletedExplicitFormulaLeftCenteredAffineLine F t)‖ ≤
              C * (1 + ‖t‖) ^ (-(4 : ℤ)) :=
          zetaCompletedExplicitFormulaPhi_leftCenteredAffineLine_decay_bound
            f F h 4 t
        have hphi_nonneg :
            0 ≤ ‖zetaCompletedExplicitFormulaPhi f
              (zetaCompletedExplicitFormulaLeftCenteredAffineLine F t)‖ :=
          norm_nonneg
            (zetaCompletedExplicitFormulaPhi f
              (zetaCompletedExplicitFormulaLeftCenteredAffineLine F t))
        have hfactor_rhs_nonneg : 0 ≤ B * (1 + ‖t‖) :=
          mul_nonneg hB_nonneg (Real.zero_le_one_add_norm t)
        have hprod :
            ‖A t‖ *
                ‖zetaCompletedExplicitFormulaPhi f
                  (zetaCompletedExplicitFormulaLeftCenteredAffineLine F t)‖ ≤
              (B * (1 + ‖t‖)) *
                (C * (1 + ‖t‖) ^ (-(4 : ℤ))) :=
          mul_le_mul hfactor hphi hphi_nonneg hfactor_rhs_nonneg
        have hbase_nonzero : (1 + ‖t‖ : ℝ) ≠ 0 :=
          ne_of_gt (lt_of_lt_of_le zero_lt_one (Real.one_le_one_add_norm t))
        have hweight :
            (1 + ‖t‖) * (1 + ‖t‖) ^ (-(4 : ℤ)) =
              (1 + ‖t‖) ^ (-(3 : ℤ)) := by
          calc
            (1 + ‖t‖) * (1 + ‖t‖) ^ (-(4 : ℤ)) =
                (1 + ‖t‖) ^ ((1 : ℤ) + (-(4 : ℤ))) := by
              exact (zpow_add₀ hbase_nonzero (1 : ℤ) (-(4 : ℤ))).symm
            _ = (1 + ‖t‖) ^ (-(3 : ℤ)) := by
              rfl
        have hassoc :
            (B * (1 + ‖t‖)) *
                (C * (1 + ‖t‖) ^ (-(4 : ℤ))) =
              B * C * (1 + ‖t‖) ^ (-(3 : ℤ)) := by
          let a : ℝ := 1 + ‖t‖
          let b : ℝ := (1 + ‖t‖) ^ (-(4 : ℤ))
          have hscalar :
              (B * a) * (C * b) = B * C * (a * b) := by
            calc
              (B * a) * (C * b) = B * (a * (C * b)) :=
                mul_assoc B a (C * b)
              _ = B * ((a * C) * b) := by
                exact congrArg (fun x : ℝ => B * x) (mul_assoc a C b).symm
              _ = B * ((C * a) * b) := by
                exact congrArg (fun x : ℝ => B * (x * b)) (mul_comm a C)
              _ = B * (C * (a * b)) := by
                exact congrArg (fun x : ℝ => B * x) (mul_assoc C a b)
              _ = B * C * (a * b) := by
                exact (mul_assoc B C (a * b)).symm
          have hrewrite : a * b = (1 + ‖t‖) ^ (-(3 : ℤ)) :=
            hweight
          exact
            Eq.trans hscalar
              (congrArg (fun x : ℝ => B * C * x) hrewrite)
        hprod.trans_eq hassoc)
  exact
    ExplicitFormulaAffineKernelMajorantPackage.of_mul_le
      majorant hintegrable hA_meas hphi_meas hbound

/-- Strong measurability of the elementary correction logarithmic derivative
on the right affine line. -/
theorem zetaCompletedExplicitFormulaCorrectionLogDerivative_rightAffineLine_aestronglyMeasurable
    (F : ExplicitFormulaContourFamily) :
    AEStronglyMeasurable
      (fun t : ℝ =>
        explicitFormulaCorrectionLogDerivative
          (zetaCompletedExplicitFormulaRightAffineLine F t))
      (volume : Measure ℝ) := by
  let line : ℝ → ℂ := fun t : ℝ => zetaCompletedExplicitFormulaRightAffineLine F t
  have hline : Measurable line :=
    (zetaCompletedExplicitFormulaRightAffineLine_continuous F).measurable
  have hzero :
      Measurable (fun t : ℝ => (-1 : ℂ) / line t) :=
    measurable_const.div hline
  have hone :
      Measurable (fun t : ℝ => (1 : ℂ) / (line t - 1)) :=
    measurable_const.div (hline.sub measurable_const)
  have hpole :
      (fun t : ℝ => explicitFormulaCorrectionLogDerivative (line t)) =
        (fun t : ℝ => (-1 : ℂ) / line t - (1 : ℂ) / (line t - 1)) := by
    funext t
    exact explicitFormulaCorrectionLogDerivative_eq_poleCorrection (line t)
  have hmeas :
      Measurable
        (fun t : ℝ => (-1 : ℂ) / line t - (1 : ℂ) / (line t - 1)) :=
    hzero.sub hone
  exact
    Eq.subst
      (motive := fun φ : ℝ → ℂ =>
        AEStronglyMeasurable φ (volume : Measure ℝ))
      hpole.symm
      hmeas.aestronglyMeasurable

/-- Strong measurability of the elementary correction logarithmic derivative
on the left affine line. -/
theorem zetaCompletedExplicitFormulaCorrectionLogDerivative_leftAffineLine_aestronglyMeasurable
    (F : ExplicitFormulaContourFamily) :
    AEStronglyMeasurable
      (fun t : ℝ =>
        explicitFormulaCorrectionLogDerivative
          (zetaCompletedExplicitFormulaLeftAffineLine F t))
      (volume : Measure ℝ) := by
  let line : ℝ → ℂ := fun t : ℝ => zetaCompletedExplicitFormulaLeftAffineLine F t
  have hline : Measurable line :=
    (zetaCompletedExplicitFormulaLeftAffineLine_continuous F).measurable
  have hzero :
      Measurable (fun t : ℝ => (-1 : ℂ) / line t) :=
    measurable_const.div hline
  have hone :
      Measurable (fun t : ℝ => (1 : ℂ) / (line t - 1)) :=
    measurable_const.div (hline.sub measurable_const)
  have hpole :
      (fun t : ℝ => explicitFormulaCorrectionLogDerivative (line t)) =
        (fun t : ℝ => (-1 : ℂ) / line t - (1 : ℂ) / (line t - 1)) := by
    funext t
    exact explicitFormulaCorrectionLogDerivative_eq_poleCorrection (line t)
  have hmeas :
      Measurable
        (fun t : ℝ => (-1 : ℂ) / line t - (1 : ℂ) / (line t - 1)) :=
    hzero.sub hone
  exact
    Eq.subst
      (motive := fun φ : ℝ → ℂ =>
        AEStronglyMeasurable φ (volume : Measure ℝ))
      hpole.symm
      hmeas.aestronglyMeasurable

/-- Strong measurability of the right archimedean Binet main factor before
multiplication by the centered test transform. -/
theorem zetaCompletedExplicitFormulaArchimedeanRightBinetMainFactor_aestronglyMeasurable
    (F : ExplicitFormulaContourFamily) :
    AEStronglyMeasurable
      (fun t : ℝ =>
        -(zetaCompletedExplicitFormulaGammaRealPiLogDerivativeTerm +
            (1 / 2 : ℂ) *
              Complex.GammaLogDerivativeFixedVerticalMain
                (F.c / 2) (t / 2)) -
          explicitFormulaCorrectionLogDerivative
            (zetaCompletedExplicitFormulaRightAffineLine F t))
      (volume : Measure ℝ) := by
  have hscale : Measurable (fun t : ℝ => t / 2) :=
    measurable_id.div_const 2
  have hgamma :
      AEStronglyMeasurable
        (fun t : ℝ =>
          Complex.GammaLogDerivativeFixedVerticalMain (F.c / 2) (t / 2))
        (volume : Measure ℝ) :=
    (Complex.GammaLogDerivativeFixedVerticalMain_aestronglyMeasurable
      (F.c / 2)).comp_measurable hscale
  have hhalf :
      AEStronglyMeasurable
        (fun t : ℝ =>
          (1 / 2 : ℂ) *
            Complex.GammaLogDerivativeFixedVerticalMain (F.c / 2) (t / 2))
        (volume : Measure ℝ) :=
    hgamma.const_mul (1 / 2 : ℂ)
  have hwith_pi :
      AEStronglyMeasurable
        (fun t : ℝ =>
          zetaCompletedExplicitFormulaGammaRealPiLogDerivativeTerm +
            (1 / 2 : ℂ) *
              Complex.GammaLogDerivativeFixedVerticalMain (F.c / 2) (t / 2))
        (volume : Measure ℝ) :=
    aestronglyMeasurable_const.add hhalf
  have hcorr :
      AEStronglyMeasurable
        (fun t : ℝ =>
          explicitFormulaCorrectionLogDerivative
            (zetaCompletedExplicitFormulaRightAffineLine F t))
        (volume : Measure ℝ) :=
    zetaCompletedExplicitFormulaCorrectionLogDerivative_rightAffineLine_aestronglyMeasurable
      F
  exact hwith_pi.neg.sub hcorr

/-- Strong measurability of the left archimedean Binet main factor before
multiplication by the centered test transform. -/
theorem zetaCompletedExplicitFormulaArchimedeanLeftBinetMainFactor_aestronglyMeasurable
    (F : ExplicitFormulaContourFamily) :
    AEStronglyMeasurable
      (fun t : ℝ =>
        -(zetaCompletedExplicitFormulaGammaRealPiLogDerivativeTerm +
            (1 / 2 : ℂ) *
              Complex.GammaLogDerivativeFixedVerticalShiftNatMain
                ((1 - F.c) / 2)
                (zetaCompletedExplicitFormulaArchimedeanLeftBinetShiftNat F)
                (t / 2)) -
          explicitFormulaCorrectionLogDerivative
            (zetaCompletedExplicitFormulaLeftAffineLine F t))
      (volume : Measure ℝ) := by
  have hscale : Measurable (fun t : ℝ => t / 2) :=
    measurable_id.div_const 2
  have hgamma :
      AEStronglyMeasurable
        (fun t : ℝ =>
          Complex.GammaLogDerivativeFixedVerticalShiftNatMain
            ((1 - F.c) / 2)
            (zetaCompletedExplicitFormulaArchimedeanLeftBinetShiftNat F)
            (t / 2))
        (volume : Measure ℝ) :=
    (Complex.GammaLogDerivativeFixedVerticalShiftNatMain_aestronglyMeasurable
      ((1 - F.c) / 2)
      (zetaCompletedExplicitFormulaArchimedeanLeftBinetShiftNat F)).comp_measurable
        hscale
  have hhalf :
      AEStronglyMeasurable
        (fun t : ℝ =>
          (1 / 2 : ℂ) *
            Complex.GammaLogDerivativeFixedVerticalShiftNatMain
              ((1 - F.c) / 2)
              (zetaCompletedExplicitFormulaArchimedeanLeftBinetShiftNat F)
              (t / 2))
        (volume : Measure ℝ) :=
    hgamma.const_mul (1 / 2 : ℂ)
  have hwith_pi :
      AEStronglyMeasurable
        (fun t : ℝ =>
          zetaCompletedExplicitFormulaGammaRealPiLogDerivativeTerm +
            (1 / 2 : ℂ) *
              Complex.GammaLogDerivativeFixedVerticalShiftNatMain
                ((1 - F.c) / 2)
                (zetaCompletedExplicitFormulaArchimedeanLeftBinetShiftNat F)
                (t / 2))
        (volume : Measure ℝ) :=
    aestronglyMeasurable_const.add hhalf
  have hcorr :
      AEStronglyMeasurable
        (fun t : ℝ =>
          explicitFormulaCorrectionLogDerivative
            (zetaCompletedExplicitFormulaLeftAffineLine F t))
        (volume : Measure ℝ) :=
    zetaCompletedExplicitFormulaCorrectionLogDerivative_leftAffineLine_aestronglyMeasurable
      F
  exact hwith_pi.neg.sub hcorr

/-- Strong measurability of the right archimedean Binet main kernel. -/
theorem zetaCompletedExplicitFormulaArchimedeanRightBinetMainKernel_aestronglyMeasurable
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) :
    AEStronglyMeasurable
      (zetaCompletedExplicitFormulaArchimedeanRightBinetMainKernel f F)
      (volume : Measure ℝ) :=
  (zetaCompletedExplicitFormulaArchimedeanRightBinetMainFactor_aestronglyMeasurable
    F).mul
    (zetaCompletedExplicitFormulaPhi_rightCenteredAffineLine_aestronglyMeasurable
      f F h)

/-- Strong measurability of the left archimedean Binet main kernel. -/
theorem zetaCompletedExplicitFormulaArchimedeanLeftBinetMainKernel_aestronglyMeasurable
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) :
    AEStronglyMeasurable
      (zetaCompletedExplicitFormulaArchimedeanLeftBinetMainKernel f F)
      (volume : Measure ℝ) :=
  (zetaCompletedExplicitFormulaArchimedeanLeftBinetMainFactor_aestronglyMeasurable
    F).mul
    (zetaCompletedExplicitFormulaPhi_leftCenteredAffineLine_aestronglyMeasurable
      f F h)

/-- Strong measurability of the right archimedean Binet remainder factor before
multiplication by the centered test transform. -/
theorem zetaCompletedExplicitFormulaArchimedeanRightBinetRemainderFactor_aestronglyMeasurable
    (F : ExplicitFormulaContourFamily) :
    AEStronglyMeasurable
      (fun t : ℝ =>
        -((1 / 2 : ℂ) *
          Complex.GammaLogDerivativeFixedVerticalRemainder
            (F.c / 2) (t / 2)))
      (volume : Measure ℝ) := by
  have hscale : Measurable (fun t : ℝ => t / 2) :=
    measurable_id.div_const 2
  have hgamma :
      AEStronglyMeasurable
        (fun t : ℝ =>
          Complex.GammaLogDerivativeFixedVerticalRemainder (F.c / 2) (t / 2))
        (volume : Measure ℝ) :=
    (Complex.GammaLogDerivativeFixedVerticalRemainder_aestronglyMeasurable
      (F.c / 2)).comp_measurable hscale
  exact (hgamma.const_mul (1 / 2 : ℂ)).neg

/-- Strong measurability of the left archimedean Binet remainder factor before
multiplication by the centered test transform. -/
theorem zetaCompletedExplicitFormulaArchimedeanLeftBinetRemainderFactor_aestronglyMeasurable
    (F : ExplicitFormulaContourFamily) :
    AEStronglyMeasurable
      (fun t : ℝ =>
        -((1 / 2 : ℂ) *
          Complex.GammaLogDerivativeFixedVerticalShiftNatRemainder
            ((1 - F.c) / 2)
            (zetaCompletedExplicitFormulaArchimedeanLeftBinetShiftNat F)
            (t / 2)))
      (volume : Measure ℝ) := by
  have hscale : Measurable (fun t : ℝ => t / 2) :=
    measurable_id.div_const 2
  have hgamma :
      AEStronglyMeasurable
        (fun t : ℝ =>
          Complex.GammaLogDerivativeFixedVerticalShiftNatRemainder
            ((1 - F.c) / 2)
            (zetaCompletedExplicitFormulaArchimedeanLeftBinetShiftNat F)
            (t / 2))
        (volume : Measure ℝ) :=
    (Complex.GammaLogDerivativeFixedVerticalShiftNatRemainder_aestronglyMeasurable
      ((1 - F.c) / 2)
      (zetaCompletedExplicitFormulaArchimedeanLeftBinetShiftNat F)).comp_measurable
        hscale
  exact (hgamma.const_mul (1 / 2 : ℂ)).neg

/-- Strong measurability of the right archimedean Binet remainder kernel. -/
theorem zetaCompletedExplicitFormulaArchimedeanRightBinetRemainderKernel_aestronglyMeasurable
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) :
    AEStronglyMeasurable
      (zetaCompletedExplicitFormulaArchimedeanRightBinetRemainderKernel f F)
      (volume : Measure ℝ) :=
  (zetaCompletedExplicitFormulaArchimedeanRightBinetRemainderFactor_aestronglyMeasurable
    F).mul
    (zetaCompletedExplicitFormulaPhi_rightCenteredAffineLine_aestronglyMeasurable
      f F h)

/-- Strong measurability of the left archimedean Binet remainder kernel. -/
theorem zetaCompletedExplicitFormulaArchimedeanLeftBinetRemainderKernel_aestronglyMeasurable
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) :
    AEStronglyMeasurable
      (zetaCompletedExplicitFormulaArchimedeanLeftBinetRemainderKernel f F)
      (volume : Measure ℝ) :=
  (zetaCompletedExplicitFormulaArchimedeanLeftBinetRemainderFactor_aestronglyMeasurable
    F).mul
    (zetaCompletedExplicitFormulaPhi_leftCenteredAffineLine_aestronglyMeasurable
      f F h)

/-- Half-height rescaling does not increase the affine linear weight. -/
theorem real_one_add_norm_div_two_le_one_add_norm
    (t : ℝ) :
    1 + ‖t / 2‖ ≤ 1 + ‖t‖ := by
  have htwo_abs : |(2 : ℝ)| = 2 :=
    abs_of_nonneg zero_le_two
  have htwo_inv_le_one : (2 : ℝ)⁻¹ ≤ 1 := by
    exact inv_le_one_of_one_le₀ one_le_two
  have hnorm_div :
      ‖t / 2‖ = ‖t‖ * (2 : ℝ)⁻¹ := by
    calc
      ‖t / 2‖ = |t / 2| := by
        exact Real.norm_eq_abs (t / 2)
      _ = |t| / |(2 : ℝ)| := by
        exact abs_div t 2
      _ = |t| / 2 := by
        exact congrArg (fun x : ℝ => |t| / x) htwo_abs
      _ = |t| * (2 : ℝ)⁻¹ := by
        exact div_eq_mul_inv |t| 2
      _ = ‖t‖ * (2 : ℝ)⁻¹ := by
        exact congrArg (fun x : ℝ => x * (2 : ℝ)⁻¹) (Real.norm_eq_abs t).symm
  have hhalf_le : ‖t / 2‖ ≤ ‖t‖ := by
    calc
      ‖t / 2‖ = ‖t‖ * (2 : ℝ)⁻¹ := hnorm_div
      _ ≤ ‖t‖ * 1 :=
        mul_le_mul_of_nonneg_left htwo_inv_le_one (norm_nonneg t)
      _ = ‖t‖ := mul_one ‖t‖
  exact add_le_add_left hhalf_le 1

/-- A nonnegative constant is bounded by the corresponding affine linear
weight. -/
theorem real_nonneg_le_mul_one_add_norm
    {B : ℝ} (hB : 0 ≤ B) (t : ℝ) :
    B ≤ B * (1 + ‖t‖) := by
  calc
    B = B * 1 := (mul_one B).symm
    _ ≤ B * (1 + ‖t‖) :=
      mul_le_mul_of_nonneg_left (Real.one_le_one_add_norm t) hB

/-- The elementary correction logarithmic derivative on the right line has a
uniform, hence linear, bound. -/
theorem zetaCompletedExplicitFormulaCorrectionLogDerivative_rightAffineLine_linear_bound
    (F : ExplicitFormulaContourFamily) :
    ∀ t : ℝ,
      ‖explicitFormulaCorrectionLogDerivative
          (zetaCompletedExplicitFormulaRightAffineLine F t)‖ ≤
        ((1 : ℝ) / F.c + (1 : ℝ) / (F.c - 1)) *
          (1 + ‖t‖) := by
  intro t
  let line : ℂ := zetaCompletedExplicitFormulaRightAffineLine F t
  let Z : ℂ := -1 / line
  let O : ℂ := -(1 / (line - 1))
  have hpole :
      explicitFormulaCorrectionLogDerivative line = Z + O := by
    calc
      explicitFormulaCorrectionLogDerivative line =
          (-1 : ℂ) / line - (1 : ℂ) / (line - 1) := by
        exact explicitFormulaCorrectionLogDerivative_eq_poleCorrection line
      _ = Z + O := by
        exact sub_eq_add_neg ((-1 : ℂ) / line) ((1 : ℂ) / (line - 1))
  have hZ : ‖Z‖ ≤ (1 : ℝ) / F.c :=
    zetaCompletedExplicitFormulaRightAffineLine_zeroPoleCoefficient_norm_le
      F t
  have hO : ‖O‖ ≤ (1 : ℝ) / (F.c - 1) :=
    zetaCompletedExplicitFormulaRightAffineLine_onePoleCoefficient_norm_le
      F t
  have hsum :
      ‖Z‖ + ‖O‖ ≤ (1 : ℝ) / F.c + (1 : ℝ) / (F.c - 1) :=
    add_le_add hZ hO
  have hconst_nonneg :
      0 ≤ (1 : ℝ) / F.c + (1 : ℝ) / (F.c - 1) :=
    add_nonneg
      (div_nonneg zero_le_one F.c_pos.le)
      (div_nonneg zero_le_one (sub_pos.mpr F.c_gt_one).le)
  calc
    ‖explicitFormulaCorrectionLogDerivative line‖ = ‖Z + O‖ := by
      exact congrArg norm hpole
    _ ≤ ‖Z‖ + ‖O‖ :=
      norm_add_le Z O
    _ ≤ (1 : ℝ) / F.c + (1 : ℝ) / (F.c - 1) :=
      hsum
    _ ≤ ((1 : ℝ) / F.c + (1 : ℝ) / (F.c - 1)) *
        (1 + ‖t‖) :=
      real_nonneg_le_mul_one_add_norm hconst_nonneg t

/-- The elementary correction logarithmic derivative on the left line has a
uniform, hence linear, bound. -/
theorem zetaCompletedExplicitFormulaCorrectionLogDerivative_leftAffineLine_linear_bound
    (F : ExplicitFormulaContourFamily) :
    ∀ t : ℝ,
      ‖explicitFormulaCorrectionLogDerivative
          (zetaCompletedExplicitFormulaLeftAffineLine F t)‖ ≤
        ((1 : ℝ) / (-(1 - F.c)) +
            (1 : ℝ) / (-((1 - F.c) - 1))) *
          (1 + ‖t‖) := by
  intro t
  let line : ℂ := zetaCompletedExplicitFormulaLeftAffineLine F t
  let Z : ℂ := -1 / line
  let O : ℂ := -(1 / (line - 1))
  have hpole :
      explicitFormulaCorrectionLogDerivative line = Z + O := by
    calc
      explicitFormulaCorrectionLogDerivative line =
          (-1 : ℂ) / line - (1 : ℂ) / (line - 1) := by
        exact explicitFormulaCorrectionLogDerivative_eq_poleCorrection line
      _ = Z + O := by
        exact sub_eq_add_neg ((-1 : ℂ) / line) ((1 : ℂ) / (line - 1))
  have hZ : ‖Z‖ ≤ (1 : ℝ) / (-(1 - F.c)) :=
    zetaCompletedExplicitFormulaLeftAffineLine_zeroPoleCoefficient_norm_le
      F t
  have hO : ‖O‖ ≤ (1 : ℝ) / (-((1 - F.c) - 1)) :=
    zetaCompletedExplicitFormulaLeftAffineLine_onePoleCoefficient_norm_le
      F t
  have hsum :
      ‖Z‖ + ‖O‖ ≤
        (1 : ℝ) / (-(1 - F.c)) +
          (1 : ℝ) / (-((1 - F.c) - 1)) :=
    add_le_add hZ hO
  have hzero_den_pos : 0 < -(1 - F.c) :=
    neg_pos.mpr F.one_sub_c_neg
  have hone_den_pos : 0 < -((1 - F.c) - 1) := by
    have hneg : (1 - F.c) - 1 < 0 := by
      calc
        (1 - F.c) - 1 < 0 - 1 := by
          exact sub_lt_sub_right F.one_sub_c_neg 1
        _ < 0 := by
          exact neg_lt_zero.mpr zero_lt_one
    exact neg_pos.mpr hneg
  have hconst_nonneg :
      0 ≤
        (1 : ℝ) / (-(1 - F.c)) +
          (1 : ℝ) / (-((1 - F.c) - 1)) :=
    add_nonneg
      (div_nonneg zero_le_one hzero_den_pos.le)
      (div_nonneg zero_le_one hone_den_pos.le)
  calc
    ‖explicitFormulaCorrectionLogDerivative line‖ = ‖Z + O‖ := by
      exact congrArg norm hpole
    _ ≤ ‖Z‖ + ‖O‖ :=
      norm_add_le Z O
    _ ≤
        (1 : ℝ) / (-(1 - F.c)) +
          (1 : ℝ) / (-((1 - F.c) - 1)) :=
      hsum
    _ ≤
        ((1 : ℝ) / (-(1 - F.c)) +
            (1 : ℝ) / (-((1 - F.c) - 1))) *
          (1 + ‖t‖) :=
      real_nonneg_le_mul_one_add_norm hconst_nonneg t

/-- The constant `π` part of the right Binet main factor has linear growth. -/
theorem zetaCompletedExplicitFormulaGammaRealPiLogDerivativeTerm_linear_bound
    (t : ℝ) :
    ‖zetaCompletedExplicitFormulaGammaRealPiLogDerivativeTerm‖ ≤
      ‖zetaCompletedExplicitFormulaGammaRealPiLogDerivativeTerm‖ *
        (1 + ‖t‖) :=
  real_nonneg_le_mul_one_add_norm
    (norm_nonneg zetaCompletedExplicitFormulaGammaRealPiLogDerivativeTerm)
    t

/-- The fixed-vertical Gamma-main part of the right Binet main factor has
linear growth. -/
theorem zetaCompletedExplicitFormulaGammaLogDerivativeFixedVerticalMain_right_linear_bound
    (F : ExplicitFormulaContourFamily) :
    ∀ t : ℝ,
      ‖(1 / 2 : ℂ) *
          Complex.GammaLogDerivativeFixedVerticalMain
            (F.c / 2) (t / 2)‖ ≤
        (‖(1 / 2 : ℂ)‖ *
          ((|Real.log (F.c / 2)| + (F.c / 2 + 1) + Real.pi) +
            1 / (F.c / 2))) *
          (1 + ‖t‖) := by
  intro t
  let G : ℂ :=
    (1 / 2 : ℂ) *
      Complex.GammaLogDerivativeFixedVerticalMain (F.c / 2) (t / 2)
  let M : ℝ :=
    (|Real.log (F.c / 2)| + (F.c / 2 + 1) + Real.pi) +
      1 / (F.c / 2)
  have hσ : 0 < F.c / 2 :=
    div_pos F.c_pos zero_lt_two
  have hM_nonneg : 0 ≤ M :=
    Complex.GammaLogDerivativeFixedVerticalMainLinearConstant_nonneg hσ
  have hhalf_nonneg : 0 ≤ ‖(1 / 2 : ℂ)‖ :=
    norm_nonneg (1 / 2 : ℂ)
  have hG_raw :
      ‖G‖ ≤ ‖(1 / 2 : ℂ)‖ * (M * (1 + ‖t / 2‖)) := by
    have hmain :
        ‖Complex.GammaLogDerivativeFixedVerticalMain
            (F.c / 2) (t / 2)‖ ≤
          M * (1 + ‖t / 2‖) :=
      Complex.GammaLogDerivativeFixedVerticalMain_polynomial_bound
        hσ (t / 2)
    calc
      ‖G‖ =
          ‖(1 / 2 : ℂ)‖ *
            ‖Complex.GammaLogDerivativeFixedVerticalMain
              (F.c / 2) (t / 2)‖ := by
        exact norm_mul (1 / 2 : ℂ)
          (Complex.GammaLogDerivativeFixedVerticalMain
            (F.c / 2) (t / 2))
      _ ≤ ‖(1 / 2 : ℂ)‖ * (M * (1 + ‖t / 2‖)) :=
        mul_le_mul_of_nonneg_left hmain hhalf_nonneg
  have hweight :
      M * (1 + ‖t / 2‖) ≤ M * (1 + ‖t‖) :=
    mul_le_mul_of_nonneg_left
      (real_one_add_norm_div_two_le_one_add_norm t)
      hM_nonneg
  calc
    ‖(1 / 2 : ℂ) *
        Complex.GammaLogDerivativeFixedVerticalMain
          (F.c / 2) (t / 2)‖ = ‖G‖ := by
      rfl
    _ ≤ ‖(1 / 2 : ℂ)‖ * (M * (1 + ‖t / 2‖)) :=
      hG_raw
    _ ≤ ‖(1 / 2 : ℂ)‖ * (M * (1 + ‖t‖)) :=
      mul_le_mul_of_nonneg_left hweight hhalf_nonneg
    _ = (‖(1 / 2 : ℂ)‖ * M) * (1 + ‖t‖) := by
      exact (mul_assoc ‖(1 / 2 : ℂ)‖ M (1 + ‖t‖)).symm

/-- The right `π` component of the Binet main kernel has the standard affine
integrable majorant package. -/
theorem zetaCompletedExplicitFormulaGammaRealPiLogDerivativeTerm_rightKernel_majorantPackage
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) :
    ExplicitFormulaAffineKernelMajorantPackage
      (fun t : ℝ =>
        zetaCompletedExplicitFormulaGammaRealPiLogDerivativeTerm *
          zetaCompletedExplicitFormulaPhi f
            (zetaCompletedExplicitFormulaRightCenteredAffineLine F t)) := by
  let A : ℝ → ℂ := fun _ : ℝ =>
    zetaCompletedExplicitFormulaGammaRealPiLogDerivativeTerm
  let B : ℝ := ‖zetaCompletedExplicitFormulaGammaRealPiLogDerivativeTerm‖
  have hB_nonneg : 0 ≤ B :=
    norm_nonneg zetaCompletedExplicitFormulaGammaRealPiLogDerivativeTerm
  have hA_meas : AEStronglyMeasurable A (volume : Measure ℝ) :=
    aestronglyMeasurable_const
  have hA_bound : ∀ t : ℝ, ‖A t‖ ≤ B * (1 + ‖t‖) := by
    intro t
    exact zetaCompletedExplicitFormulaGammaRealPiLogDerivativeTerm_linear_bound t
  exact
    zetaCompletedExplicitFormulaRightCenteredAffineProduct_majorantPackage_of_linear_factor_bound
      f F h A B hB_nonneg hA_meas hA_bound

/-- The right fixed-vertical Gamma-main component of the Binet main kernel has
the standard affine integrable majorant package. -/
theorem zetaCompletedExplicitFormulaGammaLogDerivativeFixedVerticalMain_rightKernel_majorantPackage
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) :
    ExplicitFormulaAffineKernelMajorantPackage
      (fun t : ℝ =>
        ((1 / 2 : ℂ) *
          Complex.GammaLogDerivativeFixedVerticalMain
            (F.c / 2) (t / 2)) *
          zetaCompletedExplicitFormulaPhi f
            (zetaCompletedExplicitFormulaRightCenteredAffineLine F t)) := by
  let A : ℝ → ℂ := fun t : ℝ =>
    (1 / 2 : ℂ) *
      Complex.GammaLogDerivativeFixedVerticalMain
        (F.c / 2) (t / 2)
  let B : ℝ :=
    ‖(1 / 2 : ℂ)‖ *
      ((|Real.log (F.c / 2)| + (F.c / 2 + 1) + Real.pi) +
        1 / (F.c / 2))
  have hσ : 0 < F.c / 2 :=
    div_pos F.c_pos zero_lt_two
  have hM_nonneg :
      0 ≤
        (|Real.log (F.c / 2)| + (F.c / 2 + 1) + Real.pi) +
          1 / (F.c / 2) :=
    Complex.GammaLogDerivativeFixedVerticalMainLinearConstant_nonneg hσ
  have hB_nonneg : 0 ≤ B :=
    mul_nonneg (norm_nonneg (1 / 2 : ℂ)) hM_nonneg
  have hscale : Measurable (fun t : ℝ => t / 2) :=
    measurable_id.div_const 2
  have hgamma :
      AEStronglyMeasurable
        (fun t : ℝ =>
          Complex.GammaLogDerivativeFixedVerticalMain (F.c / 2) (t / 2))
        (volume : Measure ℝ) :=
    (Complex.GammaLogDerivativeFixedVerticalMain_aestronglyMeasurable
      (F.c / 2)).comp_measurable hscale
  have hA_meas : AEStronglyMeasurable A (volume : Measure ℝ) :=
    hgamma.const_mul (1 / 2 : ℂ)
  have hA_bound : ∀ t : ℝ, ‖A t‖ ≤ B * (1 + ‖t‖) := by
    intro t
    exact
      zetaCompletedExplicitFormulaGammaLogDerivativeFixedVerticalMain_right_linear_bound
        F t
  exact
    zetaCompletedExplicitFormulaRightCenteredAffineProduct_majorantPackage_of_linear_factor_bound
      f F h A B hB_nonneg hA_meas hA_bound

/-- The right elementary correction component of the Binet main kernel has the
standard affine integrable majorant package. -/
theorem zetaCompletedExplicitFormulaCorrectionLogDerivative_rightKernel_majorantPackage
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) :
    ExplicitFormulaAffineKernelMajorantPackage
      (fun t : ℝ =>
        explicitFormulaCorrectionLogDerivative
          (zetaCompletedExplicitFormulaRightAffineLine F t) *
          zetaCompletedExplicitFormulaPhi f
            (zetaCompletedExplicitFormulaRightCenteredAffineLine F t)) := by
  let A : ℝ → ℂ := fun t : ℝ =>
    explicitFormulaCorrectionLogDerivative
      (zetaCompletedExplicitFormulaRightAffineLine F t)
  let B : ℝ := (1 : ℝ) / F.c + (1 : ℝ) / (F.c - 1)
  have hB_nonneg : 0 ≤ B :=
    add_nonneg
      (div_nonneg zero_le_one F.c_pos.le)
      (div_nonneg zero_le_one (sub_pos.mpr F.c_gt_one).le)
  have hA_meas : AEStronglyMeasurable A (volume : Measure ℝ) :=
    zetaCompletedExplicitFormulaCorrectionLogDerivative_rightAffineLine_aestronglyMeasurable
      F
  have hA_bound : ∀ t : ℝ, ‖A t‖ ≤ B * (1 + ‖t‖) :=
    zetaCompletedExplicitFormulaCorrectionLogDerivative_rightAffineLine_linear_bound
      F
  exact
    zetaCompletedExplicitFormulaRightCenteredAffineProduct_majorantPackage_of_linear_factor_bound
      f F h A B hB_nonneg hA_meas hA_bound

/-- The right Binet main factor has linear growth on the scheduled right
affine half-line. -/
theorem zetaCompletedExplicitFormulaArchimedeanRightBinetMainFactor_linear_bound
    (F : ExplicitFormulaContourFamily) :
    ∀ t : ℝ,
      ‖-(zetaCompletedExplicitFormulaGammaRealPiLogDerivativeTerm +
            (1 / 2 : ℂ) *
              Complex.GammaLogDerivativeFixedVerticalMain
                (F.c / 2) (t / 2)) -
          explicitFormulaCorrectionLogDerivative
            (zetaCompletedExplicitFormulaRightAffineLine F t)‖ ≤
        (‖zetaCompletedExplicitFormulaGammaRealPiLogDerivativeTerm‖ +
            ‖(1 / 2 : ℂ)‖ *
              ((|Real.log (F.c / 2)| + (F.c / 2 + 1) + Real.pi) +
                1 / (F.c / 2)) +
            ((1 : ℝ) / F.c + (1 : ℝ) / (F.c - 1))) *
          (1 + ‖t‖) := by
  intro t
  let P : ℂ := zetaCompletedExplicitFormulaGammaRealPiLogDerivativeTerm
  let G : ℂ :=
    (1 / 2 : ℂ) *
      Complex.GammaLogDerivativeFixedVerticalMain (F.c / 2) (t / 2)
  let C : ℂ :=
    explicitFormulaCorrectionLogDerivative
      (zetaCompletedExplicitFormulaRightAffineLine F t)
  let M : ℝ :=
    (|Real.log (F.c / 2)| + (F.c / 2 + 1) + Real.pi) +
      1 / (F.c / 2)
  let K : ℝ := (1 : ℝ) / F.c + (1 : ℝ) / (F.c - 1)
  have hσ : 0 < F.c / 2 :=
    div_pos F.c_pos zero_lt_two
  have hM_nonneg : 0 ≤ M :=
    Complex.GammaLogDerivativeFixedVerticalMainLinearConstant_nonneg hσ
  have hP_nonneg : 0 ≤ ‖P‖ :=
    norm_nonneg P
  have hhalf_nonneg : 0 ≤ ‖(1 / 2 : ℂ)‖ :=
    norm_nonneg (1 / 2 : ℂ)
  have hhalfM_nonneg : 0 ≤ ‖(1 / 2 : ℂ)‖ * M :=
    mul_nonneg hhalf_nonneg hM_nonneg
  have hK_nonneg : 0 ≤ K :=
    add_nonneg
      (div_nonneg zero_le_one F.c_pos.le)
      (div_nonneg zero_le_one (sub_pos.mpr F.c_gt_one).le)
  have hG_raw :
      ‖G‖ ≤ ‖(1 / 2 : ℂ)‖ * (M * (1 + ‖t / 2‖)) := by
    have hmain :
        ‖Complex.GammaLogDerivativeFixedVerticalMain
            (F.c / 2) (t / 2)‖ ≤
          M * (1 + ‖t / 2‖) :=
      Complex.GammaLogDerivativeFixedVerticalMain_polynomial_bound
        hσ (t / 2)
    calc
      ‖G‖ =
          ‖(1 / 2 : ℂ)‖ *
            ‖Complex.GammaLogDerivativeFixedVerticalMain
              (F.c / 2) (t / 2)‖ := by
        exact norm_mul (1 / 2 : ℂ)
          (Complex.GammaLogDerivativeFixedVerticalMain
            (F.c / 2) (t / 2))
      _ ≤ ‖(1 / 2 : ℂ)‖ * (M * (1 + ‖t / 2‖)) :=
        mul_le_mul_of_nonneg_left hmain hhalf_nonneg
  have hG :
      ‖G‖ ≤ (‖(1 / 2 : ℂ)‖ * M) * (1 + ‖t‖) := by
    have hweight :
        M * (1 + ‖t / 2‖) ≤ M * (1 + ‖t‖) :=
      mul_le_mul_of_nonneg_left
        (real_one_add_norm_div_two_le_one_add_norm t)
        hM_nonneg
    calc
      ‖G‖ ≤ ‖(1 / 2 : ℂ)‖ * (M * (1 + ‖t / 2‖)) :=
        hG_raw
      _ ≤ ‖(1 / 2 : ℂ)‖ * (M * (1 + ‖t‖)) :=
        mul_le_mul_of_nonneg_left hweight hhalf_nonneg
      _ = (‖(1 / 2 : ℂ)‖ * M) * (1 + ‖t‖) := by
        exact (mul_assoc ‖(1 / 2 : ℂ)‖ M (1 + ‖t‖)).symm
  have hP :
      ‖P‖ ≤ ‖P‖ * (1 + ‖t‖) :=
    real_nonneg_le_mul_one_add_norm hP_nonneg t
  have hC :
      ‖C‖ ≤ K * (1 + ‖t‖) :=
    zetaCompletedExplicitFormulaCorrectionLogDerivative_rightAffineLine_linear_bound
      F t
  have hsum :
      ‖P‖ + ‖G‖ + ‖C‖ ≤
        ‖P‖ * (1 + ‖t‖) +
          (‖(1 / 2 : ℂ)‖ * M) * (1 + ‖t‖) +
            K * (1 + ‖t‖) :=
    add_le_add (add_le_add hP hG) hC
  have hfactor :
      ‖P‖ * (1 + ‖t‖) +
          (‖(1 / 2 : ℂ)‖ * M) * (1 + ‖t‖) +
            K * (1 + ‖t‖) =
        (‖P‖ + ‖(1 / 2 : ℂ)‖ * M + K) * (1 + ‖t‖) := by
    calc
      ‖P‖ * (1 + ‖t‖) +
          (‖(1 / 2 : ℂ)‖ * M) * (1 + ‖t‖) +
            K * (1 + ‖t‖) =
        (‖P‖ + ‖(1 / 2 : ℂ)‖ * M) * (1 + ‖t‖) +
            K * (1 + ‖t‖) := by
          exact congrArg
            (fun x : ℝ => x + K * (1 + ‖t‖))
            (add_mul ‖P‖ (‖(1 / 2 : ℂ)‖ * M) (1 + ‖t‖)).symm
      _ = (‖P‖ + ‖(1 / 2 : ℂ)‖ * M + K) * (1 + ‖t‖) := by
          exact (add_mul (‖P‖ + ‖(1 / 2 : ℂ)‖ * M) K (1 + ‖t‖)).symm
  calc
    ‖-(P + G) - C‖ ≤ ‖-(P + G)‖ + ‖C‖ :=
      norm_sub_le (-(P + G)) C
    _ = ‖P + G‖ + ‖C‖ := by
      exact congrArg (fun x : ℝ => x + ‖C‖) (norm_neg (P + G))
    _ ≤ (‖P‖ + ‖G‖) + ‖C‖ := by
      have hpg : ‖P + G‖ ≤ ‖P‖ + ‖G‖ :=
        norm_add_le P G
      exact add_le_add_right hpg ‖C‖
    _ = ‖P‖ + ‖G‖ + ‖C‖ :=
      add_assoc ‖P‖ ‖G‖ ‖C‖
    _ ≤
        ‖P‖ * (1 + ‖t‖) +
          (‖(1 / 2 : ℂ)‖ * M) * (1 + ‖t‖) +
            K * (1 + ‖t‖) :=
      hsum
    _ =
        (‖P‖ + ‖(1 / 2 : ℂ)‖ * M + K) * (1 + ‖t‖) :=
      hfactor

/-- The right Binet remainder factor has linear growth on the scheduled
right affine half-line. -/
theorem zetaCompletedExplicitFormulaArchimedeanRightBinetRemainderFactor_linear_bound
    (F : ExplicitFormulaContourFamily) :
    ∀ t : ℝ,
      ‖-((1 / 2 : ℂ) *
          Complex.GammaLogDerivativeFixedVerticalRemainder
            (F.c / 2) (t / 2))‖ ≤
        (‖(1 / 2 : ℂ)‖ *
          |‖(2 : ℂ)‖ *
            ∫ u : ℝ in Set.Ioi (0 : ℝ),
              (1 / (F.c / 2) ^ 2) *
                (u / (Real.exp ((2 : ℝ) * Real.pi * u) - 1))|) *
          (1 + ‖t‖) := by
  intro t
  let C : ℝ :=
    |‖(2 : ℂ)‖ *
      ∫ u : ℝ in Set.Ioi (0 : ℝ),
        (1 / (F.c / 2) ^ 2) *
          (u / (Real.exp ((2 : ℝ) * Real.pi * u) - 1))|
  have hσ : 0 < F.c / 2 :=
    div_pos F.c_pos zero_lt_two
  have hR :
      ‖Complex.GammaLogDerivativeFixedVerticalRemainder
          (F.c / 2) (t / 2)‖ ≤
        C * (1 + ‖t / 2‖) :=
    Complex.GammaLogDerivativeFixedVerticalRemainder_linear_bound
      hσ (t / 2)
  have hC_nonneg : 0 ≤ C :=
    abs_nonneg
      (‖(2 : ℂ)‖ *
        ∫ u : ℝ in Set.Ioi (0 : ℝ),
          (1 / (F.c / 2) ^ 2) *
            (u / (Real.exp ((2 : ℝ) * Real.pi * u) - 1)))
  have hhalf_nonneg : 0 ≤ ‖(1 / 2 : ℂ)‖ :=
    norm_nonneg (1 / 2 : ℂ)
  have hweight :
      C * (1 + ‖t / 2‖) ≤ C * (1 + ‖t‖) :=
    mul_le_mul_of_nonneg_left
      (real_one_add_norm_div_two_le_one_add_norm t)
      hC_nonneg
  have hscaled :
      ‖(1 / 2 : ℂ)‖ *
          ‖Complex.GammaLogDerivativeFixedVerticalRemainder
            (F.c / 2) (t / 2)‖ ≤
        ‖(1 / 2 : ℂ)‖ * (C * (1 + ‖t‖)) :=
    mul_le_mul_of_nonneg_left (hR.trans hweight) hhalf_nonneg
  calc
    ‖-((1 / 2 : ℂ) *
        Complex.GammaLogDerivativeFixedVerticalRemainder
          (F.c / 2) (t / 2))‖ =
        ‖(1 / 2 : ℂ) *
          Complex.GammaLogDerivativeFixedVerticalRemainder
            (F.c / 2) (t / 2)‖ := by
      exact norm_neg
        ((1 / 2 : ℂ) *
          Complex.GammaLogDerivativeFixedVerticalRemainder
            (F.c / 2) (t / 2))
    _ =
        ‖(1 / 2 : ℂ)‖ *
          ‖Complex.GammaLogDerivativeFixedVerticalRemainder
            (F.c / 2) (t / 2)‖ := by
      exact norm_mul (1 / 2 : ℂ)
        (Complex.GammaLogDerivativeFixedVerticalRemainder
          (F.c / 2) (t / 2))
    _ ≤ ‖(1 / 2 : ℂ)‖ * (C * (1 + ‖t‖)) :=
      hscaled
    _ =
        (‖(1 / 2 : ℂ)‖ * C) * (1 + ‖t‖) := by
      exact (mul_assoc ‖(1 / 2 : ℂ)‖ C (1 + ‖t‖)).symm

/-- The right Binet main kernel has the standard affine integrable majorant
package. -/
theorem zetaCompletedExplicitFormulaArchimedeanRightBinetMainKernel_majorantPackage
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) :
    ExplicitFormulaAffineKernelMajorantPackage
      (zetaCompletedExplicitFormulaArchimedeanRightBinetMainKernel f F) := by
  let A : ℝ → ℂ := fun t : ℝ =>
    -(zetaCompletedExplicitFormulaGammaRealPiLogDerivativeTerm +
        (1 / 2 : ℂ) *
          Complex.GammaLogDerivativeFixedVerticalMain
            (F.c / 2) (t / 2)) -
      explicitFormulaCorrectionLogDerivative
        (zetaCompletedExplicitFormulaRightAffineLine F t)
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
  have hA_meas :
      AEStronglyMeasurable A (volume : Measure ℝ) :=
    zetaCompletedExplicitFormulaArchimedeanRightBinetMainFactor_aestronglyMeasurable
      F
  have hA_bound : ∀ t : ℝ, ‖A t‖ ≤ B * (1 + ‖t‖) :=
    zetaCompletedExplicitFormulaArchimedeanRightBinetMainFactor_linear_bound
      F
  exact
    zetaCompletedExplicitFormulaRightCenteredAffineProduct_majorantPackage_of_linear_factor_bound
      f F h A B hB_nonneg hA_meas hA_bound

/-- Half of the right affine line is the fixed-vertical line with real part
`F.c / 2` and height `t / 2`. -/
theorem zetaCompletedExplicitFormulaRightAffineLine_div_two_eq_fixedVertical
    (F : ExplicitFormulaContourFamily) (t : ℝ) :
    zetaCompletedExplicitFormulaRightAffineLine F t / 2 =
      ((F.c / 2 : ℝ) + (t / 2 : ℝ) * Complex.I : ℂ) := by
  calc
    zetaCompletedExplicitFormulaRightAffineLine F t / 2 =
        ((F.c : ℂ) + t * Complex.I) / 2 := by
      exact congrArg (fun z : ℂ => z / 2)
        (zetaCompletedExplicitFormulaRightAffineLine_eq F t)
    _ = ((F.c : ℂ) / 2) + (t * Complex.I) / 2 := by
      exact add_div ((F.c : ℂ)) (t * Complex.I) (2 : ℂ)
    _ = (F.c / 2 : ℂ) + (t * Complex.I) / 2 := by
      exact congrArg
        (fun z : ℂ => z + (t * Complex.I) / 2)
        (Complex.ofReal_div F.c 2)
    _ = (F.c / 2 : ℂ) + ((t / 2 : ℝ) : ℂ) * Complex.I := by
      have ht :
          (t * Complex.I) / 2 = ((t / 2 : ℝ) : ℂ) * Complex.I := by
        calc
          (t * Complex.I) / 2 =
              ((t : ℂ) / 2) * Complex.I := by
            exact (div_mul_eq_mul_div (t : ℂ) Complex.I (2 : ℂ)).symm
          _ = ((t / 2 : ℝ) : ℂ) * Complex.I := by
            exact congrArg (fun z : ℂ => z * Complex.I)
              (Complex.ofReal_div t 2)
      exact congrArg (fun z : ℂ => (F.c / 2 : ℂ) + z) ht
    _ = ((F.c / 2 : ℝ) + (t / 2 : ℝ) * Complex.I : ℂ) := by
      rfl

/-- Half of the left affine line is the fixed-vertical line with real part
`(1 - F.c) / 2` and height `t / 2`. -/
theorem zetaCompletedExplicitFormulaLeftAffineLine_div_two_eq_fixedVertical
    (F : ExplicitFormulaContourFamily) (t : ℝ) :
    zetaCompletedExplicitFormulaLeftAffineLine F t / 2 =
      (((1 - F.c) / 2 : ℝ) + (t / 2 : ℝ) * Complex.I : ℂ) := by
  calc
    zetaCompletedExplicitFormulaLeftAffineLine F t / 2 =
        (((1 : ℂ) - (F.c : ℂ)) + t * Complex.I) / 2 := by
      exact congrArg (fun z : ℂ => z / 2)
        (zetaCompletedExplicitFormulaLeftAffineLine_eq F t)
    _ = (((1 : ℂ) - (F.c : ℂ)) / 2) + (t * Complex.I) / 2 := by
      exact add_div (((1 : ℂ) - (F.c : ℂ))) (t * Complex.I) (2 : ℂ)
    _ = ((1 - F.c) / 2 : ℂ) + (t * Complex.I) / 2 := by
      have hreal :
          (((1 : ℂ) - (F.c : ℂ)) / 2) =
            (((1 - F.c) / 2 : ℝ) : ℂ) := by
        calc
          (((1 : ℂ) - (F.c : ℂ)) / 2) =
              (((1 - F.c : ℝ) : ℂ) / 2) := by
            rfl
          _ = (((1 - F.c) / 2 : ℝ) : ℂ) := by
            exact Complex.ofReal_div (1 - F.c) 2
      exact congrArg
        (fun z : ℂ => z + (t * Complex.I) / 2)
        hreal
    _ = ((1 - F.c) / 2 : ℂ) + ((t / 2 : ℝ) : ℂ) * Complex.I := by
      have ht :
          (t * Complex.I) / 2 = ((t / 2 : ℝ) : ℂ) * Complex.I := by
        calc
          (t * Complex.I) / 2 =
              ((t : ℂ) / 2) * Complex.I := by
            exact (div_mul_eq_mul_div (t : ℂ) Complex.I (2 : ℂ)).symm
          _ = ((t / 2 : ℝ) : ℂ) * Complex.I := by
            exact congrArg (fun z : ℂ => z * Complex.I)
              (Complex.ofReal_div t 2)
      exact congrArg (fun z : ℂ => ((1 - F.c) / 2 : ℂ) + z) ht
    _ = (((1 - F.c) / 2 : ℝ) + (t / 2 : ℝ) * Complex.I : ℂ) := by
      rfl

/-- The fixed-vertical form of the left half-line avoids the ordinary Gamma
pole locus whenever the left affine line satisfies the completed-Gamma
regularity condition. -/
theorem zetaCompletedExplicitFormulaLeftFixedVertical_ne_Gamma_zero_locus_of_gammaRegular
    (F : ExplicitFormulaContourFamily)
    (hregular : zetaCompletedExplicitFormulaLeftAffineLineGammaRegular F)
    (t : ℝ) :
    ∀ n : ℕ,
      (((1 - F.c) / 2 : ℝ) + (t / 2 : ℝ) * Complex.I : ℂ) ≠
        -(n : ℂ) := by
  intro n hn
  have hline :
      zetaCompletedExplicitFormulaLeftAffineLine F t / 2 =
        (((1 - F.c) / 2 : ℝ) + (t / 2 : ℝ) * Complex.I : ℂ) :=
    zetaCompletedExplicitFormulaLeftAffineLine_div_two_eq_fixedVertical F t
  exact
    (zetaCompletedExplicitFormulaLeftAffineLine_half_ne_Gamma_zero_locus_of_gammaRegular
      F hregular t n)
      (hline.trans hn)

/-- The left fixed-vertical half-line avoids ordinary Gamma poles for every
Binet height parameter.  This is the same pole-avoidance statement as above,
with the affine parameter rescaled by `2`. -/
theorem zetaCompletedExplicitFormulaLeftFixedVertical_ne_Gamma_zero_locus_of_gammaRegular'
    (F : ExplicitFormulaContourFamily)
    (hregular : zetaCompletedExplicitFormulaLeftAffineLineGammaRegular F)
    (τ : ℝ) :
    ∀ n : ℕ,
      (((1 - F.c) / 2 : ℝ) + τ * Complex.I : ℂ) ≠
        -(n : ℂ) := by
  intro n hn
  have hraw :
      (((1 - F.c) / 2 : ℝ) + ((2 * τ) / 2 : ℝ) * Complex.I : ℂ) ≠
        -(n : ℂ) :=
    zetaCompletedExplicitFormulaLeftFixedVertical_ne_Gamma_zero_locus_of_gammaRegular
      F hregular (2 * τ) n
  have hτ : (2 * τ) / 2 = τ := by
    exact mul_div_cancel_left₀ τ (show (2 : ℝ) ≠ 0 from two_ne_zero)
  have hline :
      (((1 - F.c) / 2 : ℝ) + ((2 * τ) / 2 : ℝ) * Complex.I : ℂ) =
        (((1 - F.c) / 2 : ℝ) + τ * Complex.I : ℂ) := by
    exact congrArg
      (fun x : ℝ => (((1 - F.c) / 2 : ℝ) + x * Complex.I : ℂ))
      hτ
  exact hraw (hline.trans hn)

/-- The left finite-shift Binet main factor has linear growth on the scheduled
left affine half-line, provided the left line avoids Gamma poles. -/
theorem zetaCompletedExplicitFormulaArchimedeanLeftBinetMainFactor_linear_bound
    (F : ExplicitFormulaContourFamily)
    (hregular : zetaCompletedExplicitFormulaLeftAffineLineGammaRegular F) :
    ∀ t : ℝ,
      ‖-(zetaCompletedExplicitFormulaGammaRealPiLogDerivativeTerm +
            (1 / 2 : ℂ) *
              Complex.GammaLogDerivativeFixedVerticalShiftNatMain
                ((1 - F.c) / 2)
                (zetaCompletedExplicitFormulaArchimedeanLeftBinetShiftNat F)
                (t / 2)) -
          explicitFormulaCorrectionLogDerivative
            (zetaCompletedExplicitFormulaLeftAffineLine F t)‖ ≤
        (‖zetaCompletedExplicitFormulaGammaRealPiLogDerivativeTerm‖ +
            ‖(1 / 2 : ℂ)‖ *
              Complex.GammaLogDerivativeFixedVerticalShiftNatMainLinearConstant
                ((1 - F.c) / 2)
                (zetaCompletedExplicitFormulaArchimedeanLeftBinetShiftNat F) +
            ((1 : ℝ) / (-(1 - F.c)) +
              (1 : ℝ) / (-((1 - F.c) - 1)))) *
          (1 + ‖t‖) := by
  intro t
  let σ : ℝ := (1 - F.c) / 2
  let N : ℕ := zetaCompletedExplicitFormulaArchimedeanLeftBinetShiftNat F
  let P : ℂ := zetaCompletedExplicitFormulaGammaRealPiLogDerivativeTerm
  let G : ℂ :=
    (1 / 2 : ℂ) *
      Complex.GammaLogDerivativeFixedVerticalShiftNatMain σ N (t / 2)
  let C : ℂ :=
    explicitFormulaCorrectionLogDerivative
      (zetaCompletedExplicitFormulaLeftAffineLine F t)
  let M : ℝ :=
    Complex.GammaLogDerivativeFixedVerticalShiftNatMainLinearConstant σ N
  let K : ℝ :=
    (1 : ℝ) / (-(1 - F.c)) +
      (1 : ℝ) / (-((1 - F.c) - 1))
  have hshift_pos : 0 < σ + (N : ℝ) :=
    Complex.GammaLogDerivativeFixedVerticalPositiveShiftNat_pos σ
  have hnot_pole :
      ∀ τ : ℝ, ∀ n : ℕ,
        (σ + τ * Complex.I : ℂ) ≠ -n :=
    zetaCompletedExplicitFormulaLeftFixedVertical_ne_Gamma_zero_locus_of_gammaRegular'
      F hregular
  have hM_nonneg : 0 ≤ M :=
    Complex.GammaLogDerivativeFixedVerticalShiftNatMainLinearConstant_nonneg
      N hshift_pos
  have hP_nonneg : 0 ≤ ‖P‖ :=
    norm_nonneg P
  have hhalf_nonneg : 0 ≤ ‖(1 / 2 : ℂ)‖ :=
    norm_nonneg (1 / 2 : ℂ)
  have hzero_den_pos : 0 < -(1 - F.c) :=
    neg_pos.mpr F.one_sub_c_neg
  have hone_den_pos : 0 < -((1 - F.c) - 1) := by
    have hneg : (1 - F.c) - 1 < 0 := by
      calc
        (1 - F.c) - 1 < 0 - 1 := by
          exact sub_lt_sub_right F.one_sub_c_neg 1
        _ < 0 := by
          exact neg_lt_zero.mpr zero_lt_one
    exact neg_pos.mpr hneg
  have hK_nonneg : 0 ≤ K :=
    add_nonneg
      (div_nonneg zero_le_one hzero_den_pos.le)
      (div_nonneg zero_le_one hone_den_pos.le)
  have hG_raw :
      ‖G‖ ≤ ‖(1 / 2 : ℂ)‖ * (M * (1 + ‖t / 2‖)) := by
    have hmain :
        ‖Complex.GammaLogDerivativeFixedVerticalShiftNatMain
            σ N (t / 2)‖ ≤
          M * (1 + ‖t / 2‖) :=
      Complex.GammaLogDerivativeFixedVerticalShiftNatMain_linear_bound
        N hshift_pos hnot_pole (t / 2)
    calc
      ‖G‖ =
          ‖(1 / 2 : ℂ)‖ *
            ‖Complex.GammaLogDerivativeFixedVerticalShiftNatMain
              σ N (t / 2)‖ := by
        exact norm_mul (1 / 2 : ℂ)
          (Complex.GammaLogDerivativeFixedVerticalShiftNatMain
            σ N (t / 2))
      _ ≤ ‖(1 / 2 : ℂ)‖ * (M * (1 + ‖t / 2‖)) :=
        mul_le_mul_of_nonneg_left hmain hhalf_nonneg
  have hG :
      ‖G‖ ≤ (‖(1 / 2 : ℂ)‖ * M) * (1 + ‖t‖) := by
    have hweight :
        M * (1 + ‖t / 2‖) ≤ M * (1 + ‖t‖) :=
      mul_le_mul_of_nonneg_left
        (real_one_add_norm_div_two_le_one_add_norm t)
        hM_nonneg
    calc
      ‖G‖ ≤ ‖(1 / 2 : ℂ)‖ * (M * (1 + ‖t / 2‖)) :=
        hG_raw
      _ ≤ ‖(1 / 2 : ℂ)‖ * (M * (1 + ‖t‖)) :=
        mul_le_mul_of_nonneg_left hweight hhalf_nonneg
      _ = (‖(1 / 2 : ℂ)‖ * M) * (1 + ‖t‖) := by
        exact (mul_assoc ‖(1 / 2 : ℂ)‖ M (1 + ‖t‖)).symm
  have hP :
      ‖P‖ ≤ ‖P‖ * (1 + ‖t‖) :=
    real_nonneg_le_mul_one_add_norm hP_nonneg t
  have hC :
      ‖C‖ ≤ K * (1 + ‖t‖) :=
    zetaCompletedExplicitFormulaCorrectionLogDerivative_leftAffineLine_linear_bound
      F t
  have hsum :
      ‖P‖ + ‖G‖ + ‖C‖ ≤
        ‖P‖ * (1 + ‖t‖) +
          (‖(1 / 2 : ℂ)‖ * M) * (1 + ‖t‖) +
            K * (1 + ‖t‖) :=
    add_le_add (add_le_add hP hG) hC
  have hfactor :
      ‖P‖ * (1 + ‖t‖) +
          (‖(1 / 2 : ℂ)‖ * M) * (1 + ‖t‖) +
            K * (1 + ‖t‖) =
        (‖P‖ + ‖(1 / 2 : ℂ)‖ * M + K) * (1 + ‖t‖) := by
    calc
      ‖P‖ * (1 + ‖t‖) +
          (‖(1 / 2 : ℂ)‖ * M) * (1 + ‖t‖) +
            K * (1 + ‖t‖) =
        (‖P‖ + ‖(1 / 2 : ℂ)‖ * M) * (1 + ‖t‖) +
            K * (1 + ‖t‖) := by
          exact congrArg
            (fun x : ℝ => x + K * (1 + ‖t‖))
            (add_mul ‖P‖ (‖(1 / 2 : ℂ)‖ * M) (1 + ‖t‖)).symm
      _ = (‖P‖ + ‖(1 / 2 : ℂ)‖ * M + K) * (1 + ‖t‖) := by
          exact (add_mul (‖P‖ + ‖(1 / 2 : ℂ)‖ * M) K (1 + ‖t‖)).symm
  calc
    ‖-(P + G) - C‖ ≤ ‖-(P + G)‖ + ‖C‖ :=
      norm_sub_le (-(P + G)) C
    _ = ‖P + G‖ + ‖C‖ := by
      exact congrArg (fun x : ℝ => x + ‖C‖) (norm_neg (P + G))
    _ ≤ (‖P‖ + ‖G‖) + ‖C‖ := by
      have hpg : ‖P + G‖ ≤ ‖P‖ + ‖G‖ :=
        norm_add_le P G
      exact add_le_add_right hpg ‖C‖
    _ = ‖P‖ + ‖G‖ + ‖C‖ :=
      add_assoc ‖P‖ ‖G‖ ‖C‖
    _ ≤
        ‖P‖ * (1 + ‖t‖) +
          (‖(1 / 2 : ℂ)‖ * M) * (1 + ‖t‖) +
            K * (1 + ‖t‖) :=
      hsum
    _ =
        (‖P‖ + ‖(1 / 2 : ℂ)‖ * M + K) * (1 + ‖t‖) :=
      hfactor

/-- The left finite-shift Binet remainder factor has linear growth on the
scheduled left affine half-line, provided the left line avoids Gamma poles. -/
theorem zetaCompletedExplicitFormulaArchimedeanLeftBinetRemainderFactor_linear_bound
    (F : ExplicitFormulaContourFamily)
    (hregular : zetaCompletedExplicitFormulaLeftAffineLineGammaRegular F) :
    ∀ t : ℝ,
      ‖-((1 / 2 : ℂ) *
          Complex.GammaLogDerivativeFixedVerticalShiftNatRemainder
            ((1 - F.c) / 2)
            (zetaCompletedExplicitFormulaArchimedeanLeftBinetShiftNat F)
            (t / 2))‖ ≤
        (‖(1 / 2 : ℂ)‖ *
          Complex.GammaLogDerivativeFixedVerticalShiftNatRemainderLinearConstant
            ((1 - F.c) / 2)
            (zetaCompletedExplicitFormulaArchimedeanLeftBinetShiftNat F)) *
          (1 + ‖t‖) := by
  intro t
  let σ : ℝ := (1 - F.c) / 2
  let N : ℕ := zetaCompletedExplicitFormulaArchimedeanLeftBinetShiftNat F
  let C : ℝ :=
    Complex.GammaLogDerivativeFixedVerticalShiftNatRemainderLinearConstant σ N
  have hshift_pos : 0 < σ + (N : ℝ) :=
    Complex.GammaLogDerivativeFixedVerticalPositiveShiftNat_pos σ
  have hnot_pole :
      ∀ τ : ℝ, ∀ n : ℕ,
        (σ + τ * Complex.I : ℂ) ≠ -n :=
    zetaCompletedExplicitFormulaLeftFixedVertical_ne_Gamma_zero_locus_of_gammaRegular'
      F hregular
  have hR :
      ‖Complex.GammaLogDerivativeFixedVerticalShiftNatRemainder
          σ N (t / 2)‖ ≤
        C * (1 + ‖t / 2‖) :=
    Complex.GammaLogDerivativeFixedVerticalShiftNatRemainder_linear_bound
      N hshift_pos hnot_pole (t / 2)
  have hC_nonneg : 0 ≤ C :=
    Complex.GammaLogDerivativeFixedVerticalShiftNatRemainderLinearConstant_nonneg
      σ N
  have hhalf_nonneg : 0 ≤ ‖(1 / 2 : ℂ)‖ :=
    norm_nonneg (1 / 2 : ℂ)
  have hweight :
      C * (1 + ‖t / 2‖) ≤ C * (1 + ‖t‖) :=
    mul_le_mul_of_nonneg_left
      (real_one_add_norm_div_two_le_one_add_norm t)
      hC_nonneg
  have hscaled :
      ‖(1 / 2 : ℂ)‖ *
          ‖Complex.GammaLogDerivativeFixedVerticalShiftNatRemainder
            σ N (t / 2)‖ ≤
        ‖(1 / 2 : ℂ)‖ * (C * (1 + ‖t‖)) :=
    mul_le_mul_of_nonneg_left (hR.trans hweight) hhalf_nonneg
  calc
    ‖-((1 / 2 : ℂ) *
        Complex.GammaLogDerivativeFixedVerticalShiftNatRemainder
          σ N (t / 2))‖ =
        ‖(1 / 2 : ℂ) *
          Complex.GammaLogDerivativeFixedVerticalShiftNatRemainder
            σ N (t / 2)‖ := by
      exact norm_neg
        ((1 / 2 : ℂ) *
          Complex.GammaLogDerivativeFixedVerticalShiftNatRemainder
            σ N (t / 2))
    _ =
        ‖(1 / 2 : ℂ)‖ *
          ‖Complex.GammaLogDerivativeFixedVerticalShiftNatRemainder
            σ N (t / 2)‖ := by
      exact norm_mul (1 / 2 : ℂ)
        (Complex.GammaLogDerivativeFixedVerticalShiftNatRemainder
          σ N (t / 2))
    _ ≤ ‖(1 / 2 : ℂ)‖ * (C * (1 + ‖t‖)) :=
      hscaled
    _ = (‖(1 / 2 : ℂ)‖ * C) * (1 + ‖t‖) := by
      exact (mul_assoc ‖(1 / 2 : ℂ)‖ C (1 + ‖t‖)).symm

/-- The right Binet remainder kernel has the standard affine integrable
majorant package. -/
theorem zetaCompletedExplicitFormulaArchimedeanRightBinetRemainderKernel_majorantPackage
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) :
    ExplicitFormulaAffineKernelMajorantPackage
      (zetaCompletedExplicitFormulaArchimedeanRightBinetRemainderKernel f F) := by
  let A : ℝ → ℂ := fun t : ℝ =>
    -((1 / 2 : ℂ) *
      Complex.GammaLogDerivativeFixedVerticalRemainder
        (F.c / 2) (t / 2))
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
              (u / (Real.exp ((2 : ℝ) * Real.pi * u) - 1))))
  have hA_meas :
      AEStronglyMeasurable A (volume : Measure ℝ) :=
    zetaCompletedExplicitFormulaArchimedeanRightBinetRemainderFactor_aestronglyMeasurable
      F
  have hA_bound : ∀ t : ℝ, ‖A t‖ ≤ B * (1 + ‖t‖) :=
    zetaCompletedExplicitFormulaArchimedeanRightBinetRemainderFactor_linear_bound
      F
  exact
    zetaCompletedExplicitFormulaRightCenteredAffineProduct_majorantPackage_of_linear_factor_bound
      f F h A B hB_nonneg hA_meas hA_bound

/-- The left Binet remainder kernel has the standard affine integrable
majorant package, once the left line is known Gamma-regular. -/
theorem zetaCompletedExplicitFormulaArchimedeanLeftBinetRemainderKernel_majorantPackage
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F)
    (hregular : zetaCompletedExplicitFormulaLeftAffineLineGammaRegular F) :
    ExplicitFormulaAffineKernelMajorantPackage
      (zetaCompletedExplicitFormulaArchimedeanLeftBinetRemainderKernel f F) := by
  let A : ℝ → ℂ := fun t : ℝ =>
    -((1 / 2 : ℂ) *
      Complex.GammaLogDerivativeFixedVerticalShiftNatRemainder
        ((1 - F.c) / 2)
        (zetaCompletedExplicitFormulaArchimedeanLeftBinetShiftNat F)
        (t / 2))
  let B : ℝ :=
    ‖(1 / 2 : ℂ)‖ *
      Complex.GammaLogDerivativeFixedVerticalShiftNatRemainderLinearConstant
        ((1 - F.c) / 2)
        (zetaCompletedExplicitFormulaArchimedeanLeftBinetShiftNat F)
  have hB_nonneg : 0 ≤ B :=
    mul_nonneg
      (norm_nonneg (1 / 2 : ℂ))
      (Complex.GammaLogDerivativeFixedVerticalShiftNatRemainderLinearConstant_nonneg
        ((1 - F.c) / 2)
        (zetaCompletedExplicitFormulaArchimedeanLeftBinetShiftNat F))
  have hA_meas :
      AEStronglyMeasurable A (volume : Measure ℝ) :=
    zetaCompletedExplicitFormulaArchimedeanLeftBinetRemainderFactor_aestronglyMeasurable
      F
  have hA_bound : ∀ t : ℝ, ‖A t‖ ≤ B * (1 + ‖t‖) :=
    zetaCompletedExplicitFormulaArchimedeanLeftBinetRemainderFactor_linear_bound
      F hregular
  exact
    zetaCompletedExplicitFormulaLeftCenteredAffineProduct_majorantPackage_of_linear_factor_bound
      f F h A B hB_nonneg hA_meas hA_bound

/-- The left Binet main kernel has the standard affine integrable majorant
package, once the left line is Gamma-regular. -/
theorem zetaCompletedExplicitFormulaArchimedeanLeftBinetMainKernel_majorantPackage
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F)
    (hregular : zetaCompletedExplicitFormulaLeftAffineLineGammaRegular F) :
    ExplicitFormulaAffineKernelMajorantPackage
      (zetaCompletedExplicitFormulaArchimedeanLeftBinetMainKernel f F) := by
  let A : ℝ → ℂ := fun t : ℝ =>
    -(zetaCompletedExplicitFormulaGammaRealPiLogDerivativeTerm +
        (1 / 2 : ℂ) *
          Complex.GammaLogDerivativeFixedVerticalShiftNatMain
            ((1 - F.c) / 2)
            (zetaCompletedExplicitFormulaArchimedeanLeftBinetShiftNat F)
            (t / 2)) -
      explicitFormulaCorrectionLogDerivative
        (zetaCompletedExplicitFormulaLeftAffineLine F t)
  let B : ℝ :=
    ‖zetaCompletedExplicitFormulaGammaRealPiLogDerivativeTerm‖ +
      ‖(1 / 2 : ℂ)‖ *
        Complex.GammaLogDerivativeFixedVerticalShiftNatMainLinearConstant
          ((1 - F.c) / 2)
          (zetaCompletedExplicitFormulaArchimedeanLeftBinetShiftNat F) +
      ((1 : ℝ) / (-(1 - F.c)) +
        (1 : ℝ) / (-((1 - F.c) - 1)))
  let σ : ℝ := (1 - F.c) / 2
  let N : ℕ := zetaCompletedExplicitFormulaArchimedeanLeftBinetShiftNat F
  have hshift_pos : 0 < σ + (N : ℝ) :=
    Complex.GammaLogDerivativeFixedVerticalPositiveShiftNat_pos σ
  have hM_nonneg :
      0 ≤
        Complex.GammaLogDerivativeFixedVerticalShiftNatMainLinearConstant
          σ N :=
    Complex.GammaLogDerivativeFixedVerticalShiftNatMainLinearConstant_nonneg
      N hshift_pos
  have hzero_den_pos : 0 < -(1 - F.c) :=
    neg_pos.mpr F.one_sub_c_neg
  have hone_den_pos : 0 < -((1 - F.c) - 1) := by
    have hneg : (1 - F.c) - 1 < 0 := by
      calc
        (1 - F.c) - 1 < 0 - 1 := by
          exact sub_lt_sub_right F.one_sub_c_neg 1
        _ < 0 := by
          exact neg_lt_zero.mpr zero_lt_one
    exact neg_pos.mpr hneg
  have hB_nonneg : 0 ≤ B :=
    add_nonneg
      (add_nonneg
        (norm_nonneg zetaCompletedExplicitFormulaGammaRealPiLogDerivativeTerm)
        (mul_nonneg (norm_nonneg (1 / 2 : ℂ)) hM_nonneg))
      (add_nonneg
        (div_nonneg zero_le_one hzero_den_pos.le)
        (div_nonneg zero_le_one hone_den_pos.le))
  have hA_meas :
      AEStronglyMeasurable A (volume : Measure ℝ) :=
    zetaCompletedExplicitFormulaArchimedeanLeftBinetMainFactor_aestronglyMeasurable
      F
  have hA_bound : ∀ t : ℝ, ‖A t‖ ≤ B * (1 + ‖t‖) :=
    zetaCompletedExplicitFormulaArchimedeanLeftBinetMainFactor_linear_bound
      F hregular
  exact
    zetaCompletedExplicitFormulaLeftCenteredAffineProduct_majorantPackage_of_linear_factor_bound
      f F h A B hB_nonneg hA_meas hA_bound

/-- Full-line integrability of the right Binet main kernel. -/
theorem zetaCompletedExplicitFormulaArchimedeanRightBinetMainKernel_integrable
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) :
    Integrable
      (zetaCompletedExplicitFormulaArchimedeanRightBinetMainKernel f F)
      (volume : Measure ℝ) :=
  (zetaCompletedExplicitFormulaArchimedeanRightBinetMainKernel_majorantPackage
    f F h).integrable

/-- Full-line integrability of the left Binet main kernel. -/
theorem zetaCompletedExplicitFormulaArchimedeanLeftBinetMainKernel_integrable
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F)
    (hregular : zetaCompletedExplicitFormulaLeftAffineLineGammaRegular F) :
    Integrable
      (zetaCompletedExplicitFormulaArchimedeanLeftBinetMainKernel f F)
      (volume : Measure ℝ) :=
  (zetaCompletedExplicitFormulaArchimedeanLeftBinetMainKernel_majorantPackage
    f F h hregular).integrable

/-- Restricted-window integrability of the right Binet main kernel. -/
theorem zetaCompletedExplicitFormulaArchimedeanRightBinetMainKernel_integrable_restrict_Icc
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F)
    (a b : ℝ) :
    Integrable
      (zetaCompletedExplicitFormulaArchimedeanRightBinetMainKernel f F)
      (volume.restrict (Set.Icc a b)) :=
  (zetaCompletedExplicitFormulaArchimedeanRightBinetMainKernel_integrable
    f F h).mono_measure Measure.restrict_le_self

/-- Restricted-window integrability of the left Binet main kernel. -/
theorem zetaCompletedExplicitFormulaArchimedeanLeftBinetMainKernel_integrable_restrict_Icc
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F)
    (hregular : zetaCompletedExplicitFormulaLeftAffineLineGammaRegular F)
    (a b : ℝ) :
    Integrable
      (zetaCompletedExplicitFormulaArchimedeanLeftBinetMainKernel f F)
      (volume.restrict (Set.Icc a b)) :=
  (zetaCompletedExplicitFormulaArchimedeanLeftBinetMainKernel_integrable
    f F h hregular).mono_measure Measure.restrict_le_self

/-- Full-line integrability of the right Binet remainder kernel. -/
theorem zetaCompletedExplicitFormulaArchimedeanRightBinetRemainderKernel_integrable
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) :
    Integrable
      (zetaCompletedExplicitFormulaArchimedeanRightBinetRemainderKernel f F)
      (volume : Measure ℝ) :=
  (zetaCompletedExplicitFormulaArchimedeanRightBinetRemainderKernel_majorantPackage
    f F h).integrable

/-- Full-line integrability of the left Binet remainder kernel. -/
theorem zetaCompletedExplicitFormulaArchimedeanLeftBinetRemainderKernel_integrable
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F)
    (hregular : zetaCompletedExplicitFormulaLeftAffineLineGammaRegular F) :
    Integrable
      (zetaCompletedExplicitFormulaArchimedeanLeftBinetRemainderKernel f F)
      (volume : Measure ℝ) :=
  (zetaCompletedExplicitFormulaArchimedeanLeftBinetRemainderKernel_majorantPackage
    f F h hregular).integrable

/-- Restricted-window integrability of the right Binet remainder kernel. -/
theorem zetaCompletedExplicitFormulaArchimedeanRightBinetRemainderKernel_integrable_restrict_Icc
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F)
    (a b : ℝ) :
    Integrable
      (zetaCompletedExplicitFormulaArchimedeanRightBinetRemainderKernel f F)
      (volume.restrict (Set.Icc a b)) :=
  (zetaCompletedExplicitFormulaArchimedeanRightBinetRemainderKernel_integrable
    f F h).mono_measure Measure.restrict_le_self

/-- Restricted-window integrability of the left Binet remainder kernel. -/
theorem zetaCompletedExplicitFormulaArchimedeanLeftBinetRemainderKernel_integrable_restrict_Icc
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F)
    (hregular : zetaCompletedExplicitFormulaLeftAffineLineGammaRegular F)
    (a b : ℝ) :
    Integrable
      (zetaCompletedExplicitFormulaArchimedeanLeftBinetRemainderKernel f F)
      (volume.restrict (Set.Icc a b)) :=
  (zetaCompletedExplicitFormulaArchimedeanLeftBinetRemainderKernel_integrable
    f F h hregular).mono_measure Measure.restrict_le_self
end ZetaAdmissibleFunction

end
end LFunctions
end Boundary
