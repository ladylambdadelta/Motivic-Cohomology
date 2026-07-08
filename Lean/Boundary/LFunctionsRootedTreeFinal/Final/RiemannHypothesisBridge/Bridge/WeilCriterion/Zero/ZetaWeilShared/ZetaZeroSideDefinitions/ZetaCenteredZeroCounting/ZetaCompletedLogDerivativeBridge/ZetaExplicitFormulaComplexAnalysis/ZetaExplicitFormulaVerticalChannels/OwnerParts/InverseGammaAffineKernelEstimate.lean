import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaExplicitFormulaVerticalChannels.OwnerParts.AffineKernelMajorantPackage
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaExplicitFormulaVerticalChannels.OwnerParts.AffineLineMeasurability
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaExplicitFormulaVerticalChannels.OwnerParts.AffinePhiDecay
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaExplicitFormulaVerticalChannels.OwnerParts.InverseGammaFactorBounds
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaExplicitFormulaVerticalChannels.OwnerParts.ScheduledKernelLimitTransport
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaExplicitFormulaVerticalChannels.OwnerParts.SymmetricIntegralExhaustion
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ClassicalAnalysis.GammaBinetStirling.Owner

/-!
# Inverse-Gamma affine-kernel estimate

This file owns the analytic convergence of the right-minus-left inverse-Gamma
completion affine-kernel integrals.
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

/-- Strong measurability of the right inverse-Gamma affine kernel. -/
theorem zetaCompletedExplicitFormulaInverseGammaRightAffineKernel_aestronglyMeasurable
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) :
    AEStronglyMeasurable
      (zetaCompletedExplicitFormulaInverseGammaRightAffineKernel f F)
      (volume : Measure ℝ) :=
  (zetaCompletedExplicitFormulaInverseGammaLogDeriv_rightAffineLine_aestronglyMeasurable
    F).mul
    (zetaCompletedExplicitFormulaPhi_rightCenteredAffineLine_aestronglyMeasurable
      f F h)

/-- Under the parameter-level Gamma-regularity condition, the left
inverse-Gamma affine kernel is strongly measurable. -/
theorem zetaCompletedExplicitFormulaInverseGammaLeftAffineKernel_aestronglyMeasurable_of_gammaRegular
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F)
    (hregular : zetaCompletedExplicitFormulaLeftAffineLineGammaRegular F) :
    AEStronglyMeasurable
      (zetaCompletedExplicitFormulaInverseGammaLeftAffineKernel f F)
      (volume : Measure ℝ) :=
  (zetaCompletedExplicitFormulaInverseGammaLogDeriv_leftAffineLine_aestronglyMeasurable_of_gammaRegular
    F hregular).mul
    (zetaCompletedExplicitFormulaPhi_leftCenteredAffineLine_aestronglyMeasurable
      f F h)

/-- A polynomial bound for the inverse-Gamma logarithmic-derivative factor on
the left affine line packages the left inverse-Gamma affine kernel.  The
Gamma/Stirling owner layer is responsible for the pointwise factor bound; this
theorem owns the vertical-channel multiplication with the rapidly decaying test
transform. -/
theorem zetaCompletedExplicitFormulaInverseGammaLeftAffineKernel_majorantPackage_of_factor_bound
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F)
    (hregular : zetaCompletedExplicitFormulaLeftAffineLineGammaRegular F)
    (B : ℝ)
    (hB_nonneg : 0 ≤ B)
    (hfactor_bound :
      ∀ t : ℝ,
        ‖inverseGammaCompletionLogDeriv
            (zetaCompletedExplicitFormulaLeftAffineLine F t)‖ ≤
          B * (1 + ‖t‖)) :
    ExplicitFormulaAffineKernelMajorantPackage
      (zetaCompletedExplicitFormulaInverseGammaLeftAffineKernel f F) := by
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
    have hfinrank : Module.finrank ℝ ℝ = 1 :=
      Module.finrank_self ℝ
    have hfinrank_cast : ((Module.finrank ℝ ℝ : ℕ) : ℝ) = 1 :=
      congrArg (fun n : ℕ => (n : ℝ)) hfinrank
    have hdim : (Module.finrank ℝ ℝ : ℝ) < 3 :=
      Eq.subst
        (motive := fun x : ℝ => x < 3)
        hfinrank_cast.symm
        (lt_trans one_lt_two two_lt_three)
    have hbase :
        Integrable
          (fun t : ℝ => (1 + ‖t‖) ^ (-(3 : ℝ)))
          (volume : Measure ℝ) :=
      integrable_one_add_norm (E := ℝ) hdim
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
    exact Eq.subst
      (motive := fun φ : ℝ → ℝ => Integrable φ (volume : Measure ℝ))
      hfun.symm
      hscaled
  have hfactor_meas :
      AEStronglyMeasurable
        (fun t : ℝ =>
          inverseGammaCompletionLogDeriv
            (zetaCompletedExplicitFormulaLeftAffineLine F t))
        (volume : Measure ℝ) :=
    zetaCompletedExplicitFormulaInverseGammaLogDeriv_leftAffineLine_aestronglyMeasurable_of_gammaRegular
      F hregular
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
        ‖inverseGammaCompletionLogDeriv
            (zetaCompletedExplicitFormulaLeftAffineLine F t)‖ *
            ‖zetaCompletedExplicitFormulaPhi f
              (zetaCompletedExplicitFormulaLeftCenteredAffineLine F t)‖ ≤
          majorant t :=
    Filter.Eventually.of_forall
      (fun t : ℝ =>
        let weight : ℝ := (1 + ‖t‖) ^ (-(3 : ℤ))
        have hfactor :
            ‖inverseGammaCompletionLogDeriv
                (zetaCompletedExplicitFormulaLeftAffineLine F t)‖ ≤
              B * (1 + ‖t‖) :=
          hfactor_bound t
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
            ‖inverseGammaCompletionLogDeriv
                (zetaCompletedExplicitFormulaLeftAffineLine F t)‖ *
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
                exact
                  congrArg (fun x : ℝ => B * (x * b))
                    (mul_comm a C)
              _ = B * (C * (a * b)) := by
                exact congrArg (fun x : ℝ => B * x) (mul_assoc C a b)
              _ = B * C * (a * b) := by
                exact (mul_assoc B C (a * b)).symm
          have hrewrite :
              a * b = (1 + ‖t‖) ^ (-(3 : ℤ)) :=
            hweight
          exact
            Eq.trans hscalar
              (congrArg (fun x : ℝ => B * C * x) hrewrite)
        hprod.trans_eq hassoc)
  exact
    ExplicitFormulaAffineKernelMajorantPackage.of_mul_le
      majorant hintegrable hfactor_meas hphi_meas hbound

/-- A left-line bound for the ordinary `Gammaℝ` logarithmic derivative gives a
left-line bound for the inverse-Gamma completion logarithmic derivative. -/
theorem zetaCompletedExplicitFormulaInverseGammaCompletionLogDeriv_leftAffineLine_bound_of_Gammaℝ_logDeriv_bound
    (F : ExplicitFormulaContourFamily)
    (hregular : zetaCompletedExplicitFormulaLeftAffineLineGammaRegular F)
    (B : ℝ)
    (hGamma_bound :
      ∀ t : ℝ,
        ‖deriv Gammaℝ (zetaCompletedExplicitFormulaLeftAffineLine F t) /
            Gammaℝ (zetaCompletedExplicitFormulaLeftAffineLine F t)‖ ≤
          B * (1 + ‖t‖)) :
    ∀ t : ℝ,
      ‖inverseGammaCompletionLogDeriv
          (zetaCompletedExplicitFormulaLeftAffineLine F t)‖ ≤
        B * (1 + ‖t‖) := by
  exact
    zetaCompletedExplicitFormulaInverseGammaCompletionLogDeriv_leftAffineLine_bound_of_Gammaℝ_logDeriv_bound_owner
      F hregular B hGamma_bound

/-- A left-line bound for the ordinary Gamma logarithmic derivative at the half
argument gives a left-line bound for the inverse-Gamma completion logarithmic
derivative. -/
theorem zetaCompletedExplicitFormulaInverseGammaCompletionLogDeriv_leftAffineLine_bound_of_halfGamma_logDeriv_bound
    (F : ExplicitFormulaContourFamily)
    (hregular : zetaCompletedExplicitFormulaLeftAffineLineGammaRegular F)
    (B : ℝ)
    (hB_nonneg : 0 ≤ B)
    (hGamma_bound :
      ∀ t : ℝ,
        ‖(deriv Complex.Gamma
              (zetaCompletedExplicitFormulaLeftAffineLine F t / 2) *
            (1 / 2 : ℂ)) /
            Complex.Gamma
              (zetaCompletedExplicitFormulaLeftAffineLine F t / 2)‖ ≤
          B * (1 + ‖t‖)) :
    ∃ C : ℝ,
      0 ≤ C ∧
        ∀ t : ℝ,
          ‖inverseGammaCompletionLogDeriv
              (zetaCompletedExplicitFormulaLeftAffineLine F t)‖ ≤
            C * (1 + ‖t‖) := by
  exact
    zetaCompletedExplicitFormulaInverseGammaCompletionLogDeriv_leftAffineLine_bound_of_halfGamma_logDeriv_bound_owner
      F hregular B hB_nonneg hGamma_bound

/-- A left-line bound for the ordinary `Gammaℝ` logarithmic derivative packages
the left inverse-Gamma affine kernel. -/
theorem zetaCompletedExplicitFormulaInverseGammaLeftAffineKernel_majorantPackage_of_Gammaℝ_logDeriv_bound
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F)
    (hregular : zetaCompletedExplicitFormulaLeftAffineLineGammaRegular F)
    (B : ℝ)
    (hB_nonneg : 0 ≤ B)
    (hGamma_bound :
      ∀ t : ℝ,
        ‖deriv Gammaℝ (zetaCompletedExplicitFormulaLeftAffineLine F t) /
            Gammaℝ (zetaCompletedExplicitFormulaLeftAffineLine F t)‖ ≤
          B * (1 + ‖t‖)) :
    ExplicitFormulaAffineKernelMajorantPackage
      (zetaCompletedExplicitFormulaInverseGammaLeftAffineKernel f F) := by
  have hfactor_bound :
      ∀ t : ℝ,
        ‖inverseGammaCompletionLogDeriv
            (zetaCompletedExplicitFormulaLeftAffineLine F t)‖ ≤
          B * (1 + ‖t‖) := by
    zetaCompletedExplicitFormulaInverseGammaCompletionLogDeriv_leftAffineLine_bound_of_Gammaℝ_logDeriv_bound
      F hregular B hGamma_bound
  exact
    zetaCompletedExplicitFormulaInverseGammaLeftAffineKernel_majorantPackage_of_factor_bound
      f F h hregular B hB_nonneg hfactor_bound

/-- A left-line bound for the ordinary Gamma logarithmic derivative at the
half argument gives the left inverse-Gamma affine-kernel majorant package. -/
theorem zetaCompletedExplicitFormulaInverseGammaLeftAffineKernel_majorantPackage_of_halfGamma_logDeriv_bound
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F)
    (hregular : zetaCompletedExplicitFormulaLeftAffineLineGammaRegular F)
    (B : ℝ)
    (hB_nonneg : 0 ≤ B)
    (hGamma_bound :
      ∀ t : ℝ,
        ‖(deriv Complex.Gamma
              (zetaCompletedExplicitFormulaLeftAffineLine F t / 2) *
            (1 / 2 : ℂ)) /
            Complex.Gamma
              (zetaCompletedExplicitFormulaLeftAffineLine F t / 2)‖ ≤
          B * (1 + ‖t‖)) :
    ExplicitFormulaAffineKernelMajorantPackage
      (zetaCompletedExplicitFormulaInverseGammaLeftAffineKernel f F) := by
  match
    zetaCompletedExplicitFormulaInverseGammaCompletionLogDeriv_leftAffineLine_bound_of_halfGamma_logDeriv_bound
      F hregular B hB_nonneg hGamma_bound with
  | ⟨C, hC_nonneg, hfactor_bound⟩ =>
      exact
        zetaCompletedExplicitFormulaInverseGammaLeftAffineKernel_majorantPackage_of_factor_bound
          f F h hregular C hC_nonneg hfactor_bound

/-- A polynomial bound for the inverse-Gamma logarithmic-derivative factor on
the right affine line packages the right inverse-Gamma affine kernel.  The
Gamma/Stirling owner layer is responsible for supplying the pointwise factor
bound; this theorem owns only the vertical-channel multiplication with the
rapidly decaying test transform. -/
theorem zetaCompletedExplicitFormulaInverseGammaRightAffineKernel_majorantPackage_of_factor_bound
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F)
    (B : ℝ)
    (hB_nonneg : 0 ≤ B)
    (hfactor_bound :
      ∀ t : ℝ,
        ‖inverseGammaCompletionLogDeriv
            (zetaCompletedExplicitFormulaRightAffineLine F t)‖ ≤
          B * (1 + ‖t‖)) :
    ExplicitFormulaAffineKernelMajorantPackage
      (zetaCompletedExplicitFormulaInverseGammaRightAffineKernel f F) := by
  let C : ℝ :=
    h.phi_control.verticalStripRapidDecayConstant
      (F.c - (1 / 2 : ℝ)) (F.c - (1 / 2 : ℝ)) 4
  let majorant : ℝ → ℝ := fun t : ℝ => B * C * (1 + ‖t‖) ^ (-(3 : ℤ))
  have hC_nonneg : 0 ≤ C :=
    h.phi_control.verticalStripRapidDecayConstant_nonneg
      (F.c - (1 / 2 : ℝ)) (F.c - (1 / 2 : ℝ)) 4
  have hintegrable :
      Integrable majorant (volume : Measure ℝ) := by
    have hfinrank : Module.finrank ℝ ℝ = 1 :=
      Module.finrank_self ℝ
    have hfinrank_cast : ((Module.finrank ℝ ℝ : ℕ) : ℝ) = 1 :=
      congrArg (fun n : ℕ => (n : ℝ)) hfinrank
    have hdim : (Module.finrank ℝ ℝ : ℝ) < 3 :=
      Eq.subst
        (motive := fun x : ℝ => x < 3)
        hfinrank_cast.symm
        (lt_trans one_lt_two two_lt_three)
    have hbase :
        Integrable
          (fun t : ℝ => (1 + ‖t‖) ^ (-(3 : ℝ)))
          (volume : Measure ℝ) :=
      integrable_one_add_norm (E := ℝ) hdim
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
    exact Eq.subst
      (motive := fun φ : ℝ → ℝ => Integrable φ (volume : Measure ℝ))
      hfun.symm
      hscaled
  have hfactor_meas :
      AEStronglyMeasurable
        (fun t : ℝ =>
          inverseGammaCompletionLogDeriv
            (zetaCompletedExplicitFormulaRightAffineLine F t))
        (volume : Measure ℝ) :=
    zetaCompletedExplicitFormulaInverseGammaLogDeriv_rightAffineLine_aestronglyMeasurable
      F
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
        ‖inverseGammaCompletionLogDeriv
            (zetaCompletedExplicitFormulaRightAffineLine F t)‖ *
            ‖zetaCompletedExplicitFormulaPhi f
              (zetaCompletedExplicitFormulaRightCenteredAffineLine F t)‖ ≤
          majorant t :=
    Filter.Eventually.of_forall
      (fun t : ℝ =>
        let weight : ℝ := (1 + ‖t‖) ^ (-(3 : ℤ))
        have hfactor :
            ‖inverseGammaCompletionLogDeriv
                (zetaCompletedExplicitFormulaRightAffineLine F t)‖ ≤
              B * (1 + ‖t‖) :=
          hfactor_bound t
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
        have hright_nonneg : 0 ≤ C * (1 + ‖t‖) ^ (-(4 : ℤ)) :=
          mul_nonneg hC_nonneg (zpow_nonneg (Real.zero_le_one_add_norm t) _)
        have hfactor_rhs_nonneg : 0 ≤ B * (1 + ‖t‖) :=
          mul_nonneg hB_nonneg (Real.zero_le_one_add_norm t)
        have hprod :
            ‖inverseGammaCompletionLogDeriv
                (zetaCompletedExplicitFormulaRightAffineLine F t)‖ *
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
                exact
                  congrArg (fun x : ℝ => B * (x * b))
                    (mul_comm a C)
              _ = B * (C * (a * b)) := by
                exact congrArg (fun x : ℝ => B * x) (mul_assoc C a b)
              _ = B * C * (a * b) :=
                (mul_assoc B C (a * b)).symm
          calc
            (B * (1 + ‖t‖)) *
                (C * (1 + ‖t‖) ^ (-(4 : ℤ))) =
                B * C *
                  ((1 + ‖t‖) * (1 + ‖t‖) ^ (-(4 : ℤ))) :=
              hscalar
            _ = B * C * (1 + ‖t‖) ^ (-(3 : ℤ)) :=
              congrArg (fun x : ℝ => B * C * x) hweight
        hprod.trans_eq hassoc)
  exact
    ExplicitFormulaAffineKernelMajorantPackage.of_mul_le
      majorant hintegrable hfactor_meas hphi_meas hbound

/-- A right-line bound for the ordinary `Gammaℝ` logarithmic derivative
packages the right inverse-Gamma affine kernel. -/
theorem zetaCompletedExplicitFormulaInverseGammaRightAffineKernel_majorantPackage_of_Gammaℝ_logDeriv_bound
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F)
    (B : ℝ)
    (hB_nonneg : 0 ≤ B)
    (hGamma_bound :
      ∀ t : ℝ,
        ‖deriv Gammaℝ (zetaCompletedExplicitFormulaRightAffineLine F t) /
            Gammaℝ (zetaCompletedExplicitFormulaRightAffineLine F t)‖ ≤
          B * (1 + ‖t‖)) :
    ExplicitFormulaAffineKernelMajorantPackage
      (zetaCompletedExplicitFormulaInverseGammaRightAffineKernel f F) := by
  have hfactor_bound :
      ∀ t : ℝ,
        ‖inverseGammaCompletionLogDeriv
            (zetaCompletedExplicitFormulaRightAffineLine F t)‖ ≤
          B * (1 + ‖t‖) := by
    intro t
    have hidentity :
        inverseGammaCompletionLogDeriv
            (zetaCompletedExplicitFormulaRightAffineLine F t) =
          -deriv Gammaℝ (zetaCompletedExplicitFormulaRightAffineLine F t) /
            Gammaℝ (zetaCompletedExplicitFormulaRightAffineLine F t) :=
      zetaCompletedExplicitFormulaInverseGammaLogDeriv_rightAffineLine_eq_neg_Gammaℝ_logDeriv
        F t
    have hnorm :
        ‖inverseGammaCompletionLogDeriv
            (zetaCompletedExplicitFormulaRightAffineLine F t)‖ =
          ‖deriv Gammaℝ (zetaCompletedExplicitFormulaRightAffineLine F t) /
            Gammaℝ (zetaCompletedExplicitFormulaRightAffineLine F t)‖ := by
      calc
        ‖inverseGammaCompletionLogDeriv
            (zetaCompletedExplicitFormulaRightAffineLine F t)‖ =
            ‖-deriv Gammaℝ (zetaCompletedExplicitFormulaRightAffineLine F t) /
              Gammaℝ (zetaCompletedExplicitFormulaRightAffineLine F t)‖ := by
          exact congrArg norm hidentity
        _ =
            ‖-(deriv Gammaℝ (zetaCompletedExplicitFormulaRightAffineLine F t) /
              Gammaℝ (zetaCompletedExplicitFormulaRightAffineLine F t))‖ := by
          exact congrArg norm
            (neg_div
              (Gammaℝ (zetaCompletedExplicitFormulaRightAffineLine F t))
              (deriv Gammaℝ (zetaCompletedExplicitFormulaRightAffineLine F t)))
        _ =
            ‖deriv Gammaℝ (zetaCompletedExplicitFormulaRightAffineLine F t) /
              Gammaℝ (zetaCompletedExplicitFormulaRightAffineLine F t)‖ :=
          norm_neg
            (deriv Gammaℝ (zetaCompletedExplicitFormulaRightAffineLine F t) /
              Gammaℝ (zetaCompletedExplicitFormulaRightAffineLine F t))
    exact
      Eq.subst
        (motive := fun x : ℝ => x ≤ B * (1 + ‖t‖))
        hnorm.symm
        (hGamma_bound t)
  exact
    zetaCompletedExplicitFormulaInverseGammaRightAffineKernel_majorantPackage_of_factor_bound
      f F h B hB_nonneg hfactor_bound

/-- A right-line bound for the ordinary Gamma logarithmic derivative at the
half argument gives the right inverse-Gamma affine-kernel majorant package. -/
theorem zetaCompletedExplicitFormulaInverseGammaRightAffineKernel_majorantPackage_of_halfGamma_logDeriv_bound
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F)
    (B : ℝ)
    (hB_nonneg : 0 ≤ B)
    (hGamma_bound :
      ∀ t : ℝ,
        ‖(deriv Complex.Gamma
              (zetaCompletedExplicitFormulaRightAffineLine F t / 2) *
            (1 / 2 : ℂ)) /
            Complex.Gamma
              (zetaCompletedExplicitFormulaRightAffineLine F t / 2)‖ ≤
          B * (1 + ‖t‖)) :
    ExplicitFormulaAffineKernelMajorantPackage
      (zetaCompletedExplicitFormulaInverseGammaRightAffineKernel f F) := by
  let A : ℝ := ‖Complex.log (Real.pi : ℂ) * (-(1 / 2 : ℂ))‖
  let C : ℝ := A + B
  have hA_nonneg : 0 ≤ A :=
    norm_nonneg (Complex.log (Real.pi : ℂ) * (-(1 / 2 : ℂ)))
  have hC_nonneg : 0 ≤ C :=
    add_nonneg hA_nonneg hB_nonneg
  have hGammaℝ_bound :
      ∀ t : ℝ,
        ‖deriv Gammaℝ (zetaCompletedExplicitFormulaRightAffineLine F t) /
            Gammaℝ (zetaCompletedExplicitFormulaRightAffineLine F t)‖ ≤
          C * (1 + ‖t‖) := by
    intro t
    let Q : ℂ :=
      (deriv Complex.Gamma
          (zetaCompletedExplicitFormulaRightAffineLine F t / 2) *
        (1 / 2 : ℂ)) /
        Complex.Gamma
          (zetaCompletedExplicitFormulaRightAffineLine F t / 2)
    have hdecomp :
        deriv Gammaℝ (zetaCompletedExplicitFormulaRightAffineLine F t) /
            Gammaℝ (zetaCompletedExplicitFormulaRightAffineLine F t) =
          Complex.log (Real.pi : ℂ) * (-(1 / 2 : ℂ)) + Q :=
      zetaCompletedExplicitFormulaRightAffineLine_Gammaℝ_logDeriv_eq F t
    have hnorm_split :
        ‖deriv Gammaℝ (zetaCompletedExplicitFormulaRightAffineLine F t) /
            Gammaℝ (zetaCompletedExplicitFormulaRightAffineLine F t)‖ ≤
          A + ‖Q‖ := by
      have htriangle :
          ‖Complex.log (Real.pi : ℂ) * (-(1 / 2 : ℂ)) + Q‖ ≤
            ‖Complex.log (Real.pi : ℂ) * (-(1 / 2 : ℂ))‖ + ‖Q‖ :=
        norm_add_le (Complex.log (Real.pi : ℂ) * (-(1 / 2 : ℂ))) Q
      exact
        Eq.subst
          (motive := fun x : ℂ => ‖x‖ ≤ A + ‖Q‖)
          hdecomp.symm
          htriangle
    have hQ_bound :
        ‖Q‖ ≤ B * (1 + ‖t‖) :=
      hGamma_bound t
    have hA_bound :
        A ≤ A * (1 + ‖t‖) := by
      calc
        A = A * 1 := by
          exact (mul_one A).symm
        _ ≤ A * (1 + ‖t‖) := by
          exact mul_le_mul_of_nonneg_left
            (Real.one_le_one_add_norm t) hA_nonneg
    have hsum_bound :
        A + ‖Q‖ ≤ A * (1 + ‖t‖) + B * (1 + ‖t‖) :=
      add_le_add hA_bound hQ_bound
    have hfactor :
        A * (1 + ‖t‖) + B * (1 + ‖t‖) =
          C * (1 + ‖t‖) :=
      (add_mul A B (1 + ‖t‖)).symm
    exact hnorm_split.trans (hsum_bound.trans_eq hfactor)
  exact
    zetaCompletedExplicitFormulaInverseGammaRightAffineKernel_majorantPackage_of_Gammaℝ_logDeriv_bound
      f F h C hC_nonneg hGammaℝ_bound

/-- The conditional fixed-line Binet logarithmic-derivative estimate gives the
right inverse-Gamma affine-kernel majorant once the Gamma coherence package has
been constructed.  This is the exact bridge from the classical Gamma owner
layer to the vertical-channel owner layer. -/
theorem zetaCompletedExplicitFormulaInverseGammaRightAffineKernel_majorantPackage_of_gammaBinetCoherence
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F)
    (hcoh : Complex.gammaBinetPrincipalLogCoherence) :
    ExplicitFormulaAffineKernelMajorantPackage
      (zetaCompletedExplicitFormulaInverseGammaRightAffineKernel f F) := by
  match
    zetaCompletedExplicitFormulaInverseGammaCompletionLogDeriv_rightAffineLine_bound_of_gammaBinetCoherence_owner
      F hcoh with
  | ⟨B, hB_nonneg, hfactor_bound⟩ =>
      exact
        zetaCompletedExplicitFormulaInverseGammaRightAffineKernel_majorantPackage_of_factor_bound
          f F h B hB_nonneg hfactor_bound

/-- A finite shifted fixed-line Gamma estimate gives the left inverse-Gamma
affine-kernel majorant, provided the left half-line is Gamma-regular and the
chosen natural shift reaches the positive half-plane. -/
theorem zetaCompletedExplicitFormulaInverseGammaCompletionLogDeriv_leftAffineLine_bound_of_gammaBinetCoherence_shift
    (F : ExplicitFormulaContourFamily)
    (hregular : zetaCompletedExplicitFormulaLeftAffineLineGammaRegular F)
    (hcoh : Complex.gammaBinetPrincipalLogCoherence)
    (N : ℕ)
    (hshift_pos : 0 < ((1 - F.c) / 2 : ℝ) + (N : ℝ)) :
    ∃ B : ℝ,
      0 ≤ B ∧
        ∀ t : ℝ,
          ‖inverseGammaCompletionLogDeriv
              (zetaCompletedExplicitFormulaLeftAffineLine F t)‖ ≤
            B * (1 + ‖t‖) := by
  exact
    zetaCompletedExplicitFormulaInverseGammaCompletionLogDeriv_leftAffineLine_bound_of_gammaBinetCoherence_shift_owner
      F hregular hcoh N hshift_pos

/-- The Gamma/Stirling fixed-line estimates give a linear left-line bound for
the inverse-Gamma completion logarithmic derivative under the natural
left-half-line Gamma-regularity condition. -/
theorem zetaCompletedExplicitFormulaInverseGammaCompletionLogDeriv_leftAffineLine_bound_of_gammaBinetCoherence
    (F : ExplicitFormulaContourFamily)
    (hregular : zetaCompletedExplicitFormulaLeftAffineLineGammaRegular F)
    (hcoh : Complex.gammaBinetPrincipalLogCoherence) :
    ∃ B : ℝ,
      0 ≤ B ∧
        ∀ t : ℝ,
          ‖inverseGammaCompletionLogDeriv
              (zetaCompletedExplicitFormulaLeftAffineLine F t)‖ ≤
            B * (1 + ‖t‖) := by
  exact
    zetaCompletedExplicitFormulaInverseGammaCompletionLogDeriv_leftAffineLine_bound_of_gammaBinetCoherence_owner
      F hregular hcoh

theorem zetaCompletedExplicitFormulaInverseGammaLeftAffineKernel_majorantPackage_of_gammaBinetCoherence_shift
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F)
    (hregular : zetaCompletedExplicitFormulaLeftAffineLineGammaRegular F)
    (hcoh : Complex.gammaBinetPrincipalLogCoherence)
    (N : ℕ)
    (hshift_pos : 0 < ((1 - F.c) / 2 : ℝ) + (N : ℝ)) :
    ExplicitFormulaAffineKernelMajorantPackage
      (zetaCompletedExplicitFormulaInverseGammaLeftAffineKernel f F) := by
  let σ : ℝ := (1 - F.c) / 2
  let D : ℝ :=
    Complex.GammaLogDerivativeFixedVerticalShiftConstant σ N
  let B : ℝ := ‖(1 / 2 : ℂ)‖ * |D|
  have hB_nonneg : 0 ≤ B :=
    mul_nonneg
      (norm_nonneg (1 / 2 : ℂ))
      (abs_nonneg D)
  have hhalf_line :
      ∀ t : ℝ,
        zetaCompletedExplicitFormulaLeftAffineLine F t / 2 =
          (σ + (t / 2) * Complex.I : ℂ) := by
    intro t
    calc
      zetaCompletedExplicitFormulaLeftAffineLine F t / 2 =
          (((1 : ℂ) - (F.c : ℂ)) + t * Complex.I) / 2 := by
        exact congrArg (fun z : ℂ => z / 2)
          (zetaCompletedExplicitFormulaLeftAffineLine_eq F t)
      _ = (((1 : ℂ) - (F.c : ℂ)) / 2) + (t * Complex.I) / 2 := by
        exact add_div (((1 : ℂ) - (F.c : ℂ))) (t * Complex.I) (2 : ℂ)
      _ = (σ + (t / 2) * Complex.I : ℂ) := by
        have hc :
            (((1 : ℂ) - (F.c : ℂ)) / 2) = (σ : ℂ) := by
          calc
            (((1 : ℂ) - (F.c : ℂ)) / 2) =
                (((1 - F.c : ℝ) : ℂ) / 2) := by
              exact congrArg (fun z : ℂ => z / 2)
                (Complex.ofReal_sub 1 F.c).symm
            _ = (((1 - F.c) / 2 : ℝ) : ℂ) := by
              exact Complex.ofReal_div (1 - F.c) 2
            _ = (σ : ℂ) := by
              exact Eq.refl _
        have ht :
            (t * Complex.I) / 2 = ((t / 2 : ℝ) : ℂ) * Complex.I := by
          calc
            (t * Complex.I) / 2 =
                ((t : ℂ) / 2) * Complex.I := by
              exact (div_mul_eq_mul_div (t : ℂ) Complex.I (2 : ℂ)).symm
            _ = ((t / 2 : ℝ) : ℂ) * Complex.I := by
              exact congrArg (fun z : ℂ => z * Complex.I)
                (Complex.ofReal_div t 2)
        exact congrArg₂ HAdd.hAdd hc ht
  have hnot_pole :
      ∀ u : ℝ, ∀ n : ℕ,
        (σ + u * Complex.I : ℂ) ≠ -n := by
    intro u n hpole
    have hline :
        zetaCompletedExplicitFormulaLeftAffineLine F (2 * u) / 2 =
          (σ + u * Complex.I : ℂ) := by
      have hraw :
          zetaCompletedExplicitFormulaLeftAffineLine F (2 * u) / 2 =
            (σ + ((2 * u) / 2) * Complex.I : ℂ) :=
        hhalf_line (2 * u)
      have hheight :
          ((2 * u) / 2 : ℝ) = u := by
        exact mul_div_cancel_left₀ u
          (show (2 : ℝ) ≠ 0 from two_ne_zero)
      exact
        hraw.trans
          (congrArg (fun x : ℝ => (σ + x * Complex.I : ℂ)) hheight)
    exact
      (zetaCompletedExplicitFormulaLeftAffineLine_half_ne_Gamma_zero_locus_of_gammaRegular
        F hregular (2 * u) n)
      (hline.trans hpole)
  have hfixed_bound :
      ∀ u : ℝ,
        ‖deriv Complex.Gamma (σ + u * Complex.I) /
            Complex.Gamma (σ + u * Complex.I)‖ ≤
          D * (1 + ‖u‖) :=
    Complex.Gamma_logDerivative_fixedRealPartLine_linear_bound_of_shift_nat
      hcoh N hshift_pos hnot_pole
  have hgamma_bound :
      ∀ t : ℝ,
        ‖(deriv Complex.Gamma
              (zetaCompletedExplicitFormulaLeftAffineLine F t / 2) *
            (1 / 2 : ℂ)) /
            Complex.Gamma
              (zetaCompletedExplicitFormulaLeftAffineLine F t / 2)‖ ≤
          B * (1 + ‖t‖) := by
    intro t
    let z : ℂ := zetaCompletedExplicitFormulaLeftAffineLine F t / 2
    let q : ℂ := deriv Complex.Gamma z / Complex.Gamma z
    have hline : z = (σ + (t / 2) * Complex.I : ℂ) :=
      hhalf_line t
    have hfixed :
        ‖deriv Complex.Gamma (σ + (t / 2) * Complex.I) /
            Complex.Gamma (σ + (t / 2) * Complex.I)‖ ≤
          D * (1 + ‖t / 2‖) :=
      hfixed_bound (t / 2)
    have hfixed_abs :
        ‖deriv Complex.Gamma (σ + (t / 2) * Complex.I) /
            Complex.Gamma (σ + (t / 2) * Complex.I)‖ ≤
          |D| * (1 + ‖t / 2‖) := by
      have hfactor_nonneg : 0 ≤ 1 + ‖t / 2‖ :=
        Real.zero_le_one_add_norm (t / 2)
      have hD_le_abs : D ≤ |D| :=
        le_abs_self D
      have hright :
          D * (1 + ‖t / 2‖) ≤ |D| * (1 + ‖t / 2‖) :=
        mul_le_mul_of_nonneg_right hD_le_abs hfactor_nonneg
      exact hfixed.trans hright
    have hsmall :
        1 + ‖t / 2‖ ≤ 1 + ‖t‖ := by
      have hnorm :
          ‖t / 2‖ ≤ ‖t‖ := by
        calc
          ‖t / 2‖ = ‖t‖ / ‖(2 : ℝ)‖ := by
            exact norm_div t (2 : ℝ)
          _ ≤ ‖t‖ := by
            have htwo_norm : (1 : ℝ) ≤ ‖(2 : ℝ)‖ := by
              have htwo_nonneg : (0 : ℝ) ≤ 2 :=
                zero_le_two
              have htwo_norm_eq : ‖(2 : ℝ)‖ = (2 : ℝ) :=
                norm_of_nonneg htwo_nonneg
              exact
                Eq.subst
                  (motive := fun x : ℝ => (1 : ℝ) ≤ x)
                  htwo_norm_eq.symm
                  one_le_two
            exact div_le_self (norm_nonneg t) htwo_norm
      exact add_le_add_left hnorm 1
    have hfixed_big :
        ‖deriv Complex.Gamma (σ + (t / 2) * Complex.I) /
            Complex.Gamma (σ + (t / 2) * Complex.I)‖ ≤
          |D| * (1 + ‖t‖) :=
      hfixed_abs.trans
        (mul_le_mul_of_nonneg_left hsmall (abs_nonneg D))
    have hq_bound :
        ‖q‖ ≤ |D| * (1 + ‖t‖) := by
      exact
        Eq.subst
          (motive := fun w : ℂ => ‖w‖ ≤ |D| * (1 + ‖t‖))
          (congrArg
            (fun w : ℂ => deriv Complex.Gamma w / Complex.Gamma w)
            hline).symm
          hfixed_big
    have halgebra :
        (deriv Complex.Gamma z * (1 / 2 : ℂ)) / Complex.Gamma z =
          q * (1 / 2 : ℂ) := by
      calc
        (deriv Complex.Gamma z * (1 / 2 : ℂ)) / Complex.Gamma z =
            (deriv Complex.Gamma z / Complex.Gamma z) * (1 / 2 : ℂ) := by
          exact (mul_div_right_comm
            (deriv Complex.Gamma z) (1 / 2 : ℂ) (Complex.Gamma z)).symm
        _ = q * (1 / 2 : ℂ) := by
          exact Eq.refl _
    have hnorm_mul :
        ‖(deriv Complex.Gamma z * (1 / 2 : ℂ)) / Complex.Gamma z‖ ≤
          B * (1 + ‖t‖) := by
      have hmul_norm :
          ‖q * (1 / 2 : ℂ)‖ = ‖q‖ * ‖(1 / 2 : ℂ)‖ :=
        norm_mul q (1 / 2 : ℂ)
      have hprod :
          ‖q‖ * ‖(1 / 2 : ℂ)‖ ≤
            (|D| * (1 + ‖t‖)) * ‖(1 / 2 : ℂ)‖ :=
        mul_le_mul_of_nonneg_right hq_bound
          (norm_nonneg (1 / 2 : ℂ))
      have hcomm :
          (|D| * (1 + ‖t‖)) * ‖(1 / 2 : ℂ)‖ =
            B * (1 + ‖t‖) := by
        calc
          (|D| * (1 + ‖t‖)) * ‖(1 / 2 : ℂ)‖ =
              (‖(1 / 2 : ℂ)‖ * |D|) * (1 + ‖t‖) := by
            exact Eq.trans
              (mul_assoc |D| (1 + ‖t‖) ‖(1 / 2 : ℂ)‖)
              (congrArg (fun x : ℝ => x * (1 + ‖t‖))
                (mul_comm |D| ‖(1 / 2 : ℂ)‖))
          _ = B * (1 + ‖t‖) := by
            exact Eq.refl _
      exact
        Eq.subst
          (motive := fun x : ℝ => x ≤ B * (1 + ‖t‖))
          hmul_norm.symm
          (hprod.trans_eq hcomm)
    exact
      Eq.subst
        (motive := fun w : ℂ => ‖w‖ ≤ B * (1 + ‖t‖))
        halgebra.symm
        hnorm_mul
  exact
    zetaCompletedExplicitFormulaInverseGammaLeftAffineKernel_majorantPackage_of_halfGamma_logDeriv_bound
      f F h hregular B hB_nonneg hgamma_bound

/-- The Gamma/Stirling fixed-line estimates give the left inverse-Gamma
affine-kernel majorant under the natural left-half-line Gamma-regularity
condition.  The natural shift is chosen by Archimedeanness of `ℝ`. -/
theorem zetaCompletedExplicitFormulaInverseGammaLeftAffineKernel_majorantPackage_of_gammaBinetCoherence
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F)
    (hregular : zetaCompletedExplicitFormulaLeftAffineLineGammaRegular F)
    (hcoh : Complex.gammaBinetPrincipalLogCoherence) :
    ExplicitFormulaAffineKernelMajorantPackage
      (zetaCompletedExplicitFormulaInverseGammaLeftAffineKernel f F) := by
  let σ : ℝ := (1 - F.c) / 2
  match exists_nat_ge (1 - σ) with
  | ⟨N, hN⟩ =>
      have hone_le_shift : 1 ≤ σ + (N : ℝ) := by
        have hleft :
            σ + (1 - σ) = (1 : ℝ) := by
          calc
            σ + (1 - σ) = σ + (1 + -σ) := by
              exact congrArg (fun x : ℝ => σ + x) (sub_eq_add_neg 1 σ)
            _ = (σ + 1) + -σ := by
              exact (add_assoc σ 1 (-σ)).symm
            _ = (σ + -σ) + 1 := by
              exact add_right_comm σ 1 (-σ)
            _ = 0 + 1 := by
              exact congrArg (fun x : ℝ => x + 1) (add_neg_cancel σ)
            _ = 1 := zero_add 1
        calc
          1 = σ + (1 - σ) := hleft.symm
          _ ≤ σ + (N : ℝ) := by
            exact add_le_add_left hN σ
      have hshift_pos : 0 < σ + (N : ℝ) :=
        lt_of_lt_of_le zero_lt_one hone_le_shift
      exact
        zetaCompletedExplicitFormulaInverseGammaLeftAffineKernel_majorantPackage_of_gammaBinetCoherence_shift
          f F h hregular hcoh N hshift_pos

/-- Bundled majorant package for the right inverse-Gamma affine kernel. -/
theorem zetaCompletedExplicitFormulaInverseGammaRightAffineKernel_majorantPackage
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F)
    (hcoh : Complex.gammaBinetPrincipalLogCoherence) :
    ExplicitFormulaAffineKernelMajorantPackage
      (zetaCompletedExplicitFormulaInverseGammaRightAffineKernel f F) :=
  zetaCompletedExplicitFormulaInverseGammaRightAffineKernel_majorantPackage_of_gammaBinetCoherence
    f F h hcoh

/-- Gamma/Binet-coherence-qualified existential majorant package for the right
inverse-Gamma affine kernel. -/
theorem zetaCompletedExplicitFormulaInverseGammaRightAffineKernel_integrableMajorant_of_gammaBinetCoherence
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F)
    (hcoh : Complex.gammaBinetPrincipalLogCoherence) :
    ∃ majorant : ℝ → ℝ,
      Integrable majorant (volume : Measure ℝ) ∧
        AEStronglyMeasurable
          (zetaCompletedExplicitFormulaInverseGammaRightAffineKernel f F)
          (volume : Measure ℝ) ∧
        ∀ᵐ t ∂(volume : Measure ℝ),
          ‖zetaCompletedExplicitFormulaInverseGammaRightAffineKernel f F t‖
            ≤ majorant t :=
  (zetaCompletedExplicitFormulaInverseGammaRightAffineKernel_majorantPackage_of_gammaBinetCoherence
    f F h hcoh).exists_majorant

/-- Gamma/Binet-coherence-qualified integrability of the right inverse-Gamma
affine kernel. -/
theorem zetaCompletedExplicitFormulaInverseGammaRightAffineKernel_integrable_of_gammaBinetCoherence
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F)
    (hcoh : Complex.gammaBinetPrincipalLogCoherence) :
    Integrable
      (zetaCompletedExplicitFormulaInverseGammaRightAffineKernel f F)
      (volume : Measure ℝ) :=
  (zetaCompletedExplicitFormulaInverseGammaRightAffineKernel_majorantPackage_of_gammaBinetCoherence
    f F h hcoh).integrable

/-- Existential majorant package for the right inverse-Gamma affine kernel. -/
theorem zetaCompletedExplicitFormulaInverseGammaRightAffineKernel_integrableMajorant
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F)
    (hcoh : Complex.gammaBinetPrincipalLogCoherence) :
    ∃ majorant : ℝ → ℝ,
      Integrable majorant (volume : Measure ℝ) ∧
        AEStronglyMeasurable
          (zetaCompletedExplicitFormulaInverseGammaRightAffineKernel f F)
          (volume : Measure ℝ) ∧
        ∀ᵐ t ∂(volume : Measure ℝ),
          ‖zetaCompletedExplicitFormulaInverseGammaRightAffineKernel f F t‖
            ≤ majorant t :=
  (zetaCompletedExplicitFormulaInverseGammaRightAffineKernel_majorantPackage
    f F h hcoh).exists_majorant

/-- Integrability of the right inverse-Gamma affine kernel. -/
theorem zetaCompletedExplicitFormulaInverseGammaRightAffineKernel_integrable
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F)
    (hcoh : Complex.gammaBinetPrincipalLogCoherence) :
    Integrable
      (zetaCompletedExplicitFormulaInverseGammaRightAffineKernel f F)
      (volume : Measure ℝ) :=
  (zetaCompletedExplicitFormulaInverseGammaRightAffineKernel_majorantPackage
    f F h hcoh).integrable

/-- Bundled majorant package for the left inverse-Gamma affine kernel. -/
theorem zetaCompletedExplicitFormulaInverseGammaLeftAffineKernel_majorantPackage
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F)
    (hregular : zetaCompletedExplicitFormulaLeftAffineLineGammaRegular F)
    (hcoh : Complex.gammaBinetPrincipalLogCoherence) :
    ExplicitFormulaAffineKernelMajorantPackage
      (zetaCompletedExplicitFormulaInverseGammaLeftAffineKernel f F) :=
  zetaCompletedExplicitFormulaInverseGammaLeftAffineKernel_majorantPackage_of_gammaBinetCoherence
    f F h hregular hcoh

/-- Regular Gamma/Binet-coherence-qualified existential majorant package for
the left inverse-Gamma affine kernel. -/
theorem zetaCompletedExplicitFormulaInverseGammaLeftAffineKernel_integrableMajorant_of_gammaBinetCoherence_regular
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F)
    (hregular : zetaCompletedExplicitFormulaLeftAffineLineGammaRegular F)
    (hcoh : Complex.gammaBinetPrincipalLogCoherence) :
    ∃ majorant : ℝ → ℝ,
      Integrable majorant (volume : Measure ℝ) ∧
        AEStronglyMeasurable
          (zetaCompletedExplicitFormulaInverseGammaLeftAffineKernel f F)
          (volume : Measure ℝ) ∧
        ∀ᵐ t ∂(volume : Measure ℝ),
          ‖zetaCompletedExplicitFormulaInverseGammaLeftAffineKernel f F t‖
            ≤ majorant t :=
  (zetaCompletedExplicitFormulaInverseGammaLeftAffineKernel_majorantPackage_of_gammaBinetCoherence
    f F h hregular hcoh).exists_majorant

/-- Regular Gamma/Binet-coherence-qualified integrability of the left
inverse-Gamma affine kernel. -/
theorem zetaCompletedExplicitFormulaInverseGammaLeftAffineKernel_integrable_of_gammaBinetCoherence_regular
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F)
    (hregular : zetaCompletedExplicitFormulaLeftAffineLineGammaRegular F)
    (hcoh : Complex.gammaBinetPrincipalLogCoherence) :
    Integrable
      (zetaCompletedExplicitFormulaInverseGammaLeftAffineKernel f F)
      (volume : Measure ℝ) :=
  (zetaCompletedExplicitFormulaInverseGammaLeftAffineKernel_majorantPackage_of_gammaBinetCoherence
    f F h hregular hcoh).integrable

/-- Existential majorant package for the left inverse-Gamma affine kernel. -/
theorem zetaCompletedExplicitFormulaInverseGammaLeftAffineKernel_integrableMajorant
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F)
    (hregular : zetaCompletedExplicitFormulaLeftAffineLineGammaRegular F)
    (hcoh : Complex.gammaBinetPrincipalLogCoherence) :
    ∃ majorant : ℝ → ℝ,
      Integrable majorant (volume : Measure ℝ) ∧
        AEStronglyMeasurable
          (zetaCompletedExplicitFormulaInverseGammaLeftAffineKernel f F)
          (volume : Measure ℝ) ∧
        ∀ᵐ t ∂(volume : Measure ℝ),
          ‖zetaCompletedExplicitFormulaInverseGammaLeftAffineKernel f F t‖
            ≤ majorant t :=
  (zetaCompletedExplicitFormulaInverseGammaLeftAffineKernel_majorantPackage
    f F h hregular hcoh).exists_majorant

/-- Integrability of the left inverse-Gamma affine kernel. -/
theorem zetaCompletedExplicitFormulaInverseGammaLeftAffineKernel_integrable
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F)
    (hregular : zetaCompletedExplicitFormulaLeftAffineLineGammaRegular F)
    (hcoh : Complex.gammaBinetPrincipalLogCoherence) :
    Integrable
      (zetaCompletedExplicitFormulaInverseGammaLeftAffineKernel f F)
      (volume : Measure ℝ) :=
  (zetaCompletedExplicitFormulaInverseGammaLeftAffineKernel_majorantPackage
    f F h hregular hcoh).integrable

/-- Bundled majorant package for the right-minus-left inverse-Gamma affine
kernel. -/
theorem zetaCompletedExplicitFormulaInverseGammaDifferenceAffineKernel_majorantPackage
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F)
    (hregular : zetaCompletedExplicitFormulaLeftAffineLineGammaRegular F)
    (hcoh : Complex.gammaBinetPrincipalLogCoherence) :
    ExplicitFormulaAffineKernelMajorantPackage
      (zetaCompletedExplicitFormulaInverseGammaDifferenceAffineKernel f F) :=
  (zetaCompletedExplicitFormulaInverseGammaRightAffineKernel_majorantPackage
    f F h hcoh).sub
    (zetaCompletedExplicitFormulaInverseGammaLeftAffineKernel_majorantPackage
      f F h hregular hcoh)

/-- Regular, Gamma-coherence-qualified bundled majorant package for the
right-minus-left inverse-Gamma affine kernel.  This is the honest analytic path:
the right side uses the positive half-plane Binet estimate, while the left side
uses finite recurrence shift and requires the left half-line to avoid Gamma
poles. -/
theorem zetaCompletedExplicitFormulaInverseGammaDifferenceAffineKernel_majorantPackage_of_gammaBinetCoherence_regular
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F)
    (hregular : zetaCompletedExplicitFormulaLeftAffineLineGammaRegular F)
    (hcoh : Complex.gammaBinetPrincipalLogCoherence) :
    ExplicitFormulaAffineKernelMajorantPackage
      (zetaCompletedExplicitFormulaInverseGammaDifferenceAffineKernel f F) :=
  (zetaCompletedExplicitFormulaInverseGammaRightAffineKernel_majorantPackage_of_gammaBinetCoherence
    f F h hcoh).sub
    (zetaCompletedExplicitFormulaInverseGammaLeftAffineKernel_majorantPackage_of_gammaBinetCoherence
      f F h hregular hcoh)

/-- Integrability of the right-minus-left inverse-Gamma affine kernel. -/
theorem zetaCompletedExplicitFormulaInverseGammaDifferenceAffineKernel_integrable
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F)
    (hregular : zetaCompletedExplicitFormulaLeftAffineLineGammaRegular F)
    (hcoh : Complex.gammaBinetPrincipalLogCoherence) :
    Integrable
      (zetaCompletedExplicitFormulaInverseGammaDifferenceAffineKernel f F)
      (volume : Measure ℝ) :=
  (zetaCompletedExplicitFormulaInverseGammaDifferenceAffineKernel_majorantPackage
    f F h hregular hcoh).integrable

/-- Regular, Gamma-coherence-qualified integrability of the right-minus-left
inverse-Gamma affine kernel. -/
theorem zetaCompletedExplicitFormulaInverseGammaDifferenceAffineKernel_integrable_of_gammaBinetCoherence_regular
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F)
    (hregular : zetaCompletedExplicitFormulaLeftAffineLineGammaRegular F)
    (hcoh : Complex.gammaBinetPrincipalLogCoherence) :
    Integrable
      (zetaCompletedExplicitFormulaInverseGammaDifferenceAffineKernel f F)
      (volume : Measure ℝ) :=
  (zetaCompletedExplicitFormulaInverseGammaDifferenceAffineKernel_majorantPackage_of_gammaBinetCoherence_regular
    f F h hregular hcoh).integrable

/-- Vertically regular, Gamma-coherence-qualified integrability of the
right-minus-left inverse-Gamma affine kernel. -/
theorem zetaCompletedExplicitFormulaInverseGammaDifferenceAffineKernel_integrable_of_verticallyRegular_gammaBinetCoherence
    (f : ZetaAdmissibleFunction)
    (F : ExplicitFormulaVerticallyRegularContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F.toContourFamily)
    (hcoh : Complex.gammaBinetPrincipalLogCoherence) :
    Integrable
      (zetaCompletedExplicitFormulaInverseGammaDifferenceAffineKernel
        f F.toContourFamily)
      (volume : Measure ℝ) :=
  zetaCompletedExplicitFormulaInverseGammaDifferenceAffineKernel_integrable_of_gammaBinetCoherence_regular
    f F.toContourFamily h
    (zetaCompletedExplicitFormulaLeftAffineLineGammaRegular_of_verticallyRegular
      F)
    hcoh

/-- Symmetric-window convergence of the inverse-Gamma difference affine kernel
to its actual whole-line integral under the regular Gamma/Binet hypotheses.
This separates exhaustion from the later value identification with the
archimedean plus correction boundary terms. -/
theorem zetaCompletedExplicitFormulaInverseGammaAffineKernelIntegrals_tendsto_integral_symmetric_of_gammaBinetCoherence_regular
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F)
    (hregular : zetaCompletedExplicitFormulaLeftAffineLineGammaRegular F)
    (hcoh : Complex.gammaBinetPrincipalLogCoherence) :
    Tendsto
      (fun T : ℝ =>
        ∫ t in Set.Icc (-T) T,
          zetaCompletedExplicitFormulaInverseGammaDifferenceAffineKernel f F t)
      atTop
      (𝓝 (∫ t : ℝ,
        zetaCompletedExplicitFormulaInverseGammaDifferenceAffineKernel f F t)) := by
  exact
    explicitFormulaSymmetricIntervalIntegral_tendsto_integral
      (zetaCompletedExplicitFormulaInverseGammaDifferenceAffineKernel f F)
      (zetaCompletedExplicitFormulaInverseGammaDifferenceAffineKernel_integrable_of_gammaBinetCoherence_regular
        f F h hregular hcoh)

/-- Rectangle-window convergence of the inverse-Gamma difference affine kernel
to its actual whole-line integral under the regular Gamma/Binet hypotheses. -/
theorem zetaCompletedExplicitFormulaInverseGammaAffineKernelIntegrals_tendsto_integral_unscheduled_of_gammaBinetCoherence_regular
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F)
    (hregular : zetaCompletedExplicitFormulaLeftAffineLineGammaRegular F)
    (hcoh : Complex.gammaBinetPrincipalLogCoherence) :
    Tendsto
      (fun T : ℝ =>
        ∫ t in Set.Icc
            (-(F.rectangle T).T)
            (F.rectangle T).T,
          zetaCompletedExplicitFormulaInverseGammaDifferenceAffineKernel f F t)
      atTop
      (𝓝 (∫ t : ℝ,
        zetaCompletedExplicitFormulaInverseGammaDifferenceAffineKernel f F t)) := by
  exact
    explicitFormulaRectangleWindowIntegral_tendsto_of_symmetric
      F
      (zetaCompletedExplicitFormulaInverseGammaDifferenceAffineKernel f F)
      (∫ t : ℝ,
        zetaCompletedExplicitFormulaInverseGammaDifferenceAffineKernel f F t)
      (zetaCompletedExplicitFormulaInverseGammaAffineKernelIntegrals_tendsto_integral_symmetric_of_gammaBinetCoherence_regular
        f F h hregular hcoh)

/-- Scheduled-window convergence of the inverse-Gamma difference affine kernel
to its actual whole-line integral under the regular Gamma/Binet hypotheses. -/
theorem zetaCompletedExplicitFormulaInverseGammaAffineKernelIntegrals_tendsto_integral_of_gammaBinetCoherence_regular
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F)
    (hregular : zetaCompletedExplicitFormulaLeftAffineLineGammaRegular F)
    (hcoh : Complex.gammaBinetPrincipalLogCoherence) :
    Tendsto
      (fun u : ℝ =>
        ∫ t in Set.Icc
            (-(F.rectangle (h.height_schedule.height u)).T)
            (F.rectangle (h.height_schedule.height u)).T,
          zetaCompletedExplicitFormulaInverseGammaDifferenceAffineKernel f F t)
      atTop
      (𝓝 (∫ t : ℝ,
        zetaCompletedExplicitFormulaInverseGammaDifferenceAffineKernel f F t)) := by
  let K : ℝ → ℂ := fun T : ℝ =>
    ∫ t in Set.Icc
        (-(F.rectangle T).T)
        (F.rectangle T).T,
      zetaCompletedExplicitFormulaInverseGammaDifferenceAffineKernel f F t
  have hkernel :
      Tendsto K atTop
        (𝓝 (∫ t : ℝ,
          zetaCompletedExplicitFormulaInverseGammaDifferenceAffineKernel f F t)) :=
    zetaCompletedExplicitFormulaInverseGammaAffineKernelIntegrals_tendsto_integral_unscheduled_of_gammaBinetCoherence_regular
      f F h hregular hcoh
  exact
    explicitFormulaScheduledScalar_tendsto_of_unscheduled
      K
      h.height_schedule.height
      (∫ t : ℝ,
        zetaCompletedExplicitFormulaInverseGammaDifferenceAffineKernel f F t)
      hkernel
      h.height_schedule.cofinal

/-- Symmetric-window inverse-Gamma completion convergence from the regular
Gamma/Binet majorant hypotheses and a separately proved whole-line value
identity. -/
theorem zetaCompletedExplicitFormulaInverseGammaAffineKernelIntegrals_tendsto_archimedean_add_correction_symmetric_of_gammaBinetCoherence_regular_and_integral_eq
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F)
    (hregular : zetaCompletedExplicitFormulaLeftAffineLineGammaRegular F)
    (hcoh : Complex.gammaBinetPrincipalLogCoherence)
    (hvalue :
      (∫ t : ℝ,
        zetaCompletedExplicitFormulaInverseGammaDifferenceAffineKernel f F t) =
        zetaCompletedExplicitFormulaArchimedeanContribution f +
          zetaCompletedExplicitFormulaCorrectionStandardContourContribution f) :
    Tendsto
      (fun T : ℝ =>
        ∫ t in Set.Icc (-T) T,
          zetaCompletedExplicitFormulaInverseGammaDifferenceAffineKernel f F t)
      atTop
      (𝓝
        (zetaCompletedExplicitFormulaArchimedeanContribution f +
          zetaCompletedExplicitFormulaCorrectionStandardContourContribution f)) := by
  exact
    explicitFormulaSymmetricIntervalIntegral_tendsto_value
      (zetaCompletedExplicitFormulaInverseGammaDifferenceAffineKernel f F)
      (zetaCompletedExplicitFormulaArchimedeanContribution f +
        zetaCompletedExplicitFormulaCorrectionStandardContourContribution f)
      (zetaCompletedExplicitFormulaInverseGammaDifferenceAffineKernel_integrable_of_gammaBinetCoherence_regular
        f F h hregular hcoh)
      hvalue

/-- Rectangle-window inverse-Gamma completion convergence from the regular
Gamma/Binet majorant hypotheses and a separately proved whole-line value
identity. -/
theorem zetaCompletedExplicitFormulaInverseGammaAffineKernelIntegrals_tendsto_archimedean_add_correction_unscheduled_of_gammaBinetCoherence_regular_and_integral_eq
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F)
    (hregular : zetaCompletedExplicitFormulaLeftAffineLineGammaRegular F)
    (hcoh : Complex.gammaBinetPrincipalLogCoherence)
    (hvalue :
      (∫ t : ℝ,
        zetaCompletedExplicitFormulaInverseGammaDifferenceAffineKernel f F t) =
        zetaCompletedExplicitFormulaArchimedeanContribution f +
          zetaCompletedExplicitFormulaCorrectionStandardContourContribution f) :
    Tendsto
      (fun T : ℝ =>
        ∫ t in Set.Icc
            (-(F.rectangle T).T)
            (F.rectangle T).T,
          zetaCompletedExplicitFormulaInverseGammaDifferenceAffineKernel f F t)
      atTop
      (𝓝
        (zetaCompletedExplicitFormulaArchimedeanContribution f +
          zetaCompletedExplicitFormulaCorrectionStandardContourContribution f)) := by
  exact
    explicitFormulaRectangleWindowIntegral_tendsto_of_symmetric
      F
      (zetaCompletedExplicitFormulaInverseGammaDifferenceAffineKernel f F)
      (zetaCompletedExplicitFormulaArchimedeanContribution f +
        zetaCompletedExplicitFormulaCorrectionStandardContourContribution f)
      (zetaCompletedExplicitFormulaInverseGammaAffineKernelIntegrals_tendsto_archimedean_add_correction_symmetric_of_gammaBinetCoherence_regular_and_integral_eq
        f F h hregular hcoh hvalue)

/-- Scheduled-window inverse-Gamma completion convergence from the regular
Gamma/Binet majorant hypotheses and a separately proved whole-line value
identity. -/
theorem zetaCompletedExplicitFormulaInverseGammaAffineKernelIntegrals_tendsto_archimedean_add_correction_of_gammaBinetCoherence_regular_and_integral_eq
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F)
    (hregular : zetaCompletedExplicitFormulaLeftAffineLineGammaRegular F)
    (hcoh : Complex.gammaBinetPrincipalLogCoherence)
    (hvalue :
      (∫ t : ℝ,
        zetaCompletedExplicitFormulaInverseGammaDifferenceAffineKernel f F t) =
        zetaCompletedExplicitFormulaArchimedeanContribution f +
          zetaCompletedExplicitFormulaCorrectionStandardContourContribution f) :
    Tendsto
      (fun u : ℝ =>
        ∫ t in Set.Icc
            (-(F.rectangle (h.height_schedule.height u)).T)
            (F.rectangle (h.height_schedule.height u)).T,
          zetaCompletedExplicitFormulaInverseGammaDifferenceAffineKernel f F t)
      atTop
      (𝓝
        (zetaCompletedExplicitFormulaArchimedeanContribution f +
          zetaCompletedExplicitFormulaCorrectionStandardContourContribution f)) := by
  let K : ℝ → ℂ := fun T : ℝ =>
    ∫ t in Set.Icc
        (-(F.rectangle T).T)
        (F.rectangle T).T,
      zetaCompletedExplicitFormulaInverseGammaDifferenceAffineKernel f F t
  have hkernel :
      Tendsto K atTop
        (𝓝
          (zetaCompletedExplicitFormulaArchimedeanContribution f +
            zetaCompletedExplicitFormulaCorrectionStandardContourContribution f)) :=
    zetaCompletedExplicitFormulaInverseGammaAffineKernelIntegrals_tendsto_archimedean_add_correction_unscheduled_of_gammaBinetCoherence_regular_and_integral_eq
      f F h hregular hcoh hvalue
  exact
    explicitFormulaScheduledScalar_tendsto_of_unscheduled
      K
      h.height_schedule.height
      (zetaCompletedExplicitFormulaArchimedeanContribution f +
        zetaCompletedExplicitFormulaCorrectionStandardContourContribution f)
      hkernel
      h.height_schedule.cofinal

/-- The whole-line inverse-Gamma difference affine-kernel value follows from a
scheduled inverse-Gamma completion value theorem.  This is a compatibility
transport; the owner normalization is the whole-line Gamma/Binet value. -/
theorem zetaCompletedExplicitFormulaInverseGammaDifferenceAffineKernel_integral_eq_archimedean_add_correction_of_scheduled_tendsto_archimedean_add_correction
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F)
    (hregular : zetaCompletedExplicitFormulaLeftAffineLineGammaRegular F)
    (hcoh : Complex.gammaBinetPrincipalLogCoherence)
    (hscheduled :
      Tendsto
        (fun u : ℝ =>
          ∫ t in Set.Icc
              (-(F.rectangle (h.height_schedule.height u)).T)
              (F.rectangle (h.height_schedule.height u)).T,
            zetaCompletedExplicitFormulaInverseGammaDifferenceAffineKernel f F t)
        atTop
        (𝓝
          (zetaCompletedExplicitFormulaArchimedeanContribution f +
            zetaCompletedExplicitFormulaCorrectionStandardContourContribution f))) :
    (∫ t : ℝ,
      zetaCompletedExplicitFormulaInverseGammaDifferenceAffineKernel f F t) =
      zetaCompletedExplicitFormulaArchimedeanContribution f +
        zetaCompletedExplicitFormulaCorrectionStandardContourContribution f := by
  have hintegral :
      Tendsto
        (fun u : ℝ =>
          ∫ t in Set.Icc
              (-(F.rectangle (h.height_schedule.height u)).T)
              (F.rectangle (h.height_schedule.height u)).T,
            zetaCompletedExplicitFormulaInverseGammaDifferenceAffineKernel f F t)
        atTop
        (𝓝
          (∫ t : ℝ,
            zetaCompletedExplicitFormulaInverseGammaDifferenceAffineKernel f F t)) :=
    zetaCompletedExplicitFormulaInverseGammaAffineKernelIntegrals_tendsto_integral_of_gammaBinetCoherence_regular
      f F h hregular hcoh
  exact
    explicitFormulaScheduledScalar_integral_eq_of_tendsto_integral_and_value
      (fun u : ℝ =>
        ∫ t in Set.Icc
            (-(F.rectangle (h.height_schedule.height u)).T)
            (F.rectangle (h.height_schedule.height u)).T,
          zetaCompletedExplicitFormulaInverseGammaDifferenceAffineKernel f F t)
      (∫ t : ℝ,
        zetaCompletedExplicitFormulaInverseGammaDifferenceAffineKernel f F t)
      (zetaCompletedExplicitFormulaArchimedeanContribution f +
        zetaCompletedExplicitFormulaCorrectionStandardContourContribution f)
      hintegral
      hscheduled

/-- Vertically regular whole-line inverse-Gamma value from a scheduled
inverse-Gamma completion value theorem.  This theorem is retained as a transport
wrapper; the owner normalization is the whole-line Gamma/Binet value. -/
theorem zetaCompletedExplicitFormulaInverseGammaDifferenceAffineKernel_integral_eq_archimedean_add_correction_of_verticallyRegular_gammaBinet_scheduled_tendsto
    (f : ZetaAdmissibleFunction)
    (F : ExplicitFormulaVerticallyRegularContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F.toContourFamily)
    (hcoh : Complex.gammaBinetPrincipalLogCoherence)
    (hscheduled :
      Tendsto
        (fun u : ℝ =>
          ∫ t in Set.Icc
              (-(F.toContourFamily.rectangle (h.height_schedule.height u)).T)
              (F.toContourFamily.rectangle (h.height_schedule.height u)).T,
            zetaCompletedExplicitFormulaInverseGammaDifferenceAffineKernel
              f F.toContourFamily t)
        atTop
        (𝓝
          (zetaCompletedExplicitFormulaArchimedeanContribution f +
            zetaCompletedExplicitFormulaCorrectionStandardContourContribution f))) :
    (∫ t : ℝ,
      zetaCompletedExplicitFormulaInverseGammaDifferenceAffineKernel
        f F.toContourFamily t) =
      zetaCompletedExplicitFormulaArchimedeanContribution f +
        zetaCompletedExplicitFormulaCorrectionStandardContourContribution f :=
  zetaCompletedExplicitFormulaInverseGammaDifferenceAffineKernel_integral_eq_archimedean_add_correction_of_scheduled_tendsto_archimedean_add_correction
    f F.toContourFamily h
    (zetaCompletedExplicitFormulaLeftAffineLineGammaRegular_of_verticallyRegular
      F)
    hcoh hscheduled

/-- On a finite symmetric window, the inverse-Gamma difference affine kernel
recombines into the archimedean and elementary correction difference kernels. -/
theorem zetaCompletedExplicitFormulaInverseGammaDifferenceAffineKernel_intervalIntegral_eq_archimedean_add_correction
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily) (T : ℝ) :
    (∫ t in Set.Icc (-T) T,
      zetaCompletedExplicitFormulaInverseGammaDifferenceAffineKernel f F t) =
      ∫ t in Set.Icc (-T) T,
        zetaCompletedExplicitFormulaArchimedeanDifferenceAffineKernel f F t +
          zetaCompletedExplicitFormulaCorrectionDifferenceAffineKernel f F t := by
  exact MeasureTheory.setIntegral_congr_fun
    measurableSet_Icc
    (fun t _ht =>
      zetaCompletedExplicitFormulaInverseGammaDifferenceAffineKernel_eq_archimedean_add_correction
        f F t)

/-- Whole-line additive splitting of the inverse-Gamma difference affine kernel.

This lemma contains only integration algebra.  The analytic normalization still
lives in the owner normalization theorem: this helper may be used only after
the archimedean and elementary correction summands have independently supplied
their own integrability and value statements. -/
theorem zetaCompletedExplicitFormulaInverseGammaDifferenceAffineKernel_integral_eq_archimedean_integral_add_correction_integral
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (harch :
      Integrable
        (zetaCompletedExplicitFormulaArchimedeanDifferenceAffineKernel f F)
        (volume : Measure ℝ))
    (hcorr :
      Integrable
        (zetaCompletedExplicitFormulaCorrectionDifferenceAffineKernel f F)
        (volume : Measure ℝ)) :
    (∫ t : ℝ,
      zetaCompletedExplicitFormulaInverseGammaDifferenceAffineKernel f F t) =
      (∫ t : ℝ,
        zetaCompletedExplicitFormulaArchimedeanDifferenceAffineKernel f F t) +
        ∫ t : ℝ,
          zetaCompletedExplicitFormulaCorrectionDifferenceAffineKernel f F t := by
  have hpoint :
      (fun t : ℝ =>
        zetaCompletedExplicitFormulaInverseGammaDifferenceAffineKernel f F t) =ᵐ[volume]
        fun t : ℝ =>
          zetaCompletedExplicitFormulaArchimedeanDifferenceAffineKernel f F t +
            zetaCompletedExplicitFormulaCorrectionDifferenceAffineKernel f F t :=
    Filter.Eventually.of_forall
      (fun t =>
        zetaCompletedExplicitFormulaInverseGammaDifferenceAffineKernel_eq_archimedean_add_correction
          f F t)
  exact Eq.trans
    (integral_congr_ae hpoint)
    (integral_add harch hcorr)

/-- Whole-line splitting of the right-minus-left inverse-Gamma affine kernel
into its two affine-line components.

This is only Bochner-integral algebra.  It is the component-level counterpart
of the archimedean/correction split above and is useful when a later proof has
an independent right inverse-Gamma value and the already normalized
right-minus-left inverse-Gamma value. -/
theorem zetaCompletedExplicitFormulaInverseGammaDifferenceAffineKernel_integral_eq_rightIntegral_sub_leftIntegral
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (hright :
      Integrable
        (zetaCompletedExplicitFormulaInverseGammaRightAffineKernel f F)
        (volume : Measure ℝ))
    (hleft :
      Integrable
        (zetaCompletedExplicitFormulaInverseGammaLeftAffineKernel f F)
        (volume : Measure ℝ)) :
    (∫ t : ℝ,
      zetaCompletedExplicitFormulaInverseGammaDifferenceAffineKernel f F t) =
      (∫ t : ℝ,
        zetaCompletedExplicitFormulaInverseGammaRightAffineKernel f F t) -
        ∫ t : ℝ,
          zetaCompletedExplicitFormulaInverseGammaLeftAffineKernel f F t := by
  exact integral_sub hright hleft

/-- Extract the left inverse-Gamma affine value from a right affine value and
the right-minus-left difference value.

The equation is intentionally algebraic: since the difference kernel is
`right - left`, a proved value for the difference and a proved value for the
right component determine the left component as `right - difference`. -/
theorem zetaCompletedExplicitFormulaInverseGammaLeftAffineKernel_integral_eq_rightValue_sub_differenceValue
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (hright :
      Integrable
        (zetaCompletedExplicitFormulaInverseGammaRightAffineKernel f F)
        (volume : Measure ℝ))
    (hleft :
      Integrable
        (zetaCompletedExplicitFormulaInverseGammaLeftAffineKernel f F)
        (volume : Measure ℝ))
    (R D : ℂ)
    (hright_value :
      (∫ t : ℝ,
        zetaCompletedExplicitFormulaInverseGammaRightAffineKernel f F t) = R)
    (hdifference_value :
      (∫ t : ℝ,
        zetaCompletedExplicitFormulaInverseGammaDifferenceAffineKernel f F t) = D) :
    (∫ t : ℝ,
      zetaCompletedExplicitFormulaInverseGammaLeftAffineKernel f F t) =
      R - D := by
  let L : ℂ :=
    ∫ t : ℝ,
      zetaCompletedExplicitFormulaInverseGammaLeftAffineKernel f F t
  have hsplit :
      D = R - L := by
    calc
      D =
          ∫ t : ℝ,
            zetaCompletedExplicitFormulaInverseGammaDifferenceAffineKernel f F t := by
        exact hdifference_value.symm
      _ =
          (∫ t : ℝ,
            zetaCompletedExplicitFormulaInverseGammaRightAffineKernel f F t) -
            ∫ t : ℝ,
              zetaCompletedExplicitFormulaInverseGammaLeftAffineKernel f F t := by
        exact
          zetaCompletedExplicitFormulaInverseGammaDifferenceAffineKernel_integral_eq_rightIntegral_sub_leftIntegral
            f F hright hleft
      _ = R - L := by
        exact congrArg
          (fun z : ℂ => z - L)
          hright_value
  have hR_sub_D :
      R - D = L := by
    calc
      R - D = R - (R - L) := by
        exact congrArg (fun z : ℂ => R - z) hsplit
      _ = L := by
        exact sub_sub_cancel_left R L
  exact hR_sub_D.symm

/-- Integrability of the right-minus-left inverse-Gamma affine kernel under the
regular Gamma/Binet hypotheses. -/
theorem zetaCompletedExplicitFormulaInverseGammaDifferenceAffineKernel_integrable_owner
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F)
    (hregular : zetaCompletedExplicitFormulaLeftAffineLineGammaRegular F)
    (hcoh : Complex.gammaBinetPrincipalLogCoherence) :
    Integrable
      (zetaCompletedExplicitFormulaInverseGammaDifferenceAffineKernel f F)
      (volume : Measure ℝ) := by
  exact
    zetaCompletedExplicitFormulaInverseGammaDifferenceAffineKernel_integrable_of_gammaBinetCoherence_regular
      f F h hregular hcoh

/-- Scheduled inverse-Gamma completion convergence once the whole-line
inverse-Gamma value identity has been proved. -/
theorem zetaCompletedExplicitFormulaInverseGammaDifferenceAffineKernelIntegral_tendsto_archimedean_add_correction_direct
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F)
    (hregular : zetaCompletedExplicitFormulaLeftAffineLineGammaRegular F)
    (hcoh : Complex.gammaBinetPrincipalLogCoherence)
    (hvalue :
      (∫ t : ℝ,
        zetaCompletedExplicitFormulaInverseGammaDifferenceAffineKernel f F t) =
        zetaCompletedExplicitFormulaArchimedeanContribution f +
          zetaCompletedExplicitFormulaCorrectionStandardContourContribution f) :
    Tendsto
      (fun u : ℝ =>
        ∫ t in Set.Icc
            (-(F.rectangle (h.height_schedule.height u)).T)
            (F.rectangle (h.height_schedule.height u)).T,
          zetaCompletedExplicitFormulaInverseGammaDifferenceAffineKernel f F t)
      atTop
      (𝓝
        (zetaCompletedExplicitFormulaArchimedeanContribution f +
          zetaCompletedExplicitFormulaCorrectionStandardContourContribution f)) := by
  exact
    zetaCompletedExplicitFormulaInverseGammaAffineKernelIntegrals_tendsto_archimedean_add_correction_of_gammaBinetCoherence_regular_and_integral_eq
      f F h hregular hcoh hvalue

/-- Whole-line value of the right-minus-left inverse-Gamma affine kernel from a
separately proved scheduled inverse-Gamma normalization. -/
theorem zetaCompletedExplicitFormulaInverseGammaDifferenceAffineKernel_integral_eq_archimedean_add_correction
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F)
    (hregular : zetaCompletedExplicitFormulaLeftAffineLineGammaRegular F)
    (hcoh : Complex.gammaBinetPrincipalLogCoherence)
    (hscheduled :
      Tendsto
        (fun u : ℝ =>
          ∫ t in Set.Icc
              (-(F.rectangle (h.height_schedule.height u)).T)
              (F.rectangle (h.height_schedule.height u)).T,
            zetaCompletedExplicitFormulaInverseGammaDifferenceAffineKernel f F t)
        atTop
        (𝓝
          (zetaCompletedExplicitFormulaArchimedeanContribution f +
            zetaCompletedExplicitFormulaCorrectionStandardContourContribution f))) :
    (∫ t : ℝ,
      zetaCompletedExplicitFormulaInverseGammaDifferenceAffineKernel f F t) =
      zetaCompletedExplicitFormulaArchimedeanContribution f +
        zetaCompletedExplicitFormulaCorrectionStandardContourContribution f := by
  exact
    zetaCompletedExplicitFormulaInverseGammaDifferenceAffineKernel_integral_eq_archimedean_add_correction_of_scheduled_tendsto_archimedean_add_correction
      f F h hregular hcoh hscheduled

/-- Symmetric-window inverse-Gamma completion convergence on vertical lines from
the whole-line inverse-Gamma value identity. -/
theorem zetaCompletedExplicitFormulaInverseGammaAffineKernelIntegrals_tendsto_archimedean_add_correction_symmetric
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F)
    (hregular : zetaCompletedExplicitFormulaLeftAffineLineGammaRegular F)
    (hcoh : Complex.gammaBinetPrincipalLogCoherence)
    (hvalue :
      (∫ t : ℝ,
        zetaCompletedExplicitFormulaInverseGammaDifferenceAffineKernel f F t) =
        zetaCompletedExplicitFormulaArchimedeanContribution f +
          zetaCompletedExplicitFormulaCorrectionStandardContourContribution f) :
    Tendsto
      (fun T : ℝ =>
        (∫ t in Set.Icc (-T) T,
          zetaCompletedExplicitFormulaInverseGammaRightAffineKernel f F t) -
          ∫ t in Set.Icc (-T) T,
          zetaCompletedExplicitFormulaInverseGammaLeftAffineKernel f F t)
      atTop
      (𝓝
        (zetaCompletedExplicitFormulaArchimedeanContribution f +
          zetaCompletedExplicitFormulaCorrectionStandardContourContribution f)) := by
  let K : ℝ → ℂ :=
    zetaCompletedExplicitFormulaInverseGammaDifferenceAffineKernel f F
  let R : ℝ → ℂ :=
    zetaCompletedExplicitFormulaInverseGammaRightAffineKernel f F
  let L : ℝ → ℂ :=
    zetaCompletedExplicitFormulaInverseGammaLeftAffineKernel f F
  have hK_limit :
      Tendsto
        (fun T : ℝ => ∫ t in Set.Icc (-T) T, K t)
        atTop
        (𝓝
          (zetaCompletedExplicitFormulaArchimedeanContribution f +
            zetaCompletedExplicitFormulaCorrectionStandardContourContribution f)) :=
    zetaCompletedExplicitFormulaInverseGammaAffineKernelIntegrals_tendsto_archimedean_add_correction_symmetric_of_gammaBinetCoherence_regular_and_integral_eq
      f F h hregular hcoh hvalue
  have hR_integrable :
      Integrable R (volume : Measure ℝ) :=
    zetaCompletedExplicitFormulaInverseGammaRightAffineKernel_integrable f F
      h hcoh
  have hL_integrable :
      Integrable L (volume : Measure ℝ) :=
    zetaCompletedExplicitFormulaInverseGammaLeftAffineKernel_integrable f F
      h hregular hcoh
  have hdisplay :
      (fun T : ℝ =>
        (∫ t in Set.Icc (-T) T,
          zetaCompletedExplicitFormulaInverseGammaRightAffineKernel f F t) -
          ∫ t in Set.Icc (-T) T,
          zetaCompletedExplicitFormulaInverseGammaLeftAffineKernel f F t) =
        (fun T : ℝ => ∫ t in Set.Icc (-T) T, K t) := by
    funext T
    exact
      explicitFormulaSymmetricIntervalIntegral_sub_eq_integral_sub
        R L hR_integrable hL_integrable T
  exact Eq.subst
    (motive := fun ψ : ℝ → ℂ =>
      Tendsto ψ atTop
        (𝓝
          (zetaCompletedExplicitFormulaArchimedeanContribution f +
            zetaCompletedExplicitFormulaCorrectionStandardContourContribution f)))
    hdisplay.symm
    hK_limit

/-- Unscheduled rectangle-window inverse-Gamma completion convergence on
vertical lines from the whole-line inverse-Gamma value identity. -/
theorem zetaCompletedExplicitFormulaInverseGammaAffineKernelIntegrals_tendsto_archimedean_add_correction_unscheduled
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F)
    (hregular : zetaCompletedExplicitFormulaLeftAffineLineGammaRegular F)
    (hcoh : Complex.gammaBinetPrincipalLogCoherence)
    (hvalue :
      (∫ t : ℝ,
        zetaCompletedExplicitFormulaInverseGammaDifferenceAffineKernel f F t) =
        zetaCompletedExplicitFormulaArchimedeanContribution f +
          zetaCompletedExplicitFormulaCorrectionStandardContourContribution f) :
    Tendsto
      (fun T : ℝ =>
        (∫ t in Set.Icc
            (-(F.rectangle T).T)
            (F.rectangle T).T,
          zetaCompletedExplicitFormulaInverseGammaRightAffineKernel f F t) -
          ∫ t in Set.Icc
            (-(F.rectangle T).T)
            (F.rectangle T).T,
          zetaCompletedExplicitFormulaInverseGammaLeftAffineKernel f F t)
      atTop
      (𝓝
        (zetaCompletedExplicitFormulaArchimedeanContribution f +
          zetaCompletedExplicitFormulaCorrectionStandardContourContribution f)) := by
  let R : ℝ → ℂ := fun T : ℝ =>
    ∫ t in Set.Icc (-T) T,
      zetaCompletedExplicitFormulaInverseGammaRightAffineKernel f F t
  let L : ℝ → ℂ := fun T : ℝ =>
    ∫ t in Set.Icc (-T) T,
      zetaCompletedExplicitFormulaInverseGammaLeftAffineKernel f F t
  let Rrect : ℝ → ℂ := fun T : ℝ =>
    ∫ t in Set.Icc (-(F.rectangle T).T) (F.rectangle T).T,
      zetaCompletedExplicitFormulaInverseGammaRightAffineKernel f F t
  let Lrect : ℝ → ℂ := fun T : ℝ =>
    ∫ t in Set.Icc (-(F.rectangle T).T) (F.rectangle T).T,
      zetaCompletedExplicitFormulaInverseGammaLeftAffineKernel f F t
  have hR : Rrect = R := by
    funext T
    exact
      explicitFormulaRectangleWindowIntegral_eq_symmetric
        F
        (zetaCompletedExplicitFormulaInverseGammaRightAffineKernel f F)
        T
  have hL : Lrect = L := by
    funext T
    exact
      explicitFormulaRectangleWindowIntegral_eq_symmetric
        F
        (zetaCompletedExplicitFormulaInverseGammaLeftAffineKernel f F)
        T
  have hdiff :
      (fun T : ℝ => Rrect T - Lrect T) =
        fun T : ℝ => R T - L T := by
    funext T
    exact congrArg₂ HSub.hSub (congrArg (fun φ : ℝ → ℂ => φ T) hR)
      (congrArg (fun φ : ℝ → ℂ => φ T) hL)
  exact Eq.subst
    (motive := fun ψ : ℝ → ℂ =>
      Tendsto ψ atTop
        (𝓝
          (zetaCompletedExplicitFormulaArchimedeanContribution f +
            zetaCompletedExplicitFormulaCorrectionStandardContourContribution f)))
    hdiff.symm
    (zetaCompletedExplicitFormulaInverseGammaAffineKernelIntegrals_tendsto_archimedean_add_correction_symmetric
      f F h hregular hcoh hvalue)

/-- Kernel-level inverse-Gamma completion convergence on the scheduled vertical
lines from the whole-line inverse-Gamma value identity. -/
theorem zetaCompletedExplicitFormulaInverseGammaAffineKernelIntegrals_tendsto_archimedean_add_correction
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F)
    (hregular : zetaCompletedExplicitFormulaLeftAffineLineGammaRegular F)
    (hcoh : Complex.gammaBinetPrincipalLogCoherence)
    (hvalue :
      (∫ t : ℝ,
        zetaCompletedExplicitFormulaInverseGammaDifferenceAffineKernel f F t) =
        zetaCompletedExplicitFormulaArchimedeanContribution f +
          zetaCompletedExplicitFormulaCorrectionStandardContourContribution f) :
    Tendsto
      (fun u : ℝ =>
        (∫ t in Set.Icc
            (-(F.rectangle (h.height_schedule.height u)).T)
            (F.rectangle (h.height_schedule.height u)).T,
          zetaCompletedExplicitFormulaInverseGammaRightAffineKernel f F t) -
          ∫ t in Set.Icc
            (-(F.rectangle (h.height_schedule.height u)).T)
            (F.rectangle (h.height_schedule.height u)).T,
          zetaCompletedExplicitFormulaInverseGammaLeftAffineKernel f F t)
      atTop
      (𝓝
        (zetaCompletedExplicitFormulaArchimedeanContribution f +
          zetaCompletedExplicitFormulaCorrectionStandardContourContribution f)) := by
  let K : ℝ → ℂ := fun T : ℝ =>
    (∫ t in Set.Icc
        (-(F.rectangle T).T)
        (F.rectangle T).T,
      zetaCompletedExplicitFormulaInverseGammaRightAffineKernel f F t) -
      ∫ t in Set.Icc
        (-(F.rectangle T).T)
        (F.rectangle T).T,
      zetaCompletedExplicitFormulaInverseGammaLeftAffineKernel f F t
  have hkernel :
      Tendsto K atTop
        (𝓝
          (zetaCompletedExplicitFormulaArchimedeanContribution f +
            zetaCompletedExplicitFormulaCorrectionStandardContourContribution f)) :=
    zetaCompletedExplicitFormulaInverseGammaAffineKernelIntegrals_tendsto_archimedean_add_correction_unscheduled
      f F h hregular hcoh hvalue
  exact
    explicitFormulaScheduledScalar_tendsto_of_unscheduled
      K
      h.height_schedule.height
      (zetaCompletedExplicitFormulaArchimedeanContribution f +
        zetaCompletedExplicitFormulaCorrectionStandardContourContribution f)
      hkernel
      h.height_schedule.cofinal

end ZetaAdmissibleFunction

end
end LFunctions
end Boundary
