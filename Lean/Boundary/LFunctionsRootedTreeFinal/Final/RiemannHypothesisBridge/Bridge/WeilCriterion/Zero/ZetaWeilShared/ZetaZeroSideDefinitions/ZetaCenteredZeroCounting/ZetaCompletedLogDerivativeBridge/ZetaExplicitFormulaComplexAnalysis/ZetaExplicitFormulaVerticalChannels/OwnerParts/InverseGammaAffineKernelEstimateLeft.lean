import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaExplicitFormulaVerticalChannels.OwnerParts.InverseGammaAffineKernelEstimateCommon
/-!
# Inverse-Gamma affine-kernel base estimate split part

This file is a mechanical owner split of the inverse-Gamma affine-kernel base estimates.
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

/-- A polynomial bound for the inverse-Gamma logarithmic-derivative factor on
the left affine line packages the left inverse-Gamma affine kernel.  The
Gamma/Stirling owner layer is responsible for the pointwise factor bound; this
theorem owns the vertical-channel multiplication with the rapidly decaying test
transform. -/
def zetaCompletedExplicitFormulaInverseGammaLeftAffineKernel_majorantPackage_of_factor_bound
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
  let majorant : ℝ → ℝ := fun t : ℝ => B * (C * (1 + ‖t‖) ^ (-(3 : ℤ)))
  have hintegrable :
      Integrable majorant (volume : Measure ℝ) := by
    have hfinrank : Module.finrank ℝ ℝ = 1 :=
      Module.finrank_self ℝ
    have hfinrank_cast : ((Module.finrank ℝ ℝ : ℕ) : ℝ) = 1 :=
      Eq.trans
        (congrArg (fun n : ℕ => (n : ℝ)) hfinrank)
        Nat.cast_one
    have htwo_lt_three : (2 : ℝ) < 3 := by
      have htwo_add_one : (2 : ℝ) + 1 = 3 :=
        two_add_one_eq_three
      exact Eq.subst
        (motive := fun value : ℝ => (2 : ℝ) < value)
        htwo_add_one
        (lt_add_of_pos_right 2 zero_lt_one)
    have hdim : (Module.finrank ℝ ℝ : ℝ) < 3 :=
      Eq.subst
        (motive := fun x : ℝ => x < 3)
        hfinrank_cast.symm
        (lt_trans one_lt_two htwo_lt_three)
    have hbase :
        Integrable
          (fun t : ℝ => (1 + ‖t‖) ^ (-(3 : ℝ)))
          (volume : Measure ℝ) :=
      integrable_one_add_norm hdim
    have hscaled :
        Integrable
          (fun t : ℝ => B * (C * (1 + ‖t‖) ^ (-(3 : ℝ))))
          (volume : Measure ℝ) :=
      (hbase.const_mul C).const_mul B
    have hfun :
        majorant =
          (fun t : ℝ => B * (C * (1 + ‖t‖) ^ (-(3 : ℝ)))) := by
      funext t
      have hpow :
          (1 + ‖t‖) ^ (-(3 : ℤ)) =
            (1 + ‖t‖) ^ (-(3 : ℝ)) :=
        realLine_one_add_norm_zpow_three_eq_rpow_three t
      exact congrArg (fun x : ℝ => B * (C * x)) hpow
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
          have hone_zpow :
              (1 + ‖t‖) ^ (1 : ℤ) = (1 + ‖t‖ : ℝ) :=
            zpow_one (1 + ‖t‖)
          calc
            (1 + ‖t‖) * (1 + ‖t‖) ^ (-(4 : ℤ)) =
                (1 + ‖t‖) ^ (1 : ℤ) *
                  (1 + ‖t‖) ^ (-(4 : ℤ)) := by
              exact congrArg
                (fun value : ℝ => value * (1 + ‖t‖) ^ (-(4 : ℤ)))
                hone_zpow.symm
            _ =
                (1 + ‖t‖) ^ ((1 : ℤ) + (-(4 : ℤ))) := by
              exact (zpow_add₀ hbase_nonzero (1 : ℤ) (-(4 : ℤ))).symm
            _ = (1 + ‖t‖) ^ (-(3 : ℤ)) := by
              rfl
        have hassoc :
            (B * (1 + ‖t‖)) *
                (C * (1 + ‖t‖) ^ (-(4 : ℤ))) =
              B * (C * (1 + ‖t‖) ^ (-(3 : ℤ))) := by
          let a : ℝ := 1 + ‖t‖
          let b : ℝ := (1 + ‖t‖) ^ (-(4 : ℤ))
          have hscalar :
              (B * a) * (C * b) = B * (C * (a * b)) := by
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
          have hrewrite :
              a * b = (1 + ‖t‖) ^ (-(3 : ℤ)) :=
            hweight
          exact
            Eq.trans hscalar
              (congrArg (fun x : ℝ => B * (C * x)) hrewrite)
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
        ‖deriv Complex.Gammaℝ (zetaCompletedExplicitFormulaLeftAffineLine F t) /
            Complex.Gammaℝ (zetaCompletedExplicitFormulaLeftAffineLine F t)‖ ≤
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
def zetaCompletedExplicitFormulaInverseGammaLeftAffineKernel_majorantPackage_of_Gammaℝ_logDeriv_bound
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F)
    (hregular : zetaCompletedExplicitFormulaLeftAffineLineGammaRegular F)
    (B : ℝ)
    (hB_nonneg : 0 ≤ B)
    (hGamma_bound :
      ∀ t : ℝ,
        ‖deriv Complex.Gammaℝ (zetaCompletedExplicitFormulaLeftAffineLine F t) /
            Complex.Gammaℝ (zetaCompletedExplicitFormulaLeftAffineLine F t)‖ ≤
          B * (1 + ‖t‖)) :
    ExplicitFormulaAffineKernelMajorantPackage
      (zetaCompletedExplicitFormulaInverseGammaLeftAffineKernel f F) := by
  have hfactor_bound :
      ∀ t : ℝ,
        ‖inverseGammaCompletionLogDeriv
            (zetaCompletedExplicitFormulaLeftAffineLine F t)‖ ≤
          B * (1 + ‖t‖) := by
    exact
      zetaCompletedExplicitFormulaInverseGammaCompletionLogDeriv_leftAffineLine_bound_of_Gammaℝ_logDeriv_bound
        F hregular B hGamma_bound
  exact
    zetaCompletedExplicitFormulaInverseGammaLeftAffineKernel_majorantPackage_of_factor_bound
      f F h hregular B hB_nonneg hfactor_bound

/-- A left-line bound for the ordinary Gamma logarithmic derivative at the
half argument gives the left inverse-Gamma affine-kernel majorant package. -/
def zetaCompletedExplicitFormulaInverseGammaLeftAffineKernel_majorantPackage_of_halfGamma_logDeriv_bound
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
  let A : ℝ := ‖Complex.log (Real.pi : ℂ) * (-(1 / 2 : ℂ))‖
  let C : ℝ := A + B
  have hA_nonneg : 0 ≤ A :=
    norm_nonneg (Complex.log (Real.pi : ℂ) * (-(1 / 2 : ℂ)))
  have hC_nonneg : 0 ≤ C :=
    add_nonneg hA_nonneg hB_nonneg
  have hGammaℝ_bound :
      ∀ t : ℝ,
        ‖deriv Complex.Gammaℝ (zetaCompletedExplicitFormulaLeftAffineLine F t) /
            Complex.Gammaℝ (zetaCompletedExplicitFormulaLeftAffineLine F t)‖ ≤
          C * (1 + ‖t‖) := by
    intro t
    let Q : ℂ :=
      (deriv Complex.Gamma
          (zetaCompletedExplicitFormulaLeftAffineLine F t / 2) *
        (1 / 2 : ℂ)) /
        Complex.Gamma
          (zetaCompletedExplicitFormulaLeftAffineLine F t / 2)
    have hdecomp :
        deriv Complex.Gammaℝ (zetaCompletedExplicitFormulaLeftAffineLine F t) /
            Complex.Gammaℝ (zetaCompletedExplicitFormulaLeftAffineLine F t) =
          Complex.log (Real.pi : ℂ) * (-(1 / 2 : ℂ)) + Q :=
      zetaCompletedExplicitFormulaLeftAffineLine_Gammaℝ_logDeriv_eq_of_gammaRegular
        F hregular t
    have hnorm_split :
        ‖deriv Complex.Gammaℝ (zetaCompletedExplicitFormulaLeftAffineLine F t) /
            Complex.Gammaℝ (zetaCompletedExplicitFormulaLeftAffineLine F t)‖ ≤
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
  have hfactor_bound :
      ∀ t : ℝ,
        ‖inverseGammaCompletionLogDeriv
            (zetaCompletedExplicitFormulaLeftAffineLine F t)‖ ≤
          C * (1 + ‖t‖) :=
    zetaCompletedExplicitFormulaInverseGammaCompletionLogDeriv_leftAffineLine_bound_of_Gammaℝ_logDeriv_bound_owner
      F hregular C hGammaℝ_bound
  exact
    zetaCompletedExplicitFormulaInverseGammaLeftAffineKernel_majorantPackage_of_factor_bound
      f F h hregular C hC_nonneg hfactor_bound

end ZetaAdmissibleFunction

end
end LFunctions
end Boundary
