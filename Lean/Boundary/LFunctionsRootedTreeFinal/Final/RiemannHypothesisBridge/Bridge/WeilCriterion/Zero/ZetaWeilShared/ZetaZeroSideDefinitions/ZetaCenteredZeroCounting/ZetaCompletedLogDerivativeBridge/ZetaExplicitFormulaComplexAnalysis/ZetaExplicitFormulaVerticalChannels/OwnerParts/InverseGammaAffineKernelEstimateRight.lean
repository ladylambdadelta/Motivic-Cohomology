import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaExplicitFormulaVerticalChannels.OwnerParts.InverseGammaAffineKernelEstimateLeft
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
the right affine line packages the right inverse-Gamma affine kernel.  The
Gamma/Stirling owner layer is responsible for supplying the pointwise factor
bound; this theorem owns only the vertical-channel multiplication with the
rapidly decaying test transform. -/
def zetaCompletedExplicitFormulaInverseGammaRightAffineKernel_majorantPackage_of_phiControl_factor_bound
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (hPhi : ZetaPhiAnalyticControl f)
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
    hPhi.verticalStripRapidDecayConstant
      (F.c - (1 / 2 : ℝ)) (F.c - (1 / 2 : ℝ)) 4
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
    zetaCompletedExplicitFormulaPhi_rightCenteredAffineLine_aestronglyMeasurable_of_phiControl
      f F hPhi
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
          zetaCompletedExplicitFormulaPhi_rightCenteredAffineLine_decay_bound_of_phiControl
            f F hPhi 4 t
        have hphi_nonneg :
            0 ≤ ‖zetaCompletedExplicitFormulaPhi f
              (zetaCompletedExplicitFormulaRightCenteredAffineLine F t)‖ :=
          norm_nonneg
            (zetaCompletedExplicitFormulaPhi f
              (zetaCompletedExplicitFormulaRightCenteredAffineLine F t))
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
          calc
            (B * (1 + ‖t‖)) *
                (C * (1 + ‖t‖) ^ (-(4 : ℤ))) =
                B *
                  (C * ((1 + ‖t‖) * (1 + ‖t‖) ^ (-(4 : ℤ)))) :=
              hscalar
            _ = B * (C * (1 + ‖t‖) ^ (-(3 : ℤ))) :=
              congrArg (fun x : ℝ => B * (C * x)) hweight
        hprod.trans_eq hassoc)
  exact
    ExplicitFormulaAffineKernelMajorantPackage.of_mul_le
      majorant hintegrable hfactor_meas hphi_meas hbound

/-- A polynomial bound for the inverse-Gamma logarithmic-derivative factor on
the right affine line packages the right inverse-Gamma affine kernel. -/
def zetaCompletedExplicitFormulaInverseGammaRightAffineKernel_majorantPackage_of_factor_bound
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
      (zetaCompletedExplicitFormulaInverseGammaRightAffineKernel f F) :=
  zetaCompletedExplicitFormulaInverseGammaRightAffineKernel_majorantPackage_of_phiControl_factor_bound
    f F h.phi_control B hB_nonneg hfactor_bound

/-- A right-line bound for the ordinary `Gammaℝ` logarithmic derivative
packages the right inverse-Gamma affine kernel. -/
def zetaCompletedExplicitFormulaInverseGammaRightAffineKernel_majorantPackage_of_Gammaℝ_logDeriv_bound
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F)
    (B : ℝ)
    (hB_nonneg : 0 ≤ B)
    (hGamma_bound :
      ∀ t : ℝ,
        ‖deriv Complex.Gammaℝ (zetaCompletedExplicitFormulaRightAffineLine F t) /
            Complex.Gammaℝ (zetaCompletedExplicitFormulaRightAffineLine F t)‖ ≤
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
          -deriv Complex.Gammaℝ (zetaCompletedExplicitFormulaRightAffineLine F t) /
            Complex.Gammaℝ (zetaCompletedExplicitFormulaRightAffineLine F t) :=
      zetaCompletedExplicitFormulaInverseGammaLogDeriv_rightAffineLine_eq_neg_Gammaℝ_logDeriv
        F t
    have hnorm :
        ‖inverseGammaCompletionLogDeriv
            (zetaCompletedExplicitFormulaRightAffineLine F t)‖ =
          ‖deriv Complex.Gammaℝ (zetaCompletedExplicitFormulaRightAffineLine F t) /
            Complex.Gammaℝ (zetaCompletedExplicitFormulaRightAffineLine F t)‖ := by
      calc
        ‖inverseGammaCompletionLogDeriv
            (zetaCompletedExplicitFormulaRightAffineLine F t)‖ =
            ‖-deriv Complex.Gammaℝ (zetaCompletedExplicitFormulaRightAffineLine F t) /
              Complex.Gammaℝ (zetaCompletedExplicitFormulaRightAffineLine F t)‖ := by
          exact congrArg norm hidentity
        _ =
            ‖-(deriv Complex.Gammaℝ (zetaCompletedExplicitFormulaRightAffineLine F t) /
              Complex.Gammaℝ (zetaCompletedExplicitFormulaRightAffineLine F t))‖ := by
          exact congrArg norm
            (neg_div
              (Complex.Gammaℝ (zetaCompletedExplicitFormulaRightAffineLine F t))
              (deriv Complex.Gammaℝ (zetaCompletedExplicitFormulaRightAffineLine F t)))
        _ =
            ‖deriv Complex.Gammaℝ (zetaCompletedExplicitFormulaRightAffineLine F t) /
              Complex.Gammaℝ (zetaCompletedExplicitFormulaRightAffineLine F t)‖ :=
          norm_neg
            (deriv Complex.Gammaℝ (zetaCompletedExplicitFormulaRightAffineLine F t) /
              Complex.Gammaℝ (zetaCompletedExplicitFormulaRightAffineLine F t))
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
def zetaCompletedExplicitFormulaInverseGammaRightAffineKernel_majorantPackage_of_halfGamma_logDeriv_bound
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
        ‖deriv Complex.Gammaℝ (zetaCompletedExplicitFormulaRightAffineLine F t) /
            Complex.Gammaℝ (zetaCompletedExplicitFormulaRightAffineLine F t)‖ ≤
          C * (1 + ‖t‖) := by
    intro t
    let Q : ℂ :=
      (deriv Complex.Gamma
          (zetaCompletedExplicitFormulaRightAffineLine F t / 2) *
        (1 / 2 : ℂ)) /
        Complex.Gamma
          (zetaCompletedExplicitFormulaRightAffineLine F t / 2)
    have hdecomp :
        deriv Complex.Gammaℝ (zetaCompletedExplicitFormulaRightAffineLine F t) /
            Complex.Gammaℝ (zetaCompletedExplicitFormulaRightAffineLine F t) =
          Complex.log (Real.pi : ℂ) * (-(1 / 2 : ℂ)) + Q :=
      zetaCompletedExplicitFormulaRightAffineLine_Gammaℝ_logDeriv_eq F t
    have hnorm_split :
        ‖deriv Complex.Gammaℝ (zetaCompletedExplicitFormulaRightAffineLine F t) /
            Complex.Gammaℝ (zetaCompletedExplicitFormulaRightAffineLine F t)‖ ≤
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


end ZetaAdmissibleFunction

end
end LFunctions
end Boundary
