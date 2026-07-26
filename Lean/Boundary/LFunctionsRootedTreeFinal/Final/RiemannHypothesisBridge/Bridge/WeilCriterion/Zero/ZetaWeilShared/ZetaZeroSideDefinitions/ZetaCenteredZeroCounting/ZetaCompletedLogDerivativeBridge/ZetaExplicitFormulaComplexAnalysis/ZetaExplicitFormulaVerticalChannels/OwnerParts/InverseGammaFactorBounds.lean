import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaExplicitFormulaVerticalChannels.OwnerParts.AffineLineMeasurability
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ClassicalAnalysis.GammaBinetStirling.LogDerivativeFiniteFormula

/-!
# Inverse-Gamma factor bounds

This file owns pointwise linear bounds for the inverse-Gamma completion
logarithmic derivative on affine vertical lines.  Kernel majorant files consume
these bounds, but the bounds themselves are independent of test-function
decay and whole-line integration.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open Complex
open LSeries ArithmeticFunction
open scoped ArithmeticFunction

namespace ZetaAdmissibleFunction

set_option maxHeartbeats 5000000

/-- A right-line bound for the ordinary `Gammaℝ` logarithmic derivative gives a
right-line bound for the inverse-Gamma completion logarithmic derivative. -/
theorem zetaCompletedExplicitFormulaInverseGammaCompletionLogDeriv_rightAffineLine_bound_of_Gammaℝ_logDeriv_bound_owner
    (F : ExplicitFormulaContourFamily)
    (B : ℝ)
    (hGamma_bound :
      ∀ t : ℝ,
        ‖deriv Complex.Gammaℝ (zetaCompletedExplicitFormulaRightAffineLine F t) /
            Complex.Gammaℝ (zetaCompletedExplicitFormulaRightAffineLine F t)‖ ≤
          B * (1 + ‖t‖)) :
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

/-- A right-line bound for the ordinary Gamma logarithmic derivative at the
half argument gives a right-line bound for the inverse-Gamma completion
logarithmic derivative. -/
theorem zetaCompletedExplicitFormulaInverseGammaCompletionLogDeriv_rightAffineLine_bound_of_halfGamma_logDeriv_bound_owner
    (F : ExplicitFormulaContourFamily)
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
    ∃ C : ℝ,
      0 ≤ C ∧
        ∀ t : ℝ,
          ‖inverseGammaCompletionLogDeriv
              (zetaCompletedExplicitFormulaRightAffineLine F t)‖ ≤
            C * (1 + ‖t‖) := by
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
    ⟨C, hC_nonneg,
      zetaCompletedExplicitFormulaInverseGammaCompletionLogDeriv_rightAffineLine_bound_of_Gammaℝ_logDeriv_bound_owner
        F C hGammaℝ_bound⟩

/-- The Gamma/Stirling fixed-line estimates give a linear right-line bound for
the inverse-Gamma completion logarithmic derivative. -/
theorem zetaCompletedExplicitFormulaInverseGammaCompletionLogDeriv_rightAffineLine_bound_of_gammaBinet_owner
    (F : ExplicitFormulaContourFamily) :
    ∃ B : ℝ,
      0 ≤ B ∧
        ∀ t : ℝ,
          ‖inverseGammaCompletionLogDeriv
              (zetaCompletedExplicitFormulaRightAffineLine F t)‖ ≤
            B * (1 + ‖t‖) := by
  let sigma := (F.c / 2 : ℝ)
  let B : ℝ :=
    ‖(1 / 2 : ℂ)‖ *
      |Complex.GammaLogDerivativeFixedVerticalPositiveLineConstant sigma|
  have hsigma_pos : 0 < sigma :=
    div_pos F.c_pos zero_lt_two
  have hB_nonneg : 0 ≤ B :=
    mul_nonneg
      (norm_nonneg (1 / 2 : ℂ))
      (abs_nonneg
        (Complex.GammaLogDerivativeFixedVerticalPositiveLineConstant sigma))
  have hhalf_line :
      ∀ t : ℝ,
        zetaCompletedExplicitFormulaRightAffineLine F t / 2 =
          (sigma + ((t : ℂ) / 2) * Complex.I : ℂ) := by
    intro t
    calc
      zetaCompletedExplicitFormulaRightAffineLine F t / 2 =
          ((F.c : ℂ) + t * Complex.I) / 2 := by
        exact congrArg (fun z : ℂ => z / 2)
          (zetaCompletedExplicitFormulaRightAffineLine_eq F t)
      _ = ((F.c : ℂ) / 2) + (t * Complex.I) / 2 := by
        exact add_div ((F.c : ℂ)) (t * Complex.I) (2 : ℂ)
      _ = (sigma + (t / 2) * Complex.I : ℂ) := by
        have hc :
            ((F.c : ℂ) / 2) = (sigma : ℂ) := by
          exact (Complex.ofReal_div F.c 2).symm
        have ht :
            (t * Complex.I) / 2 = ((t : ℂ) / 2) * Complex.I := by
          exact mul_div_right_comm (t : ℂ) Complex.I (2 : ℂ)
        exact congrArg₂ HAdd.hAdd hc ht
  have hgamma_bound :
      ∀ t : ℝ,
        ‖(deriv Complex.Gamma
              (zetaCompletedExplicitFormulaRightAffineLine F t / 2) *
            (1 / 2 : ℂ)) /
            Complex.Gamma
              (zetaCompletedExplicitFormulaRightAffineLine F t / 2)‖ ≤
          B * (1 + ‖t‖) := by
    intro t
    let z : ℂ := zetaCompletedExplicitFormulaRightAffineLine F t / 2
    let q : ℂ := deriv Complex.Gamma z / Complex.Gamma z
    have hline :
        z = (sigma + (((t / 2 : ℝ) : ℂ) * Complex.I) : ℂ) := by
      have hraw :
          z = (sigma + ((t : ℂ) / 2) * Complex.I : ℂ) :=
        hhalf_line t
      have hheight :
          ((t : ℂ) / 2) = ((t / 2 : ℝ) : ℂ) :=
        (Complex.ofReal_div t 2).symm
      exact
        hraw.trans
          (congrArg
            (fun x : ℂ => (sigma + x * Complex.I : ℂ))
            hheight)
    have hfixed :=
      Complex.Gamma_logDerivative_fixedRealPartLine_linear_bound_direct
        hsigma_pos (t / 2)
    have hfixed_abs :
        ‖deriv Complex.Gamma (sigma + (((t / 2 : ℝ) : ℂ) * Complex.I)) /
            Complex.Gamma (sigma + (((t / 2 : ℝ) : ℂ) * Complex.I))‖ ≤
          |Complex.GammaLogDerivativeFixedVerticalPositiveLineConstant sigma| *
            (1 + ‖t / 2‖) := by
      have hfactor_nonneg : 0 ≤ 1 + ‖t / 2‖ :=
        Real.zero_le_one_add_norm (t / 2)
      have hD_le_abs :
          Complex.GammaLogDerivativeFixedVerticalPositiveLineConstant sigma ≤
            |Complex.GammaLogDerivativeFixedVerticalPositiveLineConstant sigma| :=
        le_abs_self
          (Complex.GammaLogDerivativeFixedVerticalPositiveLineConstant sigma)
      exact hfixed.trans
        (mul_le_mul_of_nonneg_right hD_le_abs hfactor_nonneg)
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
                Real.norm_of_nonneg htwo_nonneg
              exact
                Eq.subst
                  (motive := fun x : ℝ => (1 : ℝ) ≤ x)
                  htwo_norm_eq.symm
                  one_le_two
            exact div_le_self (norm_nonneg t) htwo_norm
      exact add_le_add_left hnorm 1
    have hfixed_big :
        ‖deriv Complex.Gamma (sigma + (((t / 2 : ℝ) : ℂ) * Complex.I)) /
            Complex.Gamma (sigma + (((t / 2 : ℝ) : ℂ) * Complex.I))‖ ≤
          |Complex.GammaLogDerivativeFixedVerticalPositiveLineConstant sigma| *
            (1 + ‖t‖) :=
      hfixed_abs.trans
        (mul_le_mul_of_nonneg_left hsmall
          (abs_nonneg
            (Complex.GammaLogDerivativeFixedVerticalPositiveLineConstant sigma)))
    have hq_bound :
        ‖q‖ ≤
          |Complex.GammaLogDerivativeFixedVerticalPositiveLineConstant sigma| *
            (1 + ‖t‖) := by
      exact
        Eq.subst
          (motive := fun w : ℂ =>
            ‖w‖ ≤
              |Complex.GammaLogDerivativeFixedVerticalPositiveLineConstant sigma| *
                (1 + ‖t‖))
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
          exact mul_div_right_comm
            (deriv Complex.Gamma z) (1 / 2 : ℂ) (Complex.Gamma z)
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
            (|Complex.GammaLogDerivativeFixedVerticalPositiveLineConstant sigma| *
                (1 + ‖t‖)) * ‖(1 / 2 : ℂ)‖ :=
        mul_le_mul_of_nonneg_right hq_bound
          (norm_nonneg (1 / 2 : ℂ))
      have hcomm :
          (|Complex.GammaLogDerivativeFixedVerticalPositiveLineConstant sigma| *
              (1 + ‖t‖)) * ‖(1 / 2 : ℂ)‖ =
            B * (1 + ‖t‖) := by
        calc
          (|Complex.GammaLogDerivativeFixedVerticalPositiveLineConstant sigma| *
              (1 + ‖t‖)) * ‖(1 / 2 : ℂ)‖ =
              (‖(1 / 2 : ℂ)‖ *
                |Complex.GammaLogDerivativeFixedVerticalPositiveLineConstant sigma|) *
                  (1 + ‖t‖) := by
            calc
              (|Complex.GammaLogDerivativeFixedVerticalPositiveLineConstant sigma| *
                  (1 + ‖t‖)) * ‖(1 / 2 : ℂ)‖ =
                |Complex.GammaLogDerivativeFixedVerticalPositiveLineConstant sigma| *
                  ((1 + ‖t‖) * ‖(1 / 2 : ℂ)‖) := by
                exact mul_assoc
                  |Complex.GammaLogDerivativeFixedVerticalPositiveLineConstant sigma|
                  (1 + ‖t‖) ‖(1 / 2 : ℂ)‖
              _ =
                |Complex.GammaLogDerivativeFixedVerticalPositiveLineConstant sigma| *
                  (‖(1 / 2 : ℂ)‖ * (1 + ‖t‖)) := by
                exact congrArg
                  (fun x : ℝ =>
                    |Complex.GammaLogDerivativeFixedVerticalPositiveLineConstant sigma| * x)
                  (mul_comm (1 + ‖t‖) ‖(1 / 2 : ℂ)‖)
              _ =
                (|Complex.GammaLogDerivativeFixedVerticalPositiveLineConstant sigma| *
                    ‖(1 / 2 : ℂ)‖) * (1 + ‖t‖) := by
                exact (mul_assoc
                  |Complex.GammaLogDerivativeFixedVerticalPositiveLineConstant sigma|
                  ‖(1 / 2 : ℂ)‖ (1 + ‖t‖)).symm
              _ =
                (‖(1 / 2 : ℂ)‖ *
                  |Complex.GammaLogDerivativeFixedVerticalPositiveLineConstant sigma|) *
                    (1 + ‖t‖) := by
                exact congrArg (fun x : ℝ => x * (1 + ‖t‖))
                  (mul_comm
                    |Complex.GammaLogDerivativeFixedVerticalPositiveLineConstant sigma|
                    ‖(1 / 2 : ℂ)‖)
          _ = B * (1 + ‖t‖) := by
            exact Eq.refl _
      have hqmul_norm :
          ‖q * (1 / 2 : ℂ)‖ ≤ B * (1 + ‖t‖) :=
        Eq.subst
          (motive := fun x : ℝ => x ≤ B * (1 + ‖t‖))
          hmul_norm.symm
          (hprod.trans_eq hcomm)
      exact
        Eq.subst
          (motive := fun w : ℂ => ‖w‖ ≤ B * (1 + ‖t‖))
          halgebra.symm
          hqmul_norm
    exact
      Eq.subst
        (motive := fun w : ℂ =>
          ‖(deriv Complex.Gamma w * (1 / 2 : ℂ)) /
              Complex.Gamma w‖ ≤
            B * (1 + ‖t‖))
        (show z = zetaCompletedExplicitFormulaRightAffineLine F t / 2 from rfl)
        hnorm_mul
  exact
    zetaCompletedExplicitFormulaInverseGammaCompletionLogDeriv_rightAffineLine_bound_of_halfGamma_logDeriv_bound_owner
      F B hB_nonneg hgamma_bound

/-- Compatibility wrapper for the former coherence-qualified right-line API. -/
theorem zetaCompletedExplicitFormulaInverseGammaCompletionLogDeriv_rightAffineLine_bound_of_gammaBinetCoherence_owner
    (F : ExplicitFormulaContourFamily)
    (coherence : Complex.gammaBinetPrincipalLogCoherence) :
    ∃ B : ℝ,
      0 ≤ B ∧
        ∀ t : ℝ,
          ‖inverseGammaCompletionLogDeriv
              (zetaCompletedExplicitFormulaRightAffineLine F t)‖ ≤
            B * (1 + ‖t‖) := by
  exact
    zetaCompletedExplicitFormulaInverseGammaCompletionLogDeriv_rightAffineLine_bound_of_gammaBinet_owner
      F

/- The right-line inverse-Gamma estimate is supplied by the concrete Binet
owner construction itself; no principal-log coherence hypothesis is used. -/
theorem zetaCompletedExplicitFormulaInverseGammaCompletionLogDeriv_rightAffineLine_bound_unconditional_owner
    (F : ExplicitFormulaContourFamily) :
    ∃ B : ℝ,
      0 ≤ B ∧
        ∀ t : ℝ,
          ‖inverseGammaCompletionLogDeriv
              (zetaCompletedExplicitFormulaRightAffineLine F t)‖ ≤
            B * (1 + ‖t‖) := by
  exact
    zetaCompletedExplicitFormulaInverseGammaCompletionLogDeriv_rightAffineLine_bound_of_gammaBinet_owner
      F

/-- A left-line bound for the ordinary `Gammaℝ` logarithmic derivative gives a
left-line bound for the inverse-Gamma completion logarithmic derivative. -/
theorem zetaCompletedExplicitFormulaInverseGammaCompletionLogDeriv_leftAffineLine_bound_of_Gammaℝ_logDeriv_bound_owner
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
  intro t
  have hidentity :
      inverseGammaCompletionLogDeriv
          (zetaCompletedExplicitFormulaLeftAffineLine F t) =
        -deriv Complex.Gammaℝ (zetaCompletedExplicitFormulaLeftAffineLine F t) /
          Complex.Gammaℝ (zetaCompletedExplicitFormulaLeftAffineLine F t) :=
    zetaCompletedExplicitFormulaInverseGammaLogDeriv_leftAffineLine_eq_neg_Gammaℝ_logDeriv_of_gammaRegular
      F hregular t
  have hnorm :
      ‖inverseGammaCompletionLogDeriv
          (zetaCompletedExplicitFormulaLeftAffineLine F t)‖ =
        ‖deriv Complex.Gammaℝ (zetaCompletedExplicitFormulaLeftAffineLine F t) /
          Complex.Gammaℝ (zetaCompletedExplicitFormulaLeftAffineLine F t)‖ := by
    calc
      ‖inverseGammaCompletionLogDeriv
          (zetaCompletedExplicitFormulaLeftAffineLine F t)‖ =
          ‖-deriv Complex.Gammaℝ (zetaCompletedExplicitFormulaLeftAffineLine F t) /
            Complex.Gammaℝ (zetaCompletedExplicitFormulaLeftAffineLine F t)‖ := by
        exact congrArg norm hidentity
      _ =
          ‖-(deriv Complex.Gammaℝ (zetaCompletedExplicitFormulaLeftAffineLine F t) /
            Complex.Gammaℝ (zetaCompletedExplicitFormulaLeftAffineLine F t))‖ := by
        exact congrArg norm
          (neg_div
            (Complex.Gammaℝ (zetaCompletedExplicitFormulaLeftAffineLine F t))
            (deriv Complex.Gammaℝ (zetaCompletedExplicitFormulaLeftAffineLine F t)))
      _ =
          ‖deriv Complex.Gammaℝ (zetaCompletedExplicitFormulaLeftAffineLine F t) /
            Complex.Gammaℝ (zetaCompletedExplicitFormulaLeftAffineLine F t)‖ :=
        norm_neg
          (deriv Complex.Gammaℝ (zetaCompletedExplicitFormulaLeftAffineLine F t) /
            Complex.Gammaℝ (zetaCompletedExplicitFormulaLeftAffineLine F t))
  exact
    Eq.subst
      (motive := fun x : ℝ => x ≤ B * (1 + ‖t‖))
      hnorm.symm
      (hGamma_bound t)

/-- A left-line bound for the ordinary Gamma logarithmic derivative at the half
argument gives a left-line bound for the inverse-Gamma completion logarithmic
derivative. -/
theorem zetaCompletedExplicitFormulaInverseGammaCompletionLogDeriv_leftAffineLine_bound_of_halfGamma_logDeriv_bound_owner
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
  exact
    ⟨C, hC_nonneg,
      zetaCompletedExplicitFormulaInverseGammaCompletionLogDeriv_leftAffineLine_bound_of_Gammaℝ_logDeriv_bound_owner
        F hregular C hGammaℝ_bound⟩

/-- A finite shifted fixed-line Gamma estimate gives a linear bound for the
inverse-Gamma completion logarithmic derivative on the left affine line. -/
theorem zetaCompletedExplicitFormulaInverseGammaCompletionLogDeriv_leftAffineLine_bound_of_gammaBinet_shift_owner
    (F : ExplicitFormulaContourFamily)
    (hregular : zetaCompletedExplicitFormulaLeftAffineLineGammaRegular F)
    (N : ℕ)
    (hshift_pos : 0 < ((1 - F.c) / 2 : ℝ) + (N : ℝ)) :
    ∃ B : ℝ,
      0 ≤ B ∧
        ∀ t : ℝ,
          ‖inverseGammaCompletionLogDeriv
              (zetaCompletedExplicitFormulaLeftAffineLine F t)‖ ≤
            B * (1 + ‖t‖) := by
  let sigma := ((1 - F.c) / 2 : ℝ)
  let B : ℝ :=
    ‖(1 / 2 : ℂ)‖ *
      |Complex.GammaLogDerivativeFixedVerticalShiftConstant sigma N|
  have hB_nonneg : 0 ≤ B :=
    mul_nonneg
      (norm_nonneg (1 / 2 : ℂ))
      (abs_nonneg
        (Complex.GammaLogDerivativeFixedVerticalShiftConstant sigma N))
  have hhalf_line :
      ∀ t : ℝ,
        zetaCompletedExplicitFormulaLeftAffineLine F t / 2 =
          (sigma + ((t : ℂ) / 2) * Complex.I : ℂ) := by
    intro t
    calc
      zetaCompletedExplicitFormulaLeftAffineLine F t / 2 =
          (((1 : ℂ) - (F.c : ℂ)) + t * Complex.I) / 2 := by
        exact congrArg (fun z : ℂ => z / 2)
          (zetaCompletedExplicitFormulaLeftAffineLine_eq F t)
      _ = (((1 : ℂ) - (F.c : ℂ)) / 2) + (t * Complex.I) / 2 := by
        exact add_div (((1 : ℂ) - (F.c : ℂ))) (t * Complex.I) (2 : ℂ)
      _ = (sigma + (t / 2) * Complex.I : ℂ) := by
        have hc :
            (((1 : ℂ) - (F.c : ℂ)) / 2) = (sigma : ℂ) := by
          calc
            (((1 : ℂ) - (F.c : ℂ)) / 2) =
                (((1 - F.c : ℝ) : ℂ) / 2) := by
              exact congrArg (fun z : ℂ => z / 2)
                (Complex.ofReal_sub 1 F.c).symm
            _ = (((1 - F.c) / 2 : ℝ) : ℂ) := by
              exact (Complex.ofReal_div (1 - F.c) 2).symm
            _ = (sigma : ℂ) := by
              exact Eq.refl _
        have ht :
            (t * Complex.I) / 2 = ((t : ℂ) / 2) * Complex.I := by
          exact mul_div_right_comm (t : ℂ) Complex.I (2 : ℂ)
        exact congrArg₂ HAdd.hAdd hc ht
  have hnot_pole :
      ∀ u : ℝ, ∀ n : ℕ,
        (sigma + u * Complex.I : ℂ) ≠ -n := by
    intro u n hpole
    have hline :
        zetaCompletedExplicitFormulaLeftAffineLine F (2 * u) / 2 =
          (sigma + u * Complex.I : ℂ) := by
      have hraw :
          zetaCompletedExplicitFormulaLeftAffineLine F (2 * u) / 2 =
            (sigma + (((2 * u : ℝ) : ℂ) / 2) * Complex.I : ℂ) :=
        hhalf_line (2 * u)
      have hheight :
          ((2 * u) / 2 : ℝ) = u := by
        exact mul_div_cancel_left₀ u
          (show (2 : ℝ) ≠ 0 from two_ne_zero)
      have hheight_complex :
          ((2 * u : ℝ) : ℂ) / 2 = (u : ℂ) := by
        exact Eq.trans
          (Complex.ofReal_div (2 * u) 2).symm
          (congrArg (fun x : ℝ => (x : ℂ)) hheight)
      exact
        hraw.trans
          (congrArg (fun x : ℂ => (sigma + x * Complex.I : ℂ)) hheight_complex)
    exact
      (zetaCompletedExplicitFormulaLeftAffineLine_half_ne_Gamma_zero_locus_of_gammaRegular
        F hregular (2 * u) n)
      (hline.trans hpole)
  have hfixed_bound :
      ∀ u : ℝ,
        ‖deriv Complex.Gamma (sigma + u * Complex.I) /
            Complex.Gamma (sigma + u * Complex.I)‖ ≤
          Complex.GammaLogDerivativeFixedVerticalShiftConstant sigma N *
            (1 + ‖u‖) :=
    Complex.Gamma_logDerivative_fixedRealPartLine_linear_bound_of_shift_nat_direct
      N hshift_pos hnot_pole
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
    have hline :
        z = (sigma + (((t / 2 : ℝ) : ℂ) * Complex.I) : ℂ) := by
      have hraw :
          z = (sigma + ((t : ℂ) / 2) * Complex.I : ℂ) :=
        hhalf_line t
      have hheight :
          ((t : ℂ) / 2) = ((t / 2 : ℝ) : ℂ) :=
        (Complex.ofReal_div t 2).symm
      exact
        hraw.trans
          (congrArg
            (fun x : ℂ => (sigma + x * Complex.I : ℂ))
            hheight)
    have hfixed :=
      hfixed_bound (t / 2)
    have hfixed_abs :
        ‖deriv Complex.Gamma (sigma + (((t / 2 : ℝ) : ℂ) * Complex.I)) /
            Complex.Gamma (sigma + (((t / 2 : ℝ) : ℂ) * Complex.I))‖ ≤
          |Complex.GammaLogDerivativeFixedVerticalShiftConstant sigma N| *
            (1 + ‖t / 2‖) := by
      have hfactor_nonneg : 0 ≤ 1 + ‖t / 2‖ :=
        Real.zero_le_one_add_norm (t / 2)
      have hD_le_abs :
          Complex.GammaLogDerivativeFixedVerticalShiftConstant sigma N ≤
            |Complex.GammaLogDerivativeFixedVerticalShiftConstant sigma N| :=
        le_abs_self
          (Complex.GammaLogDerivativeFixedVerticalShiftConstant sigma N)
      exact hfixed.trans
        (mul_le_mul_of_nonneg_right hD_le_abs hfactor_nonneg)
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
                Real.norm_of_nonneg htwo_nonneg
              exact
                Eq.subst
                  (motive := fun x : ℝ => (1 : ℝ) ≤ x)
                  htwo_norm_eq.symm
                  one_le_two
            exact div_le_self (norm_nonneg t) htwo_norm
      exact add_le_add_left hnorm 1
    have hfixed_big :
        ‖deriv Complex.Gamma (sigma + (((t / 2 : ℝ) : ℂ) * Complex.I)) /
            Complex.Gamma (sigma + (((t / 2 : ℝ) : ℂ) * Complex.I))‖ ≤
          |Complex.GammaLogDerivativeFixedVerticalShiftConstant sigma N| *
            (1 + ‖t‖) :=
      hfixed_abs.trans
        (mul_le_mul_of_nonneg_left hsmall
          (abs_nonneg
            (Complex.GammaLogDerivativeFixedVerticalShiftConstant sigma N)))
    have hq_bound :
        ‖q‖ ≤
          |Complex.GammaLogDerivativeFixedVerticalShiftConstant sigma N| *
            (1 + ‖t‖) := by
      exact
        Eq.subst
          (motive := fun w : ℂ =>
            ‖w‖ ≤
              |Complex.GammaLogDerivativeFixedVerticalShiftConstant sigma N| *
                (1 + ‖t‖))
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
          exact mul_div_right_comm
            (deriv Complex.Gamma z) (1 / 2 : ℂ) (Complex.Gamma z)
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
            (|Complex.GammaLogDerivativeFixedVerticalShiftConstant sigma N| *
                (1 + ‖t‖)) * ‖(1 / 2 : ℂ)‖ :=
        mul_le_mul_of_nonneg_right hq_bound
          (norm_nonneg (1 / 2 : ℂ))
      have hcomm :
          (|Complex.GammaLogDerivativeFixedVerticalShiftConstant sigma N| *
              (1 + ‖t‖)) * ‖(1 / 2 : ℂ)‖ =
            B * (1 + ‖t‖) := by
        calc
          (|Complex.GammaLogDerivativeFixedVerticalShiftConstant sigma N| *
              (1 + ‖t‖)) * ‖(1 / 2 : ℂ)‖ =
              (‖(1 / 2 : ℂ)‖ *
                |Complex.GammaLogDerivativeFixedVerticalShiftConstant sigma N|) *
                  (1 + ‖t‖) := by
            calc
              (|Complex.GammaLogDerivativeFixedVerticalShiftConstant sigma N| *
                  (1 + ‖t‖)) * ‖(1 / 2 : ℂ)‖ =
                |Complex.GammaLogDerivativeFixedVerticalShiftConstant sigma N| *
                  ((1 + ‖t‖) * ‖(1 / 2 : ℂ)‖) := by
                exact mul_assoc
                  |Complex.GammaLogDerivativeFixedVerticalShiftConstant sigma N|
                  (1 + ‖t‖) ‖(1 / 2 : ℂ)‖
              _ =
                |Complex.GammaLogDerivativeFixedVerticalShiftConstant sigma N| *
                  (‖(1 / 2 : ℂ)‖ * (1 + ‖t‖)) := by
                exact congrArg
                  (fun x : ℝ =>
                    |Complex.GammaLogDerivativeFixedVerticalShiftConstant sigma N| * x)
                  (mul_comm (1 + ‖t‖) ‖(1 / 2 : ℂ)‖)
              _ =
                (|Complex.GammaLogDerivativeFixedVerticalShiftConstant sigma N| *
                    ‖(1 / 2 : ℂ)‖) * (1 + ‖t‖) := by
                exact (mul_assoc
                  |Complex.GammaLogDerivativeFixedVerticalShiftConstant sigma N|
                  ‖(1 / 2 : ℂ)‖ (1 + ‖t‖)).symm
              _ =
                (‖(1 / 2 : ℂ)‖ *
                  |Complex.GammaLogDerivativeFixedVerticalShiftConstant sigma N|) *
                    (1 + ‖t‖) := by
                exact congrArg (fun x : ℝ => x * (1 + ‖t‖))
                  (mul_comm
                    |Complex.GammaLogDerivativeFixedVerticalShiftConstant sigma N|
                    ‖(1 / 2 : ℂ)‖)
          _ = B * (1 + ‖t‖) := by
            exact Eq.refl _
      have hqmul_norm :
          ‖q * (1 / 2 : ℂ)‖ ≤ B * (1 + ‖t‖) :=
        Eq.subst
          (motive := fun x : ℝ => x ≤ B * (1 + ‖t‖))
          hmul_norm.symm
          (hprod.trans_eq hcomm)
      exact
        Eq.subst
          (motive := fun w : ℂ => ‖w‖ ≤ B * (1 + ‖t‖))
          halgebra.symm
          hqmul_norm
    exact
      Eq.subst
        (motive := fun w : ℂ =>
          ‖(deriv Complex.Gamma w * (1 / 2 : ℂ)) /
              Complex.Gamma w‖ ≤
            B * (1 + ‖t‖))
        (show z = zetaCompletedExplicitFormulaLeftAffineLine F t / 2 from rfl)
        hnorm_mul
  exact
    zetaCompletedExplicitFormulaInverseGammaCompletionLogDeriv_leftAffineLine_bound_of_halfGamma_logDeriv_bound_owner
      F hregular B hB_nonneg hgamma_bound

/-- Compatibility wrapper for the former shifted coherence-qualified API. -/
theorem zetaCompletedExplicitFormulaInverseGammaCompletionLogDeriv_leftAffineLine_bound_of_gammaBinetCoherence_shift_owner
    (F : ExplicitFormulaContourFamily)
    (hregular : zetaCompletedExplicitFormulaLeftAffineLineGammaRegular F)
    (coherence : Complex.gammaBinetPrincipalLogCoherence)
    (N : ℕ)
    (hshift_pos : 0 < ((1 - F.c) / 2 : ℝ) + (N : ℝ)) :
    ∃ B : ℝ,
      0 ≤ B ∧
        ∀ t : ℝ,
          ‖inverseGammaCompletionLogDeriv
              (zetaCompletedExplicitFormulaLeftAffineLine F t)‖ ≤
            B * (1 + ‖t‖) := by
  exact
    zetaCompletedExplicitFormulaInverseGammaCompletionLogDeriv_leftAffineLine_bound_of_gammaBinet_shift_owner
      F hregular N hshift_pos

/-- The Gamma/Stirling fixed-line estimates give a linear left-line bound for
the inverse-Gamma completion logarithmic derivative under the natural
left-half-line Gamma-regularity condition. -/
theorem zetaCompletedExplicitFormulaInverseGammaCompletionLogDeriv_leftAffineLine_bound_of_gammaBinet_owner
    (F : ExplicitFormulaContourFamily)
    (hregular : zetaCompletedExplicitFormulaLeftAffineLineGammaRegular F) :
    ∃ B : ℝ,
      0 ≤ B ∧
        ∀ t : ℝ,
          ‖inverseGammaCompletionLogDeriv
              (zetaCompletedExplicitFormulaLeftAffineLine F t)‖ ≤
            B * (1 + ‖t‖) := by
  let sigma := ((1 - F.c) / 2 : ℝ)
  match exists_nat_ge (1 - sigma) with
  | ⟨N, hN⟩ =>
      have hone_le_shift : 1 ≤ sigma + (N : ℝ) := by
        have hleft :
            sigma + (1 - sigma) = (1 : ℝ) := by
          calc
            sigma + (1 - sigma) = sigma + (1 + -sigma) := by
              exact congrArg (fun x : ℝ => sigma + x) (sub_eq_add_neg 1 sigma)
            _ = (sigma + 1) + -sigma := by
              exact (add_assoc sigma 1 (-sigma)).symm
            _ = (sigma + -sigma) + 1 := by
              exact add_right_comm sigma 1 (-sigma)
            _ = 0 + 1 := by
              exact congrArg (fun x : ℝ => x + 1) (add_neg_cancel sigma)
            _ = 1 := zero_add 1
        calc
          1 = sigma + (1 - sigma) := hleft.symm
          _ ≤ sigma + (N : ℝ) := by
            exact add_le_add_left hN sigma
      have hshift_pos : 0 < sigma + (N : ℝ) :=
        lt_of_lt_of_le zero_lt_one hone_le_shift
      exact
        zetaCompletedExplicitFormulaInverseGammaCompletionLogDeriv_leftAffineLine_bound_of_gammaBinet_shift_owner
          F hregular N hshift_pos

/-- Compatibility wrapper for the former coherence-qualified left-line API. -/
theorem zetaCompletedExplicitFormulaInverseGammaCompletionLogDeriv_leftAffineLine_bound_of_gammaBinetCoherence_owner
    (F : ExplicitFormulaContourFamily)
    (hregular : zetaCompletedExplicitFormulaLeftAffineLineGammaRegular F)
    (coherence : Complex.gammaBinetPrincipalLogCoherence) :
    ∃ B : ℝ,
      0 ≤ B ∧
        ∀ t : ℝ,
          ‖inverseGammaCompletionLogDeriv
              (zetaCompletedExplicitFormulaLeftAffineLine F t)‖ ≤
            B * (1 + ‖t‖) := by
  exact
    zetaCompletedExplicitFormulaInverseGammaCompletionLogDeriv_leftAffineLine_bound_of_gammaBinet_owner
      F hregular

/- The left-line estimate is likewise provided by the concrete shifted Binet
owner construction and does not require principal-log coherence. -/
theorem zetaCompletedExplicitFormulaInverseGammaCompletionLogDeriv_leftAffineLine_bound_unconditional_owner
    (F : ExplicitFormulaContourFamily)
    (hregular : zetaCompletedExplicitFormulaLeftAffineLineGammaRegular F) :
    ∃ B : ℝ,
      0 ≤ B ∧
        ∀ t : ℝ,
          ‖inverseGammaCompletionLogDeriv
              (zetaCompletedExplicitFormulaLeftAffineLine F t)‖ ≤
            B * (1 + ‖t‖) := by
  exact
    zetaCompletedExplicitFormulaInverseGammaCompletionLogDeriv_leftAffineLine_bound_of_gammaBinet_owner
      F hregular

end ZetaAdmissibleFunction

end
end LFunctions
end Boundary
