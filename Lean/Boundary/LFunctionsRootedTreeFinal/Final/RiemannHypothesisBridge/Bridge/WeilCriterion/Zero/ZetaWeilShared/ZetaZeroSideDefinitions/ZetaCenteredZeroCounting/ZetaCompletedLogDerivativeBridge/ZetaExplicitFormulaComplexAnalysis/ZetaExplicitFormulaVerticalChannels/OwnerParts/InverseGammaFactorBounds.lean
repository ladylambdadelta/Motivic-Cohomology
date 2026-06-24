import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaExplicitFormulaVerticalChannels.OwnerParts.AffineLineMeasurability
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ClassicalAnalysis.GammaBinetStirling.Owner

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

/-- A right-line bound for the ordinary `Gammaℝ` logarithmic derivative gives a
right-line bound for the inverse-Gamma completion logarithmic derivative. -/
theorem zetaCompletedExplicitFormulaInverseGammaCompletionLogDeriv_rightAffineLine_bound_of_Gammaℝ_logDeriv_bound_owner
    (F : ExplicitFormulaContourFamily)
    (B : ℝ)
    (hGamma_bound :
      ∀ t : ℝ,
        ‖deriv Gammaℝ (zetaCompletedExplicitFormulaRightAffineLine F t) /
            Gammaℝ (zetaCompletedExplicitFormulaRightAffineLine F t)‖ ≤
          B * (1 + ‖t‖)) :
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
    ⟨C, hC_nonneg,
      zetaCompletedExplicitFormulaInverseGammaCompletionLogDeriv_rightAffineLine_bound_of_Gammaℝ_logDeriv_bound_owner
        F C hGammaℝ_bound⟩

/-- The Gamma/Stirling fixed-line estimates give a linear right-line bound for
the inverse-Gamma completion logarithmic derivative. -/
theorem zetaCompletedExplicitFormulaInverseGammaCompletionLogDeriv_rightAffineLine_bound_of_gammaBinetCoherence_owner
    (F : ExplicitFormulaContourFamily)
    (hcoh : Complex.gammaBinetPrincipalLogCoherence) :
    ∃ B : ℝ,
      0 ≤ B ∧
        ∀ t : ℝ,
          ‖inverseGammaCompletionLogDeriv
              (zetaCompletedExplicitFormulaRightAffineLine F t)‖ ≤
            B * (1 + ‖t‖) := by
  let σ : ℝ := F.c / 2
  let D : ℝ :=
    (((|Real.log σ| + (σ + 1) + Real.pi) + 1 / σ) +
      |‖(2 : ℂ)‖ *
        ∫ u : ℝ in Set.Ioi (0 : ℝ),
          (1 / σ ^ 2) *
            (u / (Real.exp ((2 : ℝ) * Real.pi * u) - 1))|)
  let B : ℝ := ‖(1 / 2 : ℂ)‖ * |D|
  have hσ_pos : 0 < σ :=
    div_pos F.c_pos zero_lt_two
  have hB_nonneg : 0 ≤ B :=
    mul_nonneg
      (norm_nonneg (1 / 2 : ℂ))
      (abs_nonneg D)
  have hhalf_line :
      ∀ t : ℝ,
        zetaCompletedExplicitFormulaRightAffineLine F t / 2 =
          (σ + (t / 2) * Complex.I : ℂ) := by
    intro t
    calc
      zetaCompletedExplicitFormulaRightAffineLine F t / 2 =
          ((F.c : ℂ) + t * Complex.I) / 2 := by
        exact congrArg (fun z : ℂ => z / 2)
          (zetaCompletedExplicitFormulaRightAffineLine_eq F t)
      _ = ((F.c : ℂ) / 2) + (t * Complex.I) / 2 := by
        exact add_div ((F.c : ℂ)) (t * Complex.I) (2 : ℂ)
      _ = (σ + (t / 2) * Complex.I : ℂ) := by
        have hc :
            ((F.c : ℂ) / 2) = (σ : ℂ) := by
          exact Complex.ofReal_div F.c 2
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
    have hline : z = (σ + (t / 2) * Complex.I : ℂ) :=
      hhalf_line t
    have hfixed :
        ‖deriv Complex.Gamma (σ + (t / 2) * Complex.I) /
            Complex.Gamma (σ + (t / 2) * Complex.I)‖ ≤
          D * (1 + ‖t / 2‖) :=
      Complex.Gamma_logDerivative_fixedRealPartLine_linear_bound
        hcoh hσ_pos (t / 2)
    have hfixed_abs :
        ‖deriv Complex.Gamma (σ + (t / 2) * Complex.I) /
            Complex.Gamma (σ + (t / 2) * Complex.I)‖ ≤
          |D| * (1 + ‖t / 2‖) := by
      have hfactor_nonneg : 0 ≤ 1 + ‖t / 2‖ :=
        Real.zero_le_one_add_norm (t / 2)
      have hD_le_abs : D ≤ |D| :=
        le_abs_self D
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
    zetaCompletedExplicitFormulaInverseGammaCompletionLogDeriv_rightAffineLine_bound_of_halfGamma_logDeriv_bound_owner
      F B hB_nonneg hgamma_bound

/-- A left-line bound for the ordinary `Gammaℝ` logarithmic derivative gives a
left-line bound for the inverse-Gamma completion logarithmic derivative. -/
theorem zetaCompletedExplicitFormulaInverseGammaCompletionLogDeriv_leftAffineLine_bound_of_Gammaℝ_logDeriv_bound_owner
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
  intro t
  have hidentity :
      inverseGammaCompletionLogDeriv
          (zetaCompletedExplicitFormulaLeftAffineLine F t) =
        -deriv Gammaℝ (zetaCompletedExplicitFormulaLeftAffineLine F t) /
          Gammaℝ (zetaCompletedExplicitFormulaLeftAffineLine F t) :=
    zetaCompletedExplicitFormulaInverseGammaLogDeriv_leftAffineLine_eq_neg_Gammaℝ_logDeriv_of_gammaRegular
      F hregular t
  have hnorm :
      ‖inverseGammaCompletionLogDeriv
          (zetaCompletedExplicitFormulaLeftAffineLine F t)‖ =
        ‖deriv Gammaℝ (zetaCompletedExplicitFormulaLeftAffineLine F t) /
          Gammaℝ (zetaCompletedExplicitFormulaLeftAffineLine F t)‖ := by
    calc
      ‖inverseGammaCompletionLogDeriv
          (zetaCompletedExplicitFormulaLeftAffineLine F t)‖ =
          ‖-deriv Gammaℝ (zetaCompletedExplicitFormulaLeftAffineLine F t) /
            Gammaℝ (zetaCompletedExplicitFormulaLeftAffineLine F t)‖ := by
        exact congrArg norm hidentity
      _ =
          ‖-(deriv Gammaℝ (zetaCompletedExplicitFormulaLeftAffineLine F t) /
            Gammaℝ (zetaCompletedExplicitFormulaLeftAffineLine F t))‖ := by
        exact congrArg norm
          (neg_div
            (Gammaℝ (zetaCompletedExplicitFormulaLeftAffineLine F t))
            (deriv Gammaℝ (zetaCompletedExplicitFormulaLeftAffineLine F t)))
      _ =
          ‖deriv Gammaℝ (zetaCompletedExplicitFormulaLeftAffineLine F t) /
            Gammaℝ (zetaCompletedExplicitFormulaLeftAffineLine F t)‖ :=
        norm_neg
          (deriv Gammaℝ (zetaCompletedExplicitFormulaLeftAffineLine F t) /
            Gammaℝ (zetaCompletedExplicitFormulaLeftAffineLine F t))
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
        ‖deriv Gammaℝ (zetaCompletedExplicitFormulaLeftAffineLine F t) /
            Gammaℝ (zetaCompletedExplicitFormulaLeftAffineLine F t)‖ ≤
          C * (1 + ‖t‖) := by
    intro t
    let Q : ℂ :=
      (deriv Complex.Gamma
          (zetaCompletedExplicitFormulaLeftAffineLine F t / 2) *
        (1 / 2 : ℂ)) /
        Complex.Gamma
          (zetaCompletedExplicitFormulaLeftAffineLine F t / 2)
    have hdecomp :
        deriv Gammaℝ (zetaCompletedExplicitFormulaLeftAffineLine F t) /
            Gammaℝ (zetaCompletedExplicitFormulaLeftAffineLine F t) =
          Complex.log (Real.pi : ℂ) * (-(1 / 2 : ℂ)) + Q :=
      zetaCompletedExplicitFormulaLeftAffineLine_Gammaℝ_logDeriv_eq_of_gammaRegular
        F hregular t
    have hnorm_split :
        ‖deriv Gammaℝ (zetaCompletedExplicitFormulaLeftAffineLine F t) /
            Gammaℝ (zetaCompletedExplicitFormulaLeftAffineLine F t)‖ ≤
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
theorem zetaCompletedExplicitFormulaInverseGammaCompletionLogDeriv_leftAffineLine_bound_of_gammaBinetCoherence_shift_owner
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
    zetaCompletedExplicitFormulaInverseGammaCompletionLogDeriv_leftAffineLine_bound_of_halfGamma_logDeriv_bound_owner
      F hregular B hB_nonneg hgamma_bound

/-- The Gamma/Stirling fixed-line estimates give a linear left-line bound for
the inverse-Gamma completion logarithmic derivative under the natural
left-half-line Gamma-regularity condition. -/
theorem zetaCompletedExplicitFormulaInverseGammaCompletionLogDeriv_leftAffineLine_bound_of_gammaBinetCoherence_owner
    (F : ExplicitFormulaContourFamily)
    (hregular : zetaCompletedExplicitFormulaLeftAffineLineGammaRegular F)
    (hcoh : Complex.gammaBinetPrincipalLogCoherence) :
    ∃ B : ℝ,
      0 ≤ B ∧
        ∀ t : ℝ,
          ‖inverseGammaCompletionLogDeriv
              (zetaCompletedExplicitFormulaLeftAffineLine F t)‖ ≤
            B * (1 + ‖t‖) := by
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
        zetaCompletedExplicitFormulaInverseGammaCompletionLogDeriv_leftAffineLine_bound_of_gammaBinetCoherence_shift_owner
          F hregular hcoh N hshift_pos

end ZetaAdmissibleFunction

end
end LFunctions
end Boundary
