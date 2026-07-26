import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaExplicitFormulaVerticalChannels.OwnerParts.InverseGammaAffineKernelEstimateBasic
/-!
# Inverse-Gamma affine-kernel estimate split part

This file is a mechanical owner split of the inverse-Gamma affine-kernel estimate.
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

/-- The conditional fixed-line Binet logarithmic-derivative estimate gives the
right inverse-Gamma affine-kernel majorant once the Gamma coherence package has
been constructed.  This is the exact bridge from the classical Gamma owner
layer to the vertical-channel owner layer. -/
def zetaCompletedExplicitFormulaInverseGammaRightAffineKernel_majorantPackage_of_gammaBinet
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) :
    ExplicitFormulaAffineKernelMajorantPackage
      (zetaCompletedExplicitFormulaInverseGammaRightAffineKernel f F) := by
  let sigma : ℝ := F.c / 2
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
        exact congrArg
          (fun z : ℂ => z / 2)
          (zetaCompletedExplicitFormulaRightAffineLine_eq F t)
      _ = ((F.c : ℂ) / 2) + (t * Complex.I) / 2 := by
        exact add_div (F.c : ℂ) (t * Complex.I) (2 : ℂ)
      _ = (sigma + (t / 2 : ℂ) * Complex.I : ℂ) := by
        have hc :
            ((F.c : ℂ) / 2) = (sigma : ℂ) := by
          exact (Complex.ofReal_div F.c 2).symm
        have ht :
            (t * Complex.I) / 2 = ((t : ℂ) / 2) * Complex.I := by
          exact mul_div_right_comm (t : ℂ) Complex.I (2 : ℂ)
        exact congrArg₂ HAdd.hAdd hc ht
  have hGamma_bound :
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
      exact
        hfixed.trans
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
          exact Eq.refl (q * (1 / 2 : ℂ))
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
            exact
              (mul_assoc
                |Complex.GammaLogDerivativeFixedVerticalPositiveLineConstant sigma|
                ‖(1 / 2 : ℂ)‖ (1 + ‖t‖)).symm
          _ =
                (‖(1 / 2 : ℂ)‖ *
                  |Complex.GammaLogDerivativeFixedVerticalPositiveLineConstant sigma|) *
                    (1 + ‖t‖) := by
            exact congrArg
              (fun x : ℝ => x * (1 + ‖t‖))
              (mul_comm
                |Complex.GammaLogDerivativeFixedVerticalPositiveLineConstant sigma|
                ‖(1 / 2 : ℂ)‖)
          _ = B * (1 + ‖t‖) := by
            exact Eq.refl (B * (1 + ‖t‖))
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
    zetaCompletedExplicitFormulaInverseGammaRightAffineKernel_majorantPackage_of_halfGamma_logDeriv_bound
      f F h B hB_nonneg hGamma_bound

/-- A finite shifted fixed-line Gamma estimate gives the left inverse-Gamma
affine-kernel majorant, provided the left half-line is Gamma-regular and the
chosen natural shift reaches the positive half-plane. -/
theorem zetaCompletedExplicitFormulaInverseGammaCompletionLogDeriv_leftAffineLine_bound_of_gammaBinet_shift
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
  exact
    zetaCompletedExplicitFormulaInverseGammaCompletionLogDeriv_leftAffineLine_bound_of_gammaBinet_shift_owner
      F hregular N hshift_pos

/-- The Gamma/Stirling fixed-line estimates give a linear left-line bound for
the inverse-Gamma completion logarithmic derivative under the natural
left-half-line Gamma-regularity condition. -/
theorem zetaCompletedExplicitFormulaInverseGammaCompletionLogDeriv_leftAffineLine_bound_of_gammaBinet
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

/-- The canonical vertically regular contour family supplies the Gamma
regularity needed by the left affine estimate.  This is the owner-level
transport used by the finite-rectangle contour consumers; it does not add a
new analytic assumption to the contour data. -/
theorem zetaCompletedExplicitFormulaInverseGammaCompletionLogDeriv_leftAffineLine_bound_of_verticallyRegular
    (F : ExplicitFormulaVerticallyRegularContourFamily) :
    ∃ B : ℝ,
      0 ≤ B ∧
        ∀ t : ℝ,
          ‖inverseGammaCompletionLogDeriv
              (zetaCompletedExplicitFormulaLeftAffineLine F.toContourFamily t)‖ ≤
            B * (1 + ‖t‖) := by
  have hregular :
      zetaCompletedExplicitFormulaLeftAffineLineGammaRegular F.toContourFamily :=
    zetaCompletedExplicitFormulaLeftAffineLineGammaRegular_of_verticallyRegular F
  exact
    zetaCompletedExplicitFormulaInverseGammaCompletionLogDeriv_leftAffineLine_bound_of_gammaBinet
      F.toContourFamily hregular

def zetaCompletedExplicitFormulaInverseGammaLeftAffineKernel_majorantPackage_of_gammaBinet_shift
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F)
    (hregular : zetaCompletedExplicitFormulaLeftAffineLineGammaRegular F)
    (N : ℕ)
    (hshift_pos : 0 < ((1 - F.c) / 2 : ℝ) + (N : ℝ)) :
    ExplicitFormulaAffineKernelMajorantPackage
      (zetaCompletedExplicitFormulaInverseGammaLeftAffineKernel f F) := by
  let sigma : ℝ := (1 - F.c) / 2
  let D : ℝ :=
    Complex.GammaLogDerivativeFixedVerticalShiftConstant sigma N
  let B : ℝ := ‖(1 / 2 : ℂ)‖ * |D|
  have hB_nonneg : 0 ≤ B :=
    mul_nonneg
      (norm_nonneg (1 / 2 : ℂ))
      (abs_nonneg D)
  have hhalf_line :
      ∀ t : ℝ,
        zetaCompletedExplicitFormulaLeftAffineLine F t / 2 =
          (((1 - F.c) / 2 : ℝ) +
            (((t / 2 : ℝ) : ℂ) * Complex.I) : ℂ) := by
    exact fun t : ℝ =>
      zetaCompletedExplicitFormulaLeftAffineLine_div_two_eq_fixedVertical F t
  have hnot_pole :
      ∀ u : ℝ, ∀ n : ℕ,
        (sigma + u * Complex.I : ℂ) ≠ -n := by
    intro u n hpole
    have hline :
        zetaCompletedExplicitFormulaLeftAffineLine F (2 * u) / 2 =
          (sigma + u * Complex.I : ℂ) := by
      have hraw :
          zetaCompletedExplicitFormulaLeftAffineLine F (2 * u) / 2 =
            (((1 - F.c) / 2 : ℝ) +
              (((2 * u) / 2 : ℝ) : ℂ) * Complex.I : ℂ) :=
        hhalf_line (2 * u)
      have hheight :
          ((2 * u) / 2 : ℝ) = u := by
        exact mul_div_cancel_left₀ u
          (show (2 : ℝ) ≠ 0 from two_ne_zero)
      have hheight_complex :
          (((2 * u) / 2 : ℝ) : ℂ) * Complex.I =
            (u : ℂ) * Complex.I :=
        congrArg (fun x : ℝ => (x : ℂ) * Complex.I) hheight
      have htarget :
          (((1 - F.c) / 2 : ℝ) +
              (((2 * u) / 2 : ℝ) : ℂ) * Complex.I : ℂ) =
            (sigma + u * Complex.I : ℂ) :=
        Eq.trans
          (congrArg
            (fun z : ℂ => (((1 - F.c) / 2 : ℝ) : ℂ) + z)
            hheight_complex)
          (Eq.refl _)
      exact
        hraw.trans htarget
    exact
      (zetaCompletedExplicitFormulaLeftAffineLine_half_ne_Gamma_zero_locus_of_gammaRegular
        F hregular (2 * u) n)
      (hline.trans hpole)
  have hfixed_bound :
      ∀ u : ℝ,
        ‖deriv Complex.Gamma (sigma + u * Complex.I) /
            Complex.Gamma (sigma + u * Complex.I)‖ ≤
          D * (1 + ‖u‖) :=
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
    let u : ℝ := t / 2
    let z : ℂ := zetaCompletedExplicitFormulaLeftAffineLine F t / 2
    let q : ℂ := deriv Complex.Gamma z / Complex.Gamma z
    have hline :
        z = (sigma + (u : ℂ) * Complex.I : ℂ) :=
      Eq.trans
        (hhalf_line t)
        (congrArg
          (fun x : ℂ => x + (u : ℂ) * Complex.I)
          (show (((1 - F.c) / 2 : ℝ) : ℂ) = (sigma : ℂ) from Eq.refl _))
    have hfixed :
        ‖deriv Complex.Gamma (sigma + (u : ℂ) * Complex.I) /
            Complex.Gamma (sigma + (u : ℂ) * Complex.I)‖ ≤
          D * (1 + ‖u‖) :=
      hfixed_bound u
    have hfixed_abs :
        ‖deriv Complex.Gamma (sigma + (u : ℂ) * Complex.I) /
            Complex.Gamma (sigma + (u : ℂ) * Complex.I)‖ ≤
          |D| * (1 + ‖u‖) := by
      have hfactor_nonneg : 0 ≤ 1 + ‖u‖ :=
        Real.zero_le_one_add_norm u
      have hD_le_abs : D ≤ |D| :=
        le_abs_self D
      have hright :
          D * (1 + ‖u‖) ≤ |D| * (1 + ‖u‖) :=
        mul_le_mul_of_nonneg_right hD_le_abs hfactor_nonneg
      exact hfixed.trans hright
    have hsmall :
        1 + ‖u‖ ≤ 1 + ‖t‖ := by
      have hnorm :
          ‖u‖ ≤ ‖t‖ := by
        calc
          ‖u‖ = ‖t / 2‖ := by
            rfl
          _ = ‖t‖ / ‖(2 : ℝ)‖ := by
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
        ‖deriv Complex.Gamma (sigma + (u : ℂ) * Complex.I) /
            Complex.Gamma (sigma + (u : ℂ) * Complex.I)‖ ≤
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
          exact mul_div_right_comm
            (deriv Complex.Gamma z) (1 / 2 : ℂ) (Complex.Gamma z)
        _ = q * (1 / 2 : ℂ) := by
          rfl
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
              |D| * ((1 + ‖t‖) * ‖(1 / 2 : ℂ)‖) :=
            mul_assoc |D| (1 + ‖t‖) ‖(1 / 2 : ℂ)‖
          _ = |D| * (‖(1 / 2 : ℂ)‖ * (1 + ‖t‖)) := by
            exact congrArg
              (fun x : ℝ => |D| * x)
              (mul_comm (1 + ‖t‖) ‖(1 / 2 : ℂ)‖)
          _ = (|D| * ‖(1 / 2 : ℂ)‖) * (1 + ‖t‖) := by
            exact (mul_assoc |D| ‖(1 / 2 : ℂ)‖ (1 + ‖t‖)).symm
          _ = (‖(1 / 2 : ℂ)‖ * |D|) * (1 + ‖t‖) := by
            exact congrArg
              (fun x : ℝ => x * (1 + ‖t‖))
              (mul_comm |D| ‖(1 / 2 : ℂ)‖)
          _ = B * (1 + ‖t‖) := by
            rfl
      have hq_half_bound :
          ‖q * (1 / 2 : ℂ)‖ ≤ B * (1 + ‖t‖) :=
        hmul_norm.trans_le (hprod.trans_eq hcomm)
      have horiginal_norm :
          ‖(deriv Complex.Gamma z * (1 / 2 : ℂ)) / Complex.Gamma z‖ =
            ‖q * (1 / 2 : ℂ)‖ :=
        congrArg norm halgebra
      exact horiginal_norm.trans_le hq_half_bound
    exact hnorm_mul
  exact
    zetaCompletedExplicitFormulaInverseGammaLeftAffineKernel_majorantPackage_of_halfGamma_logDeriv_bound
      f F h hregular B hB_nonneg hgamma_bound

/-- The Gamma/Stirling fixed-line estimates give the left inverse-Gamma
affine-kernel majorant under the natural left-half-line Gamma-regularity
condition.  The natural shift is chosen by Archimedeanness of `ℝ`. -/
def zetaCompletedExplicitFormulaInverseGammaLeftAffineKernel_majorantPackage_of_gammaBinet
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F)
    (hregular : zetaCompletedExplicitFormulaLeftAffineLineGammaRegular F) :
    ExplicitFormulaAffineKernelMajorantPackage
      (zetaCompletedExplicitFormulaInverseGammaLeftAffineKernel f F) := by
  let sigma : ℝ := (1 - F.c) / 2
  let N : ℕ := Nat.ceil (1 - sigma)
  have hN : 1 - sigma ≤ (N : ℝ) :=
    Nat.le_ceil (1 - sigma)
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
    zetaCompletedExplicitFormulaInverseGammaLeftAffineKernel_majorantPackage_of_gammaBinet_shift
      f F h hregular N hshift_pos

end ZetaAdmissibleFunction

end
end LFunctions
end Boundary
