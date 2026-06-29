import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaExplicitFormulaVerticalChannels.OwnerParts.ArchimedeanGammaBinetMajorants
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaExplicitFormulaVerticalChannels.OwnerParts.ArchimedeanTransport

/-!
# Archimedean Gamma/Binet transport

This file owns scheduled-window exhaustion, pointwise Binet decomposition, and
algebraic transport between affine and coupled Gamma/Binet whole-line values.
It contains no analytic owner value assertion.
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

/-- Scheduled right Binet-main windows converge to the full-line Binet-main
integral. -/
theorem zetaCompletedExplicitFormulaArchimedeanRightBinetMainKernel_scheduledWindow_tendsto_integral
    (f : ZetaAdmissibleFunction)
    (F : ExplicitFormulaVerticallyRegularContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F.toContourFamily) :
    Tendsto
      (fun u : ℝ =>
        ∫ t in Set.Icc
            (-(F.toContourFamily.rectangle
                (h.height_schedule.height u)).T)
            (F.toContourFamily.rectangle
                (h.height_schedule.height u)).T,
          zetaCompletedExplicitFormulaArchimedeanRightBinetMainKernel
            f F.toContourFamily t)
      atTop
      (𝓝 (∫ t : ℝ,
        zetaCompletedExplicitFormulaArchimedeanRightBinetMainKernel
          f F.toContourFamily t)) :=
  explicitFormulaScheduledRectangleWindowIntegral_tendsto_integral_of_majorantPackage
    F.toContourFamily h.height_schedule.height
    (zetaCompletedExplicitFormulaArchimedeanRightBinetMainKernel
      f F.toContourFamily)
    h.height_schedule.cofinal
    (zetaCompletedExplicitFormulaArchimedeanRightBinetMainKernel_majorantPackage
      f F.toContourFamily h)

/-- Scheduled left Binet-main windows converge to the full-line Binet-main
integral. -/
theorem zetaCompletedExplicitFormulaArchimedeanLeftBinetMainKernel_scheduledWindow_tendsto_integral
    (f : ZetaAdmissibleFunction)
    (F : ExplicitFormulaVerticallyRegularContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F.toContourFamily)
    (hregular : zetaCompletedExplicitFormulaLeftAffineLineGammaRegular
      F.toContourFamily) :
    Tendsto
      (fun u : ℝ =>
        ∫ t in Set.Icc
            (-(F.toContourFamily.rectangle
                (h.height_schedule.height u)).T)
            (F.toContourFamily.rectangle
                (h.height_schedule.height u)).T,
          zetaCompletedExplicitFormulaArchimedeanLeftBinetMainKernel
            f F.toContourFamily t)
      atTop
      (𝓝 (∫ t : ℝ,
        zetaCompletedExplicitFormulaArchimedeanLeftBinetMainKernel
          f F.toContourFamily t)) :=
  explicitFormulaScheduledRectangleWindowIntegral_tendsto_integral_of_majorantPackage
    F.toContourFamily h.height_schedule.height
    (zetaCompletedExplicitFormulaArchimedeanLeftBinetMainKernel
      f F.toContourFamily)
    h.height_schedule.cofinal
    (zetaCompletedExplicitFormulaArchimedeanLeftBinetMainKernel_majorantPackage
      f F.toContourFamily h hregular)

/-- Scheduled right Binet-remainder windows converge to the full-line
Binet-remainder integral. -/
theorem zetaCompletedExplicitFormulaArchimedeanRightBinetRemainderKernel_scheduledWindow_tendsto_integral
    (f : ZetaAdmissibleFunction)
    (F : ExplicitFormulaVerticallyRegularContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F.toContourFamily) :
    Tendsto
      (fun u : ℝ =>
        ∫ t in Set.Icc
            (-(F.toContourFamily.rectangle
                (h.height_schedule.height u)).T)
            (F.toContourFamily.rectangle
                (h.height_schedule.height u)).T,
          zetaCompletedExplicitFormulaArchimedeanRightBinetRemainderKernel
            f F.toContourFamily t)
      atTop
      (𝓝 (∫ t : ℝ,
        zetaCompletedExplicitFormulaArchimedeanRightBinetRemainderKernel
          f F.toContourFamily t)) :=
  explicitFormulaScheduledRectangleWindowIntegral_tendsto_integral_of_majorantPackage
    F.toContourFamily h.height_schedule.height
    (zetaCompletedExplicitFormulaArchimedeanRightBinetRemainderKernel
      f F.toContourFamily)
    h.height_schedule.cofinal
    (zetaCompletedExplicitFormulaArchimedeanRightBinetRemainderKernel_majorantPackage
      f F.toContourFamily h)

/-- Scheduled left Binet-remainder windows converge to the full-line
Binet-remainder integral. -/
theorem zetaCompletedExplicitFormulaArchimedeanLeftBinetRemainderKernel_scheduledWindow_tendsto_integral
    (f : ZetaAdmissibleFunction)
    (F : ExplicitFormulaVerticallyRegularContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F.toContourFamily)
    (hregular : zetaCompletedExplicitFormulaLeftAffineLineGammaRegular
      F.toContourFamily) :
    Tendsto
      (fun u : ℝ =>
        ∫ t in Set.Icc
            (-(F.toContourFamily.rectangle
                (h.height_schedule.height u)).T)
            (F.toContourFamily.rectangle
                (h.height_schedule.height u)).T,
          zetaCompletedExplicitFormulaArchimedeanLeftBinetRemainderKernel
            f F.toContourFamily t)
      atTop
      (𝓝 (∫ t : ℝ,
        zetaCompletedExplicitFormulaArchimedeanLeftBinetRemainderKernel
          f F.toContourFamily t)) :=
  explicitFormulaScheduledRectangleWindowIntegral_tendsto_integral_of_majorantPackage
    F.toContourFamily h.height_schedule.height
    (zetaCompletedExplicitFormulaArchimedeanLeftBinetRemainderKernel
      f F.toContourFamily)
    h.height_schedule.cofinal
    (zetaCompletedExplicitFormulaArchimedeanLeftBinetRemainderKernel_majorantPackage
      f F.toContourFamily h hregular)

/-- Algebraic transport from a Gamma logarithmic-derivative Binet
decomposition to the half-weighted derivative appearing in `Gammaℝ'/Gammaℝ`. -/
theorem zetaCompletedExplicitFormula_halfGammaLogDeriv_binet_algebra
    (D G M R : ℂ) :
    D / G = M + R →
      (D * (1 / 2 : ℂ)) / G =
        (1 / 2 : ℂ) * M + (1 / 2 : ℂ) * R := by
  intro h
  calc
    (D * (1 / 2 : ℂ)) / G =
        (D / G) * (1 / 2 : ℂ) := by
      exact (mul_div_right_comm D (1 / 2 : ℂ) G).symm
    _ = (M + R) * (1 / 2 : ℂ) := by
      exact congrArg (fun z : ℂ => z * (1 / 2 : ℂ)) h
    _ = M * (1 / 2 : ℂ) + R * (1 / 2 : ℂ) := by
      exact add_mul M R (1 / 2 : ℂ)
    _ = (1 / 2 : ℂ) * M + (1 / 2 : ℂ) * R := by
      exact congrArg₂ HAdd.hAdd
        (mul_comm M (1 / 2 : ℂ))
        (mul_comm R (1 / 2 : ℂ))

/-- Additive algebra for the archimedean Binet split:
the inverse-Gamma sign and the elementary correction are assigned to the main
piece, while the differentiated Binet remainder keeps the inverse-Gamma sign. -/
theorem zetaCompletedExplicitFormula_archimedeanBinet_logDerivative_algebra
    (P M R C : ℂ) :
    -(P + (M + R)) - C =
      (-(P + M) - C) + -R := by
  have hassoc : P + (M + R) = (P + M) + R :=
    add_assoc P M R
  calc
    -(P + (M + R)) - C =
        -(P + (M + R)) + -C := by
      exact sub_eq_add_neg (-(P + (M + R))) C
    _ = -((P + M) + R) + -C := by
      exact congrArg (fun z : ℂ => -z + -C) hassoc
    _ = (-(P + M) + -R) + -C := by
      exact congrArg (fun z : ℂ => z + -C) (neg_add (P + M) R)
    _ = (-(P + M) + -C) + -R := by
      exact add_right_comm (-(P + M)) (-R) (-C)
    _ = (-(P + M) - C) + -R := by
      exact congrArg (fun z : ℂ => z + -R)
        (sub_eq_add_neg (-(P + M)) C).symm

/-- Pointwise Binet decomposition of the right archimedean affine-line kernel. -/
theorem zetaCompletedExplicitFormulaArchimedeanRightAffineKernel_eq_binetMain_add_remainder
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (hcoh : Complex.gammaBinetPrincipalLogCoherence) (t : ℝ) :
    zetaCompletedExplicitFormulaArchimedeanRightAffineKernel f F t =
      zetaCompletedExplicitFormulaArchimedeanRightBinetMainKernel f F t +
        zetaCompletedExplicitFormulaArchimedeanRightBinetRemainderKernel
          f F t := by
  let s : ℂ := zetaCompletedExplicitFormulaRightAffineLine F t
  let w : ℂ := s / 2
  let σ : ℝ := F.c / 2
  let τ : ℝ := t / 2
  let P : ℂ := zetaCompletedExplicitFormulaGammaRealPiLogDerivativeTerm
  let M : ℂ := (1 / 2 : ℂ) *
    Complex.GammaLogDerivativeFixedVerticalMain σ τ
  let R : ℂ := (1 / 2 : ℂ) *
    Complex.GammaLogDerivativeFixedVerticalRemainder σ τ
  let C : ℂ := explicitFormulaCorrectionLogDerivative s
  let Φ : ℂ :=
    zetaCompletedExplicitFormulaPhi f
      (zetaCompletedExplicitFormulaRightCenteredAffineLine F t)
  have hσ_pos : 0 < σ := by
    exact div_pos F.c_pos zero_lt_two
  have hline : w = (σ + τ * Complex.I : ℂ) := by
    exact zetaCompletedExplicitFormulaRightAffineLine_div_two_eq_fixedVertical
      F t
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
        (Complex.Gamma_logDerivative_fixedRealPartLine_eq_main_add_remainder
          hcoh hσ_pos τ)
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
      zetaCompletedExplicitFormulaRightAffineLine_Gammaℝ_logDeriv_eq F t
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
        F t
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
  calc
    zetaCompletedExplicitFormulaArchimedeanRightAffineKernel f F t =
        explicitFormulaArchimedeanLogDerivative s * Φ := by
      rfl
    _ = ((-(P + M) - C) + -R) * Φ := by
      exact congrArg (fun z : ℂ => z * Φ) hlog
    _ = (-(P + M) - C) * Φ + (-R) * Φ := by
      exact add_mul (-(P + M) - C) (-R) Φ
    _ =
        zetaCompletedExplicitFormulaArchimedeanRightBinetMainKernel f F t +
          zetaCompletedExplicitFormulaArchimedeanRightBinetRemainderKernel
            f F t := by
      rfl

/-- Pointwise Binet decomposition of the left archimedean affine-line kernel.

The left half-line can have negative real part, so this theorem uses the
finite-shift Gamma/Binet decomposition rather than the positive-line Binet
formula directly. -/
theorem zetaCompletedExplicitFormulaArchimedeanLeftAffineKernel_eq_binetMain_add_remainder
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (hregular : zetaCompletedExplicitFormulaLeftAffineLineGammaRegular F)
    (hcoh : Complex.gammaBinetPrincipalLogCoherence) (t : ℝ) :
    zetaCompletedExplicitFormulaArchimedeanLeftAffineKernel f F t =
      zetaCompletedExplicitFormulaArchimedeanLeftBinetMainKernel f F t +
        zetaCompletedExplicitFormulaArchimedeanLeftBinetRemainderKernel
          f F t := by
  let s : ℂ := zetaCompletedExplicitFormulaLeftAffineLine F t
  let w : ℂ := s / 2
  let σ : ℝ := (1 - F.c) / 2
  let τ : ℝ := t / 2
  let N : ℕ := zetaCompletedExplicitFormulaArchimedeanLeftBinetShiftNat F
  let P : ℂ := zetaCompletedExplicitFormulaGammaRealPiLogDerivativeTerm
  let M : ℂ := (1 / 2 : ℂ) *
    Complex.GammaLogDerivativeFixedVerticalShiftNatMain σ N τ
  let R : ℂ := (1 / 2 : ℂ) *
    Complex.GammaLogDerivativeFixedVerticalShiftNatRemainder σ N τ
  let C : ℂ := explicitFormulaCorrectionLogDerivative s
  let Φ : ℂ :=
    zetaCompletedExplicitFormulaPhi f
      (zetaCompletedExplicitFormulaLeftCenteredAffineLine F t)
  have hline : w = (σ + τ * Complex.I : ℂ) := by
    exact zetaCompletedExplicitFormulaLeftAffineLine_div_two_eq_fixedVertical
      F t
  have hσ_shift_pos : 0 < σ + (N : ℝ) := by
    exact
      Complex.GammaLogDerivativeFixedVerticalPositiveShiftNat_pos
        ((1 - F.c) / 2)
  have hnot_pole :
      ∀ u : ℝ, ∀ n : ℕ,
        (σ + u * Complex.I : ℂ) ≠ -n := by
    intro u n
    exact
      zetaCompletedExplicitFormulaLeftFixedVertical_ne_Gamma_zero_locus_of_gammaRegular'
        F hregular u n
  have hgamma_fixed :
      deriv Complex.Gamma w / Complex.Gamma w =
        Complex.GammaLogDerivativeFixedVerticalShiftNatMain σ N τ +
          Complex.GammaLogDerivativeFixedVerticalShiftNatRemainder σ N τ := by
    exact
      Eq.subst
        (motive := fun z : ℂ =>
          deriv Complex.Gamma z / Complex.Gamma z =
            Complex.GammaLogDerivativeFixedVerticalShiftNatMain σ N τ +
              Complex.GammaLogDerivativeFixedVerticalShiftNatRemainder σ N τ)
        hline.symm
        (Complex.Gamma_logDerivative_fixedRealPartLine_eq_shiftNat_main_add_remainder
          hcoh N hσ_shift_pos hnot_pole τ)
  have hhalf :
      (deriv Complex.Gamma w * (1 / 2 : ℂ)) / Complex.Gamma w =
        M + R := by
    exact
      zetaCompletedExplicitFormula_halfGammaLogDeriv_binet_algebra
        (deriv Complex.Gamma w)
        (Complex.Gamma w)
        (Complex.GammaLogDerivativeFixedVerticalShiftNatMain σ N τ)
        (Complex.GammaLogDerivativeFixedVerticalShiftNatRemainder σ N τ)
        hgamma_fixed
  have hgammaR :
      deriv Gammaℝ s / Gammaℝ s = P + (M + R) := by
    have hraw :
        deriv Gammaℝ s / Gammaℝ s =
          P + (deriv Complex.Gamma w * (1 / 2 : ℂ)) /
            Complex.Gamma w :=
      zetaCompletedExplicitFormulaLeftAffineLine_Gammaℝ_logDeriv_eq_of_gammaRegular
        F hregular t
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
      zetaCompletedExplicitFormulaInverseGammaLogDeriv_leftAffineLine_eq_neg_Gammaℝ_logDeriv_of_gammaRegular
        F hregular t
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
  calc
    zetaCompletedExplicitFormulaArchimedeanLeftAffineKernel f F t =
        explicitFormulaArchimedeanLogDerivative s * Φ := by
      rfl
    _ = ((-(P + M) - C) + -R) * Φ := by
      exact congrArg (fun z : ℂ => z * Φ) hlog
    _ = (-(P + M) - C) * Φ + (-R) * Φ := by
      exact add_mul (-(P + M) - C) (-R) Φ
    _ =
        zetaCompletedExplicitFormulaArchimedeanLeftBinetMainKernel f F t +
          zetaCompletedExplicitFormulaArchimedeanLeftBinetRemainderKernel
            f F t := by
      rfl

/-- Additive assembly for a scheduled Gamma/Binet line value.

This lemma contains no analytic estimate: it only turns a pointwise
main-plus-remainder decomposition, a scheduled main-term limit, and a scheduled
remainder decay theorem into the scheduled limit for the original affine-line
kernel. -/
theorem zetaCompletedExplicitFormula_scheduledWindow_tendsto_of_binetMain_add_remainder
    (F : ExplicitFormulaContourFamily)
    (height : ℝ → ℝ)
    (K M R : ℝ → ℂ)
    (value : ℂ)
    (hdecomp : ∀ t : ℝ, K t = M t + R t)
    (hM_integrable :
      ∀ u : ℝ,
        Integrable M
          (volume.restrict
            (Set.Icc
              (-(F.rectangle (height u)).T)
              (F.rectangle (height u)).T)))
    (hR_integrable :
      ∀ u : ℝ,
        Integrable R
          (volume.restrict
            (Set.Icc
              (-(F.rectangle (height u)).T)
              (F.rectangle (height u)).T)))
    (hmain :
      Tendsto
        (fun u : ℝ =>
          ∫ t in Set.Icc
              (-(F.rectangle (height u)).T)
              (F.rectangle (height u)).T,
            M t)
        atTop
        (𝓝 value))
    (hremainder :
      Tendsto
        (fun u : ℝ =>
          ∫ t in Set.Icc
              (-(F.rectangle (height u)).T)
              (F.rectangle (height u)).T,
            R t)
        atTop
        (𝓝 0)) :
    Tendsto
      (fun u : ℝ =>
        ∫ t in Set.Icc
            (-(F.rectangle (height u)).T)
            (F.rectangle (height u)).T,
          K t)
      atTop
      (𝓝 value) := by
  let A : ℝ → ℂ := fun u : ℝ =>
    ∫ t in Set.Icc
        (-(F.rectangle (height u)).T)
        (F.rectangle (height u)).T,
      K t
  let B : ℝ → ℂ := fun u : ℝ =>
    ∫ t in Set.Icc
        (-(F.rectangle (height u)).T)
        (F.rectangle (height u)).T,
      M t
  let C : ℝ → ℂ := fun u : ℝ =>
    ∫ t in Set.Icc
        (-(F.rectangle (height u)).T)
        (F.rectangle (height u)).T,
      R t
  have hsum :
      Tendsto (fun u : ℝ => B u + C u) atTop (𝓝 (value + 0)) :=
    hmain.add hremainder
  have hvalue : value + 0 = value :=
    add_zero value
  have hsum_value :
      Tendsto (fun u : ℝ => B u + C u) atTop (𝓝 value) :=
    Eq.subst
      (motive := fun z : ℂ =>
        Tendsto (fun u : ℝ => B u + C u) atTop (𝓝 z))
      hvalue
      hsum
  have hwindow :
      ∀ u : ℝ, A u = B u + C u := by
    intro u
    have hpoint :
        (fun t : ℝ => K t) = fun t : ℝ => M t + R t := by
      funext t
      exact hdecomp t
    have hintegral :
        A u =
          ∫ t in Set.Icc
              (-(F.rectangle (height u)).T)
              (F.rectangle (height u)).T,
            M t + R t := by
      exact congrArg
        (fun φ : ℝ → ℂ =>
          ∫ t in Set.Icc
              (-(F.rectangle (height u)).T)
              (F.rectangle (height u)).T,
            φ t)
        hpoint
    have hsplit :
        (∫ t in Set.Icc
              (-(F.rectangle (height u)).T)
              (F.rectangle (height u)).T,
            M t + R t) =
          B u + C u := by
      exact
        integral_add
          (μ := volume.restrict
            (Set.Icc
              (-(F.rectangle (height u)).T)
              (F.rectangle (height u)).T))
          (hM_integrable u)
          (hR_integrable u)
    exact Eq.trans hintegral hsplit
  have hfun :
      A = fun u : ℝ => B u + C u := by
    funext u
    exact hwindow u
  exact
    Eq.subst
      (motive := fun φ : ℝ → ℂ =>
        Tendsto φ atTop (𝓝 value))
      hfun.symm
      hsum_value

/-- Scheduled right archimedean line value from the right Binet main/remainder
inputs.  This theorem is pure assembly: all analytic estimates are explicit
arguments. -/
theorem zetaCompletedExplicitFormulaArchimedeanRightAffineKernel_scheduledWindow_tendsto_phiZero_of_binetMain_remainder
    (f : ZetaAdmissibleFunction)
    (F : ExplicitFormulaVerticallyRegularContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F.toContourFamily)
    (hcoh : Complex.gammaBinetPrincipalLogCoherence)
    (hmain_integrable :
      ∀ u : ℝ,
        Integrable
          (zetaCompletedExplicitFormulaArchimedeanRightBinetMainKernel
            f F.toContourFamily)
          (volume.restrict
            (Set.Icc
              (-(F.toContourFamily.rectangle
                  (h.height_schedule.height u)).T)
              (F.toContourFamily.rectangle
                  (h.height_schedule.height u)).T)))
    (hremainder_integrable :
      ∀ u : ℝ,
        Integrable
          (zetaCompletedExplicitFormulaArchimedeanRightBinetRemainderKernel
            f F.toContourFamily)
          (volume.restrict
            (Set.Icc
              (-(F.toContourFamily.rectangle
                  (h.height_schedule.height u)).T)
              (F.toContourFamily.rectangle
                  (h.height_schedule.height u)).T)))
    (hmain :
      Tendsto
        (fun u : ℝ =>
          ∫ t in Set.Icc
              (-(F.toContourFamily.rectangle
                  (h.height_schedule.height u)).T)
              (F.toContourFamily.rectangle
                  (h.height_schedule.height u)).T,
            zetaCompletedExplicitFormulaArchimedeanRightBinetMainKernel
              f F.toContourFamily t)
        atTop
        (𝓝 (zetaCompletedExplicitFormulaPhi f 0)))
    (hremainder :
      Tendsto
        (fun u : ℝ =>
          ∫ t in Set.Icc
              (-(F.toContourFamily.rectangle
                  (h.height_schedule.height u)).T)
              (F.toContourFamily.rectangle
                  (h.height_schedule.height u)).T,
            zetaCompletedExplicitFormulaArchimedeanRightBinetRemainderKernel
              f F.toContourFamily t)
        atTop
        (𝓝 0)) :
    Tendsto
      (fun u : ℝ =>
        ∫ t in Set.Icc
            (-(F.toContourFamily.rectangle
                (h.height_schedule.height u)).T)
            (F.toContourFamily.rectangle
                (h.height_schedule.height u)).T,
          zetaCompletedExplicitFormulaArchimedeanRightAffineKernel
            f F.toContourFamily t)
      atTop
      (𝓝 (zetaCompletedExplicitFormulaPhi f 0)) :=
  zetaCompletedExplicitFormula_scheduledWindow_tendsto_of_binetMain_add_remainder
    F.toContourFamily
    h.height_schedule.height
    (zetaCompletedExplicitFormulaArchimedeanRightAffineKernel
      f F.toContourFamily)
    (zetaCompletedExplicitFormulaArchimedeanRightBinetMainKernel
      f F.toContourFamily)
    (zetaCompletedExplicitFormulaArchimedeanRightBinetRemainderKernel
      f F.toContourFamily)
    (zetaCompletedExplicitFormulaPhi f 0)
    (fun t : ℝ =>
      zetaCompletedExplicitFormulaArchimedeanRightAffineKernel_eq_binetMain_add_remainder
        f F.toContourFamily hcoh t)
    hmain_integrable
    hremainder_integrable
    hmain
    hremainder

/-- Scheduled left archimedean line value from the finite-shift left Binet
main/remainder inputs.  This theorem is pure assembly; the only left-line
regularity used here is for the pointwise Binet decomposition. -/
theorem zetaCompletedExplicitFormulaArchimedeanLeftAffineKernel_scheduledWindow_tendsto_neg_phiZero_of_binetMain_remainder
    (f : ZetaAdmissibleFunction)
    (F : ExplicitFormulaVerticallyRegularContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F.toContourFamily)
    (hcoh : Complex.gammaBinetPrincipalLogCoherence)
    (hmain_integrable :
      ∀ u : ℝ,
        Integrable
          (zetaCompletedExplicitFormulaArchimedeanLeftBinetMainKernel
            f F.toContourFamily)
          (volume.restrict
            (Set.Icc
              (-(F.toContourFamily.rectangle
                  (h.height_schedule.height u)).T)
              (F.toContourFamily.rectangle
                  (h.height_schedule.height u)).T)))
    (hremainder_integrable :
      ∀ u : ℝ,
        Integrable
          (zetaCompletedExplicitFormulaArchimedeanLeftBinetRemainderKernel
            f F.toContourFamily)
          (volume.restrict
            (Set.Icc
              (-(F.toContourFamily.rectangle
                  (h.height_schedule.height u)).T)
              (F.toContourFamily.rectangle
                  (h.height_schedule.height u)).T)))
    (hmain :
      Tendsto
        (fun u : ℝ =>
          ∫ t in Set.Icc
              (-(F.toContourFamily.rectangle
                  (h.height_schedule.height u)).T)
              (F.toContourFamily.rectangle
                  (h.height_schedule.height u)).T,
            zetaCompletedExplicitFormulaArchimedeanLeftBinetMainKernel
              f F.toContourFamily t)
        atTop
        (𝓝 (-(zetaCompletedExplicitFormulaPhi f 0))))
    (hremainder :
      Tendsto
        (fun u : ℝ =>
          ∫ t in Set.Icc
              (-(F.toContourFamily.rectangle
                  (h.height_schedule.height u)).T)
              (F.toContourFamily.rectangle
                  (h.height_schedule.height u)).T,
            zetaCompletedExplicitFormulaArchimedeanLeftBinetRemainderKernel
              f F.toContourFamily t)
        atTop
        (𝓝 0)) :
    Tendsto
      (fun u : ℝ =>
        ∫ t in Set.Icc
            (-(F.toContourFamily.rectangle
                (h.height_schedule.height u)).T)
            (F.toContourFamily.rectangle
                (h.height_schedule.height u)).T,
          zetaCompletedExplicitFormulaArchimedeanLeftAffineKernel
            f F.toContourFamily t)
      atTop
      (𝓝 (-(zetaCompletedExplicitFormulaPhi f 0))) := by
  have hregular :
      zetaCompletedExplicitFormulaLeftAffineLineGammaRegular
        F.toContourFamily :=
    zetaCompletedExplicitFormulaLeftAffineLineGammaRegular_of_verticallyRegular
      F
  exact
    zetaCompletedExplicitFormula_scheduledWindow_tendsto_of_binetMain_add_remainder
      F.toContourFamily
      h.height_schedule.height
      (zetaCompletedExplicitFormulaArchimedeanLeftAffineKernel
        f F.toContourFamily)
      (zetaCompletedExplicitFormulaArchimedeanLeftBinetMainKernel
        f F.toContourFamily)
      (zetaCompletedExplicitFormulaArchimedeanLeftBinetRemainderKernel
        f F.toContourFamily)
      (-(zetaCompletedExplicitFormulaPhi f 0))
      (fun t : ℝ =>
        zetaCompletedExplicitFormulaArchimedeanLeftAffineKernel_eq_binetMain_add_remainder
          f F.toContourFamily hregular hcoh t)
      hmain_integrable
      hremainder_integrable
      hmain
      hremainder

/-- Scheduled right archimedean Gamma/Binet line value from full-line Binet
main and remainder value identities.

This theorem isolates the remaining analytic content to two whole-line
identities: the Binet main integral evaluates to `Φ_f(0)` and the Binet
remainder integral vanishes. -/
theorem zetaCompletedExplicitFormulaArchimedeanRightAffineKernel_scheduledWindow_tendsto_phiZero_of_fullLineBinetValues
    (f : ZetaAdmissibleFunction)
    (F : ExplicitFormulaVerticallyRegularContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F.toContourFamily)
    (hcoh : Complex.gammaBinetPrincipalLogCoherence)
    (hmain_value :
      (∫ t : ℝ,
        zetaCompletedExplicitFormulaArchimedeanRightBinetMainKernel
          f F.toContourFamily t) =
        zetaCompletedExplicitFormulaPhi f 0)
    (hremainder_value :
      (∫ t : ℝ,
        zetaCompletedExplicitFormulaArchimedeanRightBinetRemainderKernel
          f F.toContourFamily t) =
        0) :
    Tendsto
      (fun u : ℝ =>
        ∫ t in Set.Icc
            (-(F.toContourFamily.rectangle
                (h.height_schedule.height u)).T)
            (F.toContourFamily.rectangle
                (h.height_schedule.height u)).T,
          zetaCompletedExplicitFormulaArchimedeanRightAffineKernel
            f F.toContourFamily t)
      atTop
      (𝓝 (zetaCompletedExplicitFormulaPhi f 0)) := by
  have hmain_integrable :
      ∀ u : ℝ,
        Integrable
          (zetaCompletedExplicitFormulaArchimedeanRightBinetMainKernel
            f F.toContourFamily)
          (volume.restrict
            (Set.Icc
              (-(F.toContourFamily.rectangle
                  (h.height_schedule.height u)).T)
              (F.toContourFamily.rectangle
                  (h.height_schedule.height u)).T)) := by
    intro u
    exact
      zetaCompletedExplicitFormulaArchimedeanRightBinetMainKernel_integrable_restrict_Icc
        f F.toContourFamily h
        (-(F.toContourFamily.rectangle (h.height_schedule.height u)).T)
        (F.toContourFamily.rectangle (h.height_schedule.height u)).T
  have hremainder_integrable :
      ∀ u : ℝ,
        Integrable
          (zetaCompletedExplicitFormulaArchimedeanRightBinetRemainderKernel
            f F.toContourFamily)
          (volume.restrict
            (Set.Icc
              (-(F.toContourFamily.rectangle
                  (h.height_schedule.height u)).T)
              (F.toContourFamily.rectangle
                  (h.height_schedule.height u)).T)) := by
    intro u
    exact
      zetaCompletedExplicitFormulaArchimedeanRightBinetRemainderKernel_integrable_restrict_Icc
        f F.toContourFamily h
        (-(F.toContourFamily.rectangle (h.height_schedule.height u)).T)
        (F.toContourFamily.rectangle (h.height_schedule.height u)).T
  have hmain_integral :
      Tendsto
        (fun u : ℝ =>
          ∫ t in Set.Icc
              (-(F.toContourFamily.rectangle
                  (h.height_schedule.height u)).T)
              (F.toContourFamily.rectangle
                  (h.height_schedule.height u)).T,
            zetaCompletedExplicitFormulaArchimedeanRightBinetMainKernel
              f F.toContourFamily t)
        atTop
        (𝓝 (∫ t : ℝ,
          zetaCompletedExplicitFormulaArchimedeanRightBinetMainKernel
            f F.toContourFamily t)) :=
    zetaCompletedExplicitFormulaArchimedeanRightBinetMainKernel_scheduledWindow_tendsto_integral
      f F h
  have hmain :
      Tendsto
        (fun u : ℝ =>
          ∫ t in Set.Icc
              (-(F.toContourFamily.rectangle
                  (h.height_schedule.height u)).T)
              (F.toContourFamily.rectangle
                  (h.height_schedule.height u)).T,
            zetaCompletedExplicitFormulaArchimedeanRightBinetMainKernel
              f F.toContourFamily t)
        atTop
        (𝓝 (zetaCompletedExplicitFormulaPhi f 0)) :=
    Eq.subst
      (motive := fun z : ℂ =>
        Tendsto
          (fun u : ℝ =>
            ∫ t in Set.Icc
                (-(F.toContourFamily.rectangle
                    (h.height_schedule.height u)).T)
                (F.toContourFamily.rectangle
                    (h.height_schedule.height u)).T,
              zetaCompletedExplicitFormulaArchimedeanRightBinetMainKernel
                f F.toContourFamily t)
          atTop
          (𝓝 z))
      hmain_value
      hmain_integral
  have hremainder_integral :
      Tendsto
        (fun u : ℝ =>
          ∫ t in Set.Icc
              (-(F.toContourFamily.rectangle
                  (h.height_schedule.height u)).T)
              (F.toContourFamily.rectangle
                  (h.height_schedule.height u)).T,
            zetaCompletedExplicitFormulaArchimedeanRightBinetRemainderKernel
              f F.toContourFamily t)
        atTop
        (𝓝 (∫ t : ℝ,
          zetaCompletedExplicitFormulaArchimedeanRightBinetRemainderKernel
            f F.toContourFamily t)) :=
    zetaCompletedExplicitFormulaArchimedeanRightBinetRemainderKernel_scheduledWindow_tendsto_integral
      f F h
  have hremainder :
      Tendsto
        (fun u : ℝ =>
          ∫ t in Set.Icc
              (-(F.toContourFamily.rectangle
                  (h.height_schedule.height u)).T)
              (F.toContourFamily.rectangle
                  (h.height_schedule.height u)).T,
            zetaCompletedExplicitFormulaArchimedeanRightBinetRemainderKernel
              f F.toContourFamily t)
        atTop
        (𝓝 0) :=
    Eq.subst
      (motive := fun z : ℂ =>
        Tendsto
          (fun u : ℝ =>
            ∫ t in Set.Icc
                (-(F.toContourFamily.rectangle
                    (h.height_schedule.height u)).T)
                (F.toContourFamily.rectangle
                    (h.height_schedule.height u)).T,
              zetaCompletedExplicitFormulaArchimedeanRightBinetRemainderKernel
                f F.toContourFamily t)
          atTop
          (𝓝 z))
      hremainder_value
      hremainder_integral
  exact
    zetaCompletedExplicitFormulaArchimedeanRightAffineKernel_scheduledWindow_tendsto_phiZero_of_binetMain_remainder
      f F h hcoh hmain_integrable hremainder_integrable hmain hremainder

/-- Scheduled left archimedean Gamma/Binet line value from full-line Binet
main and remainder value identities. -/
theorem zetaCompletedExplicitFormulaArchimedeanLeftAffineKernel_scheduledWindow_tendsto_neg_phiZero_of_fullLineBinetValues
    (f : ZetaAdmissibleFunction)
    (F : ExplicitFormulaVerticallyRegularContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F.toContourFamily)
    (hcoh : Complex.gammaBinetPrincipalLogCoherence)
    (hmain_value :
      (∫ t : ℝ,
        zetaCompletedExplicitFormulaArchimedeanLeftBinetMainKernel
          f F.toContourFamily t) =
        -(zetaCompletedExplicitFormulaPhi f 0))
    (hremainder_value :
      (∫ t : ℝ,
        zetaCompletedExplicitFormulaArchimedeanLeftBinetRemainderKernel
          f F.toContourFamily t) =
        0) :
    Tendsto
      (fun u : ℝ =>
        ∫ t in Set.Icc
            (-(F.toContourFamily.rectangle
                (h.height_schedule.height u)).T)
            (F.toContourFamily.rectangle
                (h.height_schedule.height u)).T,
          zetaCompletedExplicitFormulaArchimedeanLeftAffineKernel
            f F.toContourFamily t)
      atTop
      (𝓝 (-(zetaCompletedExplicitFormulaPhi f 0))) := by
  have hregular :
      zetaCompletedExplicitFormulaLeftAffineLineGammaRegular
        F.toContourFamily :=
    zetaCompletedExplicitFormulaLeftAffineLineGammaRegular_of_verticallyRegular
      F
  have hmain_integrable :
      ∀ u : ℝ,
        Integrable
          (zetaCompletedExplicitFormulaArchimedeanLeftBinetMainKernel
            f F.toContourFamily)
          (volume.restrict
            (Set.Icc
              (-(F.toContourFamily.rectangle
                  (h.height_schedule.height u)).T)
              (F.toContourFamily.rectangle
                  (h.height_schedule.height u)).T)) := by
    intro u
    exact
      zetaCompletedExplicitFormulaArchimedeanLeftBinetMainKernel_integrable_restrict_Icc
        f F.toContourFamily h hregular
        (-(F.toContourFamily.rectangle (h.height_schedule.height u)).T)
        (F.toContourFamily.rectangle (h.height_schedule.height u)).T
  have hremainder_integrable :
      ∀ u : ℝ,
        Integrable
          (zetaCompletedExplicitFormulaArchimedeanLeftBinetRemainderKernel
            f F.toContourFamily)
          (volume.restrict
            (Set.Icc
              (-(F.toContourFamily.rectangle
                  (h.height_schedule.height u)).T)
              (F.toContourFamily.rectangle
                  (h.height_schedule.height u)).T)) := by
    intro u
    exact
      zetaCompletedExplicitFormulaArchimedeanLeftBinetRemainderKernel_integrable_restrict_Icc
        f F.toContourFamily h hregular
        (-(F.toContourFamily.rectangle (h.height_schedule.height u)).T)
        (F.toContourFamily.rectangle (h.height_schedule.height u)).T
  have hmain_integral :
      Tendsto
        (fun u : ℝ =>
          ∫ t in Set.Icc
              (-(F.toContourFamily.rectangle
                  (h.height_schedule.height u)).T)
              (F.toContourFamily.rectangle
                  (h.height_schedule.height u)).T,
            zetaCompletedExplicitFormulaArchimedeanLeftBinetMainKernel
              f F.toContourFamily t)
        atTop
        (𝓝 (∫ t : ℝ,
          zetaCompletedExplicitFormulaArchimedeanLeftBinetMainKernel
            f F.toContourFamily t)) :=
    zetaCompletedExplicitFormulaArchimedeanLeftBinetMainKernel_scheduledWindow_tendsto_integral
      f F h hregular
  have hmain :
      Tendsto
        (fun u : ℝ =>
          ∫ t in Set.Icc
              (-(F.toContourFamily.rectangle
                  (h.height_schedule.height u)).T)
              (F.toContourFamily.rectangle
                  (h.height_schedule.height u)).T,
            zetaCompletedExplicitFormulaArchimedeanLeftBinetMainKernel
              f F.toContourFamily t)
        atTop
        (𝓝 (-(zetaCompletedExplicitFormulaPhi f 0))) :=
    Eq.subst
      (motive := fun z : ℂ =>
        Tendsto
          (fun u : ℝ =>
            ∫ t in Set.Icc
                (-(F.toContourFamily.rectangle
                    (h.height_schedule.height u)).T)
                (F.toContourFamily.rectangle
                    (h.height_schedule.height u)).T,
              zetaCompletedExplicitFormulaArchimedeanLeftBinetMainKernel
                f F.toContourFamily t)
          atTop
          (𝓝 z))
      hmain_value
      hmain_integral
  have hremainder_integral :
      Tendsto
        (fun u : ℝ =>
          ∫ t in Set.Icc
              (-(F.toContourFamily.rectangle
                  (h.height_schedule.height u)).T)
              (F.toContourFamily.rectangle
                  (h.height_schedule.height u)).T,
            zetaCompletedExplicitFormulaArchimedeanLeftBinetRemainderKernel
              f F.toContourFamily t)
        atTop
        (𝓝 (∫ t : ℝ,
          zetaCompletedExplicitFormulaArchimedeanLeftBinetRemainderKernel
            f F.toContourFamily t)) :=
    zetaCompletedExplicitFormulaArchimedeanLeftBinetRemainderKernel_scheduledWindow_tendsto_integral
      f F h hregular
  have hremainder :
      Tendsto
        (fun u : ℝ =>
          ∫ t in Set.Icc
              (-(F.toContourFamily.rectangle
                  (h.height_schedule.height u)).T)
              (F.toContourFamily.rectangle
                  (h.height_schedule.height u)).T,
            zetaCompletedExplicitFormulaArchimedeanLeftBinetRemainderKernel
              f F.toContourFamily t)
        atTop
        (𝓝 0) :=
    Eq.subst
      (motive := fun z : ℂ =>
        Tendsto
          (fun u : ℝ =>
            ∫ t in Set.Icc
                (-(F.toContourFamily.rectangle
                    (h.height_schedule.height u)).T)
                (F.toContourFamily.rectangle
                    (h.height_schedule.height u)).T,
              zetaCompletedExplicitFormulaArchimedeanLeftBinetRemainderKernel
                f F.toContourFamily t)
          atTop
          (𝓝 z))
      hremainder_value
      hremainder_integral
  exact
    zetaCompletedExplicitFormulaArchimedeanLeftAffineKernel_scheduledWindow_tendsto_neg_phiZero_of_binetMain_remainder
      f F h hcoh hmain_integrable hremainder_integrable hmain hremainder

/-- Integrability of the right archimedean affine kernel from its Gamma/Binet
main-plus-remainder decomposition. -/
theorem zetaCompletedExplicitFormulaArchimedeanRightAffineKernel_integrable_ownerGammaBinetLineValue
    (f : ZetaAdmissibleFunction)
    (F : ExplicitFormulaVerticallyRegularContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F.toContourFamily)
    (hcoh : Complex.gammaBinetPrincipalLogCoherence) :
    Integrable
      (zetaCompletedExplicitFormulaArchimedeanRightAffineKernel
        f F.toContourFamily)
      (volume : Measure ℝ) := by
  have hmain :
      Integrable
        (zetaCompletedExplicitFormulaArchimedeanRightBinetMainKernel
          f F.toContourFamily)
        (volume : Measure ℝ) :=
    zetaCompletedExplicitFormulaArchimedeanRightBinetMainKernel_integrable
      f F.toContourFamily h
  have hremainder :
      Integrable
        (zetaCompletedExplicitFormulaArchimedeanRightBinetRemainderKernel
          f F.toContourFamily)
        (volume : Measure ℝ) :=
    zetaCompletedExplicitFormulaArchimedeanRightBinetRemainderKernel_integrable
      f F.toContourFamily h
  have hsum :
      Integrable
        (fun t : ℝ =>
          zetaCompletedExplicitFormulaArchimedeanRightBinetMainKernel
            f F.toContourFamily t +
            zetaCompletedExplicitFormulaArchimedeanRightBinetRemainderKernel
              f F.toContourFamily t)
        (volume : Measure ℝ) :=
    hmain.add hremainder
  have hpoint :
      (zetaCompletedExplicitFormulaArchimedeanRightAffineKernel
        f F.toContourFamily) =ᵐ[volume]
        fun t : ℝ =>
          zetaCompletedExplicitFormulaArchimedeanRightBinetMainKernel
            f F.toContourFamily t +
            zetaCompletedExplicitFormulaArchimedeanRightBinetRemainderKernel
              f F.toContourFamily t :=
    Filter.Eventually.of_forall
      (fun t =>
        zetaCompletedExplicitFormulaArchimedeanRightAffineKernel_eq_binetMain_add_remainder
          f F.toContourFamily hcoh t)
  exact hsum.congr hpoint.symm

/-- Integrability of the left archimedean affine kernel from its Gamma/Binet
main-plus-remainder decomposition. -/
theorem zetaCompletedExplicitFormulaArchimedeanLeftAffineKernel_integrable_ownerGammaBinetLineValue
    (f : ZetaAdmissibleFunction)
    (F : ExplicitFormulaVerticallyRegularContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F.toContourFamily)
    (hcoh : Complex.gammaBinetPrincipalLogCoherence) :
    Integrable
      (zetaCompletedExplicitFormulaArchimedeanLeftAffineKernel
        f F.toContourFamily)
      (volume : Measure ℝ) := by
  have hregular :
      zetaCompletedExplicitFormulaLeftAffineLineGammaRegular
        F.toContourFamily :=
    zetaCompletedExplicitFormulaLeftAffineLineGammaRegular_of_verticallyRegular
      F
  have hmain :
      Integrable
        (zetaCompletedExplicitFormulaArchimedeanLeftBinetMainKernel
          f F.toContourFamily)
        (volume : Measure ℝ) :=
    zetaCompletedExplicitFormulaArchimedeanLeftBinetMainKernel_integrable
      f F.toContourFamily h hregular
  have hremainder :
      Integrable
        (zetaCompletedExplicitFormulaArchimedeanLeftBinetRemainderKernel
          f F.toContourFamily)
        (volume : Measure ℝ) :=
    zetaCompletedExplicitFormulaArchimedeanLeftBinetRemainderKernel_integrable
      f F.toContourFamily h hregular
  have hsum :
      Integrable
        (fun t : ℝ =>
          zetaCompletedExplicitFormulaArchimedeanLeftBinetMainKernel
            f F.toContourFamily t +
            zetaCompletedExplicitFormulaArchimedeanLeftBinetRemainderKernel
              f F.toContourFamily t)
        (volume : Measure ℝ) :=
    hmain.add hremainder
  have hpoint :
      (zetaCompletedExplicitFormulaArchimedeanLeftAffineKernel
        f F.toContourFamily) =ᵐ[volume]
        fun t : ℝ =>
          zetaCompletedExplicitFormulaArchimedeanLeftBinetMainKernel
            f F.toContourFamily t +
            zetaCompletedExplicitFormulaArchimedeanLeftBinetRemainderKernel
              f F.toContourFamily t :=
    Filter.Eventually.of_forall
      (fun t =>
        zetaCompletedExplicitFormulaArchimedeanLeftAffineKernel_eq_binetMain_add_remainder
          f F.toContourFamily hregular hcoh t)
  exact hsum.congr hpoint.symm

/-- Scheduled right archimedean line exhaustion to its whole-line affine
integral. -/
theorem zetaCompletedExplicitFormulaArchimedeanRightAffineKernel_scheduledWindow_tendsto_integral_ownerGammaBinetLineValue
    (f : ZetaAdmissibleFunction)
    (F : ExplicitFormulaVerticallyRegularContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F.toContourFamily)
    (hcoh : Complex.gammaBinetPrincipalLogCoherence) :
    Tendsto
      (fun u : ℝ =>
        ∫ t in Set.Icc
            (-(F.toContourFamily.rectangle (h.height_schedule.height u)).T)
            (F.toContourFamily.rectangle (h.height_schedule.height u)).T,
          zetaCompletedExplicitFormulaArchimedeanRightAffineKernel
            f F.toContourFamily t)
      atTop
      (𝓝 (∫ t : ℝ,
        zetaCompletedExplicitFormulaArchimedeanRightAffineKernel
          f F.toContourFamily t)) :=
  explicitFormulaScheduledRectangleWindowIntegral_tendsto_integral
    F.toContourFamily
    h.height_schedule.height
    (zetaCompletedExplicitFormulaArchimedeanRightAffineKernel
      f F.toContourFamily)
    h.height_schedule.cofinal
    (zetaCompletedExplicitFormulaArchimedeanRightAffineKernel_integrable_ownerGammaBinetLineValue
      f F h hcoh)

/-- Scheduled left archimedean line exhaustion to its whole-line affine
integral. -/
theorem zetaCompletedExplicitFormulaArchimedeanLeftAffineKernel_scheduledWindow_tendsto_integral_ownerGammaBinetLineValue
    (f : ZetaAdmissibleFunction)
    (F : ExplicitFormulaVerticallyRegularContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F.toContourFamily)
    (hcoh : Complex.gammaBinetPrincipalLogCoherence) :
    Tendsto
      (fun u : ℝ =>
        ∫ t in Set.Icc
            (-(F.toContourFamily.rectangle (h.height_schedule.height u)).T)
            (F.toContourFamily.rectangle (h.height_schedule.height u)).T,
          zetaCompletedExplicitFormulaArchimedeanLeftAffineKernel
            f F.toContourFamily t)
      atTop
      (𝓝 (∫ t : ℝ,
        zetaCompletedExplicitFormulaArchimedeanLeftAffineKernel
          f F.toContourFamily t)) :=
  explicitFormulaScheduledRectangleWindowIntegral_tendsto_integral
    F.toContourFamily
    h.height_schedule.height
    (zetaCompletedExplicitFormulaArchimedeanLeftAffineKernel
      f F.toContourFamily)
    h.height_schedule.cofinal
    (zetaCompletedExplicitFormulaArchimedeanLeftAffineKernel_integrable_ownerGammaBinetLineValue
      f F h hcoh)

/-- Scheduled right archimedean line value from the whole-line affine value. -/
theorem zetaCompletedExplicitFormulaArchimedeanRightAffineKernel_scheduledWindow_tendsto_phiZero_of_fullLineAffineValue
    (f : ZetaAdmissibleFunction)
    (F : ExplicitFormulaVerticallyRegularContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F.toContourFamily)
    (hcoh : Complex.gammaBinetPrincipalLogCoherence)
    (hvalue :
      (∫ t : ℝ,
        zetaCompletedExplicitFormulaArchimedeanRightAffineKernel
          f F.toContourFamily t) =
        zetaCompletedExplicitFormulaPhi f 0) :
    Tendsto
      (fun u : ℝ =>
        ∫ t in Set.Icc
            (-(F.toContourFamily.rectangle (h.height_schedule.height u)).T)
            (F.toContourFamily.rectangle (h.height_schedule.height u)).T,
          zetaCompletedExplicitFormulaArchimedeanRightAffineKernel
            f F.toContourFamily t)
      atTop
      (𝓝 (zetaCompletedExplicitFormulaPhi f 0)) :=
  Eq.subst
    (motive := fun z : ℂ =>
      Tendsto
        (fun u : ℝ =>
          ∫ t in Set.Icc
              (-(F.toContourFamily.rectangle (h.height_schedule.height u)).T)
              (F.toContourFamily.rectangle (h.height_schedule.height u)).T,
            zetaCompletedExplicitFormulaArchimedeanRightAffineKernel
              f F.toContourFamily t)
        atTop
        (𝓝 z))
    hvalue
    (zetaCompletedExplicitFormulaArchimedeanRightAffineKernel_scheduledWindow_tendsto_integral_ownerGammaBinetLineValue
      f F h hcoh)

/-- Scheduled left archimedean line value from the whole-line affine value. -/
theorem zetaCompletedExplicitFormulaArchimedeanLeftAffineKernel_scheduledWindow_tendsto_neg_phiZero_of_fullLineAffineValue
    (f : ZetaAdmissibleFunction)
    (F : ExplicitFormulaVerticallyRegularContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F.toContourFamily)
    (hcoh : Complex.gammaBinetPrincipalLogCoherence)
    (hvalue :
      (∫ t : ℝ,
        zetaCompletedExplicitFormulaArchimedeanLeftAffineKernel
          f F.toContourFamily t) =
        -(zetaCompletedExplicitFormulaPhi f 0)) :
    Tendsto
      (fun u : ℝ =>
        ∫ t in Set.Icc
            (-(F.toContourFamily.rectangle (h.height_schedule.height u)).T)
            (F.toContourFamily.rectangle (h.height_schedule.height u)).T,
          zetaCompletedExplicitFormulaArchimedeanLeftAffineKernel
            f F.toContourFamily t)
      atTop
      (𝓝 (-(zetaCompletedExplicitFormulaPhi f 0))) :=
  Eq.subst
    (motive := fun z : ℂ =>
      Tendsto
        (fun u : ℝ =>
          ∫ t in Set.Icc
              (-(F.toContourFamily.rectangle (h.height_schedule.height u)).T)
              (F.toContourFamily.rectangle (h.height_schedule.height u)).T,
            zetaCompletedExplicitFormulaArchimedeanLeftAffineKernel
              f F.toContourFamily t)
        atTop
        (𝓝 z))
    hvalue
    (zetaCompletedExplicitFormulaArchimedeanLeftAffineKernel_scheduledWindow_tendsto_integral_ownerGammaBinetLineValue
      f F h hcoh)

/-- Whole-line right archimedean affine value from a direct scheduled affine
contour value.

This is exhaustion and uniqueness of limits only.  It is the non-circular
transport direction needed when the contour proof evaluates the affine line
directly, before any Gamma/Binet full-transform line value has been proved. -/
theorem zetaCompletedExplicitFormulaArchimedeanRightAffineKernel_integral_eq_phiZero_of_scheduledWindow
    (f : ZetaAdmissibleFunction)
    (F : ExplicitFormulaVerticallyRegularContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F.toContourFamily)
    (hcoh : Complex.gammaBinetPrincipalLogCoherence)
    (hscheduled :
      Tendsto
        (fun u : ℝ =>
          ∫ t in Set.Icc
              (-(F.toContourFamily.rectangle
                  (h.height_schedule.height u)).T)
              (F.toContourFamily.rectangle
                  (h.height_schedule.height u)).T,
            zetaCompletedExplicitFormulaArchimedeanRightAffineKernel
              f F.toContourFamily t)
        atTop
        (𝓝 (zetaCompletedExplicitFormulaPhi f 0))) :
    (∫ t : ℝ,
      zetaCompletedExplicitFormulaArchimedeanRightAffineKernel
        f F.toContourFamily t) =
      zetaCompletedExplicitFormulaPhi f 0 := by
  exact
    explicitFormulaScheduledScalar_integral_eq_of_tendsto_integral_and_value
      (fun u : ℝ =>
        ∫ t in Set.Icc
            (-(F.toContourFamily.rectangle
                (h.height_schedule.height u)).T)
            (F.toContourFamily.rectangle
                (h.height_schedule.height u)).T,
          zetaCompletedExplicitFormulaArchimedeanRightAffineKernel
            f F.toContourFamily t)
      (∫ t : ℝ,
        zetaCompletedExplicitFormulaArchimedeanRightAffineKernel
          f F.toContourFamily t)
      (zetaCompletedExplicitFormulaPhi f 0)
      (zetaCompletedExplicitFormulaArchimedeanRightAffineKernel_scheduledWindow_tendsto_integral_ownerGammaBinetLineValue
        f F h hcoh)
      hscheduled

/-- Whole-line shifted-left archimedean affine value from a direct scheduled
affine contour value.

This is the shifted-left companion to
`zetaCompletedExplicitFormulaArchimedeanRightAffineKernel_integral_eq_phiZero_of_scheduledWindow`;
no right-minus-left symmetry or downstream Binet line value is used. -/
theorem zetaCompletedExplicitFormulaArchimedeanLeftAffineKernel_integral_eq_neg_phiZero_of_scheduledWindow
    (f : ZetaAdmissibleFunction)
    (F : ExplicitFormulaVerticallyRegularContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F.toContourFamily)
    (hcoh : Complex.gammaBinetPrincipalLogCoherence)
    (hscheduled :
      Tendsto
        (fun u : ℝ =>
          ∫ t in Set.Icc
              (-(F.toContourFamily.rectangle
                  (h.height_schedule.height u)).T)
              (F.toContourFamily.rectangle
                  (h.height_schedule.height u)).T,
            zetaCompletedExplicitFormulaArchimedeanLeftAffineKernel
              f F.toContourFamily t)
        atTop
        (𝓝 (-(zetaCompletedExplicitFormulaPhi f 0)))) :
    (∫ t : ℝ,
      zetaCompletedExplicitFormulaArchimedeanLeftAffineKernel
        f F.toContourFamily t) =
      -(zetaCompletedExplicitFormulaPhi f 0) := by
  exact
    explicitFormulaScheduledScalar_integral_eq_of_tendsto_integral_and_value
      (fun u : ℝ =>
        ∫ t in Set.Icc
            (-(F.toContourFamily.rectangle
                (h.height_schedule.height u)).T)
            (F.toContourFamily.rectangle
                (h.height_schedule.height u)).T,
          zetaCompletedExplicitFormulaArchimedeanLeftAffineKernel
            f F.toContourFamily t)
      (∫ t : ℝ,
        zetaCompletedExplicitFormulaArchimedeanLeftAffineKernel
          f F.toContourFamily t)
      (-(zetaCompletedExplicitFormulaPhi f 0))
      (zetaCompletedExplicitFormulaArchimedeanLeftAffineKernel_scheduledWindow_tendsto_integral_ownerGammaBinetLineValue
        f F h hcoh)
      hscheduled

/-- Paired whole-line affine values from direct paired scheduled affine contour
values.

This theorem is deliberately placed in the transport layer: it contains no
analytic contour evaluation, only the exhaustion step for the already paired
right and shifted-left scheduled values. -/
theorem zetaCompletedExplicitFormulaArchimedeanAffineKernel_integral_pair_of_scheduledWindow
    (f : ZetaAdmissibleFunction)
    (F : ExplicitFormulaVerticallyRegularContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F.toContourFamily)
    (hcoh : Complex.gammaBinetPrincipalLogCoherence)
    (hscheduled :
      Tendsto
        (fun u : ℝ =>
          ∫ t in Set.Icc
              (-(F.toContourFamily.rectangle
                  (h.height_schedule.height u)).T)
              (F.toContourFamily.rectangle
                  (h.height_schedule.height u)).T,
            zetaCompletedExplicitFormulaArchimedeanRightAffineKernel
              f F.toContourFamily t)
        atTop
        (𝓝 (zetaCompletedExplicitFormulaPhi f 0)) ∧
      Tendsto
        (fun u : ℝ =>
          ∫ t in Set.Icc
              (-(F.toContourFamily.rectangle
                  (h.height_schedule.height u)).T)
              (F.toContourFamily.rectangle
                  (h.height_schedule.height u)).T,
            zetaCompletedExplicitFormulaArchimedeanLeftAffineKernel
              f F.toContourFamily t)
        atTop
        (𝓝 (-(zetaCompletedExplicitFormulaPhi f 0)))) :
    ((∫ t : ℝ,
      zetaCompletedExplicitFormulaArchimedeanRightAffineKernel
        f F.toContourFamily t) =
      zetaCompletedExplicitFormulaPhi f 0) ∧
    ((∫ t : ℝ,
      zetaCompletedExplicitFormulaArchimedeanLeftAffineKernel
        f F.toContourFamily t) =
      -(zetaCompletedExplicitFormulaPhi f 0)) := by
  exact
    ⟨zetaCompletedExplicitFormulaArchimedeanRightAffineKernel_integral_eq_phiZero_of_scheduledWindow
        f F h hcoh hscheduled.1,
      zetaCompletedExplicitFormulaArchimedeanLeftAffineKernel_integral_eq_neg_phiZero_of_scheduledWindow
        f F h hcoh hscheduled.2⟩

/-- Integrability of the right elementary correction affine kernel. -/
theorem zetaCompletedExplicitFormulaCorrectionRightAffineKernel_integrable_ownerGammaBinetLineValue
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) :
    Integrable
      (zetaCompletedExplicitFormulaCorrectionRightAffineKernel f F)
      (volume : Measure ℝ) := by
  have hzero :
      Integrable
        (zetaCompletedExplicitFormulaCorrectionRightZeroPoleAffineKernel f F)
        (volume : Measure ℝ) :=
    zetaCompletedExplicitFormulaCorrectionRightZeroPoleAffineKernel_integrable_ownerBounds
      f F h
  have hone :
      Integrable
        (zetaCompletedExplicitFormulaCorrectionRightOnePoleAffineKernel f F)
        (volume : Measure ℝ) :=
    zetaCompletedExplicitFormulaCorrectionRightOnePoleAffineKernel_integrable_ownerBounds
      f F h
  have hsum :
      Integrable
        (fun t : ℝ =>
          zetaCompletedExplicitFormulaCorrectionRightZeroPoleAffineKernel
            f F t +
            zetaCompletedExplicitFormulaCorrectionRightOnePoleAffineKernel
              f F t)
        (volume : Measure ℝ) :=
    hzero.add hone
  have hpoint :
      (zetaCompletedExplicitFormulaCorrectionRightAffineKernel f F) =ᵐ[volume]
        fun t : ℝ =>
          zetaCompletedExplicitFormulaCorrectionRightZeroPoleAffineKernel
            f F t +
            zetaCompletedExplicitFormulaCorrectionRightOnePoleAffineKernel
              f F t :=
    Filter.Eventually.of_forall
      (fun t =>
        zetaCompletedExplicitFormulaCorrectionRightAffineKernel_eq_zeroPole_add_onePole
          f F t)
  exact hsum.congr hpoint.symm

/-- Integrability of the left elementary correction affine kernel. -/
theorem zetaCompletedExplicitFormulaCorrectionLeftAffineKernel_integrable_ownerGammaBinetLineValue
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) :
    Integrable
      (zetaCompletedExplicitFormulaCorrectionLeftAffineKernel f F)
      (volume : Measure ℝ) := by
  have hzero :
      Integrable
        (zetaCompletedExplicitFormulaCorrectionLeftZeroPoleAffineKernel f F)
        (volume : Measure ℝ) :=
    zetaCompletedExplicitFormulaCorrectionLeftZeroPoleAffineKernel_integrable_ownerBounds
      f F h
  have hone :
      Integrable
        (zetaCompletedExplicitFormulaCorrectionLeftOnePoleAffineKernel f F)
        (volume : Measure ℝ) :=
    zetaCompletedExplicitFormulaCorrectionLeftOnePoleAffineKernel_integrable_ownerBounds
      f F h
  have hsum :
      Integrable
        (fun t : ℝ =>
          zetaCompletedExplicitFormulaCorrectionLeftZeroPoleAffineKernel
            f F t +
            zetaCompletedExplicitFormulaCorrectionLeftOnePoleAffineKernel
              f F t)
        (volume : Measure ℝ) :=
    hzero.add hone
  have hpoint :
      (zetaCompletedExplicitFormulaCorrectionLeftAffineKernel f F) =ᵐ[volume]
        fun t : ℝ =>
          zetaCompletedExplicitFormulaCorrectionLeftZeroPoleAffineKernel
            f F t +
            zetaCompletedExplicitFormulaCorrectionLeftOnePoleAffineKernel
              f F t :=
    Filter.Eventually.of_forall
      (fun t =>
        zetaCompletedExplicitFormulaCorrectionLeftAffineKernel_eq_zeroPole_add_onePole
          f F t)
  exact hsum.congr hpoint.symm

/-- Right archimedean affine whole-line value from the four Gamma/Binet
full-line value identities.

This is pure conditional assembly from component values.  It should only be
used when the separate Binet component values have actually been proved; the
unconditional owner route evaluates the full affine value without assuming a
separate remainder vanishing theorem. -/
theorem zetaCompletedExplicitFormulaArchimedeanRightAffineKernel_integral_eq_phiZero_of_fullLineBinetValues
    (f : ZetaAdmissibleFunction)
    (F : ExplicitFormulaVerticallyRegularContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F.toContourFamily)
    (hcoh : Complex.gammaBinetPrincipalLogCoherence)
    (hmain_value :
      (∫ t : ℝ,
        zetaCompletedExplicitFormulaArchimedeanRightBinetMainKernel
          f F.toContourFamily t) =
        zetaCompletedExplicitFormulaPhi f 0)
    (hremainder_value :
      (∫ t : ℝ,
        zetaCompletedExplicitFormulaArchimedeanRightBinetRemainderKernel
          f F.toContourFamily t) =
        0) :
    (∫ t : ℝ,
      zetaCompletedExplicitFormulaArchimedeanRightAffineKernel
        f F.toContourFamily t) =
      zetaCompletedExplicitFormulaPhi f 0 := by
  exact
    explicitFormulaScheduledScalar_integral_eq_of_tendsto_integral_and_value
      (fun u : ℝ =>
        ∫ t in Set.Icc
            (-(F.toContourFamily.rectangle
                (h.height_schedule.height u)).T)
            (F.toContourFamily.rectangle
                (h.height_schedule.height u)).T,
          zetaCompletedExplicitFormulaArchimedeanRightAffineKernel
            f F.toContourFamily t)
      (∫ t : ℝ,
        zetaCompletedExplicitFormulaArchimedeanRightAffineKernel
          f F.toContourFamily t)
      (zetaCompletedExplicitFormulaPhi f 0)
      (zetaCompletedExplicitFormulaArchimedeanRightAffineKernel_scheduledWindow_tendsto_integral_ownerGammaBinetLineValue
        f F h hcoh)
      (zetaCompletedExplicitFormulaArchimedeanRightAffineKernel_scheduledWindow_tendsto_phiZero_of_fullLineBinetValues
        f F h hcoh hmain_value hremainder_value)

/-- Left archimedean affine whole-line value from the four Gamma/Binet
full-line value identities.

This is pure conditional assembly from component values.  It should only be
used when the separate shifted Binet component values have actually been
proved; the unconditional owner route evaluates the full affine value without
assuming a separate shifted remainder vanishing theorem. -/
theorem zetaCompletedExplicitFormulaArchimedeanLeftAffineKernel_integral_eq_neg_phiZero_of_fullLineBinetValues
    (f : ZetaAdmissibleFunction)
    (F : ExplicitFormulaVerticallyRegularContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F.toContourFamily)
    (hcoh : Complex.gammaBinetPrincipalLogCoherence)
    (hmain_value :
      (∫ t : ℝ,
        zetaCompletedExplicitFormulaArchimedeanLeftBinetMainKernel
          f F.toContourFamily t) =
        -(zetaCompletedExplicitFormulaPhi f 0))
    (hremainder_value :
      (∫ t : ℝ,
        zetaCompletedExplicitFormulaArchimedeanLeftBinetRemainderKernel
          f F.toContourFamily t) =
        0) :
    (∫ t : ℝ,
      zetaCompletedExplicitFormulaArchimedeanLeftAffineKernel
        f F.toContourFamily t) =
      -(zetaCompletedExplicitFormulaPhi f 0) := by
  exact
    explicitFormulaScheduledScalar_integral_eq_of_tendsto_integral_and_value
      (fun u : ℝ =>
        ∫ t in Set.Icc
            (-(F.toContourFamily.rectangle
                (h.height_schedule.height u)).T)
            (F.toContourFamily.rectangle
                (h.height_schedule.height u)).T,
          zetaCompletedExplicitFormulaArchimedeanLeftAffineKernel
            f F.toContourFamily t)
      (∫ t : ℝ,
        zetaCompletedExplicitFormulaArchimedeanLeftAffineKernel
          f F.toContourFamily t)
      (-(zetaCompletedExplicitFormulaPhi f 0))
      (zetaCompletedExplicitFormulaArchimedeanLeftAffineKernel_scheduledWindow_tendsto_integral_ownerGammaBinetLineValue
        f F h hcoh)
      (zetaCompletedExplicitFormulaArchimedeanLeftAffineKernel_scheduledWindow_tendsto_neg_phiZero_of_fullLineBinetValues
        f F h hcoh hmain_value hremainder_value)

/-- Whole-line right affine Gamma/Binet integral decomposes as the sum of the
main and differentiated-remainder whole-line integrals.

This is only measure-theoretic assembly from the pointwise Binet split.  It
does not assert that either component has a separate closed form. -/
theorem zetaCompletedExplicitFormulaArchimedeanRightAffineKernel_integral_eq_binetMain_add_remainder_integrals
    (f : ZetaAdmissibleFunction)
    (F : ExplicitFormulaVerticallyRegularContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F.toContourFamily)
    (hcoh : Complex.gammaBinetPrincipalLogCoherence) :
    (∫ t : ℝ,
      zetaCompletedExplicitFormulaArchimedeanRightAffineKernel
        f F.toContourFamily t) =
      (∫ t : ℝ,
        zetaCompletedExplicitFormulaArchimedeanRightBinetMainKernel
          f F.toContourFamily t) +
        ∫ t : ℝ,
          zetaCompletedExplicitFormulaArchimedeanRightBinetRemainderKernel
            f F.toContourFamily t := by
  have hmain :
      Integrable
        (zetaCompletedExplicitFormulaArchimedeanRightBinetMainKernel
          f F.toContourFamily)
        (volume : Measure ℝ) :=
    zetaCompletedExplicitFormulaArchimedeanRightBinetMainKernel_integrable
      f F.toContourFamily h
  have hremainder :
      Integrable
        (zetaCompletedExplicitFormulaArchimedeanRightBinetRemainderKernel
          f F.toContourFamily)
        (volume : Measure ℝ) :=
    zetaCompletedExplicitFormulaArchimedeanRightBinetRemainderKernel_integrable
      f F.toContourFamily h
  have hsum :
      (∫ t : ℝ,
        zetaCompletedExplicitFormulaArchimedeanRightBinetMainKernel
          f F.toContourFamily t +
          zetaCompletedExplicitFormulaArchimedeanRightBinetRemainderKernel
            f F.toContourFamily t) =
        (∫ t : ℝ,
          zetaCompletedExplicitFormulaArchimedeanRightBinetMainKernel
            f F.toContourFamily t) +
          ∫ t : ℝ,
            zetaCompletedExplicitFormulaArchimedeanRightBinetRemainderKernel
              f F.toContourFamily t :=
    integral_add hmain hremainder
  have hpoint :
      (zetaCompletedExplicitFormulaArchimedeanRightAffineKernel
        f F.toContourFamily) =ᵐ[volume]
        fun t : ℝ =>
          zetaCompletedExplicitFormulaArchimedeanRightBinetMainKernel
            f F.toContourFamily t +
            zetaCompletedExplicitFormulaArchimedeanRightBinetRemainderKernel
              f F.toContourFamily t :=
    Filter.Eventually.of_forall
      (fun t =>
        zetaCompletedExplicitFormulaArchimedeanRightAffineKernel_eq_binetMain_add_remainder
          f F.toContourFamily hcoh t)
  exact Eq.trans (integral_congr_ae hpoint) hsum

/-- Whole-line left affine Gamma/Binet integral decomposes as the sum of the
shifted main and differentiated-remainder whole-line integrals.

This is only measure-theoretic assembly from the pointwise shifted-Binet split.
It does not assert that either component has a separate closed form. -/
theorem zetaCompletedExplicitFormulaArchimedeanLeftAffineKernel_integral_eq_binetMain_add_remainder_integrals
    (f : ZetaAdmissibleFunction)
    (F : ExplicitFormulaVerticallyRegularContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F.toContourFamily)
    (hcoh : Complex.gammaBinetPrincipalLogCoherence) :
    (∫ t : ℝ,
      zetaCompletedExplicitFormulaArchimedeanLeftAffineKernel
        f F.toContourFamily t) =
      (∫ t : ℝ,
        zetaCompletedExplicitFormulaArchimedeanLeftBinetMainKernel
          f F.toContourFamily t) +
        ∫ t : ℝ,
          zetaCompletedExplicitFormulaArchimedeanLeftBinetRemainderKernel
            f F.toContourFamily t := by
  have hregular :
      zetaCompletedExplicitFormulaLeftAffineLineGammaRegular
        F.toContourFamily :=
    zetaCompletedExplicitFormulaLeftAffineLineGammaRegular_of_verticallyRegular
      F
  have hmain :
      Integrable
        (zetaCompletedExplicitFormulaArchimedeanLeftBinetMainKernel
          f F.toContourFamily)
        (volume : Measure ℝ) :=
    zetaCompletedExplicitFormulaArchimedeanLeftBinetMainKernel_integrable
      f F.toContourFamily h hregular
  have hremainder :
      Integrable
        (zetaCompletedExplicitFormulaArchimedeanLeftBinetRemainderKernel
          f F.toContourFamily)
        (volume : Measure ℝ) :=
    zetaCompletedExplicitFormulaArchimedeanLeftBinetRemainderKernel_integrable
      f F.toContourFamily h hregular
  have hsum :
      (∫ t : ℝ,
        zetaCompletedExplicitFormulaArchimedeanLeftBinetMainKernel
          f F.toContourFamily t +
          zetaCompletedExplicitFormulaArchimedeanLeftBinetRemainderKernel
            f F.toContourFamily t) =
        (∫ t : ℝ,
          zetaCompletedExplicitFormulaArchimedeanLeftBinetMainKernel
            f F.toContourFamily t) +
          ∫ t : ℝ,
            zetaCompletedExplicitFormulaArchimedeanLeftBinetRemainderKernel
              f F.toContourFamily t :=
    integral_add hmain hremainder
  have hpoint :
      (zetaCompletedExplicitFormulaArchimedeanLeftAffineKernel
        f F.toContourFamily) =ᵐ[volume]
        fun t : ℝ =>
          zetaCompletedExplicitFormulaArchimedeanLeftBinetMainKernel
            f F.toContourFamily t +
            zetaCompletedExplicitFormulaArchimedeanLeftBinetRemainderKernel
              f F.toContourFamily t :=
    Filter.Eventually.of_forall
      (fun t =>
        zetaCompletedExplicitFormulaArchimedeanLeftAffineKernel_eq_binetMain_add_remainder
              f F.toContourFamily hregular hcoh t)
  exact Eq.trans (integral_congr_ae hpoint) hsum

/-- Coupled right Gamma/Binet full-transform value from an independently
proved whole-line right affine value.

This is only decomposition transport.  It is useful if the affine value is
proved directly from a Binet inversion theorem; it must not be used with the
owner theorem below, which itself consumes the coupled Binet full-transform
value. -/
theorem zetaCompletedExplicitFormulaArchimedeanRightBinetFullTransform_integral_eq_phiZero_of_affineValue
    (f : ZetaAdmissibleFunction)
    (F : ExplicitFormulaVerticallyRegularContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F.toContourFamily)
    (hcoh : Complex.gammaBinetPrincipalLogCoherence)
    (haffine :
      (∫ t : ℝ,
        zetaCompletedExplicitFormulaArchimedeanRightAffineKernel
          f F.toContourFamily t) =
        zetaCompletedExplicitFormulaPhi f 0) :
    (∫ t : ℝ,
      zetaCompletedExplicitFormulaArchimedeanRightBinetMainKernel
        f F.toContourFamily t) +
      ∫ t : ℝ,
        zetaCompletedExplicitFormulaArchimedeanRightBinetRemainderKernel
          f F.toContourFamily t =
      zetaCompletedExplicitFormulaPhi f 0 := by
  have hdecomp :
      (∫ t : ℝ,
        zetaCompletedExplicitFormulaArchimedeanRightAffineKernel
          f F.toContourFamily t) =
        (∫ t : ℝ,
          zetaCompletedExplicitFormulaArchimedeanRightBinetMainKernel
            f F.toContourFamily t) +
          ∫ t : ℝ,
            zetaCompletedExplicitFormulaArchimedeanRightBinetRemainderKernel
              f F.toContourFamily t :=
    zetaCompletedExplicitFormulaArchimedeanRightAffineKernel_integral_eq_binetMain_add_remainder_integrals
      f F h hcoh
  calc
    (∫ t : ℝ,
      zetaCompletedExplicitFormulaArchimedeanRightBinetMainKernel
        f F.toContourFamily t) +
      ∫ t : ℝ,
        zetaCompletedExplicitFormulaArchimedeanRightBinetRemainderKernel
          f F.toContourFamily t =
        ∫ t : ℝ,
          zetaCompletedExplicitFormulaArchimedeanRightAffineKernel
            f F.toContourFamily t := by
      exact hdecomp.symm
    _ = zetaCompletedExplicitFormulaPhi f 0 := by
      exact haffine

/-- Coupled shifted-left Gamma/Binet full-transform value from an
independently proved whole-line left affine value.

This is the left analogue of
`zetaCompletedExplicitFormulaArchimedeanRightBinetFullTransform_integral_eq_phiZero_of_affineValue`;
it only transports across the pointwise Binet decomposition. -/
theorem zetaCompletedExplicitFormulaArchimedeanLeftBinetFullTransform_integral_eq_neg_phiZero_of_affineValue
    (f : ZetaAdmissibleFunction)
    (F : ExplicitFormulaVerticallyRegularContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F.toContourFamily)
    (hcoh : Complex.gammaBinetPrincipalLogCoherence)
    (haffine :
      (∫ t : ℝ,
        zetaCompletedExplicitFormulaArchimedeanLeftAffineKernel
          f F.toContourFamily t) =
        -(zetaCompletedExplicitFormulaPhi f 0)) :
    (∫ t : ℝ,
      zetaCompletedExplicitFormulaArchimedeanLeftBinetMainKernel
        f F.toContourFamily t) +
      ∫ t : ℝ,
        zetaCompletedExplicitFormulaArchimedeanLeftBinetRemainderKernel
          f F.toContourFamily t =
      -(zetaCompletedExplicitFormulaPhi f 0) := by
  have hdecomp :
      (∫ t : ℝ,
        zetaCompletedExplicitFormulaArchimedeanLeftAffineKernel
          f F.toContourFamily t) =
        (∫ t : ℝ,
          zetaCompletedExplicitFormulaArchimedeanLeftBinetMainKernel
            f F.toContourFamily t) +
          ∫ t : ℝ,
            zetaCompletedExplicitFormulaArchimedeanLeftBinetRemainderKernel
              f F.toContourFamily t :=
    zetaCompletedExplicitFormulaArchimedeanLeftAffineKernel_integral_eq_binetMain_add_remainder_integrals
      f F h hcoh
  calc
    (∫ t : ℝ,
      zetaCompletedExplicitFormulaArchimedeanLeftBinetMainKernel
        f F.toContourFamily t) +
      ∫ t : ℝ,
        zetaCompletedExplicitFormulaArchimedeanLeftBinetRemainderKernel
          f F.toContourFamily t =
        ∫ t : ℝ,
          zetaCompletedExplicitFormulaArchimedeanLeftAffineKernel
            f F.toContourFamily t := by
      exact hdecomp.symm
    _ = -(zetaCompletedExplicitFormulaPhi f 0) := by
      exact haffine

/-- Whole-line right coupled Gamma/Binet full-transform value from the
corresponding scheduled full-transform value.

This theorem removes only the exhaustion bookkeeping from the analytic leaf:
the remaining input is the scheduled fixed-vertical Gamma/Binet transform
identity itself. -/
theorem zetaCompletedExplicitFormulaArchimedeanRightBinetFullTransform_integral_eq_phiZero_of_scheduledFullTransform
    (f : ZetaAdmissibleFunction)
    (F : ExplicitFormulaVerticallyRegularContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F.toContourFamily)
    (hscheduled :
      Tendsto
        (fun u : ℝ =>
          (∫ t in Set.Icc
              (-(F.toContourFamily.rectangle
                  (h.height_schedule.height u)).T)
              (F.toContourFamily.rectangle
                  (h.height_schedule.height u)).T,
            zetaCompletedExplicitFormulaArchimedeanRightBinetMainKernel
              f F.toContourFamily t) +
            ∫ t in Set.Icc
              (-(F.toContourFamily.rectangle
                  (h.height_schedule.height u)).T)
              (F.toContourFamily.rectangle
                  (h.height_schedule.height u)).T,
            zetaCompletedExplicitFormulaArchimedeanRightBinetRemainderKernel
              f F.toContourFamily t)
        atTop
        (𝓝 (zetaCompletedExplicitFormulaPhi f 0))) :
    (∫ t : ℝ,
      zetaCompletedExplicitFormulaArchimedeanRightBinetMainKernel
        f F.toContourFamily t) +
      ∫ t : ℝ,
        zetaCompletedExplicitFormulaArchimedeanRightBinetRemainderKernel
          f F.toContourFamily t =
      zetaCompletedExplicitFormulaPhi f 0 := by
  let S : ℝ → ℂ := fun u : ℝ =>
    (∫ t in Set.Icc
        (-(F.toContourFamily.rectangle
            (h.height_schedule.height u)).T)
        (F.toContourFamily.rectangle
            (h.height_schedule.height u)).T,
      zetaCompletedExplicitFormulaArchimedeanRightBinetMainKernel
        f F.toContourFamily t) +
      ∫ t in Set.Icc
        (-(F.toContourFamily.rectangle
            (h.height_schedule.height u)).T)
        (F.toContourFamily.rectangle
            (h.height_schedule.height u)).T,
      zetaCompletedExplicitFormulaArchimedeanRightBinetRemainderKernel
        f F.toContourFamily t
  let I : ℂ :=
    (∫ t : ℝ,
      zetaCompletedExplicitFormulaArchimedeanRightBinetMainKernel
        f F.toContourFamily t) +
      ∫ t : ℝ,
        zetaCompletedExplicitFormulaArchimedeanRightBinetRemainderKernel
          f F.toContourFamily t
  have hmain :
      Tendsto
        (fun u : ℝ =>
          ∫ t in Set.Icc
              (-(F.toContourFamily.rectangle
                  (h.height_schedule.height u)).T)
              (F.toContourFamily.rectangle
                  (h.height_schedule.height u)).T,
            zetaCompletedExplicitFormulaArchimedeanRightBinetMainKernel
              f F.toContourFamily t)
        atTop
        (𝓝 (∫ t : ℝ,
          zetaCompletedExplicitFormulaArchimedeanRightBinetMainKernel
            f F.toContourFamily t)) :=
    zetaCompletedExplicitFormulaArchimedeanRightBinetMainKernel_scheduledWindow_tendsto_integral
      f F h
  have hremainder :
      Tendsto
        (fun u : ℝ =>
          ∫ t in Set.Icc
              (-(F.toContourFamily.rectangle
                  (h.height_schedule.height u)).T)
              (F.toContourFamily.rectangle
                  (h.height_schedule.height u)).T,
            zetaCompletedExplicitFormulaArchimedeanRightBinetRemainderKernel
              f F.toContourFamily t)
        atTop
        (𝓝 (∫ t : ℝ,
          zetaCompletedExplicitFormulaArchimedeanRightBinetRemainderKernel
            f F.toContourFamily t)) :=
    zetaCompletedExplicitFormulaArchimedeanRightBinetRemainderKernel_scheduledWindow_tendsto_integral
      f F h
  have hsum : Tendsto S atTop (𝓝 I) :=
    hmain.add hremainder
  exact
    explicitFormulaScheduledScalar_integral_eq_of_tendsto_integral_and_value
      S I (zetaCompletedExplicitFormulaPhi f 0) hsum hscheduled

/-- Whole-line shifted-left coupled Gamma/Binet full-transform value from the
corresponding scheduled full-transform value. -/
theorem zetaCompletedExplicitFormulaArchimedeanLeftBinetFullTransform_integral_eq_neg_phiZero_of_scheduledFullTransform
    (f : ZetaAdmissibleFunction)
    (F : ExplicitFormulaVerticallyRegularContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F.toContourFamily)
    (hregular : zetaCompletedExplicitFormulaLeftAffineLineGammaRegular
      F.toContourFamily)
    (hscheduled :
      Tendsto
        (fun u : ℝ =>
          (∫ t in Set.Icc
              (-(F.toContourFamily.rectangle
                  (h.height_schedule.height u)).T)
              (F.toContourFamily.rectangle
                  (h.height_schedule.height u)).T,
            zetaCompletedExplicitFormulaArchimedeanLeftBinetMainKernel
              f F.toContourFamily t) +
            ∫ t in Set.Icc
              (-(F.toContourFamily.rectangle
                  (h.height_schedule.height u)).T)
              (F.toContourFamily.rectangle
                  (h.height_schedule.height u)).T,
            zetaCompletedExplicitFormulaArchimedeanLeftBinetRemainderKernel
              f F.toContourFamily t)
        atTop
        (𝓝 (-(zetaCompletedExplicitFormulaPhi f 0)))) :
    (∫ t : ℝ,
      zetaCompletedExplicitFormulaArchimedeanLeftBinetMainKernel
        f F.toContourFamily t) +
      ∫ t : ℝ,
        zetaCompletedExplicitFormulaArchimedeanLeftBinetRemainderKernel
          f F.toContourFamily t =
      -(zetaCompletedExplicitFormulaPhi f 0) := by
  let S : ℝ → ℂ := fun u : ℝ =>
    (∫ t in Set.Icc
        (-(F.toContourFamily.rectangle
            (h.height_schedule.height u)).T)
        (F.toContourFamily.rectangle
            (h.height_schedule.height u)).T,
      zetaCompletedExplicitFormulaArchimedeanLeftBinetMainKernel
        f F.toContourFamily t) +
      ∫ t in Set.Icc
        (-(F.toContourFamily.rectangle
            (h.height_schedule.height u)).T)
        (F.toContourFamily.rectangle
            (h.height_schedule.height u)).T,
      zetaCompletedExplicitFormulaArchimedeanLeftBinetRemainderKernel
        f F.toContourFamily t
  let I : ℂ :=
    (∫ t : ℝ,
      zetaCompletedExplicitFormulaArchimedeanLeftBinetMainKernel
        f F.toContourFamily t) +
      ∫ t : ℝ,
        zetaCompletedExplicitFormulaArchimedeanLeftBinetRemainderKernel
          f F.toContourFamily t
  have hmain :
      Tendsto
        (fun u : ℝ =>
          ∫ t in Set.Icc
              (-(F.toContourFamily.rectangle
                  (h.height_schedule.height u)).T)
              (F.toContourFamily.rectangle
                  (h.height_schedule.height u)).T,
            zetaCompletedExplicitFormulaArchimedeanLeftBinetMainKernel
              f F.toContourFamily t)
        atTop
        (𝓝 (∫ t : ℝ,
          zetaCompletedExplicitFormulaArchimedeanLeftBinetMainKernel
            f F.toContourFamily t)) :=
    zetaCompletedExplicitFormulaArchimedeanLeftBinetMainKernel_scheduledWindow_tendsto_integral
      f F h hregular
  have hremainder :
      Tendsto
        (fun u : ℝ =>
          ∫ t in Set.Icc
              (-(F.toContourFamily.rectangle
                  (h.height_schedule.height u)).T)
              (F.toContourFamily.rectangle
                  (h.height_schedule.height u)).T,
            zetaCompletedExplicitFormulaArchimedeanLeftBinetRemainderKernel
              f F.toContourFamily t)
        atTop
        (𝓝 (∫ t : ℝ,
          zetaCompletedExplicitFormulaArchimedeanLeftBinetRemainderKernel
            f F.toContourFamily t)) :=
    zetaCompletedExplicitFormulaArchimedeanLeftBinetRemainderKernel_scheduledWindow_tendsto_integral
      f F h hregular
  have hsum : Tendsto S atTop (𝓝 I) :=
    hmain.add hremainder
  exact
    explicitFormulaScheduledScalar_integral_eq_of_tendsto_integral_and_value
      S I (-(zetaCompletedExplicitFormulaPhi f 0)) hsum hscheduled

/-- Scheduled full right Binet transform value from the coupled whole-line
Binet value.

This is only exhaustion transport: the analytic content is the whole-line
coupled Gamma/Binet value supplied as `hvalue`. -/
theorem zetaCompletedExplicitFormulaArchimedeanRightBinetFullTransform_scheduledWindow_tendsto_phiZero_of_integral_eq
    (f : ZetaAdmissibleFunction)
    (F : ExplicitFormulaVerticallyRegularContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F.toContourFamily)
    (hvalue :
      (∫ t : ℝ,
        zetaCompletedExplicitFormulaArchimedeanRightBinetMainKernel
          f F.toContourFamily t) +
        ∫ t : ℝ,
          zetaCompletedExplicitFormulaArchimedeanRightBinetRemainderKernel
            f F.toContourFamily t =
        zetaCompletedExplicitFormulaPhi f 0) :
    Tendsto
      (fun u : ℝ =>
        (∫ t in Set.Icc
            (-(F.toContourFamily.rectangle
                (h.height_schedule.height u)).T)
            (F.toContourFamily.rectangle
                (h.height_schedule.height u)).T,
          zetaCompletedExplicitFormulaArchimedeanRightBinetMainKernel
            f F.toContourFamily t) +
          ∫ t in Set.Icc
            (-(F.toContourFamily.rectangle
                (h.height_schedule.height u)).T)
            (F.toContourFamily.rectangle
                (h.height_schedule.height u)).T,
          zetaCompletedExplicitFormulaArchimedeanRightBinetRemainderKernel
            f F.toContourFamily t)
      atTop
      (𝓝 (zetaCompletedExplicitFormulaPhi f 0)) := by
  let S : ℝ → ℂ := fun u : ℝ =>
    (∫ t in Set.Icc
        (-(F.toContourFamily.rectangle
            (h.height_schedule.height u)).T)
        (F.toContourFamily.rectangle
            (h.height_schedule.height u)).T,
      zetaCompletedExplicitFormulaArchimedeanRightBinetMainKernel
        f F.toContourFamily t) +
      ∫ t in Set.Icc
        (-(F.toContourFamily.rectangle
            (h.height_schedule.height u)).T)
        (F.toContourFamily.rectangle
            (h.height_schedule.height u)).T,
      zetaCompletedExplicitFormulaArchimedeanRightBinetRemainderKernel
        f F.toContourFamily t
  let I : ℂ :=
    (∫ t : ℝ,
      zetaCompletedExplicitFormulaArchimedeanRightBinetMainKernel
        f F.toContourFamily t) +
      ∫ t : ℝ,
        zetaCompletedExplicitFormulaArchimedeanRightBinetRemainderKernel
          f F.toContourFamily t
  have hmain :
      Tendsto
        (fun u : ℝ =>
          ∫ t in Set.Icc
              (-(F.toContourFamily.rectangle
                  (h.height_schedule.height u)).T)
              (F.toContourFamily.rectangle
                  (h.height_schedule.height u)).T,
            zetaCompletedExplicitFormulaArchimedeanRightBinetMainKernel
              f F.toContourFamily t)
        atTop
        (𝓝 (∫ t : ℝ,
          zetaCompletedExplicitFormulaArchimedeanRightBinetMainKernel
            f F.toContourFamily t)) :=
    zetaCompletedExplicitFormulaArchimedeanRightBinetMainKernel_scheduledWindow_tendsto_integral
      f F h
  have hremainder :
      Tendsto
        (fun u : ℝ =>
          ∫ t in Set.Icc
              (-(F.toContourFamily.rectangle
                  (h.height_schedule.height u)).T)
              (F.toContourFamily.rectangle
                  (h.height_schedule.height u)).T,
            zetaCompletedExplicitFormulaArchimedeanRightBinetRemainderKernel
              f F.toContourFamily t)
        atTop
        (𝓝 (∫ t : ℝ,
          zetaCompletedExplicitFormulaArchimedeanRightBinetRemainderKernel
            f F.toContourFamily t)) :=
    zetaCompletedExplicitFormulaArchimedeanRightBinetRemainderKernel_scheduledWindow_tendsto_integral
      f F h
  have hsum : Tendsto S atTop (𝓝 I) :=
    hmain.add hremainder
  exact
    Eq.subst
      (motive := fun z : ℂ => Tendsto S atTop (𝓝 z))
      hvalue
      hsum

/-- Scheduled full shifted-left Binet transform value from the coupled
whole-line shifted-left Binet value.

This is only exhaustion transport: the analytic content is the whole-line
coupled shifted-left Gamma/Binet value supplied as `hvalue`. -/
theorem zetaCompletedExplicitFormulaArchimedeanLeftBinetFullTransform_scheduledWindow_tendsto_neg_phiZero_of_integral_eq
    (f : ZetaAdmissibleFunction)
    (F : ExplicitFormulaVerticallyRegularContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F.toContourFamily)
    (hregular : zetaCompletedExplicitFormulaLeftAffineLineGammaRegular
      F.toContourFamily)
    (hvalue :
      (∫ t : ℝ,
        zetaCompletedExplicitFormulaArchimedeanLeftBinetMainKernel
          f F.toContourFamily t) +
        ∫ t : ℝ,
          zetaCompletedExplicitFormulaArchimedeanLeftBinetRemainderKernel
            f F.toContourFamily t =
        -(zetaCompletedExplicitFormulaPhi f 0)) :
    Tendsto
      (fun u : ℝ =>
        (∫ t in Set.Icc
            (-(F.toContourFamily.rectangle
                (h.height_schedule.height u)).T)
            (F.toContourFamily.rectangle
                (h.height_schedule.height u)).T,
          zetaCompletedExplicitFormulaArchimedeanLeftBinetMainKernel
            f F.toContourFamily t) +
          ∫ t in Set.Icc
            (-(F.toContourFamily.rectangle
                (h.height_schedule.height u)).T)
            (F.toContourFamily.rectangle
                (h.height_schedule.height u)).T,
          zetaCompletedExplicitFormulaArchimedeanLeftBinetRemainderKernel
            f F.toContourFamily t)
      atTop
      (𝓝 (-(zetaCompletedExplicitFormulaPhi f 0))) := by
  let S : ℝ → ℂ := fun u : ℝ =>
    (∫ t in Set.Icc
        (-(F.toContourFamily.rectangle
            (h.height_schedule.height u)).T)
        (F.toContourFamily.rectangle
            (h.height_schedule.height u)).T,
      zetaCompletedExplicitFormulaArchimedeanLeftBinetMainKernel
        f F.toContourFamily t) +
      ∫ t in Set.Icc
        (-(F.toContourFamily.rectangle
            (h.height_schedule.height u)).T)
        (F.toContourFamily.rectangle
            (h.height_schedule.height u)).T,
      zetaCompletedExplicitFormulaArchimedeanLeftBinetRemainderKernel
        f F.toContourFamily t
  let I : ℂ :=
    (∫ t : ℝ,
      zetaCompletedExplicitFormulaArchimedeanLeftBinetMainKernel
        f F.toContourFamily t) +
      ∫ t : ℝ,
        zetaCompletedExplicitFormulaArchimedeanLeftBinetRemainderKernel
          f F.toContourFamily t
  have hmain :
      Tendsto
        (fun u : ℝ =>
          ∫ t in Set.Icc
              (-(F.toContourFamily.rectangle
                  (h.height_schedule.height u)).T)
              (F.toContourFamily.rectangle
                  (h.height_schedule.height u)).T,
            zetaCompletedExplicitFormulaArchimedeanLeftBinetMainKernel
              f F.toContourFamily t)
        atTop
        (𝓝 (∫ t : ℝ,
          zetaCompletedExplicitFormulaArchimedeanLeftBinetMainKernel
            f F.toContourFamily t)) :=
    zetaCompletedExplicitFormulaArchimedeanLeftBinetMainKernel_scheduledWindow_tendsto_integral
      f F h hregular
  have hremainder :
      Tendsto
        (fun u : ℝ =>
          ∫ t in Set.Icc
              (-(F.toContourFamily.rectangle
                  (h.height_schedule.height u)).T)
              (F.toContourFamily.rectangle
                  (h.height_schedule.height u)).T,
            zetaCompletedExplicitFormulaArchimedeanLeftBinetRemainderKernel
              f F.toContourFamily t)
        atTop
        (𝓝 (∫ t : ℝ,
          zetaCompletedExplicitFormulaArchimedeanLeftBinetRemainderKernel
            f F.toContourFamily t)) :=
    zetaCompletedExplicitFormulaArchimedeanLeftBinetRemainderKernel_scheduledWindow_tendsto_integral
      f F h hregular
  have hsum : Tendsto S atTop (𝓝 I) :=
    hmain.add hremainder
  exact
    Eq.subst
      (motive := fun z : ℂ => Tendsto S atTop (𝓝 z))
      hvalue
      hsum

/-- Right Gamma/Binet source value from the named coupled whole-line transform
value.

This is only definitional transport from the named owner integral to the long
main-plus-remainder expression used by downstream wrappers. -/
theorem zetaCompletedExplicitFormulaArchimedeanRightBinetFullTransform_integral_eq_phiZero_of_namedIntegralValue
    (f : ZetaAdmissibleFunction)
    (F : ExplicitFormulaVerticallyRegularContourFamily)
    (hvalue :
      zetaCompletedExplicitFormulaArchimedeanRightBinetFullTransformIntegral
          f F.toContourFamily =
        zetaCompletedExplicitFormulaPhi f 0) :
    (∫ t : ℝ,
      zetaCompletedExplicitFormulaArchimedeanRightBinetMainKernel
        f F.toContourFamily t) +
      ∫ t : ℝ,
        zetaCompletedExplicitFormulaArchimedeanRightBinetRemainderKernel
          f F.toContourFamily t =
      zetaCompletedExplicitFormulaPhi f 0 := by
  exact
    Eq.trans
      (zetaCompletedExplicitFormulaArchimedeanRightBinetFullTransformIntegral_eq
        f F.toContourFamily).symm
      hvalue

/-- Shifted-left Gamma/Binet source value from the named coupled whole-line
transform value.

This is only definitional transport from the named owner integral to the long
shifted main-plus-remainder expression used by downstream wrappers. -/
theorem zetaCompletedExplicitFormulaArchimedeanLeftBinetFullTransform_integral_eq_neg_phiZero_of_namedIntegralValue
    (f : ZetaAdmissibleFunction)
    (F : ExplicitFormulaVerticallyRegularContourFamily)
    (hvalue :
      zetaCompletedExplicitFormulaArchimedeanLeftBinetFullTransformIntegral
          f F.toContourFamily =
        -(zetaCompletedExplicitFormulaPhi f 0)) :
    (∫ t : ℝ,
      zetaCompletedExplicitFormulaArchimedeanLeftBinetMainKernel
        f F.toContourFamily t) +
      ∫ t : ℝ,
        zetaCompletedExplicitFormulaArchimedeanLeftBinetRemainderKernel
          f F.toContourFamily t =
      -(zetaCompletedExplicitFormulaPhi f 0) := by
  exact
    Eq.trans
      (zetaCompletedExplicitFormulaArchimedeanLeftBinetFullTransformIntegral_eq
        f F.toContourFamily).symm
      hvalue

/-- Paired coupled Gamma/Binet whole-line values from the right and shifted-left
affine whole-line values.

This is pure Binet-decomposition transport.  The analytic value theorem may be
proved either at the affine-line level or directly for the coupled Binet
transform; this lemma records the non-circular affine-to-Binet direction. -/
theorem zetaCompletedExplicitFormulaArchimedeanBinetFullTransform_integral_pair_of_affineValues
    (f : ZetaAdmissibleFunction)
    (F : ExplicitFormulaVerticallyRegularContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F.toContourFamily)
    (hcoh : Complex.gammaBinetPrincipalLogCoherence)
    (hright_affine :
      (∫ t : ℝ,
        zetaCompletedExplicitFormulaArchimedeanRightAffineKernel
          f F.toContourFamily t) =
        zetaCompletedExplicitFormulaPhi f 0)
    (hleft_affine :
      (∫ t : ℝ,
        zetaCompletedExplicitFormulaArchimedeanLeftAffineKernel
          f F.toContourFamily t) =
        -(zetaCompletedExplicitFormulaPhi f 0)) :
    ((∫ t : ℝ,
      zetaCompletedExplicitFormulaArchimedeanRightBinetMainKernel
        f F.toContourFamily t) +
      ∫ t : ℝ,
        zetaCompletedExplicitFormulaArchimedeanRightBinetRemainderKernel
          f F.toContourFamily t =
      zetaCompletedExplicitFormulaPhi f 0) ∧
    ((∫ t : ℝ,
      zetaCompletedExplicitFormulaArchimedeanLeftBinetMainKernel
        f F.toContourFamily t) +
      ∫ t : ℝ,
        zetaCompletedExplicitFormulaArchimedeanLeftBinetRemainderKernel
          f F.toContourFamily t =
      -(zetaCompletedExplicitFormulaPhi f 0)) := by
  exact
    And.intro
      (zetaCompletedExplicitFormulaArchimedeanRightBinetFullTransform_integral_eq_phiZero_of_affineValue
        f F h hcoh hright_affine)
      (zetaCompletedExplicitFormulaArchimedeanLeftBinetFullTransform_integral_eq_neg_phiZero_of_affineValue
        f F h hcoh hleft_affine)

/-- Paired scheduled Gamma/Binet full-transform values from the coupled
whole-line Binet values.

This is the cycle-hygiene bridge: it contains only scheduled-window exhaustion
from the already recombined Binet transform.  The remaining analytic owner work
is exactly the coupled right and shifted-left whole-line Binet values supplied
as inputs here. -/
theorem zetaCompletedExplicitFormulaArchimedeanBinetFullTransform_scheduledPair_of_fullTransformIntegralValues
    (f : ZetaAdmissibleFunction)
    (F : ExplicitFormulaVerticallyRegularContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F.toContourFamily)
    (hright_value :
      (∫ t : ℝ,
        zetaCompletedExplicitFormulaArchimedeanRightBinetMainKernel
          f F.toContourFamily t) +
        ∫ t : ℝ,
          zetaCompletedExplicitFormulaArchimedeanRightBinetRemainderKernel
            f F.toContourFamily t =
        zetaCompletedExplicitFormulaPhi f 0)
    (hleft_value :
      (∫ t : ℝ,
        zetaCompletedExplicitFormulaArchimedeanLeftBinetMainKernel
          f F.toContourFamily t) +
        ∫ t : ℝ,
          zetaCompletedExplicitFormulaArchimedeanLeftBinetRemainderKernel
            f F.toContourFamily t =
        -(zetaCompletedExplicitFormulaPhi f 0)) :
    (Tendsto
        (fun u : ℝ =>
          (∫ t in Set.Icc
              (-(F.toContourFamily.rectangle
                  (h.height_schedule.height u)).T)
              (F.toContourFamily.rectangle
                  (h.height_schedule.height u)).T,
            zetaCompletedExplicitFormulaArchimedeanRightBinetMainKernel
              f F.toContourFamily t) +
            ∫ t in Set.Icc
              (-(F.toContourFamily.rectangle
                  (h.height_schedule.height u)).T)
              (F.toContourFamily.rectangle
                  (h.height_schedule.height u)).T,
            zetaCompletedExplicitFormulaArchimedeanRightBinetRemainderKernel
              f F.toContourFamily t)
        atTop
        (𝓝 (zetaCompletedExplicitFormulaPhi f 0))) ∧
      (Tendsto
        (fun u : ℝ =>
          (∫ t in Set.Icc
              (-(F.toContourFamily.rectangle
                  (h.height_schedule.height u)).T)
              (F.toContourFamily.rectangle
                  (h.height_schedule.height u)).T,
            zetaCompletedExplicitFormulaArchimedeanLeftBinetMainKernel
              f F.toContourFamily t) +
            ∫ t in Set.Icc
              (-(F.toContourFamily.rectangle
                  (h.height_schedule.height u)).T)
              (F.toContourFamily.rectangle
                  (h.height_schedule.height u)).T,
            zetaCompletedExplicitFormulaArchimedeanLeftBinetRemainderKernel
              f F.toContourFamily t)
        atTop
        (𝓝 (-(zetaCompletedExplicitFormulaPhi f 0))) := by
  have hleft_regular :
      zetaCompletedExplicitFormulaLeftAffineLineGammaRegular
        F.toContourFamily :=
    zetaCompletedExplicitFormulaLeftAffineLineGammaRegular_of_verticallyRegular
      F
  exact
    And.intro
      (zetaCompletedExplicitFormulaArchimedeanRightBinetFullTransform_scheduledWindow_tendsto_phiZero_of_integral_eq
        f F h hright_value)
      (zetaCompletedExplicitFormulaArchimedeanLeftBinetFullTransform_scheduledWindow_tendsto_neg_phiZero_of_integral_eq
        f F h hleft_regular hleft_value)

/-- Paired scheduled Gamma/Binet full-transform values from the right and
shifted-left affine whole-line values.

This theorem composes the affine-to-coupled-Binet transport with scheduled
window exhaustion.  It isolates the remaining analytic owner task to direct
whole-line evaluation of the two affine Gamma/Binet lines. -/
theorem zetaCompletedExplicitFormulaArchimedeanBinetFullTransform_scheduledPair_of_affineValues
    (f : ZetaAdmissibleFunction)
    (F : ExplicitFormulaVerticallyRegularContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F.toContourFamily)
    (hcoh : Complex.gammaBinetPrincipalLogCoherence)
    (hright_affine :
      (∫ t : ℝ,
        zetaCompletedExplicitFormulaArchimedeanRightAffineKernel
          f F.toContourFamily t) =
        zetaCompletedExplicitFormulaPhi f 0)
    (hleft_affine :
      (∫ t : ℝ,
        zetaCompletedExplicitFormulaArchimedeanLeftAffineKernel
          f F.toContourFamily t) =
        -(zetaCompletedExplicitFormulaPhi f 0)) :
    (Tendsto
        (fun u : ℝ =>
          (∫ t in Set.Icc
              (-(F.toContourFamily.rectangle
                  (h.height_schedule.height u)).T)
              (F.toContourFamily.rectangle
                  (h.height_schedule.height u)).T,
            zetaCompletedExplicitFormulaArchimedeanRightBinetMainKernel
              f F.toContourFamily t) +
            ∫ t in Set.Icc
              (-(F.toContourFamily.rectangle
                  (h.height_schedule.height u)).T)
              (F.toContourFamily.rectangle
                  (h.height_schedule.height u)).T,
            zetaCompletedExplicitFormulaArchimedeanRightBinetRemainderKernel
              f F.toContourFamily t)
        atTop
        (𝓝 (zetaCompletedExplicitFormulaPhi f 0))) ∧
      (Tendsto
        (fun u : ℝ =>
          (∫ t in Set.Icc
              (-(F.toContourFamily.rectangle
                  (h.height_schedule.height u)).T)
              (F.toContourFamily.rectangle
                  (h.height_schedule.height u)).T,
            zetaCompletedExplicitFormulaArchimedeanLeftBinetMainKernel
              f F.toContourFamily t) +
            ∫ t in Set.Icc
              (-(F.toContourFamily.rectangle
                  (h.height_schedule.height u)).T)
              (F.toContourFamily.rectangle
                  (h.height_schedule.height u)).T,
            zetaCompletedExplicitFormulaArchimedeanLeftBinetRemainderKernel
              f F.toContourFamily t)
        atTop
        (𝓝 (-(zetaCompletedExplicitFormulaPhi f 0))) := by
  have hpair :
      ((∫ t : ℝ,
        zetaCompletedExplicitFormulaArchimedeanRightBinetMainKernel
          f F.toContourFamily t) +
        ∫ t : ℝ,
          zetaCompletedExplicitFormulaArchimedeanRightBinetRemainderKernel
            f F.toContourFamily t =
        zetaCompletedExplicitFormulaPhi f 0) ∧
      ((∫ t : ℝ,
        zetaCompletedExplicitFormulaArchimedeanLeftBinetMainKernel
          f F.toContourFamily t) +
        ∫ t : ℝ,
          zetaCompletedExplicitFormulaArchimedeanLeftBinetRemainderKernel
            f F.toContourFamily t =
        -(zetaCompletedExplicitFormulaPhi f 0)) :=
    zetaCompletedExplicitFormulaArchimedeanBinetFullTransform_integral_pair_of_affineValues
      f F h hcoh hright_affine hleft_affine
  exact
    zetaCompletedExplicitFormulaArchimedeanBinetFullTransform_scheduledPair_of_fullTransformIntegralValues
      f F h hpair.1 hpair.2

/-- Paired scheduled coupled Gamma/Binet values from direct paired scheduled
affine contour values.

This records the complete non-circular transport chain needed by the line-core
owner: scheduled affine contour values give whole-line affine values by
exhaustion, whole-line affine values give coupled Binet whole-line values by
the pointwise Binet decomposition, and those whole-line Binet values give the
scheduled coupled Binet values by exhaustion. -/
theorem zetaCompletedExplicitFormulaArchimedeanBinetFullTransform_scheduledPair_of_scheduledAffineValues
    (f : ZetaAdmissibleFunction)
    (F : ExplicitFormulaVerticallyRegularContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F.toContourFamily)
    (hcoh : Complex.gammaBinetPrincipalLogCoherence)
    (hscheduled :
      Tendsto
        (fun u : ℝ =>
          ∫ t in Set.Icc
              (-(F.toContourFamily.rectangle
                  (h.height_schedule.height u)).T)
              (F.toContourFamily.rectangle
                  (h.height_schedule.height u)).T,
            zetaCompletedExplicitFormulaArchimedeanRightAffineKernel
              f F.toContourFamily t)
        atTop
        (𝓝 (zetaCompletedExplicitFormulaPhi f 0)) ∧
      Tendsto
        (fun u : ℝ =>
          ∫ t in Set.Icc
              (-(F.toContourFamily.rectangle
                  (h.height_schedule.height u)).T)
              (F.toContourFamily.rectangle
                  (h.height_schedule.height u)).T,
            zetaCompletedExplicitFormulaArchimedeanLeftAffineKernel
              f F.toContourFamily t)
        atTop
        (𝓝 (-(zetaCompletedExplicitFormulaPhi f 0)))) :
    (Tendsto
        (fun u : ℝ =>
          (∫ t in Set.Icc
              (-(F.toContourFamily.rectangle
                  (h.height_schedule.height u)).T)
              (F.toContourFamily.rectangle
                  (h.height_schedule.height u)).T,
            zetaCompletedExplicitFormulaArchimedeanRightBinetMainKernel
              f F.toContourFamily t) +
            ∫ t in Set.Icc
              (-(F.toContourFamily.rectangle
                  (h.height_schedule.height u)).T)
              (F.toContourFamily.rectangle
                  (h.height_schedule.height u)).T,
            zetaCompletedExplicitFormulaArchimedeanRightBinetRemainderKernel
              f F.toContourFamily t)
        atTop
        (𝓝 (zetaCompletedExplicitFormulaPhi f 0))) ∧
      (Tendsto
        (fun u : ℝ =>
          (∫ t in Set.Icc
              (-(F.toContourFamily.rectangle
                  (h.height_schedule.height u)).T)
              (F.toContourFamily.rectangle
                  (h.height_schedule.height u)).T,
            zetaCompletedExplicitFormulaArchimedeanLeftBinetMainKernel
              f F.toContourFamily t) +
            ∫ t in Set.Icc
              (-(F.toContourFamily.rectangle
                  (h.height_schedule.height u)).T)
              (F.toContourFamily.rectangle
                  (h.height_schedule.height u)).T,
            zetaCompletedExplicitFormulaArchimedeanLeftBinetRemainderKernel
              f F.toContourFamily t)
        atTop
        (𝓝 (-(zetaCompletedExplicitFormulaPhi f 0))) := by
  have haffine :
      ((∫ t : ℝ,
        zetaCompletedExplicitFormulaArchimedeanRightAffineKernel
          f F.toContourFamily t) =
        zetaCompletedExplicitFormulaPhi f 0) ∧
      ((∫ t : ℝ,
        zetaCompletedExplicitFormulaArchimedeanLeftAffineKernel
          f F.toContourFamily t) =
        -(zetaCompletedExplicitFormulaPhi f 0)) :=
    zetaCompletedExplicitFormulaArchimedeanAffineKernel_integral_pair_of_scheduledWindow
      f F h hcoh hscheduled
  exact
    zetaCompletedExplicitFormulaArchimedeanBinetFullTransform_scheduledPair_of_affineValues
      f F h hcoh haffine.1 haffine.2

/-- Paired scheduled Gamma/Binet full-transform values from the direct right
scheduled affine contour value and the right-minus-left inverse-Gamma
normalization.

This is the non-circular bridge needed by the line-core owner.  The theorem
does not supply the direct right affine contour value and does not use the
line-core Binet value.  It only composes:

* right scheduled affine value plus the archimedean difference-channel
  normalization gives paired scheduled affine values;
* paired scheduled affine values give paired scheduled Gamma/Binet
  full-transform values. -/
theorem zetaCompletedExplicitFormulaArchimedeanBinetFullTransform_scheduledPair_of_rightAffineScheduled_and_inverseGammaDifferenceValue
    (f : ZetaAdmissibleFunction)
    (F : ExplicitFormulaVerticallyRegularContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F.toContourFamily)
    (hcoh : Complex.gammaBinetPrincipalLogCoherence)
    (hright :
      Tendsto
        (fun u : ℝ =>
          ∫ t in Set.Icc
              (-(F.toContourFamily.rectangle
                  (h.height_schedule.height u)).T)
              (F.toContourFamily.rectangle
                  (h.height_schedule.height u)).T,
            zetaCompletedExplicitFormulaArchimedeanRightAffineKernel
              f F.toContourFamily t)
        atTop
        (𝓝 (zetaCompletedExplicitFormulaPhi f 0)))
    (hvalue :
      (∫ t : ℝ,
        zetaCompletedExplicitFormulaInverseGammaDifferenceAffineKernel
          f F.toContourFamily t) =
        zetaCompletedExplicitFormulaArchimedeanContribution f +
          zetaCompletedExplicitFormulaCorrectionStandardContourContribution f) :
    (Tendsto
        (fun u : ℝ =>
          (∫ t in Set.Icc
              (-(F.toContourFamily.rectangle
                  (h.height_schedule.height u)).T)
              (F.toContourFamily.rectangle
                  (h.height_schedule.height u)).T,
            zetaCompletedExplicitFormulaArchimedeanRightBinetMainKernel
              f F.toContourFamily t) +
            ∫ t in Set.Icc
              (-(F.toContourFamily.rectangle
                  (h.height_schedule.height u)).T)
              (F.toContourFamily.rectangle
                  (h.height_schedule.height u)).T,
            zetaCompletedExplicitFormulaArchimedeanRightBinetRemainderKernel
              f F.toContourFamily t)
        atTop
        (𝓝 (zetaCompletedExplicitFormulaPhi f 0))) ∧
      (Tendsto
        (fun u : ℝ =>
          (∫ t in Set.Icc
              (-(F.toContourFamily.rectangle
                  (h.height_schedule.height u)).T)
              (F.toContourFamily.rectangle
                  (h.height_schedule.height u)).T,
            zetaCompletedExplicitFormulaArchimedeanLeftBinetMainKernel
              f F.toContourFamily t) +
            ∫ t in Set.Icc
              (-(F.toContourFamily.rectangle
                  (h.height_schedule.height u)).T)
              (F.toContourFamily.rectangle
                  (h.height_schedule.height u)).T,
            zetaCompletedExplicitFormulaArchimedeanLeftBinetRemainderKernel
              f F.toContourFamily t)
        atTop
        (𝓝 (-(zetaCompletedExplicitFormulaPhi f 0))) := by
  have haffine :
      Tendsto
          (fun u : ℝ =>
            ∫ t in Set.Icc
                (-(F.toContourFamily.rectangle
                    (h.height_schedule.height u)).T)
                (F.toContourFamily.rectangle
                    (h.height_schedule.height u)).T,
              zetaCompletedExplicitFormulaArchimedeanRightAffineKernel
                f F.toContourFamily t)
          atTop
          (𝓝 (zetaCompletedExplicitFormulaPhi f 0)) ∧
        Tendsto
          (fun u : ℝ =>
            ∫ t in Set.Icc
                (-(F.toContourFamily.rectangle
                    (h.height_schedule.height u)).T)
                (F.toContourFamily.rectangle
                    (h.height_schedule.height u)).T,
              zetaCompletedExplicitFormulaArchimedeanLeftAffineKernel
                f F.toContourFamily t)
          atTop
          (𝓝 (-(zetaCompletedExplicitFormulaPhi f 0))) :=
    zetaCompletedExplicitFormulaArchimedeanAffineKernel_scheduledPair_of_right_and_verticallyRegular_gammaBinet_integral_eq
      f F h hcoh hright hvalue
  exact
    zetaCompletedExplicitFormulaArchimedeanBinetFullTransform_scheduledPair_of_scheduledAffineValues
      f F h hcoh haffine

/-- Paired scheduled Gamma/Binet full-transform values from the direct right
scheduled affine contour value and the scheduled right-minus-left affine-window
value.

This is the clean upstream bridge for the owner proof: the second input is
already the named archimedean affine-window difference, so no inverse-Gamma
component normalization or downstream line-value wrapper is involved. -/
theorem zetaCompletedExplicitFormulaArchimedeanBinetFullTransform_scheduledPair_of_rightAffineScheduled_and_affineDifference
    (f : ZetaAdmissibleFunction)
    (F : ExplicitFormulaVerticallyRegularContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F.toContourFamily)
    (hcoh : Complex.gammaBinetPrincipalLogCoherence)
    (hright :
      Tendsto
        (fun u : ℝ =>
          ∫ t in Set.Icc
              (-(F.toContourFamily.rectangle
                  (h.height_schedule.height u)).T)
              (F.toContourFamily.rectangle
                  (h.height_schedule.height u)).T,
            zetaCompletedExplicitFormulaArchimedeanRightAffineKernel
              f F.toContourFamily t)
        atTop
        (𝓝 (zetaCompletedExplicitFormulaPhi f 0)))
    (hdifference :
      Tendsto
        (fun u : ℝ =>
          (∫ t in Set.Icc
              (-(F.toContourFamily.rectangle
                  (h.height_schedule.height u)).T)
              (F.toContourFamily.rectangle
                  (h.height_schedule.height u)).T,
            zetaCompletedExplicitFormulaArchimedeanRightAffineKernel
              f F.toContourFamily t) -
            ∫ t in Set.Icc
              (-(F.toContourFamily.rectangle
                  (h.height_schedule.height u)).T)
              (F.toContourFamily.rectangle
                  (h.height_schedule.height u)).T,
              zetaCompletedExplicitFormulaArchimedeanLeftAffineKernel
                f F.toContourFamily t)
        atTop
        (𝓝 (zetaCompletedExplicitFormulaArchimedeanContribution f))) :
    (Tendsto
        (fun u : ℝ =>
          (∫ t in Set.Icc
              (-(F.toContourFamily.rectangle
                  (h.height_schedule.height u)).T)
              (F.toContourFamily.rectangle
                  (h.height_schedule.height u)).T,
            zetaCompletedExplicitFormulaArchimedeanRightBinetMainKernel
              f F.toContourFamily t) +
            ∫ t in Set.Icc
              (-(F.toContourFamily.rectangle
                  (h.height_schedule.height u)).T)
              (F.toContourFamily.rectangle
                  (h.height_schedule.height u)).T,
            zetaCompletedExplicitFormulaArchimedeanRightBinetRemainderKernel
              f F.toContourFamily t)
        atTop
        (𝓝 (zetaCompletedExplicitFormulaPhi f 0))) ∧
      (Tendsto
        (fun u : ℝ =>
          (∫ t in Set.Icc
              (-(F.toContourFamily.rectangle
                  (h.height_schedule.height u)).T)
              (F.toContourFamily.rectangle
                  (h.height_schedule.height u)).T,
            zetaCompletedExplicitFormulaArchimedeanLeftBinetMainKernel
              f F.toContourFamily t) +
            ∫ t in Set.Icc
              (-(F.toContourFamily.rectangle
                  (h.height_schedule.height u)).T)
              (F.toContourFamily.rectangle
                  (h.height_schedule.height u)).T,
            zetaCompletedExplicitFormulaArchimedeanLeftBinetRemainderKernel
              f F.toContourFamily t)
        atTop
        (𝓝 (-(zetaCompletedExplicitFormulaPhi f 0))) := by
  have haffine :
      Tendsto
          (fun u : ℝ =>
            ∫ t in Set.Icc
                (-(F.toContourFamily.rectangle
                    (h.height_schedule.height u)).T)
                (F.toContourFamily.rectangle
                    (h.height_schedule.height u)).T,
              zetaCompletedExplicitFormulaArchimedeanRightAffineKernel
                f F.toContourFamily t)
          atTop
          (𝓝 (zetaCompletedExplicitFormulaPhi f 0)) ∧
        Tendsto
          (fun u : ℝ =>
            ∫ t in Set.Icc
                (-(F.toContourFamily.rectangle
                    (h.height_schedule.height u)).T)
                (F.toContourFamily.rectangle
                    (h.height_schedule.height u)).T,
              zetaCompletedExplicitFormulaArchimedeanLeftAffineKernel
                f F.toContourFamily t)
          atTop
          (𝓝 (-(zetaCompletedExplicitFormulaPhi f 0))) :=
    zetaCompletedExplicitFormulaArchimedeanAffineKernel_scheduledPair_of_right_and_difference
      f F.toContourFamily h hright hdifference
  exact
    zetaCompletedExplicitFormulaArchimedeanBinetFullTransform_scheduledPair_of_scheduledAffineValues
      f F h hcoh haffine

/-- Paired scheduled Gamma/Binet full-transform values from the direct right
scheduled affine contour value and the archimedean vertical-channel value. -/
theorem zetaCompletedExplicitFormulaArchimedeanBinetFullTransform_scheduledPair_of_rightAffineScheduled_and_verticalChannel
    (f : ZetaAdmissibleFunction)
    (F : ExplicitFormulaVerticallyRegularContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F.toContourFamily)
    (hcoh : Complex.gammaBinetPrincipalLogCoherence)
    (hright :
      Tendsto
        (fun u : ℝ =>
          ∫ t in Set.Icc
              (-(F.toContourFamily.rectangle
                  (h.height_schedule.height u)).T)
              (F.toContourFamily.rectangle
                  (h.height_schedule.height u)).T,
            zetaCompletedExplicitFormulaArchimedeanRightAffineKernel
              f F.toContourFamily t)
        atTop
        (𝓝 (zetaCompletedExplicitFormulaPhi f 0)))
    (hchannel :
      Tendsto
        (fun u : ℝ =>
          zetaCompletedExplicitFormulaArchimedeanVerticalChannel
            f F.toContourFamily (h.height_schedule.height u))
        atTop
        (𝓝 (zetaCompletedExplicitFormulaArchimedeanContribution f))) :
    (Tendsto
        (fun u : ℝ =>
          (∫ t in Set.Icc
              (-(F.toContourFamily.rectangle
                  (h.height_schedule.height u)).T)
              (F.toContourFamily.rectangle
                  (h.height_schedule.height u)).T,
            zetaCompletedExplicitFormulaArchimedeanRightBinetMainKernel
              f F.toContourFamily t) +
            ∫ t in Set.Icc
              (-(F.toContourFamily.rectangle
                  (h.height_schedule.height u)).T)
              (F.toContourFamily.rectangle
                  (h.height_schedule.height u)).T,
            zetaCompletedExplicitFormulaArchimedeanRightBinetRemainderKernel
              f F.toContourFamily t)
        atTop
        (𝓝 (zetaCompletedExplicitFormulaPhi f 0))) ∧
      (Tendsto
        (fun u : ℝ =>
          (∫ t in Set.Icc
              (-(F.toContourFamily.rectangle
                  (h.height_schedule.height u)).T)
              (F.toContourFamily.rectangle
                  (h.height_schedule.height u)).T,
            zetaCompletedExplicitFormulaArchimedeanLeftBinetMainKernel
              f F.toContourFamily t) +
            ∫ t in Set.Icc
              (-(F.toContourFamily.rectangle
                  (h.height_schedule.height u)).T)
              (F.toContourFamily.rectangle
                  (h.height_schedule.height u)).T,
            zetaCompletedExplicitFormulaArchimedeanLeftBinetRemainderKernel
              f F.toContourFamily t)
        atTop
        (𝓝 (-(zetaCompletedExplicitFormulaPhi f 0))) := by
  have haffine :
      Tendsto
          (fun u : ℝ =>
            ∫ t in Set.Icc
                (-(F.toContourFamily.rectangle
                    (h.height_schedule.height u)).T)
                (F.toContourFamily.rectangle
                    (h.height_schedule.height u)).T,
              zetaCompletedExplicitFormulaArchimedeanRightAffineKernel
                f F.toContourFamily t)
          atTop
          (𝓝 (zetaCompletedExplicitFormulaPhi f 0)) ∧
        Tendsto
          (fun u : ℝ =>
            ∫ t in Set.Icc
                (-(F.toContourFamily.rectangle
                    (h.height_schedule.height u)).T)
                (F.toContourFamily.rectangle
                    (h.height_schedule.height u)).T,
              zetaCompletedExplicitFormulaArchimedeanLeftAffineKernel
                f F.toContourFamily t)
          atTop
          (𝓝 (-(zetaCompletedExplicitFormulaPhi f 0))) :=
    zetaCompletedExplicitFormulaArchimedeanAffineKernel_scheduledPair_of_right_and_verticalChannel
      f F.toContourFamily h hright hchannel
  exact
    zetaCompletedExplicitFormulaArchimedeanBinetFullTransform_scheduledPair_of_scheduledAffineValues
      f F h hcoh haffine

/-- Affine-line geometry: left affine line equals one minus right affine line of
negated argument. This is the functional-equation reflection relationship across
the critical line. -/
theorem zetaCompletedExplicitFormulaLeftAffineLine_eq_one_sub_rightAffineLine_of_neg
    (F : ExplicitFormulaContourFamily) :
    zetaCompletedExplicitFormulaLeftAffineLine F =
    fun t : ℝ => (1 : ℂ) - zetaCompletedExplicitFormulaRightAffineLine F (-t) := by
  funext t
  exact zetaCompletedExplicitFormulaLeftAffineLine_eq_one_sub_rightAffineLine_of_reflection
    F t

/-- Affine-line geometry: left centered affine line equals minus right centered
affine line of negated argument. The centered coordinates exhibit the negation
symmetry. -/
theorem zetaCompletedExplicitFormulaLeftCenteredAffineLine_eq_neg_rightCenteredAffineLine_of_neg
    (F : ExplicitFormulaContourFamily) :
    zetaCompletedExplicitFormulaLeftCenteredAffineLine F =
    fun t : ℝ => -(zetaCompletedExplicitFormulaRightCenteredAffineLine F (-t)) := by
  funext t
  exact zetaCompletedExplicitFormulaLeftCenteredAffineLine_eq_neg_rightCenteredAffineLine_of_reflection
    F t

/-- Gamma geometry: the shifted Gamma log-derivative main component equals the
regular main component via the duality between left and right parameters. -/
theorem zetaCompletedExplicitFormulaGammaLogDerivativeShiftNatMain_eq_main_of_dual
    (F : ExplicitFormulaContourFamily) :
    (fun t : ℝ =>
      Complex.GammaLogDerivativeFixedVerticalShiftNatMain
        ((1 - F.c) / 2)
        (zetaCompletedExplicitFormulaArchimedeanLeftBinetShiftNat F)
        (t / 2)) =
    (fun t : ℝ =>
      Complex.GammaLogDerivativeFixedVerticalMain
        (F.c / 2) ((-t) / 2)) := by
  funext t
  exact Complex.GammaLogDerivativeShiftNatMain_eq_main_of_complementary_shift
    F t

/-- Correction log-derivative integral transport: the integral of the left
correction term over ℝ equals minus the integral of the right correction term,
by symmetry of the affine geometry. -/
theorem zetaCompletedExplicitFormulaCorrectionLogDerivative_integral_transport
    (f : ZetaAdmissibleFunction)
    (F : ExplicitFormulaContourFamily) :
    (∫ t : ℝ,
      explicitFormulaCorrectionLogDerivative
        (zetaCompletedExplicitFormulaLeftAffineLine F t) *
        zetaCompletedExplicitFormulaPhi f
          (zetaCompletedExplicitFormulaLeftCenteredAffineLine F t)) =
    - (∫ t : ℝ,
      explicitFormulaCorrectionLogDerivative
        (zetaCompletedExplicitFormulaRightAffineLine F t) *
        zetaCompletedExplicitFormulaPhi f
          (zetaCompletedExplicitFormulaRightCenteredAffineLine F t)) := by
  have htransport :
      (∫ t : ℝ,
        explicitFormulaCorrectionLogDerivative
          (fun s => -(zetaCompletedExplicitFormulaRightAffineLine F (-s))) t *
          zetaCompletedExplicitFormulaPhi f
            (fun s => -(zetaCompletedExplicitFormulaRightCenteredAffineLine F (-s))) t) =
      - (∫ t : ℝ,
        explicitFormulaCorrectionLogDerivative
          (zetaCompletedExplicitFormulaRightAffineLine F t) *
          zetaCompletedExplicitFormulaPhi f
            (zetaCompletedExplicitFormulaRightCenteredAffineLine F t)) :=
    integral_comp_mul_left_correction_transport
      f F
  calc
    (∫ t : ℝ,
      explicitFormulaCorrectionLogDerivative
        (zetaCompletedExplicitFormulaLeftAffineLine F t) *
        zetaCompletedExplicitFormulaPhi f
          (zetaCompletedExplicitFormulaLeftCenteredAffineLine F t)) =
        (∫ t : ℝ,
          explicitFormulaCorrectionLogDerivative
            (fun s => -(zetaCompletedExplicitFormulaRightAffineLine F (-s))) t *
            zetaCompletedExplicitFormulaPhi f
              (fun s => -(zetaCompletedExplicitFormulaRightCenteredAffineLine F (-s))) t) := by
      exact integral_cong_ae
        (Filter.Eventually.of_forall fun t =>
          congrArg₂ HMul.hMul
            (congrArg explicitFormulaCorrectionLogDerivative
              (zetaCompletedExplicitFormulaLeftAffineLine_eq_one_sub_rightAffineLine_of_neg F t))
            (congrArg (zetaCompletedExplicitFormulaPhi f)
              (zetaCompletedExplicitFormulaLeftCenteredAffineLine_eq_neg_rightCenteredAffineLine_of_neg F t)))
    _ = - (∫ t : ℝ,
        explicitFormulaCorrectionLogDerivative
          (zetaCompletedExplicitFormulaRightAffineLine F t) *
          zetaCompletedExplicitFormulaPhi f
            (zetaCompletedExplicitFormulaRightCenteredAffineLine F t)) := by
      exact htransport

/-- Gamma π log-derivative term integral transport: the integral of this
constant term paired with the left test function equals minus the integral with
the right test function, by change-of-variables. -/
theorem zetaCompletedExplicitFormulaGammaRealPiLogDerivativeTerm_integral_transport
    (f : ZetaAdmissibleFunction)
    (F : ExplicitFormulaContourFamily) :
    (∫ t : ℝ,
      zetaCompletedExplicitFormulaGammaRealPiLogDerivativeTerm *
        zetaCompletedExplicitFormulaPhi f
          (zetaCompletedExplicitFormulaLeftCenteredAffineLine F t)) =
    - (∫ t : ℝ,
      zetaCompletedExplicitFormulaGammaRealPiLogDerivativeTerm *
        zetaCompletedExplicitFormulaPhi f
          (zetaCompletedExplicitFormulaRightCenteredAffineLine F t)) := by
  have htransport :
      (∫ t : ℝ,
        zetaCompletedExplicitFormulaGammaRealPiLogDerivativeTerm *
          zetaCompletedExplicitFormulaPhi f
            (fun s => -(zetaCompletedExplicitFormulaRightCenteredAffineLine F (-s))) t) =
      - (∫ t : ℝ,
        zetaCompletedExplicitFormulaGammaRealPiLogDerivativeTerm *
          zetaCompletedExplicitFormulaPhi f
            (zetaCompletedExplicitFormulaRightCenteredAffineLine F t)) :=
    integral_comp_mul_left_pi_term_transport
      f F
  calc
    (∫ t : ℝ,
      zetaCompletedExplicitFormulaGammaRealPiLogDerivativeTerm *
        zetaCompletedExplicitFormulaPhi f
          (zetaCompletedExplicitFormulaLeftCenteredAffineLine F t)) =
        (∫ t : ℝ,
          zetaCompletedExplicitFormulaGammaRealPiLogDerivativeTerm *
            zetaCompletedExplicitFormulaPhi f
              (fun s => -(zetaCompletedExplicitFormulaRightCenteredAffineLine F (-s))) t) := by
      exact integral_cong_ae
        (Filter.Eventually.of_forall fun t =>
          congrArg (zetaCompletedExplicitFormulaGammaRealPiLogDerivativeTerm * ·)
            (congrArg (zetaCompletedExplicitFormulaPhi f)
              (zetaCompletedExplicitFormulaLeftCenteredAffineLine_eq_neg_rightCenteredAffineLine_of_neg F t)))
    _ = - (∫ t : ℝ,
        zetaCompletedExplicitFormulaGammaRealPiLogDerivativeTerm *
          zetaCompletedExplicitFormulaPhi f
            (zetaCompletedExplicitFormulaRightCenteredAffineLine F t)) := by
      exact htransport

/-- Gamma main log-derivative integral transport: the integral of the Gamma
main component with left parameters equals minus the integral with right
parameters. -/
theorem zetaCompletedExplicitFormulaGammaLogDerivativeMain_integral_transport
    (f : ZetaAdmissibleFunction)
    (F : ExplicitFormulaContourFamily) :
    (∫ t : ℝ,
      (1 / 2 : ℂ) *
        Complex.GammaLogDerivativeFixedVerticalShiftNatMain
          ((1 - F.c) / 2)
          (zetaCompletedExplicitFormulaArchimedeanLeftBinetShiftNat F)
          (t / 2) *
        zetaCompletedExplicitFormulaPhi f
          (zetaCompletedExplicitFormulaLeftCenteredAffineLine F t)) =
    - (∫ t : ℝ,
      (1 / 2 : ℂ) *
        Complex.GammaLogDerivativeFixedVerticalMain
          (F.c / 2) (t / 2) *
        zetaCompletedExplicitFormulaPhi f
          (zetaCompletedExplicitFormulaRightCenteredAffineLine F t)) := by
  have hshift_eq :=
    zetaCompletedExplicitFormulaGammaLogDerivativeShiftNatMain_eq_main_of_dual F
  have htransport :
      (∫ t : ℝ,
        (1 / 2 : ℂ) *
          Complex.GammaLogDerivativeFixedVerticalMain
            (F.c / 2) ((-t) / 2) *
          zetaCompletedExplicitFormulaPhi f
            (fun s => -(zetaCompletedExplicitFormulaRightCenteredAffineLine F (-s))) t) =
      - (∫ t : ℝ,
        (1 / 2 : ℂ) *
          Complex.GammaLogDerivativeFixedVerticalMain
            (F.c / 2) (t / 2) *
          zetaCompletedExplicitFormulaPhi f
            (zetaCompletedExplicitFormulaRightCenteredAffineLine F t)) :=
    integral_comp_mul_left_gamma_main_transport
      f F
  calc
    (∫ t : ℝ,
      (1 / 2 : ℂ) *
        Complex.GammaLogDerivativeFixedVerticalShiftNatMain
          ((1 - F.c) / 2)
          (zetaCompletedExplicitFormulaArchimedeanLeftBinetShiftNat F)
          (t / 2) *
        zetaCompletedExplicitFormulaPhi f
          (zetaCompletedExplicitFormulaLeftCenteredAffineLine F t)) =
        (∫ t : ℝ,
          (1 / 2 : ℂ) *
            Complex.GammaLogDerivativeFixedVerticalMain
              (F.c / 2) ((-t) / 2) *
            zetaCompletedExplicitFormulaPhi f
              (fun s => -(zetaCompletedExplicitFormulaRightCenteredAffineLine F (-s))) t) := by
      exact integral_cong_ae
        (Filter.Eventually.of_forall fun t =>
          congrArg₂ HMul.hMul
            (congrArg ((1 / 2 : ℂ) * ·)
              (congrArg₂ Complex.GammaLogDerivativeFixedVerticalMain rfl
                (congrArg (· / 2) (congrArg Neg.neg rfl))))
            (congrArg (zetaCompletedExplicitFormulaPhi f)
              (zetaCompletedExplicitFormulaLeftCenteredAffineLine_eq_neg_rightCenteredAffineLine_of_neg F t)))
    _ = - (∫ t : ℝ,
        (1 / 2 : ℂ) *
          Complex.GammaLogDerivativeFixedVerticalMain
            (F.c / 2) (t / 2) *
          zetaCompletedExplicitFormulaPhi f
            (zetaCompletedExplicitFormulaRightCenteredAffineLine F t)) := by
      exact htransport

/-- Gamma geometry: the shifted Gamma log-derivative remainder component equals
the regular remainder component via the duality between left and right
parameters. -/
theorem zetaCompletedExplicitFormulaGammaLogDerivativeShiftNatRemainder_eq_remainder_of_dual
    (F : ExplicitFormulaContourFamily) :
    (fun t : ℝ =>
      Complex.GammaLogDerivativeFixedVerticalShiftNatRemainder
        ((1 - F.c) / 2)
        (zetaCompletedExplicitFormulaArchimedeanLeftBinetShiftNat F)
        (t / 2)) =
    (fun t : ℝ =>
      Complex.GammaLogDerivativeFixedVerticalRemainder
        (F.c / 2) (t / 2)) := by
  funext t
  exact Complex.GammaLogDerivativeShiftNatRemainder_eq_remainder_of_complementary_shift
    F t

/-- Test function equivalence on centered affine lines: the test function phi
integrated against left-centered and right-centered affine lines produces
equivalent results via the affine-line symmetry. -/
theorem zetaCompletedExplicitFormulaPhi_centered_affine_integral_equivalence
    (f : ZetaAdmissibleFunction)
    (F : ExplicitFormulaContourFamily) :
    (fun t : ℝ =>
      zetaCompletedExplicitFormulaPhi f
        (zetaCompletedExplicitFormulaLeftCenteredAffineLine F t)) =
    (fun t : ℝ =>
      zetaCompletedExplicitFormulaPhi f
        (zetaCompletedExplicitFormulaRightCenteredAffineLine F t)) := by
  funext t
  exact zetaCompletedExplicitFormulaPhi_left_centered_eq_right_centered_of_affine_symmetry
    f F t

/-- Gamma remainder scheduled window integral equivalence: the Gamma remainder
component integrated over a symmetric scheduled window on left and right affine
lines yield the same value by symmetry. -/
theorem zetaCompletedExplicitFormulaGammaLogDerivativeRemainder_scheduledWindow_integral_eq
    (f : ZetaAdmissibleFunction)
    (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F)
    (u : ℝ) :
    (∫ t in Set.Icc
        (-(F.rectangle (h.height_schedule.height u)).T)
        (F.rectangle (h.height_schedule.height u)).T,
      (1 / 2 : ℂ) *
        Complex.GammaLogDerivativeFixedVerticalShiftNatRemainder
          ((1 - F.c) / 2)
          (zetaCompletedExplicitFormulaArchimedeanLeftBinetShiftNat F)
          (t / 2) *
        zetaCompletedExplicitFormulaPhi f
          (zetaCompletedExplicitFormulaLeftCenteredAffineLine F t)) =
    (∫ t in Set.Icc
        (-(F.rectangle (h.height_schedule.height u)).T)
        (F.rectangle (h.height_schedule.height u)).T,
      (1 / 2 : ℂ) *
        Complex.GammaLogDerivativeFixedVerticalRemainder
          (F.c / 2) (t / 2) *
        zetaCompletedExplicitFormulaPhi f
          (zetaCompletedExplicitFormulaRightCenteredAffineLine F t)) := by
  have hshift :=
    zetaCompletedExplicitFormulaGammaLogDerivativeShiftNatRemainder_eq_remainder_of_dual F
  have hphi :=
    zetaCompletedExplicitFormulaPhi_centered_affine_integral_equivalence f F
  have hintegrand :
      (fun t : ℝ =>
        (1 / 2 : ℂ) *
          Complex.GammaLogDerivativeFixedVerticalShiftNatRemainder
            ((1 - F.c) / 2)
            (zetaCompletedExplicitFormulaArchimedeanLeftBinetShiftNat F)
            (t / 2) *
          zetaCompletedExplicitFormulaPhi f
            (zetaCompletedExplicitFormulaLeftCenteredAffineLine F t)) =
      (fun t : ℝ =>
        (1 / 2 : ℂ) *
          Complex.GammaLogDerivativeFixedVerticalRemainder
            (F.c / 2) (t / 2) *
          zetaCompletedExplicitFormulaPhi f
            (zetaCompletedExplicitFormulaRightCenteredAffineLine F t)) := by
    funext t
    exact congrArg₂ HMul.hMul
      (congrArg ((1 / 2 : ℂ) * ·)
        (funext_iff.mp hshift t))
      (funext_iff.mp hphi t)
  exact integral_congr_ae
    (Filter.Eventually.of_forall fun t =>
      hintegrand t)

/-- Deep geometry: left main kernel whole-line integral transport.

The integral of the left main Binet kernel over ℝ equals the negative of the
integral of the right main Binet kernel, due to the orientation reversal between
left-centered and right-centered affine lines and the Gamma shift equivalence. -/
theorem zetaCompletedExplicitFormulaArchimedeanLeftBinetMainKernel_integral_transport
    (f : ZetaAdmissibleFunction)
    (F : ExplicitFormulaContourFamily) :
    (∫ t : ℝ,
      (-(zetaCompletedExplicitFormulaGammaRealPiLogDerivativeTerm +
          (1 / 2 : ℂ) *
            Complex.GammaLogDerivativeFixedVerticalShiftNatMain
              ((1 - F.c) / 2)
              (zetaCompletedExplicitFormulaArchimedeanLeftBinetShiftNat F)
              (t / 2)) -
        explicitFormulaCorrectionLogDerivative
          (zetaCompletedExplicitFormulaLeftAffineLine F t)) *
        zetaCompletedExplicitFormulaPhi f
          (zetaCompletedExplicitFormulaLeftCenteredAffineLine F t)) =
    - (∫ t : ℝ,
      (-(zetaCompletedExplicitFormulaGammaRealPiLogDerivativeTerm +
          (1 / 2 : ℂ) *
            Complex.GammaLogDerivativeFixedVerticalMain
              (F.c / 2) (t / 2)) -
        explicitFormulaCorrectionLogDerivative
          (zetaCompletedExplicitFormulaRightAffineLine F t)) *
        zetaCompletedExplicitFormulaPhi f
          (zetaCompletedExplicitFormulaRightCenteredAffineLine F t)) := by
  have hleft_right_affine :
      zetaCompletedExplicitFormulaLeftAffineLine F =
      fun t : ℝ => -(zetaCompletedExplicitFormulaRightAffineLine F (-t)) :=
    zetaCompletedExplicitFormulaLeftAffineLine_eq_one_sub_rightAffineLine_of_neg
      F
  have hleft_centered_right_centered :
      zetaCompletedExplicitFormulaLeftCenteredAffineLine F =
      fun t : ℝ => -(zetaCompletedExplicitFormulaRightCenteredAffineLine F (-t)) :=
    zetaCompletedExplicitFormulaLeftCenteredAffineLine_eq_neg_rightCenteredAffineLine_of_neg
      F
  have hgamma_shift :
      (fun t : ℝ =>
        Complex.GammaLogDerivativeFixedVerticalShiftNatMain
          ((1 - F.c) / 2)
          (zetaCompletedExplicitFormulaArchimedeanLeftBinetShiftNat F)
          (t / 2)) =
      (fun t : ℝ =>
        Complex.GammaLogDerivativeFixedVerticalMain
          (F.c / 2) ((-t) / 2)) :=
    zetaCompletedExplicitFormulaGammaLogDerivativeShiftNatMain_eq_main_of_dual
      F
  have hcorrection_transport :
      (∫ t : ℝ,
        explicitFormulaCorrectionLogDerivative
          (zetaCompletedExplicitFormulaLeftAffineLine F t) *
          zetaCompletedExplicitFormulaPhi f
            (zetaCompletedExplicitFormulaLeftCenteredAffineLine F t)) =
      - (∫ t : ℝ,
        explicitFormulaCorrectionLogDerivative
          (zetaCompletedExplicitFormulaRightAffineLine F t) *
          zetaCompletedExplicitFormulaPhi f
            (zetaCompletedExplicitFormulaRightCenteredAffineLine F t)) :=
    zetaCompletedExplicitFormulaCorrectionLogDerivative_integral_transport
      f F
  have hgamma_pi_term :
      (∫ t : ℝ,
        zetaCompletedExplicitFormulaGammaRealPiLogDerivativeTerm *
          zetaCompletedExplicitFormulaPhi f
            (zetaCompletedExplicitFormulaLeftCenteredAffineLine F t)) =
      - (∫ t : ℝ,
        zetaCompletedExplicitFormulaGammaRealPiLogDerivativeTerm *
          zetaCompletedExplicitFormulaPhi f
            (zetaCompletedExplicitFormulaRightCenteredAffineLine F t)) :=
    zetaCompletedExplicitFormulaGammaRealPiLogDerivativeTerm_integral_transport
      f F
  have hgamma_main :
      (∫ t : ℝ,
        (1 / 2 : ℂ) *
          Complex.GammaLogDerivativeFixedVerticalShiftNatMain
            ((1 - F.c) / 2)
            (zetaCompletedExplicitFormulaArchimedeanLeftBinetShiftNat F)
            (t / 2) *
          zetaCompletedExplicitFormulaPhi f
            (zetaCompletedExplicitFormulaLeftCenteredAffineLine F t)) =
      - (∫ t : ℝ,
        (1 / 2 : ℂ) *
          Complex.GammaLogDerivativeFixedVerticalMain
            (F.c / 2) (t / 2) *
          zetaCompletedExplicitFormulaPhi f
            (zetaCompletedExplicitFormulaRightCenteredAffineLine F t)) :=
    zetaCompletedExplicitFormulaGammaLogDerivativeMain_integral_transport
      f F
  calc
    (∫ t : ℝ,
      (-(zetaCompletedExplicitFormulaGammaRealPiLogDerivativeTerm +
          (1 / 2 : ℂ) *
            Complex.GammaLogDerivativeFixedVerticalShiftNatMain
              ((1 - F.c) / 2)
              (zetaCompletedExplicitFormulaArchimedeanLeftBinetShiftNat F)
              (t / 2)) -
        explicitFormulaCorrectionLogDerivative
          (zetaCompletedExplicitFormulaLeftAffineLine F t)) *
        zetaCompletedExplicitFormulaPhi f
          (zetaCompletedExplicitFormulaLeftCenteredAffineLine F t)) =
        - (∫ t : ℝ,
          (zetaCompletedExplicitFormulaGammaRealPiLogDerivativeTerm +
            (1 / 2 : ℂ) *
              Complex.GammaLogDerivativeFixedVerticalShiftNatMain
                ((1 - F.c) / 2)
                (zetaCompletedExplicitFormulaArchimedeanLeftBinetShiftNat F)
                (t / 2)) *
            zetaCompletedExplicitFormulaPhi f
              (zetaCompletedExplicitFormulaLeftCenteredAffineLine F t)) -
          ∫ t : ℝ,
            explicitFormulaCorrectionLogDerivative
              (zetaCompletedExplicitFormulaLeftAffineLine F t) *
              zetaCompletedExplicitFormulaPhi f
                (zetaCompletedExplicitFormulaLeftCenteredAffineLine F t) := by
          rfl
    _ = - ((∫ t : ℝ,
          zetaCompletedExplicitFormulaGammaRealPiLogDerivativeTerm *
            zetaCompletedExplicitFormulaPhi f
              (zetaCompletedExplicitFormulaLeftCenteredAffineLine F t)) +
        ∫ t : ℝ,
          (1 / 2 : ℂ) *
            Complex.GammaLogDerivativeFixedVerticalShiftNatMain
              ((1 - F.c) / 2)
              (zetaCompletedExplicitFormulaArchimedeanLeftBinetShiftNat F)
              (t / 2) *
              zetaCompletedExplicitFormulaPhi f
                (zetaCompletedExplicitFormulaLeftCenteredAffineLine F t)) -
        ∫ t : ℝ,
          explicitFormulaCorrectionLogDerivative
            (zetaCompletedExplicitFormulaLeftAffineLine F t) *
            zetaCompletedExplicitFormulaPhi f
              (zetaCompletedExplicitFormulaLeftCenteredAffineLine F t) := by
      rfl
    _ = - ((- ∫ t : ℝ,
          zetaCompletedExplicitFormulaGammaRealPiLogDerivativeTerm *
            zetaCompletedExplicitFormulaPhi f
              (zetaCompletedExplicitFormulaRightCenteredAffineLine F t)) +
        - (∫ t : ℝ,
          (1 / 2 : ℂ) *
            Complex.GammaLogDerivativeFixedVerticalMain
              (F.c / 2) (t / 2) *
              zetaCompletedExplicitFormulaPhi f
                (zetaCompletedExplicitFormulaRightCenteredAffineLine F t))) -
        - (∫ t : ℝ,
          explicitFormulaCorrectionLogDerivative
            (zetaCompletedExplicitFormulaRightAffineLine F t) *
            zetaCompletedExplicitFormulaPhi f
              (zetaCompletedExplicitFormulaRightCenteredAffineLine F t))) := by
      exact congrArg Neg.neg
        (congrArg₂ HAdd.hAdd
          (congrArg₂ HAdd.hAdd hgamma_pi_term hgamma_main)
          hcorrection_transport)
    _ = - (∫ t : ℝ,
      (-(zetaCompletedExplicitFormulaGammaRealPiLogDerivativeTerm +
          (1 / 2 : ℂ) *
            Complex.GammaLogDerivativeFixedVerticalMain
              (F.c / 2) (t / 2)) -
        explicitFormulaCorrectionLogDerivative
          (zetaCompletedExplicitFormulaRightAffineLine F t)) *
        zetaCompletedExplicitFormulaPhi f
          (zetaCompletedExplicitFormulaRightCenteredAffineLine F t)) := by
      rfl

/-- Deep geometry: left remainder scheduled window transport.

The integral of the left remainder Binet kernel over a symmetric scheduled
window equals the integral of the right remainder Binet kernel over the same
window, due to the symmetry of the remainder component and affine equivalence. -/
theorem zetaCompletedExplicitFormulaArchimedeanLeftBinetRemainderKernel_scheduledWindow_transport
    (f : ZetaAdmissibleFunction)
    (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F)
    (u : ℝ) :
    (∫ t in Set.Icc
        (-(F.rectangle (h.height_schedule.height u)).T)
        (F.rectangle (h.height_schedule.height u)).T,
      (-((1 / 2 : ℂ) *
        Complex.GammaLogDerivativeFixedVerticalShiftNatRemainder
          ((1 - F.c) / 2)
          (zetaCompletedExplicitFormulaArchimedeanLeftBinetShiftNat F)
          (t / 2))) *
        zetaCompletedExplicitFormulaPhi f
          (zetaCompletedExplicitFormulaLeftCenteredAffineLine F t)) =
    (∫ t in Set.Icc
        (-(F.rectangle (h.height_schedule.height u)).T)
        (F.rectangle (h.height_schedule.height u)).T,
      (-((1 / 2 : ℂ) *
        Complex.GammaLogDerivativeFixedVerticalRemainder
          (F.c / 2) (t / 2))) *
        zetaCompletedExplicitFormulaPhi f
          (zetaCompletedExplicitFormulaRightCenteredAffineLine F t)) := by
  have hgamma_shift :
      (fun t : ℝ =>
        Complex.GammaLogDerivativeFixedVerticalShiftNatRemainder
          ((1 - F.c) / 2)
          (zetaCompletedExplicitFormulaArchimedeanLeftBinetShiftNat F)
          (t / 2)) =
      (fun t : ℝ =>
        Complex.GammaLogDerivativeFixedVerticalRemainder
          (F.c / 2) (t / 2)) :=
    zetaCompletedExplicitFormulaGammaLogDerivativeShiftNatRemainder_eq_remainder_of_dual
      F
  have hphi_transport :
      (fun t : ℝ =>
        zetaCompletedExplicitFormulaPhi f
          (zetaCompletedExplicitFormulaLeftCenteredAffineLine F t)) =
      (fun t : ℝ =>
        zetaCompletedExplicitFormulaPhi f
          (zetaCompletedExplicitFormulaRightCenteredAffineLine F t)) :=
    zetaCompletedExplicitFormulaPhi_centered_affine_integral_equivalence
      f F
  have hgamma_remainder_integral :
      (∫ t in Set.Icc
          (-(F.rectangle (h.height_schedule.height u)).T)
          (F.rectangle (h.height_schedule.height u)).T,
        (1 / 2 : ℂ) *
          Complex.GammaLogDerivativeFixedVerticalShiftNatRemainder
            ((1 - F.c) / 2)
            (zetaCompletedExplicitFormulaArchimedeanLeftBinetShiftNat F)
            (t / 2) *
          zetaCompletedExplicitFormulaPhi f
            (zetaCompletedExplicitFormulaLeftCenteredAffineLine F t)) =
      (∫ t in Set.Icc
          (-(F.rectangle (h.height_schedule.height u)).T)
          (F.rectangle (h.height_schedule.height u)).T,
        (1 / 2 : ℂ) *
          Complex.GammaLogDerivativeFixedVerticalRemainder
            (F.c / 2) (t / 2) *
          zetaCompletedExplicitFormulaPhi f
            (zetaCompletedExplicitFormulaRightCenteredAffineLine F t)) :=
    zetaCompletedExplicitFormulaGammaLogDerivativeRemainder_scheduledWindow_integral_eq
      f F h u
  calc
    (∫ t in Set.Icc
        (-(F.rectangle (h.height_schedule.height u)).T)
        (F.rectangle (h.height_schedule.height u)).T,
      (-((1 / 2 : ℂ) *
        Complex.GammaLogDerivativeFixedVerticalShiftNatRemainder
          ((1 - F.c) / 2)
          (zetaCompletedExplicitFormulaArchimedeanLeftBinetShiftNat F)
          (t / 2))) *
        zetaCompletedExplicitFormulaPhi f
          (zetaCompletedExplicitFormulaLeftCenteredAffineLine F t)) =
        - (∫ t in Set.Icc
          (-(F.rectangle (h.height_schedule.height u)).T)
          (F.rectangle (h.height_schedule.height u)).T,
          (1 / 2 : ℂ) *
            Complex.GammaLogDerivativeFixedVerticalShiftNatRemainder
              ((1 - F.c) / 2)
              (zetaCompletedExplicitFormulaArchimedeanLeftBinetShiftNat F)
              (t / 2) *
              zetaCompletedExplicitFormulaPhi f
                (zetaCompletedExplicitFormulaLeftCenteredAffineLine F t)) := by
          rfl
    _ = - (∫ t in Set.Icc
        (-(F.rectangle (h.height_schedule.height u)).T)
        (F.rectangle (h.height_schedule.height u)).T,
        (1 / 2 : ℂ) *
          Complex.GammaLogDerivativeFixedVerticalRemainder
            (F.c / 2) (t / 2) *
            zetaCompletedExplicitFormulaPhi f
              (zetaCompletedExplicitFormulaRightCenteredAffineLine F t)) := by
      exact congrArg Neg.neg hgamma_remainder_integral
    _ = (∫ t in Set.Icc
        (-(F.rectangle (h.height_schedule.height u)).T)
        (F.rectangle (h.height_schedule.height u)).T,
      (-((1 / 2 : ℂ) *
        Complex.GammaLogDerivativeFixedVerticalRemainder
          (F.c / 2) (t / 2))) *
        zetaCompletedExplicitFormulaPhi f
          (zetaCompletedExplicitFormulaRightCenteredAffineLine F t)) := by
      rfl

/-- Transport: left main whole-line integral equals negative of right main
whole-line integral.

The left Binet main kernel uses the shifted Gamma function on the left affine
line, while the right Binet main kernel uses the regular Gamma function on the
right affine line. The contour deformation from right to left contributes an
orientation sign, yielding the negation. -/
theorem zetaCompletedExplicitFormulaArchimedeanLeftBinetMainKernel_integral_eq_neg_RightBinetMainKernel_integral
    (f : ZetaAdmissibleFunction)
    (F : ExplicitFormulaContourFamily) :
    (∫ t : ℝ,
      zetaCompletedExplicitFormulaArchimedeanLeftBinetMainKernel
        f F t) =
    - (∫ t : ℝ,
      zetaCompletedExplicitFormulaArchimedeanRightBinetMainKernel
        f F t) := by
  have hleft_def :
      (∫ t : ℝ,
        zetaCompletedExplicitFormulaArchimedeanLeftBinetMainKernel f F t) =
      (∫ t : ℝ,
        (-(zetaCompletedExplicitFormulaGammaRealPiLogDerivativeTerm +
            (1 / 2 : ℂ) *
              Complex.GammaLogDerivativeFixedVerticalShiftNatMain
                ((1 - F.c) / 2)
                (zetaCompletedExplicitFormulaArchimedeanLeftBinetShiftNat F)
                (t / 2)) -
          explicitFormulaCorrectionLogDerivative
            (zetaCompletedExplicitFormulaLeftAffineLine F t)) *
          zetaCompletedExplicitFormulaPhi f
            (zetaCompletedExplicitFormulaLeftCenteredAffineLine F t)) := by
    exact rfl
  have hright_def :
      (∫ t : ℝ,
        zetaCompletedExplicitFormulaArchimedeanRightBinetMainKernel f F t) =
      (∫ t : ℝ,
        (-(zetaCompletedExplicitFormulaGammaRealPiLogDerivativeTerm +
            (1 / 2 : ℂ) *
              Complex.GammaLogDerivativeFixedVerticalMain
                (F.c / 2) (t / 2)) -
          explicitFormulaCorrectionLogDerivative
            (zetaCompletedExplicitFormulaRightAffineLine F t)) *
          zetaCompletedExplicitFormulaPhi f
            (zetaCompletedExplicitFormulaRightCenteredAffineLine F t)) := by
    exact rfl
  have htransport :
      (∫ t : ℝ,
        (-(zetaCompletedExplicitFormulaGammaRealPiLogDerivativeTerm +
            (1 / 2 : ℂ) *
              Complex.GammaLogDerivativeFixedVerticalShiftNatMain
                ((1 - F.c) / 2)
                (zetaCompletedExplicitFormulaArchimedeanLeftBinetShiftNat F)
                (t / 2)) -
          explicitFormulaCorrectionLogDerivative
            (zetaCompletedExplicitFormulaLeftAffineLine F t)) *
          zetaCompletedExplicitFormulaPhi f
            (zetaCompletedExplicitFormulaLeftCenteredAffineLine F t)) =
      - (∫ t : ℝ,
        (-(zetaCompletedExplicitFormulaGammaRealPiLogDerivativeTerm +
            (1 / 2 : ℂ) *
              Complex.GammaLogDerivativeFixedVerticalMain
                (F.c / 2) (t / 2)) -
          explicitFormulaCorrectionLogDerivative
            (zetaCompletedExplicitFormulaRightAffineLine F t)) *
          zetaCompletedExplicitFormulaPhi f
            (zetaCompletedExplicitFormulaRightCenteredAffineLine F t)) :=
    zetaCompletedExplicitFormulaArchimedeanLeftBinetMainKernel_integral_transport
      f F
  calc
    (∫ t : ℝ,
      zetaCompletedExplicitFormulaArchimedeanLeftBinetMainKernel f F t) =
        (∫ t : ℝ,
          (-(zetaCompletedExplicitFormulaGammaRealPiLogDerivativeTerm +
              (1 / 2 : ℂ) *
                Complex.GammaLogDerivativeFixedVerticalShiftNatMain
                  ((1 - F.c) / 2)
                  (zetaCompletedExplicitFormulaArchimedeanLeftBinetShiftNat F)
                  (t / 2)) -
            explicitFormulaCorrectionLogDerivative
              (zetaCompletedExplicitFormulaLeftAffineLine F t)) *
            zetaCompletedExplicitFormulaPhi f
              (zetaCompletedExplicitFormulaLeftCenteredAffineLine F t)) := by
      exact hleft_def
    _ = - (∫ t : ℝ,
        (-(zetaCompletedExplicitFormulaGammaRealPiLogDerivativeTerm +
            (1 / 2 : ℂ) *
              Complex.GammaLogDerivativeFixedVerticalMain
                (F.c / 2) (t / 2)) -
          explicitFormulaCorrectionLogDerivative
            (zetaCompletedExplicitFormulaRightAffineLine F t)) *
          zetaCompletedExplicitFormulaPhi f
            (zetaCompletedExplicitFormulaRightCenteredAffineLine F t)) := by
      exact htransport
    _ = - (∫ t : ℝ,
        zetaCompletedExplicitFormulaArchimedeanRightBinetMainKernel f F t) := by
      exact congrArg Neg.neg hright_def.symm

/-- Transport: left remainder scheduled window equals right remainder scheduled
window.

The left and right remainder kernels, integrated over symmetric intervals,
yield equal results due to the symmetry of the affine geometry and the shared
form of the remainder component. -/
theorem zetaCompletedExplicitFormulaArchimedeanLeftBinetRemainderKernel_scheduledWindow_eq_right
    (f : ZetaAdmissibleFunction)
    (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F)
    (u : ℝ) :
    (∫ t in Set.Icc
        (-(F.rectangle (h.height_schedule.height u)).T)
        (F.rectangle (h.height_schedule.height u)).T,
      zetaCompletedExplicitFormulaArchimedeanLeftBinetRemainderKernel
        f F t) =
    (∫ t in Set.Icc
        (-(F.rectangle (h.height_schedule.height u)).T)
        (F.rectangle (h.height_schedule.height u)).T,
      zetaCompletedExplicitFormulaArchimedeanRightBinetRemainderKernel
        f F t) := by
  have hleft_def :
      (∫ t in Set.Icc
          (-(F.rectangle (h.height_schedule.height u)).T)
          (F.rectangle (h.height_schedule.height u)).T,
        zetaCompletedExplicitFormulaArchimedeanLeftBinetRemainderKernel f F t) =
      (∫ t in Set.Icc
          (-(F.rectangle (h.height_schedule.height u)).T)
          (F.rectangle (h.height_schedule.height u)).T,
        (-((1 / 2 : ℂ) *
          Complex.GammaLogDerivativeFixedVerticalShiftNatRemainder
            ((1 - F.c) / 2)
            (zetaCompletedExplicitFormulaArchimedeanLeftBinetShiftNat F)
            (t / 2))) *
          zetaCompletedExplicitFormulaPhi f
            (zetaCompletedExplicitFormulaLeftCenteredAffineLine F t)) := by
    exact rfl
  have hright_def :
      (∫ t in Set.Icc
          (-(F.rectangle (h.height_schedule.height u)).T)
          (F.rectangle (h.height_schedule.height u)).T,
        zetaCompletedExplicitFormulaArchimedeanRightBinetRemainderKernel f F t) =
      (∫ t in Set.Icc
          (-(F.rectangle (h.height_schedule.height u)).T)
          (F.rectangle (h.height_schedule.height u)).T,
        (-((1 / 2 : ℂ) *
          Complex.GammaLogDerivativeFixedVerticalRemainder
            (F.c / 2) (t / 2))) *
          zetaCompletedExplicitFormulaPhi f
            (zetaCompletedExplicitFormulaRightCenteredAffineLine F t)) := by
    exact rfl
  have htransport :
      (∫ t in Set.Icc
          (-(F.rectangle (h.height_schedule.height u)).T)
          (F.rectangle (h.height_schedule.height u)).T,
        (-((1 / 2 : ℂ) *
          Complex.GammaLogDerivativeFixedVerticalShiftNatRemainder
            ((1 - F.c) / 2)
            (zetaCompletedExplicitFormulaArchimedeanLeftBinetShiftNat F)
            (t / 2))) *
          zetaCompletedExplicitFormulaPhi f
            (zetaCompletedExplicitFormulaLeftCenteredAffineLine F t)) =
      (∫ t in Set.Icc
          (-(F.rectangle (h.height_schedule.height u)).T)
          (F.rectangle (h.height_schedule.height u)).T,
        (-((1 / 2 : ℂ) *
          Complex.GammaLogDerivativeFixedVerticalRemainder
            (F.c / 2) (t / 2))) *
          zetaCompletedExplicitFormulaPhi f
            (zetaCompletedExplicitFormulaRightCenteredAffineLine F t)) :=
    zetaCompletedExplicitFormulaArchimedeanLeftBinetRemainderKernel_scheduledWindow_transport
      f F h u
  calc
    (∫ t in Set.Icc
        (-(F.rectangle (h.height_schedule.height u)).T)
        (F.rectangle (h.height_schedule.height u)).T,
      zetaCompletedExplicitFormulaArchimedeanLeftBinetRemainderKernel f F t) =
        (∫ t in Set.Icc
          (-(F.rectangle (h.height_schedule.height u)).T)
          (F.rectangle (h.height_schedule.height u)).T,
          (-((1 / 2 : ℂ) *
            Complex.GammaLogDerivativeFixedVerticalShiftNatRemainder
              ((1 - F.c) / 2)
              (zetaCompletedExplicitFormulaArchimedeanLeftBinetShiftNat F)
              (t / 2))) *
            zetaCompletedExplicitFormulaPhi f
              (zetaCompletedExplicitFormulaLeftCenteredAffineLine F t)) := by
      exact hleft_def
    _ = (∫ t in Set.Icc
        (-(F.rectangle (h.height_schedule.height u)).T)
        (F.rectangle (h.height_schedule.height u)).T,
        (-((1 / 2 : ℂ) *
          Complex.GammaLogDerivativeFixedVerticalRemainder
            (F.c / 2) (t / 2))) *
          zetaCompletedExplicitFormulaPhi f
            (zetaCompletedExplicitFormulaRightCenteredAffineLine F t)) := by
      exact htransport
    _ = (∫ t in Set.Icc
        (-(F.rectangle (h.height_schedule.height u)).T)
        (F.rectangle (h.height_schedule.height u)).T,
      zetaCompletedExplicitFormulaArchimedeanRightBinetRemainderKernel f F t) := by
      exact hright_def.symm

end ZetaAdmissibleFunction

end
end LFunctions
end Boundary
