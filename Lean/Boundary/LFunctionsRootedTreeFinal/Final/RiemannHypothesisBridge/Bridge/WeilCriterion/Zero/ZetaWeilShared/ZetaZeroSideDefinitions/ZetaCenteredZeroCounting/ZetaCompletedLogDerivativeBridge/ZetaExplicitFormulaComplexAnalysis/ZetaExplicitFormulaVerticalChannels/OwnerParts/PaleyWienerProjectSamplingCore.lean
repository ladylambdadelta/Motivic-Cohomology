import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaExplicitFormulaVerticalChannels.OwnerParts.PrimeNaturalTimeArithmetic
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaExplicitFormulaVerticalChannels.OwnerParts.PrimeRightTermKernelAlgebra
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaExplicitFormulaVerticalChannels.OwnerParts.PaleyWienerFourierHypotheses

/-!
# Project-convention Paley-Wiener sampling core

This file owns the analytic Fourier/Mellin sampling theorem for a single
positive natural frequency in the project convention.  The statement is kept at
the raw `dt` integral level so the `2 * pi` normalization and Mellin prefactor
cannot be hidden in downstream arithmetic.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open Complex
open Filter
open LSeries ArithmeticFunction
open MeasureTheory
open scoped ArithmeticFunction
open scoped FourierTransform
open scoped Topology

namespace ZetaAdmissibleFunction

/-- Direct Mellin/Fourier inversion at the project natural-number center.

This is only specialization of the generic Mellin bridge to the positive real
argument supplied by a nonzero natural index.  The analytic raw-line sampling
theorem still has to identify the project `dt` integral with this Mellin
inverse and track the `sqrt n` character normalization. -/
theorem zetaCompletedExplicitFormulaDirectVerticalMellinInv_eq_fourierIntegralInv_primeNaturalCenter
    (σ : ℝ) (G : ℂ → ℂ) {n : ℕ} (hn : n ≠ 0) :
    zetaCompletedExplicitFormulaDirectVerticalMellinInv σ G n =
      (n : ℂ) ^ (-σ : ℂ) •
        𝓕⁻ (fun y : ℝ => G (σ + 2 * π * y * I))
          (-(zetaCompletedExplicitFormulaPrimeNaturalCenter n)) := by
  have hpositive : 0 < (n : ℝ) :=
    zetaCompletedExplicitFormulaPrimeNaturalCast_pos hn
  have hgeneric :
      zetaCompletedExplicitFormulaDirectVerticalMellinInv σ G n =
        (n : ℂ) ^ (-σ : ℂ) •
          𝓕⁻ (fun y : ℝ => G (σ + 2 * π * y * I))
            (-Real.log n) :=
    zetaCompletedExplicitFormulaDirectVerticalMellinInv_eq_fourierIntegralInv
      σ G hpositive
  have hcenter :
      -Real.log n =
        -(zetaCompletedExplicitFormulaPrimeNaturalCenter n) := by
    exact congrArg Neg.neg
      (zetaCompletedExplicitFormulaPrimeNaturalCenter_eq_log n).symm
  exact Eq.subst
    (motive := fun x : ℝ =>
      zetaCompletedExplicitFormulaDirectVerticalMellinInv σ G n =
        (n : ℂ) ^ (-σ : ℂ) •
          𝓕⁻ (fun y : ℝ => G (σ + 2 * π * y * I)) x)
    hcenter
    hgeneric

/-- The direct Mellin integrand on the centered right affine line is the
centered right-line character times `Phi_f`.

This is only a coordinate/definition bridge; the uncentered project character
still has to be related to this expression by the separate `sqrt n`
normalization. -/
theorem zetaCompletedExplicitFormulaDirectVerticalMellinIntegrand_eq_rightCenteredPhi
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (n : ℕ) (t : ℝ) :
    zetaCompletedExplicitFormulaDirectVerticalMellinIntegrand
        (F.c - (1 / 2 : ℝ))
        (zetaCompletedExplicitFormulaPhi f)
        n t =
      (n : ℂ) ^
          (-(zetaCompletedExplicitFormulaRightCenteredAffineLine F t)) *
        zetaCompletedExplicitFormulaPhi f
          (zetaCompletedExplicitFormulaRightCenteredAffineLine F t) := by
  calc
    zetaCompletedExplicitFormulaDirectVerticalMellinIntegrand
        (F.c - (1 / 2 : ℝ))
        (zetaCompletedExplicitFormulaPhi f)
        n t =
        (n : ℂ) ^
            (-(((F.c - (1 / 2 : ℝ) : ℝ) : ℂ) + t * I)) *
          zetaCompletedExplicitFormulaPhi f
            (((F.c - (1 / 2 : ℝ) : ℝ) : ℂ) + t * I) := by
      rfl
    _ =
        (n : ℂ) ^
            (-(((F.c : ℂ) - (1 / 2 : ℂ)) + t * I)) *
          zetaCompletedExplicitFormulaPhi f
            (((F.c : ℂ) - (1 / 2 : ℂ)) + t * I) := by
      have hline :
          (((F.c - (1 / 2 : ℝ) : ℝ) : ℂ) + t * I) =
            (((F.c : ℂ) - (1 / 2 : ℂ)) + t * I) := by
        exact congrArg (fun z : ℂ => z + t * I)
          (Complex.ofReal_sub F.c (1 / 2 : ℝ))
      exact congrArg
        (fun z : ℂ =>
          (n : ℂ) ^ (-z) * zetaCompletedExplicitFormulaPhi f z)
        hline
    _ =
        (n : ℂ) ^
            (-(zetaCompletedExplicitFormulaRightCenteredAffineLine F t)) *
          zetaCompletedExplicitFormulaPhi f
            (zetaCompletedExplicitFormulaRightCenteredAffineLine F t) := by
      exact congrArg
        (fun z : ℂ =>
          (n : ℂ) ^ (-z) * zetaCompletedExplicitFormulaPhi f z)
        (zetaCompletedExplicitFormulaRightCenteredAffineLine_eq F t).symm

/-- Whole-line integral form of the centered right-line Mellin integrand
coordinate bridge. -/
theorem zetaCompletedExplicitFormulaDirectVerticalMellinIntegral_eq_rightCenteredPhi_integral
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (n : ℕ) :
    zetaCompletedExplicitFormulaDirectVerticalMellinIntegral
        (F.c - (1 / 2 : ℝ))
        (zetaCompletedExplicitFormulaPhi f)
        n =
      ∫ t : ℝ,
        (n : ℂ) ^
            (-(zetaCompletedExplicitFormulaRightCenteredAffineLine F t)) *
          zetaCompletedExplicitFormulaPhi f
            (zetaCompletedExplicitFormulaRightCenteredAffineLine F t) := by
  have hfun :
      (fun t : ℝ =>
        zetaCompletedExplicitFormulaDirectVerticalMellinIntegrand
          (F.c - (1 / 2 : ℝ))
          (zetaCompletedExplicitFormulaPhi f)
          n t) =
        fun t : ℝ =>
          (n : ℂ) ^
              (-(zetaCompletedExplicitFormulaRightCenteredAffineLine F t)) *
            zetaCompletedExplicitFormulaPhi f
              (zetaCompletedExplicitFormulaRightCenteredAffineLine F t) := by
    funext t
    exact
      zetaCompletedExplicitFormulaDirectVerticalMellinIntegrand_eq_rightCenteredPhi
        f F n t
  calc
    zetaCompletedExplicitFormulaDirectVerticalMellinIntegral
        (F.c - (1 / 2 : ℝ))
        (zetaCompletedExplicitFormulaPhi f)
        n =
        ∫ t : ℝ,
          zetaCompletedExplicitFormulaDirectVerticalMellinIntegrand
            (F.c - (1 / 2 : ℝ))
            (zetaCompletedExplicitFormulaPhi f)
            n t := by
      rfl
    _ =
        ∫ t : ℝ,
          (n : ℂ) ^
              (-(zetaCompletedExplicitFormulaRightCenteredAffineLine F t)) *
            zetaCompletedExplicitFormulaPhi f
              (zetaCompletedExplicitFormulaRightCenteredAffineLine F t) := by
      exact congrArg (fun φ : ℝ → ℂ => ∫ t : ℝ, φ t) hfun

/-- The uncentered right affine line is the centered right affine line shifted
by `1/2`.  This is the algebraic source of the `sqrt n` factor in the
project prime normalization. -/
theorem zetaCompletedExplicitFormulaRightAffineLine_eq_rightCentered_add_half
    (F : ExplicitFormulaContourFamily) (t : ℝ) :
    zetaCompletedExplicitFormulaRightAffineLine F t =
      zetaCompletedExplicitFormulaRightCenteredAffineLine F t +
        (1 / 2 : ℂ) := by
  calc
    zetaCompletedExplicitFormulaRightAffineLine F t =
        (F.c : ℂ) + t * I := by
      exact zetaCompletedExplicitFormulaRightAffineLine_eq F t
    _ =
        (((F.c : ℂ) - (1 / 2 : ℂ)) + t * I) +
          (1 / 2 : ℂ) := by
      calc
        (F.c : ℂ) + t * I =
            ((F.c : ℂ) + 0) + t * I := by
          exact congrArg (fun z : ℂ => z + t * I)
            (add_zero (F.c : ℂ)).symm
        _ =
            ((F.c : ℂ) + (-(1 / 2 : ℂ) + (1 / 2 : ℂ))) + t * I := by
          exact congrArg (fun z : ℂ => ((F.c : ℂ) + z) + t * I)
            (neg_add_cancel (1 / 2 : ℂ)).symm
        _ =
            (((F.c : ℂ) + -(1 / 2 : ℂ)) + (1 / 2 : ℂ)) + t * I := by
          exact congrArg (fun z : ℂ => z + t * I)
            (add_assoc (F.c : ℂ) (-(1 / 2 : ℂ)) (1 / 2 : ℂ)).symm
        _ =
            (((F.c : ℂ) - (1 / 2 : ℂ)) + (1 / 2 : ℂ)) + t * I := by
          exact congrArg (fun z : ℂ => (z + (1 / 2 : ℂ)) + t * I)
            (sub_eq_add_neg (F.c : ℂ) (1 / 2 : ℂ)).symm
        _ =
            ((F.c : ℂ) - (1 / 2 : ℂ)) + ((1 / 2 : ℂ) + t * I) := by
          exact add_assoc ((F.c : ℂ) - (1 / 2 : ℂ)) (1 / 2 : ℂ) (t * I)
        _ =
            ((F.c : ℂ) - (1 / 2 : ℂ)) + (t * I + (1 / 2 : ℂ)) := by
          exact congrArg
            (fun z : ℂ => ((F.c : ℂ) - (1 / 2 : ℂ)) + z)
            (add_comm (1 / 2 : ℂ) (t * I))
        _ =
            (((F.c : ℂ) - (1 / 2 : ℂ)) + t * I) +
              (1 / 2 : ℂ) := by
          exact (add_assoc ((F.c : ℂ) - (1 / 2 : ℂ)) (t * I) (1 / 2 : ℂ)).symm
    _ =
        zetaCompletedExplicitFormulaRightCenteredAffineLine F t +
          (1 / 2 : ℂ) := by
      exact congrArg (fun z : ℂ => z + (1 / 2 : ℂ))
        (zetaCompletedExplicitFormulaRightCenteredAffineLine_eq F t).symm

/-- The right-line natural character splits into the centered character and
the inverse square-root factor. -/
theorem zetaCompletedExplicitFormulaPrimeNatural_rightAffineCharacter_eq_invSqrt_mul_centered
    (F : ExplicitFormulaContourFamily) {n : ℕ} (hn : n ≠ 0) (t : ℝ) :
    (n : ℂ) ^ (-(zetaCompletedExplicitFormulaRightAffineLine F t)) =
      ((Real.sqrt n : ℂ))⁻¹ *
        (n : ℂ) ^
          (-(zetaCompletedExplicitFormulaRightCenteredAffineLine F t)) := by
  let centered : ℂ :=
    zetaCompletedExplicitFormulaRightCenteredAffineLine F t
  have hbase : (n : ℂ) ≠ 0 :=
    zetaCompletedExplicitFormulaPrimeNaturalCast_complex_ne_zero hn
  have hright :
      zetaCompletedExplicitFormulaRightAffineLine F t =
        centered + (1 / 2 : ℂ) :=
    zetaCompletedExplicitFormulaRightAffineLine_eq_rightCentered_add_half F t
  have hexponent :
      -(zetaCompletedExplicitFormulaRightAffineLine F t) =
        (-(1 / 2 : ℂ)) + (-centered) := by
    have hneg :
        -(centered + (1 / 2 : ℂ)) =
          (-centered) + (-(1 / 2 : ℂ)) :=
      neg_add centered (1 / 2 : ℂ)
    calc
      -(zetaCompletedExplicitFormulaRightAffineLine F t) =
          -(centered + (1 / 2 : ℂ)) := by
        exact congrArg Neg.neg hright
      _ = (-centered) + (-(1 / 2 : ℂ)) :=
        hneg
      _ = (-(1 / 2 : ℂ)) + (-centered) := by
        exact add_comm (-centered) (-(1 / 2 : ℂ))
  have hsplit :
      (n : ℂ) ^ ((-(1 / 2 : ℂ)) + (-centered)) =
        (n : ℂ) ^ (-(1 / 2 : ℂ)) *
          (n : ℂ) ^ (-centered) :=
    Complex.cpow_add (-(1 / 2 : ℂ)) (-centered) hbase
  calc
    (n : ℂ) ^ (-(zetaCompletedExplicitFormulaRightAffineLine F t)) =
        (n : ℂ) ^ ((-(1 / 2 : ℂ)) + (-centered)) := by
      exact congrArg (fun z : ℂ => (n : ℂ) ^ z) hexponent
    _ =
        (n : ℂ) ^ (-(1 / 2 : ℂ)) *
          (n : ℂ) ^ (-centered) :=
      hsplit
    _ =
        ((Real.sqrt n : ℂ))⁻¹ *
          (n : ℂ) ^ (-centered) := by
      exact congrArg
        (fun z : ℂ => z * (n : ℂ) ^ (-centered))
        (zetaCompletedExplicitFormulaPrimeNatural_cpow_neg_half_eq_inv_sqrt n)

/-- Pointwise project-character normalization for a positive natural
von-Mangoldt monomial on the right line. -/
theorem zetaCompletedExplicitFormulaPrimeRightVonMangoldtPositiveMonomial_eq_weight_mul_centeredMellinIntegrand
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    {n : ℕ} (hn : n ≠ 0) (t : ℝ) :
    ((↗Λ) n /
        (n : ℂ) ^ zetaCompletedExplicitFormulaRightAffineLine F t) *
      zetaCompletedExplicitFormulaPhi f
        (zetaCompletedExplicitFormulaRightCenteredAffineLine F t) =
      ((Λ n / Real.sqrt n : ℝ) : ℂ) *
        ((n : ℂ) ^
            (-(zetaCompletedExplicitFormulaRightCenteredAffineLine F t)) *
          zetaCompletedExplicitFormulaPhi f
            (zetaCompletedExplicitFormulaRightCenteredAffineLine F t)) := by
  let centered : ℂ :=
    zetaCompletedExplicitFormulaRightCenteredAffineLine F t
  let phi : ℂ :=
    zetaCompletedExplicitFormulaPhi f centered
  have hbase : (n : ℂ) ≠ 0 :=
    zetaCompletedExplicitFormulaPrimeNaturalCast_complex_ne_zero hn
  have hchar_inv :
      ((n : ℂ) ^ zetaCompletedExplicitFormulaRightAffineLine F t)⁻¹ =
        (n : ℂ) ^ (-(zetaCompletedExplicitFormulaRightAffineLine F t)) :=
    (Complex.cpow_neg (n : ℂ)
      (zetaCompletedExplicitFormulaRightAffineLine F t)).symm
  have hchar_split :
      (n : ℂ) ^ (-(zetaCompletedExplicitFormulaRightAffineLine F t)) =
        ((Real.sqrt n : ℂ))⁻¹ * (n : ℂ) ^ (-centered) :=
    zetaCompletedExplicitFormulaPrimeNatural_rightAffineCharacter_eq_invSqrt_mul_centered
      F hn t
  have hweight :
      ((Λ n / Real.sqrt n : ℝ) : ℂ) =
        ((↗Λ) n : ℂ) * ((Real.sqrt n : ℂ))⁻¹ :=
    zetaCompletedExplicitFormulaPrimeNaturalWeight_complex_eq n
  calc
    ((↗Λ) n /
        (n : ℂ) ^ zetaCompletedExplicitFormulaRightAffineLine F t) *
      zetaCompletedExplicitFormulaPhi f
        (zetaCompletedExplicitFormulaRightCenteredAffineLine F t) =
        (((↗Λ) n : ℂ) *
          ((n : ℂ) ^
            zetaCompletedExplicitFormulaRightAffineLine F t)⁻¹) *
          phi := by
      exact congrArg (fun z : ℂ => z * phi)
        (div_eq_mul_inv ((↗Λ) n : ℂ)
          ((n : ℂ) ^ zetaCompletedExplicitFormulaRightAffineLine F t))
    _ =
        (((↗Λ) n : ℂ) *
          (n : ℂ) ^
            (-(zetaCompletedExplicitFormulaRightAffineLine F t))) *
          phi := by
      exact congrArg
        (fun z : ℂ => (((↗Λ) n : ℂ) * z) * phi)
        hchar_inv
    _ =
        (((↗Λ) n : ℂ) *
          (((Real.sqrt n : ℂ))⁻¹ * (n : ℂ) ^ (-centered))) *
          phi := by
      exact congrArg
        (fun z : ℂ => (((↗Λ) n : ℂ) * z) * phi)
        hchar_split
    _ =
        ((((↗Λ) n : ℂ) * ((Real.sqrt n : ℂ))⁻¹) *
          (n : ℂ) ^ (-centered)) *
          phi := by
      exact congrArg (fun z : ℂ => z * phi)
        (mul_assoc ((↗Λ) n : ℂ) ((Real.sqrt n : ℂ))⁻¹
          ((n : ℂ) ^ (-centered))).symm
    _ =
        (((↗Λ) n : ℂ) * ((Real.sqrt n : ℂ))⁻¹) *
          ((n : ℂ) ^ (-centered) * phi) := by
      exact mul_assoc
        (((↗Λ) n : ℂ) * ((Real.sqrt n : ℂ))⁻¹)
        ((n : ℂ) ^ (-centered))
        phi
    _ =
        ((Λ n / Real.sqrt n : ℝ) : ℂ) *
          ((n : ℂ) ^ (-centered) * phi) := by
      exact congrArg (fun z : ℂ => z * ((n : ℂ) ^ (-centered) * phi))
        hweight.symm

/-- Whole-line integral form of the right-line project-character
normalization. -/
theorem zetaCompletedExplicitFormulaPrimeRightVonMangoldtPositiveMonomial_integral_eq_weight_mul_centeredMellinIntegral
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    {n : ℕ} (hn : n ≠ 0) :
    (∫ t : ℝ,
      ((↗Λ) n /
          (n : ℂ) ^ zetaCompletedExplicitFormulaRightAffineLine F t) *
        zetaCompletedExplicitFormulaPhi f
          (zetaCompletedExplicitFormulaRightCenteredAffineLine F t)) =
      ∫ t : ℝ,
        ((Λ n / Real.sqrt n : ℝ) : ℂ) *
          ((n : ℂ) ^
              (-(zetaCompletedExplicitFormulaRightCenteredAffineLine F t)) *
            zetaCompletedExplicitFormulaPhi f
              (zetaCompletedExplicitFormulaRightCenteredAffineLine F t)) := by
  have hfun :
      (fun t : ℝ =>
        ((↗Λ) n /
            (n : ℂ) ^ zetaCompletedExplicitFormulaRightAffineLine F t) *
          zetaCompletedExplicitFormulaPhi f
            (zetaCompletedExplicitFormulaRightCenteredAffineLine F t)) =
        fun t : ℝ =>
          ((Λ n / Real.sqrt n : ℝ) : ℂ) *
            ((n : ℂ) ^
                (-(zetaCompletedExplicitFormulaRightCenteredAffineLine F t)) *
              zetaCompletedExplicitFormulaPhi f
                (zetaCompletedExplicitFormulaRightCenteredAffineLine F t)) := by
    funext t
    exact
      zetaCompletedExplicitFormulaPrimeRightVonMangoldtPositiveMonomial_eq_weight_mul_centeredMellinIntegrand
        f F hn t
  exact congrArg (fun φ : ℝ → ℂ => ∫ t : ℝ, φ t) hfun

/-- The weighted centered Mellin integral factors as the completed
von-Mangoldt scalar times the centered direct Mellin integral. -/
theorem zetaCompletedExplicitFormula_weightedCenteredMellinIntegral_eq_weight_mul_directVerticalMellinIntegral
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (n : ℕ) :
    (∫ t : ℝ,
      ((Λ n / Real.sqrt n : ℝ) : ℂ) *
        ((n : ℂ) ^
            (-(zetaCompletedExplicitFormulaRightCenteredAffineLine F t)) *
          zetaCompletedExplicitFormulaPhi f
            (zetaCompletedExplicitFormulaRightCenteredAffineLine F t))) =
      ((Λ n / Real.sqrt n : ℝ) : ℂ) *
        zetaCompletedExplicitFormulaDirectVerticalMellinIntegral
          (F.c - (1 / 2 : ℝ))
          (zetaCompletedExplicitFormulaPhi f)
          n := by
  let weight : ℂ := ((Λ n / Real.sqrt n : ℝ) : ℂ)
  let centeredIntegrand : ℝ → ℂ :=
    fun t : ℝ =>
      (n : ℂ) ^
          (-(zetaCompletedExplicitFormulaRightCenteredAffineLine F t)) *
        zetaCompletedExplicitFormulaPhi f
          (zetaCompletedExplicitFormulaRightCenteredAffineLine F t)
  have hfactor :
      (∫ t : ℝ, weight * centeredIntegrand t) =
        weight * ∫ t : ℝ, centeredIntegrand t :=
    MeasureTheory.integral_mul_left weight centeredIntegrand
  have hcenteredIntegral :
      (∫ t : ℝ, centeredIntegrand t) =
        zetaCompletedExplicitFormulaDirectVerticalMellinIntegral
          (F.c - (1 / 2 : ℝ))
          (zetaCompletedExplicitFormulaPhi f)
          n :=
    (zetaCompletedExplicitFormulaDirectVerticalMellinIntegral_eq_rightCenteredPhi_integral
      f F n).symm
  calc
    (∫ t : ℝ,
      ((Λ n / Real.sqrt n : ℝ) : ℂ) *
        ((n : ℂ) ^
            (-(zetaCompletedExplicitFormulaRightCenteredAffineLine F t)) *
          zetaCompletedExplicitFormulaPhi f
            (zetaCompletedExplicitFormulaRightCenteredAffineLine F t))) =
        ∫ t : ℝ, weight * centeredIntegrand t := by
      rfl
    _ =
        weight * ∫ t : ℝ, centeredIntegrand t :=
      hfactor
    _ =
        weight *
          zetaCompletedExplicitFormulaDirectVerticalMellinIntegral
            (F.c - (1 / 2 : ℝ))
            (zetaCompletedExplicitFormulaPhi f)
            n := by
      exact congrArg (fun z : ℂ => weight * z) hcenteredIntegral

/-- The raw project right monomial integral is the completed von-Mangoldt
weight times the centered direct vertical Mellin integral. -/
theorem zetaCompletedExplicitFormulaPrimeRightVonMangoldtPositiveMonomial_integral_eq_weight_mul_directVerticalMellinIntegral
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    {n : ℕ} (hn : n ≠ 0) :
    (∫ t : ℝ,
      ((↗Λ) n /
          (n : ℂ) ^ zetaCompletedExplicitFormulaRightAffineLine F t) *
        zetaCompletedExplicitFormulaPhi f
          (zetaCompletedExplicitFormulaRightCenteredAffineLine F t)) =
      ((Λ n / Real.sqrt n : ℝ) : ℂ) *
        zetaCompletedExplicitFormulaDirectVerticalMellinIntegral
          (F.c - (1 / 2 : ℝ))
          (zetaCompletedExplicitFormulaPhi f)
          n := by
  exact Eq.trans
    (zetaCompletedExplicitFormulaPrimeRightVonMangoldtPositiveMonomial_integral_eq_weight_mul_centeredMellinIntegral
      f F hn)
    (zetaCompletedExplicitFormula_weightedCenteredMellinIntegral_eq_weight_mul_directVerticalMellinIntegral
      f F n)

/-- The raw project right monomial integral is the completed von-Mangoldt
weight times `2π` times the normalized Mellin inverse. -/
theorem zetaCompletedExplicitFormulaPrimeRightVonMangoldtPositiveMonomial_integral_eq_weight_mul_twoPi_smul_directVerticalMellinInv
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    {n : ℕ} (hn : n ≠ 0) :
    (∫ t : ℝ,
      ((↗Λ) n /
          (n : ℂ) ^ zetaCompletedExplicitFormulaRightAffineLine F t) *
        zetaCompletedExplicitFormulaPhi f
          (zetaCompletedExplicitFormulaRightCenteredAffineLine F t)) =
      ((Λ n / Real.sqrt n : ℝ) : ℂ) *
        ((2 * π : ℝ) •
          zetaCompletedExplicitFormulaDirectVerticalMellinInv
            (F.c - (1 / 2 : ℝ))
            (zetaCompletedExplicitFormulaPhi f)
            n) := by
  have hraw :
      (∫ t : ℝ,
        ((↗Λ) n /
            (n : ℂ) ^ zetaCompletedExplicitFormulaRightAffineLine F t) *
          zetaCompletedExplicitFormulaPhi f
            (zetaCompletedExplicitFormulaRightCenteredAffineLine F t)) =
        ((Λ n / Real.sqrt n : ℝ) : ℂ) *
          zetaCompletedExplicitFormulaDirectVerticalMellinIntegral
            (F.c - (1 / 2 : ℝ))
            (zetaCompletedExplicitFormulaPhi f)
            n :=
    zetaCompletedExplicitFormulaPrimeRightVonMangoldtPositiveMonomial_integral_eq_weight_mul_directVerticalMellinIntegral
      f F hn
  have hinv :
      zetaCompletedExplicitFormulaDirectVerticalMellinIntegral
          (F.c - (1 / 2 : ℝ))
          (zetaCompletedExplicitFormulaPhi f)
          n =
        (2 * π : ℝ) •
          zetaCompletedExplicitFormulaDirectVerticalMellinInv
            (F.c - (1 / 2 : ℝ))
            (zetaCompletedExplicitFormulaPhi f)
            n :=
    zetaCompletedExplicitFormulaDirectVerticalMellinIntegral_eq_twoPi_smul_mellinInv
      (F.c - (1 / 2 : ℝ)) (zetaCompletedExplicitFormulaPhi f) n
  exact Eq.trans hraw
    (congrArg
      (fun z : ℂ => ((Λ n / Real.sqrt n : ℝ) : ℂ) * z)
      hinv)

/-- Exact normalized Paley-Wiener inversion sample.

All project character algebra, the `sqrt n` factor, the right/centered line
shift, the von Mangoldt scalar, and the raw `dt` Mellin prefactor have already
been removed before this theorem.  The only analytic content left here is the
canonical inverse-Mellin/Fourier inversion of the completed autocorrelation
transform at the logarithmic natural center.

The proof must come from the canonical Mellin inversion theorem applied to the
logarithmic autocorrelation/time kernel.  In particular, this is not an
equality between the spectral/Laplace value `Phi_f (log n)` and the time value
`zetaCompletedTimeBoundaryValue f (log n)`. -/
theorem zetaCompletedExplicitFormulaDirectVerticalMellinInv_twoPi_smul_eq_twoPi_smul_timeSample_ownerSamplingCore
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) {n : ℕ} (hn : n ≠ 0) :
    (2 * π : ℝ) •
        zetaCompletedExplicitFormulaDirectVerticalMellinInv
          (F.c - (1 / 2 : ℝ))
          (zetaCompletedExplicitFormulaPhi f)
          n =
      (2 * π : ℝ) •
        zetaCompletedTimeBoundaryValue f
          (zetaCompletedExplicitFormulaPrimeNaturalCenter n) := by
  let σ : ℝ := F.c - (1 / 2 : ℝ)
  have hn_pos : 0 < (n : ℝ) :=
    zetaCompletedExplicitFormulaPrimeNaturalCast_pos hn
  have hsample :
      zetaCompletedExplicitFormulaDirectVerticalMellinInv σ
          (zetaCompletedExplicitFormulaPhi f)
          n =
        zetaCompletedTimeBoundaryValue f (Real.log n) :=
    zetaCompletedExplicitFormulaDirectVerticalMellinInv_eq_timeSample
      f σ hn_pos
      (zetaCompletedExplicitFormula_twistedTimeKernel_integrable f σ)
      (zetaCompletedExplicitFormula_twistedTimeKernel_fourier_integrable f σ)
      (zetaCompletedExplicitFormula_twistedTimeKernel_continuousAt
        f σ (Real.log n))
  have hcenter :
      Real.log n = zetaCompletedExplicitFormulaPrimeNaturalCenter n :=
    (zetaCompletedExplicitFormulaPrimeNaturalCenter_eq_log n).symm
  have htime :
      zetaCompletedTimeBoundaryValue f (Real.log n) =
        zetaCompletedTimeBoundaryValue f
          (zetaCompletedExplicitFormulaPrimeNaturalCenter n) :=
    congrArg (fun a : ℝ => zetaCompletedTimeBoundaryValue f a) hcenter
  exact
    congrArg (fun z : ℂ => (2 * π : ℝ) • z)
      (Eq.trans hsample htime)

/-- Unconditional normalized Paley-Wiener inversion sample.

The package-shaped theorem above is retained for existing vertical-channel
call sites, but its proof uses only admissibility of `f`; the Fourier
hypotheses are discharged in `PaleyWienerFourierHypotheses`.  This owner form
is the one used by reflected sampling, where constructing the whole contour
analytic package would be the wrong abstraction. -/
theorem zetaCompletedExplicitFormulaDirectVerticalMellinInv_twoPi_smul_eq_twoPi_smul_timeSample_ownerSamplingCore_unconditional
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    {n : ℕ} (hn : n ≠ 0) :
    (2 * π : ℝ) •
        zetaCompletedExplicitFormulaDirectVerticalMellinInv
          (F.c - (1 / 2 : ℝ))
          (zetaCompletedExplicitFormulaPhi f)
          n =
      (2 * π : ℝ) •
        zetaCompletedTimeBoundaryValue f
          (zetaCompletedExplicitFormulaPrimeNaturalCenter n) := by
  let σ : ℝ := F.c - (1 / 2 : ℝ)
  have hn_pos : 0 < (n : ℝ) :=
    zetaCompletedExplicitFormulaPrimeNaturalCast_pos hn
  have hsample :
      zetaCompletedExplicitFormulaDirectVerticalMellinInv σ
          (zetaCompletedExplicitFormulaPhi f)
          n =
        zetaCompletedTimeBoundaryValue f (Real.log n) :=
    zetaCompletedExplicitFormulaDirectVerticalMellinInv_eq_timeSample
      f σ hn_pos
      (zetaCompletedExplicitFormula_twistedTimeKernel_integrable f σ)
      (zetaCompletedExplicitFormula_twistedTimeKernel_fourier_integrable f σ)
      (zetaCompletedExplicitFormula_twistedTimeKernel_continuousAt
        f σ (Real.log n))
  have hcenter :
      Real.log n = zetaCompletedExplicitFormulaPrimeNaturalCenter n :=
    (zetaCompletedExplicitFormulaPrimeNaturalCenter_eq_log n).symm
  have htime :
      zetaCompletedTimeBoundaryValue f (Real.log n) =
        zetaCompletedTimeBoundaryValue f
          (zetaCompletedExplicitFormulaPrimeNaturalCenter n) :=
    congrArg (fun a : ℝ => zetaCompletedTimeBoundaryValue f a) hcenter
  exact
    congrArg (fun z : ℂ => (2 * π : ℝ) • z)
      (Eq.trans hsample htime)

/-- Exact remaining Paley-Wiener inversion value in unweighted direct-Mellin
form.

This theorem is now only raw-line normalization transport from the normalized
inverse-Mellin/Fourier sample theorem above. -/
theorem zetaCompletedExplicitFormulaDirectVerticalMellinIntegral_eq_twoPi_smul_timeSample_ownerSamplingCore
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) {n : ℕ} (hn : n ≠ 0) :
    zetaCompletedExplicitFormulaDirectVerticalMellinIntegral
        (F.c - (1 / 2 : ℝ))
        (zetaCompletedExplicitFormulaPhi f)
        n =
      (2 * π : ℝ) •
        zetaCompletedTimeBoundaryValue f
          (zetaCompletedExplicitFormulaPrimeNaturalCenter n) := by
  exact Eq.trans
    (zetaCompletedExplicitFormulaDirectVerticalMellinIntegral_eq_twoPi_smul_mellinInv
      (F.c - (1 / 2 : ℝ))
      (zetaCompletedExplicitFormulaPhi f)
      n)
    (zetaCompletedExplicitFormulaDirectVerticalMellinInv_twoPi_smul_eq_twoPi_smul_timeSample_ownerSamplingCore
      f F h hn)

/-- Unconditional direct-Mellin form of the Paley-Wiener sample. -/
theorem zetaCompletedExplicitFormulaDirectVerticalMellinIntegral_eq_twoPi_smul_timeSample_ownerSamplingCore_unconditional
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    {n : ℕ} (hn : n ≠ 0) :
    zetaCompletedExplicitFormulaDirectVerticalMellinIntegral
        (F.c - (1 / 2 : ℝ))
        (zetaCompletedExplicitFormulaPhi f)
        n =
      (2 * π : ℝ) •
        zetaCompletedTimeBoundaryValue f
          (zetaCompletedExplicitFormulaPrimeNaturalCenter n) := by
  exact Eq.trans
    (zetaCompletedExplicitFormulaDirectVerticalMellinIntegral_eq_twoPi_smul_mellinInv
      (F.c - (1 / 2 : ℝ))
      (zetaCompletedExplicitFormulaPhi f)
      n)
    (zetaCompletedExplicitFormulaDirectVerticalMellinInv_twoPi_smul_eq_twoPi_smul_timeSample_ownerSamplingCore_unconditional
      f F hn)

/-- Scalar transport from an unweighted complex value equal to a negative real
sample to the weighted project convention.

This is purely algebraic.  It is separated from the Paley-Wiener inversion
leaf so that the analytic theorem only has to prove the unweighted inverse
Mellin value. -/
theorem zetaCompletedExplicitFormula_realWeight_mul_eq_neg_realWeight_mul_of_eq_neg_real
    (a r : ℝ) (w : ℂ) (hw : w = -(r : ℂ)) :
    (a : ℂ) * w = -((a * r : ℝ) : ℂ) := by
  calc
    (a : ℂ) * w = (a : ℂ) * (-(r : ℂ)) := by
      exact congrArg (fun y : ℂ => (a : ℂ) * y) hw
    _ = -((a : ℂ) * (r : ℂ)) := by
      exact mul_neg (a : ℂ) (r : ℂ)
    _ = -((a * r : ℝ) : ℂ) := by
      exact congrArg Neg.neg (Complex.ofReal_mul a r).symm

/-- Weighted Paley-Wiener inversion value in direct-Mellin form.

All project character algebra, the `sqrt n` factor, and the right/centered
line shift have already been removed before this theorem.  This wrapper
performs only scalar transport from the unweighted analytic inversion theorem
above. -/
theorem zetaCompletedExplicitFormula_weightedDirectVerticalMellinIntegral_eq_timeSample_ownerSamplingCore
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) {n : ℕ} (hn : n ≠ 0) :
    ((Λ n / Real.sqrt n : ℝ) : ℂ) *
        zetaCompletedExplicitFormulaDirectVerticalMellinIntegral
          (F.c - (1 / 2 : ℝ))
          (zetaCompletedExplicitFormulaPhi f)
          n =
      ((Λ n / Real.sqrt n : ℝ) : ℂ) *
        ((2 * π : ℝ) •
          zetaCompletedTimeBoundaryValue f
            (zetaCompletedExplicitFormulaPrimeNaturalCenter n)) := by
  have hdirect :
      zetaCompletedExplicitFormulaDirectVerticalMellinIntegral
          (F.c - (1 / 2 : ℝ))
          (zetaCompletedExplicitFormulaPhi f)
          n =
        (2 * π : ℝ) •
          zetaCompletedTimeBoundaryValue f
            (zetaCompletedExplicitFormulaPrimeNaturalCenter n) := by
    exact
      zetaCompletedExplicitFormulaDirectVerticalMellinIntegral_eq_twoPi_smul_timeSample_ownerSamplingCore
        f F h hn
  exact
    congrArg
      (fun z : ℂ => ((Λ n / Real.sqrt n : ℝ) : ℂ) * z)
      hdirect

/-- Unconditional weighted direct-Mellin Paley-Wiener sample. -/
theorem zetaCompletedExplicitFormula_weightedDirectVerticalMellinIntegral_eq_timeSample_ownerSamplingCore_unconditional
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    {n : ℕ} (hn : n ≠ 0) :
    ((Λ n / Real.sqrt n : ℝ) : ℂ) *
        zetaCompletedExplicitFormulaDirectVerticalMellinIntegral
          (F.c - (1 / 2 : ℝ))
          (zetaCompletedExplicitFormulaPhi f)
          n =
      ((Λ n / Real.sqrt n : ℝ) : ℂ) *
        ((2 * π : ℝ) •
          zetaCompletedTimeBoundaryValue f
            (zetaCompletedExplicitFormulaPrimeNaturalCenter n)) := by
  have hdirect :
      zetaCompletedExplicitFormulaDirectVerticalMellinIntegral
          (F.c - (1 / 2 : ℝ))
          (zetaCompletedExplicitFormulaPhi f)
          n =
        (2 * π : ℝ) •
          zetaCompletedTimeBoundaryValue f
            (zetaCompletedExplicitFormulaPrimeNaturalCenter n) := by
    exact
      zetaCompletedExplicitFormulaDirectVerticalMellinIntegral_eq_twoPi_smul_timeSample_ownerSamplingCore_unconditional
        f F hn
  exact
    congrArg
      (fun z : ℂ => ((Λ n / Real.sqrt n : ℝ) : ℂ) * z)
      hdirect

/-- Project-convention Paley-Wiener sampling theorem for one positive natural
frequency, assembled from the normalized inverse-Mellin sample and the
right-line character normalization.

The analytic inverse-Mellin/Fourier content is owned by
`zetaCompletedExplicitFormulaDirectVerticalMellinInv_twoPi_smul_eq_twoPi_smul_timeSample_ownerSamplingCore`.
This theorem performs the remaining project-coordinate transport:

1. Start from the raw direct-Mellin integral normalization.
2. Perform the explicit change of variables `t = 2 * pi * y`.
3. Track the `1 / (2 * pi)` Mellin prefactor against the raw project `dt`
   integral.
4. Use the character identity for `(n : C) ^ (-(F.c + I*t))`, with `n ≠ 0`.

If this derivation produces an extra scalar, this theorem and its consumers
must be corrected rather than hiding the scalar in the arithmetic layer. -/
theorem zetaCompletedExplicitFormulaPhi_projectRightVonMangoldtMonomial_integral_eq_timeSample_ownerSamplingCore
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) {n : ℕ} (hn : n ≠ 0) :
    (∫ t : ℝ,
      ((↗Λ) n /
          (n : ℂ) ^ zetaCompletedExplicitFormulaRightAffineLine F t) *
        zetaCompletedExplicitFormulaPhi f
          (zetaCompletedExplicitFormulaRightCenteredAffineLine F t)) =
      ((Λ n / Real.sqrt n : ℝ) : ℂ) *
        ((2 * π : ℝ) •
          zetaCompletedTimeBoundaryValue f
            (zetaCompletedExplicitFormulaPrimeNaturalCenter n)) := by
  exact Eq.trans
    (zetaCompletedExplicitFormulaPrimeRightVonMangoldtPositiveMonomial_integral_eq_weight_mul_directVerticalMellinIntegral
      f F hn)
    (zetaCompletedExplicitFormula_weightedDirectVerticalMellinIntegral_eq_timeSample_ownerSamplingCore
      f F h hn)

/-- Unconditional core analytic Paley-Wiener sampling theorem for one positive
natural frequency. -/
theorem zetaCompletedExplicitFormulaPhi_projectRightVonMangoldtMonomial_integral_eq_timeSample_ownerSamplingCore_unconditional
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    {n : ℕ} (hn : n ≠ 0) :
    (∫ t : ℝ,
      ((↗Λ) n /
          (n : ℂ) ^ zetaCompletedExplicitFormulaRightAffineLine F t) *
        zetaCompletedExplicitFormulaPhi f
          (zetaCompletedExplicitFormulaRightCenteredAffineLine F t)) =
      ((Λ n / Real.sqrt n : ℝ) : ℂ) *
        ((2 * π : ℝ) •
          zetaCompletedTimeBoundaryValue f
            (zetaCompletedExplicitFormulaPrimeNaturalCenter n)) := by
  exact Eq.trans
    (zetaCompletedExplicitFormulaPrimeRightVonMangoldtPositiveMonomial_integral_eq_weight_mul_directVerticalMellinIntegral
      f F hn)
    (zetaCompletedExplicitFormula_weightedDirectVerticalMellinIntegral_eq_timeSample_ownerSamplingCore_unconditional
      f F hn)

end ZetaAdmissibleFunction

end
end LFunctions
end Boundary
