import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaExplicitFormulaVerticalChannels.OwnerParts.PrimeNaturalTimeArithmetic
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaExplicitFormulaVerticalChannels.OwnerParts.PrimeLeftReflectedTermKernelAlgebra
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaExplicitFormulaVerticalChannels.OwnerParts.PaleyWienerProjectSampling

/-!
# Fourier wrapper for a single reflected-left von Mangoldt term kernel

This file owns the non-analytic transport from the reflected monomial form to
the named reflected-left term kernel.  The actual reflected
Paley-Wiener/Mellin sampling theorem is not asserted here; callers must supply
that value explicitly.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open Complex
open Filter
open LSeries ArithmeticFunction
open MeasureTheory
open Real
open scoped ArithmeticFunction
open scoped LSeries.notation
open scoped Topology

namespace ZetaAdmissibleFunction

/-- Pointwise algebraic transport from the positive-index reflected monomial
form to the named reflected-left von Mangoldt term kernel. -/
theorem zetaCompletedExplicitFormulaPrimeLeftReflectedPositiveMonomial_eq_termKernel
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    {n : ℕ} (hn : n ≠ 0) (t : ℝ) :
    (-((↗Λ) n /
        (n : ℂ) ^ zetaCompletedExplicitFormulaRightAffineLine F (-t))) *
      zetaCompletedExplicitFormulaPhi f
        (zetaCompletedExplicitFormulaLeftCenteredAffineLine F t) =
      zetaCompletedExplicitFormulaPrimeLeftReflectedTermKernel f F n t := by
  exact
    (zetaCompletedExplicitFormulaPrimeLeftReflectedTermKernel_eq_of_ne_zero
      f F hn t).symm

/-- The reflected positive monomial is the negative of the right-line
denominator paired with the opposite centered test transform.

This is the algebraic target for the reflected Mellin inversion theorem: after
the change of variables on the reflected line, the new analytic content is the
Mellin inversion of `Phi` on the opposite centered line, not another use of
the ordinary right one-sided sampling theorem. -/
theorem zetaCompletedExplicitFormulaPrimeLeftReflectedPositiveMonomial_eq_neg_rightOppositeCentered
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (n : ℕ) (t : ℝ) :
    (-((↗Λ) n /
        (n : ℂ) ^ zetaCompletedExplicitFormulaRightAffineLine F (-t))) *
      zetaCompletedExplicitFormulaPhi f
        (zetaCompletedExplicitFormulaLeftCenteredAffineLine F t) =
      -(((↗Λ) n /
          (n : ℂ) ^ zetaCompletedExplicitFormulaRightAffineLine F (-t)) *
        zetaCompletedExplicitFormulaPhi f
          (-(zetaCompletedExplicitFormulaRightCenteredAffineLine F (-t)))) := by
  let A : ℂ :=
    (↗Λ) n /
      (n : ℂ) ^ zetaCompletedExplicitFormulaRightAffineLine F (-t)
  let ΦL : ℂ :=
    zetaCompletedExplicitFormulaPhi f
      (zetaCompletedExplicitFormulaLeftCenteredAffineLine F t)
  let ΦR : ℂ :=
    zetaCompletedExplicitFormulaPhi f
      (-(zetaCompletedExplicitFormulaRightCenteredAffineLine F (-t)))
  have hline :
      zetaCompletedExplicitFormulaPhi f
        (zetaCompletedExplicitFormulaLeftCenteredAffineLine F t) =
      zetaCompletedExplicitFormulaPhi f
        (-(zetaCompletedExplicitFormulaRightCenteredAffineLine F (-t))) :=
    congrArg
      (fun z : ℂ => zetaCompletedExplicitFormulaPhi f z)
      (zetaCompletedExplicitFormulaLeftCenteredAffineLine_eq_neg_rightCenteredAffineLine
        F t)
  have hmul :
      (-A) * ΦR = -(A * ΦR) := by
    exact neg_mul A ΦR
  calc
    (-((↗Λ) n /
        (n : ℂ) ^ zetaCompletedExplicitFormulaRightAffineLine F (-t))) *
      zetaCompletedExplicitFormulaPhi f
        (zetaCompletedExplicitFormulaLeftCenteredAffineLine F t) =
        (-A) * ΦL := by
      rfl
    _ = (-A) * ΦR := by
      exact congrArg (fun z : ℂ => (-A) * z) hline
    _ = -(A * ΦR) := by
      exact hmul
    _ =
      -(((↗Λ) n /
          (n : ℂ) ^ zetaCompletedExplicitFormulaRightAffineLine F (-t)) *
        zetaCompletedExplicitFormulaPhi f
          (-(zetaCompletedExplicitFormulaRightCenteredAffineLine F (-t)))) := by
      rfl

/-- Whole-line integral form of the reflected-positive-monomial reduction to
the opposite centered Mellin integrand. -/
theorem zetaCompletedExplicitFormulaPrimeLeftReflectedPositiveMonomial_integral_eq_neg_rightOppositeCenteredIntegral
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (n : ℕ) :
    (∫ t : ℝ,
      (-((↗Λ) n /
          (n : ℂ) ^ zetaCompletedExplicitFormulaRightAffineLine F (-t))) *
        zetaCompletedExplicitFormulaPhi f
          (zetaCompletedExplicitFormulaLeftCenteredAffineLine F t)) =
      ∫ t : ℝ,
        -(((↗Λ) n /
            (n : ℂ) ^ zetaCompletedExplicitFormulaRightAffineLine F (-t)) *
          zetaCompletedExplicitFormulaPhi f
            (-(zetaCompletedExplicitFormulaRightCenteredAffineLine F (-t)))) := by
  have hfun :
      (fun t : ℝ =>
        (-((↗Λ) n /
            (n : ℂ) ^ zetaCompletedExplicitFormulaRightAffineLine F (-t))) *
          zetaCompletedExplicitFormulaPhi f
            (zetaCompletedExplicitFormulaLeftCenteredAffineLine F t)) =
      fun t : ℝ =>
        -(((↗Λ) n /
            (n : ℂ) ^ zetaCompletedExplicitFormulaRightAffineLine F (-t)) *
          zetaCompletedExplicitFormulaPhi f
            (-(zetaCompletedExplicitFormulaRightCenteredAffineLine F (-t)))) := by
    funext t
    exact
      zetaCompletedExplicitFormulaPrimeLeftReflectedPositiveMonomial_eq_neg_rightOppositeCentered
        f F n t
  exact congrArg (fun φ : ℝ → ℂ => ∫ t : ℝ, φ t) hfun

/-- The reflected positive monomial integral is the negative of the named
opposite-centered raw transform integral. -/
theorem zetaCompletedExplicitFormulaPrimeLeftReflectedPositiveMonomial_integral_eq_neg_oppositeRawIntegral
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (n : ℕ) :
    (∫ t : ℝ,
      (-((↗Λ) n /
          (n : ℂ) ^ zetaCompletedExplicitFormulaRightAffineLine F (-t))) *
        zetaCompletedExplicitFormulaPhi f
          (zetaCompletedExplicitFormulaLeftCenteredAffineLine F t)) =
      -(zetaCompletedExplicitFormulaPhi_projectRightVonMangoldtOppositeRawIntegral
          f F n) := by
  let ψ : ℝ → ℂ := fun t : ℝ =>
    ((↗Λ) n /
        (n : ℂ) ^ zetaCompletedExplicitFormulaRightAffineLine F (-t)) *
      zetaCompletedExplicitFormulaPhi f
        (-(zetaCompletedExplicitFormulaRightCenteredAffineLine F (-t)))
  have hraw :
      zetaCompletedExplicitFormulaPhi_projectRightVonMangoldtOppositeRawIntegral
          f F n =
        ∫ t : ℝ, ψ t := by
    exact
      zetaCompletedExplicitFormulaPhi_projectRightVonMangoldtOppositeRawIntegral_eq
        f F n
  have hneg :
      (∫ t : ℝ, -ψ t) =
        -(∫ t : ℝ, ψ t) := by
    exact integral_neg ψ
  calc
    (∫ t : ℝ,
      (-((↗Λ) n /
          (n : ℂ) ^ zetaCompletedExplicitFormulaRightAffineLine F (-t))) *
        zetaCompletedExplicitFormulaPhi f
          (zetaCompletedExplicitFormulaLeftCenteredAffineLine F t)) =
        ∫ t : ℝ, -ψ t := by
      exact
        zetaCompletedExplicitFormulaPrimeLeftReflectedPositiveMonomial_integral_eq_neg_rightOppositeCenteredIntegral
          f F n
    _ = -(∫ t : ℝ, ψ t) := by
      exact hneg
    _ =
        -(zetaCompletedExplicitFormulaPhi_projectRightVonMangoldtOppositeRawIntegral
          f F n) := by
      exact congrArg Neg.neg hraw.symm

/-- Positive-index reflected-left monomial sampling, reduced to the reflected
time-boundary value at the opposite logarithmic center. -/
theorem zetaCompletedExplicitFormulaPrimeLeftReflectedPositiveMonomial_integral_eq_neg_reflectTimeBoundarySample
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    {n : ℕ} (hn : n ≠ 0) :
    (∫ t : ℝ,
      (-((↗Λ) n /
          (n : ℂ) ^ zetaCompletedExplicitFormulaRightAffineLine F (-t))) *
        zetaCompletedExplicitFormulaPhi f
          (zetaCompletedExplicitFormulaLeftCenteredAffineLine F t)) =
      -(((Λ n / Real.sqrt n : ℝ) : ℂ) *
        ((2 * Real.pi : ℝ) •
          zetaCompletedTimeBoundaryValue f
            (-(zetaCompletedExplicitFormulaPrimeNaturalCenter n)))) := by
  exact
    Eq.trans
      (zetaCompletedExplicitFormulaPrimeLeftReflectedPositiveMonomial_integral_eq_neg_oppositeRawIntegral
        f F n)
      (congrArg Neg.neg
        (zetaCompletedExplicitFormulaPhi_projectRightVonMangoldtOppositeRawIntegral_eq_reflectTimeBoundarySample
          f F hn))

/-- Positive-index reflected-left monomial sampling, reduced to the named
reflected natural boundary sample. -/
theorem zetaCompletedExplicitFormulaPrimeLeftReflectedPositiveMonomial_integral_eq_neg_reflectedTimeBoundarySample
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    {n : ℕ} (hn : n ≠ 0) :
    (∫ t : ℝ,
      (-((↗Λ) n /
          (n : ℂ) ^ zetaCompletedExplicitFormulaRightAffineLine F (-t))) *
        zetaCompletedExplicitFormulaPhi f
          (zetaCompletedExplicitFormulaLeftCenteredAffineLine F t)) =
      -(zetaCompletedExplicitFormulaPrimeNaturalReflectedTimeBoundarySample
        f n) := by
  exact
    Eq.trans
      (zetaCompletedExplicitFormulaPrimeLeftReflectedPositiveMonomial_integral_eq_neg_oppositeRawIntegral
        f F n)
      (congrArg Neg.neg
        (zetaCompletedExplicitFormulaPhi_projectRightVonMangoldtOppositeRawIntegral_eq_reflectedTimeBoundarySample
          f F hn))

/-- Whole-line integral transport from the positive-index reflected monomial
form to the named reflected-left von Mangoldt term kernel. -/
theorem zetaCompletedExplicitFormulaPrimeLeftReflectedPositiveMonomial_integral_eq_termKernel_integral
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    {n : ℕ} (hn : n ≠ 0) :
    (∫ t : ℝ,
      (-((↗Λ) n /
          (n : ℂ) ^ zetaCompletedExplicitFormulaRightAffineLine F (-t))) *
        zetaCompletedExplicitFormulaPhi f
          (zetaCompletedExplicitFormulaLeftCenteredAffineLine F t)) =
      ∫ t : ℝ,
        zetaCompletedExplicitFormulaPrimeLeftReflectedTermKernel f F n t := by
  have hfun :
      (fun t : ℝ =>
        (-((↗Λ) n /
            (n : ℂ) ^ zetaCompletedExplicitFormulaRightAffineLine F (-t))) *
          zetaCompletedExplicitFormulaPhi f
            (zetaCompletedExplicitFormulaLeftCenteredAffineLine F t)) =
        fun t : ℝ =>
          zetaCompletedExplicitFormulaPrimeLeftReflectedTermKernel f F n t := by
    funext t
    exact
      zetaCompletedExplicitFormulaPrimeLeftReflectedPositiveMonomial_eq_termKernel
        f F hn t
  exact congrArg (fun φ : ℝ → ℂ => ∫ t : ℝ, φ t) hfun

/-- Positive-index named reflected-left term-kernel sampling, reduced to the
reflected time-boundary value at the opposite logarithmic center. -/
theorem zetaCompletedExplicitFormulaPrimeLeftReflectedTermKernel_integral_eq_neg_reflectTimeBoundarySample
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    {n : ℕ} (hn : n ≠ 0) :
    (∫ t : ℝ,
      zetaCompletedExplicitFormulaPrimeLeftReflectedTermKernel f F n t) =
      -(((Λ n / Real.sqrt n : ℝ) : ℂ) *
        ((2 * Real.pi : ℝ) •
          zetaCompletedTimeBoundaryValue f
            (-(zetaCompletedExplicitFormulaPrimeNaturalCenter n)))) := by
  exact
    Eq.trans
      (zetaCompletedExplicitFormulaPrimeLeftReflectedPositiveMonomial_integral_eq_termKernel_integral
        f F hn).symm
      (zetaCompletedExplicitFormulaPrimeLeftReflectedPositiveMonomial_integral_eq_neg_reflectTimeBoundarySample
        f F hn)

/-- Positive-index named reflected-left term-kernel sampling, reduced to the
named reflected natural boundary sample. -/
theorem zetaCompletedExplicitFormulaPrimeLeftReflectedTermKernel_integral_eq_neg_reflectedTimeBoundarySample
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    {n : ℕ} (hn : n ≠ 0) :
    (∫ t : ℝ,
      zetaCompletedExplicitFormulaPrimeLeftReflectedTermKernel f F n t) =
      -(zetaCompletedExplicitFormulaPrimeNaturalReflectedTimeBoundarySample
        f n) := by
  exact
    Eq.trans
      (zetaCompletedExplicitFormulaPrimeLeftReflectedPositiveMonomial_integral_eq_termKernel_integral
        f F hn).symm
      (zetaCompletedExplicitFormulaPrimeLeftReflectedPositiveMonomial_integral_eq_neg_reflectedTimeBoundarySample
        f F hn)

/-- The zeroth reflected term kernel has the negative reflected boundary
sample value. -/
theorem zetaCompletedExplicitFormulaPrimeLeftReflectedTermKernel_integral_eq_neg_reflectedTimeBoundarySample_zero
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily) :
    (∫ t : ℝ,
      zetaCompletedExplicitFormulaPrimeLeftReflectedTermKernel f F 0 t) =
      -(zetaCompletedExplicitFormulaPrimeNaturalReflectedTimeBoundarySample
        f 0) := by
  calc
    (∫ t : ℝ,
      zetaCompletedExplicitFormulaPrimeLeftReflectedTermKernel f F 0 t) =
        0 := by
      exact
        zetaCompletedExplicitFormulaPrimeLeftReflectedTermKernel_integral_zero
          f F
    _ =
        -(zetaCompletedExplicitFormulaPrimeNaturalReflectedTimeBoundarySample
          f 0) := by
      have hzero :
          zetaCompletedExplicitFormulaPrimeNaturalReflectedTimeBoundarySample
            f 0 = 0 :=
        zetaCompletedExplicitFormulaPrimeNaturalReflectedTimeBoundarySample_zero
          f
      have hnegZero :
          (0 : ℂ) = -(0 : ℂ) :=
        (neg_zero : -(0 : ℂ) = 0).symm
      have hnegSample :
          -(0 : ℂ) =
            -(zetaCompletedExplicitFormulaPrimeNaturalReflectedTimeBoundarySample
              f 0) :=
        congrArg Neg.neg hzero.symm
      exact
        Eq.trans hnegZero hnegSample

/-- Reflected-left term-kernel sampling to the negative reflected boundary
sample over all natural indices. -/
theorem zetaCompletedExplicitFormulaPrimeLeftReflectedTermKernel_integral_eq_neg_reflectedTimeBoundarySample_all
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (n : ℕ) :
    (∫ t : ℝ,
      zetaCompletedExplicitFormulaPrimeLeftReflectedTermKernel f F n t) =
      -(zetaCompletedExplicitFormulaPrimeNaturalReflectedTimeBoundarySample
        f n) := by
  by_cases hn : n = 0
  · exact
      Eq.subst
        (motive := fun m : ℕ =>
          (∫ t : ℝ,
            zetaCompletedExplicitFormulaPrimeLeftReflectedTermKernel
              f F m t) =
            -(zetaCompletedExplicitFormulaPrimeNaturalReflectedTimeBoundarySample
              f m))
        hn.symm
        (zetaCompletedExplicitFormulaPrimeLeftReflectedTermKernel_integral_eq_neg_reflectedTimeBoundarySample_zero
          f F)
  · exact
      zetaCompletedExplicitFormulaPrimeLeftReflectedTermKernel_integral_eq_neg_reflectedTimeBoundarySample
        f F hn

/-- Reflected-left term-kernel sampling summed to the negative reflected
boundary contribution. -/
theorem zetaCompletedExplicitFormulaPrimeLeftReflectedTermKernel_integrals_tsum_eq_neg_reflectedBoundaryContribution
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily) :
    (∑' n : ℕ,
      ∫ t : ℝ,
        zetaCompletedExplicitFormulaPrimeLeftReflectedTermKernel f F n t) =
      -(zetaCompletedExplicitFormulaPrimeNaturalReflectedBoundaryContribution
        f) := by
  have hterm :
      (∑' n : ℕ,
        ∫ t : ℝ,
          zetaCompletedExplicitFormulaPrimeLeftReflectedTermKernel f F n t) =
        ∑' n : ℕ,
          -(zetaCompletedExplicitFormulaPrimeNaturalReflectedTimeBoundarySample
            f n) :=
    tsum_congr
      (fun n : ℕ =>
        zetaCompletedExplicitFormulaPrimeLeftReflectedTermKernel_integral_eq_neg_reflectedTimeBoundarySample_all
          f F n)
  have hneg :
      (∑' n : ℕ,
        -(zetaCompletedExplicitFormulaPrimeNaturalReflectedTimeBoundarySample
          f n)) =
        -(∑' n : ℕ,
          zetaCompletedExplicitFormulaPrimeNaturalReflectedTimeBoundarySample
            f n) :=
    tsum_neg
  calc
    (∑' n : ℕ,
      ∫ t : ℝ,
        zetaCompletedExplicitFormulaPrimeLeftReflectedTermKernel f F n t) =
        ∑' n : ℕ,
          -(zetaCompletedExplicitFormulaPrimeNaturalReflectedTimeBoundarySample
            f n) := by
      exact hterm
    _ =
        -(∑' n : ℕ,
          zetaCompletedExplicitFormulaPrimeNaturalReflectedTimeBoundarySample
            f n) := by
      exact hneg
    _ =
        -(zetaCompletedExplicitFormulaPrimeNaturalReflectedBoundaryContribution
          f) := by
      exact congrArg Neg.neg
        (zetaCompletedExplicitFormulaPrimeNaturalReflectedBoundaryContribution_eq_tsum
          f).symm

/-- Reflected-left term-kernel sampling summed to the negative complementary
contribution, from a pointwise reflected/complement normalization. -/
theorem zetaCompletedExplicitFormulaPrimeLeftReflectedTermKernel_integrals_tsum_eq_neg_complementContribution_of_reflected_eq_complement
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (hreflected :
      ∀ n : ℕ,
        zetaCompletedExplicitFormulaPrimeNaturalReflectedTimeBoundarySample
          f n =
        zetaCompletedExplicitFormulaPrimeNaturalComplementTimeSample f n) :
    (∑' n : ℕ,
      ∫ t : ℝ,
        zetaCompletedExplicitFormulaPrimeLeftReflectedTermKernel f F n t) =
      -(zetaCompletedExplicitFormulaPrimeNaturalComplementContribution f) := by
  have hterm :
      (∑' n : ℕ,
        ∫ t : ℝ,
          zetaCompletedExplicitFormulaPrimeLeftReflectedTermKernel f F n t) =
        -(zetaCompletedExplicitFormulaPrimeNaturalReflectedBoundaryContribution
          f) :=
    zetaCompletedExplicitFormulaPrimeLeftReflectedTermKernel_integrals_tsum_eq_neg_reflectedBoundaryContribution
      f F
  have hcontribution :
      zetaCompletedExplicitFormulaPrimeNaturalReflectedBoundaryContribution f =
        zetaCompletedExplicitFormulaPrimeNaturalComplementContribution f :=
    zetaCompletedExplicitFormulaPrimeNaturalReflectedBoundaryContribution_eq_complementContribution_of_reflected_eq_complement
      f hreflected
  calc
    (∑' n : ℕ,
      ∫ t : ℝ,
        zetaCompletedExplicitFormulaPrimeLeftReflectedTermKernel f F n t) =
        -(zetaCompletedExplicitFormulaPrimeNaturalReflectedBoundaryContribution
          f) := by
      exact hterm
    _ = -(zetaCompletedExplicitFormulaPrimeNaturalComplementContribution f) := by
      exact congrArg Neg.neg hcontribution

/-- Reflected-left term-kernel sampling summed to the negative complementary
contribution, from the pointwise two-face decomposition. -/
theorem zetaCompletedExplicitFormulaPrimeLeftReflectedTermKernel_integrals_tsum_eq_neg_complementContribution_of_timeSummand_eq_twoFace
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (hsplit :
      ∀ n : ℕ,
        zetaCompletedExplicitFormulaPrimeNaturalTimeSummand f n =
          zetaCompletedExplicitFormulaPrimeNaturalTwoFaceBoundarySample f n) :
    (∑' n : ℕ,
      ∫ t : ℝ,
        zetaCompletedExplicitFormulaPrimeLeftReflectedTermKernel f F n t) =
      -(zetaCompletedExplicitFormulaPrimeNaturalComplementContribution f) := by
  exact
    zetaCompletedExplicitFormulaPrimeLeftReflectedTermKernel_integrals_tsum_eq_neg_complementContribution_of_reflected_eq_complement
      f F
      (fun n : ℕ =>
        zetaCompletedExplicitFormulaPrimeNaturalReflectedTimeBoundarySample_eq_complementTimeSample_of_timeSummand_eq_twoFace
          f n (hsplit n))

/-- If the reflected natural boundary sample is identified with the
complementary natural prime sample, then the reflected-left term kernel has
the required positive-index complement value.

This wrapper is intentionally one theorem below the arithmetic normalization:
it performs only the analytic transport already proved in this file plus a
single named time-side equality. -/
theorem zetaCompletedExplicitFormulaPrimeLeftReflectedTermKernel_integral_eq_neg_complementTimeSample_of_reflectedTimeBoundarySample_eq
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    {n : ℕ} (hn : n ≠ 0)
    (hreflected :
      zetaCompletedExplicitFormulaPrimeNaturalReflectedTimeBoundarySample f n =
        zetaCompletedExplicitFormulaPrimeNaturalComplementTimeSample f n) :
    (∫ t : ℝ,
      zetaCompletedExplicitFormulaPrimeLeftReflectedTermKernel f F n t) =
      -(zetaCompletedExplicitFormulaPrimeNaturalComplementTimeSample f n) := by
  exact
    Eq.trans
      (zetaCompletedExplicitFormulaPrimeLeftReflectedTermKernel_integral_eq_neg_reflectedTimeBoundarySample
        f F hn)
      (congrArg Neg.neg hreflected)

/-- Positive-index reflected-left term-kernel complement value from the
two-face decomposition of the symmetric natural summand. -/
theorem zetaCompletedExplicitFormulaPrimeLeftReflectedTermKernel_integral_eq_neg_complementTimeSample_of_timeSummand_eq_oneSided_add_reflected
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    {n : ℕ} (hn : n ≠ 0)
    (hsplit :
      zetaCompletedExplicitFormulaPrimeNaturalTimeSummand f n =
        zetaCompletedExplicitFormulaPrimeNaturalOneSidedTimeSample f n +
          zetaCompletedExplicitFormulaPrimeNaturalReflectedTimeBoundarySample
            f n) :
    (∫ t : ℝ,
      zetaCompletedExplicitFormulaPrimeLeftReflectedTermKernel f F n t) =
      -(zetaCompletedExplicitFormulaPrimeNaturalComplementTimeSample f n) := by
  exact
    zetaCompletedExplicitFormulaPrimeLeftReflectedTermKernel_integral_eq_neg_complementTimeSample_of_reflectedTimeBoundarySample_eq
      f F hn
      (zetaCompletedExplicitFormulaPrimeNaturalReflectedTimeBoundarySample_eq_complementTimeSample_of_timeSummand_eq_oneSided_add_reflected
        f n hsplit)

/-- Positive-index reflected-left term-kernel complement value from the named
two-face decomposition of the symmetric natural summand. -/
theorem zetaCompletedExplicitFormulaPrimeLeftReflectedTermKernel_integral_eq_neg_complementTimeSample_of_timeSummand_eq_twoFace
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    {n : ℕ} (hn : n ≠ 0)
    (hsplit :
      zetaCompletedExplicitFormulaPrimeNaturalTimeSummand f n =
        zetaCompletedExplicitFormulaPrimeNaturalTwoFaceBoundarySample f n) :
    (∫ t : ℝ,
      zetaCompletedExplicitFormulaPrimeLeftReflectedTermKernel f F n t) =
      -(zetaCompletedExplicitFormulaPrimeNaturalComplementTimeSample f n) := by
  exact
    zetaCompletedExplicitFormulaPrimeLeftReflectedTermKernel_integral_eq_neg_complementTimeSample_of_reflectedTimeBoundarySample_eq
      f F hn
      (zetaCompletedExplicitFormulaPrimeNaturalReflectedTimeBoundarySample_eq_complementTimeSample_of_timeSummand_eq_twoFace
        f n hsplit)

/-- Assembly form of the reflected positive-index Fourier/Mellin sampling
leaf: once the named reflected term kernel has been inverted, the original
reflected monomial form follows by definitional algebra. -/
theorem zetaCompletedExplicitFormulaPrimeLeftReflectedPositiveMonomial_integral_eq_complementTimeSample_of_termKernel_integral_eq
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    {n : ℕ} (hn : n ≠ 0)
    (hterm :
      (∫ t : ℝ,
        zetaCompletedExplicitFormulaPrimeLeftReflectedTermKernel f F n t) =
        -(zetaCompletedExplicitFormulaPrimeNaturalComplementTimeSample f n)) :
    (∫ t : ℝ,
      (-((↗Λ) n /
          (n : ℂ) ^ zetaCompletedExplicitFormulaRightAffineLine F (-t))) *
        zetaCompletedExplicitFormulaPhi f
          (zetaCompletedExplicitFormulaLeftCenteredAffineLine F t)) =
      -(zetaCompletedExplicitFormulaPrimeNaturalComplementTimeSample f n) := by
  exact
    Eq.trans
      (zetaCompletedExplicitFormulaPrimeLeftReflectedPositiveMonomial_integral_eq_termKernel_integral
        f F hn)
      hterm

/-- The zeroth reflected term kernel has the correct negative-complement
sample value. -/
theorem zetaCompletedExplicitFormulaPrimeLeftReflectedTermKernel_integral_eq_neg_complementTimeSample_zero
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily) :
    (∫ t : ℝ,
      zetaCompletedExplicitFormulaPrimeLeftReflectedTermKernel f F 0 t) =
      -(zetaCompletedExplicitFormulaPrimeNaturalComplementTimeSample f 0) := by
  calc
    (∫ t : ℝ,
      zetaCompletedExplicitFormulaPrimeLeftReflectedTermKernel f F 0 t) =
        0 := by
      exact zetaCompletedExplicitFormulaPrimeLeftReflectedTermKernel_integral_zero
        f F
    _ = -(zetaCompletedExplicitFormulaPrimeNaturalComplementTimeSample f 0) := by
      exact
        (zetaCompletedExplicitFormulaPrimeNatural_neg_complementTimeSample_zero
          f).symm

/-- Termwise reflected Mellin inversion over all natural indices from the
positive-index analytic reflected sampling theorem.

The positive-index hypothesis is the real analytic input.  This wrapper owns
only the zero-index case split. -/
theorem zetaCompletedExplicitFormulaPrimeLeftReflectedTermKernel_integral_eq_neg_complementTimeSample_of_pos
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (hpos :
      ∀ n : ℕ, n ≠ 0 →
        (∫ t : ℝ,
          zetaCompletedExplicitFormulaPrimeLeftReflectedTermKernel f F n t) =
          -(zetaCompletedExplicitFormulaPrimeNaturalComplementTimeSample f n))
    (n : ℕ) :
    (∫ t : ℝ,
      zetaCompletedExplicitFormulaPrimeLeftReflectedTermKernel f F n t) =
      -(zetaCompletedExplicitFormulaPrimeNaturalComplementTimeSample f n) := by
  by_cases hn : n = 0
  · exact
      Eq.subst
        (motive := fun m : ℕ =>
          (∫ t : ℝ,
            zetaCompletedExplicitFormulaPrimeLeftReflectedTermKernel f F m t) =
            -(zetaCompletedExplicitFormulaPrimeNaturalComplementTimeSample f m))
        hn.symm
        (zetaCompletedExplicitFormulaPrimeLeftReflectedTermKernel_integral_eq_neg_complementTimeSample_zero
          f F)
  · exact hpos n hn

/-- Termwise reflected Mellin inversion summed over natural indices.

This is the reflected analogue of the right von-Mangoldt `tsum_congr` wrapper:
it changes equal summands under `tsum` and does not assert any sum-integral
exchange or completed-kernel expansion. -/
theorem zetaCompletedExplicitFormulaPrimeLeftReflectedTermKernel_integrals_tsum_eq_neg_complementTimeTsum_of_pos
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (hpos :
      ∀ n : ℕ, n ≠ 0 →
        (∫ t : ℝ,
          zetaCompletedExplicitFormulaPrimeLeftReflectedTermKernel f F n t) =
          -(zetaCompletedExplicitFormulaPrimeNaturalComplementTimeSample f n)) :
    (∑' n : ℕ,
      ∫ t : ℝ,
        zetaCompletedExplicitFormulaPrimeLeftReflectedTermKernel f F n t) =
      ∑' n : ℕ,
        -(zetaCompletedExplicitFormulaPrimeNaturalComplementTimeSample f n) := by
  exact
    tsum_congr
      (fun n : ℕ =>
        zetaCompletedExplicitFormulaPrimeLeftReflectedTermKernel_integral_eq_neg_complementTimeSample_of_pos
          f F hpos n)

/-- Reflected termwise Mellin inversion summed to the negative complementary
natural contribution, once the complementary time samples have themselves
been normalized as a `tsum`.

The two inputs are the genuine analytic/summability obligations:
positive-index reflected Mellin inversion and the natural complement `tsum`
normalization.  This theorem owns only the final `tsum` sign transport. -/
theorem zetaCompletedExplicitFormulaPrimeLeftReflectedTermKernel_integrals_tsum_eq_neg_complementContribution_of_pos_and_complement_tsum
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (hpos :
      ∀ n : ℕ, n ≠ 0 →
        (∫ t : ℝ,
          zetaCompletedExplicitFormulaPrimeLeftReflectedTermKernel f F n t) =
          -(zetaCompletedExplicitFormulaPrimeNaturalComplementTimeSample f n))
    (hcomplement_tsum :
      (∑' n : ℕ,
        zetaCompletedExplicitFormulaPrimeNaturalComplementTimeSample f n) =
        zetaCompletedExplicitFormulaPrimeNaturalComplementContribution f) :
    (∑' n : ℕ,
      ∫ t : ℝ,
        zetaCompletedExplicitFormulaPrimeLeftReflectedTermKernel f F n t) =
      -(zetaCompletedExplicitFormulaPrimeNaturalComplementContribution f) := by
  have hterm_tsum :
      (∑' n : ℕ,
        ∫ t : ℝ,
          zetaCompletedExplicitFormulaPrimeLeftReflectedTermKernel f F n t) =
        ∑' n : ℕ,
          -(zetaCompletedExplicitFormulaPrimeNaturalComplementTimeSample f n) :=
    zetaCompletedExplicitFormulaPrimeLeftReflectedTermKernel_integrals_tsum_eq_neg_complementTimeTsum_of_pos
      f F hpos
  have hneg_tsum :
      (∑' n : ℕ,
        -(zetaCompletedExplicitFormulaPrimeNaturalComplementTimeSample f n)) =
        -(∑' n : ℕ,
          zetaCompletedExplicitFormulaPrimeNaturalComplementTimeSample f n) :=
    tsum_neg
  calc
    (∑' n : ℕ,
      ∫ t : ℝ,
        zetaCompletedExplicitFormulaPrimeLeftReflectedTermKernel f F n t) =
        ∑' n : ℕ,
          -(zetaCompletedExplicitFormulaPrimeNaturalComplementTimeSample f n) := by
      exact hterm_tsum
    _ = -(∑' n : ℕ,
          zetaCompletedExplicitFormulaPrimeNaturalComplementTimeSample f n) := by
      exact hneg_tsum
    _ = -(zetaCompletedExplicitFormulaPrimeNaturalComplementContribution f) := by
      exact congrArg Neg.neg hcomplement_tsum

/-- Reflected termwise Mellin inversion summed to the negative complementary
natural contribution, with the complementary `tsum` normalization discharged
from summability of the two natural prime series. -/
theorem zetaCompletedExplicitFormulaPrimeLeftReflectedTermKernel_integrals_tsum_eq_neg_complementContribution_of_pos_and_summable
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (hpos :
      ∀ n : ℕ, n ≠ 0 →
        (∫ t : ℝ,
          zetaCompletedExplicitFormulaPrimeLeftReflectedTermKernel f F n t) =
          -(zetaCompletedExplicitFormulaPrimeNaturalComplementTimeSample f n))
    (hsymmetric :
      Summable
        (fun n : ℕ =>
          zetaCompletedExplicitFormulaPrimeNaturalTimeSummand f n))
    (honeSided :
      Summable
        (fun n : ℕ =>
          zetaCompletedExplicitFormulaPrimeNaturalOneSidedTimeSample f n)) :
    (∑' n : ℕ,
      ∫ t : ℝ,
        zetaCompletedExplicitFormulaPrimeLeftReflectedTermKernel f F n t) =
      -(zetaCompletedExplicitFormulaPrimeNaturalComplementContribution f) := by
  exact
    zetaCompletedExplicitFormulaPrimeLeftReflectedTermKernel_integrals_tsum_eq_neg_complementContribution_of_pos_and_complement_tsum
      f F hpos
      (zetaCompletedExplicitFormulaPrimeNaturalComplementTimeSample_tsum_eq_contribution_of_summable
        f hsymmetric honeSided)

/-- Reflected termwise Mellin inversion summed to the negative complementary
natural contribution, with the natural-prime summability facts supplied by the
arithmetic owner file.

After this wrapper, the only remaining input is the genuine positive-index
reflected Mellin inversion theorem. -/
theorem zetaCompletedExplicitFormulaPrimeLeftReflectedTermKernel_integrals_tsum_eq_neg_complementContribution_of_pos
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (hpos :
      ∀ n : ℕ, n ≠ 0 →
        (∫ t : ℝ,
          zetaCompletedExplicitFormulaPrimeLeftReflectedTermKernel f F n t) =
          -(zetaCompletedExplicitFormulaPrimeNaturalComplementTimeSample f n)) :
    (∑' n : ℕ,
      ∫ t : ℝ,
        zetaCompletedExplicitFormulaPrimeLeftReflectedTermKernel f F n t) =
      -(zetaCompletedExplicitFormulaPrimeNaturalComplementContribution f) := by
  exact
    zetaCompletedExplicitFormulaPrimeLeftReflectedTermKernel_integrals_tsum_eq_neg_complementContribution_of_pos_and_summable
      f F hpos
      (zetaCompletedExplicitFormulaPrimeNaturalTimeSummand_summable f)
      (zetaCompletedExplicitFormulaPrimeNaturalOneSidedTimeSample_summable f)

end ZetaAdmissibleFunction

end
end LFunctions
end Boundary
