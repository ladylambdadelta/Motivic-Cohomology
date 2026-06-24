import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaExplicitFormulaVerticalChannels.OwnerParts.PrimeNaturalTimeArithmetic
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaExplicitFormulaVerticalChannels.OwnerParts.PrimeRightTermKernelAlgebra
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaExplicitFormulaVerticalChannels.OwnerParts.PaleyWienerProjectSamplingCore

/-!
# Project-convention Paley-Wiener sampling

This file owns the Fourier/Mellin sampling theorem for one positive natural
frequency in the completed explicit-formula normalization.  Arithmetic
normalization and term-kernel algebra live downstream.
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

/-- The raw project-convention right-line monomial integral for a positive
natural Dirichlet frequency.

This is intentionally unnormalized: it is the `dt`-line integral used by the
vertical-channel prime branch, not mathlib's normalized `mellinInv`. -/
noncomputable def zetaCompletedExplicitFormulaPhi_projectRightVonMangoldtMonomialRawIntegral
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (n : ℕ) : ℂ :=
  ∫ t : ℝ,
    ((↗Λ) n /
        (n : ℂ) ^ zetaCompletedExplicitFormulaRightAffineLine F t) *
      zetaCompletedExplicitFormulaPhi f
        (zetaCompletedExplicitFormulaRightCenteredAffineLine F t)

/-- The raw project monomial integral unfolds to the vertical-channel
integral. -/
theorem zetaCompletedExplicitFormulaPhi_projectRightVonMangoldtMonomialRawIntegral_eq
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (n : ℕ) :
    zetaCompletedExplicitFormulaPhi_projectRightVonMangoldtMonomialRawIntegral
        f F n =
      ∫ t : ℝ,
        ((↗Λ) n /
            (n : ℂ) ^ zetaCompletedExplicitFormulaRightAffineLine F t) *
          zetaCompletedExplicitFormulaPhi f
            (zetaCompletedExplicitFormulaRightCenteredAffineLine F t) := by
  rfl

/-- The raw project-convention opposite-centered reflected right-line monomial
integral.

This is the analytic integrand occurring in the reflected-left prime branch
after the elementary left-centered/right-centered reflection has been applied.
It is kept at the transform layer so the reflected sampling theorem can reuse
the ordinary right-line Paley-Wiener theorem through `reflect f`. -/
noncomputable def zetaCompletedExplicitFormulaPhi_projectRightVonMangoldtOppositeRawIntegral
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (n : ℕ) : ℂ :=
  ∫ t : ℝ,
    ((↗Λ) n /
        (n : ℂ) ^ zetaCompletedExplicitFormulaRightAffineLine F (-t)) *
      zetaCompletedExplicitFormulaPhi f
        (-(zetaCompletedExplicitFormulaRightCenteredAffineLine F (-t)))

/-- The opposite-centered reflected raw integral unfolds to its vertical-line
integral. -/
theorem zetaCompletedExplicitFormulaPhi_projectRightVonMangoldtOppositeRawIntegral_eq
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (n : ℕ) :
    zetaCompletedExplicitFormulaPhi_projectRightVonMangoldtOppositeRawIntegral
        f F n =
      ∫ t : ℝ,
        ((↗Λ) n /
            (n : ℂ) ^ zetaCompletedExplicitFormulaRightAffineLine F (-t)) *
          zetaCompletedExplicitFormulaPhi f
            (-(zetaCompletedExplicitFormulaRightCenteredAffineLine F (-t))) := by
  rfl

/-- The opposite-centered reflected raw integral is the ordinary right raw
integral for the reflected admissible test function.

This is only the `Phi` reflection identity plus invariance of Lebesgue measure
under `t ↦ -t`; it does not assert the complementary sample normalization. -/
theorem zetaCompletedExplicitFormulaPhi_projectRightVonMangoldtOppositeRawIntegral_eq_reflectRightRawIntegral
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (n : ℕ) :
    zetaCompletedExplicitFormulaPhi_projectRightVonMangoldtOppositeRawIntegral
        f F n =
      zetaCompletedExplicitFormulaPhi_projectRightVonMangoldtMonomialRawIntegral
        (ZetaAdmissibleFunction.reflect f) F n := by
  let g : ℝ → ℂ := fun u : ℝ =>
    ((↗Λ) n /
        (n : ℂ) ^ zetaCompletedExplicitFormulaRightAffineLine F u) *
      zetaCompletedExplicitFormulaPhi (ZetaAdmissibleFunction.reflect f)
        (zetaCompletedExplicitFormulaRightCenteredAffineLine F u)
  have hneg :
      MeasurePreserving (Homeomorph.neg ℝ).toMeasurableEquiv
        (volume : Measure ℝ) (volume : Measure ℝ) :=
    Measure.measurePreserving_neg (volume : Measure ℝ)
  have hcomp :
      (∫ t : ℝ,
        ((↗Λ) n /
            (n : ℂ) ^ zetaCompletedExplicitFormulaRightAffineLine F (-t)) *
          zetaCompletedExplicitFormulaPhi f
            (-(zetaCompletedExplicitFormulaRightCenteredAffineLine F (-t)))) =
        ∫ t : ℝ, g ((Homeomorph.neg ℝ) t) := by
    have hfun :
        (fun t : ℝ =>
          ((↗Λ) n /
              (n : ℂ) ^ zetaCompletedExplicitFormulaRightAffineLine F (-t)) *
            zetaCompletedExplicitFormulaPhi f
              (-(zetaCompletedExplicitFormulaRightCenteredAffineLine F (-t)))) =
          fun t : ℝ => g ((Homeomorph.neg ℝ) t) := by
      funext t
      have hphi :
          zetaCompletedExplicitFormulaPhi
              (ZetaAdmissibleFunction.reflect f)
              (zetaCompletedExplicitFormulaRightCenteredAffineLine F (-t)) =
            zetaCompletedExplicitFormulaPhi f
              (-(zetaCompletedExplicitFormulaRightCenteredAffineLine F (-t))) :=
        zetaCompletedExplicitFormulaPhi_reflect
          f (zetaCompletedExplicitFormulaRightCenteredAffineLine F (-t))
      exact
        congrArg
          (fun z : ℂ =>
            ((↗Λ) n /
                (n : ℂ) ^
                  zetaCompletedExplicitFormulaRightAffineLine F (-t)) * z)
          hphi.symm
    exact congrArg (fun φ : ℝ → ℂ => ∫ t : ℝ, φ t) hfun
  have hright :
      (∫ t : ℝ, g ((Homeomorph.neg ℝ) t)) =
        ∫ t : ℝ, g t :=
    hneg.integral_comp' (g := g)
  calc
    zetaCompletedExplicitFormulaPhi_projectRightVonMangoldtOppositeRawIntegral
        f F n =
        ∫ t : ℝ,
          ((↗Λ) n /
              (n : ℂ) ^ zetaCompletedExplicitFormulaRightAffineLine F (-t)) *
            zetaCompletedExplicitFormulaPhi f
              (-(zetaCompletedExplicitFormulaRightCenteredAffineLine F (-t))) := by
      exact
        zetaCompletedExplicitFormulaPhi_projectRightVonMangoldtOppositeRawIntegral_eq
          f F n
    _ = ∫ t : ℝ, g ((Homeomorph.neg ℝ) t) := by
      exact hcomp
    _ = ∫ t : ℝ, g t := by
      exact hright
    _ =
        zetaCompletedExplicitFormulaPhi_projectRightVonMangoldtMonomialRawIntegral
          (ZetaAdmissibleFunction.reflect f) F n := by
      rfl

/-- The normalized time-side target for a single positive natural
von-Mangoldt frequency. -/
noncomputable def zetaCompletedExplicitFormulaPhi_projectRightVonMangoldtMonomialTimeSample
    (f : ZetaAdmissibleFunction) (n : ℕ) : ℂ :=
  zetaCompletedExplicitFormulaPrimeNaturalOneSidedTimeSample f n

/-- The project monomial time-side sample unfolds to the completed
von-Mangoldt boundary sample. -/
theorem zetaCompletedExplicitFormulaPhi_projectRightVonMangoldtMonomialTimeSample_eq
    (f : ZetaAdmissibleFunction) (n : ℕ) :
    zetaCompletedExplicitFormulaPhi_projectRightVonMangoldtMonomialTimeSample
        f n =
      zetaCompletedExplicitFormulaPrimeNaturalOneSidedTimeSample f n := by
  rfl

/-- Away from zero, the project monomial one-sided sample unfolds to the
completed von-Mangoldt sample. -/
theorem zetaCompletedExplicitFormulaPhi_projectRightVonMangoldtMonomialTimeSample_of_ne_zero
    (f : ZetaAdmissibleFunction) {n : ℕ} (hn : n ≠ 0) :
    zetaCompletedExplicitFormulaPhi_projectRightVonMangoldtMonomialTimeSample
        f n =
      ((Λ n / Real.sqrt n : ℝ) : ℂ) *
        ((2 * π : ℝ) •
          zetaCompletedTimeBoundaryValue f
            (zetaCompletedExplicitFormulaPrimeNaturalCenter n)) :=
  zetaCompletedExplicitFormulaPrimeNaturalOneSidedTimeSample_of_ne_zero f hn

/-- Core analytic Paley-Wiener sampling statement in named raw-integral form.

This is the exact remaining analytic obligation for the prime right monomial:
the left side is the unnormalized project `dt` integral, and the right side is
the completed time/log-side sample. -/
theorem zetaCompletedExplicitFormulaPhi_projectRightVonMangoldtMonomialRawIntegral_eq_timeSample
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) {n : ℕ} (hn : n ≠ 0) :
    zetaCompletedExplicitFormulaPhi_projectRightVonMangoldtMonomialRawIntegral
        f F n =
      zetaCompletedExplicitFormulaPhi_projectRightVonMangoldtMonomialTimeSample
        f n := by
  exact
    Eq.trans
      (zetaCompletedExplicitFormulaPhi_projectRightVonMangoldtMonomialRawIntegral_eq
        f F n)
      (Eq.trans
        (zetaCompletedExplicitFormulaPhi_projectRightVonMangoldtMonomial_integral_eq_timeSample_ownerSamplingCore
          f F h hn)
        (zetaCompletedExplicitFormulaPhi_projectRightVonMangoldtMonomialTimeSample_eq
          f n).symm)

/-- Unconditional core analytic Paley-Wiener sampling statement in named
raw-integral form. -/
theorem zetaCompletedExplicitFormulaPhi_projectRightVonMangoldtMonomialRawIntegral_eq_timeSample_unconditional
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    {n : ℕ} (hn : n ≠ 0) :
    zetaCompletedExplicitFormulaPhi_projectRightVonMangoldtMonomialRawIntegral
        f F n =
      zetaCompletedExplicitFormulaPhi_projectRightVonMangoldtMonomialTimeSample
        f n := by
  exact
    Eq.trans
      (zetaCompletedExplicitFormulaPhi_projectRightVonMangoldtMonomialRawIntegral_eq
        f F n)
      (Eq.trans
        (zetaCompletedExplicitFormulaPhi_projectRightVonMangoldtMonomial_integral_eq_timeSample_ownerSamplingCore_unconditional
          f F hn)
        (zetaCompletedExplicitFormulaPhi_projectRightVonMangoldtMonomialTimeSample_eq
          f n).symm)

/-- Reflected/opposite-centered project sampling reduces to the ordinary
right-line sampling theorem applied to the reflected admissible probe. -/
theorem zetaCompletedExplicitFormulaPhi_projectRightVonMangoldtOppositeRawIntegral_eq_reflectOneSidedTimeSample
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (hreflect :
      ExplicitFormulaFamilyAnalyticPackage
        (ZetaAdmissibleFunction.reflect f) F)
    {n : ℕ} (hn : n ≠ 0) :
    zetaCompletedExplicitFormulaPhi_projectRightVonMangoldtOppositeRawIntegral
        f F n =
      zetaCompletedExplicitFormulaPrimeNaturalOneSidedTimeSample
        (ZetaAdmissibleFunction.reflect f) n := by
  calc
    zetaCompletedExplicitFormulaPhi_projectRightVonMangoldtOppositeRawIntegral
        f F n =
        zetaCompletedExplicitFormulaPhi_projectRightVonMangoldtMonomialRawIntegral
          (ZetaAdmissibleFunction.reflect f) F n := by
      exact
        zetaCompletedExplicitFormulaPhi_projectRightVonMangoldtOppositeRawIntegral_eq_reflectRightRawIntegral
          f F n
    _ =
        zetaCompletedExplicitFormulaPhi_projectRightVonMangoldtMonomialTimeSample
          (ZetaAdmissibleFunction.reflect f) n := by
      exact
        zetaCompletedExplicitFormulaPhi_projectRightVonMangoldtMonomialRawIntegral_eq_timeSample
          (ZetaAdmissibleFunction.reflect f) F hreflect hn
    _ =
        zetaCompletedExplicitFormulaPrimeNaturalOneSidedTimeSample
          (ZetaAdmissibleFunction.reflect f) n := by
      exact
        zetaCompletedExplicitFormulaPhi_projectRightVonMangoldtMonomialTimeSample_eq
          (ZetaAdmissibleFunction.reflect f) n

/-- Unconditional reflected/opposite-centered project sampling, reduced to
the ordinary right-line Paley-Wiener theorem for `reflect f`. -/
theorem zetaCompletedExplicitFormulaPhi_projectRightVonMangoldtOppositeRawIntegral_eq_reflectOneSidedTimeSample_unconditional
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    {n : ℕ} (hn : n ≠ 0) :
    zetaCompletedExplicitFormulaPhi_projectRightVonMangoldtOppositeRawIntegral
        f F n =
      zetaCompletedExplicitFormulaPrimeNaturalOneSidedTimeSample
        (ZetaAdmissibleFunction.reflect f) n := by
  calc
    zetaCompletedExplicitFormulaPhi_projectRightVonMangoldtOppositeRawIntegral
        f F n =
        zetaCompletedExplicitFormulaPhi_projectRightVonMangoldtMonomialRawIntegral
          (ZetaAdmissibleFunction.reflect f) F n := by
      exact
        zetaCompletedExplicitFormulaPhi_projectRightVonMangoldtOppositeRawIntegral_eq_reflectRightRawIntegral
          f F n
    _ =
        zetaCompletedExplicitFormulaPhi_projectRightVonMangoldtMonomialTimeSample
          (ZetaAdmissibleFunction.reflect f) n := by
      exact
        zetaCompletedExplicitFormulaPhi_projectRightVonMangoldtMonomialRawIntegral_eq_timeSample_unconditional
          (ZetaAdmissibleFunction.reflect f) F hn
    _ =
        zetaCompletedExplicitFormulaPrimeNaturalOneSidedTimeSample
          (ZetaAdmissibleFunction.reflect f) n := by
      exact
        zetaCompletedExplicitFormulaPhi_projectRightVonMangoldtMonomialTimeSample_eq
          (ZetaAdmissibleFunction.reflect f) n

/-- Unconditional reflected/opposite-centered project sampling, unfolded to
the original test function at the opposite logarithmic center.

This is the last transform-side theorem before the genuine left-prime
time-side normalization.  It deliberately stops at the reflected one-sided
boundary value; identifying this value with the complementary prime sample is a
separate arithmetic/functional-equation theorem. -/
theorem zetaCompletedExplicitFormulaPhi_projectRightVonMangoldtOppositeRawIntegral_eq_reflectTimeBoundarySample
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    {n : ℕ} (hn : n ≠ 0) :
    zetaCompletedExplicitFormulaPhi_projectRightVonMangoldtOppositeRawIntegral
        f F n =
      ((Λ n / Real.sqrt n : ℝ) : ℂ) *
        ((2 * π : ℝ) •
          zetaCompletedTimeBoundaryValue f
            (-(zetaCompletedExplicitFormulaPrimeNaturalCenter n))) := by
  exact
    Eq.trans
      (zetaCompletedExplicitFormulaPhi_projectRightVonMangoldtOppositeRawIntegral_eq_reflectOneSidedTimeSample_unconditional
        f F hn)
      (zetaCompletedExplicitFormulaPrimeNaturalOneSidedTimeSample_reflect_of_ne_zero
        f hn)

/-- Unconditional reflected/opposite-centered project sampling, in the named
reflected natural boundary-sample normalization. -/
theorem zetaCompletedExplicitFormulaPhi_projectRightVonMangoldtOppositeRawIntegral_eq_reflectedTimeBoundarySample
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    {n : ℕ} (hn : n ≠ 0) :
    zetaCompletedExplicitFormulaPhi_projectRightVonMangoldtOppositeRawIntegral
        f F n =
      zetaCompletedExplicitFormulaPrimeNaturalReflectedTimeBoundarySample
        f n := by
  exact
    Eq.trans
      (zetaCompletedExplicitFormulaPhi_projectRightVonMangoldtOppositeRawIntegral_eq_reflectOneSidedTimeSample_unconditional
        f F hn)
      (zetaCompletedExplicitFormulaPrimeNaturalOneSidedTimeSample_reflect_eq_reflectedTimeBoundarySample
        f n)

/-- Project-convention Paley-Wiener/Fourier sampling for the shifted right
vertical character attached to a positive natural index.

The proof belongs at the Paley-Wiener transform layer.  It must combine:

* the vertical-line Fourier inversion theorem for the autocorrelation test
  function;
* the exponential-character identity for `(n : ℂ) ^ (-(F.c + i t))`;
* the completed normalization at the time point `Real.log n`.

This is the analytic owner theorem.  The file
`PaleyWienerFourierInversion` consumes it and performs only vertical-channel
algebra. -/
theorem zetaCompletedExplicitFormulaPhi_projectRightVonMangoldtMonomial_integral_eq_timeSample
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
  exact
    Eq.trans
      (zetaCompletedExplicitFormulaPhi_projectRightVonMangoldtMonomialRawIntegral_eq
        f F n).symm
      (Eq.trans
        (zetaCompletedExplicitFormulaPhi_projectRightVonMangoldtMonomialRawIntegral_eq_timeSample
          f F h hn)
        (zetaCompletedExplicitFormulaPhi_projectRightVonMangoldtMonomialTimeSample_of_ne_zero
          f hn))

end ZetaAdmissibleFunction

end
end LFunctions
end Boundary
