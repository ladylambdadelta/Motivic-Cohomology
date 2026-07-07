import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaExplicitFormulaVerticalChannels.OwnerParts.PrimeNaturalTimeArithmetic
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaExplicitFormulaVerticalChannels.OwnerParts.PrimeRightTermKernelAlgebra
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaExplicitFormulaVerticalChannels.OwnerParts.PaleyWienerProjectSampling

/-!
# Paley-Wiener Fourier inversion inputs for vertical channels

This file owns the Fourier/Mellin inversion theorem that converts a vertical
line integral of the spectral/Laplace transform `Φ_f` into a time/log-side
boundary sample.  It deliberately does not identify `Φ_f a` with the time-side
value at `a`; those are distinct realizations in the analytic core.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open Complex
open Filter
open LSeries ArithmeticFunction
open MeasureTheory
open scoped ArithmeticFunction
open scoped LSeries.notation
open scoped Topology

namespace ZetaAdmissibleFunction

/-- Pointwise algebraic transport from the positive-index monomial form to the
named right von Mangoldt term kernel. -/
theorem zetaCompletedExplicitFormulaPrimeRightVonMangoldtPositiveMonomial_eq_termKernel
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    {n : ℕ} (hn : n ≠ 0) (t : ℝ) :
    ((↗Λ) n /
        (n : ℂ) ^ zetaCompletedExplicitFormulaRightAffineLine F t) *
      zetaCompletedExplicitFormulaPhi f
        (zetaCompletedExplicitFormulaRightCenteredAffineLine F t) =
      zetaCompletedExplicitFormulaPrimeRightVonMangoldtTermKernel f F n t := by
  exact
    (zetaCompletedExplicitFormulaPrimeRightVonMangoldtTermKernel_eq_of_ne_zero
      f F hn t).symm

/-- Whole-line integral transport from the positive-index monomial form to the
named right von Mangoldt term kernel. -/
theorem zetaCompletedExplicitFormulaPrimeRightVonMangoldtPositiveMonomial_integral_eq_termKernel_integral
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    {n : ℕ} (hn : n ≠ 0) :
    (∫ t : ℝ,
      ((↗Λ) n /
          (n : ℂ) ^ zetaCompletedExplicitFormulaRightAffineLine F t) *
        zetaCompletedExplicitFormulaPhi f
          (zetaCompletedExplicitFormulaRightCenteredAffineLine F t)) =
      ∫ t : ℝ,
        zetaCompletedExplicitFormulaPrimeRightVonMangoldtTermKernel f F n t := by
  have hfun :
      (fun t : ℝ =>
        ((↗Λ) n /
            (n : ℂ) ^ zetaCompletedExplicitFormulaRightAffineLine F t) *
          zetaCompletedExplicitFormulaPhi f
            (zetaCompletedExplicitFormulaRightCenteredAffineLine F t)) =
        fun t : ℝ =>
          zetaCompletedExplicitFormulaPrimeRightVonMangoldtTermKernel f F n t := by
    funext t
    exact
      zetaCompletedExplicitFormulaPrimeRightVonMangoldtPositiveMonomial_eq_termKernel
        f F hn t
  exact congrArg (fun φ : ℝ → ℂ => ∫ t : ℝ, φ t) hfun

/-- Assembly form of the positive-index Fourier inversion leaf: once the
named right von Mangoldt term kernel has been inverted, the original monomial
form follows by definitional algebra. -/
theorem zetaCompletedExplicitFormulaPrimeRightVonMangoldtPositiveMonomial_integral_eq_primeNaturalTimeSummand_of_termKernel_integral_eq
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) {n : ℕ} (hn : n ≠ 0)
    (hterm :
      (∫ t : ℝ,
        zetaCompletedExplicitFormulaPrimeRightVonMangoldtTermKernel f F n t) =
        zetaCompletedExplicitFormulaPrimeNaturalTimeSummand f n) :
    (∫ t : ℝ,
      ((↗Λ) n /
          (n : ℂ) ^ zetaCompletedExplicitFormulaRightAffineLine F t) *
        zetaCompletedExplicitFormulaPhi f
          (zetaCompletedExplicitFormulaRightCenteredAffineLine F t)) =
      zetaCompletedExplicitFormulaPrimeNaturalTimeSummand f n := by
  exact
    Eq.trans
      (zetaCompletedExplicitFormulaPrimeRightVonMangoldtPositiveMonomial_integral_eq_termKernel_integral
        f F hn)
      hterm

/-- Positive-index Paley-Wiener/Fourier inversion for one right-line von
Mangoldt monomial.

The analytic project-convention sampling theorem is owned in
`PaleyWienerProjectSampling`.  This theorem is a compatibility name for the
vertical-channel prime branch. -/
theorem zetaCompletedExplicitFormulaPrimeRightVonMangoldtPositiveMonomial_integral_eq_primeNaturalOneSidedTimeSample_ownerFourierInversion
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) {n : ℕ} (hn : n ≠ 0) :
    (∫ t : ℝ,
      ((↗Λ) n /
          (n : ℂ) ^ zetaCompletedExplicitFormulaRightAffineLine F t) *
        zetaCompletedExplicitFormulaPhi f
          (zetaCompletedExplicitFormulaRightCenteredAffineLine F t)) =
      zetaCompletedExplicitFormulaPrimeNaturalOneSidedTimeSample f n := by
  exact Eq.trans
    (zetaCompletedExplicitFormulaPhi_projectRightVonMangoldtMonomial_integral_eq_timeSample
      f F h hn)
    (zetaCompletedExplicitFormulaPrimeNaturalOneSidedTimeSample_of_ne_zero
      f hn).symm

end ZetaAdmissibleFunction

end
end LFunctions
end Boundary
