import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaExplicitFormulaVerticalChannels.OwnerParts.PrimeNaturalTimeArithmetic
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaExplicitFormulaVerticalChannels.OwnerParts.PaleyWienerFourierInversion
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaExplicitFormulaVerticalChannels.OwnerParts.PrimeRightTermKernelAlgebra

/-!
# Fourier value of a single right von Mangoldt term kernel

This file owns the non-circular wrapper from the monomial Paley-Wiener/Fourier
inversion theorem to the named single-term right von Mangoldt kernel.  It sits
upstream of the sum/integral exchange and Dirichlet-series assembly files, but
the analytic sampling theorem itself lives in `PaleyWienerFourierInversion`.

The project vertical convention uses `exp (I * y * t)`, not mathlib's
`2π`-normalized Fourier convention.  The proof must therefore pass through an
explicit normalization bridge, with the change of variables
`y_mathlib = y / (2 * Real.pi)`, before reducing the scalar factor to
`Λ n / sqrt n`.
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

/-- Owner wrapper: positive-index Fourier/Mellin inversion for a single right
von Mangoldt term kernel.

Proof chain:
`monomial Paley-Wiener/Fourier value`
`-> pointwise term-kernel algebra`
`-> integral transport`. -/
theorem zetaCompletedExplicitFormulaPrimeRightVonMangoldtTermKernel_integral_eq_primeNaturalOneSidedTimeSample_ownerFourierValue
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) {n : ℕ} (hn : n ≠ 0) :
    (∫ t : ℝ,
      zetaCompletedExplicitFormulaPrimeRightVonMangoldtTermKernel f F n t) =
      zetaCompletedExplicitFormulaPrimeNaturalOneSidedTimeSample f n := by
  let M : ℂ :=
    ∫ t : ℝ,
      ((↗Λ) n /
          (n : ℂ) ^ zetaCompletedExplicitFormulaRightAffineLine F t) *
        zetaCompletedExplicitFormulaPhi f
          (zetaCompletedExplicitFormulaRightCenteredAffineLine F t)
  let K : ℂ :=
    ∫ t : ℝ,
      zetaCompletedExplicitFormulaPrimeRightVonMangoldtTermKernel f F n t
  let S : ℂ :=
    zetaCompletedExplicitFormulaPrimeNaturalOneSidedTimeSample f n
  have hMK : M = K :=
    zetaCompletedExplicitFormulaPrimeRightVonMangoldtPositiveMonomial_integral_eq_termKernel_integral
      f F hn
  have hMS : M = S :=
    zetaCompletedExplicitFormulaPrimeRightVonMangoldtPositiveMonomial_integral_eq_primeNaturalOneSidedTimeSample_ownerFourierInversion
      f F h hn
  exact Eq.trans hMK.symm hMS

/-- Owner wrapper: positive-index Fourier/Mellin inversion for a single right
von Mangoldt term kernel, using the unconditional Paley-Wiener sampling
theorem. -/
theorem zetaCompletedExplicitFormulaPrimeRightVonMangoldtTermKernel_integral_eq_primeNaturalOneSidedTimeSample_unconditional_ownerFourierValue
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    {n : ℕ} (hn : n ≠ 0) :
    (∫ t : ℝ,
      zetaCompletedExplicitFormulaPrimeRightVonMangoldtTermKernel f F n t) =
      zetaCompletedExplicitFormulaPrimeNaturalOneSidedTimeSample f n :=
  let M : ℂ :=
    ∫ t : ℝ,
      ((↗Λ) n /
          (n : ℂ) ^ zetaCompletedExplicitFormulaRightAffineLine F t) *
        zetaCompletedExplicitFormulaPhi f
          (zetaCompletedExplicitFormulaRightCenteredAffineLine F t)
  let K : ℂ :=
    ∫ t : ℝ,
      zetaCompletedExplicitFormulaPrimeRightVonMangoldtTermKernel f F n t
  let S : ℂ :=
    zetaCompletedExplicitFormulaPrimeNaturalOneSidedTimeSample f n
  have hMK : M = K :=
    zetaCompletedExplicitFormulaPrimeRightVonMangoldtPositiveMonomial_integral_eq_termKernel_integral
      f F hn
  have hMS : M = S :=
    Eq.trans
      (zetaCompletedExplicitFormulaPhi_projectRightVonMangoldtMonomialRawIntegral_eq
        f F n).symm
      (Eq.trans
        (zetaCompletedExplicitFormulaPhi_projectRightVonMangoldtMonomialRawIntegral_eq_timeSample_unconditional
          f F hn)
        (zetaCompletedExplicitFormulaPhi_projectRightVonMangoldtMonomialTimeSample_eq
          f n))
  Eq.trans hMK.symm hMS

end ZetaAdmissibleFunction

end
end LFunctions
end Boundary
