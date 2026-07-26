import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaCompletedHilbertSource.ZetaHermitianPacket.PrimeCenterSamplingDecayParts.TraceBesselParts.PrimeAmplitudeProjectionEnergy
import Mathlib.Order.Filter.Defs
import Mathlib.Topology.Algebra.InfiniteSum.Order

/-!
# Prime weighted sampling Bessel core

This file owns the acyclic finite-window definitions and coordinate comparison
lemmas for weighted prime-center sampling.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open Filter
open scoped BigOperators

namespace ZetaAdmissibleFunction

/-- A scalar is an upper bound for every rectangular box subtrace of the weighted
completed prime-center sampling stream. -/
def CompletedAutocorrelationSpectralTransformWeightedPrimeSamplingBoxSubtraceUpperBound
    (f : ZetaAdmissibleFunction) (C : ℝ) : Prop :=
  ∀ N : ℕ,
    ∑ index in ZetaPrimePowerIndex.box N,
      completedAutocorrelationSpectralTransform_weightedPrimeSampling
        index f ≤ C

/-- A scalar is an upper bound for every genuine window subtrace of the weighted
completed prime-center sampling stream. -/
def CompletedAutocorrelationSpectralTransformWeightedPrimeSamplingWindowSubtraceUpperBound
    (f : ZetaAdmissibleFunction) (C : ℝ) : Prop :=
  ∀ N : ℕ,
    ∑ index in ZetaPrimePowerIndex.window N,
      completedAutocorrelationSpectralTransform_weightedPrimeSampling
        index f ≤ C

/-- A scalar is an upper bound for every genuine window of square-root-weighted
completed prime spectral amplitudes. -/
def ZetaCompletedPrimeSpectralAmplitudeWindowNormSqUpperBound
    (f : ZetaAdmissibleFunction) (C : ℝ) : Prop :=
  ∀ N : ℕ,
    ∑ index in ZetaPrimePowerIndex.window N,
      ‖zetaCompletedPrimeSpectralAmplitudeIndex index f‖ ^ 2 ≤ C

/-- A scalar is an upper bound for every completed prime diagonal-debt real
window. -/
def ZetaCompletedPrimeDefectKernelDiagonalDebtRealWindowUpperBound
    (f : ZetaAdmissibleFunction) (C : ℝ) : Prop :=
  ∀ N : ℕ,
    zetaCompletedPrimeDefectKernelDiagonalDebtRealWindow N f ≤ C

/-- Every finite weighted prime-center subtrace is dominated by a rectangular
box subtrace. -/
theorem completedAutocorrelationSpectralTransform_weightedPrimeSampling_finiteSubtrace_le_boxSubtrace_traceBessel
    (f : ZetaAdmissibleFunction) :
    ∀ s : Finset ZetaPrimePowerIndex,
      ∃ N : ℕ,
        ∑ index in s,
          completedAutocorrelationSpectralTransform_weightedPrimeSampling
            index f ≤
        ∑ index in ZetaPrimePowerIndex.box N,
          completedAutocorrelationSpectralTransform_weightedPrimeSampling
            index f :=
  fun s =>
  let hcontainsEventually :
      ∀ᶠ N in Filter.atTop,
        s ≤ ZetaPrimePowerIndex.box N :=
    ZetaPrimePowerIndex.box_tendsto_atTop.eventually
      (Filter.eventually_ge_atTop s)
  match hcontainsEventually.exists with
  | ⟨N, hN⟩ =>
      let hsubset : s ⊆ ZetaPrimePowerIndex.box N := hN
      let hsum :
          ∑ index in s,
            completedAutocorrelationSpectralTransform_weightedPrimeSampling
              index f ≤
          ∑ index in ZetaPrimePowerIndex.box N,
            completedAutocorrelationSpectralTransform_weightedPrimeSampling
              index f :=
        Finset.sum_le_sum_of_subset_of_nonneg
          hsubset
          (fun index boxMembership outsideMembership =>
            completedAutocorrelationSpectralTransform_weightedPrimeSampling_nonnegative
              index f)
      Exists.intro N hsum

/-- A positive completed prime face coordinate is bounded by its completed
diagonal-debt coordinate real scalar. -/
theorem zetaCompletedPrimeSpectralAmplitudeIndex_normSq_le_diagonalDebtCoordinate_re_traceBessel
    (index : ZetaPrimePowerIndex) (f : ZetaAdmissibleFunction) :
    ‖zetaCompletedPrimeSpectralAmplitudeIndex index f‖ ^ 2 ≤
      Complex.re
        (zetaCompletedPrimeDefectKernelDiagonalDebtCoordinate index f) :=
  let hcoordinate :
      Complex.re
          (zetaCompletedPrimeDefectKernelDiagonalDebtCoordinate index f) =
        Complex.normSq
            (zetaCompletedPrimeSpectralAmplitudeIndex index f) +
          Complex.normSq
            (zetaCompletedPrimeOppositeSpectralAmplitudeIndex index f) :=
    zetaCompletedPrimeDefectKernelDiagonalDebtCoordinate_re_eq_normSq_add_normSq
      index f
  let hpositiveNorm :
      ‖zetaCompletedPrimeSpectralAmplitudeIndex index f‖ ^ 2 =
        Complex.normSq
          (zetaCompletedPrimeSpectralAmplitudeIndex index f) :=
    (Complex.normSq_eq_norm_sq
      (zetaCompletedPrimeSpectralAmplitudeIndex index f)).symm
  let hoppositeNonnegative :
      0 ≤
        Complex.normSq
          (zetaCompletedPrimeOppositeSpectralAmplitudeIndex index f) :=
    Complex.normSq_nonneg
      (zetaCompletedPrimeOppositeSpectralAmplitudeIndex index f)
  let hleftLe :
      Complex.normSq
          (zetaCompletedPrimeSpectralAmplitudeIndex index f) ≤
        Complex.normSq
            (zetaCompletedPrimeSpectralAmplitudeIndex index f) +
          Complex.normSq
          (zetaCompletedPrimeOppositeSpectralAmplitudeIndex index f) :=
    le_add_of_nonneg_right hoppositeNonnegative
  Eq.subst
    (motive := fun value : ℝ =>
      ‖zetaCompletedPrimeSpectralAmplitudeIndex index f‖ ^ 2 ≤ value)
    hcoordinate.symm
    (Eq.subst
      (motive := fun value : ℝ =>
        value ≤
          Complex.normSq
              (zetaCompletedPrimeSpectralAmplitudeIndex index f) +
            Complex.normSq
              (zetaCompletedPrimeOppositeSpectralAmplitudeIndex index f))
      hpositiveNorm.symm
      hleftLe)

theorem zetaCompletedPrimeDefectKernelDiagonalDebtRealWindow_eq_sum_re_traceBessel
    (N : ℕ) (f : ZetaAdmissibleFunction) :
    zetaCompletedPrimeDefectKernelDiagonalDebtRealWindow N f =
      ∑ index in ZetaPrimePowerIndex.window N,
        Complex.re
          (zetaCompletedPrimeDefectKernelDiagonalDebtCoordinate index f) :=
  Complex.re_sum
    (ZetaPrimePowerIndex.window N)
    (fun index : ZetaPrimePowerIndex =>
      zetaCompletedPrimeDefectKernelDiagonalDebtCoordinate index f)

/-- A positive completed prime face window is bounded by the completed
diagonal-debt real window. -/
theorem zetaCompletedPrimeSpectralAmplitudeIndex_normSq_windowSubtrace_le_diagonalDebtRealWindow_traceBessel
    (N : ℕ) (f : ZetaAdmissibleFunction) :
    (∑ index in ZetaPrimePowerIndex.window N,
      ‖zetaCompletedPrimeSpectralAmplitudeIndex index f‖ ^ 2) ≤
      zetaCompletedPrimeDefectKernelDiagonalDebtRealWindow N f :=
  let hsum :
      (∑ index in ZetaPrimePowerIndex.window N,
        ‖zetaCompletedPrimeSpectralAmplitudeIndex index f‖ ^ 2) ≤
        ∑ index in ZetaPrimePowerIndex.window N,
          Complex.re
            (zetaCompletedPrimeDefectKernelDiagonalDebtCoordinate index f) :=
    Finset.sum_le_sum
      (fun index windowMembership =>
        zetaCompletedPrimeSpectralAmplitudeIndex_normSq_le_diagonalDebtCoordinate_re_traceBessel
          index f)
  let hrealWindow :
      zetaCompletedPrimeDefectKernelDiagonalDebtRealWindow N f =
        ∑ index in ZetaPrimePowerIndex.window N,
          Complex.re
            (zetaCompletedPrimeDefectKernelDiagonalDebtCoordinate index f) :=
    zetaCompletedPrimeDefectKernelDiagonalDebtRealWindow_eq_sum_re_traceBessel
      N f
  Eq.subst
    (motive := fun value : ℝ =>
      (∑ index in ZetaPrimePowerIndex.window N,
        ‖zetaCompletedPrimeSpectralAmplitudeIndex index f‖ ^ 2) ≤ value)
    hrealWindow.symm
    hsum

/-- A completed prime diagonal-debt coordinate has nonnegative real scalar. -/
theorem zetaCompletedPrimeDefectKernelDiagonalDebtCoordinate_re_nonnegative_traceBessel
    (index : ZetaPrimePowerIndex) (f : ZetaAdmissibleFunction) :
    0 ≤
      Complex.re
        (zetaCompletedPrimeDefectKernelDiagonalDebtCoordinate index f) :=
  let hcoordinate :
      Complex.re
          (zetaCompletedPrimeDefectKernelDiagonalDebtCoordinate index f) =
        Complex.normSq
            (zetaCompletedPrimeSpectralAmplitudeIndex index f) +
          Complex.normSq
            (zetaCompletedPrimeOppositeSpectralAmplitudeIndex index f) :=
    zetaCompletedPrimeDefectKernelDiagonalDebtCoordinate_re_eq_normSq_add_normSq
      index f
  let hpositive :
      0 ≤
        Complex.normSq
          (zetaCompletedPrimeSpectralAmplitudeIndex index f) :=
    Complex.normSq_nonneg
      (zetaCompletedPrimeSpectralAmplitudeIndex index f)
  let hnegative :
      0 ≤
        Complex.normSq
          (zetaCompletedPrimeOppositeSpectralAmplitudeIndex index f) :=
    Complex.normSq_nonneg
      (zetaCompletedPrimeOppositeSpectralAmplitudeIndex index f)
  Eq.subst
    (motive := fun value : ℝ => 0 ≤ value)
    hcoordinate.symm
    (add_nonneg hpositive hnegative)

end ZetaAdmissibleFunction

end
end LFunctions
end Boundary
