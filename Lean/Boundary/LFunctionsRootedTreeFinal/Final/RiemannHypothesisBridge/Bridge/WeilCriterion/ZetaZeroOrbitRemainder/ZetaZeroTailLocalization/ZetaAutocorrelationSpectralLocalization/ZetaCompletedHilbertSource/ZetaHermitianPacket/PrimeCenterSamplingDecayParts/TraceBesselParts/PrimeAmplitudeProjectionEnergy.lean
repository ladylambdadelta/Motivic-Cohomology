import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaCompletedHilbertSource.ZetaHermitianPacket.CompletedPrimePowerSampling
import Mathlib.Order.Filter.Defs
import Mathlib.Topology.Algebra.InfiniteSum.Order

/-!
# Prime amplitude projection energy

This file owns the finite one-face completed prime spectral-amplitude
projection-energy source.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open Filter
open scoped BigOperators

namespace ZetaAdmissibleFunction

/-- Completed prime spectral amplitude coordinate squares are nonnegative. -/
theorem zetaCompletedPrimeSpectralAmplitudeIndex_normSq_nonnegative_traceBessel
    (index : ZetaPrimePowerIndex) (f : ZetaAdmissibleFunction) :
    0 ≤ ‖zetaCompletedPrimeSpectralAmplitudeIndex index f‖ ^ 2 :=
  sq_nonneg ‖zetaCompletedPrimeSpectralAmplitudeIndex index f‖

/-- The finite one-face completed prime spectral-amplitude projection energy. -/
noncomputable def zetaCompletedPrimeSpectralAmplitudeIndex_normSqProjectionEnergy_traceBessel
    (s : Finset ZetaPrimePowerIndex) (f : ZetaAdmissibleFunction) : ℝ :=
  ∑ index in s,
    ‖zetaCompletedPrimeSpectralAmplitudeIndex index f‖ ^ 2

/-- The finite one-face completed prime spectral-amplitude projection energy
unfolds to its finite sum. -/
theorem zetaCompletedPrimeSpectralAmplitudeIndex_normSqProjectionEnergy_eq_sum_traceBessel
    (s : Finset ZetaPrimePowerIndex) (f : ZetaAdmissibleFunction) :
    zetaCompletedPrimeSpectralAmplitudeIndex_normSqProjectionEnergy_traceBessel
        s f =
      ∑ index in s,
        ‖zetaCompletedPrimeSpectralAmplitudeIndex index f‖ ^ 2 :=
  Eq.refl
    (zetaCompletedPrimeSpectralAmplitudeIndex_normSqProjectionEnergy_traceBessel
      s f)

/-- Nongenuine prime-power indices have zero positive completed prime spectral
amplitude. -/
theorem zetaCompletedPrimeSpectralAmplitudeIndex_eq_zero_of_not_isGenuine_traceBessel
    (index : ZetaPrimePowerIndex) (f : ZetaAdmissibleFunction)
    (hindex : ¬ ZetaPrimePowerIndex.IsGenuine index) :
    zetaCompletedPrimeSpectralAmplitudeIndex index f = 0 :=
  let hweight : ZetaPrimePowerIndex.weight index = 0 :=
    ZetaPrimePowerIndex.weight_eq_zero_of_not_isGenuine index hindex
  let hsqrt : ZetaPrimePowerIndex.sqrtWeight index = 0 :=
    (congrArg Real.sqrt hweight).trans Real.sqrt_zero
  Eq.trans
    (congrArg
      (fun value : ℝ =>
        (value : ℂ) *
          zetaCompletedPrimeHermitianSeedAmplitude index.p index.n f)
      hsqrt)
    (zero_mul (zetaCompletedPrimeHermitianSeedAmplitude index.p index.n f))

/-- Nongenuine prime-power indices have zero positive completed prime spectral
amplitude norm-square. -/
theorem zetaCompletedPrimeSpectralAmplitudeIndex_normSq_eq_zero_of_not_isGenuine_traceBessel
    (index : ZetaPrimePowerIndex) (f : ZetaAdmissibleFunction)
    (hindex : ¬ ZetaPrimePowerIndex.IsGenuine index) :
    ‖zetaCompletedPrimeSpectralAmplitudeIndex index f‖ ^ 2 = 0 :=
  let hamplitude :
      zetaCompletedPrimeSpectralAmplitudeIndex index f = 0 :=
    zetaCompletedPrimeSpectralAmplitudeIndex_eq_zero_of_not_isGenuine_traceBessel
      index f hindex
  let hnormZero :
      ‖(0 : ℂ)‖ ^ 2 = 0 :=
    Eq.trans
      (congrArg
        (fun value : ℝ => value ^ 2)
        (norm_zero : ‖(0 : ℂ)‖ = 0))
      (Eq.trans (pow_two (0 : ℝ)) (zero_mul (0 : ℝ)))
  Eq.trans
    (congrArg
      (fun value : ℂ => ‖value‖ ^ 2)
      hamplitude)
    hnormZero

/-- Rectangular boxes and genuine windows give the same positive completed
prime spectral-amplitude norm-square sum. -/
theorem sum_box_zetaCompletedPrimeSpectralAmplitudeIndex_normSq_eq_sum_window_traceBessel
    (N : ℕ) (f : ZetaAdmissibleFunction) :
    (∑ index in ZetaPrimePowerIndex.box N,
      ‖zetaCompletedPrimeSpectralAmplitudeIndex index f‖ ^ 2) =
      ∑ index in ZetaPrimePowerIndex.window N,
        ‖zetaCompletedPrimeSpectralAmplitudeIndex index f‖ ^ 2 :=
  ZetaPrimePowerIndex.sum_box_eq_sum_window_of_zero_not_isGenuine
    (fun index : ZetaPrimePowerIndex =>
      ‖zetaCompletedPrimeSpectralAmplitudeIndex index f‖ ^ 2)
    (fun index hindex =>
      zetaCompletedPrimeSpectralAmplitudeIndex_normSq_eq_zero_of_not_isGenuine_traceBessel
        index f hindex)
    N

/-- Every finite positive completed prime spectral-amplitude subtrace is
dominated by some rectangular box subtrace. -/
theorem zetaCompletedPrimeSpectralAmplitudeIndex_normSqProjectionEnergy_le_boxSubtrace_traceBessel
    (s : Finset ZetaPrimePowerIndex) (f : ZetaAdmissibleFunction) :
    ∃ N : ℕ,
      zetaCompletedPrimeSpectralAmplitudeIndex_normSqProjectionEnergy_traceBessel
          s f ≤
        ∑ index in ZetaPrimePowerIndex.box N,
          ‖zetaCompletedPrimeSpectralAmplitudeIndex index f‖ ^ 2 :=
  let hcontainsEventually :
      ∀ᶠ N in Filter.atTop,
        s ≤ ZetaPrimePowerIndex.box N :=
    ZetaPrimePowerIndex.box_tendsto_atTop.eventually
      (Filter.eventually_ge_atTop s)
  match hcontainsEventually.exists with
  | ⟨N, hN⟩ =>
      let hsubset :
          s ⊆ ZetaPrimePowerIndex.box N :=
        hN
      let hsum :
          ∑ index in s,
            ‖zetaCompletedPrimeSpectralAmplitudeIndex index f‖ ^ 2 ≤
          ∑ index in ZetaPrimePowerIndex.box N,
            ‖zetaCompletedPrimeSpectralAmplitudeIndex index f‖ ^ 2 :=
        Finset.sum_le_sum_of_subset_of_nonneg
          hsubset
          (fun index boxMembership outsideMembership =>
            zetaCompletedPrimeSpectralAmplitudeIndex_normSq_nonnegative_traceBessel
              index f)
      Exists.intro N
        (Eq.subst
          (motive := fun value : ℝ =>
            value ≤
              ∑ index in ZetaPrimePowerIndex.box N,
                ‖zetaCompletedPrimeSpectralAmplitudeIndex index f‖ ^ 2)
          (zetaCompletedPrimeSpectralAmplitudeIndex_normSqProjectionEnergy_eq_sum_traceBessel
            s f).symm
          hsum)

/-- A positive completed prime face coordinate is bounded by its completed
diagonal-debt coordinate real scalar. -/
theorem zetaCompletedPrimeSpectralAmplitudeIndex_normSq_le_diagonalDebtCoordinate_re_traceBessel_projection
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

theorem zetaCompletedPrimeDefectKernelDiagonalDebtRealWindow_eq_sum_re_traceBessel_projection
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
theorem zetaCompletedPrimeSpectralAmplitudeIndex_normSq_windowSubtrace_le_diagonalDebtRealWindow_traceBessel_projection
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
        zetaCompletedPrimeSpectralAmplitudeIndex_normSq_le_diagonalDebtCoordinate_re_traceBessel_projection
          index f)
  let hrealWindow :
      zetaCompletedPrimeDefectKernelDiagonalDebtRealWindow N f =
        ∑ index in ZetaPrimePowerIndex.window N,
          Complex.re
            (zetaCompletedPrimeDefectKernelDiagonalDebtCoordinate index f) :=
    zetaCompletedPrimeDefectKernelDiagonalDebtRealWindow_eq_sum_re_traceBessel_projection
      N f
  Eq.subst
    (motive := fun value : ℝ =>
      (∑ index in ZetaPrimePowerIndex.window N,
        ‖zetaCompletedPrimeSpectralAmplitudeIndex index f‖ ^ 2) ≤ value)
    hrealWindow.symm
    hsum

/-- A finite one-face completed prime spectral-amplitude projection is bounded
by some completed diagonal-debt real window. -/
theorem zetaCompletedPrimeSpectralAmplitudeIndex_normSqProjectionEnergy_le_diagonalDebtRealWindow_traceBessel
    (s : Finset ZetaPrimePowerIndex) (f : ZetaAdmissibleFunction) :
    ∃ N : ℕ,
      zetaCompletedPrimeSpectralAmplitudeIndex_normSqProjectionEnergy_traceBessel
          s f ≤
        zetaCompletedPrimeDefectKernelDiagonalDebtRealWindow N f :=
  match
    zetaCompletedPrimeSpectralAmplitudeIndex_normSqProjectionEnergy_le_boxSubtrace_traceBessel
      s f with
  | ⟨N, hfinite_le_box⟩ =>
      let hbox_eq_window :
          (∑ index in ZetaPrimePowerIndex.box N,
            ‖zetaCompletedPrimeSpectralAmplitudeIndex index f‖ ^ 2) =
            ∑ index in ZetaPrimePowerIndex.window N,
              ‖zetaCompletedPrimeSpectralAmplitudeIndex index f‖ ^ 2 :=
        sum_box_zetaCompletedPrimeSpectralAmplitudeIndex_normSq_eq_sum_window_traceBessel
          N f
      let hwindow_le_diagonal :
          (∑ index in ZetaPrimePowerIndex.window N,
            ‖zetaCompletedPrimeSpectralAmplitudeIndex index f‖ ^ 2) ≤
            zetaCompletedPrimeDefectKernelDiagonalDebtRealWindow N f :=
        zetaCompletedPrimeSpectralAmplitudeIndex_normSq_windowSubtrace_le_diagonalDebtRealWindow_traceBessel_projection
          N f
      let hbox_le_diagonal :
          (∑ index in ZetaPrimePowerIndex.box N,
            ‖zetaCompletedPrimeSpectralAmplitudeIndex index f‖ ^ 2) ≤
            zetaCompletedPrimeDefectKernelDiagonalDebtRealWindow N f :=
        Eq.subst
          (motive := fun value : ℝ =>
            value ≤ zetaCompletedPrimeDefectKernelDiagonalDebtRealWindow N f)
          hbox_eq_window.symm
          hwindow_le_diagonal
      Exists.intro N (le_trans hfinite_le_box hbox_le_diagonal)

end ZetaAdmissibleFunction

end
end LFunctions
end Boundary
