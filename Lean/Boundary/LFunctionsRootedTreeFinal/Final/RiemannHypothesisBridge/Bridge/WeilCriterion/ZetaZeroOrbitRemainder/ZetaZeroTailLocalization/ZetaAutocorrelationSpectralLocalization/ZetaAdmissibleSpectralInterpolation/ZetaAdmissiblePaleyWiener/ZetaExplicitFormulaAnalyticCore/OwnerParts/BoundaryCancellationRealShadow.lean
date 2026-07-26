import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaAdmissibleSpectralInterpolation.ZetaAdmissiblePaleyWiener.ZetaExplicitFormulaAnalyticCore.OwnerParts.ContourTomography
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaAdmissibleSpectralInterpolation.ZetaAdmissiblePaleyWiener.ZetaExplicitFormulaAnalyticCore.OwnerParts.BoundaryCancellationRealShadowParts.TwoFaceWindowParts.PairedTraceKernel

/-!
# Boundary cancellation real-shadow source

This file owns the real-shadow rectangular cancellation input consumed by the
completed prime-power autocorrelation ledger.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open scoped BigOperators Topology

namespace ZetaAdmissibleFunction

/-- Source rectangular cancellation for the paired completed two-face
autocorrelation coordinate stream.  This is the concrete contour trace
identity; the ledger proposition and real-shadow forms are projections of this
stream-level statement. -/
theorem zetaCompletedPrimePowerAutocorrelationTwoFaceCoordinate_boxSum_tendsto_zero_traceKernel_source_core
    (f : ZetaAdmissibleFunction)
    (hmajorant : Summable (fun index : ZetaPrimePowerIndex =>
      zetaCompletedPrimeSpectralCoordinateMajorant index f)) :
    Filter.Tendsto
      (fun N : ℕ =>
        ∑ index in ZetaPrimePowerIndex.box N,
          (zetaCompletedPrimePowerAutocorrelationOrientedCrossCoordinate
              index f +
            zetaCompletedPrimePowerAutocorrelationOppositeOrientedCrossCoordinate
              index f))
      Filter.atTop
      (nhds 0) := by
  exact
    zetaCompletedPrimePowerAutocorrelationTwoFaceCoordinate_boxSum_tendsto_zero_pairedTraceKernel_source
      f hmajorant

/-- The trace-kernel paired window cancellation supplies the completed
prime-power autocorrelation ledger cancellation. -/
theorem zetaCompletedPrimePowerAutocorrelationLedgerCancellation_traceKernel_window_source_core
    (f : ZetaAdmissibleFunction)
    (hmajorant : Summable (fun index : ZetaPrimePowerIndex =>
      zetaCompletedPrimeSpectralCoordinateMajorant index f)) :
    ZetaCompletedPrimePowerAutocorrelationLedgerCancellation f := by
  exact
    zetaCompletedPrimePowerAutocorrelationTwoFaceCoordinate_boxSum_tendsto_zero_traceKernel_source_core
      f hmajorant

/-- Source scalar cancellation for the real part of the oriented completed
prime-power autocorrelation box sums. -/
theorem zetaCompletedPrimePowerAutocorrelation_oriented_boxSum_re_tendsto_zero_traceKernel_source_core
    (f : ZetaAdmissibleFunction)
    (hmajorant : Summable (fun index : ZetaPrimePowerIndex =>
      zetaCompletedPrimeSpectralCoordinateMajorant index f)) :
    Filter.Tendsto
      (fun N : ℕ =>
        Complex.re
          (∑ index in ZetaPrimePowerIndex.box N,
            zetaCompletedPrimePowerAutocorrelationOrientedCrossCoordinate
              index f))
      Filter.atTop
      (nhds 0) := by
  exact
    zetaCompletedPrimePowerAutocorrelation_oriented_boxSum_re_tendsto_zero_residueLedger_source
      f
      (zetaCompletedPrimePowerAutocorrelationLedgerCancellation_traceKernel_window_source_core
        f hmajorant)

/-- Pointwise normalization of the real-shadow box window. -/
theorem zetaCompletedPrimePowerAutocorrelation_oriented_boxRealShadowWindow_eq_complexTwoReBoxSum_source_core
    (N : ℕ) (f : ZetaAdmissibleFunction) :
    (((2 : ℝ) *
      Complex.re
        (∑ index in ZetaPrimePowerIndex.box N,
          zetaCompletedPrimePowerAutocorrelationOrientedCrossCoordinate
            index f) : ℝ) : ℂ) =
      ∑ index in ZetaPrimePowerIndex.box N,
        (2 : ℝ) *
          (Complex.re
            (zetaCompletedPrimePowerAutocorrelationOrientedCrossCoordinate
              index f) : ℂ) := by
  have hbox :
      zetaCompletedPrimePowerAutocorrelationOrientedCrossBoxSum N f =
        ∑ index in ZetaPrimePowerIndex.box N,
          zetaCompletedPrimePowerAutocorrelationOrientedCrossCoordinate
            index f := by
    exact Eq.refl
      (∑ index in ZetaPrimePowerIndex.box N,
        zetaCompletedPrimePowerAutocorrelationOrientedCrossCoordinate
          index f)
  have hmul :
      (((2 : ℝ) *
        Complex.re
          (∑ index in ZetaPrimePowerIndex.box N,
            zetaCompletedPrimePowerAutocorrelationOrientedCrossCoordinate
              index f) : ℝ) : ℂ) =
        ((2 : ℝ) : ℂ) *
          (Complex.re
            (∑ index in ZetaPrimePowerIndex.box N,
              zetaCompletedPrimePowerAutocorrelationOrientedCrossCoordinate
                index f) : ℂ) := by
    exact Complex.ofReal_mul
      (2 : ℝ)
      (Complex.re
        (∑ index in ZetaPrimePowerIndex.box N,
          zetaCompletedPrimePowerAutocorrelationOrientedCrossCoordinate
            index f))
  have hboxRe :
      ((2 : ℝ) : ℂ) *
          (Complex.re
            (∑ index in ZetaPrimePowerIndex.box N,
              zetaCompletedPrimePowerAutocorrelationOrientedCrossCoordinate
                index f) : ℂ) =
        ((2 : ℝ) : ℂ) *
          (Complex.re
            (zetaCompletedPrimePowerAutocorrelationOrientedCrossBoxSum
              N f) : ℂ) := by
    exact congrArg
      (fun value : ℂ => ((2 : ℝ) : ℂ) * (Complex.re value : ℂ))
      hbox.symm
  have hshadow :
      ((2 : ℝ) : ℂ) *
          (Complex.re
            (zetaCompletedPrimePowerAutocorrelationOrientedCrossBoxSum
              N f) : ℂ) =
        ∑ index in ZetaPrimePowerIndex.box N,
          (2 : ℝ) *
            (Complex.re
              (zetaCompletedPrimePowerAutocorrelationOrientedCrossCoordinate
                index f) : ℂ) := by
    exact
      (zetaCompletedPrimePowerAutocorrelation_oriented_boxRealShadow_eq_two_re_boxSum_source
        N f).symm
  exact Eq.trans hmul (Eq.trans hboxRe hshadow)

/-- Source rectangular real-shadow cancellation for the oriented
prime-power face. -/
theorem zetaCompletedPrimePowerAutocorrelation_oriented_boxRealShadow_tendsto_zero_traceKernel_source_core
    (f : ZetaAdmissibleFunction) :
    Filter.Tendsto
      (fun N : ℕ =>
        ∑ index in ZetaPrimePowerIndex.box N,
          (2 : ℝ) *
            (Complex.re
              (zetaCompletedPrimePowerAutocorrelationOrientedCrossCoordinate
                index f) : ℂ))
      Filter.atTop
      (nhds 0) := by
  have hreal :
      Filter.Tendsto
        (fun N : ℕ =>
          Complex.re
            (∑ index in ZetaPrimePowerIndex.box N,
              zetaCompletedPrimePowerAutocorrelationOrientedCrossCoordinate
                index f))
        Filter.atTop
        (nhds 0) :=
    zetaCompletedPrimePowerAutocorrelation_oriented_boxSum_re_tendsto_zero_traceKernel_source_core
      f
  have htwo :
      Filter.Tendsto
        (fun N : ℕ =>
          (2 : ℝ) *
            Complex.re
              (∑ index in ZetaPrimePowerIndex.box N,
                zetaCompletedPrimePowerAutocorrelationOrientedCrossCoordinate
                  index f))
        Filter.atTop
        (nhds ((2 : ℝ) * 0)) :=
    Filter.Tendsto.const_mul (2 : ℝ) hreal
  have htwoZero :
      Filter.Tendsto
        (fun N : ℕ =>
          (2 : ℝ) *
            Complex.re
              (∑ index in ZetaPrimePowerIndex.box N,
                zetaCompletedPrimePowerAutocorrelationOrientedCrossCoordinate
                  index f))
        Filter.atTop
        (nhds 0) := by
    exact Eq.subst
      (motive := fun value : ℝ =>
        Filter.Tendsto
          (fun N : ℕ =>
            (2 : ℝ) *
              Complex.re
                (∑ index in ZetaPrimePowerIndex.box N,
                  zetaCompletedPrimePowerAutocorrelationOrientedCrossCoordinate
                    index f))
          Filter.atTop
          (nhds value))
      (mul_zero (2 : ℝ))
      htwo
  have hcomplex :
      Filter.Tendsto
        (fun N : ℕ =>
          (((2 : ℝ) *
            Complex.re
              (∑ index in ZetaPrimePowerIndex.box N,
                zetaCompletedPrimePowerAutocorrelationOrientedCrossCoordinate
                  index f) : ℝ) : ℂ))
        Filter.atTop
        (nhds (0 : ℂ)) :=
    (Complex.continuous_ofReal.tendsto (0 : ℝ)).comp htwoZero
  have hwindow :
      (fun N : ℕ =>
        (((2 : ℝ) *
          Complex.re
            (∑ index in ZetaPrimePowerIndex.box N,
              zetaCompletedPrimePowerAutocorrelationOrientedCrossCoordinate
                index f) : ℝ) : ℂ)) =
        fun N : ℕ =>
          ∑ index in ZetaPrimePowerIndex.box N,
            (2 : ℝ) *
              (Complex.re
                (zetaCompletedPrimePowerAutocorrelationOrientedCrossCoordinate
                  index f) : ℂ) := by
    funext N
    exact
      zetaCompletedPrimePowerAutocorrelation_oriented_boxRealShadowWindow_eq_complexTwoReBoxSum_source_core
        N f
  exact Eq.subst
    (motive := fun stream : ℕ → ℂ =>
      Filter.Tendsto stream Filter.atTop (nhds 0))
    hwindow
    hcomplex

/-- Source paired oriented-face rectangular cancellation for completed
prime-power autocorrelation coordinates. -/
theorem zetaCompletedPrimePowerAutocorrelation_oriented_add_opposite_boxSum_tendsto_zero_traceKernel_source_core
    (f : ZetaAdmissibleFunction)
    (hmajorant : Summable (fun index : ZetaPrimePowerIndex =>
      zetaCompletedPrimeSpectralCoordinateMajorant index f)) :
    Filter.Tendsto
      (fun N : ℕ =>
        ∑ index in ZetaPrimePowerIndex.box N,
          (zetaCompletedPrimePowerAutocorrelationOrientedCrossCoordinate
              index f +
            zetaCompletedPrimePowerAutocorrelationOppositeOrientedCrossCoordinate
              index f))
      Filter.atTop
      (nhds 0) := by
  exact
    zetaCompletedPrimePowerAutocorrelationLedgerCancellation_traceKernel_window_source_core
      f hmajorant

/-- Source completed prime-power autocorrelation contour-ledger cancellation. -/
theorem zetaCompletedPrimePowerAutocorrelationLedgerCancellation_traceKernel_source_core
    (f : ZetaAdmissibleFunction) :
    ZetaCompletedPrimePowerAutocorrelationLedgerCancellation f := by
  exact
    zetaCompletedPrimePowerAutocorrelation_oriented_add_opposite_boxSum_tendsto_zero_traceKernel_source_core
      f hmajorant

/-- Source scalar cancellation for the real part of the oriented completed
prime-power autocorrelation box sums. -/
theorem zetaCompletedPrimePowerAutocorrelation_oriented_boxSum_re_tendsto_zero_realShadow_source_core
    (f : ZetaAdmissibleFunction) :
    Filter.Tendsto
      (fun N : ℕ =>
        Complex.re
          (∑ index in ZetaPrimePowerIndex.box N,
            zetaCompletedPrimePowerAutocorrelationOrientedCrossCoordinate
              index f))
      Filter.atTop
      (nhds 0) := by
  exact
    zetaCompletedPrimePowerAutocorrelation_oriented_boxSum_re_tendsto_zero_residueLedger_source
      f
      (zetaCompletedPrimePowerAutocorrelationLedgerCancellation_traceKernel_source_core
        f)

/-- Source rectangular real-shadow cancellation for the oriented prime-power
face. -/
theorem zetaCompletedPrimePowerAutocorrelation_oriented_boxRealShadow_tendsto_zero_realShadow_source_core
    (f : ZetaAdmissibleFunction) :
    Filter.Tendsto
      (fun N : ℕ =>
        ∑ index in ZetaPrimePowerIndex.box N,
          (2 : ℝ) *
            (Complex.re
              (zetaCompletedPrimePowerAutocorrelationOrientedCrossCoordinate
                index f) : ℂ))
      Filter.atTop
      (nhds 0) := by
  have hreal :
      Filter.Tendsto
        (fun N : ℕ =>
          Complex.re
            (∑ index in ZetaPrimePowerIndex.box N,
              zetaCompletedPrimePowerAutocorrelationOrientedCrossCoordinate
                index f))
        Filter.atTop
        (nhds 0) :=
    zetaCompletedPrimePowerAutocorrelation_oriented_boxSum_re_tendsto_zero_realShadow_source_core
      f
  have htwo :
      Filter.Tendsto
        (fun N : ℕ =>
          (2 : ℝ) *
            Complex.re
              (∑ index in ZetaPrimePowerIndex.box N,
                zetaCompletedPrimePowerAutocorrelationOrientedCrossCoordinate
                  index f))
        Filter.atTop
        (nhds ((2 : ℝ) * 0)) :=
    Filter.Tendsto.const_mul (2 : ℝ) hreal
  have htwoZero :
      Filter.Tendsto
        (fun N : ℕ =>
          (2 : ℝ) *
            Complex.re
              (∑ index in ZetaPrimePowerIndex.box N,
                zetaCompletedPrimePowerAutocorrelationOrientedCrossCoordinate
                  index f))
        Filter.atTop
        (nhds 0) := by
    exact Eq.subst
      (motive := fun value : ℝ =>
        Filter.Tendsto
          (fun N : ℕ =>
            (2 : ℝ) *
              Complex.re
                (∑ index in ZetaPrimePowerIndex.box N,
                  zetaCompletedPrimePowerAutocorrelationOrientedCrossCoordinate
                    index f))
          Filter.atTop
          (nhds value))
      (mul_zero (2 : ℝ))
      htwo
  have hcomplex :
      Filter.Tendsto
        (fun N : ℕ =>
          (((2 : ℝ) *
            Complex.re
              (∑ index in ZetaPrimePowerIndex.box N,
                zetaCompletedPrimePowerAutocorrelationOrientedCrossCoordinate
                  index f) : ℝ) : ℂ))
        Filter.atTop
        (nhds (0 : ℂ)) :=
    (Complex.continuous_ofReal.tendsto (0 : ℝ)).comp htwoZero
  have hwindow :
      (fun N : ℕ =>
        (((2 : ℝ) *
          Complex.re
            (∑ index in ZetaPrimePowerIndex.box N,
              zetaCompletedPrimePowerAutocorrelationOrientedCrossCoordinate
                index f) : ℝ) : ℂ)) =
        fun N : ℕ =>
          ∑ index in ZetaPrimePowerIndex.box N,
            (2 : ℝ) *
              (Complex.re
                (zetaCompletedPrimePowerAutocorrelationOrientedCrossCoordinate
                  index f) : ℂ) := by
    funext N
    exact
      zetaCompletedPrimePowerAutocorrelation_oriented_boxRealShadowWindow_eq_complexTwoReBoxSum_source_core
        N f
  exact Eq.subst
    (motive := fun stream : ℕ → ℂ =>
      Filter.Tendsto stream Filter.atTop (nhds 0))
    hwindow
    hcomplex

/-- Source rectangular completed-contour cancellation for the two oriented
prime-power faces. -/
theorem zetaCompletedPrimePowerAutocorrelation_oriented_add_opposite_boxSum_tendsto_zero_realShadow_source_core
    (f : ZetaAdmissibleFunction) :
    Filter.Tendsto
      (fun N : ℕ =>
        ∑ index in ZetaPrimePowerIndex.box N,
          (zetaCompletedPrimePowerAutocorrelationOrientedCrossCoordinate
              index f +
            zetaCompletedPrimePowerAutocorrelationOppositeOrientedCrossCoordinate
              index f))
      Filter.atTop
      (nhds 0) := by
  have hrealShadow :
      Filter.Tendsto
        (fun N : ℕ =>
          ∑ index in ZetaPrimePowerIndex.box N,
            (2 : ℝ) *
              (Complex.re
                (zetaCompletedPrimePowerAutocorrelationOrientedCrossCoordinate
                  index f) : ℂ))
        Filter.atTop
        (nhds 0) :=
    zetaCompletedPrimePowerAutocorrelation_oriented_boxRealShadow_tendsto_zero_realShadow_source_core
      f
  have hfun :
      (fun N : ℕ =>
        ∑ index in ZetaPrimePowerIndex.box N,
          (zetaCompletedPrimePowerAutocorrelationOrientedCrossCoordinate
              index f +
            zetaCompletedPrimePowerAutocorrelationOppositeOrientedCrossCoordinate
              index f)) =
        fun N : ℕ =>
          ∑ index in ZetaPrimePowerIndex.box N,
            (2 : ℝ) *
              (Complex.re
                (zetaCompletedPrimePowerAutocorrelationOrientedCrossCoordinate
                  index f) : ℂ) := by
    funext N
    exact
      zetaCompletedPrimePowerAutocorrelation_oriented_add_opposite_boxSum_eq_realShadow
        N f
  exact Eq.subst
    (motive := fun stream : ℕ → ℂ =>
      Filter.Tendsto stream Filter.atTop (nhds 0))
    hfun.symm
    hrealShadow

/-- Source construction of the completed prime-power autocorrelation ledger
cancellation consumed by the real-shadow contour-tomography theorem. -/
theorem zetaCompletedPrimePowerAutocorrelationLedgerCancellation_realShadow_source_core
    (f : ZetaAdmissibleFunction) :
    ZetaCompletedPrimePowerAutocorrelationLedgerCancellation f := by
  exact
    zetaCompletedPrimePowerAutocorrelationLedgerCancellation_traceKernel_source_core
      f

/-- The source rectangular ledger gives `HasSum` cancellation for the paired
completed two-face coordinate stream once the oriented face is summable. -/
theorem zetaCompletedPrimePowerAutocorrelationTwoFaceCoordinate_hasSum_zero_of_ledger_source_core
    (f : ZetaAdmissibleFunction)
    (horiented :
      Summable
        (fun index : ZetaPrimePowerIndex =>
          zetaCompletedPrimePowerAutocorrelationOrientedCrossCoordinate
            index f)) :
    HasSum
      (fun index : ZetaPrimePowerIndex =>
        zetaCompletedPrimePowerAutocorrelationOrientedCrossCoordinate
            index f +
          zetaCompletedPrimePowerAutocorrelationOppositeOrientedCrossCoordinate
            index f)
      0 := by
  let oriented : ZetaPrimePowerIndex → ℂ :=
    fun index : ZetaPrimePowerIndex =>
      zetaCompletedPrimePowerAutocorrelationOrientedCrossCoordinate
        index f
  let opposite : ZetaPrimePowerIndex → ℂ :=
    fun index : ZetaPrimePowerIndex =>
      zetaCompletedPrimePowerAutocorrelationOppositeOrientedCrossCoordinate
        index f
  let paired : ZetaPrimePowerIndex → ℂ :=
    fun index : ZetaPrimePowerIndex => oriented index + opposite index
  have horientedLocal : Summable oriented := by
    exact horiented
  have hoppositeLocal : Summable opposite := by
    exact horientedLocal.star.congr
      (fun index : ZetaPrimePowerIndex =>
        zetaCompletedPrimePowerAutocorrelationOrientedCrossCoordinate_star_eq_opposite
          index f)
  have hpairedSummable : Summable paired :=
    horientedLocal.add hoppositeLocal
  have hboxTsum :
      Filter.Tendsto
        (fun N : ℕ =>
          ∑ index in ZetaPrimePowerIndex.box N, paired index)
        Filter.atTop
        (nhds (∑' index : ZetaPrimePowerIndex, paired index)) :=
    ZetaPrimePowerIndex.tendsto_sum_box_of_hasSum_complex
      paired
      (∑' index : ZetaPrimePowerIndex, paired index)
      hpairedSummable.hasSum
  have hboxZero :
      Filter.Tendsto
        (fun N : ℕ =>
          ∑ index in ZetaPrimePowerIndex.box N, paired index)
        Filter.atTop
        (nhds 0) :=
    zetaCompletedPrimePowerAutocorrelationLedgerCancellation_realShadow_source_core
      f
  have htotal :
      (∑' index : ZetaPrimePowerIndex, paired index) = 0 :=
    tendsto_nhds_unique hboxTsum hboxZero
  exact Eq.subst
    (motive := fun value : ℂ => HasSum paired value)
    htotal
    hpairedSummable.hasSum

/-- Source contour-ledger cancellation for the oriented real shadow. -/
theorem zetaCompletedPrimePowerAutocorrelation_oriented_boxRealShadow_tendsto_zero_contourLedger_source_core
    (f : ZetaAdmissibleFunction) :
    Filter.Tendsto
      (fun N : ℕ =>
        ∑ index in ZetaPrimePowerIndex.box N,
          ((2 : ℝ) * Complex.re
            (zetaCompletedPrimePowerAutocorrelationOrientedCrossCoordinate
              index f) : ℂ))
      Filter.atTop
      (nhds 0) := by
  exact
    zetaCompletedPrimePowerAutocorrelation_oriented_boxRealShadow_tendsto_zero_contourTomography
      f
      (zetaCompletedPrimePowerAutocorrelationLedgerCancellation_realShadow_source_core
        f)

/-- Source rectangular cancellation for paired two-face coordinates. -/
theorem zetaCompletedPrimePowerAutocorrelationTwoFaceCoordinate_boxSum_tendsto_zero_contourLedger_source_core
    (f : ZetaAdmissibleFunction) :
    Filter.Tendsto
      (fun N : ℕ =>
        ∑ index in ZetaPrimePowerIndex.box N,
          (zetaCompletedPrimePowerAutocorrelationOrientedCrossCoordinate
              index f +
            zetaCompletedPrimePowerAutocorrelationOppositeOrientedCrossCoordinate
              index f))
      Filter.atTop
      (nhds 0) := by
  exact
    zetaCompletedPrimePowerAutocorrelationLedgerCancellation_realShadow_source_core
      f

end ZetaAdmissibleFunction

end
end LFunctions
end Boundary
