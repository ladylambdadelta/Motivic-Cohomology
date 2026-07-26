import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaAdmissibleSpectralInterpolation.ZetaAdmissiblePaleyWiener.ZetaExplicitFormulaAnalyticCore.OwnerParts.BoundaryCancellationRealShadowParts.TwoFaceWindowParts.PairedTraceKernel

/-!
# Boundary cancellation real-shadow source

This file owns the scalar real-part vanishing input for the completed
prime-power boundary cancellation lane.
-/

namespace Boundary
namespace LFunctions

noncomputable section

namespace ZetaAdmissibleFunction

/-- The real-part stream of the oriented completed prime-power
autocorrelation coordinates has total sum zero. -/
def ZetaCompletedPrimePowerAutocorrelationOrientedRealPartHasSumZero
    (f : ZetaAdmissibleFunction) : Prop :=
  HasSum
    (fun index : ZetaPrimePowerIndex =>
      Complex.re
        (zetaCompletedPrimePowerAutocorrelationOrientedCrossCoordinate
          index f))
    0

/-- Source scalar summation cancellation for the real part of the oriented
completed prime-power autocorrelation coordinate stream. -/
theorem zetaCompletedPrimePowerAutocorrelation_oriented_realPart_hasSum_zero_contour_source
    (f : ZetaAdmissibleFunction)
    (hmajorant :
      Summable
        (fun index : ZetaPrimePowerIndex =>
          zetaCompletedPrimeSpectralCoordinateMajorant index f)) :
    ZetaCompletedPrimePowerAutocorrelationOrientedRealPartHasSumZero f := by
  let oriented : ZetaPrimePowerIndex → ℂ :=
    fun index : ZetaPrimePowerIndex =>
      zetaCompletedPrimePowerAutocorrelationOrientedCrossCoordinate index f
  have horiented :
      Summable oriented :=
    zetaCompletedPrimePowerAutocorrelationOrientedCrossCoordinate_summable_of_spectralMajorant
      f
      hmajorant
  have hledger :
      ZetaCompletedPrimePowerAutocorrelationLedgerCancellation f :=
    zetaCompletedPrimePowerAutocorrelationLedgerCancellation_pairedTraceKernel_source
      f hmajorant
  have hcomplex :
      HasSum oriented (∑' index : ZetaPrimePowerIndex, oriented index) :=
    horiented.hasSum
  have hrealRaw :
      HasSum
        (fun index : ZetaPrimePowerIndex =>
          Complex.reCLM (oriented index))
        (Complex.reCLM (∑' index : ZetaPrimePowerIndex, oriented index)) :=
    hcomplex.mapL Complex.reCLM
  have hpoint :
      (fun index : ZetaPrimePowerIndex =>
        Complex.reCLM (oriented index)) =
      (fun index : ZetaPrimePowerIndex =>
        Complex.re
          (zetaCompletedPrimePowerAutocorrelationOrientedCrossCoordinate
            index f)) := by
    funext index
    exact Complex.reCLM_apply (oriented index)
  have hlimit :
      Complex.reCLM (∑' index : ZetaPrimePowerIndex, oriented index) = 0 := by
    exact Eq.trans
      (Complex.reCLM_apply (∑' index : ZetaPrimePowerIndex, oriented index))
      (zetaCompletedPrimePowerAutocorrelation_oriented_tsum_re_eq_zero_residueLedger_source
        f hledger horiented)
  exact Eq.subst
    (motive := fun series : ZetaPrimePowerIndex → ℝ =>
      HasSum series 0)
    hpoint
    (Eq.subst
      (motive := fun value : ℝ =>
        HasSum
          (fun index : ZetaPrimePowerIndex =>
            Complex.reCLM (oriented index))
          value)
      hlimit
      hrealRaw)

/-- Explicit diagonal-debt real-coordinate `HasSum` inputs give scalar
summation cancellation for the real part of the oriented completed prime-power
autocorrelation coordinate stream. -/
theorem zetaCompletedPrimePowerAutocorrelation_oriented_realPart_hasSum_zero_of_diagonalDebtCoordinate_re_hasSum_contour_source
    (f : ZetaAdmissibleFunction) (C Creflect : ℝ)
    (hhasSum :
      HasSum
        (fun index : ZetaPrimePowerIndex =>
          Complex.re
            (zetaCompletedPrimeDefectKernelDiagonalDebtCoordinate index f))
        C)
    (hhasSumReflect :
      HasSum
        (fun index : ZetaPrimePowerIndex =>
          Complex.re
            (zetaCompletedPrimeDefectKernelDiagonalDebtCoordinate
              index (ZetaAdmissibleFunction.reflect f)))
        Creflect) :
    ZetaCompletedPrimePowerAutocorrelationOrientedRealPartHasSumZero f := by
  let oriented : ZetaPrimePowerIndex → ℂ :=
    fun index : ZetaPrimePowerIndex =>
      zetaCompletedPrimePowerAutocorrelationOrientedCrossCoordinate index f
  have hmajorant :
      Summable
        (fun index : ZetaPrimePowerIndex =>
          zetaCompletedPrimeSpectralCoordinateMajorant index f) :=
    zetaCompletedPrimeSpectralCoordinateMajorant_summable_of_diagonalDebtCoordinate_re_hasSum_positiveRealWindowLimit
      f C Creflect hhasSum hhasSumReflect
  have horiented :
      Summable oriented :=
    zetaCompletedPrimePowerAutocorrelationOrientedCrossCoordinate_summable_of_spectralMajorant
      f hmajorant
  have hledger :
      ZetaCompletedPrimePowerAutocorrelationLedgerCancellation f :=
    zetaCompletedPrimePowerAutocorrelationLedgerCancellation_pairedTraceKernel_source
      f hmajorant
  have hcomplex :
      HasSum oriented (∑' index : ZetaPrimePowerIndex, oriented index) :=
    horiented.hasSum
  have hrealRaw :
      HasSum
        (fun index : ZetaPrimePowerIndex =>
          Complex.reCLM (oriented index))
        (Complex.reCLM (∑' index : ZetaPrimePowerIndex, oriented index)) :=
    hcomplex.mapL Complex.reCLM
  have hpoint :
      (fun index : ZetaPrimePowerIndex =>
        Complex.reCLM (oriented index)) =
      (fun index : ZetaPrimePowerIndex =>
        Complex.re
          (zetaCompletedPrimePowerAutocorrelationOrientedCrossCoordinate
            index f)) := by
    funext index
    exact Complex.reCLM_apply (oriented index)
  have hlimit :
      Complex.reCLM (∑' index : ZetaPrimePowerIndex, oriented index) = 0 := by
    exact Eq.trans
      (Complex.reCLM_apply (∑' index : ZetaPrimePowerIndex, oriented index))
      (zetaCompletedPrimePowerAutocorrelation_oriented_tsum_re_eq_zero_residueLedger_source
        f hledger horiented)
  exact Eq.subst
    (motive := fun series : ZetaPrimePowerIndex → ℝ =>
      HasSum series 0)
    hpoint
    (Eq.subst
      (motive := fun value : ℝ =>
        HasSum
          (fun index : ZetaPrimePowerIndex =>
            Complex.reCLM (oriented index))
          value)
      hlimit
      hrealRaw)

/-- Source summability for the real part of the oriented completed prime-power
autocorrelation coordinate stream. -/
theorem zetaCompletedPrimePowerAutocorrelation_oriented_realPart_summable_source
    (f : ZetaAdmissibleFunction)
    (hmajorant : Summable (fun index : ZetaPrimePowerIndex =>
      zetaCompletedPrimeSpectralCoordinateMajorant index f)) :
    Summable
      (fun index : ZetaPrimePowerIndex =>
        Complex.re
          (zetaCompletedPrimePowerAutocorrelationOrientedCrossCoordinate
            index f)) := by
  exact
    (zetaCompletedPrimePowerAutocorrelation_oriented_realPart_hasSum_zero_contour_source
      f hmajorant).summable

/-- Source vanishing of the completed sum of oriented real parts. -/
theorem zetaCompletedPrimePowerAutocorrelation_oriented_realPart_tsum_eq_zero_source
    (f : ZetaAdmissibleFunction)
    (hmajorant : Summable (fun index : ZetaPrimePowerIndex =>
      zetaCompletedPrimeSpectralCoordinateMajorant index f)) :
    (∑' index : ZetaPrimePowerIndex,
        Complex.re
          (zetaCompletedPrimePowerAutocorrelationOrientedCrossCoordinate
            index f)) = 0 := by
  exact
    (zetaCompletedPrimePowerAutocorrelation_oriented_realPart_hasSum_zero_contour_source
      f hmajorant).tsum_eq

/-- Source scalar summation cancellation for the real part of the oriented
completed prime-power autocorrelation coordinate stream. -/
theorem zetaCompletedPrimePowerAutocorrelation_oriented_realPart_hasSum_zero_source
    (f : ZetaAdmissibleFunction)
    (hmajorant : Summable (fun index : ZetaPrimePowerIndex =>
      zetaCompletedPrimeSpectralCoordinateMajorant index f)) :
    ZetaCompletedPrimePowerAutocorrelationOrientedRealPartHasSumZero f := by
  exact
    zetaCompletedPrimePowerAutocorrelation_oriented_realPart_hasSum_zero_contour_source
      f hmajorant

/-- Scalar contour cancellation of the oriented completed prime-power
autocorrelation windows. -/
def ZetaCompletedPrimePowerAutocorrelationOrientedScalarContourCancellation
    (f : ZetaAdmissibleFunction) : Prop :=
  Filter.Tendsto
    (fun N : ℕ =>
      zetaCompletedPrimePowerAutocorrelationOrientedCrossBoxRealPart
        N f)
    Filter.atTop
    (nhds 0)

/-- Source scalar contour cancellation for the oriented completed prime-power
autocorrelation windows. -/
theorem zetaCompletedPrimePowerAutocorrelation_oriented_scalarContourCancellation_source
    (f : ZetaAdmissibleFunction)
    (hmajorant : Summable (fun index : ZetaPrimePowerIndex =>
      zetaCompletedPrimeSpectralCoordinateMajorant index f)) :
    ZetaCompletedPrimePowerAutocorrelationOrientedScalarContourCancellation f := by
  have hsum :
      HasSum
        (fun index : ZetaPrimePowerIndex =>
          Complex.re
            (zetaCompletedPrimePowerAutocorrelationOrientedCrossCoordinate
              index f))
        0 :=
    zetaCompletedPrimePowerAutocorrelation_oriented_realPart_hasSum_zero_source
      f hmajorant
  have hbox :
      Filter.Tendsto
        (fun N : ℕ =>
          ∑ index in ZetaPrimePowerIndex.box N,
            Complex.re
              (zetaCompletedPrimePowerAutocorrelationOrientedCrossCoordinate
                index f))
        Filter.atTop
        (nhds 0) :=
    hsum.comp ZetaPrimePowerIndex.box_tendsto_atTop
  have hwindow :
      (fun N : ℕ =>
        ∑ index in ZetaPrimePowerIndex.box N,
          Complex.re
            (zetaCompletedPrimePowerAutocorrelationOrientedCrossCoordinate
              index f)) =
      (fun N : ℕ =>
        zetaCompletedPrimePowerAutocorrelationOrientedCrossBoxRealPart
          N f) := by
    funext N
    unfold zetaCompletedPrimePowerAutocorrelationOrientedCrossBoxRealPart
    unfold zetaCompletedPrimePowerAutocorrelationOrientedCrossBoxSum
    exact
      (Complex.re_sum
        (ZetaPrimePowerIndex.box N)
        (fun index : ZetaPrimePowerIndex =>
          zetaCompletedPrimePowerAutocorrelationOrientedCrossCoordinate
            index f)).symm
  exact Eq.subst
    (motive := fun window : ℕ → ℝ =>
      Filter.Tendsto window Filter.atTop (nhds 0))
    hwindow
    hbox

/-- Source scalar cancellation for the real part of the oriented completed
prime-power autocorrelation box sums. -/
theorem zetaCompletedPrimePowerAutocorrelation_oriented_boxSum_re_tendsto_zero_contourLedger_source
    (f : ZetaAdmissibleFunction) :
    Filter.Tendsto
      (fun N : ℕ =>
        Complex.re
          (∑ index in ZetaPrimePowerIndex.box N,
            zetaCompletedPrimePowerAutocorrelationOrientedCrossCoordinate
              index f))
      Filter.atTop
      (nhds 0) := by
  have hnamed :
      Filter.Tendsto
        (fun N : ℕ =>
          zetaCompletedPrimePowerAutocorrelationOrientedCrossBoxRealPart
            N f)
        Filter.atTop
        (nhds 0) :=
    zetaCompletedPrimePowerAutocorrelation_oriented_scalarContourCancellation_source
      f
  have hwindow :
      (fun N : ℕ =>
        zetaCompletedPrimePowerAutocorrelationOrientedCrossBoxRealPart
          N f) =
      (fun N : ℕ =>
        Complex.re
          (∑ index in ZetaPrimePowerIndex.box N,
            zetaCompletedPrimePowerAutocorrelationOrientedCrossCoordinate
              index f)) := by
    funext N
    rfl
  exact Eq.subst
    (motive := fun window : ℕ → ℝ =>
      Filter.Tendsto window Filter.atTop (nhds 0))
    hwindow
    hnamed

/-- Scalar real-part cancellation gives the complex real-shadow cancellation
used by the paired two-face coordinate stream. -/
theorem zetaCompletedPrimePowerAutocorrelation_oriented_realShadowWindow_tendsto_zero_of_boxSum_re
    (f : ZetaAdmissibleFunction)
    (hreal :
      Filter.Tendsto
        (fun N : ℕ =>
          Complex.re
            (∑ index in ZetaPrimePowerIndex.box N,
              zetaCompletedPrimePowerAutocorrelationOrientedCrossCoordinate
                index f))
        Filter.atTop
        (nhds 0)) :
    Filter.Tendsto
      (fun N : ℕ =>
        ∑ index in ZetaPrimePowerIndex.box N,
          ((2 : ℝ) *
            Complex.re
              (zetaCompletedPrimePowerAutocorrelationOrientedCrossCoordinate
                index f) : ℂ))
      Filter.atTop
      (nhds 0) := by
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
  have hzero : ((2 : ℝ) * 0) = 0 :=
    mul_zero (2 : ℝ)
  have htwoZero :
      Filter.Tendsto
        (fun N : ℕ =>
          (2 : ℝ) *
            Complex.re
              (∑ index in ZetaPrimePowerIndex.box N,
                zetaCompletedPrimePowerAutocorrelationOrientedCrossCoordinate
                  index f))
        Filter.atTop
        (nhds 0) :=
    Eq.subst
      (motive := fun limit : ℝ =>
        Filter.Tendsto
          (fun N : ℕ =>
            (2 : ℝ) *
              Complex.re
                (∑ index in ZetaPrimePowerIndex.box N,
                  zetaCompletedPrimePowerAutocorrelationOrientedCrossCoordinate
                    index f))
          Filter.atTop
          (nhds limit))
      hzero
      htwo
  have hofReal :
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
  have hpoint :
      (fun N : ℕ =>
        (((2 : ℝ) *
          Complex.re
            (∑ index in ZetaPrimePowerIndex.box N,
              zetaCompletedPrimePowerAutocorrelationOrientedCrossCoordinate
                index f) : ℝ) : ℂ)) =
      (fun N : ℕ =>
        ∑ index in ZetaPrimePowerIndex.box N,
          ((2 : ℝ) *
            Complex.re
              (zetaCompletedPrimePowerAutocorrelationOrientedCrossCoordinate
                index f) : ℂ)) := by
    funext N
    have hbox :
        zetaCompletedPrimePowerAutocorrelationOrientedCrossBoxSum N f =
          ∑ index in ZetaPrimePowerIndex.box N,
            zetaCompletedPrimePowerAutocorrelationOrientedCrossCoordinate
              index f := by
      exact Eq.refl _
    calc
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
      _ =
          ((2 : ℝ) : ℂ) *
            (Complex.re
              (zetaCompletedPrimePowerAutocorrelationOrientedCrossBoxSum
                N f) : ℂ) := by
        exact congrArg
          (fun value : ℂ => ((2 : ℝ) : ℂ) * (Complex.re value : ℂ))
          hbox.symm
      _ =
          ∑ index in ZetaPrimePowerIndex.box N,
            ((2 : ℝ) *
              Complex.re
                (zetaCompletedPrimePowerAutocorrelationOrientedCrossCoordinate
                  index f) : ℂ) := by
        exact
          (zetaCompletedPrimePowerAutocorrelation_oriented_boxRealShadow_eq_two_re_boxSum_source
            N f).symm
  exact Eq.subst
    (motive := fun window : ℕ → ℂ =>
      Filter.Tendsto window Filter.atTop (nhds 0))
    hpoint
    hofReal

/-- Source contour-ledger cancellation for the oriented real shadow of the
completed autocorrelation prime-power face. -/
theorem zetaCompletedPrimePowerAutocorrelationOrientedRealShadowBoxSum_tendsto_zero_contourLedger_source
    (f : ZetaAdmissibleFunction) :
    Filter.Tendsto
      (fun N : ℕ =>
        ∑ index in ZetaPrimePowerIndex.box N,
          ((2 : ℝ) *
            Complex.re
              (zetaCompletedPrimePowerAutocorrelationOrientedCrossCoordinate
                index f) : ℂ))
      Filter.atTop
      (nhds 0) := by
  exact
    zetaCompletedPrimePowerAutocorrelation_oriented_realShadowWindow_tendsto_zero_of_boxSum_re
      f
      (zetaCompletedPrimePowerAutocorrelation_oriented_boxSum_re_tendsto_zero_contourLedger_source
        f)

end ZetaAdmissibleFunction

end
end LFunctions
end Boundary
