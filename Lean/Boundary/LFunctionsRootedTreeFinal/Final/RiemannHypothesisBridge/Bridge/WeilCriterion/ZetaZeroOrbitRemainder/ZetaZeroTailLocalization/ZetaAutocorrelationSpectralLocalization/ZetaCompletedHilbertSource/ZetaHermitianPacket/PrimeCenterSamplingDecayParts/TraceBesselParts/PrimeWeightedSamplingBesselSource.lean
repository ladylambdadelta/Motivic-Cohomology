import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaCompletedHilbertSource.ZetaHermitianPacket.PrimeCenterSamplingDecayParts.TraceBesselParts.PrimeWeightedSamplingBesselCore
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaCompletedHilbertSource.ZetaHermitianPacket.PrimeCenterSamplingDecayParts.TraceBesselParts.PrimeWeightedSamplingTraceEnergy
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaCompletedHilbertSource.ZetaHermitianPacket.PrimeCenterSamplingSpectralOwner
import Mathlib.Order.Filter.Defs
import Mathlib.Topology.Algebra.InfiniteSum.Order

/-!
# Prime weighted sampling Bessel source

This file owns the direct analytic Bessel source for finite weighted
prime-center sampling subtraces.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open Filter
open scoped BigOperators

namespace ZetaAdmissibleFunction

theorem zetaCompletedPrimeVerticalSpectralAmplitudeIndex_normSq_summable_owner
    (f : ZetaAdmissibleFunction) (D : ℝ) (k : ℕ)
    (hbound : VerticalPrimeCenterWeightedSpectralPolynomialBound f D k) :
    Summable
      (fun ι : ZetaPrimePowerIndex =>
        ‖zetaCompletedPrimeVerticalSpectralAmplitudeIndex ι f‖ ^ 2) := by
  have hsample :
      Summable
        (fun ι : ZetaPrimePowerIndex =>
          completedAutocorrelationSpectralTransform_verticalWeightedPrimeSampling
            ι f) :=
    completedAutocorrelationSpectralTransform_verticalWeightedPrimeSampling_summable_of_weightedVerticalBound
      f D k hbound
  exact hsample.congr
    (fun ι : ZetaPrimePowerIndex =>
      (zetaCompletedPrimeVerticalSpectralAmplitudeIndex_norm_sq_eq_weightedVerticalSample
        ι f).symm)

theorem zetaCompletedPrimeVerticalOppositeSpectralAmplitudeIndex_normSq_summable_owner
    (f : ZetaAdmissibleFunction) (D : ℝ) (k : ℕ)
    (hbound : VerticalPrimeCenterWeightedSpectralPolynomialBound
      (ZetaAdmissibleFunction.reflect f) D k) :
    Summable
      (fun ι : ZetaPrimePowerIndex =>
        ‖zetaCompletedPrimeVerticalOppositeSpectralAmplitudeIndex ι f‖ ^ 2) := by
  have hsample :
      Summable
        (fun ι : ZetaPrimePowerIndex =>
          completedAutocorrelationSpectralTransform_verticalWeightedPrimeSampling
            ι (ZetaAdmissibleFunction.reflect f)) :=
    completedAutocorrelationSpectralTransform_verticalWeightedPrimeSampling_summable_of_weightedVerticalBound
      (ZetaAdmissibleFunction.reflect f) D k hbound
  exact hsample.congr
    (fun ι : ZetaPrimePowerIndex =>
      (zetaCompletedPrimeVerticalOppositeSpectralAmplitudeIndex_norm_sq_eq_reflectedWeightedVerticalSample
        ι f).symm)

noncomputable def zetaCompletedPrimeVerticalOppositeSpectralAmplitudeIndex_normSqTraceEnergy
    (f : ZetaAdmissibleFunction) : ℝ :=
  ∑' ι : ZetaPrimePowerIndex,
    ‖zetaCompletedPrimeVerticalOppositeSpectralAmplitudeIndex ι f‖ ^ 2

theorem zetaCompletedPrimeVerticalOppositeSpectralAmplitudeIndex_normSq_hasSum_traceEnergy_owner
    (f : ZetaAdmissibleFunction) (D : ℝ) (k : ℕ)
    (hbound : VerticalPrimeCenterWeightedSpectralPolynomialBound
      (ZetaAdmissibleFunction.reflect f) D k) :
    HasSum
      (fun ι : ZetaPrimePowerIndex =>
        ‖zetaCompletedPrimeVerticalOppositeSpectralAmplitudeIndex ι f‖ ^ 2)
      (zetaCompletedPrimeVerticalOppositeSpectralAmplitudeIndex_normSqTraceEnergy f) := by
  exact
    (zetaCompletedPrimeVerticalOppositeSpectralAmplitudeIndex_normSq_summable_owner
      f D k hbound).hasSum

theorem zetaCompletedPrimeVerticalOppositeSpectralAmplitudeIndex_normSq_finiteSubtrace_le_traceEnergy_owner
    (f : ZetaAdmissibleFunction) (D : ℝ) (k : ℕ)
    (hbound : VerticalPrimeCenterWeightedSpectralPolynomialBound
      (ZetaAdmissibleFunction.reflect f) D k)
    (s : Finset ZetaPrimePowerIndex) :
    ∑ ι in s,
        ‖zetaCompletedPrimeVerticalOppositeSpectralAmplitudeIndex ι f‖ ^ 2 ≤
      zetaCompletedPrimeVerticalOppositeSpectralAmplitudeIndex_normSqTraceEnergy f := by
  exact
    sum_le_hasSum
      s
      (fun ι hι => sq_nonneg
        ‖zetaCompletedPrimeVerticalOppositeSpectralAmplitudeIndex ι f‖)
      (zetaCompletedPrimeVerticalOppositeSpectralAmplitudeIndex_normSq_hasSum_traceEnergy_owner
        f D k hbound)

theorem zetaCompletedPrimeVerticalOppositeSpectralAmplitudeIndex_normSq_windowSubtrace_le_traceEnergy_owner
    (f : ZetaAdmissibleFunction) (D : ℝ) (k N : ℕ)
    (hbound : VerticalPrimeCenterWeightedSpectralPolynomialBound
      (ZetaAdmissibleFunction.reflect f) D k) :
    ∑ ι in ZetaPrimePowerIndex.window N,
        ‖zetaCompletedPrimeVerticalOppositeSpectralAmplitudeIndex ι f‖ ^ 2 ≤
      zetaCompletedPrimeVerticalOppositeSpectralAmplitudeIndex_normSqTraceEnergy f := by
  exact
    zetaCompletedPrimeVerticalOppositeSpectralAmplitudeIndex_normSq_finiteSubtrace_le_traceEnergy_owner
      f D k hbound (ZetaPrimePowerIndex.window N)

theorem zetaCompletedPrimeVerticalOppositeSpectralAmplitudeIndex_normSq_boxSubtrace_le_traceEnergy_owner
    (f : ZetaAdmissibleFunction) (D : ℝ) (k N : ℕ)
    (hbound : VerticalPrimeCenterWeightedSpectralPolynomialBound
      (ZetaAdmissibleFunction.reflect f) D k) :
    ∑ ι in ZetaPrimePowerIndex.box N,
        ‖zetaCompletedPrimeVerticalOppositeSpectralAmplitudeIndex ι f‖ ^ 2 ≤
      zetaCompletedPrimeVerticalOppositeSpectralAmplitudeIndex_normSqTraceEnergy f := by
  exact
    zetaCompletedPrimeVerticalOppositeSpectralAmplitudeIndex_normSq_finiteSubtrace_le_traceEnergy_owner
      f D k hbound (ZetaPrimePowerIndex.box N)

noncomputable def zetaCompletedPrimeVerticalSpectralAmplitudeIndex_normSqTraceEnergy
    (f : ZetaAdmissibleFunction) : ℝ :=
  ∑' ι : ZetaPrimePowerIndex,
    ‖zetaCompletedPrimeVerticalSpectralAmplitudeIndex ι f‖ ^ 2

theorem zetaCompletedPrimeVerticalSpectralAmplitudeIndex_normSq_hasSum_traceEnergy_owner
    (f : ZetaAdmissibleFunction) (D : ℝ) (k : ℕ)
    (hbound : VerticalPrimeCenterWeightedSpectralPolynomialBound f D k) :
    HasSum
      (fun ι : ZetaPrimePowerIndex =>
        ‖zetaCompletedPrimeVerticalSpectralAmplitudeIndex ι f‖ ^ 2)
      (zetaCompletedPrimeVerticalSpectralAmplitudeIndex_normSqTraceEnergy f) := by
  exact
    (zetaCompletedPrimeVerticalSpectralAmplitudeIndex_normSq_summable_owner
      f D k hbound).hasSum

theorem zetaCompletedPrimeVerticalSpectralAmplitudeIndex_normSq_finiteSubtrace_le_traceEnergy_owner
    (f : ZetaAdmissibleFunction) (D : ℝ) (k : ℕ)
    (hbound : VerticalPrimeCenterWeightedSpectralPolynomialBound f D k)
    (s : Finset ZetaPrimePowerIndex) :
    ∑ ι in s, ‖zetaCompletedPrimeVerticalSpectralAmplitudeIndex ι f‖ ^ 2 ≤
      zetaCompletedPrimeVerticalSpectralAmplitudeIndex_normSqTraceEnergy f := by
  exact
    sum_le_hasSum
      s
      (fun ι hι => sq_nonneg
        ‖zetaCompletedPrimeVerticalSpectralAmplitudeIndex ι f‖)
      (zetaCompletedPrimeVerticalSpectralAmplitudeIndex_normSq_hasSum_traceEnergy_owner
        f D k hbound)

theorem zetaCompletedPrimeVerticalSpectralAmplitudeIndex_normSq_boxSubtrace_le_traceEnergy_owner
    (f : ZetaAdmissibleFunction) (D : ℝ) (k N : ℕ)
    (hbound : VerticalPrimeCenterWeightedSpectralPolynomialBound f D k) :
    ∑ ι in ZetaPrimePowerIndex.box N,
        ‖zetaCompletedPrimeVerticalSpectralAmplitudeIndex ι f‖ ^ 2 ≤
      zetaCompletedPrimeVerticalSpectralAmplitudeIndex_normSqTraceEnergy f := by
  exact
    zetaCompletedPrimeVerticalSpectralAmplitudeIndex_normSq_finiteSubtrace_le_traceEnergy_owner
      f D k hbound (ZetaPrimePowerIndex.box N)

theorem zetaCompletedPrimeVerticalSpectralAmplitudeIndex_normSq_windowSubtrace_le_traceEnergy_owner
    (f : ZetaAdmissibleFunction) (D : ℝ) (k N : ℕ)
    (hbound : VerticalPrimeCenterWeightedSpectralPolynomialBound f D k) :
    ∑ ι in ZetaPrimePowerIndex.window N,
        ‖zetaCompletedPrimeVerticalSpectralAmplitudeIndex ι f‖ ^ 2 ≤
      zetaCompletedPrimeVerticalSpectralAmplitudeIndex_normSqTraceEnergy f := by
  exact
    zetaCompletedPrimeVerticalSpectralAmplitudeIndex_normSq_finiteSubtrace_le_traceEnergy_owner
      f D k hbound (ZetaPrimePowerIndex.window N)

/-- Trace-energy summability of the weighted prime sampling stream gives
one-face Hilbert-amplitude square summability. -/
theorem zetaCompletedPrimeSpectralAmplitudeIndex_normSq_summable_traceBessel_source
    (f : ZetaAdmissibleFunction) (C : ℝ) (k : ℕ)
    (hbound : PrimeCenterSpectralPolynomialBound f C k) :
    Summable
      (fun index : ZetaPrimePowerIndex =>
        ‖zetaCompletedPrimeSpectralAmplitudeIndex index f‖ ^ 2) :=
  zetaCompletedPrimeSpectralAmplitudeIndex_normSq_summable_traceEnergy_source
    f C k hbound

/-- Reflection transports one-face Hilbert-amplitude square-summability to the
opposite completed prime spectral amplitude stream. -/
theorem zetaCompletedPrimeOppositeSpectralAmplitudeIndex_normSq_summable_traceBessel_source
    (f : ZetaAdmissibleFunction) (C : ℝ) (k : ℕ)
    (hbound : PrimeCenterSpectralPolynomialBound
      (ZetaAdmissibleFunction.reflect f) C k) :
    Summable
      (fun index : ZetaPrimePowerIndex =>
        ‖zetaCompletedPrimeOppositeSpectralAmplitudeIndex index f‖ ^ 2) :=
  zetaCompletedPrimeOppositeSpectralAmplitudeIndex_normSq_summable_traceEnergy_source
    f C k hbound

/-- Spectral-coordinate majorant summability follows by adding the positive and
opposite Hilbert-amplitude square-summable streams. -/
theorem zetaCompletedPrimeSpectralCoordinateMajorant_summable_traceBessel_source
    (f : ZetaAdmissibleFunction) (Cpos : ℝ) (kpos : ℕ)
    (hpos : PrimeCenterSpectralPolynomialBound f Cpos kpos)
    (Cneg : ℝ) (kneg : ℕ)
    (hneg : PrimeCenterSpectralPolynomialBound
      (ZetaAdmissibleFunction.reflect f) Cneg kneg) :
    Summable
      (fun index : ZetaPrimePowerIndex =>
        zetaCompletedPrimeSpectralCoordinateMajorant index f) :=
  zetaCompletedPrimeSpectralCoordinateMajorant_summable_traceEnergy_source
    f Cpos kpos hpos Cneg kneg hneg

/-- Spectral-coordinate majorant summability gives norm summability of the
completed prime diagonal-debt coordinate stream. -/
theorem zetaCompletedPrimeDefectKernelDiagonalDebtCoordinate_norm_summable_of_spectralCoordinateMajorant_summable_traceBessel
    (f : ZetaAdmissibleFunction)
    (hmajorant :
      Summable
        (fun index : ZetaPrimePowerIndex =>
          zetaCompletedPrimeSpectralCoordinateMajorant index f)) :
    Summable
      (fun index : ZetaPrimePowerIndex =>
        ‖zetaCompletedPrimeDefectKernelDiagonalDebtCoordinate index f‖) :=
  Summable.of_nonneg_of_le
    (fun index =>
      norm_nonneg
        (zetaCompletedPrimeDefectKernelDiagonalDebtCoordinate index f))
    (fun index =>
      norm_zetaCompletedPrimeDefectKernelDiagonalDebtCoordinate_le_spectralMajorant
        index f)
    hmajorant

/-- Spectral-coordinate majorant summability gives complex summability of the
completed prime diagonal-debt coordinate stream. -/
theorem zetaCompletedPrimeDefectKernelDiagonalDebtCoordinate_summable_of_spectralCoordinateMajorant_summable_traceBessel
    (f : ZetaAdmissibleFunction)
    (hmajorant :
      Summable
        (fun index : ZetaPrimePowerIndex =>
          zetaCompletedPrimeSpectralCoordinateMajorant index f)) :
    Summable
      (fun index : ZetaPrimePowerIndex =>
        zetaCompletedPrimeDefectKernelDiagonalDebtCoordinate index f) :=
  Summable.of_norm
    (zetaCompletedPrimeDefectKernelDiagonalDebtCoordinate_norm_summable_of_spectralCoordinateMajorant_summable_traceBessel
      f hmajorant)

/-- Complex summability gives real-coordinate summability for the completed
prime diagonal-debt coordinate stream. -/
theorem zetaCompletedPrimeDefectKernelDiagonalDebtCoordinate_re_summable_of_complex_summable_traceBessel
    (f : ZetaAdmissibleFunction)
    (hcomplex :
      Summable
        (fun index : ZetaPrimePowerIndex =>
          zetaCompletedPrimeDefectKernelDiagonalDebtCoordinate index f)) :
    Summable
      (fun index : ZetaPrimePowerIndex =>
        Complex.re
          (zetaCompletedPrimeDefectKernelDiagonalDebtCoordinate index f)) :=
  (RCLike.reCLM : ℂ →L[ℝ] ℝ).summable hcomplex

/-- Summability source for the completed prime diagonal-debt real-coordinate
stream. -/
theorem zetaCompletedPrimeDefectKernelDiagonalDebtCoordinate_re_summable_traceBessel_source
    (f : ZetaAdmissibleFunction) (Cpos : ℝ) (kpos : ℕ)
    (hpos : PrimeCenterSpectralPolynomialBound f Cpos kpos)
    (Cneg : ℝ) (kneg : ℕ)
    (hneg : PrimeCenterSpectralPolynomialBound
      (ZetaAdmissibleFunction.reflect f) Cneg kneg) :
    Summable
      (fun index : ZetaPrimePowerIndex =>
        Complex.re
          (zetaCompletedPrimeDefectKernelDiagonalDebtCoordinate index f)) :=
  let hmajorant :
      Summable
        (fun index : ZetaPrimePowerIndex =>
          zetaCompletedPrimeSpectralCoordinateMajorant index f) :=
    zetaCompletedPrimeSpectralCoordinateMajorant_summable_traceBessel_source
      f Cpos kpos hpos Cneg kneg hneg
  let hcomplex :
      Summable
        (fun index : ZetaPrimePowerIndex =>
          zetaCompletedPrimeDefectKernelDiagonalDebtCoordinate index f) :=
    zetaCompletedPrimeDefectKernelDiagonalDebtCoordinate_summable_of_spectralCoordinateMajorant_summable_traceBessel
      f hmajorant
  zetaCompletedPrimeDefectKernelDiagonalDebtCoordinate_re_summable_of_complex_summable_traceBessel
    f hcomplex

/-- The completed prime diagonal-debt real-coordinate stream has sum equal to
its `tsum`. -/
theorem zetaCompletedPrimeDefectKernelDiagonalDebtCoordinate_re_hasSum_tsum_traceBessel
    (f : ZetaAdmissibleFunction) (Cpos : ℝ) (kpos : ℕ)
    (hpos : PrimeCenterSpectralPolynomialBound f Cpos kpos)
    (Cneg : ℝ) (kneg : ℕ)
    (hneg : PrimeCenterSpectralPolynomialBound
      (ZetaAdmissibleFunction.reflect f) Cneg kneg) :
    HasSum
      (fun index : ZetaPrimePowerIndex =>
        Complex.re
          (zetaCompletedPrimeDefectKernelDiagonalDebtCoordinate index f))
      (∑' index : ZetaPrimePowerIndex,
        Complex.re
          (zetaCompletedPrimeDefectKernelDiagonalDebtCoordinate index f)) :=
  (zetaCompletedPrimeDefectKernelDiagonalDebtCoordinate_re_summable_traceBessel_source
    f Cpos kpos hpos Cneg kneg hneg).hasSum

/-- Summability of the nonnegative diagonal-debt real-coordinate stream gives a
uniform upper bound for all diagonal-debt real windows. -/
theorem zetaCompletedPrimeDefectKernelDiagonalDebtRealWindow_upperBound_of_re_summable_traceBessel
    (f : ZetaAdmissibleFunction) (Cpos : ℝ) (kpos : ℕ)
    (hpos : PrimeCenterSpectralPolynomialBound f Cpos kpos)
    (Cneg : ℝ) (kneg : ℕ)
    (hneg : PrimeCenterSpectralPolynomialBound
      (ZetaAdmissibleFunction.reflect f) Cneg kneg) :
    ∃ C : ℝ,
      ZetaCompletedPrimeDefectKernelDiagonalDebtRealWindowUpperBound
        f C :=
  let C : ℝ :=
    ∑' index : ZetaPrimePowerIndex,
      Complex.re
        (zetaCompletedPrimeDefectKernelDiagonalDebtCoordinate index f)
  let hhasSum :
      HasSum
        (fun index : ZetaPrimePowerIndex =>
          Complex.re
            (zetaCompletedPrimeDefectKernelDiagonalDebtCoordinate index f))
        C :=
    zetaCompletedPrimeDefectKernelDiagonalDebtCoordinate_re_hasSum_tsum_traceBessel
      f Cpos kpos hpos Cneg kneg hneg
  let hnonnegative :
      ∀ index : ZetaPrimePowerIndex,
        0 ≤
          Complex.re
            (zetaCompletedPrimeDefectKernelDiagonalDebtCoordinate index f) :=
    fun index =>
      zetaCompletedPrimeDefectKernelDiagonalDebtCoordinate_re_nonnegative_traceBessel
        index f
  let hbound :
      ZetaCompletedPrimeDefectKernelDiagonalDebtRealWindowUpperBound
        f C :=
    fun N =>
    let hrealWindow :
        zetaCompletedPrimeDefectKernelDiagonalDebtRealWindow N f =
          ∑ index in ZetaPrimePowerIndex.window N,
            Complex.re
              (zetaCompletedPrimeDefectKernelDiagonalDebtCoordinate index f) :=
      zetaCompletedPrimeDefectKernelDiagonalDebtRealWindow_eq_sum_re_traceBessel
        N f
    let hsum :
        (∑ index in ZetaPrimePowerIndex.window N,
          Complex.re
            (zetaCompletedPrimeDefectKernelDiagonalDebtCoordinate index f)) ≤
          C :=
      sum_le_hasSum
        (ZetaPrimePowerIndex.window N)
        (fun index membership => hnonnegative index)
        hhasSum
    Eq.subst
      (motive := fun value : ℝ => value ≤ C)
      hrealWindow.symm
      hsum
  Exists.intro C hbound

/-- Diagonal-debt real-window Bessel source for completed prime packets. -/
theorem zetaCompletedPrimeDefectKernelDiagonalDebtRealWindow_upperBound_traceBessel_source
    (f : ZetaAdmissibleFunction) (Cpos : ℝ) (kpos : ℕ)
    (hpos : PrimeCenterSpectralPolynomialBound f Cpos kpos)
    (Cneg : ℝ) (kneg : ℕ)
    (hneg : PrimeCenterSpectralPolynomialBound
      (ZetaAdmissibleFunction.reflect f) Cneg kneg) :
    ∃ C : ℝ,
      ZetaCompletedPrimeDefectKernelDiagonalDebtRealWindowUpperBound
        f C :=
  zetaCompletedPrimeDefectKernelDiagonalDebtRealWindow_upperBound_of_re_summable_traceBessel
    f Cpos kpos hpos Cneg kneg hneg

/-- Diagonal-debt real-window Bessel domination gives Hilbert-amplitude window
Bessel domination. -/
theorem zetaCompletedPrimeSpectralAmplitudeIndex_windowNormSq_upperBound_of_diagonalDebtRealWindow_upperBound_traceBessel
    (f : ZetaAdmissibleFunction) (C : ℝ)
    (hC :
      ZetaCompletedPrimeDefectKernelDiagonalDebtRealWindowUpperBound
        f C) :
    ZetaCompletedPrimeSpectralAmplitudeWindowNormSqUpperBound
      f C :=
  fun N =>
  le_trans
    (zetaCompletedPrimeSpectralAmplitudeIndex_normSq_windowSubtrace_le_diagonalDebtRealWindow_traceBessel
      N f)
    (hC N)

/-- Genuine-window Hilbert-amplitude Bessel source for the square-root-weighted
completed prime spectral amplitudes. -/
theorem zetaCompletedPrimeSpectralAmplitudeIndex_windowNormSq_upperBound_traceBessel_source
    (f : ZetaAdmissibleFunction) (Cpos : ℝ) (kpos : ℕ)
    (hpos : PrimeCenterSpectralPolynomialBound f Cpos kpos)
    (Cneg : ℝ) (kneg : ℕ)
    (hneg : PrimeCenterSpectralPolynomialBound
      (ZetaAdmissibleFunction.reflect f) Cneg kneg) :
    ∃ C : ℝ,
      ZetaCompletedPrimeSpectralAmplitudeWindowNormSqUpperBound
        f C :=
  match
    zetaCompletedPrimeDefectKernelDiagonalDebtRealWindow_upperBound_traceBessel_source
      f Cpos kpos hpos Cneg kneg hneg with
  | ⟨C, hC⟩ =>
      Exists.intro C
        (zetaCompletedPrimeSpectralAmplitudeIndex_windowNormSq_upperBound_of_diagonalDebtRealWindow_upperBound_traceBessel
          f C hC)

/-- Hilbert-amplitude window Bessel domination gives genuine-window weighted
prime-center sampling domination. -/
theorem completedAutocorrelationSpectralTransform_weightedPrimeSampling_windowSubtrace_upperBound_of_amplitude_windowNormSq_upperBound_traceBessel
    (f : ZetaAdmissibleFunction) (C : ℝ)
    (hC :
      ZetaCompletedPrimeSpectralAmplitudeWindowNormSqUpperBound
        f C) :
    CompletedAutocorrelationSpectralTransformWeightedPrimeSamplingWindowSubtraceUpperBound
      f C :=
  fun N =>
  let hweighted_eq_sample :
      (∑ index in ZetaPrimePowerIndex.window N,
        completedAutocorrelationSpectralTransform_weightedPrimeSampling
          index f) =
      ∑ index in ZetaPrimePowerIndex.window N,
        zetaCompletedPrimePositiveWeightedSampleNormSq index f :=
    Finset.sum_congr
      (Eq.refl (ZetaPrimePowerIndex.window N))
      (fun index membership =>
        (zetaCompletedPrimePositiveWeightedSampleNormSq_eq_weightedPrimeSampling
          index f).symm)
  let hsample_eq_amplitude :
      (∑ index in ZetaPrimePowerIndex.window N,
        zetaCompletedPrimePositiveWeightedSampleNormSq index f) =
      ∑ index in ZetaPrimePowerIndex.window N,
        ‖zetaCompletedPrimeSpectralAmplitudeIndex index f‖ ^ 2 :=
    Finset.sum_congr
      (Eq.refl (ZetaPrimePowerIndex.window N))
      (fun index membership =>
        (zetaCompletedPrimeSpectralAmplitudeIndex_norm_sq_eq_weightedSampleNormSq
          index f).symm)
  let hsum :
      (∑ index in ZetaPrimePowerIndex.window N,
        completedAutocorrelationSpectralTransform_weightedPrimeSampling
          index f) =
      ∑ index in ZetaPrimePowerIndex.window N,
        ‖zetaCompletedPrimeSpectralAmplitudeIndex index f‖ ^ 2 :=
    Eq.trans hweighted_eq_sample hsample_eq_amplitude
  Eq.subst
    (motive := fun value : ℝ => value ≤ C)
    hsum.symm
    (hC N)

/-- Genuine-window Bessel source for the weighted completed prime-center
sampling stream. -/
theorem completedAutocorrelationSpectralTransform_weightedPrimeSampling_windowSubtrace_upperBound_traceBessel_source
    (f : ZetaAdmissibleFunction) (Cpos : ℝ) (kpos : ℕ)
    (hpos : PrimeCenterSpectralPolynomialBound f Cpos kpos)
    (Cneg : ℝ) (kneg : ℕ)
    (hneg : PrimeCenterSpectralPolynomialBound
      (ZetaAdmissibleFunction.reflect f) Cneg kneg) :
    ∃ C : ℝ,
      CompletedAutocorrelationSpectralTransformWeightedPrimeSamplingWindowSubtraceUpperBound
        f C :=
  match
    zetaCompletedPrimeSpectralAmplitudeIndex_windowNormSq_upperBound_traceBessel_source
      f Cpos kpos hpos Cneg kneg hneg with
  | ⟨C, hC⟩ =>
      Exists.intro C
        (completedAutocorrelationSpectralTransform_weightedPrimeSampling_windowSubtrace_upperBound_of_amplitude_windowNormSq_upperBound_traceBessel
          f C hC)

/-- Genuine-window Bessel domination gives rectangular-box Bessel domination,
because nongenuine prime-power indices have zero weighted sampling mass. -/
theorem completedAutocorrelationSpectralTransform_weightedPrimeSampling_boxSubtrace_upperBound_of_windowSubtrace_upperBound_traceBessel
    (f : ZetaAdmissibleFunction) (C : ℝ)
    (hC :
      CompletedAutocorrelationSpectralTransformWeightedPrimeSamplingWindowSubtraceUpperBound
        f C) :
    CompletedAutocorrelationSpectralTransformWeightedPrimeSamplingBoxSubtraceUpperBound
      f C :=
  fun N =>
  Eq.subst
    (motive := fun value : ℝ => value ≤ C)
    (sum_box_completedAutocorrelationSpectralTransform_weightedPrimeSampling_eq_sum_window
      N f).symm
    (hC N)

/-- Rectangular-box Bessel source for the weighted completed prime-center
sampling stream. -/
theorem completedAutocorrelationSpectralTransform_weightedPrimeSampling_boxSubtrace_upperBound_traceBessel_source
    (f : ZetaAdmissibleFunction) (Cpos : ℝ) (kpos : ℕ)
    (hpos : PrimeCenterSpectralPolynomialBound f Cpos kpos)
    (Cneg : ℝ) (kneg : ℕ)
    (hneg : PrimeCenterSpectralPolynomialBound
      (ZetaAdmissibleFunction.reflect f) Cneg kneg) :
    ∃ C : ℝ,
      CompletedAutocorrelationSpectralTransformWeightedPrimeSamplingBoxSubtraceUpperBound
        f C :=
  match
    completedAutocorrelationSpectralTransform_weightedPrimeSampling_windowSubtrace_upperBound_traceBessel_source
      f Cpos kpos hpos Cneg kneg hneg with
  | ⟨C, hC⟩ =>
      Exists.intro C
        (completedAutocorrelationSpectralTransform_weightedPrimeSampling_boxSubtrace_upperBound_of_windowSubtrace_upperBound_traceBessel
          f C hC)

/-- Rectangular-box Bessel domination gives finite-subtrace Bessel domination. -/
theorem completedAutocorrelationSpectralTransform_weightedPrimeSampling_finiteSubtrace_upperBound_of_boxSubtrace_upperBound_traceBessel
    (f : ZetaAdmissibleFunction) (C : ℝ)
    (hC :
      CompletedAutocorrelationSpectralTransformWeightedPrimeSamplingBoxSubtraceUpperBound
        f C) :
    ∀ s : Finset ZetaPrimePowerIndex,
      ∑ index in s,
        completedAutocorrelationSpectralTransform_weightedPrimeSampling
          index f ≤ C :=
  fun s =>
  match
    completedAutocorrelationSpectralTransform_weightedPrimeSampling_finiteSubtrace_le_boxSubtrace_traceBessel
      f s with
  | ⟨N, hfinite_le_box⟩ =>
      le_trans hfinite_le_box (hC N)

/-- Direct finite-subtrace Bessel source for the weighted completed prime-center
sampling stream. -/
theorem completedAutocorrelationSpectralTransform_weightedPrimeSampling_finiteSubtrace_upperBound_traceBessel_source
    (f : ZetaAdmissibleFunction) (Cpos : ℝ) (kpos : ℕ)
    (hpos : PrimeCenterSpectralPolynomialBound f Cpos kpos)
    (Cneg : ℝ) (kneg : ℕ)
    (hneg : PrimeCenterSpectralPolynomialBound
      (ZetaAdmissibleFunction.reflect f) Cneg kneg) :
    ∃ C : ℝ,
      ∀ s : Finset ZetaPrimePowerIndex,
        ∑ index in s,
          completedAutocorrelationSpectralTransform_weightedPrimeSampling
            index f ≤ C :=
  match
    completedAutocorrelationSpectralTransform_weightedPrimeSampling_boxSubtrace_upperBound_traceBessel_source
      f Cpos kpos hpos Cneg kneg hneg with
  | ⟨C, hC⟩ =>
      Exists.intro C
        (completedAutocorrelationSpectralTransform_weightedPrimeSampling_finiteSubtrace_upperBound_of_boxSubtrace_upperBound_traceBessel
          f C hC)

end ZetaAdmissibleFunction

end
end LFunctions
end Boundary
