import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaCompletedHilbertSource.ZetaHermitianPacket.PrimeCenterSamplingWeightBound
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaCompletedHilbertSource.ZetaHermitianPacket.PrimeCenterSamplingSpectralOwner
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaCompletedHilbertSource.ZetaHermitianPacket.PrimeCenterSamplingDecayParts.TraceBessel
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Topology.Algebra.InfiniteSum.Order

/-!
# Prime-center trace reconstruction

This file owns the trace-reconstruction theorem that supplies summability of
the completed prime-power spectral sampling stream.  The theorem is stated for
the weighted trace image consumed by the prime majorant, not as an eventual
finite-support assertion for individual prime-center samples.
-/

namespace Boundary
namespace LFunctions

noncomputable section

namespace ZetaAdmissibleFunction

/-- The corrected vertical Fourier trace bound, stated at the decay owner
level.  Its summand is the vertical completed sample, not the legacy
real-Laplace compatibility sample. -/
def CompletedVerticalAutocorrelationSpectralTransformWeightedPrimeSamplingBoxBound
    (f : ZetaAdmissibleFunction) (D : ℝ) (k : ℕ) : Prop :=
  VerticalPrimeCenterWeightedSpectralPolynomialBound f D k

theorem completedVerticalAutocorrelationSpectralTransformWeightedPrimeSamplingBoxBound_window
    (f : ZetaAdmissibleFunction) (D : ℝ) (k : ℕ)
    (hbound : CompletedVerticalAutocorrelationSpectralTransformWeightedPrimeSamplingBoxBound
      f D k) :
    ∀ N : ℕ,
      completedAutocorrelationSpectralTransform_verticalWeightedPrimeSamplingWindow
          N f ≤
        ∑ ι in ZetaPrimePowerIndex.window N,
          D * ZetaPrimePowerIndex.polynomialHeightDecay k ι := by
  exact
    completedAutocorrelationSpectralTransform_verticalWeightedPrimeSamplingWindow_le_weightedVerticalMajorantWindow
      f D k
      (show VerticalPrimeCenterWeightedSpectralPolynomialBound f D k from hbound)

/-- The prime-center cancellation kernel attached to the completed spectral
Laplace transform. -/
noncomputable def zetaCompletedPrimeCenterCancellationKernel
    (f : ZetaAdmissibleFunction) (index : ZetaPrimePowerIndex) : ℂ :=
  zetaCompletedSpectralLaplaceTransform f index.center

/-- The completed spectral transform at a prime-power center is the
prime-center cancellation kernel. -/
theorem zetaCompletedSpectralLaplaceTransform_primeCenter_eq_cancellationKernel
    (f : ZetaAdmissibleFunction) (index : ZetaPrimePowerIndex) :
    zetaCompletedSpectralLaplaceTransform f index.center =
      zetaCompletedPrimeCenterCancellationKernel f index := by
  rfl

/-- Rectangular-box Bessel trace-energy domination for the positive weighted
prime-center sampling stream. -/
def CompletedAutocorrelationSpectralTransformWeightedPrimeSamplingBoxBesselBound
    (f : ZetaAdmissibleFunction) :
    Prop :=
  ∃ C : ℝ,
    ∀ N : ℕ,
      ∑ index in ZetaPrimePowerIndex.box N,
        completedAutocorrelationSpectralTransform_weightedPrimeSampling
          index f ≤ C

/-- Every finite positive weighted prime-center subtrace is dominated by some
rectangular box subtrace. -/
theorem completedAutocorrelationSpectralTransform_weightedPrimeSampling_finiteSubtrace_le_boxSubtrace_source_core
    (f : ZetaAdmissibleFunction) :
    ∀ s : Finset ZetaPrimePowerIndex,
      ∃ N : ℕ,
        ∑ index in s,
          completedAutocorrelationSpectralTransform_weightedPrimeSampling
            index f ≤
        ∑ index in ZetaPrimePowerIndex.box N,
          completedAutocorrelationSpectralTransform_weightedPrimeSampling
            index f := by
  intro s
  have hcontainsEventually :
      ∀ᶠ N in Filter.atTop,
        s ≤ ZetaPrimePowerIndex.box N :=
    ZetaPrimePowerIndex.box_tendsto_atTop.eventually
      (Filter.eventually_ge_atTop s)
  match hcontainsEventually.exists with
  | ⟨N, hN⟩ =>
      have hsubset :
          s ⊆ ZetaPrimePowerIndex.box N := by
        exact hN
      have hsum :
          ∑ index in s,
            completedAutocorrelationSpectralTransform_weightedPrimeSampling
              index f ≤
          ∑ index in ZetaPrimePowerIndex.box N,
            completedAutocorrelationSpectralTransform_weightedPrimeSampling
              index f :=
        Finset.sum_le_sum_of_subset_of_nonneg
          hsubset
          (fun index hbox hnot =>
            completedAutocorrelationSpectralTransform_weightedPrimeSampling_nonnegative
              index f)
      exact ⟨N, hsum⟩

/-- Source Hilbert trace-kernel Bessel domination: each rectangular
prime-center sampling subtrace is bounded by the reconstructed completed
trace-energy scalar. -/
theorem completedAutocorrelationSpectralTransform_weightedPrimeSampling_boxSubtrace_le_traceEnergy_source_core
    (f : ZetaAdmissibleFunction) (C₀ : ℝ) (k : ℕ)
    (hbound : f.PrimeCenterSpectralPolynomialBound C₀ k) :
    ∀ N : ℕ,
      ∑ index in ZetaPrimePowerIndex.box N,
        completedAutocorrelationSpectralTransform_weightedPrimeSampling
          index f ≤
      completedAutocorrelationSpectralTransform_weightedPrimeSamplingTraceEnergy
        f := by
  intro N
  have hhasSum :
      HasSum
        (fun index : ZetaPrimePowerIndex =>
          completedAutocorrelationSpectralTransform_weightedPrimeSampling
            index f)
        (completedAutocorrelationSpectralTransform_weightedPrimeSamplingTraceEnergy
          f) := by
    exact
      completedAutocorrelationSpectralTransform_weightedPrimeSampling_hasSum_traceEnergy_source_primitive
        f C₀ k hbound
  have hnonnegative :
      ∀ index : ZetaPrimePowerIndex,
        0 ≤
          completedAutocorrelationSpectralTransform_weightedPrimeSampling
            index f := by
    intro index
    exact
      completedAutocorrelationSpectralTransform_weightedPrimeSampling_nonnegative
        index f
  exact
    sum_le_hasSum
      (ZetaPrimePowerIndex.box N)
      (fun index membership => hnonnegative index)
      hhasSum

/-- Source Hilbert trace summability for the positive weighted prime-center
sampling stream.  This is the Bessel trace theorem, not pointwise decay of the
Laplace transform along the real prime-center axis. -/
theorem completedAutocorrelationSpectralTransform_weightedPrimeSampling_summable_traceEnergy_source_core
    (f : ZetaAdmissibleFunction) (C₀ : ℝ) (k : ℕ)
    (hbound : f.PrimeCenterSpectralPolynomialBound C₀ k) :
    Summable
      (fun index : ZetaPrimePowerIndex =>
        completedAutocorrelationSpectralTransform_weightedPrimeSampling
          index f) := by
  exact
    completedAutocorrelationSpectralTransform_weightedPrimeSampling_summable_traceEnergy_source_primitive
      f C₀ k hbound

/-- Source genuine-window trace-energy domination for the positive weighted
prime-center sampling stream. -/
theorem completedAutocorrelationSpectralTransform_weightedPrimeSampling_windowSubtrace_bounded_traceEnergy_source_core
    (f : ZetaAdmissibleFunction) (C₀ : ℝ) (k : ℕ)
    (hbound : f.PrimeCenterSpectralPolynomialBound C₀ k) :
    ∃ C : ℝ,
      ∀ N : ℕ,
        completedAutocorrelationSpectralTransform_weightedPrimeSamplingWindow
          N f ≤ C := by
  let C : ℝ :=
    completedAutocorrelationSpectralTransform_weightedPrimeSamplingTraceEnergy
      f
  have hhasSum :
      HasSum
        (fun index : ZetaPrimePowerIndex =>
          completedAutocorrelationSpectralTransform_weightedPrimeSampling
            index f)
        C := by
    unfold C
    exact
      completedAutocorrelationSpectralTransform_weightedPrimeSampling_hasSum_traceEnergy_source_primitive
        f C₀ k hbound
  have hnonnegative :
      ∀ index : ZetaPrimePowerIndex,
        0 ≤
          completedAutocorrelationSpectralTransform_weightedPrimeSampling
            index f := by
    intro index
    exact
      completedAutocorrelationSpectralTransform_weightedPrimeSampling_nonnegative
        index f
  have hbox :
      ∀ N : ℕ,
        ∑ index in ZetaPrimePowerIndex.box N,
          completedAutocorrelationSpectralTransform_weightedPrimeSampling
            index f ≤ C := by
    intro N
    exact
      sum_le_hasSum
        (ZetaPrimePowerIndex.box N)
        (fun index membership => hnonnegative index)
        hhasSum
  have hwindow :
      ∀ N : ℕ,
        completedAutocorrelationSpectralTransform_weightedPrimeSamplingWindow
          N f ≤ C := by
    intro N
    exact Eq.subst
      (motive := fun value : ℝ => value ≤ C)
      (sum_box_completedAutocorrelationSpectralTransform_weightedPrimeSampling_eq_window
        N f)
      (hbox N)
  exact ⟨C, hwindow⟩

/-- Source rectangular box trace-energy domination for the positive weighted
prime-center sampling stream. -/
theorem completedAutocorrelationSpectralTransform_weightedPrimeSampling_boxSubtrace_bounded_traceEnergy_source_core
    (f : ZetaAdmissibleFunction) (C₀ : ℝ) (k : ℕ)
    (hbound : f.PrimeCenterSpectralPolynomialBound C₀ k) :
    ∃ C : ℝ,
      ∀ N : ℕ,
        ∑ index in ZetaPrimePowerIndex.box N,
          completedAutocorrelationSpectralTransform_weightedPrimeSampling
            index f ≤ C := by
  match
    completedAutocorrelationSpectralTransform_weightedPrimeSampling_windowSubtrace_bounded_traceEnergy_source_core
      f C₀ k hbound with
  | ⟨C, hC⟩ =>
      have hbox :
          ∀ N : ℕ,
            ∑ index in ZetaPrimePowerIndex.box N,
              completedAutocorrelationSpectralTransform_weightedPrimeSampling
                index f ≤ C := by
        intro N
        exact Eq.subst
          (motive := fun value : ℝ => value ≤ C)
          (sum_box_completedAutocorrelationSpectralTransform_weightedPrimeSampling_eq_window
            N f).symm
          (hC N)
      exact ⟨C, hbox⟩

/-- Source finite trace-energy domination for the positive weighted
prime-center sampling stream. -/
theorem completedAutocorrelationSpectralTransform_weightedPrimeSampling_finiteSubtrace_bounded_traceEnergy_source_core
    (f : ZetaAdmissibleFunction) (C₀ : ℝ) (k : ℕ)
    (hbound : f.PrimeCenterSpectralPolynomialBound C₀ k) :
    ∃ C : ℝ,
      ∀ s : Finset ZetaPrimePowerIndex,
        ∑ index in s,
          completedAutocorrelationSpectralTransform_weightedPrimeSampling
            index f ≤ C := by
  let C : ℝ :=
    completedAutocorrelationSpectralTransform_weightedPrimeSamplingTraceEnergy
      f
  have hhasSum :
      HasSum
        (fun index : ZetaPrimePowerIndex =>
          completedAutocorrelationSpectralTransform_weightedPrimeSampling
            index f)
        C := by
    unfold C
    exact
      completedAutocorrelationSpectralTransform_weightedPrimeSampling_hasSum_traceEnergy_source_primitive
        f C₀ k hbound
  have hnonnegative :
      ∀ index : ZetaPrimePowerIndex,
        0 ≤
          completedAutocorrelationSpectralTransform_weightedPrimeSampling
            index f := by
    intro index
    exact
      completedAutocorrelationSpectralTransform_weightedPrimeSampling_nonnegative
        index f
  have hfinite :
      ∀ s : Finset ZetaPrimePowerIndex,
        ∑ index in s,
          completedAutocorrelationSpectralTransform_weightedPrimeSampling
            index f ≤ C := by
    intro s
    exact
      sum_le_hasSum
        s
        (fun index membership => hnonnegative index)
        hhasSum
  exact ⟨C, hfinite⟩

/-- Source Bessel trace-energy domination for the positive weighted
prime-center sampling stream. -/
theorem completedAutocorrelationSpectralTransform_weightedPrimeSampling_besselTraceEnergy_source_core
    (f : ZetaAdmissibleFunction) (C₀ : ℝ) (k : ℕ)
    (hbound : f.PrimeCenterSpectralPolynomialBound C₀ k) :
    CompletedAutocorrelationSpectralTransformWeightedPrimeSamplingBesselBound
      f := by
  exact
    completedAutocorrelationSpectralTransform_weightedPrimeSampling_besselBound_source_primitive
      f C₀ k hbound

/-- Source trace-energy identity for the positive weighted prime-center
sampling stream. -/
theorem completedAutocorrelationSpectralTransform_weightedPrimeSampling_hasSum_traceEnergy_source_core
    (f : ZetaAdmissibleFunction) (C₀ : ℝ) (k : ℕ)
    (hbound : f.PrimeCenterSpectralPolynomialBound C₀ k) :
    HasSum
      (fun index : ZetaPrimePowerIndex =>
        completedAutocorrelationSpectralTransform_weightedPrimeSampling
          index f)
      (completedAutocorrelationSpectralTransform_weightedPrimeSamplingTraceEnergy
        f) := by
  exact
    completedAutocorrelationSpectralTransform_weightedPrimeSampling_hasSum_traceEnergy_source_primitive
      f C₀ k hbound

/-- Source finite Bessel trace-energy domination for the positive weighted
prime-center sampling stream. -/
theorem completedAutocorrelationSpectralTransform_weightedPrimeSampling_finiteBessel_source_core
    (f : ZetaAdmissibleFunction) (C₀ : ℝ) (k : ℕ)
    (hbound : f.PrimeCenterSpectralPolynomialBound C₀ k) :
    ∃ C : ℝ,
      ∀ s : Finset ZetaPrimePowerIndex,
        ∑ index in s,
          completedAutocorrelationSpectralTransform_weightedPrimeSampling
            index f ≤ C := by
  let C : ℝ :=
    completedAutocorrelationSpectralTransform_weightedPrimeSamplingTraceEnergy
      f
  have hhasSum :
      HasSum
        (fun index : ZetaPrimePowerIndex =>
          completedAutocorrelationSpectralTransform_weightedPrimeSampling
            index f)
        C :=
    completedAutocorrelationSpectralTransform_weightedPrimeSampling_hasSum_traceEnergy_source_core
      f C₀ k hbound
  have hnonnegative :
      ∀ index : ZetaPrimePowerIndex,
        0 ≤
          completedAutocorrelationSpectralTransform_weightedPrimeSampling
            index f := by
    intro index
    exact
      completedAutocorrelationSpectralTransform_weightedPrimeSampling_nonnegative
        index f
  have hfinite :
      ∀ s : Finset ZetaPrimePowerIndex,
        ∑ index in s,
          completedAutocorrelationSpectralTransform_weightedPrimeSampling
            index f ≤ C := by
    intro s
    exact
      sum_le_hasSum
        s
        (fun index membership => hnonnegative index)
        hhasSum
  exact ⟨C, hfinite⟩

/-- Source Hilbert trace summability for the positive weighted prime-center
sampling stream.  This is a trace/Bessel statement, not pointwise decay of the
Laplace transform along the real prime-center axis. -/
theorem completedAutocorrelationSpectralTransform_weightedPrimeSampling_summable_source_core
    (f : ZetaAdmissibleFunction) (C₀ : ℝ) (k : ℕ)
    (hbound : f.PrimeCenterSpectralPolynomialBound C₀ k) :
    Summable
      (fun index : ZetaPrimePowerIndex =>
        completedAutocorrelationSpectralTransform_weightedPrimeSampling
          index f) := by
  exact
    completedAutocorrelationSpectralTransform_weightedPrimeSampling_summable_traceEnergy_source_core
      f C₀ k hbound

/-- Source Bessel trace-energy domination for the positive weighted
prime-center sampling stream. -/
theorem completedAutocorrelationSpectralTransform_weightedPrimeSampling_besselBound_source_core
    (f : ZetaAdmissibleFunction) (C₀ : ℝ) (k : ℕ)
    (hbound : f.PrimeCenterSpectralPolynomialBound C₀ k) :
    CompletedAutocorrelationSpectralTransformWeightedPrimeSamplingBesselBound
      f := by
  exact
    completedAutocorrelationSpectralTransform_weightedPrimeSampling_besselBound_source_primitive
      f C₀ k hbound

/-- Source finite trace-energy domination for the positive weighted
prime-center sampling stream. -/
theorem completedAutocorrelationSpectralTransform_weightedPrimeSampling_finiteSubtrace_bounded_source_core
    (f : ZetaAdmissibleFunction) (C₀ : ℝ) (k : ℕ)
    (hbound : f.PrimeCenterSpectralPolynomialBound C₀ k) :
    ∃ C : ℝ,
      ∀ s : Finset ZetaPrimePowerIndex,
        ∑ index in s,
          completedAutocorrelationSpectralTransform_weightedPrimeSampling
            index f ≤ C := by
  exact
    completedAutocorrelationSpectralTransform_weightedPrimeSampling_finiteSubtrace_bounded_traceEnergy_source_core
      f C₀ k hbound

/-- Rectangular weighted-prime-sampling box sums are the positive weighted
sample norm-square window sums. -/
theorem completedAutocorrelationSpectralTransform_weightedPrimeSampling_boxSum_eq_positiveWeightedSampleNormSq_window
    (N : ℕ) (f : ZetaAdmissibleFunction) :
    (∑ index in ZetaPrimePowerIndex.box N,
      completedAutocorrelationSpectralTransform_weightedPrimeSampling
        index f) =
      ∑ index in ZetaPrimePowerIndex.window N,
        zetaCompletedPrimePositiveWeightedSampleNormSq index f := by
  have hboxToWindow :
      (∑ index in ZetaPrimePowerIndex.box N,
        completedAutocorrelationSpectralTransform_weightedPrimeSampling
          index f) =
        ∑ index in ZetaPrimePowerIndex.window N,
          completedAutocorrelationSpectralTransform_weightedPrimeSampling
            index f :=
    sum_box_completedAutocorrelationSpectralTransform_weightedPrimeSampling_eq_sum_window
      N f
  have hwindowToSample :
      (∑ index in ZetaPrimePowerIndex.window N,
        completedAutocorrelationSpectralTransform_weightedPrimeSampling
          index f) =
        ∑ index in ZetaPrimePowerIndex.window N,
          zetaCompletedPrimePositiveWeightedSampleNormSq index f :=
    Finset.sum_congr
      (Eq.refl (ZetaPrimePowerIndex.window N))
      (fun index hindex =>
        (zetaCompletedPrimePositiveWeightedSampleNormSq_eq_weightedPrimeSampling
          index f).symm)
  exact hboxToWindow.trans hwindowToSample

/-- Source box-window trace-energy domination for the positive weighted
prime-center sampling stream. -/
theorem completedAutocorrelationSpectralTransform_weightedPrimeSampling_boxSubtrace_bounded_source
    (f : ZetaAdmissibleFunction) (C₀ : ℝ) (k : ℕ)
    (hbound : f.PrimeCenterSpectralPolynomialBound C₀ k) :
    ∃ C : ℝ,
      ∀ N : ℕ,
        ∑ index in ZetaPrimePowerIndex.box N,
          completedAutocorrelationSpectralTransform_weightedPrimeSampling
            index f ≤ C := by
  match
    completedAutocorrelationSpectralTransform_weightedPrimeSampling_finiteSubtrace_bounded_source_core
      f C₀ k hbound with
  | ⟨C, hC⟩ =>
      have hbox :
          ∀ N : ℕ,
            ∑ index in ZetaPrimePowerIndex.box N,
              completedAutocorrelationSpectralTransform_weightedPrimeSampling
                index f ≤ C := by
        intro N
        exact hC (ZetaPrimePowerIndex.box N)
      exact ⟨C, hbox⟩

/-- Every finite positive weighted prime-center subtrace is dominated by some
rectangular box subtrace. -/
theorem completedAutocorrelationSpectralTransform_weightedPrimeSampling_finiteSubtrace_le_boxSubtrace_source
    (f : ZetaAdmissibleFunction) (C₀ : ℝ) (k : ℕ)
    (hbound : f.PrimeCenterSpectralPolynomialBound C₀ k) :
    ∀ s : Finset ZetaPrimePowerIndex,
      ∃ N : ℕ,
        ∑ index in s,
          completedAutocorrelationSpectralTransform_weightedPrimeSampling
            index f ≤
        ∑ index in ZetaPrimePowerIndex.box N,
          completedAutocorrelationSpectralTransform_weightedPrimeSampling
            index f := by
  exact
    completedAutocorrelationSpectralTransform_weightedPrimeSampling_finiteSubtrace_le_boxSubtrace_source_core
      f

/-- Source Bessel trace-energy domination for the positive weighted
prime-center sampling stream. -/
theorem completedAutocorrelationSpectralTransform_weightedPrimeSampling_besselBound_source
    (f : ZetaAdmissibleFunction) (C₀ : ℝ) (k : ℕ)
    (hbound : f.PrimeCenterSpectralPolynomialBound C₀ k) :
    CompletedAutocorrelationSpectralTransformWeightedPrimeSamplingBesselBound
      f := by
  exact
    completedAutocorrelationSpectralTransform_weightedPrimeSampling_besselBound_source_core
      f C₀ k hbound

/-- Source finite trace-energy domination for the positive weighted
prime-center sampling stream. -/
theorem completedAutocorrelationSpectralTransform_weightedPrimeSampling_finiteSubtrace_bounded_source
    (f : ZetaAdmissibleFunction) (C₀ : ℝ) (k : ℕ)
    (hbound : f.PrimeCenterSpectralPolynomialBound C₀ k) :
    ∃ C : ℝ,
      ∀ s : Finset ZetaPrimePowerIndex,
        ∑ index in s,
          completedAutocorrelationSpectralTransform_weightedPrimeSampling
            index f ≤ C := by
  exact
    completedAutocorrelationSpectralTransform_weightedPrimeSampling_finiteSubtrace_bounded_source_core
      f C₀ k hbound

/-- Trace reconstruction bounds every finite positive weighted prime-center
subtrace by one completed trace-energy bound.  This is the exact finite
compression statement from which the infinite positive stream is recovered. -/
theorem completedAutocorrelationSpectralTransform_weightedPrimeSampling_finiteSubtrace_bounded_traceEnergy_source
    (f : ZetaAdmissibleFunction) (C₀ : ℝ) (k : ℕ)
    (hbound : f.PrimeCenterSpectralPolynomialBound C₀ k) :
    ∃ C : ℝ,
      ∀ s : Finset ZetaPrimePowerIndex,
        ∑ index in s,
          completedAutocorrelationSpectralTransform_weightedPrimeSampling
            index f ≤ C := by
  exact
    completedAutocorrelationSpectralTransform_weightedPrimeSampling_finiteSubtrace_bounded_source
      f C₀ k hbound

/-- Finite trace-energy domination gives summability of the positive weighted
prime-center sampling stream. -/
theorem completedAutocorrelationSpectralTransform_weightedPrimeSampling_summable_of_finiteSubtrace_bounded
    (f : ZetaAdmissibleFunction)
    (finiteSubtraceBound :
      ∃ C : ℝ,
        ∀ s : Finset ZetaPrimePowerIndex,
          ∑ index in s,
            completedAutocorrelationSpectralTransform_weightedPrimeSampling
              index f ≤ C) :
    Summable
      (fun index : ZetaPrimePowerIndex =>
        completedAutocorrelationSpectralTransform_weightedPrimeSampling
          index f) := by
  have hnonnegative :
      0 ≤
        fun index : ZetaPrimePowerIndex =>
          completedAutocorrelationSpectralTransform_weightedPrimeSampling
            index f := by
    intro index
    exact
      completedAutocorrelationSpectralTransform_weightedPrimeSampling_nonnegative
        index f
  match finiteSubtraceBound with
  | ⟨C, hC⟩ =>
      exact summable_of_sum_le hnonnegative hC

/-- Trace-energy reconstruction gives summability of the positive weighted
prime-center sampling stream. -/
theorem completedAutocorrelationSpectralTransform_weightedPrimeSampling_summable_traceEnergyFinite_source
    (f : ZetaAdmissibleFunction) (C₀ : ℝ) (k : ℕ)
    (hbound : f.PrimeCenterSpectralPolynomialBound C₀ k) :
    Summable
      (fun index : ZetaPrimePowerIndex =>
        completedAutocorrelationSpectralTransform_weightedPrimeSampling
          index f) := by
  exact
    completedAutocorrelationSpectralTransform_weightedPrimeSampling_summable_source_core
      f C₀ k hbound

/-- Trace reconstruction gives the completed prime-center trace-energy
`HasSum` identity for the positive weighted sampling stream. -/
theorem completedAutocorrelationSpectralTransform_weightedPrimeSampling_hasSum_traceEnergy_source
    (f : ZetaAdmissibleFunction) (C₀ : ℝ) (k : ℕ)
    (hbound : f.PrimeCenterSpectralPolynomialBound C₀ k) :
    HasSum
      (fun index : ZetaPrimePowerIndex =>
        completedAutocorrelationSpectralTransform_weightedPrimeSampling
          index f)
      (completedAutocorrelationSpectralTransform_weightedPrimeSamplingTraceEnergy
        f) := by
  exact
    completedAutocorrelationSpectralTransform_weightedPrimeSampling_hasSum_traceEnergy_source_core
      f C₀ k hbound

/-- Trace-energy reconstruction gives the completed trace-energy scalar as an
upper bound for all finite positive weighted prime-center subtraces. -/
theorem completedAutocorrelationSpectralTransform_weightedPrimeSampling_finiteSubtrace_le_traceEnergy
    (f : ZetaAdmissibleFunction) (C₀ : ℝ) (k : ℕ)
    (hbound : f.PrimeCenterSpectralPolynomialBound C₀ k) :
    ∀ s : Finset ZetaPrimePowerIndex,
        ∑ index in s,
          completedAutocorrelationSpectralTransform_weightedPrimeSampling
            index f ≤
          completedAutocorrelationSpectralTransform_weightedPrimeSamplingTraceEnergy
            f := by
  have hhasSum :
      HasSum
        (fun index : ZetaPrimePowerIndex =>
          completedAutocorrelationSpectralTransform_weightedPrimeSampling
            index f)
        (completedAutocorrelationSpectralTransform_weightedPrimeSamplingTraceEnergy
          f) :=
    completedAutocorrelationSpectralTransform_weightedPrimeSampling_hasSum_traceEnergy_source
      f C₀ k hbound
  have hnonnegative :
      ∀ index : ZetaPrimePowerIndex,
        0 ≤
          completedAutocorrelationSpectralTransform_weightedPrimeSampling
            index f := by
    intro index
    exact
      completedAutocorrelationSpectralTransform_weightedPrimeSampling_nonnegative
        index f
  have hfinite :
      ∀ s : Finset ZetaPrimePowerIndex,
        ∑ index in s,
          completedAutocorrelationSpectralTransform_weightedPrimeSampling
            index f ≤
          completedAutocorrelationSpectralTransform_weightedPrimeSamplingTraceEnergy
            f := by
    intro s
    exact
      sum_le_hasSum
        s
        (fun index membership => hnonnegative index)
        hhasSum
  exact hfinite

/-- Trace reconstruction gives summability of the weighted prime-center
sampling family as a positive completed trace stream.

This is the correct trace-theoretic source statement: the weighted prime
sampling stream is controlled by the completed boundary trace as a whole.
It is intentionally not routed through pointwise polynomial decay of
`zetaCompletedSpectralLaplaceTransform` on the real prime-center axis, since
that would be the wrong Paley-Wiener direction. -/
theorem completedAutocorrelationSpectralTransform_weightedPrimeSampling_summable_traceEnergy_source
    (f : ZetaAdmissibleFunction) (C₀ : ℝ) (k : ℕ)
    (hbound : f.PrimeCenterSpectralPolynomialBound C₀ k) :
    Summable
      (fun index : ZetaPrimePowerIndex =>
        completedAutocorrelationSpectralTransform_weightedPrimeSampling
          index f) := by
  exact
    (completedAutocorrelationSpectralTransform_weightedPrimeSampling_hasSum_traceEnergy_source
      f C₀ k hbound).summable

/-- Trace reconstruction identifies the finite weighted prime-center sampling
windows with the completed prime trace-energy scalar in the limit. -/
theorem completedAutocorrelationSpectralTransform_weightedPrimeSamplingWindow_tendsto_traceEnergy_source
    (f : ZetaAdmissibleFunction) (C₀ : ℝ) (k : ℕ)
    (hbound : f.PrimeCenterSpectralPolynomialBound C₀ k) :
    Filter.Tendsto
      (fun N : ℕ =>
        ∑ index in ZetaPrimePowerIndex.box N,
          completedAutocorrelationSpectralTransform_weightedPrimeSampling
            index f)
      Filter.atTop
      (nhds
        (completedAutocorrelationSpectralTransform_weightedPrimeSamplingTraceEnergy
          f)) := by
  have hlimit :=
    ZetaPrimePowerIndex.tendsto_sum_box_tsum_of_summable
      (fun index : ZetaPrimePowerIndex =>
        completedAutocorrelationSpectralTransform_weightedPrimeSampling
          index f)
      (completedAutocorrelationSpectralTransform_weightedPrimeSampling_summable_traceEnergy_source
        f C₀ k hbound)
  have hsum :=
    completedAutocorrelationSpectralTransform_weightedPrimeSampling_hasSum_traceEnergy_source
      f C₀ k hbound
  have hnhds :
      nhds
          (∑' index : ZetaPrimePowerIndex,
            completedAutocorrelationSpectralTransform_weightedPrimeSampling
              index f) =
        nhds
          (completedAutocorrelationSpectralTransform_weightedPrimeSamplingTraceEnergy
            f) := congrArg nhds hsum.tsum_eq
  exact Eq.subst
    (motive := fun value : ℝ =>
      Filter.Tendsto
        (fun N : ℕ =>
          ∑ index in ZetaPrimePowerIndex.box N,
            completedAutocorrelationSpectralTransform_weightedPrimeSampling
              index f)
        Filter.atTop (nhds value))
    hsum.tsum_eq hlimit

/-- Trace reconstruction gives the weighted prime sampling HasSum identity
against its trace-energy scalar. -/
theorem completedAutocorrelationSpectralTransform_weightedPrimeSampling_hasSum_traceReconstruction_source
    (f : ZetaAdmissibleFunction) (C₀ : ℝ) (k : ℕ)
    (hbound : f.PrimeCenterSpectralPolynomialBound C₀ k) :
    HasSum
      (fun index : ZetaPrimePowerIndex =>
        completedAutocorrelationSpectralTransform_weightedPrimeSampling
          index f)
      (completedAutocorrelationSpectralTransform_weightedPrimeSamplingTraceEnergy
        f) := by
  exact
    completedAutocorrelationSpectralTransform_weightedPrimeSampling_hasSum_traceEnergy_source
      f C₀ k hbound

/-- Trace reconstruction gives summability of the weighted prime sampling
stream actually consumed by the prime spectral majorant. -/
theorem completedAutocorrelationSpectralTransform_weightedPrimeSampling_summable_traceReconstruction_source
    (f : ZetaAdmissibleFunction) (C₀ : ℝ) (k : ℕ)
    (hbound : f.PrimeCenterSpectralPolynomialBound C₀ k) :
    Summable
      (fun index : ZetaPrimePowerIndex =>
        completedAutocorrelationSpectralTransform_weightedPrimeSampling
          index f) := by
  exact
    (completedAutocorrelationSpectralTransform_weightedPrimeSampling_hasSum_traceReconstruction_source
      f C₀ k hbound).summable

/-- Trace reconstruction controls the weighted completed spectral sampling
family by a completed prime-center trace-energy series. -/
theorem completedAutocorrelationSpectralTransform_weightedPrimeSampling_hasSum_ownerTraceReconstruction
    (f : ZetaAdmissibleFunction) (C₀ : ℝ) (k : ℕ)
    (hbound : f.PrimeCenterSpectralPolynomialBound C₀ k) :
    HasSum
      (fun index : ZetaPrimePowerIndex =>
        completedAutocorrelationSpectralTransform_weightedPrimeSampling
          index f)
      (completedAutocorrelationSpectralTransform_weightedPrimeSamplingTraceEnergy
        f) := by
  exact
    completedAutocorrelationSpectralTransform_weightedPrimeSampling_hasSum_traceReconstruction_source
      f C₀ k hbound

/-- Trace reconstruction controls the weighted completed spectral sampling
family by an absolutely summable trace envelope. -/
theorem completedAutocorrelationSpectralTransform_weightedPrimeSampling_summable_ownerTraceReconstruction
    (f : ZetaAdmissibleFunction) (C₀ : ℝ) (k : ℕ)
    (hbound : f.PrimeCenterSpectralPolynomialBound C₀ k) :
    Summable
      (fun index : ZetaPrimePowerIndex =>
        completedAutocorrelationSpectralTransform_weightedPrimeSampling
          index f) := by
  exact
    (completedAutocorrelationSpectralTransform_weightedPrimeSampling_hasSum_ownerTraceReconstruction
      f C₀ k hbound).summable

/-- Public owner form of trace-reconstruction summability for the completed
prime sampling density actually consumed by the spectral majorant. -/
theorem completedAutocorrelationSpectralTransform_weightedPrimeSampling_summable_ownerSamplingDecay
    (f : ZetaAdmissibleFunction) (C₀ : ℝ) (k : ℕ)
    (hbound : f.PrimeCenterSpectralPolynomialBound C₀ k) :
    Summable
      (fun index : ZetaPrimePowerIndex =>
        completedAutocorrelationSpectralTransform_weightedPrimeSampling
          index f) := by
  exact
    completedAutocorrelationSpectralTransform_weightedPrimeSampling_summable_ownerTraceReconstruction
      f C₀ k hbound

end ZetaAdmissibleFunction

end
end LFunctions
end Boundary
