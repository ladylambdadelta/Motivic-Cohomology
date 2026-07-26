import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaCompletedHilbertSource.ZetaHermitianPacket.CompletedPrimePowerSampling
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaCompletedHilbertSource.ZetaHermitianPacket.PrimeCenterSamplingDensityDecay
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaCompletedHilbertSource.ZetaHermitianPacket.PrimeCenterSamplingDecayParts.TraceBesselParts.PrimeWeightedSamplingDiagonalDebtBessel
import Mathlib.Topology.Algebra.InfiniteSum.Order

/-!
# Prime weighted sampling trace-energy primitive

This file owns the finite trace-energy Bessel primitive for the positive
weighted completed prime-center sampling stream.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open scoped BigOperators

namespace ZetaAdmissibleFunction

/-- The finite projection energy of the positive weighted completed
prime-center sampling stream. -/
noncomputable def completedAutocorrelationSpectralTransform_weightedPrimeSamplingFiniteProjectionEnergy
    (s : Finset ZetaPrimePowerIndex) (f : ZetaAdmissibleFunction) : ℝ :=
  ∑ index in s,
    completedAutocorrelationSpectralTransform_weightedPrimeSampling
      index f

/-- The finite weighted prime-center sampling projection energy unfolds to its
finite sampling sum. -/
theorem completedAutocorrelationSpectralTransform_weightedPrimeSamplingFiniteProjectionEnergy_eq_sum
    (s : Finset ZetaPrimePowerIndex) (f : ZetaAdmissibleFunction) :
    completedAutocorrelationSpectralTransform_weightedPrimeSamplingFiniteProjectionEnergy
        s f =
      ∑ index in s,
        completedAutocorrelationSpectralTransform_weightedPrimeSampling
          index f :=
  Eq.refl
    (completedAutocorrelationSpectralTransform_weightedPrimeSamplingFiniteProjectionEnergy
      s f)

/-- The positive weighted prime sampling coordinate is dominated by the
two-face completed spectral-coordinate majorant. -/
theorem completedAutocorrelationSpectralTransform_weightedPrimeSampling_le_spectralCoordinateMajorant_traceEnergy_source
    (index : ZetaPrimePowerIndex) (f : ZetaAdmissibleFunction) :
    completedAutocorrelationSpectralTransform_weightedPrimeSampling
        index f ≤
      zetaCompletedPrimeSpectralCoordinateMajorant index f :=
  let hsample_eq_weighted :
      zetaCompletedPrimePositiveWeightedSampleNormSq index f =
        completedAutocorrelationSpectralTransform_weightedPrimeSampling
          index f :=
    zetaCompletedPrimePositiveWeightedSampleNormSq_eq_weightedPrimeSampling
      index f
  let hnorm_eq_sample :
      ‖zetaCompletedPrimeSpectralAmplitudeIndex index f‖ ^ 2 =
        zetaCompletedPrimePositiveWeightedSampleNormSq index f :=
    zetaCompletedPrimeSpectralAmplitudeIndex_norm_sq_eq_weightedSampleNormSq
      index f
  let hnorm_eq_weighted :
      ‖zetaCompletedPrimeSpectralAmplitudeIndex index f‖ ^ 2 =
        completedAutocorrelationSpectralTransform_weightedPrimeSampling
          index f :=
    hnorm_eq_sample.trans hsample_eq_weighted
  let hright_nonnegative :
      0 ≤ ‖zetaCompletedPrimeOppositeSpectralAmplitudeIndex index f‖ ^ 2 :=
    sq_nonneg ‖zetaCompletedPrimeOppositeSpectralAmplitudeIndex index f‖
  let hnorm_le_majorant :
      ‖zetaCompletedPrimeSpectralAmplitudeIndex index f‖ ^ 2 ≤
        zetaCompletedPrimeSpectralCoordinateMajorant index f :=
    le_add_of_nonneg_right hright_nonnegative
  Eq.subst
    (motive := fun value : ℝ =>
      value ≤ zetaCompletedPrimeSpectralCoordinateMajorant index f)
    hnorm_eq_weighted
    hnorm_le_majorant

/-- Every finite positive prime spectral-amplitude subtrace is dominated by
some rectangular box subtrace. -/
theorem zetaCompletedPrimeSpectralAmplitudeIndex_normSq_finiteSubtrace_le_boxSubtrace_traceEnergy_source
    (f : ZetaAdmissibleFunction) :
    ∀ s : Finset ZetaPrimePowerIndex,
      ∃ N : ℕ,
        ∑ index in s,
          ‖zetaCompletedPrimeSpectralAmplitudeIndex index f‖ ^ 2 ≤
        ∑ index in ZetaPrimePowerIndex.box N,
          ‖zetaCompletedPrimeSpectralAmplitudeIndex index f‖ ^ 2 :=
  fun s =>
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
            sq_nonneg ‖zetaCompletedPrimeSpectralAmplitudeIndex index f‖)
      Exists.intro N hsum

/-- Nongenuine prime-power indices have zero positive completed prime spectral
amplitude. -/
theorem zetaCompletedPrimeSpectralAmplitudeIndex_eq_zero_of_not_isGenuine_traceEnergy_source
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
theorem zetaCompletedPrimeSpectralAmplitudeIndex_normSq_eq_zero_of_not_isGenuine_traceEnergy_source
    (index : ZetaPrimePowerIndex) (f : ZetaAdmissibleFunction)
    (hindex : ¬ ZetaPrimePowerIndex.IsGenuine index) :
    ‖zetaCompletedPrimeSpectralAmplitudeIndex index f‖ ^ 2 = 0 :=
  let hamplitude :
      zetaCompletedPrimeSpectralAmplitudeIndex index f = 0 :=
    zetaCompletedPrimeSpectralAmplitudeIndex_eq_zero_of_not_isGenuine_traceEnergy_source
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

/-- Rectangular boxes and genuine prime-power windows give the same positive
prime spectral amplitude norm-square sum. -/
theorem sum_box_zetaCompletedPrimeSpectralAmplitudeIndex_normSq_eq_sum_window_traceEnergy_source
    (N : ℕ) (f : ZetaAdmissibleFunction) :
    (∑ index in ZetaPrimePowerIndex.box N,
      ‖zetaCompletedPrimeSpectralAmplitudeIndex index f‖ ^ 2) =
      ∑ index in ZetaPrimePowerIndex.window N,
        ‖zetaCompletedPrimeSpectralAmplitudeIndex index f‖ ^ 2 :=
  ZetaPrimePowerIndex.sum_box_eq_sum_window_of_zero_not_isGenuine
    (fun index : ZetaPrimePowerIndex =>
      ‖zetaCompletedPrimeSpectralAmplitudeIndex index f‖ ^ 2)
    (fun index hindex =>
      zetaCompletedPrimeSpectralAmplitudeIndex_normSq_eq_zero_of_not_isGenuine_traceEnergy_source
        index f hindex)
    N

/-- Source finite trace-energy domination for the positive weighted completed
prime-center sampling stream. -/
theorem completedAutocorrelationSpectralTransform_weightedPrimeSampling_finiteSubtrace_upperBound_traceEnergy_owner_source
    (f : ZetaAdmissibleFunction) (C : ℝ) (k : ℕ)
    (hbound : PrimeCenterSpectralPolynomialBound f C k) :
    ∃ C : ℝ,
      ∀ s : Finset ZetaPrimePowerIndex,
        ∑ index in s,
      completedAutocorrelationSpectralTransform_weightedPrimeSampling
            index f ≤ C := by
  exact weightedPrimeSampling_finiteSubtrace_upperBound_of_spectralPolynomialBound
    f C k hbound

theorem zetaCompletedPrimeSpectralAmplitudeIndex_normSq_finiteSubtrace_bessel_traceEnergy_transport
    (f : ZetaAdmissibleFunction) (C : ℝ) (k : ℕ)
    (hbound : PrimeCenterSpectralPolynomialBound f C k) :
    ∃ C : ℝ,
      ∀ s : Finset ZetaPrimePowerIndex,
        ∑ index in s,
          ‖zetaCompletedPrimeSpectralAmplitudeIndex index f‖ ^ 2 ≤ C :=
  match
    completedAutocorrelationSpectralTransform_weightedPrimeSampling_finiteSubtrace_upperBound_traceEnergy_owner_source
      f C k hbound with
  | ⟨C, hC⟩ =>
      ⟨C, fun s =>
        Eq.subst
          (motive := fun value : ℝ => value ≤ C)
          (Finset.sum_congr
            (Eq.refl s)
            (fun index membership =>
              (zetaCompletedPrimeSpectralAmplitudeIndex_norm_sq_eq_weightedSampleNormSq
                index f).trans
                (zetaCompletedPrimePositiveWeightedSampleNormSq_eq_weightedPrimeSampling
                  index f))).symm
          (hC s)⟩

/- Source genuine-window Bessel domination for the positive completed prime
spectral amplitude norm-square stream. -/
theorem zetaCompletedPrimeSpectralAmplitudeIndex_normSq_windowSubtrace_bessel_traceEnergy_source
    (f : ZetaAdmissibleFunction) (C : ℝ) (k : ℕ)
    (hbound : PrimeCenterSpectralPolynomialBound f C k) :
    ∃ C : ℝ,
      ∀ N : ℕ,
        ∑ index in ZetaPrimePowerIndex.window N,
          ‖zetaCompletedPrimeSpectralAmplitudeIndex index f‖ ^ 2 ≤ C :=
  match
    zetaCompletedPrimeSpectralAmplitudeIndex_normSq_finiteSubtrace_bessel_traceEnergy_transport
      f C k hbound with
  | ⟨C, hC⟩ =>
      Exists.intro C
        (fun N =>
          hC (ZetaPrimePowerIndex.window N))

/-- Source rectangular-box Bessel domination for the positive completed prime
spectral amplitude norm-square stream. -/
theorem zetaCompletedPrimeSpectralAmplitudeIndex_normSq_boxSubtrace_bessel_traceEnergy_source
    (f : ZetaAdmissibleFunction) (C : ℝ) (k : ℕ)
    (hbound : PrimeCenterSpectralPolynomialBound f C k) :
    ∃ C : ℝ,
      ∀ N : ℕ,
        ∑ index in ZetaPrimePowerIndex.box N,
          ‖zetaCompletedPrimeSpectralAmplitudeIndex index f‖ ^ 2 ≤ C :=
  match
    zetaCompletedPrimeSpectralAmplitudeIndex_normSq_windowSubtrace_bessel_traceEnergy_source
      f C k hbound with
  | ⟨C, hC⟩ =>
      let hbox :
          ∀ N : ℕ,
            ∑ index in ZetaPrimePowerIndex.box N,
              ‖zetaCompletedPrimeSpectralAmplitudeIndex index f‖ ^ 2 ≤ C :=
        fun N =>
        Eq.subst
          (motive := fun value : ℝ => value ≤ C)
          (sum_box_zetaCompletedPrimeSpectralAmplitudeIndex_normSq_eq_sum_window_traceEnergy_source
            N f).symm
          (hC N)
      Exists.intro C hbox

/-- Source finite-subtrace Bessel domination for the positive completed prime
spectral amplitude norm-square stream. -/
theorem zetaCompletedPrimeSpectralAmplitudeIndex_normSq_finiteSubtrace_bessel_traceEnergy_source
    (f : ZetaAdmissibleFunction) (C : ℝ) (k : ℕ)
    (hbound : PrimeCenterSpectralPolynomialBound f C k) :
    ∃ C : ℝ,
      ∀ s : Finset ZetaPrimePowerIndex,
        ∑ index in s,
          ‖zetaCompletedPrimeSpectralAmplitudeIndex index f‖ ^ 2 ≤ C :=
  match
    zetaCompletedPrimeSpectralAmplitudeIndex_normSq_boxSubtrace_bessel_traceEnergy_source
      f C k hbound with
  | ⟨C, hC⟩ =>
      let hfinite :
          ∀ s : Finset ZetaPrimePowerIndex,
            ∑ index in s,
              ‖zetaCompletedPrimeSpectralAmplitudeIndex index f‖ ^ 2 ≤ C :=
        fun s =>
        match
          zetaCompletedPrimeSpectralAmplitudeIndex_normSq_finiteSubtrace_le_boxSubtrace_traceEnergy_source
            f s with
        | ⟨N, hleBox⟩ =>
            le_trans hleBox (hC N)
      Exists.intro C hfinite

/-- A diagonal-debt real-coordinate owner `HasSum` gives source summability
for the positive completed prime spectral-amplitude norm-square stream. -/
theorem zetaCompletedPrimeSpectralAmplitudeIndex_normSq_summable_of_diagonalDebtCoordinate_re_hasSum_traceEnergy_source
    (f : ZetaAdmissibleFunction) (C : ℝ)
    (hhasSum :
      HasSum
        (fun index : ZetaPrimePowerIndex =>
          Complex.re
            (zetaCompletedPrimeDefectKernelDiagonalDebtCoordinate index f))
        C) :
    Summable
      (fun index : ZetaPrimePowerIndex =>
        ‖zetaCompletedPrimeSpectralAmplitudeIndex index f‖ ^ 2) :=
  let hnonnegative :
      0 ≤
        fun index : ZetaPrimePowerIndex =>
          ‖zetaCompletedPrimeSpectralAmplitudeIndex index f‖ ^ 2 :=
    fun index =>
      sq_nonneg
        ‖zetaCompletedPrimeSpectralAmplitudeIndex index f‖
  let hfinite :
      ∀ s : Finset ZetaPrimePowerIndex,
        (∑ index in s,
          ‖zetaCompletedPrimeSpectralAmplitudeIndex index f‖ ^ 2) ≤ C :=
    zetaCompletedPrimeSpectralAmplitudeIndex_normSq_finiteSubtrace_bessel_of_diagonalDebtCoordinate_re_hasSum_traceEnergy_source
      f C hhasSum
  summable_of_sum_le hnonnegative hfinite

/-- A diagonal-debt real-coordinate owner `HasSum` gives source summability
for the positive weighted completed prime-center sampling stream. -/
theorem completedAutocorrelationSpectralTransform_weightedPrimeSampling_summable_of_diagonalDebtCoordinate_re_hasSum_traceEnergy_source
    (f : ZetaAdmissibleFunction) (C : ℝ)
    (hhasSum :
      HasSum
        (fun index : ZetaPrimePowerIndex =>
          Complex.re
            (zetaCompletedPrimeDefectKernelDiagonalDebtCoordinate index f))
        C) :
    Summable
      (fun index : ZetaPrimePowerIndex =>
        completedAutocorrelationSpectralTransform_weightedPrimeSampling
          index f) :=
  let hnonnegative :
      0 ≤
        fun index : ZetaPrimePowerIndex =>
          completedAutocorrelationSpectralTransform_weightedPrimeSampling
            index f :=
    fun index =>
      completedAutocorrelationSpectralTransform_weightedPrimeSampling_nonnegative
        index f
  let hfinite :
      ∀ s : Finset ZetaPrimePowerIndex,
        (∑ index in s,
          completedAutocorrelationSpectralTransform_weightedPrimeSampling
            index f) ≤ C :=
    completedAutocorrelationSpectralTransform_weightedPrimeSampling_finiteSubtrace_bessel_of_diagonalDebtCoordinate_re_hasSum_traceEnergy_source
      f C hhasSum
  summable_of_sum_le hnonnegative hfinite

/-- A diagonal-debt real-coordinate owner `HasSum` reconstructs the positive
weighted completed prime-center sampling stream at its raw `tsum`. -/
theorem completedAutocorrelationSpectralTransform_weightedPrimeSampling_hasSum_tsum_of_diagonalDebtCoordinate_re_hasSum_traceEnergy_source
    (f : ZetaAdmissibleFunction) (C : ℝ)
    (hhasSum :
      HasSum
        (fun index : ZetaPrimePowerIndex =>
          Complex.re
            (zetaCompletedPrimeDefectKernelDiagonalDebtCoordinate index f))
        C) :
    HasSum
      (fun index : ZetaPrimePowerIndex =>
        completedAutocorrelationSpectralTransform_weightedPrimeSampling
          index f)
      (∑' index : ZetaPrimePowerIndex,
        completedAutocorrelationSpectralTransform_weightedPrimeSampling
          index f) :=
  (completedAutocorrelationSpectralTransform_weightedPrimeSampling_summable_of_diagonalDebtCoordinate_re_hasSum_traceEnergy_source
    f C hhasSum).hasSum

/-- Source summability of the positive completed prime spectral amplitude
norm-square stream. -/
theorem zetaCompletedPrimeSpectralAmplitudeIndex_normSq_summable_traceEnergy_source
    (f : ZetaAdmissibleFunction) (C : ℝ) (k : ℕ)
    (hbound : PrimeCenterSpectralPolynomialBound f C k) :
    Summable
      (fun index : ZetaPrimePowerIndex =>
        ‖zetaCompletedPrimeSpectralAmplitudeIndex index f‖ ^ 2) :=
  let hnonnegative :
      0 ≤
        fun index : ZetaPrimePowerIndex =>
          ‖zetaCompletedPrimeSpectralAmplitudeIndex index f‖ ^ 2 :=
    fun index =>
      sq_nonneg ‖zetaCompletedPrimeSpectralAmplitudeIndex index f‖
  match
    zetaCompletedPrimeSpectralAmplitudeIndex_normSq_finiteSubtrace_bessel_traceEnergy_source
      f C k hbound with
  | ⟨C, hC⟩ =>
      summable_of_sum_le hnonnegative hC

theorem zetaCompletedPrimeSpectralAmplitudeIndex_reflect_normSq_eq_opposite_normSq_traceEnergy_source
    (f : ZetaAdmissibleFunction) (index : ZetaPrimePowerIndex) :
    ‖zetaCompletedPrimeSpectralAmplitudeIndex
        index (ZetaAdmissibleFunction.reflect f)‖ ^ 2 =
      ‖zetaCompletedPrimeOppositeSpectralAmplitudeIndex index f‖ ^ 2 :=
  let hpositiveNorm :
      ‖zetaCompletedPrimeSpectralAmplitudeIndex
          index (ZetaAdmissibleFunction.reflect f)‖ ^ 2 =
        zetaCompletedPrimePositiveWeightedSampleNormSq
          index (ZetaAdmissibleFunction.reflect f) :=
    zetaCompletedPrimeSpectralAmplitudeIndex_norm_sq_eq_weightedSampleNormSq
      index (ZetaAdmissibleFunction.reflect f)
  let hreflect :
      zetaCompletedPrimePositiveWeightedSampleNormSq
          index (ZetaAdmissibleFunction.reflect f) =
        zetaCompletedPrimeOppositeWeightedSampleNormSq index f :=
    (zetaCompletedPrimeOppositeWeightedSampleNormSq_eq_positive_reflect
      index f).symm
  let hoppositeNorm :
      zetaCompletedPrimeOppositeWeightedSampleNormSq index f =
        ‖zetaCompletedPrimeOppositeSpectralAmplitudeIndex index f‖ ^ 2 :=
    (zetaCompletedPrimeOppositeSpectralAmplitudeIndex_norm_sq_eq_weightedSampleNormSq
      index f).symm
  hpositiveNorm.trans (hreflect.trans hoppositeNorm)

/-- Source summability of the opposite completed prime spectral amplitude
norm-square stream. -/
theorem zetaCompletedPrimeOppositeSpectralAmplitudeIndex_normSq_summable_traceEnergy_source
    (f : ZetaAdmissibleFunction) (C : ℝ) (k : ℕ)
    (hbound : PrimeCenterSpectralPolynomialBound
      (ZetaAdmissibleFunction.reflect f) C k) :
    Summable
      (fun index : ZetaPrimePowerIndex =>
        ‖zetaCompletedPrimeOppositeSpectralAmplitudeIndex index f‖ ^ 2) :=
  let hpositiveReflect :
      Summable
        (fun index : ZetaPrimePowerIndex =>
          ‖zetaCompletedPrimeSpectralAmplitudeIndex
              index (ZetaAdmissibleFunction.reflect f)‖ ^ 2) :=
    zetaCompletedPrimeSpectralAmplitudeIndex_normSq_summable_traceEnergy_source
      (ZetaAdmissibleFunction.reflect f) C k hbound
  hpositiveReflect.congr
    (fun index : ZetaPrimePowerIndex =>
      zetaCompletedPrimeSpectralAmplitudeIndex_reflect_normSq_eq_opposite_normSq_traceEnergy_source
        f index)

/-- The completed prime spectral-coordinate majorant is pointwise the sum of
the positive and opposite face norm-square streams. -/
theorem zetaCompletedPrimeSpectralCoordinateMajorant_eq_normSq_add_normSq_traceEnergy_source
    (f : ZetaAdmissibleFunction) :
    (fun index : ZetaPrimePowerIndex =>
      zetaCompletedPrimeSpectralCoordinateMajorant index f) =
      fun index : ZetaPrimePowerIndex =>
        ‖zetaCompletedPrimeSpectralAmplitudeIndex index f‖ ^ 2 +
          ‖zetaCompletedPrimeOppositeSpectralAmplitudeIndex index f‖ ^ 2 :=
  funext
    (fun index : ZetaPrimePowerIndex =>
      Eq.refl (zetaCompletedPrimeSpectralCoordinateMajorant index f))

/-- Source summability of the completed prime spectral-coordinate majorant on
autocorrelation probes. -/
theorem zetaCompletedPrimeSpectralCoordinateMajorant_summable_traceEnergy_source
    (f : ZetaAdmissibleFunction) (Cpos : ℝ) (kpos : ℕ)
    (hpos : PrimeCenterSpectralPolynomialBound f Cpos kpos)
    (Cneg : ℝ) (kneg : ℕ)
    (hneg : PrimeCenterSpectralPolynomialBound
      (ZetaAdmissibleFunction.reflect f) Cneg kneg) :
    Summable
      (fun index : ZetaPrimePowerIndex =>
        zetaCompletedPrimeSpectralCoordinateMajorant index f) :=
  let hpositive :
      Summable
        (fun index : ZetaPrimePowerIndex =>
          ‖zetaCompletedPrimeSpectralAmplitudeIndex index f‖ ^ 2) :=
    zetaCompletedPrimeSpectralAmplitudeIndex_normSq_summable_traceEnergy_source
      f Cpos kpos hpos
  let hopposite :
      Summable
        (fun index : ZetaPrimePowerIndex =>
          ‖zetaCompletedPrimeOppositeSpectralAmplitudeIndex index f‖ ^ 2) :=
    zetaCompletedPrimeOppositeSpectralAmplitudeIndex_normSq_summable_traceEnergy_source
      f Cneg kneg hneg
  (hpositive.add hopposite).congr
    (fun index : ZetaPrimePowerIndex =>
      (congrArg
        (fun value : ZetaPrimePowerIndex → ℝ => value index)
        (zetaCompletedPrimeSpectralCoordinateMajorant_eq_normSq_add_normSq_traceEnergy_source
          f)).symm)

/-- The norm of each positive weighted prime sampling coordinate is bounded by
the completed spectral-coordinate majorant. -/
theorem completedAutocorrelationSpectralTransform_weightedPrimeSampling_norm_le_spectralCoordinateMajorant_traceEnergy_source
    (index : ZetaPrimePowerIndex) (f : ZetaAdmissibleFunction) :
    ‖completedAutocorrelationSpectralTransform_weightedPrimeSampling
        index f‖ ≤
      zetaCompletedPrimeSpectralCoordinateMajorant index f :=
  let hnonnegative :
      0 ≤
        completedAutocorrelationSpectralTransform_weightedPrimeSampling
          index f :=
    completedAutocorrelationSpectralTransform_weightedPrimeSampling_nonnegative
      index f
  let hnorm :
      ‖completedAutocorrelationSpectralTransform_weightedPrimeSampling
          index f‖ =
        completedAutocorrelationSpectralTransform_weightedPrimeSampling
          index f :=
    Real.norm_of_nonneg hnonnegative
  Eq.subst
    (motive := fun value : ℝ =>
      value ≤ zetaCompletedPrimeSpectralCoordinateMajorant index f)
    hnorm.symm
    (completedAutocorrelationSpectralTransform_weightedPrimeSampling_le_spectralCoordinateMajorant_traceEnergy_source
      index f)

/-! This is the acyclic trace-energy cut: once an upstream arithmetic owner has
proved summability of the coordinate majorant, the sampling stream and all of
its finite subtraces follow by positive norm domination. -/

theorem completedAutocorrelationSpectralTransform_weightedPrimeSampling_summable_of_majorant_summable_traceEnergy_owner
    (f : ZetaAdmissibleFunction)
    (hmajorant :
      Summable
        (fun index : ZetaPrimePowerIndex =>
          zetaCompletedPrimeSpectralCoordinateMajorant index f)) :
    Summable
      (fun index : ZetaPrimePowerIndex =>
        completedAutocorrelationSpectralTransform_weightedPrimeSampling
          index f) :=
  Summable.of_norm_bounded
    (fun index : ZetaPrimePowerIndex =>
      zetaCompletedPrimeSpectralCoordinateMajorant index f)
    hmajorant
    (fun index : ZetaPrimePowerIndex =>
      completedAutocorrelationSpectralTransform_weightedPrimeSampling_norm_le_spectralCoordinateMajorant_traceEnergy_source
        index f)

theorem completedAutocorrelationSpectralTransform_weightedPrimeSampling_finiteSubtrace_upperBound_of_majorant_summable_traceEnergy_owner
    (f : ZetaAdmissibleFunction)
    (hmajorant :
      Summable
        (fun index : ZetaPrimePowerIndex =>
          zetaCompletedPrimeSpectralCoordinateMajorant index f)) :
    ∃ C : ℝ,
      ∀ s : Finset ZetaPrimePowerIndex,
        ∑ index in s,
          completedAutocorrelationSpectralTransform_weightedPrimeSampling
            index f ≤ C := by
  have hsum :=
    completedAutocorrelationSpectralTransform_weightedPrimeSampling_summable_of_majorant_summable_traceEnergy_owner
      f hmajorant
  have hhasSum := hsum.hasSum
  have hnonnegative :
      ∀ index : ZetaPrimePowerIndex,
        0 ≤ completedAutocorrelationSpectralTransform_weightedPrimeSampling
          index f := by
    intro index
    exact completedAutocorrelationSpectralTransform_weightedPrimeSampling_nonnegative
      index f
  exact ⟨∑' index : ZetaPrimePowerIndex,
      completedAutocorrelationSpectralTransform_weightedPrimeSampling index f,
    fun s => sum_le_hasSum s
      (fun index membership => hnonnegative index) hhasSum⟩

/-- Source summability for the positive weighted completed prime-center
sampling stream. -/
theorem completedAutocorrelationSpectralTransform_weightedPrimeSampling_summable_traceEnergy_owner_source
    (f : ZetaAdmissibleFunction) (Cpos : ℝ) (kpos : ℕ)
    (hpos : PrimeCenterSpectralPolynomialBound f Cpos kpos)
    (Cneg : ℝ) (kneg : ℕ)
    (hneg : PrimeCenterSpectralPolynomialBound
      (ZetaAdmissibleFunction.reflect f) Cneg kneg) :
    Summable
      (fun index : ZetaPrimePowerIndex =>
        completedAutocorrelationSpectralTransform_weightedPrimeSampling
          index f) :=
  Summable.of_norm_bounded
    (fun index : ZetaPrimePowerIndex =>
      zetaCompletedPrimeSpectralCoordinateMajorant index f)
    (zetaCompletedPrimeSpectralCoordinateMajorant_summable_traceEnergy_source
      f Cpos kpos hpos Cneg kneg hneg)
    (fun index : ZetaPrimePowerIndex =>
      completedAutocorrelationSpectralTransform_weightedPrimeSampling_norm_le_spectralCoordinateMajorant_traceEnergy_source
        index f)

/-- Source trace reconstruction for the positive weighted completed
prime-center sampling stream. -/
theorem completedAutocorrelationSpectralTransform_weightedPrimeSampling_hasSum_traceEnergy_owner_source
    (f : ZetaAdmissibleFunction) (Cpos : ℝ) (kpos : ℕ)
    (hpos : PrimeCenterSpectralPolynomialBound f Cpos kpos)
    (Cneg : ℝ) (kneg : ℕ)
    (hneg : PrimeCenterSpectralPolynomialBound
      (ZetaAdmissibleFunction.reflect f) Cneg kneg) :
    ∃ traceEnergy : ℝ,
      HasSum
        (fun index : ZetaPrimePowerIndex =>
          completedAutocorrelationSpectralTransform_weightedPrimeSampling
            index f)
        traceEnergy :=
  Exists.intro
    (∑' index : ZetaPrimePowerIndex,
      completedAutocorrelationSpectralTransform_weightedPrimeSampling
        index f)
    (completedAutocorrelationSpectralTransform_weightedPrimeSampling_summable_traceEnergy_owner_source
      f Cpos kpos hpos Cneg kneg hneg).hasSum

/-- Source finite-subtrace domination from the positive trace reconstruction
of the weighted completed prime-center sampling stream. -/
theorem completedAutocorrelationSpectralTransform_weightedPrimeSampling_finiteSubtrace_upperBound_of_hasSum_traceEnergy_source
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
    completedAutocorrelationSpectralTransform_weightedPrimeSampling_hasSum_traceEnergy_owner_source
      f Cpos kpos hpos Cneg kneg hneg with
  | ⟨traceEnergy, htraceEnergy⟩ =>
      let hnonnegative :
          ∀ index : ZetaPrimePowerIndex,
            0 ≤
              completedAutocorrelationSpectralTransform_weightedPrimeSampling
                index f :=
        fun index =>
          completedAutocorrelationSpectralTransform_weightedPrimeSampling_nonnegative
            index f
      let hbound :
          ∀ s : Finset ZetaPrimePowerIndex,
            ∑ index in s,
              completedAutocorrelationSpectralTransform_weightedPrimeSampling
                index f ≤ traceEnergy :=
        fun s =>
          sum_le_hasSum
            s
            (fun index membership => hnonnegative index)
            htraceEnergy
      Exists.intro traceEnergy hbound

/-- Analytic source boundedness of the finite weighted prime-center sampling
projection-energy range.  This is the trace-energy Bessel primitive consumed
by the supremum package below. -/
theorem completedAutocorrelationSpectralTransform_weightedPrimeSamplingFiniteProjectionEnergy_range_bddAbove_traceEnergy_source
    (f : ZetaAdmissibleFunction) (Cpos : ℝ) (kpos : ℕ)
    (hpos : PrimeCenterSpectralPolynomialBound f Cpos kpos)
    (Cneg : ℝ) (kneg : ℕ)
    (hneg : PrimeCenterSpectralPolynomialBound
      (ZetaAdmissibleFunction.reflect f) Cneg kneg) :
    BddAbove
      (Set.range
        (fun s : Finset ZetaPrimePowerIndex =>
          completedAutocorrelationSpectralTransform_weightedPrimeSamplingFiniteProjectionEnergy
            s f)) :=
  match
    completedAutocorrelationSpectralTransform_weightedPrimeSampling_finiteSubtrace_upperBound_of_hasSum_traceEnergy_source
      f Cpos kpos hpos Cneg kneg hneg with
  | ⟨C, hC⟩ =>
      let hupper :
          ∀ value : ℝ,
            value ∈
              Set.range
                (fun s : Finset ZetaPrimePowerIndex =>
                  completedAutocorrelationSpectralTransform_weightedPrimeSamplingFiniteProjectionEnergy
                    s f) →
            value ≤ C :=
        fun value hvalue =>
        match hvalue with
        | ⟨s, hvalue_eq⟩ =>
            let hprojection :
                completedAutocorrelationSpectralTransform_weightedPrimeSamplingFiniteProjectionEnergy
                    s f ≤ C :=
              Eq.subst
                (motive := fun projectionValue : ℝ => projectionValue ≤ C)
                (completedAutocorrelationSpectralTransform_weightedPrimeSamplingFiniteProjectionEnergy_eq_sum
                  s f).symm
                (hC s)
            Eq.subst
              (motive := fun projectionValue : ℝ => projectionValue ≤ C)
              hvalue_eq
              hprojection
      Exists.intro C hupper

/-- The Bessel trace-energy constant for the positive weighted completed
prime-center sampling stream, expressed as the supremum of finite projection
energies. -/
noncomputable def completedAutocorrelationSpectralTransform_weightedPrimeSamplingBesselConstant
    (f : ZetaAdmissibleFunction) : ℝ :=
  sSup
    (Set.range
      (fun s : Finset ZetaPrimePowerIndex =>
        completedAutocorrelationSpectralTransform_weightedPrimeSamplingFiniteProjectionEnergy
          s f))

/-- Each finite weighted prime-center sampling projection is dominated by the
named Bessel trace-energy constant. -/
theorem completedAutocorrelationSpectralTransform_weightedPrimeSamplingFiniteProjectionEnergy_le_besselConstant_traceEnergy_source
    (s : Finset ZetaPrimePowerIndex) (f : ZetaAdmissibleFunction)
    (Cpos : ℝ) (kpos : ℕ)
    (hpos : PrimeCenterSpectralPolynomialBound f Cpos kpos)
    (Cneg : ℝ) (kneg : ℕ)
    (hneg : PrimeCenterSpectralPolynomialBound
      (ZetaAdmissibleFunction.reflect f) Cneg kneg) :
    completedAutocorrelationSpectralTransform_weightedPrimeSamplingFiniteProjectionEnergy
        s f ≤
      completedAutocorrelationSpectralTransform_weightedPrimeSamplingBesselConstant
        f :=
  le_csSup
    (completedAutocorrelationSpectralTransform_weightedPrimeSamplingFiniteProjectionEnergy_range_bddAbove_traceEnergy_source
      f Cpos kpos hpos Cneg kneg hneg)
    (Set.mem_range_self s)

/-- Bessel-family boundedness for the positive weighted completed prime-center
sampling coordinates. -/
def CompletedAutocorrelationSpectralTransformWeightedPrimeSamplingBesselFamily
    (f : ZetaAdmissibleFunction) : Prop :=
  ∃ C : ℝ,
    ∀ s : Finset ZetaPrimePowerIndex,
      completedAutocorrelationSpectralTransform_weightedPrimeSamplingFiniteProjectionEnergy
        s f ≤ C

/-- The completed prime-center sampling coordinates form a Bessel family in
the trace-energy Hilbert source. -/
theorem completedAutocorrelationSpectralTransform_weightedPrimeSampling_besselFamily_traceEnergy_source
    (f : ZetaAdmissibleFunction) (Cpos : ℝ) (kpos : ℕ)
    (hpos : PrimeCenterSpectralPolynomialBound f Cpos kpos)
    (Cneg : ℝ) (kneg : ℕ)
    (hneg : PrimeCenterSpectralPolynomialBound
      (ZetaAdmissibleFunction.reflect f) Cneg kneg) :
    CompletedAutocorrelationSpectralTransformWeightedPrimeSamplingBesselFamily
      f :=
  Exists.intro
    (completedAutocorrelationSpectralTransform_weightedPrimeSamplingBesselConstant
      f)
    (fun s =>
      completedAutocorrelationSpectralTransform_weightedPrimeSamplingFiniteProjectionEnergy_le_besselConstant_traceEnergy_source
        s f Cpos kpos hpos Cneg kneg hneg)

/-- Source boundedness of the finite weighted prime-center sampling projection
energy range.  This is the Hilbert trace-energy Bessel primitive. -/
theorem completedAutocorrelationSpectralTransform_weightedPrimeSamplingFiniteProjectionEnergy_bddAbove_traceEnergy_source
    (f : ZetaAdmissibleFunction) (Cpos : ℝ) (kpos : ℕ)
    (hpos : PrimeCenterSpectralPolynomialBound f Cpos kpos)
    (Cneg : ℝ) (kneg : ℕ)
    (hneg : PrimeCenterSpectralPolynomialBound
      (ZetaAdmissibleFunction.reflect f) Cneg kneg) :
    BddAbove
      (Set.range
        (fun s : Finset ZetaPrimePowerIndex =>
          completedAutocorrelationSpectralTransform_weightedPrimeSamplingFiniteProjectionEnergy
            s f)) :=
  completedAutocorrelationSpectralTransform_weightedPrimeSamplingFiniteProjectionEnergy_range_bddAbove_traceEnergy_source
    f Cpos kpos hpos Cneg kneg hneg

/-- Source upper-bound package for finite weighted completed prime-center
sampling projection energies. -/
theorem completedAutocorrelationSpectralTransform_weightedPrimeSamplingFiniteProjectionEnergy_upperBound_traceEnergy_source
    (f : ZetaAdmissibleFunction) (Cpos : ℝ) (kpos : ℕ)
    (hpos : PrimeCenterSpectralPolynomialBound f Cpos kpos)
    (Cneg : ℝ) (kneg : ℕ)
    (hneg : PrimeCenterSpectralPolynomialBound
      (ZetaAdmissibleFunction.reflect f) Cneg kneg) :
    ∃ C : ℝ,
      ∀ s : Finset ZetaPrimePowerIndex,
        completedAutocorrelationSpectralTransform_weightedPrimeSamplingFiniteProjectionEnergy
          s f ≤ C :=
  match
    completedAutocorrelationSpectralTransform_weightedPrimeSamplingFiniteProjectionEnergy_bddAbove_traceEnergy_source
      f Cpos kpos hpos Cneg kneg hneg with
  | ⟨C, hC⟩ =>
      let hupper :
          ∀ s : Finset ZetaPrimePowerIndex,
            completedAutocorrelationSpectralTransform_weightedPrimeSamplingFiniteProjectionEnergy
              s f ≤ C :=
        fun s =>
          hC
            (Exists.intro s
              (Eq.refl
                (completedAutocorrelationSpectralTransform_weightedPrimeSamplingFiniteProjectionEnergy
                  s f)))
      Exists.intro C hupper

end ZetaAdmissibleFunction

end
end LFunctions
end Boundary
