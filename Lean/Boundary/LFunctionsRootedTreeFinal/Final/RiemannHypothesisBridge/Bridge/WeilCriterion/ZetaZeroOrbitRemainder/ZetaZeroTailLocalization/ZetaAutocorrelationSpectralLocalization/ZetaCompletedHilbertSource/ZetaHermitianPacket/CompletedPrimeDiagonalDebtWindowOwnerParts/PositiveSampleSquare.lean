import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaCompletedHilbertSource.ZetaHermitianPacket.CompletedPrimeDiagonalDebtWindowOwnerParts.PrimeAmplitudeBesselSource
import Mathlib.Order.Filter.Defs
import Mathlib.Topology.Algebra.InfiniteSum.Order

/-!
# Positive sample-square source for completed prime diagonal debt

This file owns the weighted positive sample-square summability source consumed
by the completed prime diagonal-debt spectral majorant.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open scoped BigOperators

namespace ZetaAdmissibleFunction

/-- Window Bessel domination for completed prime spectral amplitudes. -/
def ZetaCompletedPrimeSpectralAmplitudeWindowNormSqUpperBound_diagonalDebt
    (f : ZetaAdmissibleFunction) (C : ℝ) : Prop :=
  ∀ N : ℕ,
    ∑ index in ZetaPrimePowerIndex.window N,
      ‖zetaCompletedPrimeSpectralAmplitudeIndex index f‖ ^ 2 ≤ C

/-- Window Bessel domination for completed weighted prime sampling. -/
def CompletedAutocorrelationSpectralTransformWeightedPrimeSamplingWindowSubtraceUpperBound_diagonalDebt
    (f : ZetaAdmissibleFunction) (C : ℝ) : Prop :=
  ∀ N : ℕ,
    ∑ index in ZetaPrimePowerIndex.window N,
      completedAutocorrelationSpectralTransform_weightedPrimeSampling
        index f ≤ C

/-- Box Bessel domination for completed weighted prime sampling. -/
def CompletedAutocorrelationSpectralTransformWeightedPrimeSamplingBoxSubtraceUpperBound_diagonalDebt
    (f : ZetaAdmissibleFunction) (C : ℝ) : Prop :=
  ∀ N : ℕ,
    ∑ index in ZetaPrimePowerIndex.box N,
      completedAutocorrelationSpectralTransform_weightedPrimeSampling
        index f ≤ C

/-- The owner trace-energy scalar for completed weighted prime sampling. -/
noncomputable def completedAutocorrelationSpectralTransform_weightedPrimeSamplingTraceEnergy_diagonalDebt
    (f : ZetaAdmissibleFunction) : ℝ :=
  ∑' index : ZetaPrimePowerIndex,
    completedAutocorrelationSpectralTransform_weightedPrimeSampling index f

/-- The finite completed prime amplitude projection energy over a finite
prime-power index set. -/
noncomputable def zetaCompletedPrimeSpectralAmplitudeIndex_normSq_finiteProjectionEnergy_diagonalDebt
    (s : Finset ZetaPrimePowerIndex) (f : ZetaAdmissibleFunction) : ℝ :=
  ∑ index in s,
    ‖zetaCompletedPrimeSpectralAmplitudeIndex index f‖ ^ 2

/-- The finite completed prime amplitude projection energy unfolds to its
finite sum. -/
theorem zetaCompletedPrimeSpectralAmplitudeIndex_normSq_finiteProjectionEnergy_eq_sum_diagonalDebt
    (s : Finset ZetaPrimePowerIndex) (f : ZetaAdmissibleFunction) :
    zetaCompletedPrimeSpectralAmplitudeIndex_normSq_finiteProjectionEnergy_diagonalDebt
        s f =
      ∑ index in s,
        ‖zetaCompletedPrimeSpectralAmplitudeIndex index f‖ ^ 2 :=
  Eq.refl
    (zetaCompletedPrimeSpectralAmplitudeIndex_normSq_finiteProjectionEnergy_diagonalDebt
      s f)

/-- A scalar uniformly bounds all finite completed prime amplitude projection
energies. -/
def ZetaCompletedPrimeSpectralAmplitudeIndexFiniteProjectionEnergyUpperBound_diagonalDebt
    (f : ZetaAdmissibleFunction) (C : ℝ) : Prop :=
  ∀ s : Finset ZetaPrimePowerIndex,
    zetaCompletedPrimeSpectralAmplitudeIndex_normSq_finiteProjectionEnergy_diagonalDebt
      s f ≤ C

/-- A finite-subtrace bound transfers to the finite projection-energy
presentation. -/
theorem zetaCompletedPrimeSpectralAmplitudeIndex_projectionEnergy_le_of_sum_le_diagonalDebt_owner
    (f : ZetaAdmissibleFunction) (C : ℝ)
    (hC :
      ∀ s : Finset ZetaPrimePowerIndex,
        ∑ index in s,
          ‖zetaCompletedPrimeSpectralAmplitudeIndex index f‖ ^ 2 ≤ C) :
    ZetaCompletedPrimeSpectralAmplitudeIndexFiniteProjectionEnergyUpperBound_diagonalDebt
      f C :=
  fun s : Finset ZetaPrimePowerIndex =>
    Eq.subst
      (motive := fun value : ℝ => value ≤ C)
      (zetaCompletedPrimeSpectralAmplitudeIndex_normSq_finiteProjectionEnergy_eq_sum_diagonalDebt
        s f).symm
      (hC s)

/-- A finite projection-energy upper bound bounds its range. -/
theorem zetaCompletedPrimeSpectralAmplitudeIndex_projectionEnergy_range_le_diagonalDebt_owner
    (f : ZetaAdmissibleFunction) (C : ℝ)
    (hC :
      ∀ s : Finset ZetaPrimePowerIndex,
        zetaCompletedPrimeSpectralAmplitudeIndex_normSq_finiteProjectionEnergy_diagonalDebt
          s f ≤ C) :
    ∀ value : ℝ,
      value ∈
        Set.range
          (fun s : Finset ZetaPrimePowerIndex =>
            zetaCompletedPrimeSpectralAmplitudeIndex_normSq_finiteProjectionEnergy_diagonalDebt
              s f) →
      value ≤ C :=
  fun value hvalue =>
    match hvalue with
    | ⟨s, hvalue_eq⟩ =>
        Eq.subst
          (motive := fun projectionValue : ℝ => projectionValue ≤ C)
          hvalue_eq
          (hC s)

/-- A bounded projection-energy range gives finite-subtrace domination in the
sum presentation. -/
theorem zetaCompletedPrimeSpectralAmplitudeIndex_sum_le_of_projectionEnergy_range_bound_diagonalDebt_owner
    (f : ZetaAdmissibleFunction) (C : ℝ)
    (hC :
      ∀ value : ℝ,
        value ∈
          Set.range
            (fun s : Finset ZetaPrimePowerIndex =>
              zetaCompletedPrimeSpectralAmplitudeIndex_normSq_finiteProjectionEnergy_diagonalDebt
                s f) →
        value ≤ C) :
    ∀ s : Finset ZetaPrimePowerIndex,
      ∑ index in s,
        ‖zetaCompletedPrimeSpectralAmplitudeIndex index f‖ ^ 2 ≤ C :=
  fun s : Finset ZetaPrimePowerIndex =>
    let hprojectionBound :
        zetaCompletedPrimeSpectralAmplitudeIndex_normSq_finiteProjectionEnergy_diagonalDebt
            s f ≤ C :=
      hC
        (zetaCompletedPrimeSpectralAmplitudeIndex_normSq_finiteProjectionEnergy_diagonalDebt
          s f)
        ⟨s, Eq.refl
          (zetaCompletedPrimeSpectralAmplitudeIndex_normSq_finiteProjectionEnergy_diagonalDebt
            s f)⟩
    Eq.subst
      (motive := fun value : ℝ => value ≤ C)
      (zetaCompletedPrimeSpectralAmplitudeIndex_normSq_finiteProjectionEnergy_eq_sum_diagonalDebt
        s f)
      hprojectionBound

/-- Source existence of a finite completed prime amplitude projection-energy
upper bound. -/
theorem zetaCompletedPrimeSpectralAmplitudeIndex_normSq_finiteProjectionEnergy_hasUpperBound_diagonalDebt_owner
    (f : ZetaAdmissibleFunction) :
    ∃ C : ℝ,
      ZetaCompletedPrimeSpectralAmplitudeIndexFiniteProjectionEnergyUpperBound_diagonalDebt
        f C :=
  match
    zetaCompletedPrimeSpectralAmplitudeIndex_normSq_finiteSubtrace_bessel_source
      f with
  | ⟨C, hC⟩ =>
      ⟨C,
        zetaCompletedPrimeSpectralAmplitudeIndex_projectionEnergy_le_of_sum_le_diagonalDebt_owner
          f C hC⟩

/-- Finite completed prime amplitude projection energies have one uniform
upper bound. -/
theorem zetaCompletedPrimeSpectralAmplitudeIndex_normSq_finiteProjectionEnergy_upperBound_diagonalDebt_owner
    (f : ZetaAdmissibleFunction) :
    ∃ C : ℝ,
      ∀ s : Finset ZetaPrimePowerIndex,
        zetaCompletedPrimeSpectralAmplitudeIndex_normSq_finiteProjectionEnergy_diagonalDebt
          s f ≤ C :=
  match
    zetaCompletedPrimeSpectralAmplitudeIndex_normSq_finiteProjectionEnergy_hasUpperBound_diagonalDebt_owner
      f with
  | ⟨C, hC⟩ =>
      ⟨C, hC⟩

/-- A uniform finite projection-energy upper bound gives boundedness of the
finite projection-energy range. -/
theorem zetaCompletedPrimeSpectralAmplitudeIndex_normSq_finiteProjectionEnergy_bddAbove_of_upperBound_diagonalDebt_owner
    (f : ZetaAdmissibleFunction)
    (hupper :
      ∃ C : ℝ,
        ∀ s : Finset ZetaPrimePowerIndex,
          zetaCompletedPrimeSpectralAmplitudeIndex_normSq_finiteProjectionEnergy_diagonalDebt
            s f ≤ C) :
    BddAbove
      (Set.range
        (fun s : Finset ZetaPrimePowerIndex =>
          zetaCompletedPrimeSpectralAmplitudeIndex_normSq_finiteProjectionEnergy_diagonalDebt
            s f)) :=
  match hupper with
  | ⟨C, hC⟩ =>
      ⟨C,
        zetaCompletedPrimeSpectralAmplitudeIndex_projectionEnergy_range_le_diagonalDebt_owner
          f C hC⟩

/-- The finite completed prime amplitude projection-energy range is bounded
above. -/
theorem zetaCompletedPrimeSpectralAmplitudeIndex_normSq_finiteProjectionEnergy_bddAbove_diagonalDebt_owner
    (f : ZetaAdmissibleFunction) :
    BddAbove
      (Set.range
        (fun s : Finset ZetaPrimePowerIndex =>
          zetaCompletedPrimeSpectralAmplitudeIndex_normSq_finiteProjectionEnergy_diagonalDebt
            s f)) :=
  zetaCompletedPrimeSpectralAmplitudeIndex_normSq_finiteProjectionEnergy_bddAbove_of_upperBound_diagonalDebt_owner
    f
    (zetaCompletedPrimeSpectralAmplitudeIndex_normSq_finiteProjectionEnergy_upperBound_diagonalDebt_owner
      f)

/-- Boundedness of the finite completed prime amplitude projection-energy
range gives finite-subtrace Bessel domination. -/
theorem zetaCompletedPrimeSpectralAmplitudeIndex_normSq_finiteSubtrace_bessel_of_projectionEnergy_bddAbove_diagonalDebt_owner
    (f : ZetaAdmissibleFunction)
    (hbounded :
      BddAbove
        (Set.range
          (fun s : Finset ZetaPrimePowerIndex =>
            zetaCompletedPrimeSpectralAmplitudeIndex_normSq_finiteProjectionEnergy_diagonalDebt
              s f))) :
    ∃ C : ℝ,
      ∀ s : Finset ZetaPrimePowerIndex,
        ∑ index in s,
          ‖zetaCompletedPrimeSpectralAmplitudeIndex index f‖ ^ 2 ≤ C :=
  match hbounded with
  | ⟨C, hC⟩ =>
      ⟨C,
        zetaCompletedPrimeSpectralAmplitudeIndex_sum_le_of_projectionEnergy_range_bound_diagonalDebt_owner
          f C hC⟩

/-- Hilbert-frame finite-subtrace Bessel source for completed prime spectral
amplitudes. -/
theorem zetaCompletedPrimeSpectralAmplitudeIndex_normSq_finiteSubtrace_bessel_diagonalDebt_owner
    (f : ZetaAdmissibleFunction) :
    ∃ C : ℝ,
      ∀ s : Finset ZetaPrimePowerIndex,
        ∑ index in s,
          ‖zetaCompletedPrimeSpectralAmplitudeIndex index f‖ ^ 2 ≤ C :=
  zetaCompletedPrimeSpectralAmplitudeIndex_normSq_finiteSubtrace_bessel_of_projectionEnergy_bddAbove_diagonalDebt_owner
    f
    (zetaCompletedPrimeSpectralAmplitudeIndex_normSq_finiteProjectionEnergy_bddAbove_diagonalDebt_owner
      f)

/-- Hilbert-amplitude window Bessel source for completed prime sampling. -/
theorem zetaCompletedPrimeSpectralAmplitudeIndex_windowNormSq_bessel_diagonalDebt_owner
    (f : ZetaAdmissibleFunction) :
    ∃ C : ℝ,
      ZetaCompletedPrimeSpectralAmplitudeWindowNormSqUpperBound_diagonalDebt
        f C :=
  match
    zetaCompletedPrimeSpectralAmplitudeIndex_normSq_finiteSubtrace_bessel_diagonalDebt_owner
      f with
  | ⟨C, hC⟩ =>
      ⟨C,
        fun N : ℕ =>
          hC (ZetaPrimePowerIndex.window N)⟩

/-- Weighted-prime window sums equal amplitude norm-square window sums. -/
theorem completedAutocorrelationSpectralTransform_weightedPrimeSampling_windowSum_eq_amplitudeNormSq_windowSum_diagonalDebt_owner
    (N : ℕ) (f : ZetaAdmissibleFunction) :
    (∑ index in ZetaPrimePowerIndex.window N,
      completedAutocorrelationSpectralTransform_weightedPrimeSampling
        index f) =
      ∑ index in ZetaPrimePowerIndex.window N,
        ‖zetaCompletedPrimeSpectralAmplitudeIndex index f‖ ^ 2 :=
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
  Eq.trans hweighted_eq_sample hsample_eq_amplitude

/-- Hilbert-amplitude window Bessel domination gives weighted-prime sampling
window domination. -/
theorem completedAutocorrelationSpectralTransform_weightedPrimeSampling_windowSubtrace_bessel_of_amplitudeWindow_diagonalDebt_owner
    (f : ZetaAdmissibleFunction) (C : ℝ)
    (hC :
      ZetaCompletedPrimeSpectralAmplitudeWindowNormSqUpperBound_diagonalDebt
        f C) :
    CompletedAutocorrelationSpectralTransformWeightedPrimeSamplingWindowSubtraceUpperBound_diagonalDebt
      f C :=
  fun N : ℕ =>
    Eq.subst
      (motive := fun value : ℝ => value ≤ C)
      (completedAutocorrelationSpectralTransform_weightedPrimeSampling_windowSum_eq_amplitudeNormSq_windowSum_diagonalDebt_owner
        N f).symm
      (hC N)

/-- Owner-level weighted-prime sampling window Bessel source. -/
theorem completedAutocorrelationSpectralTransform_weightedPrimeSampling_windowSubtrace_bessel_diagonalDebt_owner
    (f : ZetaAdmissibleFunction) :
    ∃ C : ℝ,
      CompletedAutocorrelationSpectralTransformWeightedPrimeSamplingWindowSubtraceUpperBound_diagonalDebt
        f C :=
  match
    zetaCompletedPrimeSpectralAmplitudeIndex_windowNormSq_bessel_diagonalDebt_owner
      f with
  | ⟨C, hC⟩ =>
      ⟨C,
        completedAutocorrelationSpectralTransform_weightedPrimeSampling_windowSubtrace_bessel_of_amplitudeWindow_diagonalDebt_owner
          f C hC⟩

/-- Genuine-window Bessel domination gives box Bessel domination. -/
theorem completedAutocorrelationSpectralTransform_weightedPrimeSampling_boxSubtrace_bessel_of_windowSubtrace_bessel_diagonalDebt_owner
    (f : ZetaAdmissibleFunction) (C : ℝ)
    (hC :
      CompletedAutocorrelationSpectralTransformWeightedPrimeSamplingWindowSubtraceUpperBound_diagonalDebt
        f C) :
    CompletedAutocorrelationSpectralTransformWeightedPrimeSamplingBoxSubtraceUpperBound_diagonalDebt
      f C :=
  fun N : ℕ =>
    Eq.subst
    (motive := fun value : ℝ => value ≤ C)
    (sum_box_completedAutocorrelationSpectralTransform_weightedPrimeSampling_eq_sum_window
      N f).symm
    (hC N)

/-- Owner-level weighted-prime sampling box Bessel source. -/
theorem completedAutocorrelationSpectralTransform_weightedPrimeSampling_boxSubtrace_bessel_diagonalDebt_owner
    (f : ZetaAdmissibleFunction) :
    ∃ C : ℝ,
      CompletedAutocorrelationSpectralTransformWeightedPrimeSamplingBoxSubtraceUpperBound_diagonalDebt
        f C :=
  match
    completedAutocorrelationSpectralTransform_weightedPrimeSampling_windowSubtrace_bessel_diagonalDebt_owner
      f with
  | ⟨C, hC⟩ =>
      ⟨C,
        completedAutocorrelationSpectralTransform_weightedPrimeSampling_boxSubtrace_bessel_of_windowSubtrace_bessel_diagonalDebt_owner
          f C hC⟩

/-- Inclusion in a rectangular box bounds a finite weighted-prime subtrace by
the box subtrace. -/
theorem completedAutocorrelationSpectralTransform_weightedPrimeSampling_sum_le_box_sum_of_subset_diagonalDebt_owner
    (s : Finset ZetaPrimePowerIndex) (N : ℕ) (f : ZetaAdmissibleFunction)
    (hsubset : s ⊆ ZetaPrimePowerIndex.box N) :
    (∑ index in s,
      completedAutocorrelationSpectralTransform_weightedPrimeSampling
        index f) ≤
      ∑ index in ZetaPrimePowerIndex.box N,
        completedAutocorrelationSpectralTransform_weightedPrimeSampling
          index f :=
  Finset.sum_le_sum_of_subset_of_nonneg
    hsubset
    (fun index boxMembership outsideMembership =>
      completedAutocorrelationSpectralTransform_weightedPrimeSampling_nonnegative
        index f)

/-- Every finite weighted prime-center subtrace is dominated by a rectangular
box subtrace. -/
theorem completedAutocorrelationSpectralTransform_weightedPrimeSampling_finiteSubtrace_le_boxSubtrace_diagonalDebt_owner
    (f : ZetaAdmissibleFunction) :
    ∀ s : Finset ZetaPrimePowerIndex,
      ∃ N : ℕ,
        ∑ index in s,
          completedAutocorrelationSpectralTransform_weightedPrimeSampling
            index f ≤
        ∑ index in ZetaPrimePowerIndex.box N,
          completedAutocorrelationSpectralTransform_weightedPrimeSampling
            index f :=
  fun s : Finset ZetaPrimePowerIndex =>
  let hcontainsEventually :
      ∀ᶠ N in Filter.atTop,
        s ≤ ZetaPrimePowerIndex.box N :=
    ZetaPrimePowerIndex.box_tendsto_atTop.eventually
      (Filter.eventually_ge_atTop s)
  match hcontainsEventually.exists with
  | ⟨N, hN⟩ =>
      let hsubset : s ⊆ ZetaPrimePowerIndex.box N :=
        hN
      ⟨N,
        completedAutocorrelationSpectralTransform_weightedPrimeSampling_sum_le_box_sum_of_subset_diagonalDebt_owner
          s N f hsubset⟩

/-- Box Bessel domination gives finite-subtrace Bessel domination. -/
theorem completedAutocorrelationSpectralTransform_weightedPrimeSampling_finiteSubtrace_bessel_of_boxSubtrace_bessel_diagonalDebt_owner
    (f : ZetaAdmissibleFunction) (C : ℝ)
    (hC :
      CompletedAutocorrelationSpectralTransformWeightedPrimeSamplingBoxSubtraceUpperBound_diagonalDebt
        f C) :
    ∀ s : Finset ZetaPrimePowerIndex,
      ∑ index in s,
        completedAutocorrelationSpectralTransform_weightedPrimeSampling
          index f ≤ C :=
  fun s : Finset ZetaPrimePowerIndex =>
  match
    completedAutocorrelationSpectralTransform_weightedPrimeSampling_finiteSubtrace_le_boxSubtrace_diagonalDebt_owner
      f s with
  | ⟨N, hfinite_le_box⟩ =>
      le_trans hfinite_le_box (hC N)

/-- Owner-level finite-subtrace Bessel bound for completed weighted prime
sampling. -/
theorem completedAutocorrelationSpectralTransform_weightedPrimeSampling_finiteSubtrace_bessel_diagonalDebt_owner
    (f : ZetaAdmissibleFunction) :
    ∃ C : ℝ,
      ∀ s : Finset ZetaPrimePowerIndex,
        ∑ index in s,
          completedAutocorrelationSpectralTransform_weightedPrimeSampling
            index f ≤ C :=
  match
    completedAutocorrelationSpectralTransform_weightedPrimeSampling_boxSubtrace_bessel_diagonalDebt_owner
      f with
  | ⟨C, hC⟩ =>
      ⟨C,
        completedAutocorrelationSpectralTransform_weightedPrimeSampling_finiteSubtrace_bessel_of_boxSubtrace_bessel_diagonalDebt_owner
          f C hC⟩

/-- Completed weighted-prime sampling is summable at the diagonal-debt owner
level. -/
theorem completedAutocorrelationSpectralTransform_weightedPrimeSampling_summable_diagonalDebt_owner
    (f : ZetaAdmissibleFunction) :
    Summable
      (fun index : ZetaPrimePowerIndex =>
        completedAutocorrelationSpectralTransform_weightedPrimeSampling
          index f) :=
  let hnonnegative :
      0 ≤
        fun index : ZetaPrimePowerIndex =>
          completedAutocorrelationSpectralTransform_weightedPrimeSampling
            index f :=
    fun index : ZetaPrimePowerIndex =>
      completedAutocorrelationSpectralTransform_weightedPrimeSampling_nonnegative
        index f
  match
    completedAutocorrelationSpectralTransform_weightedPrimeSampling_finiteSubtrace_bessel_diagonalDebt_owner
      f with
  | ⟨C, hC⟩ =>
      summable_of_sum_le hnonnegative hC

/-- Owner-level weighted-prime sampling `HasSum` source. -/
theorem completedAutocorrelationSpectralTransform_weightedPrimeSampling_hasSum_diagonalDebt_owner
    (f : ZetaAdmissibleFunction) :
    HasSum
      (fun index : ZetaPrimePowerIndex =>
        completedAutocorrelationSpectralTransform_weightedPrimeSampling
          index f)
      (completedAutocorrelationSpectralTransform_weightedPrimeSamplingTraceEnergy_diagonalDebt
        f) :=
  (completedAutocorrelationSpectralTransform_weightedPrimeSampling_summable_diagonalDebt_owner
    f).hasSum

/-- Positive sample squares agree pointwise with completed weighted-prime
sampling. -/
theorem zetaCompletedPrimePositiveWeightedSampleNormSq_eq_weightedPrimeSampling_diagonalDebt
    (index : ZetaPrimePowerIndex) (f : ZetaAdmissibleFunction) :
    zetaCompletedPrimePositiveWeightedSampleNormSq index f =
      completedAutocorrelationSpectralTransform_weightedPrimeSampling
        index f :=
  zetaCompletedPrimePositiveWeightedSampleNormSq_eq_weightedPrimeSampling
    index f

/-- Owner-level summability of the positive completed prime weighted
sample-square stream. -/
theorem zetaCompletedPrimePositiveWeightedSampleNormSq_summable_diagonalDebt_owner
    (f : ZetaAdmissibleFunction) :
    Summable
      (fun index : ZetaPrimePowerIndex =>
        zetaCompletedPrimePositiveWeightedSampleNormSq index f) :=
  (completedAutocorrelationSpectralTransform_weightedPrimeSampling_summable_diagonalDebt_owner
    f).congr
    (fun index : ZetaPrimePowerIndex =>
      (zetaCompletedPrimePositiveWeightedSampleNormSq_eq_weightedPrimeSampling_diagonalDebt
        index f).symm)

end ZetaAdmissibleFunction

end
end LFunctions
end Boundary
