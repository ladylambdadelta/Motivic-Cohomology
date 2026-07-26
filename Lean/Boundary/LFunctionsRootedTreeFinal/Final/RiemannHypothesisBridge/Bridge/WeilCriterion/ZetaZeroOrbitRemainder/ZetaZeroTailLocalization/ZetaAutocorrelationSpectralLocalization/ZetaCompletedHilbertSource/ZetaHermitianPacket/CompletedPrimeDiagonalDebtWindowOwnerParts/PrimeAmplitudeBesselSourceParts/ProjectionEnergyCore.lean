import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaCompletedHilbertSource.ZetaHermitianPacket.CompletedPrimePowerSampling
import Mathlib.Order.Filter.Defs

/-!
# Completed weighted prime sampling projection-energy core

This file owns the acyclic finite, box, and genuine-window projection-energy
definitions for completed weighted prime-center sampling.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open scoped BigOperators

namespace ZetaAdmissibleFunction

/-- The rectangular-box projection energy of completed weighted prime-center
samples. -/
noncomputable def completedWeightedPrimeSamplingBoxProjectionEnergy_hilbertFrame
    (N : ℕ) (f : ZetaAdmissibleFunction) : ℝ :=
  ∑ index in ZetaPrimePowerIndex.box N,
    completedAutocorrelationSpectralTransform_weightedPrimeSampling
      index f

/-- Rectangular-box projection energy unfolds to the corresponding box sum. -/
theorem completedWeightedPrimeSamplingBoxProjectionEnergy_eq_sum_hilbertFrame
    (N : ℕ) (f : ZetaAdmissibleFunction) :
    completedWeightedPrimeSamplingBoxProjectionEnergy_hilbertFrame N f =
      ∑ index in ZetaPrimePowerIndex.box N,
        completedAutocorrelationSpectralTransform_weightedPrimeSampling
          index f :=
  Eq.refl
    (completedWeightedPrimeSamplingBoxProjectionEnergy_hilbertFrame N f)

/-- The genuine-window projection energy of completed weighted prime-center
samples. -/
noncomputable def completedWeightedPrimeSamplingWindowProjectionEnergy_hilbertFrame
    (N : ℕ) (f : ZetaAdmissibleFunction) : ℝ :=
  ∑ index in ZetaPrimePowerIndex.window N,
    completedAutocorrelationSpectralTransform_weightedPrimeSampling
      index f

/-- Genuine-window projection energy unfolds to the corresponding window sum. -/
theorem completedWeightedPrimeSamplingWindowProjectionEnergy_eq_sum_hilbertFrame
    (N : ℕ) (f : ZetaAdmissibleFunction) :
    completedWeightedPrimeSamplingWindowProjectionEnergy_hilbertFrame N f =
      ∑ index in ZetaPrimePowerIndex.window N,
        completedAutocorrelationSpectralTransform_weightedPrimeSampling
          index f :=
  Eq.refl
    (completedWeightedPrimeSamplingWindowProjectionEnergy_hilbertFrame N f)

/-- Genuine-window completed weighted prime-center projection energy is the
positive weighted sample norm-square window. -/
theorem completedWeightedPrimeSamplingWindowProjectionEnergy_eq_positiveSampleNormSqWindow_hilbertFrame
    (N : ℕ) (f : ZetaAdmissibleFunction) :
    completedWeightedPrimeSamplingWindowProjectionEnergy_hilbertFrame N f =
      ∑ index in ZetaPrimePowerIndex.window N,
        zetaCompletedPrimePositiveWeightedSampleNormSq index f :=
  Finset.sum_congr (Eq.refl (ZetaPrimePowerIndex.window N))
    (fun index membership =>
      (zetaCompletedPrimePositiveWeightedSampleNormSq_eq_weightedPrimeSampling
        index f).symm)

/-- Rectangular boxes and genuine windows have the same completed weighted
prime-center projection energy. -/
theorem completedWeightedPrimeSamplingBoxProjectionEnergy_eq_windowProjectionEnergy_hilbertFrame
    (N : ℕ) (f : ZetaAdmissibleFunction) :
    completedWeightedPrimeSamplingBoxProjectionEnergy_hilbertFrame N f =
      completedWeightedPrimeSamplingWindowProjectionEnergy_hilbertFrame
        N f :=
  sum_box_completedAutocorrelationSpectralTransform_weightedPrimeSampling_eq_sum_window
    N f

/-- The finite projection energy of completed weighted prime-center samples. -/
noncomputable def completedWeightedPrimeSamplingProjectionEnergy_hilbertFrame
    (s : Finset ZetaPrimePowerIndex) (f : ZetaAdmissibleFunction) : ℝ :=
  ∑ index in s,
    completedAutocorrelationSpectralTransform_weightedPrimeSampling
      index f

/-- The finite projection energy unfolds to the corresponding finite sum. -/
theorem completedWeightedPrimeSamplingProjectionEnergy_eq_sum_hilbertFrame
    (s : Finset ZetaPrimePowerIndex) (f : ZetaAdmissibleFunction) :
    completedWeightedPrimeSamplingProjectionEnergy_hilbertFrame s f =
      ∑ index in s,
        completedAutocorrelationSpectralTransform_weightedPrimeSampling
          index f :=
  Eq.refl
    (completedWeightedPrimeSamplingProjectionEnergy_hilbertFrame s f)

/-- The finite weighted sampling sum is nonnegative before projection-energy
transport. -/
theorem completedWeightedPrimeSamplingProjectionEnergy_sum_nonnegative_hilbertFrame
    (s : Finset ZetaPrimePowerIndex) (f : ZetaAdmissibleFunction) :
    0 ≤
      ∑ index in s,
        completedAutocorrelationSpectralTransform_weightedPrimeSampling
          index f :=
  Finset.sum_nonneg
    (fun index membership =>
      completedAutocorrelationSpectralTransform_weightedPrimeSampling_nonnegative
        index f)

/-- Finite projection energies are nonnegative. -/
theorem completedWeightedPrimeSamplingProjectionEnergy_nonnegative_hilbertFrame
    (s : Finset ZetaPrimePowerIndex) (f : ZetaAdmissibleFunction) :
    0 ≤ completedWeightedPrimeSamplingProjectionEnergy_hilbertFrame s f :=
  Eq.subst
    (motive := fun value : ℝ => 0 ≤ value)
    (completedWeightedPrimeSamplingProjectionEnergy_eq_sum_hilbertFrame
      s f).symm
    (completedWeightedPrimeSamplingProjectionEnergy_sum_nonnegative_hilbertFrame
      s f)

/-- Inclusion in a rectangular box bounds the finite weighted projection sum by
the box projection sum. -/
theorem completedWeightedPrimeSamplingProjectionEnergy_sum_le_box_sum_hilbertFrame
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

/-- Inclusion in a rectangular box bounds the finite projection energy by the
box projection energy. -/
theorem completedWeightedPrimeSamplingProjectionEnergy_le_boxProjectionEnergy_of_subset_hilbertFrame
    (s : Finset ZetaPrimePowerIndex) (N : ℕ) (f : ZetaAdmissibleFunction)
    (hsubset : s ⊆ ZetaPrimePowerIndex.box N) :
    completedWeightedPrimeSamplingProjectionEnergy_hilbertFrame s f ≤
      completedWeightedPrimeSamplingBoxProjectionEnergy_hilbertFrame N f :=
  let hsum :
      (∑ index in s,
        completedAutocorrelationSpectralTransform_weightedPrimeSampling
          index f) ≤
        ∑ index in ZetaPrimePowerIndex.box N,
          completedAutocorrelationSpectralTransform_weightedPrimeSampling
            index f :=
    completedWeightedPrimeSamplingProjectionEnergy_sum_le_box_sum_hilbertFrame
      s N f hsubset
  let hleft :
      completedWeightedPrimeSamplingProjectionEnergy_hilbertFrame s f ≤
        ∑ index in ZetaPrimePowerIndex.box N,
          completedAutocorrelationSpectralTransform_weightedPrimeSampling
            index f :=
    Eq.subst
      (motive := fun value : ℝ =>
        value ≤
          ∑ index in ZetaPrimePowerIndex.box N,
            completedAutocorrelationSpectralTransform_weightedPrimeSampling
              index f)
      (completedWeightedPrimeSamplingProjectionEnergy_eq_sum_hilbertFrame
        s f).symm
      hsum
  Eq.subst
    (motive := fun value : ℝ =>
      completedWeightedPrimeSamplingProjectionEnergy_hilbertFrame s f ≤ value)
    (completedWeightedPrimeSamplingBoxProjectionEnergy_eq_sum_hilbertFrame
      N f).symm
    hleft

/-- A finite completed weighted prime-center projection is dominated by a
rectangular box projection. -/
theorem completedWeightedPrimeSamplingProjectionEnergy_le_boxProjectionEnergy_hilbertFrame
    (s : Finset ZetaPrimePowerIndex) (f : ZetaAdmissibleFunction) :
    ∃ N : ℕ,
      completedWeightedPrimeSamplingProjectionEnergy_hilbertFrame s f ≤
        completedWeightedPrimeSamplingBoxProjectionEnergy_hilbertFrame N f :=
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
      ⟨N,
        completedWeightedPrimeSamplingProjectionEnergy_le_boxProjectionEnergy_of_subset_hilbertFrame
          s N f hsubset⟩

end ZetaAdmissibleFunction

end
end LFunctions
end Boundary
