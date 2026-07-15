import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalization.BoundaryEulerAbel.BoundaryGrowth.OwnerParts.SharpPhaseIntegralParts.ContinuousBernoulliFourier.PeriodicCenteredPrimitive

/-!
# Weighted Fourier-series and interval-integral interchange
-/

namespace Boundary
namespace LFunctions

noncomputable section

open MeasureTheory

/-- One coefficient-weighted logarithmic-phase Fourier integrand. -/
noncomputable def boundaryLineOnePointRealParam_centeredBernoulliWeightedModeIntegrand
    (t : ℝ)
    (a : ℕ)
    (m : ℤ)
    (u : ℝ) : ℂ :=
  ((1 : ℂ) / (m : ℂ) ^ (2 : ℕ)) *
    (boundaryLineOnePointRealParam_unitBlockLogDerivativeAmplitude t a u *
      Complex.realPhaseOscillation
        (boundaryLineOnePointRealParam_unitBlockCombinedPhase t m a) u)

/-- Each weighted mode integrand is interval-integrable on a finite translated
post-cutoff interval. -/
theorem intervalIntegrable_boundaryLineOnePointRealParam_centeredBernoulliWeightedModeIntegrand
    (t : ℝ)
    (m : ℤ)
    {a : ℕ}
    (ha : ⌊2 + ‖t‖⌋₊ ≤ a)
    {L : ℝ}
    (hL : 0 ≤ L) :
    IntervalIntegrable
      (boundaryLineOnePointRealParam_centeredBernoulliWeightedModeIntegrand
        t a m)
      volume 0 L := by
  have hcontinuous :
      ContinuousOn
        (boundaryLineOnePointRealParam_centeredBernoulliWeightedModeIntegrand
          t a m)
        (Set.uIcc (0 : ℝ) L) := by
    intro u hu
    have huIcc : u ∈ Set.Icc (0 : ℝ) L :=
      Eq.subst (motive := fun s : Set ℝ => u ∈ s) (Set.uIcc_of_le hL) hu
    have hx : 0 < (a : ℝ) + u :=
      boundaryLineOnePointRealParam_unitBlock_coordinate_pos t ha huIcc.1
    have hamplitude :=
      (hasDerivAt_boundaryLineOnePointRealParam_unitBlockLogDerivativeAmplitude
        t a hx).continuousAt
    have hoscillation :=
      (hasDerivAt_boundaryLineOnePointRealParam_unitBlockModeOscillation
        t m ha huIcc.1).continuousAt
    unfold boundaryLineOnePointRealParam_centeredBernoulliWeightedModeIntegrand
    exact (continuousAt_const.mul (hamplitude.mul hoscillation)).continuousWithinAt
  exact hcontinuous.intervalIntegrable

/-- The weighted mode integrand is bounded by the norm of its Fourier
coefficient throughout the post-cutoff interval. -/
theorem norm_boundaryLineOnePointRealParam_centeredBernoulliWeightedModeIntegrand_le
    (t : ℝ)
    (m : ℤ)
    {a : ℕ}
    (ha : ⌊2 + ‖t‖⌋₊ ≤ a)
    {u : ℝ}
    (hu : 0 ≤ u) :
    ‖boundaryLineOnePointRealParam_centeredBernoulliWeightedModeIntegrand
        t a m u‖ ≤
      ‖(1 : ℂ) / (m : ℂ) ^ (2 : ℕ)‖ := by
  have hamplitude :=
    norm_boundaryLineOnePointRealParam_unitBlockLogDerivativeAmplitude_le_one
      t ha hu
  have hoscillation :
      ‖Complex.realPhaseOscillation
          (boundaryLineOnePointRealParam_unitBlockCombinedPhase t m a) u‖ = 1 :=
    Complex.norm_realPhaseOscillation _ _
  have hinner :
      ‖boundaryLineOnePointRealParam_unitBlockLogDerivativeAmplitude t a u *
          Complex.realPhaseOscillation
            (boundaryLineOnePointRealParam_unitBlockCombinedPhase t m a) u‖ ≤ 1 := by
    have hamplitudeMulOne :
        ‖boundaryLineOnePointRealParam_unitBlockLogDerivativeAmplitude t a u‖ *
            1 ≤ 1 :=
      Eq.subst
        (motive := fun value : ℝ => value ≤ 1)
        (mul_one
          ‖boundaryLineOnePointRealParam_unitBlockLogDerivativeAmplitude
            t a u‖).symm
        hamplitude
    exact le_trans
      (le_of_eq
        (norm_mul
          (boundaryLineOnePointRealParam_unitBlockLogDerivativeAmplitude t a u)
          (Complex.realPhaseOscillation
            (boundaryLineOnePointRealParam_unitBlockCombinedPhase t m a) u)))
      (Eq.subst
        (motive := fun value : ℝ =>
          ‖boundaryLineOnePointRealParam_unitBlockLogDerivativeAmplitude t a u‖ *
            value ≤ 1)
        hoscillation.symm
        hamplitudeMulOne)
  have hcoefficientNonnegative :
      0 ≤ ‖(1 : ℂ) / (m : ℂ) ^ (2 : ℕ)‖ :=
    norm_nonneg _
  unfold boundaryLineOnePointRealParam_centeredBernoulliWeightedModeIntegrand
  exact le_trans
    (le_of_eq
      (norm_mul
        ((1 : ℂ) / (m : ℂ) ^ (2 : ℕ))
        (boundaryLineOnePointRealParam_unitBlockLogDerivativeAmplitude t a u *
          Complex.realPhaseOscillation
            (boundaryLineOnePointRealParam_unitBlockCombinedPhase t m a) u)))
    (le_trans
      (mul_le_mul_of_nonneg_left hinner hcoefficientNonnegative)
      (le_of_eq (mul_one _)))

/-- The weighted Fourier series commutes with integration on every finite
translated post-cutoff interval. -/
theorem hasSum_intervalIntegral_boundaryLineOnePointRealParam_centeredBernoulliWeightedModeIntegrand
    (t : ℝ)
    {a : ℕ}
    (ha : ⌊2 + ‖t‖⌋₊ ≤ a)
    {L : ℝ}
    (hL : 0 ≤ L) :
    HasSum
      (fun m : ℤ =>
        ∫ u in (0 : ℝ)..L,
          boundaryLineOnePointRealParam_centeredBernoulliWeightedModeIntegrand
            t a m u)
      (∫ u in (0 : ℝ)..L,
        ∑' m : ℤ,
          boundaryLineOnePointRealParam_centeredBernoulliWeightedModeIntegrand
            t a m u) := by
  let coefficientNorm : ℤ → ℝ :=
    fun m => ‖(1 : ℂ) / (m : ℂ) ^ (2 : ℕ)‖
  have hcoefficientSummable : Summable coefficientNorm :=
    summable_centeredQuadraticPrimitive_fourier_coefficient_norm
  exact intervalIntegral.hasSum_integral_of_dominated_convergence
    (fun m : ℤ => fun _u : ℝ => coefficientNorm m)
    (fun m =>
      (intervalIntegrable_iff.mp
        (intervalIntegrable_boundaryLineOnePointRealParam_centeredBernoulliWeightedModeIntegrand
          t m ha hL)).aestronglyMeasurable)
    (fun m =>
      ae_of_all volume (fun u hu => by
        have huIoc : u ∈ Set.Ioc (0 : ℝ) L :=
          Eq.subst
            (motive := fun interval : Set ℝ => u ∈ interval)
            (Set.uIoc_of_le hL)
            hu
        exact
          norm_boundaryLineOnePointRealParam_centeredBernoulliWeightedModeIntegrand_le
            t m ha huIoc.1.le))
    (ae_of_all volume (fun _u _hu => hcoefficientSummable))
    intervalIntegrable_const
    (ae_of_all volume (fun u hu => by
      have huIoc : u ∈ Set.Ioc (0 : ℝ) L :=
        Eq.subst
          (motive := fun interval : Set ℝ => u ∈ interval)
          (Set.uIoc_of_le hL)
          hu
      exact
        (Summable.of_norm_bounded coefficientNorm hcoefficientSummable
          (fun m : ℤ =>
            norm_boundaryLineOnePointRealParam_centeredBernoulliWeightedModeIntegrand_le
              t m ha huIoc.1.le)).hasSum))

/-- Integrating a weighted mode integrand gives the previously defined
coefficient-weighted mode integral. -/
theorem intervalIntegral_boundaryLineOnePointRealParam_centeredBernoulliWeightedModeIntegrand_eq
    (t : ℝ)
    (a : ℕ)
    (L : ℝ)
    (m : ℤ) :
    (∫ u in (0 : ℝ)..L,
        boundaryLineOnePointRealParam_centeredBernoulliWeightedModeIntegrand
          t a m u) =
      boundaryLineOnePointRealParam_centeredBernoulliWeightedModeIntegral
        t a L m := by
  unfold boundaryLineOnePointRealParam_centeredBernoulliWeightedModeIntegrand
  unfold boundaryLineOnePointRealParam_centeredBernoulliWeightedModeIntegral
  exact intervalIntegral.integral_const_mul
    ((1 : ℂ) / (m : ℂ) ^ (2 : ℕ))
    (fun u : ℝ =>
      boundaryLineOnePointRealParam_unitBlockLogDerivativeAmplitude t a u *
        Complex.realPhaseOscillation
          (boundaryLineOnePointRealParam_unitBlockCombinedPhase t m a) u)

end
end LFunctions
end Boundary
