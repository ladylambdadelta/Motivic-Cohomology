import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalization.BoundaryEulerAbel.BoundaryGrowth.OwnerParts.SharpPhaseIntegralParts.ContinuousBernoulliFourier.ModewiseUniformBound

/-!
# Absolute summability of the integrated Bernoulli Fourier modes
-/

namespace Boundary
namespace LFunctions

noncomputable section

open MeasureTheory

/-- The global translated logarithmic-phase integral for one Fourier mode. -/
noncomputable def boundaryLineOnePointRealParam_centeredBernoulliModeIntegral
    (t : ℝ)
    (a : ℕ)
    (L : ℝ)
    (m : ℤ) : ℂ :=
  ∫ u in (0 : ℝ)..L,
    boundaryLineOnePointRealParam_unitBlockLogDerivativeAmplitude t a u *
      Complex.realPhaseOscillation
        (boundaryLineOnePointRealParam_unitBlockCombinedPhase t m a) u

/-- The canonical second-Bernoulli coefficient multiplying one global mode
integral. -/
noncomputable def boundaryLineOnePointRealParam_centeredBernoulliWeightedModeIntegral
    (t : ℝ)
    (a : ℕ)
    (L : ℝ)
    (m : ℤ) : ℂ :=
  ((1 : ℂ) / (m : ℂ) ^ (2 : ℕ)) *
    boundaryLineOnePointRealParam_centeredBernoulliModeIntegral t a L m

/-- The weighted zero mode vanishes because its canonical Bernoulli Fourier
coefficient is zero. -/
theorem boundaryLineOnePointRealParam_centeredBernoulliWeightedModeIntegral_zero
    (t : ℝ)
    (a : ℕ)
    (L : ℝ) :
    boundaryLineOnePointRealParam_centeredBernoulliWeightedModeIntegral
      t a L 0 = 0 := by
  have hcast : ((0 : ℤ) : ℂ) = 0 :=
    Int.cast_zero
  have hpower : ((0 : ℂ) ^ (2 : ℕ)) = 0 :=
    zero_pow (show (2 : ℕ) ≠ 0 from OfNat.ofNat_ne_zero 2)
  have hcoefficient : (1 : ℂ) / ((0 : ℤ) : ℂ) ^ (2 : ℕ) = 0 :=
    Eq.trans
      (congrArg (fun z : ℂ => (1 : ℂ) / z ^ (2 : ℕ)) hcast)
      (Eq.trans
        (congrArg (fun z : ℂ => (1 : ℂ) / z) hpower)
        (div_zero 1))
  unfold boundaryLineOnePointRealParam_centeredBernoulliWeightedModeIntegral
  exact Eq.trans
    (congrArg
      (fun z : ℂ =>
        z * boundaryLineOnePointRealParam_centeredBernoulliModeIntegral t a L 0)
      hcoefficient)
    (zero_mul _)

/-- Every weighted mode integral is bounded by four times the norm of its
second-Bernoulli Fourier coefficient. -/
theorem norm_boundaryLineOnePointRealParam_centeredBernoulliWeightedModeIntegral_le
    (t : ℝ)
    {a : ℕ}
    (ha : ⌊2 + ‖t‖⌋₊ ≤ a)
    {L : ℝ}
    (hL : 0 ≤ L)
    (m : ℤ) :
    ‖boundaryLineOnePointRealParam_centeredBernoulliWeightedModeIntegral
        t a L m‖ ≤
      4 * ‖(1 : ℂ) / (m : ℂ) ^ (2 : ℕ)‖ := by
  by_cases hm : m = 0
  · have hterm :
        boundaryLineOnePointRealParam_centeredBernoulliWeightedModeIntegral
          t a L m = 0 :=
      Eq.subst
        (motive := fun k : ℤ =>
          boundaryLineOnePointRealParam_centeredBernoulliWeightedModeIntegral
            t a L k = 0)
        hm.symm
        (boundaryLineOnePointRealParam_centeredBernoulliWeightedModeIntegral_zero
          t a L)
    have hleft :
        ‖boundaryLineOnePointRealParam_centeredBernoulliWeightedModeIntegral
            t a L m‖ = 0 :=
      Eq.trans (congrArg Norm.norm hterm) norm_zero
    have hrightNonnegative :
        0 ≤ 4 * ‖(1 : ℂ) / (m : ℂ) ^ (2 : ℕ)‖ :=
      mul_nonneg (show (0 : ℝ) ≤ 4 from zero_le_four) (norm_nonneg _)
    exact Eq.subst
      (motive := fun value : ℝ =>
        value ≤ 4 * ‖(1 : ℂ) / (m : ℂ) ^ (2 : ℕ)‖)
      hleft.symm
      hrightNonnegative
  · have hmode :
        ‖boundaryLineOnePointRealParam_centeredBernoulliModeIntegral
            t a L m‖ ≤ 4 := by
      unfold boundaryLineOnePointRealParam_centeredBernoulliModeIntegral
      exact
        norm_intervalIntegral_boundaryLineOnePointRealParam_unitBlockMode_le_four
          t hm ha hL
    have hcoefficientNonnegative :
        0 ≤ ‖(1 : ℂ) / (m : ℂ) ^ (2 : ℕ)‖ :=
      norm_nonneg _
    have hproduct :
        ‖(1 : ℂ) / (m : ℂ) ^ (2 : ℕ)‖ *
            ‖boundaryLineOnePointRealParam_centeredBernoulliModeIntegral
              t a L m‖ ≤
          ‖(1 : ℂ) / (m : ℂ) ^ (2 : ℕ)‖ * 4 :=
      mul_le_mul_of_nonneg_left hmode hcoefficientNonnegative
    have hcommute :
        ‖(1 : ℂ) / (m : ℂ) ^ (2 : ℕ)‖ * 4 =
          4 * ‖(1 : ℂ) / (m : ℂ) ^ (2 : ℕ)‖ :=
      mul_comm _ _
    unfold boundaryLineOnePointRealParam_centeredBernoulliWeightedModeIntegral
    exact le_trans
      (le_of_eq
        (norm_mul
          ((1 : ℂ) / (m : ℂ) ^ (2 : ℕ))
          (boundaryLineOnePointRealParam_centeredBernoulliModeIntegral t a L m)))
      (le_trans hproduct (le_of_eq hcommute))

/-- The coefficient-weighted global Fourier-mode integrals form an absolutely
summable complex series. -/
theorem summable_boundaryLineOnePointRealParam_centeredBernoulliWeightedModeIntegral
    (t : ℝ)
    {a : ℕ}
    (ha : ⌊2 + ‖t‖⌋₊ ≤ a)
    {L : ℝ}
    (hL : 0 ≤ L) :
    Summable
      (boundaryLineOnePointRealParam_centeredBernoulliWeightedModeIntegral
        t a L) := by
  have hmajorant :
      Summable
        (fun m : ℤ => 4 * ‖(1 : ℂ) / (m : ℂ) ^ (2 : ℕ)‖) :=
    Summable.mul_left 4
      summable_centeredQuadraticPrimitive_fourier_coefficient_norm
  exact Summable.of_norm_bounded
    (fun m : ℤ => 4 * ‖(1 : ℂ) / (m : ℂ) ^ (2 : ℕ)‖)
    hmajorant
    (norm_boundaryLineOnePointRealParam_centeredBernoulliWeightedModeIntegral_le
      t ha hL)

end
end LFunctions
end Boundary
