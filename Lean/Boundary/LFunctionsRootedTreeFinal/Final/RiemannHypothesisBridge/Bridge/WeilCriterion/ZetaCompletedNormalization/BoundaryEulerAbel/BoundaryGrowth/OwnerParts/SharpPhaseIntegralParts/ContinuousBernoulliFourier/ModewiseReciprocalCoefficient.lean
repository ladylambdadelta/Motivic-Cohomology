import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalization.BoundaryEulerAbel.BoundaryGrowth.OwnerParts.SharpPhaseIntegralParts.ContinuousBernoulliFourier.UnitBlockAmplitude

/-!
# Reciprocal phase coefficient for a Fourier mode

This file specializes the generic nonstationary reciprocal coefficient to the
combined logarithmic/Fourier phase and discharges nonvanishing from the
post-cutoff separation theorem.
-/

namespace Boundary
namespace LFunctions

noncomputable section

/-- Exact derivative of the reciprocal phase coefficient for a combined mode. -/
noncomputable def boundaryLineOnePointRealParam_unitBlockModeCoefficientDerivative
    (t : ℝ)
    (m : ℤ)
    (a : ℕ)
    (u : ℝ) : ℂ :=
  -(Complex.I *
      (boundaryLineOnePointRealParam_unitBlockCombinedPhaseSecondDerivative
        t a u : ℂ)) /
    (Complex.realPhaseDerivativeDenominator
      (boundaryLineOnePointRealParam_unitBlockCombinedPhaseDerivative t m a)
      u) ^ (2 : ℕ)

/-- Uniform phase separation makes the complex derivative denominator
nonzero. -/
theorem boundaryLineOnePointRealParam_unitBlockMode_derivativeDenominator_ne_zero
    (t : ℝ)
    {m : ℤ}
    (hm : m ≠ 0)
    {a : ℕ}
    (ha : ⌊2 + ‖t‖⌋₊ ≤ a)
    {u : ℝ}
    (hu : 0 ≤ u) :
    Complex.realPhaseDerivativeDenominator
        (boundaryLineOnePointRealParam_unitBlockCombinedPhaseDerivative t m a)
        u ≠ 0 := by
  let derivative : ℝ :=
    boundaryLineOnePointRealParam_unitBlockCombinedPhaseDerivative t m a u
  have hgap : (1 : ℝ) ≤ |derivative| :=
    boundaryLineOnePointRealParam_unitBlockCombinedPhaseDerivative_abs_ge_one
      t hm ha hu
  have hderivative_pos : 0 < |derivative| :=
    lt_of_lt_of_le zero_lt_one hgap
  have hderivative_ne : derivative ≠ 0 :=
    (abs_pos.mp hderivative_pos)
  have hcast_ne : (derivative : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr hderivative_ne
  exact mul_ne_zero Complex.I_ne_zero hcast_ne

/-- The generic reciprocal-coefficient derivative specializes directly to the
combined mode. -/
theorem hasDerivAt_boundaryLineOnePointRealParam_unitBlockModeCoefficient
    (t : ℝ)
    {m : ℤ}
    (hm : m ≠ 0)
    {a : ℕ}
    (ha : ⌊2 + ‖t‖⌋₊ ≤ a)
    {u : ℝ}
    (hu : 0 ≤ u) :
    HasDerivAt
      (Complex.realPhaseIntegrationCoefficient
        (boundaryLineOnePointRealParam_unitBlockCombinedPhaseDerivative t m a))
      (boundaryLineOnePointRealParam_unitBlockModeCoefficientDerivative
        t m a u)
      u := by
  have hx : 0 < (a : ℝ) + u :=
    boundaryLineOnePointRealParam_unitBlock_coordinate_pos t ha hu
  have hphaseDerivative :=
    hasDerivAt_boundaryLineOnePointRealParam_unitBlockCombinedPhaseDerivative
      t m a hx
  have hdenominator :=
    boundaryLineOnePointRealParam_unitBlockMode_derivativeDenominator_ne_zero
      t hm ha hu
  exact Complex.hasDerivAt_realPhaseIntegrationCoefficient
    hphaseDerivative hdenominator

/-- Uniform separation bounds the reciprocal phase coefficient by one. -/
theorem norm_boundaryLineOnePointRealParam_unitBlockModeCoefficient_le_one
    (t : ℝ)
    {m : ℤ}
    (hm : m ≠ 0)
    {a : ℕ}
    (ha : ⌊2 + ‖t‖⌋₊ ≤ a)
    {u : ℝ}
    (hu : 0 ≤ u) :
    ‖Complex.realPhaseIntegrationCoefficient
        (boundaryLineOnePointRealParam_unitBlockCombinedPhaseDerivative t m a)
        u‖ ≤ 1 := by
  let derivative : ℝ :=
    boundaryLineOnePointRealParam_unitBlockCombinedPhaseDerivative t m a u
  have hgapAbs : (1 : ℝ) ≤ |derivative| :=
    boundaryLineOnePointRealParam_unitBlockCombinedPhaseDerivative_abs_ge_one
      t hm ha hu
  have hgapNorm : (1 : ℝ) ≤ ‖derivative‖ :=
    Eq.subst
      (motive := fun value : ℝ => 1 ≤ value)
      (Real.norm_eq_abs derivative).symm
      hgapAbs
  have hinverse : (‖derivative‖)⁻¹ ≤ 1 :=
    inv_le_one_of_one_le₀ hgapNorm
  exact Eq.subst
    (motive := fun value : ℝ => value ≤ 1)
    (Complex.norm_realPhaseIntegrationCoefficient
      (boundaryLineOnePointRealParam_unitBlockCombinedPhaseDerivative t m a)
      u).symm
    hinverse

/-- The mode coefficient derivative retains the translated inverse-square
decay after the uniformly separated phase denominator is removed. -/
theorem norm_boundaryLineOnePointRealParam_unitBlockModeCoefficientDerivative_le_inverseSquare
    (t : ℝ)
    {m : ℤ}
    (hm : m ≠ 0)
    {a : ℕ}
    (ha : ⌊2 + ‖t‖⌋₊ ≤ a)
    {u : ℝ}
    (hu : 0 ≤ u) :
    ‖boundaryLineOnePointRealParam_unitBlockModeCoefficientDerivative
        t m a u‖ ≤
      ‖t‖ / (((a : ℝ) + u) ^ (2 : ℕ)) := by
  let derivative : ℝ :=
    boundaryLineOnePointRealParam_unitBlockCombinedPhaseDerivative t m a u
  let velocity : ℝ :=
    boundaryLineOnePointRealParam_unitBlockCombinedPhaseSecondDerivative t a u
  let denominator : ℂ :=
    Complex.realPhaseDerivativeDenominator
      (boundaryLineOnePointRealParam_unitBlockCombinedPhaseDerivative t m a)
      u
  have hgapAbs : (1 : ℝ) ≤ |derivative| :=
    boundaryLineOnePointRealParam_unitBlockCombinedPhaseDerivative_abs_ge_one
      t hm ha hu
  have hgapNorm : (1 : ℝ) ≤ ‖derivative‖ :=
    Eq.subst
      (motive := fun value : ℝ => 1 ≤ value)
      (Real.norm_eq_abs derivative).symm
      hgapAbs
  have hdenominatorNorm : ‖denominator‖ = ‖derivative‖ :=
    Complex.norm_realPhaseDerivativeDenominator
      (boundaryLineOnePointRealParam_unitBlockCombinedPhaseDerivative t m a)
      u
  have hdenominatorOne : (1 : ℝ) ≤ ‖denominator‖ :=
    Eq.subst
      (motive := fun value : ℝ => 1 ≤ value)
      hdenominatorNorm.symm
      hgapNorm
  have hdenominatorSquare : (1 : ℝ) ≤ ‖denominator‖ ^ (2 : ℕ) :=
    one_le_pow₀ hdenominatorOne
  have hremoveDenominator :
      |velocity| / ‖denominator‖ ^ (2 : ℕ) ≤ |velocity| :=
    div_le_self (abs_nonneg velocity) hdenominatorSquare
  have hnormExact :
      ‖boundaryLineOnePointRealParam_unitBlockModeCoefficientDerivative
          t m a u‖ =
        |velocity| / ‖denominator‖ ^ (2 : ℕ) :=
    Complex.norm_neg_I_mul_real_div_sq velocity denominator
  have hx : 0 < (a : ℝ) + u :=
    boundaryLineOnePointRealParam_unitBlock_coordinate_pos t ha hu
  have hvelocityExact :
      |velocity| = ‖t‖ / (((a : ℝ) + u) ^ (2 : ℕ)) :=
    Eq.trans
      (norm_boundaryLineOnePointRealParam_unitBlockLogDerivativeAmplitudeDerivative
        t a u).symm
      (norm_boundaryLineOnePointRealParam_unitBlockLogDerivativeAmplitudeDerivative_eq_inverseSquare
        t a hx)
  exact le_trans
    (le_of_eq hnormExact)
    (le_trans hremoveDenominator (le_of_eq hvelocityExact))

/-- The reciprocal phase-coefficient derivative is controlled by the same
inverse-square majorant as the logarithmic amplitude derivative. -/
theorem norm_boundaryLineOnePointRealParam_unitBlockModeCoefficientDerivative_le
    (t : ℝ)
    {m : ℤ}
    (hm : m ≠ 0)
    {a : ℕ}
    (ha : ⌊2 + ‖t‖⌋₊ ≤ a)
    {u : ℝ}
    (hu : 0 ≤ u) :
    ‖boundaryLineOnePointRealParam_unitBlockModeCoefficientDerivative
        t m a u‖ ≤
      ‖t‖ / ((a : ℝ) ^ (2 : ℕ)) := by
  let derivative : ℝ :=
    boundaryLineOnePointRealParam_unitBlockCombinedPhaseDerivative t m a u
  let velocity : ℝ :=
    boundaryLineOnePointRealParam_unitBlockCombinedPhaseSecondDerivative t a u
  let denominator : ℂ :=
    Complex.realPhaseDerivativeDenominator
      (boundaryLineOnePointRealParam_unitBlockCombinedPhaseDerivative t m a)
      u
  have hgapAbs : (1 : ℝ) ≤ |derivative| :=
    boundaryLineOnePointRealParam_unitBlockCombinedPhaseDerivative_abs_ge_one
      t hm ha hu
  have hgapNorm : (1 : ℝ) ≤ ‖derivative‖ :=
    Eq.subst
      (motive := fun value : ℝ => 1 ≤ value)
      (Real.norm_eq_abs derivative).symm
      hgapAbs
  have hdenominatorNorm : ‖denominator‖ = ‖derivative‖ :=
    Complex.norm_realPhaseDerivativeDenominator
      (boundaryLineOnePointRealParam_unitBlockCombinedPhaseDerivative t m a)
      u
  have hdenominatorOne : (1 : ℝ) ≤ ‖denominator‖ :=
    Eq.subst
      (motive := fun value : ℝ => 1 ≤ value)
      hdenominatorNorm.symm
      hgapNorm
  have hdenominatorSquare : (1 : ℝ) ≤ ‖denominator‖ ^ (2 : ℕ) :=
    one_le_pow₀ hdenominatorOne
  have hremoveDenominator :
      |velocity| / ‖denominator‖ ^ (2 : ℕ) ≤ |velocity| :=
    div_le_self (abs_nonneg velocity) hdenominatorSquare
  have hnormExact :
      ‖boundaryLineOnePointRealParam_unitBlockModeCoefficientDerivative
          t m a u‖ =
        |velocity| / ‖denominator‖ ^ (2 : ℕ) :=
    Complex.norm_neg_I_mul_real_div_sq velocity denominator
  have hvelocityBound :
      |velocity| ≤ ‖t‖ / ((a : ℝ) ^ (2 : ℕ)) := by
    have hamplitudeBound :=
      norm_boundaryLineOnePointRealParam_unitBlockLogDerivativeAmplitudeDerivative_le
        t ha hu
    have hamplitudeNorm :=
      norm_boundaryLineOnePointRealParam_unitBlockLogDerivativeAmplitudeDerivative
        t a u
    exact Eq.subst
      (motive := fun value : ℝ =>
        value ≤ ‖t‖ / ((a : ℝ) ^ (2 : ℕ)))
      hamplitudeNorm
      hamplitudeBound
  exact le_trans
    (le_of_eq hnormExact)
    (le_trans hremoveDenominator hvelocityBound)

end
end LFunctions
end Boundary
