import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalization.BoundaryEulerAbel.BoundaryGrowth.OwnerParts.SharpPhaseIntegralParts.ContinuousBernoulliFourier.WeightedSeriesIdentification

/-!
# Normalized periodic centered-Bernoulli integral
-/

namespace Boundary
namespace LFunctions

noncomputable section

open MeasureTheory

/-- The periodic centered-primitive integrand is the inverse-normalized
canonical Fourier-series integrand. -/
theorem boundaryLineOnePointRealParam_periodicCenteredQuadraticPrimitive_integrand_eq
    (t : ℝ)
    (a : ℕ)
    (u : ℝ) :
    (boundaryLineOnePointRealParam_unitBlockLogDerivativeAmplitude t a u *
      Complex.realPhaseOscillation
        (boundaryLineOnePointRealParam_unitBlockCombinedPhase t 0 a) u) *
      periodicCenteredQuadraticPrimitive u =
    (centeredQuadraticPrimitiveFourierNormalization)⁻¹ *
      ((boundaryLineOnePointRealParam_unitBlockLogDerivativeAmplitude t a u *
        Complex.realPhaseOscillation
          (boundaryLineOnePointRealParam_unitBlockCombinedPhase t 0 a) u) *
        ∑' m : ℤ, centeredQuadraticPrimitiveFourierMode m u) := by
  let common : ℂ :=
    boundaryLineOnePointRealParam_unitBlockLogDerivativeAmplitude t a u *
      Complex.realPhaseOscillation
        (boundaryLineOnePointRealParam_unitBlockCombinedPhase t 0 a) u
  let inverseNormalization : ℂ :=
    (centeredQuadraticPrimitiveFourierNormalization)⁻¹
  let series : ℂ :=
    ∑' m : ℤ, centeredQuadraticPrimitiveFourierMode m u
  unfold periodicCenteredQuadraticPrimitive
  calc
    common * (inverseNormalization * series) =
        (common * inverseNormalization) * series :=
      (mul_assoc common inverseNormalization series).symm
    _ = (inverseNormalization * common) * series := by
      exact congrArg (fun z : ℂ => z * series)
        (mul_comm common inverseNormalization)
    _ = inverseNormalization * (common * series) :=
      mul_assoc inverseNormalization common series

/-- The periodic centered-primitive integral is exactly the inverse-normalized
`tsum` of the coefficient-weighted global mode integrals. -/
theorem intervalIntegral_boundaryLineOnePointRealParam_periodicCenteredQuadraticPrimitive_eq
    (t : ℝ)
    {a : ℕ}
    (ha : ⌊2 + ‖t‖⌋₊ ≤ a)
    {L : ℝ}
    (hL : 0 ≤ L) :
    (∫ u in (0 : ℝ)..L,
        (boundaryLineOnePointRealParam_unitBlockLogDerivativeAmplitude t a u *
          Complex.realPhaseOscillation
            (boundaryLineOnePointRealParam_unitBlockCombinedPhase t 0 a) u) *
          periodicCenteredQuadraticPrimitive u) =
      (centeredQuadraticPrimitiveFourierNormalization)⁻¹ *
        ∑' m : ℤ,
          boundaryLineOnePointRealParam_centeredBernoulliWeightedModeIntegral
            t a L m := by
  let common : ℝ → ℂ :=
    fun u =>
      boundaryLineOnePointRealParam_unitBlockLogDerivativeAmplitude t a u *
        Complex.realPhaseOscillation
          (boundaryLineOnePointRealParam_unitBlockCombinedPhase t 0 a) u
  let series : ℝ → ℂ :=
    fun u => ∑' m : ℤ, centeredQuadraticPrimitiveFourierMode m u
  let inverseNormalization : ℂ :=
    (centeredQuadraticPrimitiveFourierNormalization)⁻¹
  have hintegrand :
      Set.EqOn
        (fun u : ℝ => common u * periodicCenteredQuadraticPrimitive u)
        (fun u : ℝ => inverseNormalization * (common u * series u))
        (Set.uIcc (0 : ℝ) L) := by
    intro u _hu
    exact
      boundaryLineOnePointRealParam_periodicCenteredQuadraticPrimitive_integrand_eq
        t a u
  have hintegralCongruence :
      (∫ u in (0 : ℝ)..L,
          common u * periodicCenteredQuadraticPrimitive u) =
        ∫ u in (0 : ℝ)..L,
          inverseNormalization * (common u * series u) :=
    intervalIntegral.integral_congr hintegrand
  have hconstant :
      (∫ u in (0 : ℝ)..L,
          inverseNormalization * (common u * series u)) =
        inverseNormalization *
          ∫ u in (0 : ℝ)..L, common u * series u :=
    intervalIntegral.integral_const_mul inverseNormalization
      (fun u : ℝ => common u * series u)
  have hseriesIntegral :
      (∑' m : ℤ,
          boundaryLineOnePointRealParam_centeredBernoulliWeightedModeIntegral
            t a L m) =
        ∫ u in (0 : ℝ)..L, common u * series u :=
    (hasSum_boundaryLineOnePointRealParam_centeredBernoulliWeightedModeIntegral_eq_integral
      t ha hL).tsum_eq
  exact Eq.trans hintegralCongruence
    (Eq.trans hconstant
      (congrArg (fun z : ℂ => inverseNormalization * z)
        hseriesIntegral.symm))

/-- Direct norm bound for the periodic centered-primitive integral before
scalar normalization is simplified. -/
theorem norm_intervalIntegral_boundaryLineOnePointRealParam_periodicCenteredQuadraticPrimitive_le_raw
    (t : ℝ)
    {a : ℕ}
    (ha : ⌊2 + ‖t‖⌋₊ ≤ a)
    {L : ℝ}
    (hL : 0 ≤ L) :
    ‖∫ u in (0 : ℝ)..L,
        (boundaryLineOnePointRealParam_unitBlockLogDerivativeAmplitude t a u *
          Complex.realPhaseOscillation
            (boundaryLineOnePointRealParam_unitBlockCombinedPhase t 0 a) u) *
          periodicCenteredQuadraticPrimitive u‖ ≤
      ‖(centeredQuadraticPrimitiveFourierNormalization)⁻¹‖ *
        (4 * (Real.pi ^ (2 : ℕ) / 6 + Real.pi ^ (2 : ℕ) / 6)) := by
  have hidentity :=
    intervalIntegral_boundaryLineOnePointRealParam_periodicCenteredQuadraticPrimitive_eq
      t ha hL
  have hseriesBound :=
    norm_tsum_boundaryLineOnePointRealParam_centeredBernoulliWeightedModeIntegral_le
      t ha hL
  have hinverseNonnegative :
      0 ≤ ‖(centeredQuadraticPrimitiveFourierNormalization)⁻¹‖ :=
    norm_nonneg _
  have hproduct :=
    mul_le_mul_of_nonneg_left hseriesBound hinverseNonnegative
  exact Eq.subst
    (motive := fun value : ℂ =>
      ‖value‖ ≤
        ‖(centeredQuadraticPrimitiveFourierNormalization)⁻¹‖ *
          (4 * (Real.pi ^ (2 : ℕ) / 6 + Real.pi ^ (2 : ℕ) / 6)))
    hidentity.symm
    (le_trans
      (le_of_eq
        (norm_mul
          (centeredQuadraticPrimitiveFourierNormalization)⁻¹
          (∑' m : ℤ,
            boundaryLineOnePointRealParam_centeredBernoulliWeightedModeIntegral
              t a L m)))
      hproduct)

end
end LFunctions
end Boundary
