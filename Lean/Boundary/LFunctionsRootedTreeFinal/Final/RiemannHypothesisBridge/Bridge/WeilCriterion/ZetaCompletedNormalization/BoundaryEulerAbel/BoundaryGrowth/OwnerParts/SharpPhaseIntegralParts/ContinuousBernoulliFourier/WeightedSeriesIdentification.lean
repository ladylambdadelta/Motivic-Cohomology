import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalization.BoundaryEulerAbel.BoundaryGrowth.OwnerParts.SharpPhaseIntegralParts.ContinuousBernoulliFourier.CombinedPhaseFactorization

/-!
# Identification of the weighted Fourier series
-/

namespace Boundary
namespace LFunctions

noncomputable section

open MeasureTheory

/-- A weighted combined-phase mode is the common zero-mode factor times the
canonical centered-quadratic Fourier mode. -/
theorem boundaryLineOnePointRealParam_centeredBernoulliWeightedModeIntegrand_eq
    (t : ℝ)
    (a : ℕ)
    (m : ℤ)
    (u : ℝ) :
    boundaryLineOnePointRealParam_centeredBernoulliWeightedModeIntegrand
        t a m u =
      (boundaryLineOnePointRealParam_unitBlockLogDerivativeAmplitude t a u *
        Complex.realPhaseOscillation
          (boundaryLineOnePointRealParam_unitBlockCombinedPhase t 0 a) u) *
        centeredQuadraticPrimitiveFourierMode m u := by
  have hfactor :=
    boundaryLineOnePointRealParam_unitBlockCombinedOscillation_factor
      t m a u
  unfold boundaryLineOnePointRealParam_centeredBernoulliWeightedModeIntegrand
  unfold centeredQuadraticPrimitiveFourierMode
  let c : ℂ := (1 : ℂ) / (m : ℂ) ^ (2 : ℕ)
  let A : ℂ :=
    boundaryLineOnePointRealParam_unitBlockLogDerivativeAmplitude t a u
  let χ : ℂ := fourier m (u : UnitAddCircle)
  let E : ℂ :=
    Complex.realPhaseOscillation
      (boundaryLineOnePointRealParam_unitBlockCombinedPhase t 0 a) u
  exact Eq.trans
    (congrArg (fun z : ℂ => c * (A * z)) hfactor)
    (calc
      c * (A * (χ * E)) = c * A * χ * E := by
        exact Eq.trans
          (mul_assoc c A (χ * E)).symm
          (mul_assoc (c * A) χ E).symm
      _ = A * E * (c * χ) := by
        calc
          c * A * χ * E = (c * A * χ) * E := rfl
          _ = E * (c * A * χ) := mul_comm _ _
          _ = E * (A * (c * χ)) := by
            exact congrArg (fun z : ℂ => E * z)
              (Eq.trans
                (congrArg (fun z : ℂ => z * χ) (mul_comm c A))
                (mul_assoc A c χ))
          _ = (A * E) * (c * χ) := by
            exact Eq.trans
              (mul_assoc E A (c * χ)).symm
              (congrArg (fun z : ℂ => z * (c * χ)) (mul_comm E A)))

/-- Pointwise, the weighted mode `tsum` factors through the common logarithmic
amplitude and zero-mode oscillator. -/
theorem tsum_boundaryLineOnePointRealParam_centeredBernoulliWeightedModeIntegrand_eq
    (t : ℝ)
    (a : ℕ)
    (u : ℝ) :
    (∑' m : ℤ,
        boundaryLineOnePointRealParam_centeredBernoulliWeightedModeIntegrand
          t a m u) =
      (boundaryLineOnePointRealParam_unitBlockLogDerivativeAmplitude t a u *
        Complex.realPhaseOscillation
          (boundaryLineOnePointRealParam_unitBlockCombinedPhase t 0 a) u) *
        ∑' m : ℤ, centeredQuadraticPrimitiveFourierMode m u := by
  let common : ℂ :=
    boundaryLineOnePointRealParam_unitBlockLogDerivativeAmplitude t a u *
      Complex.realPhaseOscillation
        (boundaryLineOnePointRealParam_unitBlockCombinedPhase t 0 a) u
  have hterms :
      (fun m : ℤ =>
        boundaryLineOnePointRealParam_centeredBernoulliWeightedModeIntegrand
          t a m u) =
        (fun m : ℤ => common * centeredQuadraticPrimitiveFourierMode m u) := by
    funext m
    exact
      boundaryLineOnePointRealParam_centeredBernoulliWeightedModeIntegrand_eq
        t a m u
  exact Eq.trans
    (congrArg (fun f : ℤ → ℂ => ∑' m : ℤ, f m) hterms)
    tsum_mul_left

/-- The named weighted mode integrals sum to the integral of the common
logarithmic factor times the canonical centered-quadratic Fourier series. -/
theorem hasSum_boundaryLineOnePointRealParam_centeredBernoulliWeightedModeIntegral_eq_integral
    (t : ℝ)
    {a : ℕ}
    (ha : ⌊2 + ‖t‖⌋₊ ≤ a)
    {L : ℝ}
    (hL : 0 ≤ L) :
    HasSum
      (boundaryLineOnePointRealParam_centeredBernoulliWeightedModeIntegral
        t a L)
      (∫ u in (0 : ℝ)..L,
        (boundaryLineOnePointRealParam_unitBlockLogDerivativeAmplitude t a u *
          Complex.realPhaseOscillation
            (boundaryLineOnePointRealParam_unitBlockCombinedPhase t 0 a) u) *
          ∑' m : ℤ, centeredQuadraticPrimitiveFourierMode m u) := by
  have hraw :=
    hasSum_intervalIntegral_boundaryLineOnePointRealParam_centeredBernoulliWeightedModeIntegrand
      t ha hL
  have hterms :
      (fun m : ℤ =>
        ∫ u in (0 : ℝ)..L,
          boundaryLineOnePointRealParam_centeredBernoulliWeightedModeIntegrand
            t a m u) =
        boundaryLineOnePointRealParam_centeredBernoulliWeightedModeIntegral
          t a L := by
    funext m
    exact
      intervalIntegral_boundaryLineOnePointRealParam_centeredBernoulliWeightedModeIntegrand_eq
        t a L m
  have htarget :
      (∫ u in (0 : ℝ)..L,
        ∑' m : ℤ,
          boundaryLineOnePointRealParam_centeredBernoulliWeightedModeIntegrand
            t a m u) =
        ∫ u in (0 : ℝ)..L,
          (boundaryLineOnePointRealParam_unitBlockLogDerivativeAmplitude t a u *
            Complex.realPhaseOscillation
              (boundaryLineOnePointRealParam_unitBlockCombinedPhase t 0 a) u) *
            ∑' m : ℤ, centeredQuadraticPrimitiveFourierMode m u :=
    intervalIntegral.integral_congr
      (fun u _hu =>
        tsum_boundaryLineOnePointRealParam_centeredBernoulliWeightedModeIntegrand_eq
          t a u)
  exact Eq.subst
    (motive := fun f : ℤ → ℂ =>
      HasSum f
        (∫ u in (0 : ℝ)..L,
          (boundaryLineOnePointRealParam_unitBlockLogDerivativeAmplitude t a u *
            Complex.realPhaseOscillation
              (boundaryLineOnePointRealParam_unitBlockCombinedPhase t 0 a) u) *
            ∑' m : ℤ, centeredQuadraticPrimitiveFourierMode m u))
    hterms
    (Eq.subst
      (motive := fun value : ℂ =>
        HasSum
          (fun m : ℤ =>
            ∫ u in (0 : ℝ)..L,
              boundaryLineOnePointRealParam_centeredBernoulliWeightedModeIntegrand
                t a m u)
          value)
      htarget
      hraw)

end
end LFunctions
end Boundary
