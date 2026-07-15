import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalization.BoundaryEulerAbel.BoundaryGrowth.OwnerParts.SharpPhaseIntegralParts.ContinuousBernoulliFourier.GlobalPhaseAssembly
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalization.BoundaryEulerAbel.BoundaryGrowth.OwnerParts.Part06_PhaseBlocks

/-!
# Final continuous Bernoulli bound from the Fourier owner construction
-/

namespace Boundary
namespace LFunctions

noncomputable section

open MeasureTheory

private theorem realTwoAddFourEqSixForCombinedBound : (2 : ℝ) + 4 = 6 := by
  have hnat : ((2 + 4 : ℕ) : ℝ) = ((6 : ℕ) : ℝ) :=
    congrArg (fun n : ℕ => (n : ℝ))
      (show (2 + 4 : ℕ) = 6 from rfl)
  have hleft : ((2 + 4 : ℕ) : ℝ) = (2 : ℝ) + 4 :=
    Nat.cast_add 2 4
  have hright : ((6 : ℕ) : ℝ) = (6 : ℝ) :=
    rfl
  exact Eq.trans hleft.symm (Eq.trans hnat hright)

/-- The sum of affine local Bernoulli phase integrals is the negative centered
derivative contribution plus the constant Bernoulli-moment contribution. -/
theorem sum_boundaryLineOnePointRealParam_firstPeriodicBernoulli_unitBlock_eq_centered_add_constant
    (t : ℝ)
    {C : ℕ}
    (hC : ⌊2 + ‖t‖⌋₊ ≤ C)
    (D : ℕ) :
    (∑ k ∈ Finset.range D,
      ∫ u in (0 : ℝ)..1,
        Complex.realPhaseOscillation
            (boundaryLineOnePointRealParam_unitBlockCombinedPhase
              t 0 (C + k)) u *
          ((u - 1 / 2 : ℝ) : ℂ)) =
      -(∑ k ∈ Finset.range D,
        ∫ u in (0 : ℝ)..1,
          (boundaryLineOnePointRealParam_unitBlockLogDerivativeAmplitude
              t (C + k) u *
            Complex.realPhaseOscillation
              (boundaryLineOnePointRealParam_unitBlockCombinedPhase
                t 0 (C + k)) u) *
            eulerMaclaurinFirstPeriodicBernoulliCenteredQuadraticPrimitiveComplex u) +
        ∑ k ∈ Finset.range D,
          ∫ u in (0 : ℝ)..1,
            (boundaryLineOnePointRealParam_unitBlockLogDerivativeAmplitude
                t (C + k) u *
              Complex.realPhaseOscillation
                (boundaryLineOnePointRealParam_unitBlockCombinedPhase
                  t 0 (C + k)) u) *
              (1 / 12 : ℂ) := by
  let centered : ℕ → ℂ := fun k =>
    ∫ u in (0 : ℝ)..1,
      (boundaryLineOnePointRealParam_unitBlockLogDerivativeAmplitude
          t (C + k) u *
        Complex.realPhaseOscillation
          (boundaryLineOnePointRealParam_unitBlockCombinedPhase
            t 0 (C + k)) u) *
        eulerMaclaurinFirstPeriodicBernoulliCenteredQuadraticPrimitiveComplex u
  let constant : ℕ → ℂ := fun k =>
    ∫ u in (0 : ℝ)..1,
      (boundaryLineOnePointRealParam_unitBlockLogDerivativeAmplitude
          t (C + k) u *
        Complex.realPhaseOscillation
          (boundaryLineOnePointRealParam_unitBlockCombinedPhase
            t 0 (C + k)) u) *
        (1 / 12 : ℂ)
  have hlocal :
      ∀ k ∈ Finset.range D,
        (∫ u in (0 : ℝ)..1,
          Complex.realPhaseOscillation
              (boundaryLineOnePointRealParam_unitBlockCombinedPhase
                t 0 (C + k)) u *
            ((u - 1 / 2 : ℝ) : ℂ)) = -centered k + constant k := by
    intro k _hk
    exact
      boundaryLineOnePointRealParam_firstPeriodicBernoulli_unitBlock_eq_neg_centered_add_constant
        t (le_trans hC (Nat.le_add_right C k))
  have hsumLocal := Finset.sum_congr rfl hlocal
  have hdistribute :
      (∑ k ∈ Finset.range D, (-centered k + constant k)) =
        (∑ k ∈ Finset.range D, -centered k) +
          ∑ k ∈ Finset.range D, constant k :=
    Finset.sum_add_distrib
  have hnegative :
      (∑ k ∈ Finset.range D, -centered k) =
        -(∑ k ∈ Finset.range D, centered k) :=
    Finset.sum_neg_distrib
  exact Eq.trans hsumLocal
    (Eq.trans hdistribute
      (congrArg
        (fun z : ℂ => z + ∑ k ∈ Finset.range D, constant k)
        hnegative))

/-- The assembled global Bernoulli phase integral has norm at most one. -/
theorem norm_boundaryLineOnePointRealParam_firstPeriodicBernoulli_globalPhaseIntegral_le_one
    (t : ℝ)
    {K : ℕ}
    (hK : ⌊2 + ‖t‖⌋₊ ≤ K) :
    ‖∫ x in Set.Ioc (⌊2 + ‖t‖⌋₊ : ℝ) (K : ℝ),
        ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) *
          ((x : ℂ) ^ (-(t : ℂ) * Complex.I))‖ ≤ 1 := by
  let C : ℕ := ⌊2 + ‖t‖⌋₊
  let D : ℕ := K - C
  let centeredGlobal : ℂ :=
    ∫ u in (0 : ℝ)..(D : ℝ),
      (boundaryLineOnePointRealParam_unitBlockLogDerivativeAmplitude t C u *
        Complex.realPhaseOscillation
          (boundaryLineOnePointRealParam_unitBlockCombinedPhase t 0 C) u) *
        periodicCenteredQuadraticPrimitive u
  let constantGlobal : ℂ :=
    ∫ u in (0 : ℝ)..(D : ℝ),
      boundaryLineOnePointRealParam_globalZeroModeDerivative t C u *
        (1 / 12 : ℂ)
  have hC : ⌊2 + ‖t‖⌋₊ ≤ C :=
    le_rfl
  have hblocks :=
    sum_boundaryLineOnePointRealParam_firstPeriodicBernoulli_phaseBlock_eq_localRange
      t hC hK
  have hsplit :=
    sum_boundaryLineOnePointRealParam_firstPeriodicBernoulli_unitBlock_eq_centered_add_constant
      t hC D
  have hcentered :=
    sum_intervalIntegral_boundaryLineOnePointRealParam_localCentered_eq_global
      t hC D
  have hconstant :=
    sum_intervalIntegral_boundaryLineOnePointRealParam_localConstant_eq_global
      t hC D
  have hphaseBlocks :
      (∑ n ∈ Finset.Ioc C K,
        ∫ x in Set.Ioc ((n - 1 : ℕ) : ℝ) (n : ℝ),
          ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) *
            ((x : ℂ) ^ (-(t : ℂ) * Complex.I))) =
        -centeredGlobal + constantGlobal := by
    exact Eq.trans hblocks
      (Eq.trans hsplit
        (congrArg₂ Add.add
          (congrArg Neg.neg hcentered)
          hconstant))
  have hglobal :=
    boundaryLineOnePointRealParam_firstPeriodicBernoulli_phaseIntegralBlockSum_eq_global
      t (M := K)
  have hglobalIdentity :
      (∫ x in Set.Ioc (C : ℝ) (K : ℝ),
          ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) *
            ((x : ℂ) ^ (-(t : ℂ) * Complex.I))) =
        -centeredGlobal + constantGlobal :=
    Eq.trans hglobal.symm hphaseBlocks
  have hcenteredNorm : ‖centeredGlobal‖ ≤ (1 : ℝ) / 2 :=
    norm_intervalIntegral_boundaryLineOnePointRealParam_periodicCenteredQuadraticPrimitive_le_one_half
      t hC (Nat.cast_nonneg D)
  have hconstantNorm : ‖constantGlobal‖ ≤ (1 : ℝ) / 6 :=
    norm_intervalIntegral_boundaryLineOnePointRealParam_globalZeroModeDerivative_mul_oneTwelfth_le_oneSixth
      t hC (D := D)
  have htriangle : ‖-centeredGlobal + constantGlobal‖ ≤
      ‖centeredGlobal‖ + ‖constantGlobal‖ := by
    exact le_trans
      (norm_add_le (-centeredGlobal) constantGlobal)
      (add_le_add_right (le_of_eq (norm_neg centeredGlobal)) ‖constantGlobal‖)
  have hsix : (6 : ℝ) ≥ 2 :=
    Eq.subst
      (motive := fun value : ℝ => 2 ≤ value)
      realTwoAddFourEqSixForCombinedBound
      (le_add_of_nonneg_right zero_le_four)
  have honeSixth_le_half : (1 : ℝ) / 6 ≤ (1 : ℝ) / 2 :=
    one_div_le_one_div_of_le zero_lt_two hsix
  have hscalar : (1 : ℝ) / 2 + (1 : ℝ) / 6 ≤ 1 :=
    le_trans
      (add_le_add_left honeSixth_le_half ((1 : ℝ) / 2))
      (le_of_eq (add_halves 1))
  exact Eq.subst
    (motive := fun z : ℂ => ‖z‖ ≤ 1)
    hglobalIdentity.symm
    (le_trans htriangle
      (le_trans (add_le_add hcenteredNorm hconstantNorm) hscalar))

/-- Public sharp-scale form of the unconditional global continuous Bernoulli
estimate. -/
theorem norm_boundaryLineOnePointRealParam_firstPeriodicBernoulli_globalPhaseIntegral_le_postCutoffScale
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    {K : ℕ}
    (hK : ⌊2 + ‖t‖⌋₊ ≤ K) :
    ‖∫ x in Set.Ioc (⌊2 + ‖t‖⌋₊ : ℝ) (K : ℝ),
        ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) *
          ((x : ℂ) ^ (-(t : ℂ) * Complex.I))‖ ≤
      Real.sqrt (1 + ‖t‖) * Real.log (2 + K) := by
  exact le_trans
    (norm_boundaryLineOnePointRealParam_firstPeriodicBernoulli_globalPhaseIntegral_le_one
      t hK)
    (boundaryLineOnePointRealParam_one_le_sqrt_one_add_norm_mul_log_two_add_postCutoff
      t ht hK)

end
end LFunctions
end Boundary
