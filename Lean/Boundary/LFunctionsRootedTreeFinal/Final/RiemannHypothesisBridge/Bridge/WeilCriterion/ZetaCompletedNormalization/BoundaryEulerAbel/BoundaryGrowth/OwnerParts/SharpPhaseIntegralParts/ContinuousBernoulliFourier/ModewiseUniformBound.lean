import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalization.BoundaryEulerAbel.BoundaryGrowth.OwnerParts.SharpPhaseIntegralParts.ContinuousBernoulliFourier.TranslatedInverseSquare

/-!
# Uniform global bound for one nonzero Bernoulli Fourier mode
-/

namespace Boundary
namespace LFunctions

noncomputable section

open MeasureTheory

/-- The integrated derivative of the amplitude-bearing reciprocal coefficient
costs at most two on the whole translated interval. -/
theorem intervalIntegral_norm_boundaryLineOnePointRealParam_unitBlockModeAmplitudeCoefficientDerivative_le_two
    (t : ℝ)
    {m : ℤ}
    (hm : m ≠ 0)
    {a : ℕ}
    (ha : ⌊2 + ‖t‖⌋₊ ≤ a)
    {L : ℝ}
    (hL : 0 ≤ L) :
    (∫ u in (0 : ℝ)..L,
        ‖Complex.realPhaseAmplitudeCoefficientDerivative
          (boundaryLineOnePointRealParam_unitBlockLogDerivativeAmplitude t a)
          (boundaryLineOnePointRealParam_unitBlockLogDerivativeAmplitudeDerivative t a)
          (boundaryLineOnePointRealParam_unitBlockModeCoefficientDerivative t m a)
          (boundaryLineOnePointRealParam_unitBlockCombinedPhaseDerivative t m a)
          u‖) ≤ 2 := by
  let density : ℝ → ℝ :=
    fun u => ‖t‖ / (((a : ℝ) + u) ^ (2 : ℕ))
  let actual : ℝ → ℝ :=
    fun u =>
      ‖Complex.realPhaseAmplitudeCoefficientDerivative
        (boundaryLineOnePointRealParam_unitBlockLogDerivativeAmplitude t a)
        (boundaryLineOnePointRealParam_unitBlockLogDerivativeAmplitudeDerivative t a)
        (boundaryLineOnePointRealParam_unitBlockModeCoefficientDerivative t m a)
        (boundaryLineOnePointRealParam_unitBlockCombinedPhaseDerivative t m a)
        u‖
  have hactual : IntervalIntegrable actual volume 0 L :=
    (intervalIntegrable_boundaryLineOnePointRealParam_unitBlockModeAmplitudeCoefficientDerivative
      t hm ha hL).norm
  have hdensity : IntervalIntegrable density volume 0 L :=
    intervalIntegrable_boundaryLineOnePointRealParam_translatedInverseSquare
      t ha hL
  have hmajorant :
      IntervalIntegrable (fun u => density u + density u) volume 0 L :=
    hdensity.add hdensity
  have hpointwise :
      ∀ u ∈ Set.Icc (0 : ℝ) L, actual u ≤ density u + density u := by
    intro u hu
    exact
      norm_boundaryLineOnePointRealParam_unitBlockModeAmplitudeCoefficientDerivative_le_inverseSquare
        t hm ha hu.1
  have hmono :
      (∫ u in (0 : ℝ)..L, actual u) ≤
        ∫ u in (0 : ℝ)..L, density u + density u :=
    intervalIntegral.integral_mono_on hL hactual hmajorant hpointwise
  have haddIntegral :
      (∫ u in (0 : ℝ)..L, density u + density u) =
        (∫ u in (0 : ℝ)..L, density u) +
          ∫ u in (0 : ℝ)..L, density u :=
    intervalIntegral.integral_add hdensity hdensity
  have hdensity_le : (∫ u in (0 : ℝ)..L, density u) ≤ 1 :=
    intervalIntegral_boundaryLineOnePointRealParam_translatedInverseSquare_le_one
      t ha hL
  have hsum :
      (∫ u in (0 : ℝ)..L, density u) +
          ∫ u in (0 : ℝ)..L, density u ≤ 1 + 1 :=
    add_le_add hdensity_le hdensity_le
  have honeAddOne : (1 : ℝ) + 1 = 2 :=
    one_add_one_eq_two
  have hsumTwo :
      (∫ u in (0 : ℝ)..L, density u) +
          ∫ u in (0 : ℝ)..L, density u ≤ 2 :=
    Eq.subst
      (motive := fun value : ℝ =>
        (∫ u in (0 : ℝ)..L, density u) +
            ∫ u in (0 : ℝ)..L, density u ≤ value)
      honeAddOne
      hsum
  have hmajorantIntegralLe :
      (∫ u in (0 : ℝ)..L, density u + density u) ≤ 2 :=
    Eq.subst
      (motive := fun value : ℝ => value ≤ 2)
      haddIntegral.symm
      hsumTwo
  exact le_trans hmono
    hmajorantIntegralLe

/-- Every nonzero Fourier mode has a uniform global norm bound of four. -/
theorem norm_intervalIntegral_boundaryLineOnePointRealParam_unitBlockMode_le_four
    (t : ℝ)
    {m : ℤ}
    (hm : m ≠ 0)
    {a : ℕ}
    (ha : ⌊2 + ‖t‖⌋₊ ≤ a)
    {L : ℝ}
    (hL : 0 ≤ L) :
    ‖∫ u in (0 : ℝ)..L,
        boundaryLineOnePointRealParam_unitBlockLogDerivativeAmplitude t a u *
          Complex.realPhaseOscillation
            (boundaryLineOnePointRealParam_unitBlockCombinedPhase t m a) u‖ ≤ 4 := by
  have hglobal :=
    norm_intervalIntegral_boundaryLineOnePointRealParam_unitBlockMode_le_boundary_add_remainder
      t hm ha hL
  have hright :=
    norm_boundaryLineOnePointRealParam_unitBlockModeAmplitudeCoefficient_le_one
      t hm ha hL
  have hleft :=
    norm_boundaryLineOnePointRealParam_unitBlockModeAmplitudeCoefficient_le_one
      t hm ha (show (0 : ℝ) ≤ 0 from le_rfl)
  have hremainder :=
    intervalIntegral_norm_boundaryLineOnePointRealParam_unitBlockModeAmplitudeCoefficientDerivative_le_two
      t hm ha hL
  have hsum : (1 : ℝ) + 1 + 2 = 4 := by
    exact Eq.trans
      (congrArg (fun value : ℝ => value + 2) one_add_one_eq_two)
      two_add_two_eq_four
  have hcomponents :
      ‖Complex.realPhaseAmplitudeCoefficient
          (boundaryLineOnePointRealParam_unitBlockLogDerivativeAmplitude t a)
          (boundaryLineOnePointRealParam_unitBlockCombinedPhaseDerivative t m a)
          L‖ +
        ‖Complex.realPhaseAmplitudeCoefficient
          (boundaryLineOnePointRealParam_unitBlockLogDerivativeAmplitude t a)
          (boundaryLineOnePointRealParam_unitBlockCombinedPhaseDerivative t m a)
          0‖ +
        (∫ u in (0 : ℝ)..L,
          ‖Complex.realPhaseAmplitudeCoefficientDerivative
            (boundaryLineOnePointRealParam_unitBlockLogDerivativeAmplitude t a)
            (boundaryLineOnePointRealParam_unitBlockLogDerivativeAmplitudeDerivative t a)
            (boundaryLineOnePointRealParam_unitBlockModeCoefficientDerivative t m a)
            (boundaryLineOnePointRealParam_unitBlockCombinedPhaseDerivative t m a)
            u‖) ≤
        (1 : ℝ) + 1 + 2 :=
    add_le_add (add_le_add hright hleft) hremainder
  have hcomponentsFour :
      ‖Complex.realPhaseAmplitudeCoefficient
          (boundaryLineOnePointRealParam_unitBlockLogDerivativeAmplitude t a)
          (boundaryLineOnePointRealParam_unitBlockCombinedPhaseDerivative t m a)
          L‖ +
        ‖Complex.realPhaseAmplitudeCoefficient
          (boundaryLineOnePointRealParam_unitBlockLogDerivativeAmplitude t a)
          (boundaryLineOnePointRealParam_unitBlockCombinedPhaseDerivative t m a)
          0‖ +
        (∫ u in (0 : ℝ)..L,
          ‖Complex.realPhaseAmplitudeCoefficientDerivative
            (boundaryLineOnePointRealParam_unitBlockLogDerivativeAmplitude t a)
            (boundaryLineOnePointRealParam_unitBlockLogDerivativeAmplitudeDerivative t a)
            (boundaryLineOnePointRealParam_unitBlockModeCoefficientDerivative t m a)
            (boundaryLineOnePointRealParam_unitBlockCombinedPhaseDerivative t m a)
            u‖) ≤ 4 :=
    Eq.subst
      (motive := fun value : ℝ =>
        ‖Complex.realPhaseAmplitudeCoefficient
            (boundaryLineOnePointRealParam_unitBlockLogDerivativeAmplitude t a)
            (boundaryLineOnePointRealParam_unitBlockCombinedPhaseDerivative t m a)
            L‖ +
          ‖Complex.realPhaseAmplitudeCoefficient
            (boundaryLineOnePointRealParam_unitBlockLogDerivativeAmplitude t a)
            (boundaryLineOnePointRealParam_unitBlockCombinedPhaseDerivative t m a)
            0‖ +
          (∫ u in (0 : ℝ)..L,
            ‖Complex.realPhaseAmplitudeCoefficientDerivative
              (boundaryLineOnePointRealParam_unitBlockLogDerivativeAmplitude t a)
              (boundaryLineOnePointRealParam_unitBlockLogDerivativeAmplitudeDerivative t a)
              (boundaryLineOnePointRealParam_unitBlockModeCoefficientDerivative t m a)
              (boundaryLineOnePointRealParam_unitBlockCombinedPhaseDerivative t m a)
              u‖) ≤ value)
      hsum
      hcomponents
  exact le_trans hglobal
    hcomponentsFour

end
end LFunctions
end Boundary
