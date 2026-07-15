import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalization.BoundaryEulerAbel.BoundaryGrowth.OwnerParts.SharpPhaseIntegralParts.ContinuousBernoulliFourier.ModewiseIntegrability

/-!
# Global nonstationary bound for one Bernoulli Fourier mode

Unlike a blockwise estimate, this theorem applies integration by parts once on
the whole translated interval.  Consequently only the two global endpoints
occur, while the interior cost retains its integrable inverse-square decay.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open MeasureTheory

/-- One nonzero Fourier mode satisfies the global amplitude-bearing
nonstationary integration-by-parts estimate. -/
theorem norm_intervalIntegral_boundaryLineOnePointRealParam_unitBlockMode_le_boundary_add_remainder
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
            (boundaryLineOnePointRealParam_unitBlockCombinedPhase t m a) u‖ ≤
      ‖Complex.realPhaseAmplitudeCoefficient
          (boundaryLineOnePointRealParam_unitBlockLogDerivativeAmplitude t a)
          (boundaryLineOnePointRealParam_unitBlockCombinedPhaseDerivative t m a)
          L‖ +
        ‖Complex.realPhaseAmplitudeCoefficient
          (boundaryLineOnePointRealParam_unitBlockLogDerivativeAmplitude t a)
          (boundaryLineOnePointRealParam_unitBlockCombinedPhaseDerivative t m a)
          0‖ +
        ∫ u in (0 : ℝ)..L,
          ‖Complex.realPhaseAmplitudeCoefficientDerivative
            (boundaryLineOnePointRealParam_unitBlockLogDerivativeAmplitude t a)
            (boundaryLineOnePointRealParam_unitBlockLogDerivativeAmplitudeDerivative t a)
            (boundaryLineOnePointRealParam_unitBlockModeCoefficientDerivative t m a)
            (boundaryLineOnePointRealParam_unitBlockCombinedPhaseDerivative t m a)
            u‖ := by
  have hnonnegative :
      ∀ u ∈ Set.uIcc (0 : ℝ) L, 0 ≤ u := by
    intro u hu
    have huIcc : u ∈ Set.Icc (0 : ℝ) L :=
      Eq.subst (motive := fun s : Set ℝ => u ∈ s) (Set.uIcc_of_le hL) hu
    exact huIcc.1
  exact
    Complex.norm_intervalIntegral_realPhaseAmplitudeOscillation_le_boundary_add_remainder
      (boundaryLineOnePointRealParam_unitBlockLogDerivativeAmplitude t a)
      (boundaryLineOnePointRealParam_unitBlockLogDerivativeAmplitudeDerivative t a)
      (boundaryLineOnePointRealParam_unitBlockCombinedPhase t m a)
      (boundaryLineOnePointRealParam_unitBlockCombinedPhaseDerivative t m a)
      (boundaryLineOnePointRealParam_unitBlockModeCoefficientDerivative t m a)
      (fun u : ℝ =>
        Complex.realPhaseOscillation
            (boundaryLineOnePointRealParam_unitBlockCombinedPhase t m a) u *
          Complex.realPhaseDerivativeDenominator
            (boundaryLineOnePointRealParam_unitBlockCombinedPhaseDerivative t m a)
            u)
      0 L hL
      (fun u hu =>
        hasDerivAt_boundaryLineOnePointRealParam_unitBlockLogDerivativeAmplitude
          t a
          (boundaryLineOnePointRealParam_unitBlock_coordinate_pos
            t ha (hnonnegative u hu)))
      (fun u hu =>
        hasDerivAt_boundaryLineOnePointRealParam_unitBlockModeCoefficient
          t hm ha (hnonnegative u hu))
      (fun u hu =>
        hasDerivAt_boundaryLineOnePointRealParam_unitBlockModeOscillation
          t m ha (hnonnegative u hu))
      (intervalIntegrable_boundaryLineOnePointRealParam_unitBlockModeAmplitudeCoefficientDerivative
        t hm ha hL)
      (intervalIntegrable_boundaryLineOnePointRealParam_unitBlockModeOscillationDerivative
        t m ha hL)
      (fun _u _hu => rfl)
      (fun u hu =>
        boundaryLineOnePointRealParam_unitBlockMode_derivativeDenominator_ne_zero
          t hm ha (hnonnegative u hu))

end
end LFunctions
end Boundary
