import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ClassicalAnalysis.ZetaEulerMaclaurinBoundary.LogarithmicPhase.PoissonPackets.QuantitativePhaseAdaptedEnhancedFarNegativeGap
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ClassicalAnalysis.ZetaEulerMaclaurinBoundary.LogarithmicPhase.PoissonPackets.QuantitativePhaseAdaptedEnhancedPositiveSeriesBudget

/-!
# Shift-preserving far-negative packet budget

The exact left-inactive majorant is reindexed by distance from the floor mode
and identified with the generic four-term shifted reciprocal packet series.
Unlike the coarse inverse-square tail, this budget retains the residual gap at
the lower endpoint and is therefore suitable for refined-scale arithmetic.
-/

namespace Boundary
namespace LFunctions

noncomputable section

def Complex.logarithmicPhaseEnhancedFarNegativeTailBudget
    (t : ℝ) (a b : ℤ) : ℝ :=
  ∑' m : Complex.logarithmicPhasePoissonFarNegativeModes t a,
    Complex.logarithmicPhaseLeftInactiveClosedMajorant t a b m

def Complex.logarithmicPhaseEnhancedFarNegativeSeriesBudget
    (t : ℝ) (a b : ℤ) : ℝ :=
  Real.shiftedReciprocalPacketSeriesBudget
    (Complex.logarithmicPhaseFarNegativeResidualGap t a)
    Complex.logarithmicPhaseAngularStep
    Complex.logarithmicPhaseAdaptedSquareCoefficient
    (Complex.logarithmicPhaseAdaptedCurvatureCubeCoefficient t a)
    (Complex.logarithmicPhaseAdaptedThirdCubeCoefficient t a b)
    (Complex.logarithmicPhaseAdaptedCurvatureFourthCoefficient t a b)

theorem Complex.enhancedFarNegativeMajorant_reindexed_eq_packetTerm
    (t : ℝ) (a b : ℤ) (n : ℕ) :
    Complex.logarithmicPhaseLeftInactiveClosedMajorant t a b
        ((Complex.logarithmicPhaseFarNegativeEquivNat t a).symm n : ℤ) =
      Real.shiftedReciprocalPacketTerm
        (Complex.logarithmicPhaseFarNegativeResidualGap t a)
        Complex.logarithmicPhaseAngularStep
        Complex.logarithmicPhaseAdaptedSquareCoefficient
        (Complex.logarithmicPhaseAdaptedCurvatureCubeCoefficient t a)
        (Complex.logarithmicPhaseAdaptedThirdCubeCoefficient t a b)
        (Complex.logarithmicPhaseAdaptedCurvatureFourthCoefficient t a b)
        n := by
  unfold Complex.logarithmicPhaseLeftInactiveClosedMajorant
  have hcoefficients :=
    Complex.logarithmicPhaseAdaptedClosedMajorant_eq_coefficients
      t a b
      (Complex.logarithmicPhaseLeftInactiveGap t
        ((Complex.logarithmicPhaseFarNegativeEquivNat t a).symm n : ℤ)
        (Complex.logarithmicPhaseQuantitativeSupportLeft a))
  have htwo :=
    Complex.enhancedFarNegative_inverseSquare_eq_shiftedTerm t a n
  have hthree :=
    Complex.enhancedFarNegative_inverseCube_eq_shiftedTerm t a n
  have hfour :=
    Complex.enhancedFarNegative_inverseFourth_eq_shiftedTerm t a n
  unfold Real.shiftedReciprocalPacketTerm
  have hsquareTransport :=
    congrArg
      (fun squareTerm : ℝ =>
        Complex.logarithmicPhaseAdaptedSquareCoefficient * squareTerm +
        Complex.logarithmicPhaseAdaptedCurvatureCubeCoefficient t a *
          (1 / (Complex.logarithmicPhaseLeftInactiveGap t
            ((Complex.logarithmicPhaseFarNegativeEquivNat t a).symm n : ℤ)
            (Complex.logarithmicPhaseQuantitativeSupportLeft a)) ^ 3) +
        Complex.logarithmicPhaseAdaptedThirdCubeCoefficient t a b *
          (1 / (Complex.logarithmicPhaseLeftInactiveGap t
            ((Complex.logarithmicPhaseFarNegativeEquivNat t a).symm n : ℤ)
            (Complex.logarithmicPhaseQuantitativeSupportLeft a)) ^ 3) +
        Complex.logarithmicPhaseAdaptedCurvatureFourthCoefficient t a b *
          (1 / (Complex.logarithmicPhaseLeftInactiveGap t
            ((Complex.logarithmicPhaseFarNegativeEquivNat t a).symm n : ℤ)
            (Complex.logarithmicPhaseQuantitativeSupportLeft a)) ^ 4))
      htwo
  have hcubeTransport :=
    congrArg
      (fun cubeTerm : ℝ =>
        Complex.logarithmicPhaseAdaptedSquareCoefficient *
            Real.shiftedInverseSquareTerm
              (Complex.logarithmicPhaseFarNegativeResidualGap t a)
              Complex.logarithmicPhaseAngularStep n +
        Complex.logarithmicPhaseAdaptedCurvatureCubeCoefficient t a *
            cubeTerm +
        Complex.logarithmicPhaseAdaptedThirdCubeCoefficient t a b *
            cubeTerm +
        Complex.logarithmicPhaseAdaptedCurvatureFourthCoefficient t a b *
          (1 / (Complex.logarithmicPhaseLeftInactiveGap t
            ((Complex.logarithmicPhaseFarNegativeEquivNat t a).symm n : ℤ)
            (Complex.logarithmicPhaseQuantitativeSupportLeft a)) ^ 4))
      hthree
  have hfourthTransport :=
    congrArg
      (fun fourthTerm : ℝ =>
        Complex.logarithmicPhaseAdaptedSquareCoefficient *
            Real.shiftedInverseSquareTerm
              (Complex.logarithmicPhaseFarNegativeResidualGap t a)
              Complex.logarithmicPhaseAngularStep n +
        Complex.logarithmicPhaseAdaptedCurvatureCubeCoefficient t a *
            Real.shiftedInverseCubeTerm
              (Complex.logarithmicPhaseFarNegativeResidualGap t a)
              Complex.logarithmicPhaseAngularStep n +
        Complex.logarithmicPhaseAdaptedThirdCubeCoefficient t a b *
            Real.shiftedInverseCubeTerm
              (Complex.logarithmicPhaseFarNegativeResidualGap t a)
              Complex.logarithmicPhaseAngularStep n +
        Complex.logarithmicPhaseAdaptedCurvatureFourthCoefficient t a b *
            fourthTerm)
      hfour
  exact Eq.trans hcoefficients
    (Eq.trans hsquareTransport
      (Eq.trans hcubeTransport hfourthTransport))

theorem Complex.tsum_enhancedFarNegativeMajorant_eq_shiftedPacketTsum
    (t : ℝ) (a b : ℤ) :
    (∑' m : Complex.logarithmicPhasePoissonFarNegativeModes t a,
      Complex.logarithmicPhaseLeftInactiveClosedMajorant t a b m) =
      ∑' n : ℕ,
        Real.shiftedReciprocalPacketTerm
          (Complex.logarithmicPhaseFarNegativeResidualGap t a)
          Complex.logarithmicPhaseAngularStep
          Complex.logarithmicPhaseAdaptedSquareCoefficient
          (Complex.logarithmicPhaseAdaptedCurvatureCubeCoefficient t a)
          (Complex.logarithmicPhaseAdaptedThirdCubeCoefficient t a b)
          (Complex.logarithmicPhaseAdaptedCurvatureFourthCoefficient t a b)
          n := by
  have hreindex := Complex.tsum_farNegative_comp_equivNat t a
    (fun m : Complex.logarithmicPhasePoissonFarNegativeModes t a =>
      Complex.logarithmicPhaseLeftInactiveClosedMajorant t a b m)
  have hterms := tsum_congr
    (fun n =>
      Complex.enhancedFarNegativeMajorant_reindexed_eq_packetTerm t a b n)
  exact Eq.trans hreindex hterms

theorem Complex.logarithmicPhaseEnhancedFarNegativeTailBudget_eq_series
    (t : ℝ) (a b : ℤ) :
    Complex.logarithmicPhaseEnhancedFarNegativeTailBudget t a b =
      ∑' n : ℕ,
        Real.shiftedReciprocalPacketTerm
          (Complex.logarithmicPhaseFarNegativeResidualGap t a)
          Complex.logarithmicPhaseAngularStep
          Complex.logarithmicPhaseAdaptedSquareCoefficient
          (Complex.logarithmicPhaseAdaptedCurvatureCubeCoefficient t a)
          (Complex.logarithmicPhaseAdaptedThirdCubeCoefficient t a b)
          (Complex.logarithmicPhaseAdaptedCurvatureFourthCoefficient t a b)
          n := by
  unfold Complex.logarithmicPhaseEnhancedFarNegativeTailBudget
  exact Complex.tsum_enhancedFarNegativeMajorant_eq_shiftedPacketTsum t a b

theorem Complex.summable_logarithmicPhaseEnhancedFarNegativeMajorant
    (t : ℝ) (a b : ℤ) (ha : 1 ≤ a) :
    Summable (fun m : Complex.logarithmicPhasePoissonFarNegativeModes t a =>
      Complex.logarithmicPhaseLeftInactiveClosedMajorant t a b m) := by
  have hresidual :=
    Complex.logarithmicPhaseFarNegativeResidualGap_nonneg t a ha
  have hstep := Complex.logarithmicPhaseAngularStep_pos
  have hseries := Real.summable_shiftedReciprocalPacketTerm
    (Complex.logarithmicPhaseFarNegativeResidualGap t a)
    Complex.logarithmicPhaseAngularStep
    Complex.logarithmicPhaseAdaptedSquareCoefficient
    (Complex.logarithmicPhaseAdaptedCurvatureCubeCoefficient t a)
    (Complex.logarithmicPhaseAdaptedThirdCubeCoefficient t a b)
    (Complex.logarithmicPhaseAdaptedCurvatureFourthCoefficient t a b)
    hresidual hstep
  have htransport :=
    (Complex.logarithmicPhaseFarNegativeEquivNat t a).summable_iff.mpr hseries
  have hfunction :
      (fun m : Complex.logarithmicPhasePoissonFarNegativeModes t a =>
        Real.shiftedReciprocalPacketTerm
          (Complex.logarithmicPhaseFarNegativeResidualGap t a)
          Complex.logarithmicPhaseAngularStep
          Complex.logarithmicPhaseAdaptedSquareCoefficient
          (Complex.logarithmicPhaseAdaptedCurvatureCubeCoefficient t a)
          (Complex.logarithmicPhaseAdaptedThirdCubeCoefficient t a b)
          (Complex.logarithmicPhaseAdaptedCurvatureFourthCoefficient t a b)
          (Complex.logarithmicPhaseFarNegativeEquivNat t a m)) =
      (fun m : Complex.logarithmicPhasePoissonFarNegativeModes t a =>
        Complex.logarithmicPhaseLeftInactiveClosedMajorant t a b m) := by
    exact funext (fun m =>
      have hrecover :=
        (Complex.logarithmicPhaseFarNegativeEquivNat t a).symm_apply_apply m
      have hterm :=
        Complex.enhancedFarNegativeMajorant_reindexed_eq_packetTerm
          t a b (Complex.logarithmicPhaseFarNegativeEquivNat t a m)
      Eq.trans hterm.symm
        (congrArg
          (fun mode : Complex.logarithmicPhasePoissonFarNegativeModes t a =>
            Complex.logarithmicPhaseLeftInactiveClosedMajorant t a b mode)
          hrecover))
  exact Eq.subst
    (motive := fun function :
      Complex.logarithmicPhasePoissonFarNegativeModes t a → ℝ =>
      Summable function)
    hfunction htransport

theorem Complex.logarithmicPhaseEnhancedFarNegativeTailBudget_le_seriesBudget
    (t : ℝ) (a b : ℤ)
    (ha : 1 ≤ a) (hab : a ≤ b) :
    Complex.logarithmicPhaseEnhancedFarNegativeTailBudget t a b ≤
      Complex.logarithmicPhaseEnhancedFarNegativeSeriesBudget t a b := by
  have hresidual :=
    Complex.logarithmicPhaseFarNegativeResidualGap_nonneg t a ha
  have hstep := Complex.logarithmicPhaseAngularStep_pos
  have hleft :=
    (Complex.logarithmicPhaseQuantitativeSupportLeft_pos a ha).le
  have hsquare :=
    Complex.logarithmicPhaseAdaptedSquareCoefficient_nonneg
  have hcurvature :=
    Complex.logarithmicPhaseAdaptedCurvatureCubeCoefficient_nonneg
      t a hleft
  have hthird :=
    Complex.logarithmicPhaseAdaptedThirdCubeCoefficient_nonneg
      t a b hab hleft
  have hfourth :=
    Complex.logarithmicPhaseAdaptedCurvatureFourthCoefficient_nonneg
      t a b hab hleft
  have hseries := Real.tsum_shiftedReciprocalPacketTerm_le_seriesBudget
    (Complex.logarithmicPhaseFarNegativeResidualGap t a)
    Complex.logarithmicPhaseAngularStep
    Complex.logarithmicPhaseAdaptedSquareCoefficient
    (Complex.logarithmicPhaseAdaptedCurvatureCubeCoefficient t a)
    (Complex.logarithmicPhaseAdaptedThirdCubeCoefficient t a b)
    (Complex.logarithmicPhaseAdaptedCurvatureFourthCoefficient t a b)
    hresidual hstep hsquare hcurvature hthird hfourth
  have hidentify :=
    Complex.logarithmicPhaseEnhancedFarNegativeTailBudget_eq_series t a b
  unfold Complex.logarithmicPhaseEnhancedFarNegativeSeriesBudget
  exact le_trans (le_of_eq hidentify) hseries

theorem Complex.norm_logarithmicPhaseEnhancedFarNegativeTail_tsum_le
    (t : ℝ) (a b : ℤ)
    (ha : 1 ≤ a) (hab : a ≤ b) :
    ‖∑' m : Complex.logarithmicPhasePoissonFarNegativeModes t a,
        Complex.logarithmicPhaseQuantitativeBlockFourierPacket (‖t‖) a b m‖ ≤
      Complex.logarithmicPhaseEnhancedFarNegativeTailBudget t a b := by
  unfold Complex.logarithmicPhaseEnhancedFarNegativeTailBudget
  exact tsum_norm_le
    (Complex.summable_logarithmicPhaseEnhancedFarNegativeMajorant
      t a b ha)
    (fun m =>
      Complex.norm_logarithmicPhaseFarNegativeModePacket_le
        t a b ha hab m)

end
end LFunctions
end Boundary
