import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalization.BoundaryEulerAbel.LogarithmicPhase.Curvature.RealPhaseLogarithmicFiniteComplementBudget
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalization.BoundaryEulerAbel.LogarithmicPhase.Curvature.RealPhaseLogarithmicPositiveTailArithmetic
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalization.BoundaryEulerAbel.LogarithmicPhase.Curvature.RealPhaseLogarithmicFarNegativeBudgetAssembly
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ClassicalAnalysis.ZetaEulerMaclaurinBoundary.LogarithmicPhase.PoissonPackets.QuantitativePhaseAdaptedEnhancedPositiveTail

/-!
# Complete complement-tail owner

This file replaces the coarse complement majorant in the completion path.  Its
finite term is the exact left/right/transition series budget, and its two
infinite terms are the proved phase-adapted far-negative and positive tails.
The public estimate is unconditional under the long-branch sign and endpoint
hypotheses and carries no analytic witness functions.
-/

namespace Boundary
namespace LFunctions

noncomputable section

def Complex.logarithmicPhaseCompleteOutsideTailBudget
    (t : ℝ) (a b : ℤ) : ℝ :=
  Complex.logarithmicPhaseEnhancedFarNegativeTailBudget t a b +
    Complex.logarithmicPhaseEnhancedPositiveTailBudget t a b

def Complex.logarithmicPhaseCompleteComplementTailBudget
    (t : ℝ) (a b : ℤ) : ℝ :=
  Complex.logarithmicPhaseFiniteComplementSeriesBudget t a b +
    Complex.logarithmicPhaseCompleteOutsideTailBudget t a b

theorem Complex.logarithmicPhaseEnhancedFarNegativeTailBudget_nonneg_explicit
    (t : ℝ) (a b : ℤ) (ha : 1 ≤ a) (hab : a ≤ b) :
    0 ≤ Complex.logarithmicPhaseEnhancedFarNegativeTailBudget t a b := by
  unfold Complex.logarithmicPhaseEnhancedFarNegativeTailBudget
  have hleft :=
    (Complex.logarithmicPhaseQuantitativeSupportLeft_pos a ha).le
  exact tsum_nonneg (fun m =>
    Complex.logarithmicPhaseAdaptedClosedMajorant_nonneg
      t a b
      (Complex.logarithmicPhaseLeftInactiveGap t m
        (Complex.logarithmicPhaseQuantitativeSupportLeft a))
      hab hleft
      (Complex.logarithmicPhaseFarNegative_leftGap_pos
        t a m ha m.property).le)

theorem Complex.logarithmicPhaseEnhancedPositiveTailBudget_nonneg_explicit
    (t : ℝ) (a b : ℤ) (ha : 1 ≤ a) (hab : a ≤ b) :
    0 ≤ Complex.logarithmicPhaseEnhancedPositiveTailBudget t a b := by
  unfold Complex.logarithmicPhaseEnhancedPositiveTailBudget
  have hleft :=
    (Complex.logarithmicPhaseQuantitativeSupportLeft_pos a ha).le
  exact tsum_nonneg (fun m =>
    Complex.logarithmicPhaseAdaptedClosedMajorant_nonneg
      t a b
      (Complex.logarithmicPhaseEnhancedPositiveModeGap t b m)
      hab hleft
      (Complex.logarithmicPhaseEnhancedPositiveModeGap_pos
        t a b m ha hab m.property).le)

theorem Complex.logarithmicPhaseCompleteOutsideTailBudget_nonneg
    (t : ℝ) (a b : ℤ) (ha : 1 ≤ a) (hab : a ≤ b) :
    0 ≤ Complex.logarithmicPhaseCompleteOutsideTailBudget t a b := by
  have hnegative :=
    Complex.logarithmicPhaseEnhancedFarNegativeTailBudget_nonneg_explicit
      t a b ha hab
  have hpositive :=
    Complex.logarithmicPhaseEnhancedPositiveTailBudget_nonneg_explicit
      t a b ha hab
  unfold Complex.logarithmicPhaseCompleteOutsideTailBudget
  exact add_nonneg hnegative hpositive

theorem Complex.logarithmicPhaseCompleteComplementTailBudget_nonneg
    (t : ℝ) (ht : 1 ≤ ‖t‖) (a b : ℤ)
    (ha : 1 ≤ a) (hab : a ≤ b) :
    0 ≤ Complex.logarithmicPhaseCompleteComplementTailBudget t a b := by
  have hfinite :=
    Complex.logarithmicPhaseFiniteComplementSeriesBudget_nonneg
      t ht a b ha hab
  have houtside :=
    Complex.logarithmicPhaseCompleteOutsideTailBudget_nonneg
      t a b ha hab
  unfold Complex.logarithmicPhaseCompleteComplementTailBudget
  exact add_nonneg hfinite houtside

theorem Complex.logarithmicPhaseAdaptedOutsideRangeBudget_eq_completeOutsideTailBudget
    (t : ℝ) (a b : ℤ) :
    Complex.logarithmicPhaseAdaptedOutsideRangeBudget t a b =
      Complex.logarithmicPhaseCompleteOutsideTailBudget t a b := by
  unfold Complex.logarithmicPhaseAdaptedOutsideRangeBudget
  unfold Complex.logarithmicPhaseCompleteOutsideTailBudget
  rfl

theorem Complex.logarithmicPhaseAdaptedInRangeInactiveBudget_eq_quantitative_of_nonneg
    (t : ℝ) (ht_nonneg : 0 ≤ t) (a b : ℤ) :
    Complex.logarithmicPhaseAdaptedInRangeInactiveBudget t a b =
      Complex.logarithmicPhaseQuantitativeInRangeInactiveBudget t a b := by
  unfold Complex.logarithmicPhaseAdaptedInRangeInactiveBudget
  unfold Complex.logarithmicPhaseQuantitativeInRangeInactiveBudget
  have hnorm : ‖t‖ = t := Real.norm_of_nonneg ht_nonneg
  exact congrArg
    (fun packetParameter : ℝ =>
      ∑ m ∈ Complex.logarithmicPhasePoissonInRangeInactiveModes t a b,
        ‖Complex.logarithmicPhaseQuantitativeBlockFourierPacket
          packetParameter a b m‖)
    hnorm

theorem Complex.logarithmicPhaseAdaptedComplementBudget_le_completeComplementTailBudget
    (t : ℝ) (ht : 1 ≤ ‖t‖) (ht_nonneg : 0 ≤ t)
    (a b : ℤ) (ha : 1 ≤ a) (hab : a ≤ b) :
    Complex.logarithmicPhaseAdaptedComplementBudget t a b ≤
      Complex.logarithmicPhaseCompleteComplementTailBudget t a b := by
  have hfiniteQuantitative :=
    Complex.logarithmicPhaseQuantitativeInRangeInactiveBudget_le_finiteComplementSeriesBudget
      t ht ht_nonneg a b ha hab
  have hbudgetIdentity :=
    Complex.logarithmicPhaseAdaptedInRangeInactiveBudget_eq_quantitative_of_nonneg
      t ht_nonneg a b
  have hfinite :
      Complex.logarithmicPhaseAdaptedInRangeInactiveBudget t a b ≤
        Complex.logarithmicPhaseFiniteComplementSeriesBudget t a b :=
    Eq.subst
      (motive := fun value : ℝ =>
        value ≤ Complex.logarithmicPhaseFiniteComplementSeriesBudget t a b)
      hbudgetIdentity.symm hfiniteQuantitative
  have houtside :
      Complex.logarithmicPhaseAdaptedOutsideRangeBudget t a b ≤
        Complex.logarithmicPhaseCompleteOutsideTailBudget t a b :=
    le_of_eq
      (Complex.logarithmicPhaseAdaptedOutsideRangeBudget_eq_completeOutsideTailBudget
        t a b)
  have hsum := add_le_add hfinite houtside
  unfold Complex.logarithmicPhaseAdaptedComplementBudget
  unfold Complex.logarithmicPhaseCompleteComplementTailBudget
  exact hsum

theorem Complex.norm_logarithmicPhaseCompleteOutsideTail_tsum_le
    (t : ℝ) (a b : ℤ) (ha : 1 ≤ a) (hab : a ≤ b) :
    ‖(∑' m : Complex.logarithmicPhasePoissonFarNegativeModes t a,
          Complex.logarithmicPhaseQuantitativeBlockFourierPacket ‖t‖ a b m) +
        (∑' m : Complex.logarithmicPhasePoissonPositiveTailModes,
          Complex.logarithmicPhaseQuantitativeBlockFourierPacket ‖t‖ a b m)‖ ≤
      Complex.logarithmicPhaseCompleteOutsideTailBudget t a b := by
  have hnegative :=
    Complex.norm_logarithmicPhaseEnhancedFarNegativeTail_tsum_le
      t a b ha hab
  have hpositive :=
    Complex.norm_logarithmicPhaseEnhancedPositiveTail_tsum_le
      t a b ha hab
  have htriangle := norm_add_le
    (∑' m : Complex.logarithmicPhasePoissonFarNegativeModes t a,
      Complex.logarithmicPhaseQuantitativeBlockFourierPacket ‖t‖ a b m)
    (∑' m : Complex.logarithmicPhasePoissonPositiveTailModes,
      Complex.logarithmicPhaseQuantitativeBlockFourierPacket ‖t‖ a b m)
  have hbudgets := add_le_add hnegative hpositive
  unfold Complex.logarithmicPhaseCompleteOutsideTailBudget
  exact le_trans htriangle hbudgets

theorem Complex.norm_logarithmicPhaseFiniteComplement_add_outsideTails_le
    (t : ℝ) (ht : 1 ≤ ‖t‖) (ht_nonneg : 0 ≤ t)
    (a b : ℤ) (ha : 1 ≤ a) (hab : a ≤ b) :
    ‖(∑' m : {m : ℤ //
          m ∈ Complex.logarithmicPhasePoissonInRangeInactiveModes t a b},
          Complex.logarithmicPhaseQuantitativeBlockFourierPacket t a b m) +
        ((∑' m : Complex.logarithmicPhasePoissonFarNegativeModes t a,
            Complex.logarithmicPhaseQuantitativeBlockFourierPacket t a b m) +
          (∑' m : Complex.logarithmicPhasePoissonPositiveTailModes,
            Complex.logarithmicPhaseQuantitativeBlockFourierPacket t a b m))‖ ≤
      Complex.logarithmicPhaseCompleteComplementTailBudget t a b := by
  have hfinite :=
    Complex.norm_logarithmicPhaseQuantitativeInRangeInactive_tsum_le_finiteComplementSeriesBudget
      t ht ht_nonneg a b ha hab
  have houtsideAtNorm :=
    Complex.norm_logarithmicPhaseCompleteOutsideTail_tsum_le
      t a b ha hab
  have hnorm : ‖t‖ = t := Real.norm_of_nonneg ht_nonneg
  have houtside :
      ‖(∑' m : Complex.logarithmicPhasePoissonFarNegativeModes t a,
          Complex.logarithmicPhaseQuantitativeBlockFourierPacket t a b m) +
        (∑' m : Complex.logarithmicPhasePoissonPositiveTailModes,
          Complex.logarithmicPhaseQuantitativeBlockFourierPacket t a b m)‖ ≤
        Complex.logarithmicPhaseCompleteOutsideTailBudget t a b :=
    Eq.subst
      (motive := fun packetParameter : ℝ =>
        ‖(∑' m : Complex.logarithmicPhasePoissonFarNegativeModes t a,
            Complex.logarithmicPhaseQuantitativeBlockFourierPacket
              packetParameter a b m) +
          (∑' m : Complex.logarithmicPhasePoissonPositiveTailModes,
            Complex.logarithmicPhaseQuantitativeBlockFourierPacket
              packetParameter a b m)‖ ≤
          Complex.logarithmicPhaseCompleteOutsideTailBudget t a b)
      hnorm houtsideAtNorm
  have htriangle := norm_add_le
    (∑' m : {m : ℤ //
      m ∈ Complex.logarithmicPhasePoissonInRangeInactiveModes t a b},
      Complex.logarithmicPhaseQuantitativeBlockFourierPacket t a b m)
    ((∑' m : Complex.logarithmicPhasePoissonFarNegativeModes t a,
        Complex.logarithmicPhaseQuantitativeBlockFourierPacket t a b m) +
      (∑' m : Complex.logarithmicPhasePoissonPositiveTailModes,
        Complex.logarithmicPhaseQuantitativeBlockFourierPacket t a b m))
  have hbudgets := add_le_add hfinite houtside
  unfold Complex.logarithmicPhaseCompleteComplementTailBudget
  exact le_trans htriangle hbudgets

theorem Complex.norm_logarithmicPhaseQuantitativePacket_tsum_le_active_add_completeComplement
    (t : ℝ) (ht : 1 ≤ ‖t‖) (ht_nonneg : 0 ≤ t)
    (a b : ℤ) (ha : 1 ≤ a) (hab : a ≤ b) :
    ‖∑' m : ℤ,
        Complex.logarithmicPhaseQuantitativeBlockFourierPacket t a b m‖ ≤
      ‖∑' m : {m : ℤ //
          m ∈ Complex.logarithmicPhasePoissonActiveModes t a b},
        Complex.logarithmicPhaseQuantitativeBlockFourierPacket t a b m‖ +
        Complex.logarithmicPhaseCompleteComplementTailBudget t a b := by
  have hglobalAtNorm :=
    Complex.norm_logarithmicPhaseQuantitativePacket_tsum_le_active_add_adaptedComplement
      t a b ha hab
  have hnorm : ‖t‖ = t := Real.norm_of_nonneg ht_nonneg
  have hglobal :
      ‖∑' m : ℤ,
          Complex.logarithmicPhaseQuantitativeBlockFourierPacket t a b m‖ ≤
        ‖∑' m : {m : ℤ //
            m ∈ Complex.logarithmicPhasePoissonActiveModes t a b},
          Complex.logarithmicPhaseQuantitativeBlockFourierPacket t a b m‖ +
          Complex.logarithmicPhaseAdaptedComplementBudget t a b :=
    Eq.subst
      (motive := fun packetParameter : ℝ =>
        ‖∑' m : ℤ,
            Complex.logarithmicPhaseQuantitativeBlockFourierPacket
              packetParameter a b m‖ ≤
          ‖∑' m : {m : ℤ //
              m ∈ Complex.logarithmicPhasePoissonActiveModes t a b},
            Complex.logarithmicPhaseQuantitativeBlockFourierPacket
              packetParameter a b m‖ +
            Complex.logarithmicPhaseAdaptedComplementBudget t a b)
      hnorm hglobalAtNorm
  have hcomplement :=
    Complex.logarithmicPhaseAdaptedComplementBudget_le_completeComplementTailBudget
      t ht ht_nonneg a b ha hab
  have hlift := add_le_add_left hcomplement
    ‖∑' m : {m : ℤ //
        m ∈ Complex.logarithmicPhasePoissonActiveModes t a b},
      Complex.logarithmicPhaseQuantitativeBlockFourierPacket t a b m‖
  exact le_trans hglobal hlift

theorem Complex.logarithmicPhaseCompleteComplementTailBudget_eq_four_classes
    (t : ℝ) (a b : ℤ) :
    Complex.logarithmicPhaseCompleteComplementTailBudget t a b =
      Complex.logarithmicPhaseFiniteLeftInactiveSeriesBudget t a b +
        Complex.logarithmicPhaseFiniteRightInactiveSeriesBudget t a b +
          Complex.logarithmicPhaseQuantitativeZeroModeBudget t a b +
            Complex.logarithmicPhaseEnhancedFarNegativeTailBudget t a b +
              Complex.logarithmicPhaseEnhancedPositiveTailBudget t a b := by
  unfold Complex.logarithmicPhaseCompleteComplementTailBudget
  unfold Complex.logarithmicPhaseFiniteComplementSeriesBudget
  unfold Complex.logarithmicPhaseCompleteOutsideTailBudget
  exact (add_assoc
    (Complex.logarithmicPhaseFiniteLeftInactiveSeriesBudget t a b +
      Complex.logarithmicPhaseFiniteRightInactiveSeriesBudget t a b +
        Complex.logarithmicPhaseQuantitativeZeroModeBudget t a b)
    (Complex.logarithmicPhaseEnhancedFarNegativeTailBudget t a b)
    (Complex.logarithmicPhaseEnhancedPositiveTailBudget t a b)).symm

end

end LFunctions
end Boundary
