import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ClassicalAnalysis.ZetaEulerMaclaurinBoundary.LogarithmicPhase.PoissonPackets.QuantitativePhaseAdaptedOutsideEquiv

/-!
# Phase-adapted outside-range packet budget

The outside-range packet sum is reindexed through the exact tail-sum
equivalence and split into far-negative and positive series.  Their proved
phase-adapted tail bounds yield the replacement outside-range budget.
-/

namespace Boundary
namespace LFunctions

noncomputable section

def Complex.logarithmicPhaseTailSumPacket
    (t : ℝ) (a b : ℤ) :
    Sum
      (Complex.logarithmicPhasePoissonFarNegativeModes t a)
      Complex.logarithmicPhasePoissonPositiveTailModes → ℂ
  | Sum.inl m =>
      Complex.logarithmicPhaseQuantitativeBlockFourierPacket t a b m
  | Sum.inr m =>
      Complex.logarithmicPhaseQuantitativeBlockFourierPacket t a b m

theorem Complex.logarithmicPhaseTailSumPacket_comp_outsideEquiv
    (t : ℝ) (a b : ℤ) (ha : 1 ≤ a)
    (m : {m : ℤ // m ∉ Complex.logarithmicPhasePoissonModeRange t a}) :
    Complex.logarithmicPhaseTailSumPacket t a b
        (Complex.logarithmicPhaseOutsideEquivTailSum t a ha m) =
      Complex.logarithmicPhaseQuantitativeBlockFourierPacket t a b m := by
  unfold Complex.logarithmicPhaseOutsideEquivTailSum
  unfold Complex.logarithmicPhaseTailSumPacket
  unfold Complex.logarithmicPhaseOutsideToTailSum
  match Complex.logarithmicPhasePoissonOutsideRange_eq_farNegative_or_positive
      t a m with
  | Or.inl hfar => exact rfl
  | Or.inr hpositive => exact rfl

theorem Complex.logarithmicPhaseOutsidePacket_tsum_eq_tailSum_tsum
    (t : ℝ) (a b : ℤ) (ha : 1 ≤ a) :
    (∑' m : {m : ℤ // m ∉ Complex.logarithmicPhasePoissonModeRange t a},
      Complex.logarithmicPhaseQuantitativeBlockFourierPacket t a b m) =
    ∑' m : Sum
      (Complex.logarithmicPhasePoissonFarNegativeModes t a)
      Complex.logarithmicPhasePoissonPositiveTailModes,
      Complex.logarithmicPhaseTailSumPacket t a b m := by
  let e := Complex.logarithmicPhaseOutsideEquivTailSum t a ha
  have hreindex := e.tsum_eq (Complex.logarithmicPhaseTailSumPacket t a b)
  have hleft := tsum_congr
    (fun m : {m : ℤ // m ∉ Complex.logarithmicPhasePoissonModeRange t a} =>
      Complex.logarithmicPhaseTailSumPacket t a b (e m))
    (fun m =>
      Complex.logarithmicPhaseQuantitativeBlockFourierPacket t a b m)
    (fun m =>
      Complex.logarithmicPhaseTailSumPacket_comp_outsideEquiv
        t a b ha m)
  exact Eq.trans hleft.symm hreindex

theorem Complex.logarithmicPhaseTailSumPacket_tsum_eq_add
    (t : ℝ) (a b : ℤ) :
    (∑' m : Sum
      (Complex.logarithmicPhasePoissonFarNegativeModes t a)
      Complex.logarithmicPhasePoissonPositiveTailModes,
      Complex.logarithmicPhaseTailSumPacket t a b m) =
      (∑' m : Complex.logarithmicPhasePoissonFarNegativeModes t a,
        Complex.logarithmicPhaseQuantitativeBlockFourierPacket t a b m) +
      (∑' m : Complex.logarithmicPhasePoissonPositiveTailModes,
        Complex.logarithmicPhaseQuantitativeBlockFourierPacket t a b m) := by
  exact tsum_sum
    (fun m : Complex.logarithmicPhasePoissonFarNegativeModes t a =>
      Complex.logarithmicPhaseQuantitativeBlockFourierPacket t a b m)
    (fun m : Complex.logarithmicPhasePoissonPositiveTailModes =>
      Complex.logarithmicPhaseQuantitativeBlockFourierPacket t a b m)

theorem Complex.logarithmicPhaseOutsidePacket_tsum_eq_farNegative_add_positive
    (t : ℝ) (a b : ℤ) (ha : 1 ≤ a) :
    (∑' m : {m : ℤ // m ∉ Complex.logarithmicPhasePoissonModeRange t a},
      Complex.logarithmicPhaseQuantitativeBlockFourierPacket t a b m) =
      (∑' m : Complex.logarithmicPhasePoissonFarNegativeModes t a,
        Complex.logarithmicPhaseQuantitativeBlockFourierPacket t a b m) +
      (∑' m : Complex.logarithmicPhasePoissonPositiveTailModes,
        Complex.logarithmicPhaseQuantitativeBlockFourierPacket t a b m) := by
  exact Eq.trans
    (Complex.logarithmicPhaseOutsidePacket_tsum_eq_tailSum_tsum t a b ha)
    (Complex.logarithmicPhaseTailSumPacket_tsum_eq_add t a b)

theorem Complex.norm_logarithmicPhaseOutsidePacket_tsum_le_adaptedBudget
    (t : ℝ) (a b : ℤ)
    (ha : 1 ≤ a) (hab : a ≤ b) :
    ‖∑' m : {m : ℤ // m ∉ Complex.logarithmicPhasePoissonModeRange t a},
      Complex.logarithmicPhaseQuantitativeBlockFourierPacket t a b m‖ ≤
      Complex.logarithmicPhaseAdaptedOutsideRangeBudget t a b := by
  have hsplit :=
    Complex.logarithmicPhaseOutsidePacket_tsum_eq_farNegative_add_positive
      t a b ha
  have htriangle := norm_add_le
    (∑' m : Complex.logarithmicPhasePoissonFarNegativeModes t a,
      Complex.logarithmicPhaseQuantitativeBlockFourierPacket t a b m)
    (∑' m : Complex.logarithmicPhasePoissonPositiveTailModes,
      Complex.logarithmicPhaseQuantitativeBlockFourierPacket t a b m)
  have hnegative :=
    Complex.norm_logarithmicPhaseAdaptedFarNegativeTail_tsum_le
      t a b ha hab
  have hpositive :=
    Complex.norm_logarithmicPhaseEnhancedPositiveTail_tsum_le
      t a b ha hab
  unfold Complex.logarithmicPhaseAdaptedOutsideRangeBudget
  exact le_trans (le_of_eq (congrArg norm hsplit))
    (le_trans htriangle (add_le_add hnegative hpositive))

end
end LFunctions
end Boundary
