import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalization.BoundaryEulerAbel.LogarithmicPhase.Curvature.RealPhaseLogarithmicFiniteInactiveProtectedSeries
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalization.BoundaryEulerAbel.LogarithmicPhase.Curvature.RealPhaseLogarithmicCompleteComplementTail

/-!
# Protected finite-complement and complete-complement budgets

The public complement component now uses full-support protected residuals for
both finite inactive classes.  The transition mode and the two already-proved
infinite tails are then added explicitly.  Every comparison is a theorem about
the actual quantitative Fourier packets.
-/

namespace Boundary
namespace LFunctions

noncomputable section

def Complex.logarithmicPhaseProtectedFiniteComplementBudget
    (t : ℝ) (a b : ℤ) : ℝ :=
  Complex.logarithmicPhaseFiniteLeftProtectedSeriesBudget t a b +
    Complex.logarithmicPhaseFiniteRightProtectedSeriesBudget t a b +
      Complex.logarithmicPhaseQuantitativeZeroModeBudget t a b

def Complex.logarithmicPhaseProtectedCompleteComplementBudget
    (t : ℝ) (a b : ℤ) : ℝ :=
  Complex.logarithmicPhaseProtectedFiniteComplementBudget t a b +
    Complex.logarithmicPhaseEnhancedFarNegativeTailBudget t a b +
      Complex.logarithmicPhaseEnhancedPositiveTailBudget t a b

theorem Complex.logarithmicPhaseProtectedFiniteComplementBudget_nonneg
    (t : ℝ) (ht : 1 ≤ ‖t‖) (a b : ℤ)
    (ha : 1 ≤ a) (hab : a ≤ b) :
    0 ≤ Complex.logarithmicPhaseProtectedFiniteComplementBudget t a b := by
  have hleft :=
    Complex.logarithmicPhaseFiniteLeftProtectedSeriesBudget_nonneg
      t ht a b ha hab
  have hright :=
    Complex.logarithmicPhaseFiniteRightProtectedSeriesBudget_nonneg
      t ht a b ha hab
  have hzero :=
    Complex.logarithmicPhaseQuantitativeZeroModeBudget_nonneg_explicit
      t a b ha hab
  unfold Complex.logarithmicPhaseProtectedFiniteComplementBudget
  exact add_nonneg (add_nonneg hleft hright) hzero

theorem Complex.logarithmicPhaseProtectedCompleteComplementBudget_nonneg
    (t : ℝ) (ht : 1 ≤ ‖t‖) (a b : ℤ)
    (ha : 1 ≤ a) (hab : a ≤ b) :
    0 ≤ Complex.logarithmicPhaseProtectedCompleteComplementBudget t a b := by
  have hfinite :=
    Complex.logarithmicPhaseProtectedFiniteComplementBudget_nonneg
      t ht a b ha hab
  have hnegative :=
    Complex.logarithmicPhaseEnhancedFarNegativeTailBudget_nonneg_explicit
      t a b ha hab
  have hpositive :=
    Complex.logarithmicPhaseEnhancedPositiveTailBudget_nonneg_explicit
      t a b ha hab
  unfold Complex.logarithmicPhaseProtectedCompleteComplementBudget
  exact add_nonneg (add_nonneg hfinite hnegative) hpositive

theorem Complex.logarithmicPhaseQuantitativeInRangeInactiveBudget_le_protectedFiniteComplementBudget
    (t : ℝ) (ht : 1 ≤ ‖t‖) (ht_nonneg : 0 ≤ t)
    (a b : ℤ) (ha : 1 ≤ a) (hab : a ≤ b) :
    Complex.logarithmicPhaseQuantitativeInRangeInactiveBudget t a b ≤
      Complex.logarithmicPhaseProtectedFiniteComplementBudget t a b := by
  have hpartition :=
    Complex.logarithmicPhaseQuantitativeInRangeInactiveBudget_le_left_add_right_add_zero
      t ht ht_nonneg a b ha hab
  have hleft :=
    Complex.logarithmicPhaseBProcessQuantitativeLeftInactiveBudget_le_protectedSeriesBudget
      t ht ht_nonneg a b ha hab
  have hright :=
    Complex.logarithmicPhaseBProcessQuantitativeRightInactiveBudget_le_protectedSeriesBudget
      t ht ht_nonneg a b ha hab
  have hzero :
      Complex.logarithmicPhaseQuantitativeZeroModeBudget t a b ≤
        Complex.logarithmicPhaseQuantitativeZeroModeBudget t a b :=
    le_refl _
  have hcombined := add_le_add (add_le_add hleft hright) hzero
  unfold Complex.logarithmicPhaseProtectedFiniteComplementBudget
  exact le_trans hpartition hcombined

theorem Complex.logarithmicPhaseAdaptedComplementBudget_le_protectedCompleteComplementBudget
    (t : ℝ) (ht : 1 ≤ ‖t‖) (ht_nonneg : 0 ≤ t)
    (a b : ℤ) (ha : 1 ≤ a) (hab : a ≤ b) :
    Complex.logarithmicPhaseAdaptedComplementBudget t a b ≤
      Complex.logarithmicPhaseProtectedCompleteComplementBudget t a b := by
  have hfinite :=
    Complex.logarithmicPhaseQuantitativeInRangeInactiveBudget_le_protectedFiniteComplementBudget
      t ht ht_nonneg a b ha hab
  have hfiniteIdentity :=
    Complex.logarithmicPhaseAdaptedInRangeInactiveBudget_eq_quantitative_of_nonneg
      t ht_nonneg a b
  have hfiniteAdapted :
      Complex.logarithmicPhaseAdaptedInRangeInactiveBudget t a b ≤
        Complex.logarithmicPhaseProtectedFiniteComplementBudget t a b :=
    Eq.subst
      (motive := fun value : ℝ =>
        value ≤ Complex.logarithmicPhaseProtectedFiniteComplementBudget t a b)
      hfiniteIdentity.symm hfinite
  have hnegative :
      Complex.logarithmicPhaseEnhancedFarNegativeTailBudget t a b ≤
        Complex.logarithmicPhaseEnhancedFarNegativeTailBudget t a b :=
    le_refl _
  have hpositive :
      Complex.logarithmicPhaseEnhancedPositiveTailBudget t a b ≤
        Complex.logarithmicPhaseEnhancedPositiveTailBudget t a b :=
    le_refl _
  have hcombined :=
    add_le_add (add_le_add hfiniteAdapted hnegative) hpositive
  have hdecomposition :=
    Complex.logarithmicPhaseAdaptedComplementBudget_eq_finite_add_tails
      t a b
  unfold Complex.logarithmicPhaseProtectedCompleteComplementBudget
  exact Eq.subst
    (motive := fun value : ℝ =>
      value ≤
        Complex.logarithmicPhaseProtectedFiniteComplementBudget t a b +
            Complex.logarithmicPhaseEnhancedFarNegativeTailBudget t a b +
          Complex.logarithmicPhaseEnhancedPositiveTailBudget t a b)
    hdecomposition.symm hcombined

theorem Complex.norm_logarithmicPhaseQuantitativeInRangeInactive_tsum_le_protectedFiniteComplementBudget
    (t : ℝ) (ht : 1 ≤ ‖t‖) (ht_nonneg : 0 ≤ t)
    (a b : ℤ) (ha : 1 ≤ a) (hab : a ≤ b) :
    ‖∑' m : {m : ℤ //
        m ∈ Complex.logarithmicPhasePoissonInRangeInactiveModes t a b},
        Complex.logarithmicPhaseQuantitativeBlockFourierPacket t a b m‖ ≤
      Complex.logarithmicPhaseProtectedFiniteComplementBudget t a b := by
  have hfinite :=
    (Complex.logarithmicPhasePoissonInRangeInactiveModes t a b).tsum_subtype
      (fun m : ℤ =>
        Complex.logarithmicPhaseQuantitativeBlockFourierPacket t a b m)
  have hnorm :
      ‖∑ m ∈ Complex.logarithmicPhasePoissonInRangeInactiveModes t a b,
          Complex.logarithmicPhaseQuantitativeBlockFourierPacket t a b m‖ ≤
        Complex.logarithmicPhaseQuantitativeInRangeInactiveBudget t a b := by
    unfold Complex.logarithmicPhaseQuantitativeInRangeInactiveBudget
    exact norm_sum_le _ _
  have hbudget :=
    Complex.logarithmicPhaseQuantitativeInRangeInactiveBudget_le_protectedFiniteComplementBudget
      t ht ht_nonneg a b ha hab
  exact Eq.subst
    (motive := fun value : ℂ =>
      ‖value‖ ≤ Complex.logarithmicPhaseProtectedFiniteComplementBudget t a b)
    hfinite.symm (le_trans hnorm hbudget)

theorem Complex.norm_logarithmicPhaseFiniteComplementAndTails_le_protectedCompleteBudget
    (t : ℝ) (ht : 1 ≤ ‖t‖) (ht_nonneg : 0 ≤ t)
    (a b : ℤ) (ha : 1 ≤ a) (hab : a ≤ b) :
    ‖(∑' m : {m : ℤ //
          m ∈ Complex.logarithmicPhasePoissonInRangeInactiveModes t a b},
          Complex.logarithmicPhaseQuantitativeBlockFourierPacket t a b m) +
        (∑' m : Complex.logarithmicPhasePoissonFarNegativeModes t a,
          Complex.logarithmicPhaseQuantitativeBlockFourierPacket t a b m) +
        (∑' m : Complex.logarithmicPhasePoissonPositiveTailModes,
          Complex.logarithmicPhaseQuantitativeBlockFourierPacket t a b m)‖ ≤
      Complex.logarithmicPhaseProtectedCompleteComplementBudget t a b := by
  have hfinite :=
    Complex.norm_logarithmicPhaseQuantitativeInRangeInactive_tsum_le_protectedFiniteComplementBudget
      t ht ht_nonneg a b ha hab
  have hnegative :=
    Complex.norm_logarithmicPhaseEnhancedFarNegativeTail_tsum_le
      t a b ha hab
  have hpositive :=
    Complex.norm_logarithmicPhaseEnhancedPositiveTail_tsum_le
      t a b ha hab
  have hnorm : ‖t‖ = t := Real.norm_of_nonneg ht_nonneg
  have hnegativeAtParameter :
      ‖∑' m : Complex.logarithmicPhasePoissonFarNegativeModes t a,
          Complex.logarithmicPhaseQuantitativeBlockFourierPacket t a b m‖ ≤
        Complex.logarithmicPhaseEnhancedFarNegativeTailBudget t a b :=
    Eq.subst
      (motive := fun packetParameter : ℝ =>
        ‖∑' m : Complex.logarithmicPhasePoissonFarNegativeModes t a,
            Complex.logarithmicPhaseQuantitativeBlockFourierPacket
              packetParameter a b m‖ ≤
          Complex.logarithmicPhaseEnhancedFarNegativeTailBudget t a b)
      hnorm hnegative
  have hpositiveAtParameter :
      ‖∑' m : Complex.logarithmicPhasePoissonPositiveTailModes,
          Complex.logarithmicPhaseQuantitativeBlockFourierPacket t a b m‖ ≤
        Complex.logarithmicPhaseEnhancedPositiveTailBudget t a b :=
    Eq.subst
      (motive := fun packetParameter : ℝ =>
        ‖∑' m : Complex.logarithmicPhasePoissonPositiveTailModes,
            Complex.logarithmicPhaseQuantitativeBlockFourierPacket
              packetParameter a b m‖ ≤
          Complex.logarithmicPhaseEnhancedPositiveTailBudget t a b)
      hnorm hpositive
  have hfirstTriangle := norm_add_le
    (∑' m : {m : ℤ //
      m ∈ Complex.logarithmicPhasePoissonInRangeInactiveModes t a b},
      Complex.logarithmicPhaseQuantitativeBlockFourierPacket t a b m)
    (∑' m : Complex.logarithmicPhasePoissonFarNegativeModes t a,
      Complex.logarithmicPhaseQuantitativeBlockFourierPacket t a b m)
  have hsecondTriangle := norm_add_le
    ((∑' m : {m : ℤ //
        m ∈ Complex.logarithmicPhasePoissonInRangeInactiveModes t a b},
        Complex.logarithmicPhaseQuantitativeBlockFourierPacket t a b m) +
      (∑' m : Complex.logarithmicPhasePoissonFarNegativeModes t a,
        Complex.logarithmicPhaseQuantitativeBlockFourierPacket t a b m))
    (∑' m : Complex.logarithmicPhasePoissonPositiveTailModes,
      Complex.logarithmicPhaseQuantitativeBlockFourierPacket t a b m)
  have hfirstBudget := add_le_add hfinite hnegativeAtParameter
  have hallBudget := add_le_add hfirstBudget hpositiveAtParameter
  unfold Complex.logarithmicPhaseProtectedCompleteComplementBudget
  exact le_trans hsecondTriangle
    (le_trans (add_le_add hfirstTriangle (le_refl _)) hallBudget)

theorem Complex.norm_logarithmicPhaseQuantitativePacket_tsum_le_active_add_protectedComplement
    (t : ℝ) (ht : 1 ≤ ‖t‖) (ht_nonneg : 0 ≤ t)
    (a b : ℤ) (ha : 1 ≤ a) (hab : a ≤ b) :
    ‖∑' m : ℤ,
        Complex.logarithmicPhaseQuantitativeBlockFourierPacket t a b m‖ ≤
      ‖∑' m : {m : ℤ //
          m ∈ Complex.logarithmicPhasePoissonActiveModes t a b},
        Complex.logarithmicPhaseQuantitativeBlockFourierPacket t a b m‖ +
        Complex.logarithmicPhaseProtectedCompleteComplementBudget t a b := by
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
    Complex.logarithmicPhaseAdaptedComplementBudget_le_protectedCompleteComplementBudget
      t ht ht_nonneg a b ha hab
  exact le_trans hglobal
    (add_le_add_left hcomplement
      ‖∑' m : {m : ℤ //
          m ∈ Complex.logarithmicPhasePoissonActiveModes t a b},
        Complex.logarithmicPhaseQuantitativeBlockFourierPacket t a b m‖)

theorem Complex.logarithmicPhaseProtectedCompleteComplementBudget_eq_components
    (t : ℝ) (a b : ℤ) :
    Complex.logarithmicPhaseProtectedCompleteComplementBudget t a b =
      Complex.logarithmicPhaseFiniteLeftProtectedSeriesBudget t a b +
        Complex.logarithmicPhaseFiniteRightProtectedSeriesBudget t a b +
          Complex.logarithmicPhaseQuantitativeZeroModeBudget t a b +
            Complex.logarithmicPhaseEnhancedFarNegativeTailBudget t a b +
              Complex.logarithmicPhaseEnhancedPositiveTailBudget t a b := by
  unfold Complex.logarithmicPhaseProtectedCompleteComplementBudget
  unfold Complex.logarithmicPhaseProtectedFiniteComplementBudget
  exact rfl

end

end LFunctions
end Boundary
