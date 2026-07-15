import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalization.BoundaryEulerAbel.LogarithmicPhase.Curvature.RealPhaseLogarithmicFiniteLeftInactiveSeries
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalization.BoundaryEulerAbel.LogarithmicPhase.Curvature.RealPhaseLogarithmicFiniteRightInactiveSeries

/-!
# Exact finite-complement packet budget

The finite complement of the active stationary family is partitioned into its
left-inactive, right-inactive, and transition classes.  The first two classes
are controlled by their shifted reciprocal series; the transition class is
the zero Fourier mode.  This owner packages those proved estimates into the
single finite-complement component consumed by the B-process assembly.
-/

namespace Boundary
namespace LFunctions

noncomputable section

def Complex.logarithmicPhaseFiniteComplementSeriesBudget
    (t : ℝ) (a b : ℤ) : ℝ :=
  Complex.logarithmicPhaseFiniteLeftInactiveSeriesBudget t a b +
    Complex.logarithmicPhaseFiniteRightInactiveSeriesBudget t a b +
      Complex.logarithmicPhaseQuantitativeZeroModeBudget t a b

theorem Complex.logarithmicPhaseQuantitativeZeroModeBudget_nonneg_explicit
    (t : ℝ) (a b : ℤ) (ha : 1 ≤ a) (hab : a ≤ b) :
    0 ≤ Complex.logarithmicPhaseQuantitativeZeroModeBudget t a b := by
  unfold Complex.logarithmicPhaseQuantitativeZeroModeBudget
  have htwoThirds : (0 : ℝ) ≤ 2 / 3 :=
    div_nonneg zero_le_two zero_le_three
  have hbNonneg : (0 : ℝ) ≤ (b : ℝ) := by
    have hbInt : 0 ≤ b := le_trans (Int.ofNat_zero_le 1) (le_trans ha hab)
    exact Int.cast_nonneg.mpr hbInt
  have hnormInv : 0 ≤ ‖t‖⁻¹ := inv_nonneg.mpr (norm_nonneg t)
  have hquotient : 0 ≤ 2 * ((b : ℝ) / ‖t‖) := by
    have hdivision := div_nonneg hbNonneg (norm_nonneg t)
    exact mul_nonneg zero_le_two hdivision
  have habReal : (a : ℝ) ≤ (b : ℝ) := Int.cast_le.mpr hab
  have hlength : 0 ≤ (b : ℝ) - (a : ℝ) := sub_nonneg.mpr habReal
  have hsmul : 0 ≤ ((b : ℝ) - (a : ℝ)) • ‖t‖⁻¹ := by
    exact smul_nonneg hlength hnormInv
  exact add_nonneg (add_nonneg htwoThirds hquotient) hsmul

theorem Complex.logarithmicPhaseFiniteComplementSeriesBudget_nonneg
    (t : ℝ) (ht : 1 ≤ ‖t‖) (a b : ℤ)
    (ha : 1 ≤ a) (hab : a ≤ b) :
    0 ≤ Complex.logarithmicPhaseFiniteComplementSeriesBudget t a b := by
  have hleft :=
    Complex.logarithmicPhaseFiniteLeftInactiveSeriesBudget_nonneg
      t a b ha hab
  have hright :=
    Complex.logarithmicPhaseFiniteRightInactiveSeriesBudget_nonneg
      t ht a b ha hab
  have hzero :=
    Complex.logarithmicPhaseQuantitativeZeroModeBudget_nonneg_explicit
      t a b ha hab
  unfold Complex.logarithmicPhaseFiniteComplementSeriesBudget
  exact add_nonneg (add_nonneg hleft hright) hzero

theorem Complex.logarithmicPhaseQuantitativeInRangeInactiveBudget_le_finiteComplementSeriesBudget
    (t : ℝ) (ht : 1 ≤ ‖t‖) (ht_nonneg : 0 ≤ t)
    (a b : ℤ) (ha : 1 ≤ a) (hab : a ≤ b) :
    Complex.logarithmicPhaseQuantitativeInRangeInactiveBudget t a b ≤
      Complex.logarithmicPhaseFiniteComplementSeriesBudget t a b := by
  have hpartition :=
    Complex.logarithmicPhaseQuantitativeInRangeInactiveBudget_le_left_add_right_add_zero
      t ht ht_nonneg a b ha hab
  have hleft :=
    Complex.logarithmicPhaseBProcessQuantitativeLeftInactiveBudget_le_seriesBudget
      t ht ht_nonneg a b ha hab
  have hright :=
    Complex.logarithmicPhaseBProcessQuantitativeRightInactiveBudget_le_seriesBudget
      t ht ht_nonneg a b ha hab
  have hzeroRefl :
      Complex.logarithmicPhaseQuantitativeZeroModeBudget t a b ≤
        Complex.logarithmicPhaseQuantitativeZeroModeBudget t a b :=
    le_refl _
  have hcombined := add_le_add (add_le_add hleft hright) hzeroRefl
  unfold Complex.logarithmicPhaseFiniteComplementSeriesBudget
  exact le_trans hpartition hcombined

theorem Complex.norm_logarithmicPhaseQuantitativeInRangeInactive_tsum_le_finiteComplementSeriesBudget
    (t : ℝ) (ht : 1 ≤ ‖t‖) (ht_nonneg : 0 ≤ t)
    (a b : ℤ) (ha : 1 ≤ a) (hab : a ≤ b) :
    ‖∑' m : {m : ℤ //
        m ∈ Complex.logarithmicPhasePoissonInRangeInactiveModes t a b},
        Complex.logarithmicPhaseQuantitativeBlockFourierPacket t a b m‖ ≤
      Complex.logarithmicPhaseFiniteComplementSeriesBudget t a b := by
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
    Complex.logarithmicPhaseQuantitativeInRangeInactiveBudget_le_finiteComplementSeriesBudget
      t ht ht_nonneg a b ha hab
  exact Eq.subst
    (motive := fun value : ℂ =>
      ‖value‖ ≤ Complex.logarithmicPhaseFiniteComplementSeriesBudget t a b)
    hfinite.symm (le_trans hnorm hbudget)

theorem Complex.norm_logarithmicPhaseFiniteComplement_left_add_right_add_transition_le
    (t : ℝ) (ht : 1 ≤ ‖t‖) (ht_nonneg : 0 ≤ t)
    (a b : ℤ) (ha : 1 ≤ a) (hab : a ≤ b) :
    ‖(∑' m : {m : ℤ //
          m ∈ Complex.logarithmicPhasePoissonLeftInactiveModes t a b},
          Complex.logarithmicPhaseQuantitativeBlockFourierPacket t a b m) +
        (∑' m : {m : ℤ //
          m ∈ Complex.logarithmicPhasePoissonRightInactiveModes t a b},
          Complex.logarithmicPhaseQuantitativeBlockFourierPacket t a b m) +
        (∑' m : {m : ℤ //
          m ∈ Complex.logarithmicPhasePoissonTransitionModes t a b},
          Complex.logarithmicPhaseQuantitativeBlockFourierPacket t a b m)‖ ≤
      Complex.logarithmicPhaseFiniteComplementSeriesBudget t a b := by
  have hleft :=
    Complex.norm_logarithmicPhaseQuantitativeLeftInactive_tsum_le_budget
      t a b
  have hright :=
    Complex.norm_logarithmicPhaseQuantitativeRightInactive_tsum_le_budget
      t a b
  have htransition :=
    Complex.norm_logarithmicPhaseQuantitativeTransition_tsum_le_budget
      t a b
  have hleftSeries :=
    Complex.logarithmicPhaseBProcessQuantitativeLeftInactiveBudget_le_seriesBudget
      t ht ht_nonneg a b ha hab
  have hrightSeries :=
    Complex.logarithmicPhaseBProcessQuantitativeRightInactiveBudget_le_seriesBudget
      t ht ht_nonneg a b ha hab
  have hzero :=
    Complex.logarithmicPhaseBProcessQuantitativeTransitionBudget_le_zeroModeBudget
      t ht ht_nonneg ha hab
  have hleftFinal := le_trans hleft hleftSeries
  have hrightFinal := le_trans hright hrightSeries
  have htransitionFinal := le_trans htransition hzero
  have hnormFirst := norm_add_le
    (∑' m : {m : ℤ //
      m ∈ Complex.logarithmicPhasePoissonLeftInactiveModes t a b},
      Complex.logarithmicPhaseQuantitativeBlockFourierPacket t a b m)
    (∑' m : {m : ℤ //
      m ∈ Complex.logarithmicPhasePoissonRightInactiveModes t a b},
      Complex.logarithmicPhaseQuantitativeBlockFourierPacket t a b m)
  have hnormSecond := norm_add_le
    ((∑' m : {m : ℤ //
      m ∈ Complex.logarithmicPhasePoissonLeftInactiveModes t a b},
      Complex.logarithmicPhaseQuantitativeBlockFourierPacket t a b m) +
      (∑' m : {m : ℤ //
        m ∈ Complex.logarithmicPhasePoissonRightInactiveModes t a b},
        Complex.logarithmicPhaseQuantitativeBlockFourierPacket t a b m))
    (∑' m : {m : ℤ //
      m ∈ Complex.logarithmicPhasePoissonTransitionModes t a b},
      Complex.logarithmicPhaseQuantitativeBlockFourierPacket t a b m)
  have hfirstBudget := add_le_add hleftFinal hrightFinal
  have hallBudget := add_le_add hfirstBudget htransitionFinal
  unfold Complex.logarithmicPhaseFiniteComplementSeriesBudget
  exact le_trans hnormSecond
    (le_trans (add_le_add hnormFirst (le_refl _)) hallBudget)

theorem Complex.logarithmicPhaseFiniteComplementSeriesBudget_eq_components
    (t : ℝ) (a b : ℤ) :
    Complex.logarithmicPhaseFiniteComplementSeriesBudget t a b =
      Complex.logarithmicPhaseFiniteLeftInactiveSeriesBudget t a b +
        Complex.logarithmicPhaseFiniteRightInactiveSeriesBudget t a b +
          Complex.logarithmicPhaseQuantitativeZeroModeBudget t a b := by
  rfl

end

end LFunctions
end Boundary
