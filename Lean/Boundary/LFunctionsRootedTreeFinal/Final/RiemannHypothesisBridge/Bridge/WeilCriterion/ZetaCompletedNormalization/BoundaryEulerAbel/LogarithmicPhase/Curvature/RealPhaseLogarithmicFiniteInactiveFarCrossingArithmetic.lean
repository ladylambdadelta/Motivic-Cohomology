import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalization.BoundaryEulerAbel.LogarithmicPhase.Curvature.RealPhaseLogarithmicFiniteInactiveSharpAssembly
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalization.BoundaryEulerAbel.LogarithmicPhase.Curvature.RealPhaseLogarithmicModeRangeCardinality

/-!
# Cardinality arithmetic for finite far-inactive crossings

The far crossing charge is exactly `2/3` times the number of far modes.  The
left and right far classes are disjoint subsets of the in-range inactive
family, hence their combined cardinality is controlled by the canonical
Poisson mode-range majorant.
-/

namespace Boundary
namespace LFunctions

noncomputable section

def Complex.logarithmicPhaseFiniteFarModes
    (t : ℝ) (a b : ℤ) : Finset ℤ :=
  Complex.logarithmicPhaseFiniteLeftFarModes t a b ∪
    Complex.logarithmicPhaseFiniteRightFarModes t a b

theorem Complex.logarithmicPhaseFiniteLeftRightFar_disjoint
    (t : ℝ) (a b : ℤ) (hab : a ≤ b) :
    Disjoint
      (Complex.logarithmicPhaseFiniteLeftFarModes t a b)
      (Complex.logarithmicPhaseFiniteRightFarModes t a b) := by
  exact Finset.disjoint_left.mpr (fun m hleft hright =>
    have hleftBase :=
      ((Complex.mem_logarithmicPhaseFiniteLeftFarModes_iff
        t a b m).mp hleft).1
    have hrightBase :=
      ((Complex.mem_logarithmicPhaseFiniteRightFarModes_iff
        t a b m).mp hright).1
    have hdisjoint :=
      Complex.logarithmicPhasePoissonLeftRightInactive_disjoint t a b hab
    (Finset.disjoint_left.mp hdisjoint) hleftBase hrightBase)

theorem Complex.logarithmicPhaseFiniteFarModes_subset_leftRightInactive
    (t : ℝ) (a b : ℤ) :
    Complex.logarithmicPhaseFiniteFarModes t a b ⊆
      Complex.logarithmicPhasePoissonLeftInactiveModes t a b ∪
        Complex.logarithmicPhasePoissonRightInactiveModes t a b := by
  intro m hm
  have hcases := Finset.mem_union.mp hm
  match hcases with
  | Or.inl hleft =>
      exact Finset.mem_union_left _
        (Complex.logarithmicPhaseFiniteLeftFarModes_subset_leftInactive
          t a b hleft)
  | Or.inr hright =>
      exact Finset.mem_union_right _
        (Complex.logarithmicPhaseFiniteRightFarModes_subset_rightInactive
          t a b hright)

theorem Complex.logarithmicPhaseFiniteFarModes_subset_inRangeInactive
    (t : ℝ) (a b : ℤ) :
    Complex.logarithmicPhaseFiniteFarModes t a b ⊆
      Complex.logarithmicPhasePoissonInRangeInactiveModes t a b := by
  exact Finset.Subset.trans
    (Complex.logarithmicPhaseFiniteFarModes_subset_leftRightInactive t a b)
    (Complex.logarithmicPhasePoissonLeftRightInactive_subset_inRangeInactive
      t a b)

theorem Complex.logarithmicPhaseFiniteFarModes_card_eq_side_sum
    (t : ℝ) (a b : ℤ) (hab : a ≤ b) :
    (Complex.logarithmicPhaseFiniteFarModes t a b).card =
      (Complex.logarithmicPhaseFiniteLeftFarModes t a b).card +
        (Complex.logarithmicPhaseFiniteRightFarModes t a b).card := by
  unfold Complex.logarithmicPhaseFiniteFarModes
  exact Finset.card_union_of_disjoint
    (Complex.logarithmicPhaseFiniteLeftRightFar_disjoint t a b hab)

theorem Complex.logarithmicPhaseFiniteFarModes_card_le_inRangeInactive
    (t : ℝ) (a b : ℤ) :
    (Complex.logarithmicPhaseFiniteFarModes t a b).card ≤
      (Complex.logarithmicPhasePoissonInRangeInactiveModes t a b).card := by
  exact Finset.card_le_card
    (Complex.logarithmicPhaseFiniteFarModes_subset_inRangeInactive t a b)

theorem Complex.logarithmicPhaseFiniteFar_side_card_sum_le_inRangeInactive
    (t : ℝ) (a b : ℤ) (hab : a ≤ b) :
    (Complex.logarithmicPhaseFiniteLeftFarModes t a b).card +
        (Complex.logarithmicPhaseFiniteRightFarModes t a b).card ≤
      (Complex.logarithmicPhasePoissonInRangeInactiveModes t a b).card := by
  have heq :=
    Complex.logarithmicPhaseFiniteFarModes_card_eq_side_sum t a b hab
  exact Eq.subst (motive := fun value : ℕ => value ≤ _) heq
    (Complex.logarithmicPhaseFiniteFarModes_card_le_inRangeInactive t a b)

theorem Complex.logarithmicPhaseFiniteFar_side_card_cast_sum
    (t : ℝ) (a b : ℤ) :
    (((Complex.logarithmicPhaseFiniteLeftFarModes t a b).card : ℝ) +
        ((Complex.logarithmicPhaseFiniteRightFarModes t a b).card : ℝ)) =
      (((Complex.logarithmicPhaseFiniteLeftFarModes t a b).card +
        (Complex.logarithmicPhaseFiniteRightFarModes t a b).card : ℕ) : ℝ) := by
  exact (Nat.cast_add _ _).symm

theorem Complex.logarithmicPhaseFiniteFar_side_card_real_le_inRangeInactive
    (t : ℝ) (a b : ℤ) (hab : a ≤ b) :
    ((Complex.logarithmicPhaseFiniteLeftFarModes t a b).card : ℝ) +
        ((Complex.logarithmicPhaseFiniteRightFarModes t a b).card : ℝ) ≤
      ((Complex.logarithmicPhasePoissonInRangeInactiveModes t a b).card : ℝ) := by
  have hnat :=
    Complex.logarithmicPhaseFiniteFar_side_card_sum_le_inRangeInactive
      t a b hab
  have hcast :
      (((Complex.logarithmicPhaseFiniteLeftFarModes t a b).card +
        (Complex.logarithmicPhaseFiniteRightFarModes t a b).card : ℕ) : ℝ) ≤
        ((Complex.logarithmicPhasePoissonInRangeInactiveModes t a b).card : ℝ) :=
    Nat.cast_le.mpr hnat
  exact Eq.subst
    (motive := fun value : ℝ => value ≤ _)
    (Complex.logarithmicPhaseFiniteFar_side_card_cast_sum t a b).symm
    hcast

theorem Complex.logarithmicPhaseFiniteFar_side_card_real_le_modeRangeMajorant
    (t : ℝ) (a b : ℤ) (ha : 1 ≤ a) (hab : a ≤ b) :
    ((Complex.logarithmicPhaseFiniteLeftFarModes t a b).card : ℝ) +
        ((Complex.logarithmicPhaseFiniteRightFarModes t a b).card : ℝ) ≤
      Complex.logarithmicPhaseModeRangeCardMajorant t a := by
  exact le_trans
    (Complex.logarithmicPhaseFiniteFar_side_card_real_le_inRangeInactive
      t a b hab)
    (Complex.logarithmicPhaseInRangeInactive_card_real_le_majorant
      t a b ha)

theorem Complex.logarithmicPhaseFiniteFarCrossingBudget_le_modeRangeMajorant_mul
    (t : ℝ) (a b : ℤ) (ha : 1 ≤ a) (hab : a ≤ b) :
    Complex.logarithmicPhaseFiniteFarCrossingBudget t a b ≤
      Complex.logarithmicPhaseModeRangeCardMajorant t a * (2 / 3 : ℝ) := by
  have hcard :=
    Complex.logarithmicPhaseFiniteFar_side_card_real_le_modeRangeMajorant
      t a b ha hab
  have hscaled := mul_le_mul_of_nonneg_right hcard
    (div_nonneg (Nat.cast_nonneg 2) (Nat.cast_nonneg 3))
  exact Eq.subst
    (motive := fun value : ℝ => value ≤ _)
    (Complex.logarithmicPhaseFiniteFarCrossingBudget_eq_card_sum_mul
      t a b).symm
    hscaled

theorem Real.two_thirds_le_one : (2 / 3 : ℝ) ≤ 1 := by
  have htwo_le_three : (2 : ℝ) ≤ 3 :=
    Nat.cast_le.mpr (Nat.le_succ 2)
  have hthree_pos : (0 : ℝ) < 3 :=
    Nat.cast_pos.mpr (Nat.zero_lt_succ 2)
  exact (div_le_one₀ hthree_pos).mpr htwo_le_three

theorem Complex.logarithmicPhaseModeRangeCardMajorant_nonneg
    (t : ℝ) (a : ℤ) (ha : 1 ≤ a) :
    0 ≤ Complex.logarithmicPhaseModeRangeCardMajorant t a := by
  unfold Complex.logarithmicPhaseModeRangeCardMajorant
  have hdenom :
      0 < 2 * Real.pi * Real.integerBlockCutoffSupportLeftEndpoint a :=
    mul_pos Complex.two_mul_pi_pos
      (Complex.integerBlockCutoffSupportLeftEndpoint_pos ha)
  have hquotient :
      0 ≤ ‖t‖ /
        (2 * Real.pi * Real.integerBlockCutoffSupportLeftEndpoint a) :=
    div_nonneg (norm_nonneg t) hdenom.le
  exact add_nonneg (Nat.cast_nonneg 2) hquotient

theorem Complex.logarithmicPhaseFiniteFarCrossingBudget_le_modeRangeMajorant
    (t : ℝ) (a b : ℤ) (ha : 1 ≤ a) (hab : a ≤ b) :
    Complex.logarithmicPhaseFiniteFarCrossingBudget t a b ≤
      Complex.logarithmicPhaseModeRangeCardMajorant t a := by
  have hfirst :=
    Complex.logarithmicPhaseFiniteFarCrossingBudget_le_modeRangeMajorant_mul
      t a b ha hab
  have hmajorantNonneg :=
    Complex.logarithmicPhaseModeRangeCardMajorant_nonneg t a ha
  have hsecond := mul_le_mul_of_nonneg_left Real.two_thirds_le_one
    hmajorantNonneg
  exact le_trans hfirst
    (le_trans hsecond (le_of_eq (mul_one _)))

theorem Complex.logarithmicPhaseFiniteFarCrossingBudget_le_explicitFrequencyLength
    (t : ℝ) (a b : ℤ) (ha : 1 ≤ a) (hab : a ≤ b) :
    Complex.logarithmicPhaseFiniteFarCrossingBudget t a b ≤
      2 + ‖t‖ /
        (2 * Real.pi * Real.integerBlockCutoffSupportLeftEndpoint a) := by
  exact
    Complex.logarithmicPhaseFiniteFarCrossingBudget_le_modeRangeMajorant
      t a b ha hab

theorem Complex.logarithmicPhaseFiniteFarCrossingBudget_le_two_thirds_explicitFrequencyLength
    (t : ℝ) (a b : ℤ) (ha : 1 ≤ a) (hab : a ≤ b) :
    Complex.logarithmicPhaseFiniteFarCrossingBudget t a b ≤
      (2 / 3 : ℝ) *
        (2 + ‖t‖ /
          (2 * Real.pi * Real.integerBlockCutoffSupportLeftEndpoint a)) := by
  have hbase :=
    Complex.logarithmicPhaseFiniteFarCrossingBudget_le_modeRangeMajorant_mul
      t a b ha hab
  unfold Complex.logarithmicPhaseModeRangeCardMajorant at hbase
  exact le_trans hbase
    (le_of_eq
      (mul_comm
        (2 + ‖t‖ /
          (2 * Real.pi * Real.integerBlockCutoffSupportLeftEndpoint a))
        (2 / 3 : ℝ)))

theorem Complex.logarithmicPhaseFiniteInactiveSharpCrossingBudget_le_explicitFrequencyLength
    (t : ℝ) (a b : ℤ) (ha : 1 ≤ a) (hab : a ≤ b) :
    Complex.logarithmicPhaseFiniteInactiveSharpCrossingBudget t a b ≤
      (2 / 3 : ℝ) *
        (2 + ‖t‖ /
          (2 * Real.pi * Real.integerBlockCutoffSupportLeftEndpoint a)) := by
  unfold Complex.logarithmicPhaseFiniteInactiveSharpCrossingBudget
  exact
    Complex.logarithmicPhaseFiniteFarCrossingBudget_le_two_thirds_explicitFrequencyLength
      t a b ha hab

theorem Complex.logarithmicPhaseFiniteInactiveSharpStationaryBudget_le_seven_halves_scale
    {t : ℝ} {a b : ℕ}
    (ht : 1 ≤ ‖t‖) (ht_nonneg : 0 ≤ t)
    (hgeometry : Real.logarithmicPhaseLongBranchGeometry t a b) :
    Complex.logarithmicPhaseFiniteInactiveSharpStationaryBudget
        t (a : ℤ) (b : ℤ) ≤
      (7 / 2 : ℝ) * Complex.logarithmicPhaseBProcessScale t := by
  unfold Complex.logarithmicPhaseFiniteInactiveSharpStationaryBudget
  exact
    Complex.logarithmicPhaseFiniteNearQuantitativeBudget_le_seven_halves_scale
      ht ht_nonneg hgeometry

end

end LFunctions
end Boundary
