import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ClassicalAnalysis.ZetaEulerMaclaurinBoundary.LogarithmicPhase.PoissonPackets.CanonicalGlobalBudget

/-!
# Arithmetic of the logarithmic Poisson mode range

The direct Poisson range is an integer interval with a floor-defined lower
endpoint.  This file owns the exact interval and cardinal identities so later
analytic estimates can use them without unfolding the range definition.
-/

namespace Boundary
namespace LFunctions

noncomputable section

def Complex.logarithmicPhasePoissonModeRangeLower
    (t : ℝ) (a : ℤ) : ℤ :=
  Int.floor
    ((-‖t‖ / Real.integerBlockCutoffSupportLeftEndpoint a) /
      (2 * Real.pi))

theorem Complex.logarithmicPhasePoissonModeRange_eq_Icc
    (t : ℝ) (a : ℤ) :
    Complex.logarithmicPhasePoissonModeRange t a =
      Finset.Icc (Complex.logarithmicPhasePoissonModeRangeLower t a) 0 :=
  rfl

theorem Complex.mem_logarithmicPhasePoissonModeRange_iff
    (t : ℝ) (a m : ℤ) :
    m ∈ Complex.logarithmicPhasePoissonModeRange t a ↔
      Complex.logarithmicPhasePoissonModeRangeLower t a ≤ m ∧ m ≤ 0 := by
  unfold Complex.logarithmicPhasePoissonModeRange
  exact Finset.mem_Icc

theorem Complex.logarithmicPhasePoissonModeRange_card_eq_toNat
    (t : ℝ) (a : ℤ) :
    (Complex.logarithmicPhasePoissonModeRange t a).card =
      (0 + 1 - Complex.logarithmicPhasePoissonModeRangeLower t a).toNat := by
  unfold Complex.logarithmicPhasePoissonModeRange
  exact Int.card_Icc

theorem Complex.logarithmicPhasePoissonModeRange_card_cast_eq_of_lower_le_one
    (t : ℝ) (a : ℤ)
    (hlower : Complex.logarithmicPhasePoissonModeRangeLower t a ≤ 1) :
    ((Complex.logarithmicPhasePoissonModeRange t a).card : ℤ) =
      1 - Complex.logarithmicPhasePoissonModeRangeLower t a := by
  change
    ((Finset.Icc (Complex.logarithmicPhasePoissonModeRangeLower t a) 0).card : ℤ) =
      0 + 1 - Complex.logarithmicPhasePoissonModeRangeLower t a
  exact Int.card_Icc_of_le hlower

theorem Complex.logarithmicPhasePoissonModeRange_lower_mem_of_lower_le_zero
    (t : ℝ) (a : ℤ)
    (hlower : Complex.logarithmicPhasePoissonModeRangeLower t a ≤ 0) :
    Complex.logarithmicPhasePoissonModeRangeLower t a ∈
      Complex.logarithmicPhasePoissonModeRange t a := by
  exact
    (Complex.mem_logarithmicPhasePoissonModeRange_iff t a
      (Complex.logarithmicPhasePoissonModeRangeLower t a)).mpr
      ⟨le_rfl, hlower⟩

theorem Complex.zero_mem_logarithmicPhasePoissonModeRange_of_lower_le_zero
    (t : ℝ) (a : ℤ)
    (hlower : Complex.logarithmicPhasePoissonModeRangeLower t a ≤ 0) :
    0 ∈ Complex.logarithmicPhasePoissonModeRange t a := by
  exact
    (Complex.mem_logarithmicPhasePoissonModeRange_iff t a 0).mpr
      ⟨hlower, le_rfl⟩

theorem Complex.integerBlockCutoffSupportLeftEndpoint_pos
    {a : ℤ} (ha : 1 ≤ a) :
    0 < Real.integerBlockCutoffSupportLeftEndpoint a := by
  have ha_real : (1 : ℝ) ≤ (a : ℝ) :=
    Int.cast_le.mpr ha
  have hthree_pos : (0 : ℝ) < 3 :=
    Nat.cast_pos.mpr (by exact Nat.succ_pos 2)
  have htwo_lt_three : (2 : ℝ) < 3 := by
    have hstep : (2 : ℝ) < 2 + 1 :=
      lt_add_of_pos_right 2 zero_lt_one
    have hnat : (2 + 1 : ℕ) = 3 :=
      rfl
    have hcast : (2 : ℝ) + 1 = 3 :=
      Eq.trans
        (Nat.cast_add 2 1).symm
        (Eq.trans
          (congrArg (fun n : ℕ => (n : ℝ)) hnat)
          Nat.cast_ofNat)
    exact hstep.trans_eq hcast
  have hmargin_lt_one : (2 / 3 : ℝ) < 1 :=
    (div_lt_one₀ hthree_pos).mpr htwo_lt_three
  have hmargin_lt_a : (2 / 3 : ℝ) < (a : ℝ) :=
    lt_of_lt_of_le hmargin_lt_one ha_real
  unfold Real.integerBlockCutoffSupportLeftEndpoint
  exact sub_pos.mpr hmargin_lt_a

theorem Complex.logarithmicPhasePoissonModeRangeLower_le_zero
    (t : ℝ) {a : ℤ} (ha : 1 ≤ a) :
    Complex.logarithmicPhasePoissonModeRangeLower t a ≤ 0 := by
  unfold Complex.logarithmicPhasePoissonModeRangeLower
  have hleft_pos : 0 < Real.integerBlockCutoffSupportLeftEndpoint a :=
    Complex.integerBlockCutoffSupportLeftEndpoint_pos ha
  have hneg_norm : -‖t‖ ≤ 0 :=
    neg_nonpos.mpr (norm_nonneg t)
  have hfirst_nonpos :
      -‖t‖ / Real.integerBlockCutoffSupportLeftEndpoint a ≤ 0 :=
    div_nonpos_of_nonpos_of_nonneg hneg_norm (le_of_lt hleft_pos)
  have hangular_pos : 0 < 2 * Real.pi :=
    mul_pos zero_lt_two Real.pi_pos
  have hquotient_nonpos :
      (-‖t‖ / Real.integerBlockCutoffSupportLeftEndpoint a) /
          (2 * Real.pi) ≤ 0 :=
    div_nonpos_of_nonpos_of_nonneg hfirst_nonpos (le_of_lt hangular_pos)
  exact
    Int.floor_le_iff.mpr
      (lt_of_le_of_lt hquotient_nonpos zero_lt_one)

theorem Complex.logarithmicPhasePoissonModeRange_card_cast_eq
    (t : ℝ) {a : ℤ} (ha : 1 ≤ a) :
    ((Complex.logarithmicPhasePoissonModeRange t a).card : ℤ) =
      1 - Complex.logarithmicPhasePoissonModeRangeLower t a := by
  exact
    Complex.logarithmicPhasePoissonModeRange_card_cast_eq_of_lower_le_one
      t a
      (le_trans
        (Complex.logarithmicPhasePoissonModeRangeLower_le_zero t ha)
        (show (0 : ℤ) ≤ 1 from zero_le_one))

end
end LFunctions
end Boundary
