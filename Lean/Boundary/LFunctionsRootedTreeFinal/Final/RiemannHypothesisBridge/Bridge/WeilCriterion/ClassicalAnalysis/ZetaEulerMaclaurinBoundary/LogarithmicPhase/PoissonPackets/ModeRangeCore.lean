import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ClassicalAnalysis.ZetaEulerMaclaurinBoundary.LogarithmicPhase.PoissonPackets.Support

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

theorem Complex.integerBlockCutoffSupportLeftEndpoint_pos
    {a : ℤ} (ha : 1 ≤ a) :
    0 < Real.integerBlockCutoffSupportLeftEndpoint a := by
  have ha_cast : ((1 : ℤ) : ℝ) = 1 := Int.cast_one
  have ha_real : (1 : ℝ) ≤ (a : ℝ) :=
    ha_cast ▸ (Int.cast_le.mpr ha)
  have hthree_pos : (0 : ℝ) < 3 :=
    Nat.cast_pos.mpr (by exact Nat.succ_pos 2)
  have htwo_lt_three : (2 : ℝ) < 3 := by
    have hstep : (2 : ℝ) < 2 + 1 :=
      lt_add_of_pos_right 2 zero_lt_one
    have hnat : (2 + 1 : ℕ) = 3 := rfl
    have hcastNat : ((2 : ℕ) : ℝ) + ((1 : ℕ) : ℝ) = ((3 : ℕ) : ℝ) :=
      Eq.trans
        (Nat.cast_add 2 1).symm
        (Eq.trans
          (congrArg (fun n : ℕ => (n : ℝ)) hnat)
          Nat.cast_ofNat)
    have htwo : ((2 : ℕ) : ℝ) = (2 : ℝ) := Nat.cast_ofNat
    have hone : ((1 : ℕ) : ℝ) = (1 : ℝ) := Nat.cast_one
    have hcast : (2 : ℝ) + 1 = 3 := by
      exact (congrArg₂ (fun x y : ℝ => x + y) htwo.symm hone.symm).trans
        (hcastNat.trans Nat.cast_ofNat)
    exact hstep.trans_eq hcast
  have hmargin_lt_one : (2 / 3 : ℝ) < 1 :=
    (div_lt_one hthree_pos).mpr htwo_lt_three
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
  exact Eq.subst
    (motive := fun value : ℤ =>
      ⌊(-‖t‖ / Real.integerBlockCutoffSupportLeftEndpoint a) /
        (2 * Real.pi)⌋ ≤ value)
    Int.floor_zero
    (Int.floor_mono hquotient_nonpos)

theorem Complex.zero_mem_logarithmicPhasePoissonModeRange_of_lower_le_zero
    (t : ℝ) (a : ℤ)
    (hlower : Complex.logarithmicPhasePoissonModeRangeLower t a ≤ 0) :
    0 ∈ Complex.logarithmicPhasePoissonModeRange t a := by
  exact (Complex.mem_logarithmicPhasePoissonModeRange_iff t a 0).mpr
    ⟨hlower, le_rfl⟩

end
end LFunctions
end Boundary
