import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ClassicalAnalysis.OscillatorySums.ShiftedReciprocalPowerSpecializations

/-!
# Arithmetic bounds for shifted reciprocal-power budgets

This owner supplies monotonicity and denominator estimates for the closed
integral budgets.  It keeps the shift available when a coefficient must be
absorbed, while also exposing shift-free bounds for constant terms.
-/

namespace Boundary
namespace LFunctions

noncomputable section

theorem Real.shiftedReciprocalPowerIntegralBudget_nonneg
    (A c p : ℝ)
    (hA : 0 ≤ A) (hc : 0 < c) (hp : 1 < p) :
    0 ≤ Real.shiftedReciprocalPowerIntegralBudget A c p := by
  unfold Real.shiftedReciprocalPowerIntegralBudget
  have hbase : 0 < A + c := add_pos_of_nonneg_of_pos hA hc
  have hnumerator : 0 ≤ (A + c) ^ (1 - p) :=
    Real.rpow_nonneg hbase.le (1 - p)
  have hfactor : 0 < p - 1 := sub_pos.mpr hp
  have hdenominator : 0 < c * (p - 1) := mul_pos hc hfactor
  exact div_nonneg hnumerator hdenominator.le

theorem Real.shiftedReciprocalPowerIntegralBudget_shift_antitone
    {A₁ A₂ c p : ℝ}
    (hA₁ : 0 ≤ A₁) (hA : A₁ ≤ A₂)
    (hc : 0 < c) (hp : 1 < p) :
    Real.shiftedReciprocalPowerIntegralBudget A₂ c p ≤
      Real.shiftedReciprocalPowerIntegralBudget A₁ c p := by
  unfold Real.shiftedReciprocalPowerIntegralBudget
  have hbase₁ : 0 < A₁ + c := add_pos_of_nonneg_of_pos hA₁ hc
  have hbaseOrder : A₁ + c ≤ A₂ + c := add_le_add_right hA c
  have hexponent : 1 - p ≤ 0 := (sub_neg.mpr hp).le
  have hrpow := Real.rpow_le_rpow_of_nonpos
    hbase₁ hbaseOrder hexponent
  have hfactor : 0 < p - 1 := sub_pos.mpr hp
  have hdenominator : 0 < c * (p - 1) := mul_pos hc hfactor
  exact div_le_div_of_nonneg_right hrpow hdenominator.le

theorem Real.shiftedReciprocalPowerIntegralBudget_le_zeroShift
    (A c p : ℝ)
    (hA : 0 ≤ A) (hc : 0 < c) (hp : 1 < p) :
    Real.shiftedReciprocalPowerIntegralBudget A c p ≤
      Real.shiftedReciprocalPowerIntegralBudget 0 c p := by
  exact Real.shiftedReciprocalPowerIntegralBudget_shift_antitone
    (A₁ := 0) (A₂ := A) (c := c) (p := p)
    (le_refl 0) hA hc hp

theorem Real.shiftedReciprocalPowerKernel_one_shift_antitone
    {A₁ A₂ c p : ℝ}
    (hA₁ : 0 ≤ A₁) (hA : A₁ ≤ A₂)
    (hc : 0 < c) (hp : 0 ≤ p) :
    Real.shiftedReciprocalPowerKernel A₂ c p 1 ≤
      Real.shiftedReciprocalPowerKernel A₁ c p 1 := by
  unfold Real.shiftedReciprocalPowerKernel
  have hbase₁ : 0 < A₁ + c * 1 :=
    add_pos_of_nonneg_of_pos hA₁ (mul_pos hc zero_lt_one)
  have hbaseOrder : A₁ + c * 1 ≤ A₂ + c * 1 :=
    add_le_add_right hA (c * 1)
  have hpowerOrder : (A₁ + c * 1) ^ p ≤ (A₂ + c * 1) ^ p :=
    Real.rpow_le_rpow hbase₁.le hbaseOrder hp
  have hpowerPos : 0 < (A₁ + c * 1) ^ p :=
    Real.rpow_pos_of_pos hbase₁ p
  exact one_div_le_one_div_of_le hpowerPos hpowerOrder

theorem Real.shiftedReciprocalPowerSeriesBudget_shift_antitone
    {A₁ A₂ c p : ℝ}
    (hA₁ : 0 ≤ A₁) (hA : A₁ ≤ A₂)
    (hc : 0 < c) (hp : 1 < p) :
    Real.shiftedReciprocalPowerSeriesBudget A₂ c p ≤
      Real.shiftedReciprocalPowerSeriesBudget A₁ c p := by
  unfold Real.shiftedReciprocalPowerSeriesBudget
  have hfirst := Real.shiftedReciprocalPowerKernel_one_shift_antitone
    hA₁ hA hc (le_trans zero_lt_one.le hp.le)
  have hintegral :=
    Real.shiftedReciprocalPowerIntegralBudget_shift_antitone
      hA₁ hA hc hp
  exact add_le_add hfirst hintegral

theorem Real.shiftedReciprocalPowerSeriesBudget_le_zeroShift
    (A c p : ℝ)
    (hA : 0 ≤ A) (hc : 0 < c) (hp : 1 < p) :
    Real.shiftedReciprocalPowerSeriesBudget A c p ≤
      Real.shiftedReciprocalPowerSeriesBudget 0 c p := by
  exact Real.shiftedReciprocalPowerSeriesBudget_shift_antitone
    (A₁ := 0) (A₂ := A) (c := c) (p := p)
    (le_refl 0) hA hc hp

theorem Real.shiftedReciprocalPowerIntegralBudget_coefficient_mono
    (A c p C : ℝ)
    (hA : 0 ≤ A) (hc : 0 < c) (hp : 1 < p)
    (hC : 0 ≤ C) :
    C * Real.shiftedReciprocalPowerIntegralBudget A c p ≤
      C * Real.shiftedReciprocalPowerIntegralBudget 0 c p := by
  exact mul_le_mul_of_nonneg_left
    (Real.shiftedReciprocalPowerIntegralBudget_le_zeroShift
      A c p hA hc hp) hC

theorem Real.shiftedReciprocalPowerIntegralBudget_mul_shift_power_le
    (A c p : ℝ)
    (hA : 0 < A) (hc : 0 < c) (hp : 1 < p) :
    A ^ (p - 1) * Real.shiftedReciprocalPowerIntegralBudget A c p ≤
      1 / (c * (p - 1)) := by
  unfold Real.shiftedReciprocalPowerIntegralBudget
  have hAle : A ≤ A + c := le_add_of_nonneg_right hc.le
  have hexponentPos : 0 < p - 1 := sub_pos.mpr hp
  have hreciprocal := Real.rpow_le_rpow_of_nonpos
    hA hAle (sub_neg.mpr hp).le
  have hproductLe :
      A ^ (p - 1) * (A + c) ^ (1 - p) ≤ 1 := by
    have hmul := mul_le_mul_of_nonneg_left hreciprocal
      (Real.rpow_nonneg hA.le (p - 1))
    have hcancel : A ^ (p - 1) * A ^ (1 - p) = 1 := by
      have hsum : (p - 1) + (1 - p) = 0 := by
        exact Eq.trans
          (congrArg₂ (fun left right : ℝ => left + right)
            (sub_eq_add_neg p 1) (sub_eq_add_neg 1 p))
          (Eq.trans
            (add_assoc p (-1) (1 + -p))
            (Eq.trans
              (congrArg (fun value : ℝ => p + value)
                (add_assoc (-1) 1 (-p)).symm)
              (Eq.trans
                (congrArg (fun value : ℝ => p + (value + -p))
                  (neg_add_cancel 1))
                (Eq.trans
                  (congrArg (fun value : ℝ => p + value) (zero_add (-p)))
                  (add_neg_cancel p)))))
      have hpow := (Real.rpow_add hA (p - 1) (1 - p)).symm
      exact Eq.trans hpow
        (Eq.trans (congrArg (fun exponent : ℝ => A ^ exponent) hsum)
          (Real.rpow_zero A))
    exact le_trans hmul (le_of_eq hcancel)
  have hdenominator : 0 < c * (p - 1) := mul_pos hc hexponentPos
  have hdivide := div_le_div_of_nonneg_right hproductLe hdenominator.le
  have hleft :
      A ^ (p - 1) *
          ((A + c) ^ (1 - p) / (c * (p - 1))) =
        (A ^ (p - 1) * (A + c) ^ (1 - p)) /
          (c * (p - 1)) :=
    (mul_div_assoc _ _ _).symm
  exact le_trans (le_of_eq hleft) hdivide

theorem Real.shiftedInverseSquareBudget_nonneg
    (A c : ℝ) (hA : 0 ≤ A) (hc : 0 < c) :
    0 ≤ Real.shiftedInverseSquareBudget A c := by
  unfold Real.shiftedInverseSquareBudget
  exact Real.shiftedReciprocalPowerIntegralBudget_nonneg
    A c 2 hA hc (Nat.one_lt_ofNat)

theorem Real.shiftedInverseCubeBudget_nonneg
    (A c : ℝ) (hA : 0 ≤ A) (hc : 0 < c) :
    0 ≤ Real.shiftedInverseCubeBudget A c := by
  unfold Real.shiftedInverseCubeBudget
  exact Real.shiftedReciprocalPowerIntegralBudget_nonneg
    A c 3 hA hc (Nat.one_lt_ofNat)

theorem Real.shiftedInverseFourthBudget_nonneg
    (A c : ℝ) (hA : 0 ≤ A) (hc : 0 < c) :
    0 ≤ Real.shiftedInverseFourthBudget A c := by
  unfold Real.shiftedInverseFourthBudget
  exact Real.shiftedReciprocalPowerIntegralBudget_nonneg
    A c 4 hA hc (Nat.one_lt_ofNat)

theorem Real.shiftedInverseSquareBudget_le_zeroShift
    (A c : ℝ) (hA : 0 ≤ A) (hc : 0 < c) :
    Real.shiftedInverseSquareBudget A c ≤
      Real.shiftedInverseSquareBudget 0 c := by
  unfold Real.shiftedInverseSquareBudget
  exact Real.shiftedReciprocalPowerIntegralBudget_le_zeroShift
    A c 2 hA hc (Nat.one_lt_ofNat)

theorem Real.shiftedInverseCubeBudget_le_zeroShift
    (A c : ℝ) (hA : 0 ≤ A) (hc : 0 < c) :
    Real.shiftedInverseCubeBudget A c ≤
      Real.shiftedInverseCubeBudget 0 c := by
  unfold Real.shiftedInverseCubeBudget
  exact Real.shiftedReciprocalPowerIntegralBudget_le_zeroShift
    A c 3 hA hc (Nat.one_lt_ofNat)

theorem Real.shiftedInverseFourthBudget_le_zeroShift
    (A c : ℝ) (hA : 0 ≤ A) (hc : 0 < c) :
    Real.shiftedInverseFourthBudget A c ≤
      Real.shiftedInverseFourthBudget 0 c := by
  unfold Real.shiftedInverseFourthBudget
  exact Real.shiftedReciprocalPowerIntegralBudget_le_zeroShift
    A c 4 hA hc (Nat.one_lt_ofNat)

theorem Real.shiftedReciprocalPacketBudget_nonneg
    (A c C₂ C₃ D₃ C₄ : ℝ)
    (hA : 0 ≤ A) (hc : 0 < c)
    (hC₂ : 0 ≤ C₂) (hC₃ : 0 ≤ C₃)
    (hD₃ : 0 ≤ D₃) (hC₄ : 0 ≤ C₄) :
    0 ≤ Real.shiftedReciprocalPacketBudget A c C₂ C₃ D₃ C₄ := by
  unfold Real.shiftedReciprocalPacketBudget
  have htwo := mul_nonneg hC₂
    (Real.shiftedInverseSquareBudget_nonneg A c hA hc)
  have hthree := mul_nonneg hC₃
    (Real.shiftedInverseCubeBudget_nonneg A c hA hc)
  have hdthree := mul_nonneg hD₃
    (Real.shiftedInverseCubeBudget_nonneg A c hA hc)
  have hfour := mul_nonneg hC₄
    (Real.shiftedInverseFourthBudget_nonneg A c hA hc)
  exact add_nonneg (add_nonneg (add_nonneg htwo hthree) hdthree) hfour

theorem Real.shiftedReciprocalPacketBudget_shift_antitone
    {A₁ A₂ c C₂ C₃ D₃ C₄ : ℝ}
    (hA₁ : 0 ≤ A₁) (hA : A₁ ≤ A₂) (hc : 0 < c)
    (hC₂ : 0 ≤ C₂) (hC₃ : 0 ≤ C₃)
    (hD₃ : 0 ≤ D₃) (hC₄ : 0 ≤ C₄) :
    Real.shiftedReciprocalPacketBudget A₂ c C₂ C₃ D₃ C₄ ≤
      Real.shiftedReciprocalPacketBudget A₁ c C₂ C₃ D₃ C₄ := by
  unfold Real.shiftedReciprocalPacketBudget
  have htwo := mul_le_mul_of_nonneg_left
    (Real.shiftedReciprocalPowerIntegralBudget_shift_antitone
      hA₁ hA hc (Nat.one_lt_ofNat : (1 : ℝ) < 2)) hC₂
  have hthree := mul_le_mul_of_nonneg_left
    (Real.shiftedReciprocalPowerIntegralBudget_shift_antitone
      hA₁ hA hc (Nat.one_lt_ofNat : (1 : ℝ) < 3)) hC₃
  have hdthree := mul_le_mul_of_nonneg_left
    (Real.shiftedReciprocalPowerIntegralBudget_shift_antitone
      hA₁ hA hc (Nat.one_lt_ofNat : (1 : ℝ) < 3)) hD₃
  have hfour := mul_le_mul_of_nonneg_left
    (Real.shiftedReciprocalPowerIntegralBudget_shift_antitone
      hA₁ hA hc (Nat.one_lt_ofNat : (1 : ℝ) < 4)) hC₄
  exact add_le_add (add_le_add (add_le_add htwo hthree) hdthree) hfour

end
end LFunctions
end Boundary
