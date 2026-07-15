import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalization.BoundaryEulerAbel.LogarithmicPhase.Curvature.RealPhaseLogarithmicPositiveTailArithmetic

/-!
# Exact positive-tail constant

This owner identifies the four positive-frequency reciprocal-series entries
with their exact common-denominator constant and inserts that constant into the
enhanced positive-tail budget.  It is independent of the far-negative ledger.
-/

namespace Boundary
namespace LFunctions

noncomputable section

private theorem realOfNat_add_eq_of_nat_eq
    (a b c : ℕ) (h : a + b = c) :
    (a : ℝ) + (b : ℝ) = (c : ℝ) :=
  Eq.trans (Nat.cast_add a b).symm
    (congrArg (fun n : ℕ => (n : ℝ)) h)

private theorem realOfNat_mul_eq_of_nat_eq
    (a b c : ℕ) (h : a * b = c) :
    (a : ℝ) * (b : ℝ) = (c : ℝ) :=
  Eq.trans (Nat.cast_mul a b).symm
    (congrArg (fun n : ℕ => (n : ℝ)) h)

def Complex.logarithmicPhaseExactPositiveTailConstant : ℝ :=
  61683 / 4608

theorem Complex.logarithmicPhaseExactPositiveTailConstant_nonneg :
    0 ≤ Complex.logarithmicPhaseExactPositiveTailConstant := by
  unfold Complex.logarithmicPhaseExactPositiveTailConstant
  exact div_nonneg (Nat.cast_nonneg 61683) (Nat.cast_nonneg 4608)

theorem Complex.logarithmicPhaseExactPositiveTailConstant_lt_fourteen_exact :
    Complex.logarithmicPhaseExactPositiveTailConstant < 14 := by
  unfold Complex.logarithmicPhaseExactPositiveTailConstant
  have hsum : (61683 : ℝ) + 2829 = 64512 :=
    realOfNat_add_eq_of_nat_eq 61683 2829 64512 rfl
  have hproduct : (14 : ℝ) * 4608 = 64512 :=
    realOfNat_mul_eq_of_nat_eq 14 4608 64512 rfl
  have hstrictRaw : (61683 : ℝ) < 61683 + 2829 :=
    lt_add_of_pos_right 61683
      (Nat.cast_pos.mpr (Nat.succ_pos 2828))
  have hstrict : (61683 : ℝ) < 64512 :=
    Eq.subst (motive := fun value : ℝ => 61683 < value)
      hsum hstrictRaw
  have htarget : (61683 : ℝ) < 14 * 4608 :=
    Eq.subst (motive := fun value : ℝ => 61683 < value)
      hproduct.symm hstrict
  exact (div_lt_iff₀
    (Nat.cast_pos.mpr (Nat.succ_pos 4607))).mpr htarget

theorem Complex.logarithmicPhasePositiveTailTotalConstant_eq_exact :
    Complex.logarithmicPhasePositiveTailTotalConstant =
      Complex.logarithmicPhaseExactPositiveTailConstant := by
  unfold Complex.logarithmicPhaseExactPositiveTailConstant
  unfold Complex.logarithmicPhasePositiveTailTotalConstant
  unfold Complex.logarithmicPhasePositiveTailSquareConstant
  unfold Complex.logarithmicPhasePositiveTailCurvatureConstant
  unfold Complex.logarithmicPhasePositiveTailThirdConstant
  unfold Complex.logarithmicPhasePositiveTailFourthConstant
  have hthreeDenominator : (3 : ℝ) ≠ 0 :=
    ne_of_gt (Nat.cast_pos.mpr (Nat.succ_pos 2))
  have hthirtyTwoDenominator : (32 : ℝ) ≠ 0 :=
    ne_of_gt (Nat.cast_pos.mpr (Nat.succ_pos 31))
  have hthreeEightyFourDenominator : (384 : ℝ) ≠ 0 :=
    ne_of_gt (Nat.cast_pos.mpr (Nat.succ_pos 383))
  have hfifteenThirtySixDenominator : (1536 : ℝ) ≠ 0 :=
    ne_of_gt (Nat.cast_pos.mpr (Nat.succ_pos 1535))
  have hdenominator : (4608 : ℝ) ≠ 0 :=
    ne_of_gt (Nat.cast_pos.mpr (Nat.succ_pos 4607))
  have hthree : (4 : ℝ) / 3 = 6144 / 4608 :=
    (div_eq_div_iff hthreeDenominator hdenominator).mpr
      ((realOfNat_mul_eq_of_nat_eq 4 4608 18432 rfl).trans
        (realOfNat_mul_eq_of_nat_eq 6144 3 18432 rfl).symm)
  have hthirtyTwo : (121 : ℝ) / 32 = 17424 / 4608 :=
    (div_eq_div_iff hthirtyTwoDenominator hdenominator).mpr
      ((realOfNat_mul_eq_of_nat_eq 121 4608 557568 rfl).trans
        (realOfNat_mul_eq_of_nat_eq 17424 32 557568 rfl).symm)
  have hthreeEightyFour : (847 : ℝ) / 384 = 10164 / 4608 :=
    (div_eq_div_iff hthreeEightyFourDenominator hdenominator).mpr
      ((realOfNat_mul_eq_of_nat_eq 847 4608 3902976 rfl).trans
        (realOfNat_mul_eq_of_nat_eq 10164 384 3902976 rfl).symm)
  have hfifteenThirtySix : (9317 : ℝ) / 1536 = 27951 / 4608 :=
    (div_eq_div_iff hfifteenThirtySixDenominator hdenominator).mpr
      ((realOfNat_mul_eq_of_nat_eq 9317 4608 42932736 rfl).trans
        (realOfNat_mul_eq_of_nat_eq 27951 1536 42932736 rfl).symm)
  have hreplace :
      (4 / 3 : ℝ) + 121 / 32 + 847 / 384 + 9317 / 1536 =
        6144 / 4608 + 17424 / 4608 + 10164 / 4608 +
          27951 / 4608 :=
    congrArg₂ (fun left right : ℝ => left + right)
      (congrArg₂ (fun left right : ℝ => left + right)
        (congrArg₂ (fun left right : ℝ => left + right)
          hthree hthirtyTwo)
        hthreeEightyFour)
      hfifteenThirtySix
  have hfirstSum :
      (6144 / 4608 : ℝ) + 17424 / 4608 =
        (6144 + 17424) / 4608 :=
    div_add_div_same 6144 17424 4608
  have hsecondSum :
      ((6144 + 17424 : ℝ) / 4608) + 10164 / 4608 =
        ((6144 + 17424) + 10164) / 4608 :=
    div_add_div_same (6144 + 17424) 10164 4608
  have hthirdSum :
      (((6144 + 17424 : ℝ) + 10164) / 4608) + 27951 / 4608 =
        (((6144 + 17424) + 10164) + 27951) / 4608 :=
    div_add_div_same ((6144 : ℝ) + 17424 + 10164) 27951 4608
  have h6144Add17424 : (6144 : ℝ) + 17424 = 23568 :=
    realOfNat_add_eq_of_nat_eq 6144 17424 23568 rfl
  have h23568Add10164 : (23568 : ℝ) + 10164 = 33732 :=
    realOfNat_add_eq_of_nat_eq 23568 10164 33732 rfl
  have h33732Add27951 : (33732 : ℝ) + 27951 = 61683 :=
    realOfNat_add_eq_of_nat_eq 33732 27951 61683 rfl
  have hnumerator :
      ((6144 + 17424 : ℝ) + 10164) + 27951 = 61683 :=
    Eq.trans
      (congrArg (fun value : ℝ => value + 27951)
        (Eq.trans
          (congrArg (fun value : ℝ => value + 10164) h6144Add17424)
          h23568Add10164))
      h33732Add27951
  have hnormalized :
      (6144 / 4608 : ℝ) + 17424 / 4608 + 10164 / 4608 +
          27951 / 4608 = 61683 / 4608 :=
    Eq.trans
      (congrArg (fun value : ℝ => value + 10164 / 4608 + 27951 / 4608)
        hfirstSum)
      (Eq.trans
        (congrArg (fun value : ℝ => value + 27951 / 4608) hsecondSum)
        (Eq.trans hthirdSum
          (congrArg (fun numerator : ℝ => numerator / 4608)
            hnumerator)))
  exact hreplace.trans hnormalized

theorem Complex.logarithmicPhaseEnhancedPositiveTailBudget_le_exactConstant
    (t : ℝ) (a b : ℕ)
    (ht : 1 ≤ ‖t‖)
    (hgeometry : Real.logarithmicPhaseLongBranchGeometry t a b) :
    Complex.logarithmicPhaseEnhancedPositiveTailBudget
        t (a : ℤ) (b : ℤ) ≤
      Complex.logarithmicPhaseExactPositiveTailConstant := by
  have ha := Real.logarithmicPhaseLongBranchGeometry_first_pos hgeometry
  have hab := Real.logarithmicPhaseLongBranchGeometry_order hgeometry
  have hseries :=
    Complex.logarithmicPhaseEnhancedPositiveTailBudget_le_seriesBudget
      t (a : ℤ) (b : ℤ)
      (Int.ofNat_le.mpr ha) (Int.ofNat_le.mpr hab)
  have hconstant :=
    Complex.logarithmicPhaseEnhancedPositiveSeriesBudget_le_constant
      t a b ht hgeometry
  exact le_trans hseries
    (le_trans hconstant
      (le_of_eq
        Complex.logarithmicPhasePositiveTailTotalConstant_eq_exact))

end

end LFunctions
end Boundary
