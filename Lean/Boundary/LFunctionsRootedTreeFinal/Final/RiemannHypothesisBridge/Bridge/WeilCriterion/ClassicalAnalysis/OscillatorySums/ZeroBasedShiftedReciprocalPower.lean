import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ClassicalAnalysis.OscillatorySums.FiniteShiftedReciprocalEmbedding

/-!
# Zero-based shifted reciprocal-power series

Frequency gaps naturally indexed from their nearest lattice point have the
form `A + c n`, including the residual term `A` at `n = 0`.  The existing
shifted-series owner starts at `A + c`.  This file separates the zero term and
reuses that owner for the remaining series.
-/

namespace Boundary
namespace LFunctions

noncomputable section

def Real.zeroBasedShiftedInverseSquareTerm
    (A c : ℝ) (n : ℕ) : ℝ :=
  1 / (A + c * (n : ℝ)) ^ 2

def Real.zeroBasedShiftedInverseCubeTerm
    (A c : ℝ) (n : ℕ) : ℝ :=
  1 / (A + c * (n : ℝ)) ^ 3

def Real.zeroBasedShiftedInverseFourthTerm
    (A c : ℝ) (n : ℕ) : ℝ :=
  1 / (A + c * (n : ℝ)) ^ 4

def Real.zeroBasedShiftedInverseSquareBudget
    (A c : ℝ) : ℝ :=
  1 / A ^ 2 + Real.shiftedInverseSquareSeriesBudget A c

def Real.zeroBasedShiftedInverseCubeBudget
    (A c : ℝ) : ℝ :=
  1 / A ^ 3 + Real.shiftedInverseCubeSeriesBudget A c

def Real.zeroBasedShiftedInverseFourthBudget
    (A c : ℝ) : ℝ :=
  1 / A ^ 4 + Real.shiftedInverseFourthSeriesBudget A c

theorem Real.shiftedReciprocalPowerSeriesBudget_nonneg_of_nonneg
    (A c p : ℝ) (hA : 0 ≤ A) (hc : 0 ≤ c) (hp : 1 ≤ p) :
    0 ≤ Real.shiftedReciprocalPowerSeriesBudget A c p := by
  have hfirst := Real.shiftedReciprocalPowerKernel_nonneg
    A c p 1 hA hc zero_le_one
  have hbase : 0 ≤ A + c := add_nonneg hA hc
  have hnumerator : 0 ≤ (A + c) ^ (1 - p) :=
    Real.rpow_nonneg hbase (1 - p)
  have hfactor : 0 ≤ p - 1 := sub_nonneg.mpr hp
  have hdenominator : 0 ≤ c * (p - 1) := mul_nonneg hc hfactor
  have hintegral :
      0 ≤ (A + c) ^ (1 - p) / (c * (p - 1)) :=
    div_nonneg hnumerator hdenominator
  unfold Real.shiftedReciprocalPowerSeriesBudget
  unfold Real.shiftedReciprocalPowerIntegralBudget
  exact add_nonneg hfirst hintegral

theorem Real.zeroBasedShiftedInverseSquareBudget_nonneg
    (A c : ℝ) (hA : 0 ≤ A) (hc : 0 ≤ c) :
    0 ≤ Real.zeroBasedShiftedInverseSquareBudget A c := by
  unfold Real.zeroBasedShiftedInverseSquareBudget
  have hbase : 0 ≤ 1 / A ^ 2 :=
    div_nonneg zero_le_one (pow_nonneg hA 2)
  have htail := Real.shiftedReciprocalPowerSeriesBudget_nonneg_of_nonneg
    A c 2 hA hc (show (1 : ℝ) ≤ 2 from one_le_two)
  have hbudget :
      Real.shiftedInverseSquareSeriesBudget A c =
        Real.shiftedReciprocalPowerSeriesBudget A c 2 := by
    unfold Real.shiftedInverseSquareSeriesBudget
    unfold Real.shiftedInverseSquareBudget
    unfold Real.shiftedReciprocalPowerSeriesBudget
    exact congrArg₂ (fun first tail : ℝ => first + tail)
      (Eq.trans
        (Real.shiftedInverseSquareTerm_eq_seriesTerm A c 0)
        (Real.shiftedReciprocalPowerKernel_one_eq_seriesTerm_zero A c 2).symm)
      rfl
  exact add_nonneg hbase (Eq.subst hbudget.symm htail)

theorem Real.zeroBasedShiftedInverseCubeBudget_nonneg
    (A c : ℝ) (hA : 0 ≤ A) (hc : 0 ≤ c) :
    0 ≤ Real.zeroBasedShiftedInverseCubeBudget A c := by
  unfold Real.zeroBasedShiftedInverseCubeBudget
  have hbase : 0 ≤ 1 / A ^ 3 :=
    div_nonneg zero_le_one (pow_nonneg hA 3)
  have htail := Real.shiftedReciprocalPowerSeriesBudget_nonneg_of_nonneg
    A c 3 hA hc (Nat.one_le_ofNat : (1 : ℝ) ≤ 3)
  have hbudget :
      Real.shiftedInverseCubeSeriesBudget A c =
        Real.shiftedReciprocalPowerSeriesBudget A c 3 := by
    unfold Real.shiftedInverseCubeSeriesBudget
    unfold Real.shiftedInverseCubeBudget
    unfold Real.shiftedReciprocalPowerSeriesBudget
    exact congrArg₂ (fun first tail : ℝ => first + tail)
      (Eq.trans
        (Real.shiftedInverseCubeTerm_eq_seriesTerm A c 0)
        (Real.shiftedReciprocalPowerKernel_one_eq_seriesTerm_zero A c 3).symm)
      rfl
  exact add_nonneg hbase (Eq.subst hbudget.symm htail)

theorem Real.zeroBasedShiftedInverseFourthBudget_nonneg
    (A c : ℝ) (hA : 0 ≤ A) (hc : 0 ≤ c) :
    0 ≤ Real.zeroBasedShiftedInverseFourthBudget A c := by
  unfold Real.zeroBasedShiftedInverseFourthBudget
  have hbase : 0 ≤ 1 / A ^ 4 :=
    div_nonneg zero_le_one (pow_nonneg hA 4)
  have htail := Real.shiftedReciprocalPowerSeriesBudget_nonneg_of_nonneg
    A c 4 hA hc (Nat.one_le_ofNat : (1 : ℝ) ≤ 4)
  have hbudget :
      Real.shiftedInverseFourthSeriesBudget A c =
        Real.shiftedReciprocalPowerSeriesBudget A c 4 := by
    unfold Real.shiftedInverseFourthSeriesBudget
    unfold Real.shiftedInverseFourthBudget
    unfold Real.shiftedReciprocalPowerSeriesBudget
    exact congrArg₂ (fun first tail : ℝ => first + tail)
      (Eq.trans
        (Real.shiftedInverseFourthTerm_eq_seriesTerm A c 0)
        (Real.shiftedReciprocalPowerKernel_one_eq_seriesTerm_zero A c 4).symm)
      rfl
  exact add_nonneg hbase (Eq.subst hbudget.symm htail)

theorem Finset.sum_const_mul_real
    {α : Type*} (s : Finset α) (c : ℝ) (f : α → ℝ) :
    (∑ x in s, c * f x) = c * ∑ x in s, f x := by
  have hinner :
      (∑ x in s, c * f x) = c * ∑ x in s, f x :=
    (Finset.mul_sum s f c).symm
  exact hinner

theorem Finset.sum_four_real
    {α : Type*} (s : Finset α) (f₁ f₂ f₃ f₄ : α → ℝ) :
    (∑ x in s, (f₁ x + f₂ x + f₃ x + f₄ x)) =
      (∑ x in s, f₁ x) +
      (∑ x in s, f₂ x) +
      (∑ x in s, f₃ x) +
      (∑ x in s, f₄ x) := by
  have hfirst := Finset.sum_add_distrib
    (s := s) (f := fun x => f₁ x + f₂ x + f₃ x) (g := f₄)
  have hsecond := Finset.sum_add_distrib
    (s := s) (f := fun x => f₁ x + f₂ x) (g := f₃)
  have hthird := Finset.sum_add_distrib (s := s) (f := f₁) (g := f₂)
  exact Eq.trans hfirst
    (Eq.trans
      (congrArg (fun value : ℝ => value + ∑ x in s, f₄ x) hsecond)
      (congrArg
        (fun value : ℝ =>
          value + ∑ x in s, f₃ x + ∑ x in s, f₄ x)
        hthird))

theorem Real.zeroBasedShiftedInverseSquareTerm_zero
    (A c : ℝ) :
    Real.zeroBasedShiftedInverseSquareTerm A c 0 = 1 / A ^ 2 := by
  unfold Real.zeroBasedShiftedInverseSquareTerm
  have hcast : ((0 : ℕ) : ℝ) = 0 := Nat.cast_zero
  have hmul : c * (0 : ℝ) = 0 := mul_zero c
  have hadd : A + c * ((0 : ℕ) : ℝ) = A := Eq.trans
    (congrArg (fun value : ℝ => A + c * value) hcast)
    (Eq.trans (congrArg (fun value : ℝ => A + value) hmul) (add_zero A))
  exact congrArg (fun value : ℝ => 1 / value ^ 2)
    hadd

theorem Real.zeroBasedShiftedInverseCubeTerm_zero
    (A c : ℝ) :
    Real.zeroBasedShiftedInverseCubeTerm A c 0 = 1 / A ^ 3 := by
  unfold Real.zeroBasedShiftedInverseCubeTerm
  have hcast : ((0 : ℕ) : ℝ) = 0 := Nat.cast_zero
  have hmul : c * (0 : ℝ) = 0 := mul_zero c
  have hadd : A + c * ((0 : ℕ) : ℝ) = A := Eq.trans
    (congrArg (fun value : ℝ => A + c * value) hcast)
    (Eq.trans (congrArg (fun value : ℝ => A + value) hmul) (add_zero A))
  exact congrArg (fun value : ℝ => 1 / value ^ 3)
    hadd

theorem Real.zeroBasedShiftedInverseFourthTerm_zero
    (A c : ℝ) :
    Real.zeroBasedShiftedInverseFourthTerm A c 0 = 1 / A ^ 4 := by
  unfold Real.zeroBasedShiftedInverseFourthTerm
  have hcast : ((0 : ℕ) : ℝ) = 0 := Nat.cast_zero
  have hmul : c * (0 : ℝ) = 0 := mul_zero c
  have hadd : A + c * ((0 : ℕ) : ℝ) = A := Eq.trans
    (congrArg (fun value : ℝ => A + c * value) hcast)
    (Eq.trans (congrArg (fun value : ℝ => A + value) hmul) (add_zero A))
  exact congrArg (fun value : ℝ => 1 / value ^ 4)
    hadd

theorem Real.zeroBasedShiftedInverseSquareTerm_succ
    (A c : ℝ) (n : ℕ) :
    Real.zeroBasedShiftedInverseSquareTerm A c (n + 1) =
      Real.shiftedInverseSquareTerm A c n := by
  unfold Real.zeroBasedShiftedInverseSquareTerm
  unfold Real.shiftedInverseSquareTerm
  have hcast : (((n + 1 : ℕ) : ℝ)) = (n : ℝ) + 1 :=
    Eq.trans (Nat.cast_add n 1)
      (congrArg (fun value : ℝ => (n : ℝ) + value) Nat.cast_one)
  exact congrArg (fun value : ℝ => 1 / (A + c * value) ^ 2) hcast

theorem Real.zeroBasedShiftedInverseCubeTerm_succ
    (A c : ℝ) (n : ℕ) :
    Real.zeroBasedShiftedInverseCubeTerm A c (n + 1) =
      Real.shiftedInverseCubeTerm A c n := by
  unfold Real.zeroBasedShiftedInverseCubeTerm
  unfold Real.shiftedInverseCubeTerm
  have hcast : (((n + 1 : ℕ) : ℝ)) = (n : ℝ) + 1 :=
    Eq.trans (Nat.cast_add n 1)
      (congrArg (fun value : ℝ => (n : ℝ) + value) Nat.cast_one)
  exact congrArg (fun value : ℝ => 1 / (A + c * value) ^ 3) hcast

theorem Real.zeroBasedShiftedInverseFourthTerm_succ
    (A c : ℝ) (n : ℕ) :
    Real.zeroBasedShiftedInverseFourthTerm A c (n + 1) =
      Real.shiftedInverseFourthTerm A c n := by
  unfold Real.zeroBasedShiftedInverseFourthTerm
  unfold Real.shiftedInverseFourthTerm
  have hcast : (((n + 1 : ℕ) : ℝ)) = (n : ℝ) + 1 :=
    Eq.trans (Nat.cast_add n 1)
      (congrArg (fun value : ℝ => (n : ℝ) + value) Nat.cast_one)
  exact congrArg (fun value : ℝ => 1 / (A + c * value) ^ 4) hcast

theorem Real.summable_zeroBasedShiftedInverseSquareTerm
    (A c : ℝ) (hA : 0 < A) (hc : 0 < c) :
    Summable (Real.zeroBasedShiftedInverseSquareTerm A c) := by
  have htail := Real.summable_shiftedInverseSquareTerm A c hA.le hc
  have hsucc : Summable
      (fun n : ℕ => Real.zeroBasedShiftedInverseSquareTerm A c (n + 1)) :=
    Eq.subst
      (motive := fun function : ℕ → ℝ => Summable function)
      (funext (fun n => Real.zeroBasedShiftedInverseSquareTerm_succ A c n)).symm
      htail
  exact (summable_nat_add_iff
    (f := Real.zeroBasedShiftedInverseSquareTerm A c)
    (G := ℝ) 1).mp hsucc

theorem Real.summable_zeroBasedShiftedInverseCubeTerm
    (A c : ℝ) (hA : 0 < A) (hc : 0 < c) :
    Summable (Real.zeroBasedShiftedInverseCubeTerm A c) := by
  have htail := Real.summable_shiftedInverseCubeTerm A c hA.le hc
  have hsucc : Summable
      (fun n : ℕ => Real.zeroBasedShiftedInverseCubeTerm A c (n + 1)) :=
    Eq.subst
      (motive := fun function : ℕ → ℝ => Summable function)
      (funext (fun n => Real.zeroBasedShiftedInverseCubeTerm_succ A c n)).symm
      htail
  exact (summable_nat_add_iff
    (f := Real.zeroBasedShiftedInverseCubeTerm A c)
    (G := ℝ) 1).mp hsucc

theorem Real.summable_zeroBasedShiftedInverseFourthTerm
    (A c : ℝ) (hA : 0 < A) (hc : 0 < c) :
    Summable (Real.zeroBasedShiftedInverseFourthTerm A c) := by
  have htail := Real.summable_shiftedInverseFourthTerm A c hA.le hc
  have hsucc : Summable
      (fun n : ℕ => Real.zeroBasedShiftedInverseFourthTerm A c (n + 1)) :=
    Eq.subst
      (motive := fun function : ℕ → ℝ => Summable function)
      (funext (fun n => Real.zeroBasedShiftedInverseFourthTerm_succ A c n)).symm
      htail
  exact (summable_nat_add_iff
    (f := Real.zeroBasedShiftedInverseFourthTerm A c)
    (G := ℝ) 1).mp hsucc

theorem Real.tsum_zeroBasedShiftedInverseSquareTerm_eq_zero_add_tail
    (A c : ℝ) (hA : 0 < A) (hc : 0 < c) :
    (∑' n : ℕ, Real.zeroBasedShiftedInverseSquareTerm A c n) =
      1 / A ^ 2 + ∑' n : ℕ, Real.shiftedInverseSquareTerm A c n := by
  have hsum := tsum_eq_zero_add
    (Real.summable_zeroBasedShiftedInverseSquareTerm A c hA hc)
  exact Eq.trans hsum
    (congrArg₂ (fun first second : ℝ => first + second)
      (Real.zeroBasedShiftedInverseSquareTerm_zero A c)
      (tsum_congr (fun n =>
        Real.zeroBasedShiftedInverseSquareTerm_succ A c n)))

theorem Real.tsum_zeroBasedShiftedInverseCubeTerm_eq_zero_add_tail
    (A c : ℝ) (hA : 0 < A) (hc : 0 < c) :
    (∑' n : ℕ, Real.zeroBasedShiftedInverseCubeTerm A c n) =
      1 / A ^ 3 + ∑' n : ℕ, Real.shiftedInverseCubeTerm A c n := by
  have hsum := tsum_eq_zero_add
    (Real.summable_zeroBasedShiftedInverseCubeTerm A c hA hc)
  exact Eq.trans hsum
    (congrArg₂ (fun first second : ℝ => first + second)
      (Real.zeroBasedShiftedInverseCubeTerm_zero A c)
      (tsum_congr (fun n =>
        Real.zeroBasedShiftedInverseCubeTerm_succ A c n)))

theorem Real.tsum_zeroBasedShiftedInverseFourthTerm_eq_zero_add_tail
    (A c : ℝ) (hA : 0 < A) (hc : 0 < c) :
    (∑' n : ℕ, Real.zeroBasedShiftedInverseFourthTerm A c n) =
      1 / A ^ 4 + ∑' n : ℕ, Real.shiftedInverseFourthTerm A c n := by
  have hsum := tsum_eq_zero_add
    (Real.summable_zeroBasedShiftedInverseFourthTerm A c hA hc)
  exact Eq.trans hsum
    (congrArg₂ (fun first second : ℝ => first + second)
      (Real.zeroBasedShiftedInverseFourthTerm_zero A c)
      (tsum_congr (fun n =>
        Real.zeroBasedShiftedInverseFourthTerm_succ A c n)))

theorem Real.tsum_zeroBasedShiftedInverseSquareTerm_le_budget
    (A c : ℝ) (hA : 0 < A) (hc : 0 < c) :
    (∑' n : ℕ, Real.zeroBasedShiftedInverseSquareTerm A c n) ≤
      Real.zeroBasedShiftedInverseSquareBudget A c := by
  have heq := Real.tsum_zeroBasedShiftedInverseSquareTerm_eq_zero_add_tail
    A c hA hc
  have htail := Real.tsum_shiftedInverseSquareTerm_le A c hA.le hc
  unfold Real.zeroBasedShiftedInverseSquareBudget
  exact Eq.subst (motive := fun value : ℝ => value ≤
      1 / A ^ 2 + Real.shiftedInverseSquareSeriesBudget A c)
    heq.symm (add_le_add_left htail (1 / A ^ 2))

theorem Real.tsum_zeroBasedShiftedInverseCubeTerm_le_budget
    (A c : ℝ) (hA : 0 < A) (hc : 0 < c) :
    (∑' n : ℕ, Real.zeroBasedShiftedInverseCubeTerm A c n) ≤
      Real.zeroBasedShiftedInverseCubeBudget A c := by
  have heq := Real.tsum_zeroBasedShiftedInverseCubeTerm_eq_zero_add_tail
    A c hA hc
  have htail := Real.tsum_shiftedInverseCubeTerm_le A c hA.le hc
  unfold Real.zeroBasedShiftedInverseCubeBudget
  exact Eq.subst (motive := fun value : ℝ => value ≤
      1 / A ^ 3 + Real.shiftedInverseCubeSeriesBudget A c)
    heq.symm (add_le_add_left htail (1 / A ^ 3))

theorem Real.tsum_zeroBasedShiftedInverseFourthTerm_le_budget
    (A c : ℝ) (hA : 0 < A) (hc : 0 < c) :
    (∑' n : ℕ, Real.zeroBasedShiftedInverseFourthTerm A c n) ≤
      Real.zeroBasedShiftedInverseFourthBudget A c := by
  have heq := Real.tsum_zeroBasedShiftedInverseFourthTerm_eq_zero_add_tail
    A c hA hc
  have htail := Real.tsum_shiftedInverseFourthTerm_le A c hA.le hc
  unfold Real.zeroBasedShiftedInverseFourthBudget
  exact Eq.subst (motive := fun value : ℝ => value ≤
      1 / A ^ 4 + Real.shiftedInverseFourthSeriesBudget A c)
    heq.symm (add_le_add_left htail (1 / A ^ 4))

end

end LFunctions
end Boundary
