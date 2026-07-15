import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ClassicalAnalysis.OscillatorySums.ShiftedReciprocalPowerTsum

/-!
# Quadratic, cubic, and quartic shifted reciprocal series

The logarithmic two-step integration-by-parts majorant contains precisely
inverse squares, cubes, and fourth powers of an affine frequency gap.  This
owner specializes the real-power comparison theorem to those three natural
powers and assembles a nonnegative four-coefficient packet budget.
-/

namespace Boundary
namespace LFunctions

noncomputable section

def Real.shiftedInverseSquareTerm
    (A c : ℝ) (n : ℕ) : ℝ :=
  1 / (A + c * ((n : ℝ) + 1)) ^ 2

def Real.shiftedInverseCubeTerm
    (A c : ℝ) (n : ℕ) : ℝ :=
  1 / (A + c * ((n : ℝ) + 1)) ^ 3

def Real.shiftedInverseFourthTerm
    (A c : ℝ) (n : ℕ) : ℝ :=
  1 / (A + c * ((n : ℝ) + 1)) ^ 4

def Real.shiftedInverseSquareBudget (A c : ℝ) : ℝ :=
  Real.shiftedReciprocalPowerIntegralBudget A c 2

def Real.shiftedInverseCubeBudget (A c : ℝ) : ℝ :=
  Real.shiftedReciprocalPowerIntegralBudget A c 3

def Real.shiftedInverseFourthBudget (A c : ℝ) : ℝ :=
  Real.shiftedReciprocalPowerIntegralBudget A c 4

def Real.shiftedInverseSquareSeriesBudget (A c : ℝ) : ℝ :=
  Real.shiftedInverseSquareTerm A c 0 +
    Real.shiftedInverseSquareBudget A c

def Real.shiftedInverseCubeSeriesBudget (A c : ℝ) : ℝ :=
  Real.shiftedInverseCubeTerm A c 0 +
    Real.shiftedInverseCubeBudget A c

def Real.shiftedInverseFourthSeriesBudget (A c : ℝ) : ℝ :=
  Real.shiftedInverseFourthTerm A c 0 +
    Real.shiftedInverseFourthBudget A c

theorem Real.shiftedInverseSquareTerm_eq_seriesTerm
    (A c : ℝ) (n : ℕ) :
    Real.shiftedInverseSquareTerm A c n =
      Real.shiftedReciprocalPowerSeriesTerm A c 2 n := by
  unfold Real.shiftedInverseSquareTerm
  unfold Real.shiftedReciprocalPowerSeriesTerm
  unfold Real.shiftedReciprocalPowerKernel
  have hpower := Real.rpow_natCast
    (A + c * ((n : ℝ) + 1)) 2
  exact congrArg (fun denominator : ℝ => 1 / denominator) hpower.symm

theorem Real.shiftedInverseCubeTerm_eq_seriesTerm
    (A c : ℝ) (n : ℕ) :
    Real.shiftedInverseCubeTerm A c n =
      Real.shiftedReciprocalPowerSeriesTerm A c 3 n := by
  unfold Real.shiftedInverseCubeTerm
  unfold Real.shiftedReciprocalPowerSeriesTerm
  unfold Real.shiftedReciprocalPowerKernel
  have hpower := Real.rpow_natCast
    (A + c * ((n : ℝ) + 1)) 3
  exact congrArg (fun denominator : ℝ => 1 / denominator) hpower.symm

theorem Real.shiftedInverseFourthTerm_eq_seriesTerm
    (A c : ℝ) (n : ℕ) :
    Real.shiftedInverseFourthTerm A c n =
      Real.shiftedReciprocalPowerSeriesTerm A c 4 n := by
  unfold Real.shiftedInverseFourthTerm
  unfold Real.shiftedReciprocalPowerSeriesTerm
  unfold Real.shiftedReciprocalPowerKernel
  have hpower := Real.rpow_natCast
    (A + c * ((n : ℝ) + 1)) 4
  exact congrArg (fun denominator : ℝ => 1 / denominator) hpower.symm

theorem Real.shiftedInverseSquareTerm_nonneg
    (A c : ℝ) (hA : 0 ≤ A) (hc : 0 < c) (n : ℕ) :
    0 ≤ Real.shiftedInverseSquareTerm A c n := by
  unfold Real.shiftedInverseSquareTerm
  have hn : 0 ≤ (n : ℝ) + 1 :=
    add_nonneg (Nat.cast_nonneg n) zero_le_one
  have hbase : 0 ≤ A + c * ((n : ℝ) + 1) :=
    add_nonneg hA (mul_nonneg hc.le hn)
  exact div_nonneg zero_le_one (pow_nonneg hbase 2)

theorem Real.shiftedInverseCubeTerm_nonneg
    (A c : ℝ) (hA : 0 ≤ A) (hc : 0 < c) (n : ℕ) :
    0 ≤ Real.shiftedInverseCubeTerm A c n := by
  unfold Real.shiftedInverseCubeTerm
  have hn : 0 ≤ (n : ℝ) + 1 :=
    add_nonneg (Nat.cast_nonneg n) zero_le_one
  have hbase : 0 ≤ A + c * ((n : ℝ) + 1) :=
    add_nonneg hA (mul_nonneg hc.le hn)
  exact div_nonneg zero_le_one (pow_nonneg hbase 3)

theorem Real.shiftedInverseFourthTerm_nonneg
    (A c : ℝ) (hA : 0 ≤ A) (hc : 0 < c) (n : ℕ) :
    0 ≤ Real.shiftedInverseFourthTerm A c n := by
  unfold Real.shiftedInverseFourthTerm
  have hn : 0 ≤ (n : ℝ) + 1 :=
    add_nonneg (Nat.cast_nonneg n) zero_le_one
  have hbase : 0 ≤ A + c * ((n : ℝ) + 1) :=
    add_nonneg hA (mul_nonneg hc.le hn)
  exact div_nonneg zero_le_one (pow_nonneg hbase 4)

theorem Real.summable_shiftedInverseSquareTerm
    (A c : ℝ) (hA : 0 ≤ A) (hc : 0 < c) :
    Summable (Real.shiftedInverseSquareTerm A c) := by
  have hseries := Real.summable_shiftedReciprocalPowerSeriesTerm
    A c 2 hA hc (show (1 : ℝ) < 2 from one_lt_two)
  have hfunction :
      Real.shiftedInverseSquareTerm A c =
        Real.shiftedReciprocalPowerSeriesTerm A c 2 := by
    funext n
    exact Real.shiftedInverseSquareTerm_eq_seriesTerm A c n
  exact Eq.subst
    (motive := fun function : ℕ → ℝ => Summable function)
    hfunction.symm hseries

theorem Real.summable_shiftedInverseCubeTerm
    (A c : ℝ) (hA : 0 ≤ A) (hc : 0 < c) :
    Summable (Real.shiftedInverseCubeTerm A c) := by
  have hseries := Real.summable_shiftedReciprocalPowerSeriesTerm
    A c 3 hA hc (Nat.one_lt_ofNat : (1 : ℝ) < 3)
  have hfunction :
      Real.shiftedInverseCubeTerm A c =
        Real.shiftedReciprocalPowerSeriesTerm A c 3 := by
    funext n
    exact Real.shiftedInverseCubeTerm_eq_seriesTerm A c n
  exact Eq.subst
    (motive := fun function : ℕ → ℝ => Summable function)
    hfunction.symm hseries

theorem Real.summable_shiftedInverseFourthTerm
    (A c : ℝ) (hA : 0 ≤ A) (hc : 0 < c) :
    Summable (Real.shiftedInverseFourthTerm A c) := by
  have hseries := Real.summable_shiftedReciprocalPowerSeriesTerm
    A c 4 hA hc (Nat.one_lt_ofNat : (1 : ℝ) < 4)
  have hfunction :
      Real.shiftedInverseFourthTerm A c =
        Real.shiftedReciprocalPowerSeriesTerm A c 4 := by
    funext n
    exact Real.shiftedInverseFourthTerm_eq_seriesTerm A c n
  exact Eq.subst
    (motive := fun function : ℕ → ℝ => Summable function)
    hfunction.symm hseries

theorem Real.tsum_shiftedInverseSquareTerm_le
    (A c : ℝ) (hA : 0 ≤ A) (hc : 0 < c) :
    (∑' n : ℕ, Real.shiftedInverseSquareTerm A c n) ≤
      Real.shiftedInverseSquareSeriesBudget A c := by
  have hseries := Real.tsum_shiftedReciprocalPowerSeriesTerm_le_seriesBudget
    A c 2 hA hc (show (1 : ℝ) < 2 from one_lt_two)
  have htsum :
      (∑' n : ℕ, Real.shiftedInverseSquareTerm A c n) =
      ∑' n : ℕ, Real.shiftedReciprocalPowerSeriesTerm A c 2 n := by
    exact tsum_congr
      (fun n => Real.shiftedInverseSquareTerm_eq_seriesTerm A c n)
  have hbudget :
      Real.shiftedReciprocalPowerSeriesBudget A c 2 =
        Real.shiftedInverseSquareSeriesBudget A c := by
    unfold Real.shiftedReciprocalPowerSeriesBudget
    unfold Real.shiftedInverseSquareSeriesBudget
    unfold Real.shiftedInverseSquareBudget
    have hfirst : Real.shiftedReciprocalPowerKernel A c 2 1 =
        Real.shiftedInverseSquareTerm A c 0 :=
      Eq.trans
        (Real.shiftedReciprocalPowerKernel_one_eq_seriesTerm_zero A c 2)
        (Real.shiftedInverseSquareTerm_eq_seriesTerm A c 0).symm
    exact congrArg₂ (fun first tail : ℝ => first + tail)
      hfirst rfl
  exact le_trans (le_of_eq htsum) (Eq.subst hbudget hseries)

theorem Real.tsum_shiftedInverseCubeTerm_le
    (A c : ℝ) (hA : 0 ≤ A) (hc : 0 < c) :
    (∑' n : ℕ, Real.shiftedInverseCubeTerm A c n) ≤
      Real.shiftedInverseCubeSeriesBudget A c := by
  have hseries := Real.tsum_shiftedReciprocalPowerSeriesTerm_le_seriesBudget
    A c 3 hA hc (Nat.one_lt_ofNat : (1 : ℝ) < 3)
  have htsum :
      (∑' n : ℕ, Real.shiftedInverseCubeTerm A c n) =
      ∑' n : ℕ, Real.shiftedReciprocalPowerSeriesTerm A c 3 n := by
    exact tsum_congr
      (fun n => Real.shiftedInverseCubeTerm_eq_seriesTerm A c n)
  have hbudget :
      Real.shiftedReciprocalPowerSeriesBudget A c 3 =
        Real.shiftedInverseCubeSeriesBudget A c := by
    unfold Real.shiftedReciprocalPowerSeriesBudget
    unfold Real.shiftedInverseCubeSeriesBudget
    unfold Real.shiftedInverseCubeBudget
    have hfirst : Real.shiftedReciprocalPowerKernel A c 3 1 =
        Real.shiftedInverseCubeTerm A c 0 :=
      Eq.trans
        (Real.shiftedReciprocalPowerKernel_one_eq_seriesTerm_zero A c 3)
        (Real.shiftedInverseCubeTerm_eq_seriesTerm A c 0).symm
    exact congrArg₂ (fun first tail : ℝ => first + tail)
      hfirst rfl
  exact le_trans (le_of_eq htsum) (Eq.subst hbudget hseries)

theorem Real.tsum_shiftedInverseFourthTerm_le
    (A c : ℝ) (hA : 0 ≤ A) (hc : 0 < c) :
    (∑' n : ℕ, Real.shiftedInverseFourthTerm A c n) ≤
      Real.shiftedInverseFourthSeriesBudget A c := by
  have hseries := Real.tsum_shiftedReciprocalPowerSeriesTerm_le_seriesBudget
    A c 4 hA hc (Nat.one_lt_ofNat : (1 : ℝ) < 4)
  have htsum :
      (∑' n : ℕ, Real.shiftedInverseFourthTerm A c n) =
      ∑' n : ℕ, Real.shiftedReciprocalPowerSeriesTerm A c 4 n := by
    exact tsum_congr
      (fun n => Real.shiftedInverseFourthTerm_eq_seriesTerm A c n)
  have hbudget :
      Real.shiftedReciprocalPowerSeriesBudget A c 4 =
        Real.shiftedInverseFourthSeriesBudget A c := by
    unfold Real.shiftedReciprocalPowerSeriesBudget
    unfold Real.shiftedInverseFourthSeriesBudget
    unfold Real.shiftedInverseFourthBudget
    have hfirst : Real.shiftedReciprocalPowerKernel A c 4 1 =
        Real.shiftedInverseFourthTerm A c 0 :=
      Eq.trans
        (Real.shiftedReciprocalPowerKernel_one_eq_seriesTerm_zero A c 4)
        (Real.shiftedInverseFourthTerm_eq_seriesTerm A c 0).symm
    exact congrArg₂ (fun first tail : ℝ => first + tail)
      hfirst rfl
  exact le_trans (le_of_eq htsum) (Eq.subst hbudget hseries)

def Real.shiftedReciprocalPacketTerm
    (A c C₂ C₃ D₃ C₄ : ℝ) (n : ℕ) : ℝ :=
  C₂ * Real.shiftedInverseSquareTerm A c n +
    C₃ * Real.shiftedInverseCubeTerm A c n +
    D₃ * Real.shiftedInverseCubeTerm A c n +
    C₄ * Real.shiftedInverseFourthTerm A c n

def Real.shiftedReciprocalPacketBudget
    (A c C₂ C₃ D₃ C₄ : ℝ) : ℝ :=
  C₂ * Real.shiftedInverseSquareBudget A c +
    C₃ * Real.shiftedInverseCubeBudget A c +
    D₃ * Real.shiftedInverseCubeBudget A c +
    C₄ * Real.shiftedInverseFourthBudget A c

def Real.shiftedReciprocalPacketSeriesBudget
    (A c C₂ C₃ D₃ C₄ : ℝ) : ℝ :=
  C₂ * Real.shiftedInverseSquareSeriesBudget A c +
    C₃ * Real.shiftedInverseCubeSeriesBudget A c +
    D₃ * Real.shiftedInverseCubeSeriesBudget A c +
    C₄ * Real.shiftedInverseFourthSeriesBudget A c

theorem Real.shiftedReciprocalPacketTerm_nonneg
    (A c C₂ C₃ D₃ C₄ : ℝ)
    (hA : 0 ≤ A) (hc : 0 < c)
    (hC₂ : 0 ≤ C₂) (hC₃ : 0 ≤ C₃)
    (hD₃ : 0 ≤ D₃) (hC₄ : 0 ≤ C₄)
    (n : ℕ) :
    0 ≤ Real.shiftedReciprocalPacketTerm A c C₂ C₃ D₃ C₄ n := by
  unfold Real.shiftedReciprocalPacketTerm
  have htwo := mul_nonneg hC₂
    (Real.shiftedInverseSquareTerm_nonneg A c hA hc n)
  have hthree := mul_nonneg hC₃
    (Real.shiftedInverseCubeTerm_nonneg A c hA hc n)
  have hdthree := mul_nonneg hD₃
    (Real.shiftedInverseCubeTerm_nonneg A c hA hc n)
  have hfour := mul_nonneg hC₄
    (Real.shiftedInverseFourthTerm_nonneg A c hA hc n)
  exact add_nonneg (add_nonneg (add_nonneg htwo hthree) hdthree) hfour

theorem Real.summable_shiftedReciprocalPacketTerm
    (A c C₂ C₃ D₃ C₄ : ℝ)
    (hA : 0 ≤ A) (hc : 0 < c) :
    Summable (Real.shiftedReciprocalPacketTerm A c C₂ C₃ D₃ C₄) := by
  unfold Real.shiftedReciprocalPacketTerm
  have htwo := (Real.summable_shiftedInverseSquareTerm A c hA hc).mul_left C₂
  have hthree := (Real.summable_shiftedInverseCubeTerm A c hA hc).mul_left C₃
  have hdthree := (Real.summable_shiftedInverseCubeTerm A c hA hc).mul_left D₃
  have hfour := (Real.summable_shiftedInverseFourthTerm A c hA hc).mul_left C₄
  exact ((htwo.add hthree).add hdthree).add hfour

theorem Real.tsum_shiftedReciprocalPacketTerm_eq_components
    (A c C₂ C₃ D₃ C₄ : ℝ)
    (hA : 0 ≤ A) (hc : 0 < c) :
    (∑' n : ℕ, Real.shiftedReciprocalPacketTerm A c C₂ C₃ D₃ C₄ n) =
      C₂ * (∑' n : ℕ, Real.shiftedInverseSquareTerm A c n) +
      C₃ * (∑' n : ℕ, Real.shiftedInverseCubeTerm A c n) +
      D₃ * (∑' n : ℕ, Real.shiftedInverseCubeTerm A c n) +
      C₄ * (∑' n : ℕ, Real.shiftedInverseFourthTerm A c n) := by
  have htwo := Real.summable_shiftedInverseSquareTerm A c hA hc
  have hthree := Real.summable_shiftedInverseCubeTerm A c hA hc
  have hfour := Real.summable_shiftedInverseFourthTerm A c hA hc
  unfold Real.shiftedReciprocalPacketTerm
  have hmulTwo := htwo.tsum_mul_left C₂
  have hmulThree := hthree.tsum_mul_left C₃
  have hmulDThree := hthree.tsum_mul_left D₃
  have hmulFour := hfour.tsum_mul_left C₄
  have haddOne := (htwo.mul_left C₂).hasSum.add
    (hthree.mul_left C₃).hasSum
  have haddTwo := haddOne.add (hthree.mul_left D₃).hasSum
  have haddThree := haddTwo.add (hfour.mul_left C₄).hasSum
  exact Eq.trans haddThree.tsum_eq
    (congrArg₂ (fun first last : ℝ => first + last)
      (congrArg₂ (fun first third : ℝ => first + third)
        (congrArg₂ (fun first second : ℝ => first + second)
          hmulTwo hmulThree)
        hmulDThree)
      hmulFour)

theorem Real.tsum_shiftedReciprocalPacketTerm_le_seriesBudget
    (A c C₂ C₃ D₃ C₄ : ℝ)
    (hA : 0 ≤ A) (hc : 0 < c)
    (hC₂ : 0 ≤ C₂) (hC₃ : 0 ≤ C₃)
    (hD₃ : 0 ≤ D₃) (hC₄ : 0 ≤ C₄) :
    (∑' n : ℕ, Real.shiftedReciprocalPacketTerm A c C₂ C₃ D₃ C₄ n) ≤
      Real.shiftedReciprocalPacketSeriesBudget A c C₂ C₃ D₃ C₄ := by
  have htwo := mul_le_mul_of_nonneg_left
    (Real.tsum_shiftedInverseSquareTerm_le A c hA hc) hC₂
  have hthree := mul_le_mul_of_nonneg_left
    (Real.tsum_shiftedInverseCubeTerm_le A c hA hc) hC₃
  have hdthree := mul_le_mul_of_nonneg_left
    (Real.tsum_shiftedInverseCubeTerm_le A c hA hc) hD₃
  have hfour := mul_le_mul_of_nonneg_left
    (Real.tsum_shiftedInverseFourthTerm_le A c hA hc) hC₄
  have hcomponents := add_le_add
    (add_le_add (add_le_add htwo hthree) hdthree) hfour
  have hdecompose := Real.tsum_shiftedReciprocalPacketTerm_eq_components
    A c C₂ C₃ D₃ C₄ hA hc
  unfold Real.shiftedReciprocalPacketSeriesBudget
  exact le_trans (le_of_eq hdecompose) hcomponents

end
end LFunctions
end Boundary
