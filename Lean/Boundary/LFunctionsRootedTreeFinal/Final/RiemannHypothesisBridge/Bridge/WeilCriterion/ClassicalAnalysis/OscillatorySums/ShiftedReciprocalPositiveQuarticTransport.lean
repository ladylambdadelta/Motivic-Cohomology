import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ClassicalAnalysis.OscillatorySums.ShiftedReciprocalPowerBudgetArithmetic
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ClassicalAnalysis.OscillatorySums.ShiftedReciprocalPositiveQuarticBudget

/-!
# Transport of shifted reciprocal series to the positive quartic

This owner retains the first discrete reciprocal term as well as the integral
tail.  The common affine shift is normalized by the barycentric coordinates
`A / (A + c)` and `c / (A + c)`.  The resulting four packet contributions are
bounded together by the quartic Bernstein envelope; no series term is dropped.
-/

namespace Boundary
namespace LFunctions

noncomputable section

private theorem shiftedReciprocal_realOfNat_mul_eq_of_nat_eq
    (a b c : ℕ) (h : a * b = c) :
    (a : ℝ) * (b : ℝ) = (c : ℝ) :=
  Eq.trans (Nat.cast_mul a b).symm
    (congrArg (fun n : ℕ => (n : ℝ)) h)

private theorem shiftedReciprocal_realOfNat_add_eq_of_nat_eq
    (a b c : ℕ) (h : a + b = c) :
    (a : ℝ) + (b : ℝ) = (c : ℝ) :=
  Eq.trans (Nat.cast_add a b).symm
    (congrArg (fun n : ℕ => (n : ℝ)) h)

private theorem shiftedReciprocal_realOfNat_pow_eq_of_nat_eq
    (a exponent c : ℕ) (h : a ^ exponent = c) :
    (a : ℝ) ^ exponent = (c : ℝ) :=
  Eq.trans (Nat.cast_pow a exponent).symm
    (congrArg (fun n : ℕ => (n : ℝ)) h)

private theorem shiftedReciprocal_natFraction_mul_eq_of_nat_eq
    (a b c d numerator denominator : ℕ)
    (hnumerator : a * c = numerator)
    (hdenominator : b * d = denominator) :
    ((a : ℝ) / (b : ℝ)) * ((c : ℝ) / (d : ℝ)) =
      (numerator : ℝ) / (denominator : ℝ) := by
  exact Eq.trans (div_mul_div_comm (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ))
    (congrArg₂ (fun left right : ℝ => left / right)
      (shiftedReciprocal_realOfNat_mul_eq_of_nat_eq a c numerator hnumerator)
      (shiftedReciprocal_realOfNat_mul_eq_of_nat_eq b d denominator hdenominator))

private theorem shiftedReciprocal_natFraction_add_eq_of_nat_eq
    (a b c d numerator denominator : ℕ)
    (hb : 0 < b) (hd : 0 < d)
    (hnumerator : a * d + b * c = numerator)
    (hdenominator : b * d = denominator) :
    (a : ℝ) / (b : ℝ) + (c : ℝ) / (d : ℝ) =
      (numerator : ℝ) / (denominator : ℝ) := by
  have hbNe : (b : ℝ) ≠ 0 := ne_of_gt (Nat.cast_pos.mpr hb)
  have hdNe : (d : ℝ) ≠ 0 := ne_of_gt (Nat.cast_pos.mpr hd)
  have hleftProduct : (a : ℝ) * d = ((a * d : ℕ) : ℝ) :=
    (Nat.cast_mul a d).symm
  have hrightProduct : (b : ℝ) * c = ((b * c : ℕ) : ℝ) :=
    (Nat.cast_mul b c).symm
  have hsum : (a : ℝ) * d + (b : ℝ) * c = (numerator : ℝ) :=
    Eq.trans
      (congrArg₂ (fun left right : ℝ => left + right)
        hleftProduct hrightProduct)
      (Eq.trans (Nat.cast_add (a * d) (b * c)).symm
        (congrArg (fun n : ℕ => (n : ℝ)) hnumerator))
  have hproduct : (b : ℝ) * d = (denominator : ℝ) :=
    shiftedReciprocal_realOfNat_mul_eq_of_nat_eq b d denominator hdenominator
  exact Eq.trans (div_add_div (a : ℝ) (c : ℝ) hbNe hdNe)
    (congrArg₂ (fun left right : ℝ => left / right) hsum hproduct)

private theorem shiftedReciprocal_natFraction_eq_of_cross
    (a b c d : ℕ)
    (hb : 0 < b) (hd : 0 < d)
    (hcross : a * d = c * b) :
    (a : ℝ) / (b : ℝ) = (c : ℝ) / (d : ℝ) := by
  have hbNe : (b : ℝ) ≠ 0 := ne_of_gt (Nat.cast_pos.mpr hb)
  have hdNe : (d : ℝ) ≠ 0 := ne_of_gt (Nat.cast_pos.mpr hd)
  have hleft : (a : ℝ) * d = ((a * d : ℕ) : ℝ) :=
    (Nat.cast_mul a d).symm
  have hright : (c : ℝ) * b = ((c * b : ℕ) : ℝ) :=
    (Nat.cast_mul c b).symm
  have hcastCross : ((a * d : ℕ) : ℝ) = ((c * b : ℕ) : ℝ) :=
    congrArg (fun n : ℕ => (n : ℝ)) hcross
  exact (div_eq_div_iff hbNe hdNe).mpr
    (Eq.trans hleft (Eq.trans hcastCross hright.symm))

private theorem shiftedReciprocal_two_add_three_eq_five :
    (2 : ℝ) + 3 = 5 := by
  have hleftTwo : (((2 : ℕ) : ℝ)) = (2 : ℝ) := Nat.cast_ofNat
  have hleftThree : (((3 : ℕ) : ℝ)) = (3 : ℝ) := Nat.cast_ofNat
  have hrightFive : (((5 : ℕ) : ℝ)) = (5 : ℝ) := Nat.cast_ofNat
  have hcastAdd : (((2 + 3 : ℕ) : ℝ)) = ((2 : ℕ) : ℝ) + ((3 : ℕ) : ℝ) :=
    Nat.cast_add 2 3
  have hcastComputation : (((2 + 3 : ℕ) : ℝ)) = ((5 : ℕ) : ℝ) :=
    congrArg (fun n : ℕ => (n : ℝ)) (show 2 + 3 = 5 from rfl)
  exact Eq.trans
    (congrArg₂ (fun left right : ℝ => left + right)
      hleftTwo.symm hleftThree.symm)
    (Eq.trans hcastAdd.symm (Eq.trans hcastComputation hrightFive))

def Real.shiftedReciprocalUnitRatio (A c : ℝ) : ℝ :=
  A / (A + c)

def Real.shiftedReciprocalUnitComplement (A c : ℝ) : ℝ :=
  c / (A + c)

theorem Real.div_eq_mul_one_div_transport (u v : ℝ) :
    u / v = u * (1 / v) := by
  exact Eq.trans (div_eq_mul_inv u v)
    (congrArg (fun factor : ℝ => u * factor) (one_div v).symm)

theorem Real.shiftedReciprocalUnitDenominator_pos
    {A c : ℝ} (hA : 0 ≤ A) (hc : 0 < c) :
    0 < A + c := by
  exact add_pos_of_nonneg_of_pos hA hc

theorem Real.shiftedReciprocalUnitRatio_nonneg
    {A c : ℝ} (hA : 0 ≤ A) (hc : 0 < c) :
    0 ≤ Real.shiftedReciprocalUnitRatio A c := by
  unfold Real.shiftedReciprocalUnitRatio
  exact div_nonneg hA
    (Real.shiftedReciprocalUnitDenominator_pos hA hc).le

theorem Real.shiftedReciprocalUnitComplement_nonneg
    {A c : ℝ} (hA : 0 ≤ A) (hc : 0 < c) :
    0 ≤ Real.shiftedReciprocalUnitComplement A c := by
  unfold Real.shiftedReciprocalUnitComplement
  exact div_nonneg hc.le
    (Real.shiftedReciprocalUnitDenominator_pos hA hc).le

theorem Real.shiftedReciprocalUnitRatio_add_complement
    {A c : ℝ} (hA : 0 ≤ A) (hc : 0 < c) :
    Real.shiftedReciprocalUnitRatio A c +
        Real.shiftedReciprocalUnitComplement A c = 1 := by
  unfold Real.shiftedReciprocalUnitRatio
  unfold Real.shiftedReciprocalUnitComplement
  have hdenominator : A + c ≠ 0 :=
    ne_of_gt (Real.shiftedReciprocalUnitDenominator_pos hA hc)
  exact Eq.trans (div_add_div_same A c (A + c))
    (div_self hdenominator)

theorem Real.shiftedReciprocalUnitRatio_le_one
    {A c : ℝ} (hA : 0 ≤ A) (hc : 0 < c) :
    Real.shiftedReciprocalUnitRatio A c ≤ 1 := by
  have hsum := Real.shiftedReciprocalUnitRatio_add_complement hA hc
  have hcomplement := Real.shiftedReciprocalUnitComplement_nonneg hA hc
  have hadd := add_le_add_left hcomplement
    (Real.shiftedReciprocalUnitRatio A c)
  have htoSum :
      Real.shiftedReciprocalUnitRatio A c ≤
        Real.shiftedReciprocalUnitRatio A c +
          Real.shiftedReciprocalUnitComplement A c :=
    le_trans
      (le_of_eq (add_zero (Real.shiftedReciprocalUnitRatio A c)).symm)
      hadd
  exact Eq.subst
    (motive := fun right : ℝ =>
      Real.shiftedReciprocalUnitRatio A c ≤ right)
    hsum htoSum

theorem Real.shiftedReciprocalUnitRatio_mem_unitInterval
    {A c : ℝ} (hA : 0 ≤ A) (hc : 0 < c) :
    Real.shiftedReciprocalUnitRatio A c ∈ Set.Icc (0 : ℝ) 1 := by
  exact ⟨Real.shiftedReciprocalUnitRatio_nonneg hA hc,
    Real.shiftedReciprocalUnitRatio_le_one hA hc⟩

theorem Real.shiftedInverseSquareTerm_zero_eq_base
    (A c : ℝ) :
    Real.shiftedInverseSquareTerm A c 0 = 1 / (A + c) ^ 2 := by
  unfold Real.shiftedInverseSquareTerm
  have hzero : (((0 : ℕ) : ℝ)) = 0 := Nat.cast_zero
  have hone : (0 : ℝ) + 1 = 1 := zero_add 1
  have hfactor : c * ((((0 : ℕ) : ℝ) + 1)) = c :=
    Eq.trans
      (congrArg (fun value : ℝ => c * (value + 1)) hzero)
      (Eq.trans (congrArg (fun value : ℝ => c * value) hone)
        (mul_one c))
  exact congrArg (fun base : ℝ => 1 / base ^ 2)
    (congrArg (fun value : ℝ => A + value) hfactor)

theorem Real.shiftedInverseCubeTerm_zero_eq_base
    (A c : ℝ) :
    Real.shiftedInverseCubeTerm A c 0 = 1 / (A + c) ^ 3 := by
  unfold Real.shiftedInverseCubeTerm
  have hzero : (((0 : ℕ) : ℝ)) = 0 := Nat.cast_zero
  have hone : (0 : ℝ) + 1 = 1 := zero_add 1
  have hfactor : c * ((((0 : ℕ) : ℝ) + 1)) = c :=
    Eq.trans
      (congrArg (fun value : ℝ => c * (value + 1)) hzero)
      (Eq.trans (congrArg (fun value : ℝ => c * value) hone)
        (mul_one c))
  exact congrArg (fun base : ℝ => 1 / base ^ 3)
    (congrArg (fun value : ℝ => A + value) hfactor)

theorem Real.shiftedInverseFourthTerm_zero_eq_base
    (A c : ℝ) :
    Real.shiftedInverseFourthTerm A c 0 = 1 / (A + c) ^ 4 := by
  unfold Real.shiftedInverseFourthTerm
  have hzero : (((0 : ℕ) : ℝ)) = 0 := Nat.cast_zero
  have hone : (0 : ℝ) + 1 = 1 := zero_add 1
  have hfactor : c * ((((0 : ℕ) : ℝ) + 1)) = c :=
    Eq.trans
      (congrArg (fun value : ℝ => c * (value + 1)) hzero)
      (Eq.trans (congrArg (fun value : ℝ => c * value) hone)
        (mul_one c))
  exact congrArg (fun base : ℝ => 1 / base ^ 4)
    (congrArg (fun value : ℝ => A + value) hfactor)

theorem Real.shiftedInverseSquareSeriesBudget_nonneg
    {A c : ℝ} (hA : 0 ≤ A) (hc : 0 < c) :
    0 ≤ Real.shiftedInverseSquareSeriesBudget A c := by
  unfold Real.shiftedInverseSquareSeriesBudget
  exact add_nonneg
    (Real.shiftedInverseSquareTerm_nonneg A c hA hc 0)
    (Real.shiftedInverseSquareBudget_nonneg A c hA hc)

theorem Real.shiftedInverseCubeSeriesBudget_nonneg
    {A c : ℝ} (hA : 0 ≤ A) (hc : 0 < c) :
    0 ≤ Real.shiftedInverseCubeSeriesBudget A c := by
  unfold Real.shiftedInverseCubeSeriesBudget
  exact add_nonneg
    (Real.shiftedInverseCubeTerm_nonneg A c hA hc 0)
    (Real.shiftedInverseCubeBudget_nonneg A c hA hc)

theorem Real.shiftedInverseFourthSeriesBudget_nonneg
    {A c : ℝ} (hA : 0 ≤ A) (hc : 0 < c) :
    0 ≤ Real.shiftedInverseFourthSeriesBudget A c := by
  unfold Real.shiftedInverseFourthSeriesBudget
  exact add_nonneg
    (Real.shiftedInverseFourthTerm_nonneg A c hA hc 0)
    (Real.shiftedInverseFourthBudget_nonneg A c hA hc)

theorem Real.shiftedInverseSquareBudget_eq_base
    {A c : ℝ} (hA : 0 ≤ A) (hc : 0 < c) :
    Real.shiftedInverseSquareBudget A c =
      1 / (c * (A + c)) := by
  unfold Real.shiftedInverseSquareBudget
  unfold Real.shiftedReciprocalPowerIntegralBudget
  let d : ℝ := A + c
  have hd : 0 < d := Real.shiftedReciprocalUnitDenominator_pos hA hc
  have hnegativeAdd : (-1 : ℝ) + 2 = 1 := by
    exact Eq.trans
      (congrArg (fun value : ℝ => (-1) + value) one_add_one_eq_two.symm)
      (neg_add_cancel_left 1 1)
  have hexponent : (1 : ℝ) - 2 = -1 :=
    sub_eq_iff_eq_add.mpr hnegativeAdd.symm
  have hfactor : (2 : ℝ) - 1 = 1 :=
    sub_eq_iff_eq_add.mpr one_add_one_eq_two.symm
  have hrpow : d ^ ((1 : ℝ) - 2) = d⁻¹ :=
    Eq.trans
      (congrArg (fun exponent : ℝ => d ^ exponent) hexponent)
      (Real.rpow_neg_one d)
  have hdenominator : c * ((2 : ℝ) - 1) = c :=
    Eq.trans (congrArg (fun value : ℝ => c * value) hfactor)
      (mul_one c)
  have hinverse : d⁻¹ / c = 1 / (c * d) := by
    exact Eq.trans (div_eq_mul_inv d⁻¹ c)
      (Eq.trans (mul_inv_rev c d).symm
        (one_div (c * d)).symm)
  exact Eq.trans
    (congrArg₂ (fun numerator denominator : ℝ => numerator / denominator)
      hrpow hdenominator)
    hinverse

theorem Real.shiftedInverseCubeBudget_eq_base
    {A c : ℝ} (hA : 0 ≤ A) (hc : 0 < c) :
    Real.shiftedInverseCubeBudget A c =
      1 / ((2 * c) * (A + c) ^ 2) := by
  unfold Real.shiftedInverseCubeBudget
  unfold Real.shiftedReciprocalPowerIntegralBudget
  let d : ℝ := A + c
  have hd : 0 < d := Real.shiftedReciprocalUnitDenominator_pos hA hc
  have hnegativeAdd : (-2 : ℝ) + 3 = 1 := by
    exact Eq.trans
      (congrArg (fun value : ℝ => (-2) + value) two_add_one_eq_three.symm)
      (neg_add_cancel_left 2 1)
  have hexponent : (1 : ℝ) - 3 = -2 :=
    sub_eq_iff_eq_add.mpr hnegativeAdd.symm
  have hfactor : (3 : ℝ) - 1 = 2 :=
    sub_eq_iff_eq_add.mpr two_add_one_eq_three.symm
  have hrpow : d ^ ((1 : ℝ) - 3) = (d ^ 2)⁻¹ := by
    have hnegative := Real.rpow_neg hd.le 2
    have hnatural := Real.rpow_natCast d 2
    exact Eq.trans
      (congrArg (fun exponent : ℝ => d ^ exponent) hexponent)
      (Eq.trans hnegative (congrArg Inv.inv hnatural))
  have hdenominator : c * ((3 : ℝ) - 1) = 2 * c :=
    Eq.trans (congrArg (fun value : ℝ => c * value) hfactor)
      (mul_comm c 2)
  have hinverse : (d ^ 2)⁻¹ / (2 * c) =
      1 / ((2 * c) * d ^ 2) := by
    exact Eq.trans (div_eq_mul_inv (d ^ 2)⁻¹ (2 * c))
      (Eq.trans (mul_inv_rev (2 * c) (d ^ 2)).symm
        (one_div ((2 * c) * d ^ 2)).symm)
  exact Eq.trans
    (congrArg₂ (fun numerator denominator : ℝ => numerator / denominator)
      hrpow hdenominator)
    hinverse

theorem Real.shiftedInverseFourthBudget_eq_base
    {A c : ℝ} (hA : 0 ≤ A) (hc : 0 < c) :
    Real.shiftedInverseFourthBudget A c =
      1 / ((3 * c) * (A + c) ^ 3) := by
  unfold Real.shiftedInverseFourthBudget
  unfold Real.shiftedReciprocalPowerIntegralBudget
  let d : ℝ := A + c
  have hd : 0 < d := Real.shiftedReciprocalUnitDenominator_pos hA hc
  have hnegativeAdd : (-3 : ℝ) + 4 = 1 := by
    exact Eq.trans
      (congrArg (fun value : ℝ => (-3) + value) three_add_one_eq_four.symm)
      (neg_add_cancel_left 3 1)
  have hexponent : (1 : ℝ) - 4 = -3 :=
    sub_eq_iff_eq_add.mpr hnegativeAdd.symm
  have hfactor : (4 : ℝ) - 1 = 3 :=
    sub_eq_iff_eq_add.mpr three_add_one_eq_four.symm
  have hrpow : d ^ ((1 : ℝ) - 4) = (d ^ 3)⁻¹ := by
    have hnegative := Real.rpow_neg hd.le 3
    have hnatural := Real.rpow_natCast d 3
    exact Eq.trans
      (congrArg (fun exponent : ℝ => d ^ exponent) hexponent)
      (Eq.trans hnegative (congrArg Inv.inv hnatural))
  have hdenominator : c * ((4 : ℝ) - 1) = 3 * c :=
    Eq.trans (congrArg (fun value : ℝ => c * value) hfactor)
      (mul_comm c 3)
  have hinverse : (d ^ 3)⁻¹ / (3 * c) =
      1 / ((3 * c) * d ^ 3) := by
    exact Eq.trans (div_eq_mul_inv (d ^ 3)⁻¹ (3 * c))
      (Eq.trans (mul_inv_rev (3 * c) (d ^ 3)).symm
        (one_div ((3 * c) * d ^ 3)).symm)
  exact Eq.trans
    (congrArg₂ (fun numerator denominator : ℝ => numerator / denominator)
      hrpow hdenominator)
    hinverse

theorem Real.one_div_mul_self_div
    {c d : ℝ} (hc : c ≠ 0) :
    (1 / c) * (c / d) = 1 / d := by
  calc
    (1 / c) * (c / d) = (1 * c) / (c * d) :=
      div_mul_div_comm 1 c c d
    _ = c / (c * d) :=
      congrArg (fun numerator : ℝ => numerator / (c * d)) (one_mul c)
    _ = (c / c) / d := div_mul_eq_div_div c c d
    _ = 1 / d := congrArg (fun value : ℝ => value / d) (div_self hc)

theorem Real.one_div_square_eq_one_div_mul
    {c : ℝ} :
    1 / c ^ 2 = (1 / c) * (1 / c) := by
  have hpow : (1 / c) ^ 2 = 1 ^ 2 / c ^ 2 := div_pow 1 c 2
  exact Eq.trans
    (congrArg (fun numerator : ℝ => numerator / c ^ 2) (one_pow 2).symm)
    (Eq.trans hpow.symm (pow_two (1 / c)))

theorem Real.one_div_square_mul_self_div_square
    {c d : ℝ} (hc : c ≠ 0) :
    (1 / c ^ 2) * (c / d) ^ 2 = 1 / d ^ 2 := by
  have hcSquare : c ^ 2 ≠ 0 := pow_ne_zero 2 hc
  have hdivPower : (c / d) ^ 2 = c ^ 2 / d ^ 2 := div_pow c d 2
  exact Eq.trans
    (congrArg (fun value : ℝ => (1 / c ^ 2) * value) hdivPower)
    (Real.one_div_mul_self_div hcSquare)

theorem Real.one_div_square_mul_self_div
    {c d : ℝ} (hc : c ≠ 0) :
    (1 / c ^ 2) * (c / d) = 1 / (c * d) := by
  have hsplit := Real.one_div_square_eq_one_div_mul (c := c)
  have hcancel := Real.one_div_mul_self_div (c := c) (d := d) hc
  have hlast : (1 / c) * (1 / d) = 1 / (c * d) := by
    exact Eq.trans (div_mul_div_comm 1 c 1 d)
      (congrArg (fun numerator : ℝ => numerator / (c * d)) (one_mul 1))
  exact Eq.trans
    (congrArg (fun value : ℝ => value * (c / d)) hsplit)
    (Eq.trans (mul_assoc (1 / c) (1 / c) (c / d))
      (Eq.trans (congrArg (fun value : ℝ => (1 / c) * value) hcancel)
        hlast))

/-- The discrete reciprocal term becomes the product of the normalized shift
power and normalized complement. -/
theorem Real.shiftedReciprocalDiscreteTerm_eq_unitCoordinates
    (A c d : ℝ) (n : ℕ) (hc : c ≠ 0) :
    A ^ n * (1 / d ^ (n + 1)) =
      (1 / c) * (A / d) ^ n * (c / d) := by
  have hratioPower : (A / d) ^ n = A ^ n / d ^ n :=
    div_pow A d n
  have hcancel : (1 / c) * (c / d) = 1 / d :=
    Real.one_div_mul_self_div hc
  have hproduct :
      (A ^ n / d ^ n) * (1 / d) = A ^ n / d ^ (n + 1) := by
    have hraw :
        (A ^ n / d ^ n) * (1 / d) =
          (A ^ n * 1) / (d ^ n * d) :=
      div_mul_div_comm (A ^ n) (d ^ n) 1 d
    have hnumerator : A ^ n * 1 = A ^ n := mul_one (A ^ n)
    have hdenominator : d ^ n * d = d ^ (n + 1) :=
      (pow_succ d n).symm
    exact Eq.trans hraw
      (congrArg₂ (fun numerator denominator : ℝ => numerator / denominator)
        hnumerator hdenominator)
  have hleft :
      A ^ n * (1 / d ^ (n + 1)) = A ^ n / d ^ (n + 1) :=
    (Real.div_eq_mul_one_div_transport (A ^ n) (d ^ (n + 1))).symm
  have hright :
      (1 / c) * (A / d) ^ n * (c / d) =
        A ^ n / d ^ (n + 1) := by
    exact Eq.trans
      (congrArg (fun value : ℝ => (1 / c) * value * (c / d))
        hratioPower)
      (Eq.trans
        (congrArg (fun value : ℝ => value * (c / d))
          (mul_comm (1 / c) (A ^ n / d ^ n)))
        (Eq.trans
          (mul_assoc (A ^ n / d ^ n) (1 / c) (c / d))
          (Eq.trans
            (congrArg (fun value : ℝ => (A ^ n / d ^ n) * value) hcancel)
            hproduct)))
  exact Eq.trans hleft hright.symm

/-- The integral reciprocal term becomes the normalized shift power times the
reciprocal step coefficient. -/
theorem Real.shiftedReciprocalIntegralTerm_eq_unitCoordinates
    (A c d k : ℝ) (n : ℕ) :
    A ^ n * (1 / ((k * c) * d ^ n)) =
      (1 / c) * (A / d) ^ n * (1 / k) := by
  have hratioPower : (A / d) ^ n = A ^ n / d ^ n :=
    div_pow A d n
  have hreciprocalProduct :
      (1 / c) * (1 / k) = 1 / (k * c) := by
    have hraw : (1 / c) * (1 / k) = (1 * 1) / (c * k) :=
      div_mul_div_comm 1 c 1 k
    have hnumerator : (1 : ℝ) * 1 = 1 := one_mul 1
    have hdenominator : c * k = k * c := mul_comm c k
    exact Eq.trans hraw
      (congrArg₂ (fun numerator denominator : ℝ => numerator / denominator)
        hnumerator hdenominator)
  have hproduct :
      (A ^ n / d ^ n) * (1 / (k * c)) =
        A ^ n / ((k * c) * d ^ n) := by
    have hraw :
        (A ^ n / d ^ n) * (1 / (k * c)) =
          (A ^ n * 1) / (d ^ n * (k * c)) :=
      div_mul_div_comm (A ^ n) (d ^ n) 1 (k * c)
    have hnumerator : A ^ n * 1 = A ^ n := mul_one (A ^ n)
    have hdenominator : d ^ n * (k * c) = (k * c) * d ^ n :=
      mul_comm (d ^ n) (k * c)
    exact Eq.trans hraw
      (congrArg₂ (fun numerator denominator : ℝ => numerator / denominator)
        hnumerator hdenominator)
  have hleft :
      A ^ n * (1 / ((k * c) * d ^ n)) =
        A ^ n / ((k * c) * d ^ n) :=
    (Real.div_eq_mul_one_div_transport
      (A ^ n) ((k * c) * d ^ n)).symm
  have hright :
      (1 / c) * (A / d) ^ n * (1 / k) =
        A ^ n / ((k * c) * d ^ n) := by
    exact Eq.trans
      (congrArg (fun value : ℝ => (1 / c) * value * (1 / k))
        hratioPower)
      (Eq.trans
        (congrArg (fun value : ℝ => value * (1 / k))
          (mul_comm (1 / c) (A ^ n / d ^ n)))
        (Eq.trans
          (mul_assoc (A ^ n / d ^ n) (1 / c) (1 / k))
          (Eq.trans
            (congrArg (fun value : ℝ => (A ^ n / d ^ n) * value)
              hreciprocalProduct)
            hproduct)))
  exact Eq.trans hleft hright.symm

theorem Real.scalar_mul_reciprocal_factor
    (K denominator X : ℝ) :
    K * ((1 / denominator) * X) = (K / denominator) * X := by
  exact Eq.trans (mul_assoc K (1 / denominator) X).symm
    (congrArg (fun value : ℝ => value * X)
      (Real.div_eq_mul_one_div_transport K denominator).symm)

theorem Real.scalar_mul_shifted_factor
    (K P B denominator X : ℝ)
    (hfactor : P * B = (1 / denominator) * X) :
    (K * P) * B = (K / denominator) * X := by
  exact Eq.trans (mul_assoc K P B)
    (Eq.trans (congrArg (fun value : ℝ => K * value) hfactor)
      (Real.scalar_mul_reciprocal_factor K denominator X))

/-- Multiplication by the barycentric identity raises a monomial by one total
degree.  Later degree-elevation proofs use only this cut and explicit
associativity transports. -/
theorem Real.barycentric_monomial_degree_elevation
    (monomial r y : ℝ) (hsum : r + y = 1) :
    monomial = monomial * r + monomial * y := by
  exact Eq.trans (mul_one monomial).symm
    (Eq.trans
      (congrArg (fun value : ℝ => monomial * value) hsum.symm)
      (mul_add monomial r y))

theorem Real.mul_power_succ_transport (x : ℝ) (n : ℕ) :
    x ^ n * x = x ^ (n + 1) :=
  (pow_succ x n).symm

theorem Real.left_mul_power_commute (r y : ℝ) (n : ℕ) :
    (r * y ^ n) * r = r ^ 2 * y ^ n := by
  have hcommute : y ^ n * r = r * y ^ n := mul_comm (y ^ n) r
  have hpair : r * r = r ^ 2 := (pow_two r).symm
  exact Eq.trans (mul_assoc r (y ^ n) r)
    (Eq.trans (congrArg (fun value : ℝ => r * value) hcommute)
      (Eq.trans (mul_assoc r r (y ^ n)).symm
        (congrArg (fun value : ℝ => value * y ^ n) hpair)))

theorem Real.power_mul_right_commute (r y : ℝ) (n : ℕ) :
    (r ^ n * y) * r = r ^ (n + 1) * y := by
  exact Eq.trans (mul_assoc (r ^ n) y r)
    (Eq.trans
      (congrArg (fun value : ℝ => r ^ n * value) (mul_comm y r))
      (Eq.trans (mul_assoc (r ^ n) r y).symm
        (congrArg (fun value : ℝ => value * y)
          (Real.mul_power_succ_transport r n))))

theorem Real.mul_y_mul_r_eq_square_mul_y (r y : ℝ) :
    (r * y) * r = r ^ 2 * y := by
  exact Eq.trans (mul_assoc r y r)
    (Eq.trans
      (congrArg (fun value : ℝ => r * value) (mul_comm y r))
      (Eq.trans (mul_assoc r r y).symm
        (congrArg (fun value : ℝ => value * y) (pow_two r).symm)))

theorem Real.mul_y_mul_y_eq_mul_square (r y : ℝ) :
    (r * y) * y = r * y ^ 2 := by
  exact Eq.trans (mul_assoc r y y)
    (congrArg (fun value : ℝ => r * value) (pow_two y).symm)

theorem Real.power_mul_y_mul_y_eq_power_mul_square
    (r y : ℝ) (n : ℕ) :
    (r ^ n * y) * y = r ^ n * y ^ 2 := by
  exact Eq.trans (mul_assoc (r ^ n) y y)
    (congrArg (fun value : ℝ => r ^ n * value) (pow_two y).symm)

theorem Real.add_duplicate_middle (a b c : ℝ) :
    (a + b) + (b + c) = a + 2 * b + c := by
  exact Eq.trans (add_assoc a b (b + c))
    (Eq.trans
      (congrArg (fun value : ℝ => a + value) (add_assoc b b c).symm)
      (Eq.trans
        (congrArg (fun value : ℝ => a + (value + c)) (two_mul b).symm)
        (add_assoc a (2 * b) c).symm))

theorem Real.three_mul_explicit (x : ℝ) :
    3 * x = 2 * x + x := by
  exact Eq.trans
    (congrArg (fun coefficient : ℝ => coefficient * x)
      two_add_one_eq_three.symm)
    (Eq.trans (add_mul 2 1 x)
      (congrArg (fun value : ℝ => 2 * x + value) (one_mul x)))

theorem Real.add_pascal_degree_three (a b c d : ℝ) :
    (a + 2 * b + c) + (b + 2 * c + d) =
      a + 3 * b + 3 * c + d := by
  have hb : 2 * b + b = 3 * b := by
    exact (Real.three_mul_explicit b).symm
  have hc : c + 2 * c = 3 * c := by
    exact Eq.trans
      (add_comm c (2 * c))
      (Real.three_mul_explicit c).symm
  have hswap : c + (b + (2 * c + d)) = b + (c + (2 * c + d)) := by
    exact Eq.trans (add_assoc c b (2 * c + d)).symm
      (Eq.trans
        (congrArg (fun value : ℝ => value + (2 * c + d)) (add_comm c b))
        (add_assoc b c (2 * c + d)))
  calc
    (a + 2 * b + c) + (b + 2 * c + d) =
        a + (2 * b + (c + (b + (2 * c + d)))) := by
      exact Eq.trans
        (congrArg (fun value : ℝ => (a + 2 * b + c) + value)
          (add_assoc b (2 * c) d))
        (Eq.trans
          (add_assoc (a + 2 * b) c (b + (2 * c + d)))
          (add_assoc a (2 * b) (c + (b + (2 * c + d)))))
    _ = a + (2 * b + (b + (c + (2 * c + d)))) :=
      congrArg (fun value : ℝ => a + (2 * b + value)) hswap
    _ = a + ((2 * b + b) + (c + (2 * c + d))) :=
      congrArg (fun value : ℝ => a + value)
        (add_assoc (2 * b) b (c + (2 * c + d))).symm
    _ = a + (3 * b + (3 * c + d)) := by
      exact congrArg₂ (fun left right : ℝ => a + (left + right)) hb
        (Eq.trans (add_assoc c (2 * c) d).symm
          (congrArg (fun value : ℝ => value + d) hc))
    _ = a + 3 * b + 3 * c + d := by
      exact Eq.trans (add_assoc a (3 * b) (3 * c + d)).symm
        (add_assoc (a + 3 * b) (3 * c) d).symm

theorem Real.barycentric_y_square_degree_four
    (r y : ℝ) (hsum : r + y = 1) :
    y ^ 2 = r ^ 2 * y ^ 2 + 2 * (r * y ^ 3) + y ^ 4 := by
  have hfirst :=
    Real.barycentric_monomial_degree_elevation (y ^ 2) r y hsum
  have hfirstNormalized : y ^ 2 = r * y ^ 2 + y ^ 3 := by
    exact Eq.trans hfirst
      (congrArg₂ (fun left right : ℝ => left + right)
        (mul_comm (y ^ 2) r)
        (Real.mul_power_succ_transport y 2))
  have hmixed :=
    Real.barycentric_monomial_degree_elevation (r * y ^ 2) r y hsum
  have hmixedNormalized :
      r * y ^ 2 = r ^ 2 * y ^ 2 + r * y ^ 3 := by
    have hright : (r * y ^ 2) * y = r * y ^ 3 :=
      Eq.trans (mul_assoc r (y ^ 2) y)
        (congrArg (fun value : ℝ => r * value)
          (Real.mul_power_succ_transport y 2))
    exact Eq.trans hmixed
      (congrArg₂ (fun left right : ℝ => left + right)
        (Real.left_mul_power_commute r y 2) hright)
  have hyCube :=
    Real.barycentric_monomial_degree_elevation (y ^ 3) r y hsum
  have hyCubeNormalized : y ^ 3 = r * y ^ 3 + y ^ 4 := by
    exact Eq.trans hyCube
      (congrArg₂ (fun left right : ℝ => left + right)
        (mul_comm (y ^ 3) r)
        (Real.mul_power_succ_transport y 3))
  exact Eq.trans hfirstNormalized
    (Eq.trans
      (congrArg₂ (fun left right : ℝ => left + right)
        hmixedNormalized hyCubeNormalized)
      (Real.add_duplicate_middle
        (r ^ 2 * y ^ 2) (r * y ^ 3) (y ^ 4)))

theorem Real.barycentric_y_degree_four
    (r y : ℝ) (hsum : r + y = 1) :
    y = r ^ 3 * y + 3 * (r ^ 2 * y ^ 2) +
      3 * (r * y ^ 3) + y ^ 4 := by
  have hry :=
    Real.barycentric_monomial_degree_elevation (r * y) r y hsum
  have hryNormalized : r * y = r ^ 2 * y + r * y ^ 2 := by
    have hleft : (r * y) * r = r ^ 2 * y :=
      Real.mul_y_mul_r_eq_square_mul_y r y
    have hright : (r * y) * y = r * y ^ 2 :=
      Real.mul_y_mul_y_eq_mul_square r y
    exact Eq.trans hry
      (congrArg₂ (fun left right : ℝ => left + right) hleft hright)
  have hrSquareY :=
    Real.barycentric_monomial_degree_elevation (r ^ 2 * y) r y hsum
  have hrSquareYNormalized :
      r ^ 2 * y = r ^ 3 * y + r ^ 2 * y ^ 2 := by
    have hleft : (r ^ 2 * y) * r = r ^ 3 * y :=
      Real.power_mul_right_commute r y 2
    have hright : (r ^ 2 * y) * y = r ^ 2 * y ^ 2 :=
      Real.power_mul_y_mul_y_eq_power_mul_square r y 2
    exact Eq.trans hrSquareY
      (congrArg₂ (fun left right : ℝ => left + right) hleft hright)
  have hrYSquare :=
    Real.barycentric_monomial_degree_elevation (r * y ^ 2) r y hsum
  have hrYSquareNormalized :
      r * y ^ 2 = r ^ 2 * y ^ 2 + r * y ^ 3 := by
    have hright : (r * y ^ 2) * y = r * y ^ 3 :=
      Eq.trans (mul_assoc r (y ^ 2) y)
        (congrArg (fun value : ℝ => r * value)
          (Real.mul_power_succ_transport y 2))
    exact Eq.trans hrYSquare
      (congrArg₂ (fun left right : ℝ => left + right)
        (Real.left_mul_power_commute r y 2) hright)
  have hryDegreeFour :
      r * y = r ^ 3 * y + 2 * (r ^ 2 * y ^ 2) + r * y ^ 3 := by
    exact Eq.trans hryNormalized
      (Eq.trans
        (congrArg₂ (fun left right : ℝ => left + right)
          hrSquareYNormalized hrYSquareNormalized)
        (Real.add_duplicate_middle
          (r ^ 3 * y) (r ^ 2 * y ^ 2) (r * y ^ 3)))
  have hyFirst :=
    Real.barycentric_monomial_degree_elevation y r y hsum
  have hyFirstNormalized : y = r * y + y ^ 2 := by
    exact Eq.trans hyFirst
      (congrArg₂ (fun left right : ℝ => left + right)
        (mul_comm y r) (pow_two y).symm)
  exact Eq.trans hyFirstNormalized
    (Eq.trans
      (congrArg₂ (fun left right : ℝ => left + right)
        hryDegreeFour (Real.barycentric_y_square_degree_four r y hsum))
      (Real.add_pascal_degree_three
        (r ^ 3 * y) (r ^ 2 * y ^ 2) (r * y ^ 3) (y ^ 4)))

theorem Real.barycentric_r_square_y_degree_four
    (r y : ℝ) (hsum : r + y = 1) :
    r ^ 2 * y = r ^ 3 * y + r ^ 2 * y ^ 2 := by
  have helevated :=
    Real.barycentric_monomial_degree_elevation (r ^ 2 * y) r y hsum
  have hleft : (r ^ 2 * y) * r = r ^ 3 * y :=
    Real.power_mul_right_commute r y 2
  have hright : (r ^ 2 * y) * y = r ^ 2 * y ^ 2 :=
    Real.power_mul_y_mul_y_eq_power_mul_square r y 2
  exact Eq.trans helevated
    (congrArg₂ (fun left right : ℝ => left + right) hleft hright)

theorem Real.barycentric_r_cube_degree_four
    (r y : ℝ) (hsum : r + y = 1) :
    r ^ 3 = r ^ 4 + r ^ 3 * y := by
  have helevated :=
    Real.barycentric_monomial_degree_elevation (r ^ 3) r y hsum
  exact Eq.trans helevated
    (congrArg₂ (fun left right : ℝ => left + right)
      (Real.mul_power_succ_transport r 3) rfl)

theorem Real.barycentric_r_square_degree_four
    (r y : ℝ) (hsum : r + y = 1) :
    r ^ 2 = r ^ 4 + 2 * (r ^ 3 * y) + r ^ 2 * y ^ 2 := by
  have helevated :=
    Real.barycentric_monomial_degree_elevation (r ^ 2) r y hsum
  have hfirst : r ^ 2 = r ^ 3 + r ^ 2 * y := by
    exact Eq.trans helevated
      (congrArg₂ (fun left right : ℝ => left + right)
        (Real.mul_power_succ_transport r 2) rfl)
  exact Eq.trans hfirst
    (Eq.trans
      (congrArg₂ (fun left right : ℝ => left + right)
        (Real.barycentric_r_cube_degree_four r y hsum)
        (Real.barycentric_r_square_y_degree_four r y hsum))
      (Real.add_duplicate_middle
        (r ^ 4) (r ^ 3 * y) (r ^ 2 * y ^ 2)))

theorem Real.one_half_mul_two : (1 / 2 : ℝ) * 2 = 1 := by
  have htwoNe : (2 : ℝ) ≠ 0 :=
    ne_of_gt (Nat.cast_pos.mpr (Nat.zero_lt_succ 1))
  exact Eq.trans (div_mul_eq_mul_div 1 2 2)
    (Eq.trans (congrArg (fun numerator : ℝ => numerator / 2) (one_mul 2))
      (div_self htwoNe))

theorem Real.one_third_mul_three : (1 / 3 : ℝ) * 3 = 1 := by
  have hthreeNe : (3 : ℝ) ≠ 0 :=
    ne_of_gt (Nat.cast_pos.mpr (Nat.zero_lt_succ 2))
  exact Eq.trans (div_mul_eq_mul_div 1 3 3)
    (Eq.trans (congrArg (fun numerator : ℝ => numerator / 3) (one_mul 3))
      (div_self hthreeNe))

theorem Real.barycentric_square_packet_expansion
    (r y : ℝ) (hsum : r + y = 1) :
    y ^ 2 + y =
      (r ^ 2 * y ^ 2 + 2 * (r * y ^ 3) + y ^ 4) +
      (r ^ 3 * y + 3 * (r ^ 2 * y ^ 2) +
        3 * (r * y ^ 3) + y ^ 4) := by
  exact congrArg₂ (fun left right : ℝ => left + right)
    (Real.barycentric_y_square_degree_four r y hsum)
    (Real.barycentric_y_degree_four r y hsum)

theorem Real.barycentric_cube_packet_expansion
    (r y : ℝ) (hsum : r + y = 1) :
    r ^ 2 * (y + 1 / 2) =
      (r ^ 3 * y + r ^ 2 * y ^ 2) +
        (1 / 2) * (r ^ 4 + 2 * (r ^ 3 * y) + r ^ 2 * y ^ 2) := by
  have hfirst := Real.barycentric_r_square_y_degree_four r y hsum
  have hsecond :
      r ^ 2 * (1 / 2) =
        (1 / 2) * (r ^ 4 + 2 * (r ^ 3 * y) + r ^ 2 * y ^ 2) := by
    exact Eq.trans (mul_comm (r ^ 2) (1 / 2))
      (congrArg (fun value : ℝ => (1 / 2) * value)
        (Real.barycentric_r_square_degree_four r y hsum))
  exact Eq.trans (mul_add (r ^ 2) y (1 / 2))
    (congrArg₂ (fun left right : ℝ => left + right) hfirst hsecond)

theorem Real.barycentric_fourth_packet_expansion
    (r y : ℝ) (hsum : r + y = 1) :
    r ^ 3 * (y + 1 / 3) =
      r ^ 3 * y + (1 / 3) * (r ^ 4 + r ^ 3 * y) := by
  have hsecond :
      r ^ 3 * (1 / 3) = (1 / 3) * (r ^ 4 + r ^ 3 * y) := by
    exact Eq.trans (mul_comm (r ^ 3) (1 / 3))
      (congrArg (fun value : ℝ => (1 / 3) * value)
        (Real.barycentric_r_cube_degree_four r y hsum))
  exact Eq.trans (mul_add (r ^ 3) y (1 / 3))
    (congrArg (fun value : ℝ => r ^ 3 * y + value) hsecond)

theorem Real.shiftedInverseSquareSeriesBudget_eq_unitCoordinates
    {A c : ℝ} (hA : 0 ≤ A) (hc : 0 < c) :
    Real.shiftedInverseSquareSeriesBudget A c =
      (1 / c ^ 2) *
        (Real.shiftedReciprocalUnitComplement A c ^ 2 +
          Real.shiftedReciprocalUnitComplement A c) := by
  unfold Real.shiftedInverseSquareSeriesBudget
  have hterm := Real.shiftedInverseSquareTerm_zero_eq_base A c
  have hbudget := Real.shiftedInverseSquareBudget_eq_base hA hc
  have hcNe : c ≠ 0 := ne_of_gt hc
  have hdNe : A + c ≠ 0 :=
    ne_of_gt (Real.shiftedReciprocalUnitDenominator_pos hA hc)
  unfold Real.shiftedReciprocalUnitComplement
  calc
    Real.shiftedInverseSquareTerm A c 0 +
        Real.shiftedInverseSquareBudget A c =
      1 / (A + c) ^ 2 + 1 / (c * (A + c)) :=
        congrArg₂ (fun left right : ℝ => left + right) hterm hbudget
    _ = (1 / c ^ 2) *
        ((c / (A + c)) ^ 2 + c / (A + c)) := by
      have hsquare := Real.one_div_square_mul_self_div_square
        (d := A + c) hcNe
      have hlinear := Real.one_div_square_mul_self_div
        (d := A + c) hcNe
      exact Eq.trans
        (congrArg₂ (fun left right : ℝ => left + right)
          hsquare.symm hlinear.symm)
        (mul_add (1 / c ^ 2)
          ((c / (A + c)) ^ 2) (c / (A + c))).symm

theorem Real.shiftedInverseCubeSeriesBudget_mul_shiftSquare_eq_unitCoordinates
    {A c : ℝ} (hA : 0 ≤ A) (hc : 0 < c) :
    A ^ 2 * Real.shiftedInverseCubeSeriesBudget A c =
      (1 / c) * Real.shiftedReciprocalUnitRatio A c ^ 2 *
        (Real.shiftedReciprocalUnitComplement A c + 1 / 2) := by
  unfold Real.shiftedInverseCubeSeriesBudget
  have hterm := Real.shiftedInverseCubeTerm_zero_eq_base A c
  have hbudget := Real.shiftedInverseCubeBudget_eq_base hA hc
  have hcNe : c ≠ 0 := ne_of_gt hc
  have hdNe : A + c ≠ 0 :=
    ne_of_gt (Real.shiftedReciprocalUnitDenominator_pos hA hc)
  unfold Real.shiftedReciprocalUnitRatio
  unfold Real.shiftedReciprocalUnitComplement
  calc
    A ^ 2 *
        (Real.shiftedInverseCubeTerm A c 0 +
          Real.shiftedInverseCubeBudget A c) =
      A ^ 2 *
        (1 / (A + c) ^ 3 +
          1 / ((2 * c) * (A + c) ^ 2)) :=
        congrArg (fun value : ℝ => A ^ 2 * value)
          (congrArg₂ (fun left right : ℝ => left + right)
            hterm hbudget)
    _ = (1 / c) * (A / (A + c)) ^ 2 *
        (c / (A + c) + 1 / 2) := by
      have hdiscrete := Real.shiftedReciprocalDiscreteTerm_eq_unitCoordinates
        A c (A + c) 2 hcNe
      have hintegral := Real.shiftedReciprocalIntegralTerm_eq_unitCoordinates
        A c (A + c) 2 2
      exact Eq.trans
        (mul_add (A ^ 2) (1 / (A + c) ^ 3)
          (1 / ((2 * c) * (A + c) ^ 2)))
        (Eq.trans
          (congrArg₂ (fun left right : ℝ => left + right)
            hdiscrete hintegral)
          (mul_add ((1 / c) * (A / (A + c)) ^ 2)
            (c / (A + c)) (1 / 2)).symm)

theorem Real.shiftedInverseFourthSeriesBudget_mul_shiftCube_eq_unitCoordinates
    {A c : ℝ} (hA : 0 ≤ A) (hc : 0 < c) :
    A ^ 3 * Real.shiftedInverseFourthSeriesBudget A c =
      (1 / c) * Real.shiftedReciprocalUnitRatio A c ^ 3 *
        (Real.shiftedReciprocalUnitComplement A c + 1 / 3) := by
  unfold Real.shiftedInverseFourthSeriesBudget
  have hterm := Real.shiftedInverseFourthTerm_zero_eq_base A c
  have hbudget := Real.shiftedInverseFourthBudget_eq_base hA hc
  have hcNe : c ≠ 0 := ne_of_gt hc
  have hdNe : A + c ≠ 0 :=
    ne_of_gt (Real.shiftedReciprocalUnitDenominator_pos hA hc)
  unfold Real.shiftedReciprocalUnitRatio
  unfold Real.shiftedReciprocalUnitComplement
  calc
    A ^ 3 *
        (Real.shiftedInverseFourthTerm A c 0 +
          Real.shiftedInverseFourthBudget A c) =
      A ^ 3 *
        (1 / (A + c) ^ 4 +
          1 / ((3 * c) * (A + c) ^ 3)) :=
        congrArg (fun value : ℝ => A ^ 3 * value)
          (congrArg₂ (fun left right : ℝ => left + right)
            hterm hbudget)
    _ = (1 / c) * (A / (A + c)) ^ 3 *
        (c / (A + c) + 1 / 3) := by
      have hdiscrete := Real.shiftedReciprocalDiscreteTerm_eq_unitCoordinates
        A c (A + c) 3 hcNe
      have hintegral := Real.shiftedReciprocalIntegralTerm_eq_unitCoordinates
        A c (A + c) 3 3
      exact Eq.trans
        (mul_add (A ^ 3) (1 / (A + c) ^ 4)
          (1 / ((3 * c) * (A + c) ^ 3)))
        (Eq.trans
          (congrArg₂ (fun left right : ℝ => left + right)
            hdiscrete hintegral)
          (mul_add ((1 / c) * (A / (A + c)) ^ 3)
            (c / (A + c)) (1 / 3)).symm)

/-- The normalized polynomial produced by the complete positive reciprocal
series, before conversion to degree-four Bernstein form. -/
def Real.shiftedReciprocalPositiveNormalizedBudget
    (r y : ℝ) : ℝ :=
  (4 / 3) * (y ^ 2 + y) +
    (2299 / 192) * (r ^ 2 * (y + 1 / 2)) +
    (9317 / 512) * (r ^ 3 * (y + 1 / 3))

def Real.shiftedReciprocalPositiveDegreeFourExpansion
    (r y : ℝ) : ℝ :=
  (4 / 3) *
      ((r ^ 2 * y ^ 2 + 2 * (r * y ^ 3) + y ^ 4) +
        (r ^ 3 * y + 3 * (r ^ 2 * y ^ 2) +
          3 * (r * y ^ 3) + y ^ 4)) +
    (2299 / 192) *
      ((r ^ 3 * y + r ^ 2 * y ^ 2) +
        (1 / 2) * (r ^ 4 + 2 * (r ^ 3 * y) + r ^ 2 * y ^ 2)) +
    (9317 / 512) *
      (r ^ 3 * y + (1 / 3) * (r ^ 4 + r ^ 3 * y))

def Real.reverseQuarticMonomial (r y : ℝ) (k : Fin 5) : ℝ :=
  Fin.cases (r ^ 4)
    (fun k₁ : Fin 4 =>
      Fin.cases (r ^ 3 * y)
        (fun k₂ : Fin 3 =>
          Fin.cases (r ^ 2 * y ^ 2)
            (fun k₃ : Fin 2 =>
              Fin.cases (r * y ^ 3)
                (fun _k₄ : Fin 1 => y ^ 4)
                k₃)
            k₂)
        k₁)
    k

def Real.reverseQuarticLinearForm
    (coefficients : Fin 5 → ℝ) (r y : ℝ) : ℝ :=
  ∑ k : Fin 5, coefficients k * Real.reverseQuarticMonomial r y k

def Real.finFive
    (a₀ a₁ a₂ a₃ a₄ : ℝ) : Fin 5 → ℝ :=
  Fin.cases a₀
    (fun k₁ : Fin 4 =>
      Fin.cases a₁
        (fun k₂ : Fin 3 =>
          Fin.cases a₂
            (fun k₃ : Fin 2 => Fin.cases a₃ (fun _k₄ : Fin 1 => a₄) k₃)
            k₂)
        k₁)

theorem Real.reverseQuarticLinearForm_add
    (left right : Fin 5 → ℝ) (r y : ℝ) :
    Real.reverseQuarticLinearForm (fun k => left k + right k) r y =
      Real.reverseQuarticLinearForm left r y +
        Real.reverseQuarticLinearForm right r y := by
  unfold Real.reverseQuarticLinearForm
  have hpointwise :
      (∑ k : Fin 5,
          (left k + right k) * Real.reverseQuarticMonomial r y k) =
        ∑ k : Fin 5,
          (left k * Real.reverseQuarticMonomial r y k +
            right k * Real.reverseQuarticMonomial r y k) := by
    exact Finset.sum_congr rfl
      (fun k _hk => add_mul (left k) (right k)
        (Real.reverseQuarticMonomial r y k))
  exact Eq.trans hpointwise Finset.sum_add_distrib

theorem Real.reverseQuarticLinearForm_scalar
    (scalar : ℝ) (coefficients : Fin 5 → ℝ) (r y : ℝ) :
    Real.reverseQuarticLinearForm (fun k => scalar * coefficients k) r y =
      scalar * Real.reverseQuarticLinearForm coefficients r y := by
  unfold Real.reverseQuarticLinearForm
  have hpointwise :
      (∑ k : Fin 5,
          (scalar * coefficients k) * Real.reverseQuarticMonomial r y k) =
        ∑ k : Fin 5,
          scalar * (coefficients k * Real.reverseQuarticMonomial r y k) := by
    exact Finset.sum_congr rfl
      (fun k _hk =>
        mul_assoc scalar (coefficients k)
          (Real.reverseQuarticMonomial r y k))
  exact Eq.trans hpointwise (Finset.mul_sum Finset.univ _ scalar).symm

theorem Real.reverseQuarticLinearForm_eq_five_terms
    (coefficients : Fin 5 → ℝ) (r y : ℝ) :
    Real.reverseQuarticLinearForm coefficients r y =
      coefficients 0 * r ^ 4 +
        coefficients 1 * (r ^ 3 * y) +
        coefficients 2 * (r ^ 2 * y ^ 2) +
        coefficients 3 * (r * y ^ 3) +
        coefficients 4 * y ^ 4 := by
  unfold Real.reverseQuarticLinearForm
  have hsum := Real.sum_fin_five
    (fun k : Fin 5 => coefficients k * Real.reverseQuarticMonomial r y k)
  exact hsum

theorem Real.reverseQuarticLinearForm_finFive
    (a₀ a₁ a₂ a₃ a₄ r y : ℝ) :
    Real.reverseQuarticLinearForm (Real.finFive a₀ a₁ a₂ a₃ a₄) r y =
      a₀ * r ^ 4 + a₁ * (r ^ 3 * y) + a₂ * (r ^ 2 * y ^ 2) +
        a₃ * (r * y ^ 3) + a₄ * y ^ 4 := by
  exact Real.reverseQuarticLinearForm_eq_five_terms
    (Real.finFive a₀ a₁ a₂ a₃ a₄) r y

def Real.reverseYSquareCoefficients : Fin 5 → ℝ :=
  Real.finFive 0 0 1 2 1

def Real.reverseYCoefficients : Fin 5 → ℝ :=
  Real.finFive 0 1 3 3 1

def Real.reverseRSquareYCoefficients : Fin 5 → ℝ :=
  Real.finFive 0 1 1 0 0

def Real.reverseRSquareCoefficients : Fin 5 → ℝ :=
  Real.finFive 1 2 1 0 0

def Real.reverseRCubeYCoefficients : Fin 5 → ℝ :=
  Real.finFive 0 1 0 0 0

def Real.reverseRCubeCoefficients : Fin 5 → ℝ :=
  Real.finFive 1 1 0 0 0

theorem Real.reverseQuarticLinearForm_ySquare (r y : ℝ) :
    Real.reverseQuarticLinearForm Real.reverseYSquareCoefficients r y =
      r ^ 2 * y ^ 2 + 2 * (r * y ^ 3) + y ^ 4 := by
  unfold Real.reverseYSquareCoefficients
  have hfive := Real.reverseQuarticLinearForm_finFive 0 0 1 2 1 r y
  have hterms :
      (0 : ℝ) * r ^ 4 + 0 * (r ^ 3 * y) + 1 * (r ^ 2 * y ^ 2) +
          2 * (r * y ^ 3) + 1 * y ^ 4 =
        0 + 0 + (r ^ 2 * y ^ 2) + 2 * (r * y ^ 3) + y ^ 4 :=
    congrArg₂ (fun left right : ℝ => left + right)
      (congrArg₂ (fun left right : ℝ => left + right)
        (congrArg₂ (fun left right : ℝ => left + right)
          (congrArg₂ (fun left right : ℝ => left + right)
            (zero_mul (r ^ 4)) (zero_mul (r ^ 3 * y)))
          (one_mul (r ^ 2 * y ^ 2)))
        rfl)
      (one_mul (y ^ 4))
  have hzero :
      0 + 0 + (r ^ 2 * y ^ 2) = r ^ 2 * y ^ 2 := by
    exact Eq.trans
      (congrArg (fun value : ℝ => value + r ^ 2 * y ^ 2) (zero_add 0))
      (zero_add (r ^ 2 * y ^ 2))
  exact Eq.trans hfive
    (Eq.trans hterms
      (congrArg (fun value : ℝ => value + 2 * (r * y ^ 3) + y ^ 4) hzero))

theorem Real.reverseQuarticLinearForm_y (r y : ℝ) :
    Real.reverseQuarticLinearForm Real.reverseYCoefficients r y =
      r ^ 3 * y + 3 * (r ^ 2 * y ^ 2) + 3 * (r * y ^ 3) + y ^ 4 := by
  unfold Real.reverseYCoefficients
  have hfive := Real.reverseQuarticLinearForm_finFive 0 1 3 3 1 r y
  have hterms :
      (0 : ℝ) * r ^ 4 + 1 * (r ^ 3 * y) + 3 * (r ^ 2 * y ^ 2) +
          3 * (r * y ^ 3) + 1 * y ^ 4 =
        0 + (r ^ 3 * y) + 3 * (r ^ 2 * y ^ 2) +
          3 * (r * y ^ 3) + y ^ 4 :=
    congrArg₂ (fun left right : ℝ => left + right)
      (congrArg₂ (fun left right : ℝ => left + right)
        (congrArg₂ (fun left right : ℝ => left + right)
          (congrArg₂ (fun left right : ℝ => left + right)
            (zero_mul (r ^ 4)) (one_mul (r ^ 3 * y)))
          rfl)
        rfl)
      (one_mul (y ^ 4))
  exact Eq.trans hfive
    (Eq.trans hterms
      (congrArg (fun value : ℝ =>
          value + 3 * (r ^ 2 * y ^ 2) + 3 * (r * y ^ 3) + y ^ 4)
        (zero_add (r ^ 3 * y))))

theorem Real.reverseQuarticLinearForm_rSquareY (r y : ℝ) :
    Real.reverseQuarticLinearForm Real.reverseRSquareYCoefficients r y =
      r ^ 3 * y + r ^ 2 * y ^ 2 := by
  unfold Real.reverseRSquareYCoefficients
  have hfive := Real.reverseQuarticLinearForm_finFive 0 1 1 0 0 r y
  have hterms :
      (0 : ℝ) * r ^ 4 + 1 * (r ^ 3 * y) + 1 * (r ^ 2 * y ^ 2) +
          0 * (r * y ^ 3) + 0 * y ^ 4 =
        0 + (r ^ 3 * y) + (r ^ 2 * y ^ 2) + 0 + 0 :=
    congrArg₂ (fun left right : ℝ => left + right)
      (congrArg₂ (fun left right : ℝ => left + right)
        (congrArg₂ (fun left right : ℝ => left + right)
          (congrArg₂ (fun left right : ℝ => left + right)
            (zero_mul (r ^ 4)) (one_mul (r ^ 3 * y)))
          (one_mul (r ^ 2 * y ^ 2)))
        (zero_mul (r * y ^ 3)))
      (zero_mul (y ^ 4))
  have hzeroLeft : 0 + (r ^ 3 * y) = r ^ 3 * y := zero_add _
  have hzeroRight :
      r ^ 3 * y + r ^ 2 * y ^ 2 + 0 + 0 =
        r ^ 3 * y + r ^ 2 * y ^ 2 :=
    Eq.trans (congrArg (fun value : ℝ => value + 0) (add_zero _)) (add_zero _)
  exact Eq.trans hfive
    (Eq.trans hterms
      (Eq.trans
        (congrArg (fun value : ℝ => value + r ^ 2 * y ^ 2 + 0 + 0)
          hzeroLeft)
        hzeroRight))

theorem Real.reverseQuarticLinearForm_rSquare (r y : ℝ) :
    Real.reverseQuarticLinearForm Real.reverseRSquareCoefficients r y =
      r ^ 4 + 2 * (r ^ 3 * y) + r ^ 2 * y ^ 2 := by
  unfold Real.reverseRSquareCoefficients
  have hfive := Real.reverseQuarticLinearForm_finFive 1 2 1 0 0 r y
  have hterms :
      (1 : ℝ) * r ^ 4 + 2 * (r ^ 3 * y) + 1 * (r ^ 2 * y ^ 2) +
          0 * (r * y ^ 3) + 0 * y ^ 4 =
        r ^ 4 + 2 * (r ^ 3 * y) + (r ^ 2 * y ^ 2) + 0 + 0 :=
    congrArg₂ (fun left right : ℝ => left + right)
      (congrArg₂ (fun left right : ℝ => left + right)
        (congrArg₂ (fun left right : ℝ => left + right)
          (congrArg₂ (fun left right : ℝ => left + right)
            (one_mul (r ^ 4)) rfl)
          (one_mul (r ^ 2 * y ^ 2)))
        (zero_mul (r * y ^ 3)))
      (zero_mul (y ^ 4))
  exact Eq.trans hfive
    (Eq.trans hterms
      (Eq.trans (congrArg (fun value : ℝ => value + 0) (add_zero _)) (add_zero _)))

theorem Real.reverseQuarticLinearForm_rCubeY (r y : ℝ) :
    Real.reverseQuarticLinearForm Real.reverseRCubeYCoefficients r y =
      r ^ 3 * y := by
  unfold Real.reverseRCubeYCoefficients
  have hfive := Real.reverseQuarticLinearForm_finFive 0 1 0 0 0 r y
  have hterms :
      (0 : ℝ) * r ^ 4 + 1 * (r ^ 3 * y) + 0 * (r ^ 2 * y ^ 2) +
          0 * (r * y ^ 3) + 0 * y ^ 4 =
        0 + (r ^ 3 * y) + 0 + 0 + 0 :=
    congrArg₂ (fun left right : ℝ => left + right)
      (congrArg₂ (fun left right : ℝ => left + right)
        (congrArg₂ (fun left right : ℝ => left + right)
          (congrArg₂ (fun left right : ℝ => left + right)
            (zero_mul (r ^ 4)) (one_mul (r ^ 3 * y)))
          (zero_mul (r ^ 2 * y ^ 2)))
        (zero_mul (r * y ^ 3)))
      (zero_mul (y ^ 4))
  have hzero₀ : 0 + r ^ 3 * y = r ^ 3 * y := zero_add _
  have hzero₁ : r ^ 3 * y + 0 = r ^ 3 * y := add_zero _
  exact Eq.trans hfive
    (Eq.trans hterms
      (Eq.trans
        (congrArg (fun value : ℝ => value + 0 + 0 + 0) hzero₀)
        (Eq.trans
          (congrArg (fun value : ℝ => value + 0 + 0) hzero₁)
          (Eq.trans (congrArg (fun value : ℝ => value + 0) hzero₁) hzero₁))))

theorem Real.reverseQuarticLinearForm_rCube (r y : ℝ) :
    Real.reverseQuarticLinearForm Real.reverseRCubeCoefficients r y =
      r ^ 4 + r ^ 3 * y := by
  unfold Real.reverseRCubeCoefficients
  have hfive := Real.reverseQuarticLinearForm_finFive 1 1 0 0 0 r y
  have hterms :
      (1 : ℝ) * r ^ 4 + 1 * (r ^ 3 * y) + 0 * (r ^ 2 * y ^ 2) +
          0 * (r * y ^ 3) + 0 * y ^ 4 =
        r ^ 4 + (r ^ 3 * y) + 0 + 0 + 0 :=
    congrArg₂ (fun left right : ℝ => left + right)
      (congrArg₂ (fun left right : ℝ => left + right)
        (congrArg₂ (fun left right : ℝ => left + right)
          (congrArg₂ (fun left right : ℝ => left + right)
            (one_mul (r ^ 4)) (one_mul (r ^ 3 * y)))
          (zero_mul (r ^ 2 * y ^ 2)))
        (zero_mul (r * y ^ 3)))
      (zero_mul (y ^ 4))
  have hzero : r ^ 4 + r ^ 3 * y + 0 = r ^ 4 + r ^ 3 * y := add_zero _
  exact Eq.trans hfive
    (Eq.trans hterms
      (Eq.trans
        (congrArg (fun value : ℝ => value + 0 + 0) hzero)
        (Eq.trans (congrArg (fun value : ℝ => value + 0) hzero) hzero)))

def Real.reverseSquarePacketCoefficients (k : Fin 5) : ℝ :=
  Real.reverseYSquareCoefficients k + Real.reverseYCoefficients k

def Real.reverseCubePacketCoefficients (k : Fin 5) : ℝ :=
  Real.reverseRSquareYCoefficients k +
    (1 / 2) * Real.reverseRSquareCoefficients k

def Real.reverseFourthPacketCoefficients (k : Fin 5) : ℝ :=
  Real.reverseRCubeYCoefficients k +
    (1 / 3) * Real.reverseRCubeCoefficients k

def Real.shiftedReciprocalPositiveDegreeFourCoefficients (k : Fin 5) : ℝ :=
  (4 / 3) * Real.reverseSquarePacketCoefficients k +
    (2299 / 192) * Real.reverseCubePacketCoefficients k +
    (9317 / 512) * Real.reverseFourthPacketCoefficients k

theorem Real.reverseQuarticLinearForm_squarePacket (r y : ℝ) :
    Real.reverseQuarticLinearForm Real.reverseSquarePacketCoefficients r y =
      (r ^ 2 * y ^ 2 + 2 * (r * y ^ 3) + y ^ 4) +
        (r ^ 3 * y + 3 * (r ^ 2 * y ^ 2) +
          3 * (r * y ^ 3) + y ^ 4) := by
  unfold Real.reverseSquarePacketCoefficients
  exact Eq.trans
    (Real.reverseQuarticLinearForm_add
      Real.reverseYSquareCoefficients Real.reverseYCoefficients r y)
    (congrArg₂ (fun left right : ℝ => left + right)
      (Real.reverseQuarticLinearForm_ySquare r y)
      (Real.reverseQuarticLinearForm_y r y))

theorem Real.reverseQuarticLinearForm_cubePacket (r y : ℝ) :
    Real.reverseQuarticLinearForm Real.reverseCubePacketCoefficients r y =
      (r ^ 3 * y + r ^ 2 * y ^ 2) +
        (1 / 2) * (r ^ 4 + 2 * (r ^ 3 * y) + r ^ 2 * y ^ 2) := by
  unfold Real.reverseCubePacketCoefficients
  have hscalar := Real.reverseQuarticLinearForm_scalar
    (1 / 2) Real.reverseRSquareCoefficients r y
  have hscaled :
      Real.reverseQuarticLinearForm
          (fun k => (1 / 2) * Real.reverseRSquareCoefficients k) r y =
        (1 / 2) * (r ^ 4 + 2 * (r ^ 3 * y) + r ^ 2 * y ^ 2) :=
    Eq.trans hscalar
      (congrArg (fun value : ℝ => (1 / 2) * value)
        (Real.reverseQuarticLinearForm_rSquare r y))
  exact Eq.trans
    (Real.reverseQuarticLinearForm_add
      Real.reverseRSquareYCoefficients
      (fun k => (1 / 2) * Real.reverseRSquareCoefficients k) r y)
    (congrArg₂ (fun left right : ℝ => left + right)
      (Real.reverseQuarticLinearForm_rSquareY r y) hscaled)

theorem Real.reverseQuarticLinearForm_fourthPacket (r y : ℝ) :
    Real.reverseQuarticLinearForm Real.reverseFourthPacketCoefficients r y =
      r ^ 3 * y + (1 / 3) * (r ^ 4 + r ^ 3 * y) := by
  unfold Real.reverseFourthPacketCoefficients
  have hscalar := Real.reverseQuarticLinearForm_scalar
    (1 / 3) Real.reverseRCubeCoefficients r y
  have hscaled :
      Real.reverseQuarticLinearForm
          (fun k => (1 / 3) * Real.reverseRCubeCoefficients k) r y =
        (1 / 3) * (r ^ 4 + r ^ 3 * y) :=
    Eq.trans hscalar
      (congrArg (fun value : ℝ => (1 / 3) * value)
        (Real.reverseQuarticLinearForm_rCube r y))
  exact Eq.trans
    (Real.reverseQuarticLinearForm_add
      Real.reverseRCubeYCoefficients
      (fun k => (1 / 3) * Real.reverseRCubeCoefficients k) r y)
    (congrArg₂ (fun left right : ℝ => left + right)
      (Real.reverseQuarticLinearForm_rCubeY r y) hscaled)

theorem Real.reverseQuarticLinearForm_positiveDegreeFour (r y : ℝ) :
    Real.reverseQuarticLinearForm
        Real.shiftedReciprocalPositiveDegreeFourCoefficients r y =
      Real.shiftedReciprocalPositiveDegreeFourExpansion r y := by
  unfold Real.shiftedReciprocalPositiveDegreeFourCoefficients
  unfold Real.shiftedReciprocalPositiveDegreeFourExpansion
  have hsquareScalar := Real.reverseQuarticLinearForm_scalar
    (4 / 3) Real.reverseSquarePacketCoefficients r y
  have hcubeScalar := Real.reverseQuarticLinearForm_scalar
    (2299 / 192) Real.reverseCubePacketCoefficients r y
  have hfourthScalar := Real.reverseQuarticLinearForm_scalar
    (9317 / 512) Real.reverseFourthPacketCoefficients r y
  have hfirstAdd := Real.reverseQuarticLinearForm_add
    (fun k => (4 / 3) * Real.reverseSquarePacketCoefficients k)
    (fun k => (2299 / 192) * Real.reverseCubePacketCoefficients k) r y
  have hallAdd := Real.reverseQuarticLinearForm_add
    (fun k =>
      (4 / 3) * Real.reverseSquarePacketCoefficients k +
        (2299 / 192) * Real.reverseCubePacketCoefficients k)
    (fun k => (9317 / 512) * Real.reverseFourthPacketCoefficients k) r y
  have hlinear :
      Real.reverseQuarticLinearForm
          (fun k =>
            (4 / 3) * Real.reverseSquarePacketCoefficients k +
              (2299 / 192) * Real.reverseCubePacketCoefficients k +
              (9317 / 512) * Real.reverseFourthPacketCoefficients k) r y =
        (4 / 3) *
            Real.reverseQuarticLinearForm Real.reverseSquarePacketCoefficients r y +
          (2299 / 192) *
            Real.reverseQuarticLinearForm Real.reverseCubePacketCoefficients r y +
          (9317 / 512) *
            Real.reverseQuarticLinearForm Real.reverseFourthPacketCoefficients r y := by
    exact Eq.trans hallAdd
      (congrArg₂ (fun left right : ℝ => left + right)
        (Eq.trans hfirstAdd
          (congrArg₂ (fun left right : ℝ => left + right)
            hsquareScalar hcubeScalar))
        hfourthScalar)
  exact Eq.trans hlinear
    (congrArg₂ (fun left right : ℝ => left + right)
      (congrArg₂ (fun left right : ℝ => left + right)
        (congrArg (fun value : ℝ => (4 / 3) * value)
          (Real.reverseQuarticLinearForm_squarePacket r y))
        (congrArg (fun value : ℝ => (2299 / 192) * value)
          (Real.reverseQuarticLinearForm_cubePacket r y)))
      (congrArg (fun value : ℝ => (9317 / 512) * value)
        (Real.reverseQuarticLinearForm_fourthPacket r y)))

theorem Real.positiveDegreeFourCoefficient_zero :
    (2299 / 192 : ℝ) * (1 / 2) +
        (9317 / 512 : ℝ) * (1 / 3) =
      6171 / 512 := by
  have hfirst : (2299 / 192 : ℝ) * (1 / 2) = 2299 / 384 :=
    Eq.trans (div_mul_div_comm 2299 192 1 2)
      (congrArg₂ (fun numerator denominator : ℝ => numerator / denominator)
        (mul_one 2299)
        (shiftedReciprocal_realOfNat_mul_eq_of_nat_eq 192 2 384 rfl))
  have hsecond : (9317 / 512 : ℝ) * (1 / 3) = 9317 / 1536 :=
    Eq.trans (div_mul_div_comm 9317 512 1 3)
      (congrArg₂ (fun numerator denominator : ℝ => numerator / denominator)
        (mul_one 9317)
        (shiftedReciprocal_realOfNat_mul_eq_of_nat_eq 512 3 1536 rfl))
  have hfirstCommon : (2299 / 384 : ℝ) = 9196 / 1536 :=
    shiftedReciprocal_natFraction_eq_of_cross
      2299 384 9196 1536
      (Nat.zero_lt_succ 383) (Nat.zero_lt_succ 1535) rfl
  have hsum : (9196 / 1536 : ℝ) + 9317 / 1536 = 18513 / 1536 := by
    exact Eq.trans (div_add_div_same 9196 9317 1536)
      (congrArg (fun numerator : ℝ => numerator / 1536)
        (shiftedReciprocal_realOfNat_add_eq_of_nat_eq 9196 9317 18513 rfl))
  have hreduce : (18513 / 1536 : ℝ) = 6171 / 512 :=
    shiftedReciprocal_natFraction_eq_of_cross
      18513 1536 6171 512
      (Nat.zero_lt_succ 1535) (Nat.zero_lt_succ 511) rfl
  exact Eq.trans
    (congrArg₂ (fun left right : ℝ => left + right)
      (Eq.trans hfirst hfirstCommon) hsecond)
    (Eq.trans hsum hreduce)

theorem Real.positiveDegreeFourCoefficient_one :
    (4 / 3 : ℝ) + (2299 / 192) * 2 +
        (9317 / 512) * (4 / 3) =
      4 * (19025 / 1536) := by
  have hfirst : (4 / 3 : ℝ) = 2048 / 1536 :=
    shiftedReciprocal_natFraction_eq_of_cross
      4 3 2048 1536
      (Nat.zero_lt_succ 2) (Nat.zero_lt_succ 1535) rfl
  have hsecondRaw : (2299 / 192 : ℝ) * 2 = 4598 / 192 := by
    have hmul : (2299 / 192 : ℝ) * (2 / 1) = 4598 / 192 :=
      Eq.trans (div_mul_div_comm 2299 192 2 1)
        (congrArg₂ (fun numerator denominator : ℝ => numerator / denominator)
          (shiftedReciprocal_realOfNat_mul_eq_of_nat_eq 2299 2 4598 rfl)
          (mul_one 192))
    exact Eq.trans
      (congrArg (fun value : ℝ => (2299 / 192) * value) (div_one 2).symm)
      hmul
  have hsecond : (2299 / 192 : ℝ) * 2 = 36784 / 1536 :=
    Eq.trans hsecondRaw
      (shiftedReciprocal_natFraction_eq_of_cross
        4598 192 36784 1536
        (Nat.zero_lt_succ 191) (Nat.zero_lt_succ 1535) rfl)
  have hthird : (9317 / 512 : ℝ) * (4 / 3) = 37268 / 1536 :=
    Eq.trans (div_mul_div_comm 9317 512 4 3)
      (congrArg₂ (fun numerator denominator : ℝ => numerator / denominator)
        (shiftedReciprocal_realOfNat_mul_eq_of_nat_eq 9317 4 37268 rfl)
        (shiftedReciprocal_realOfNat_mul_eq_of_nat_eq 512 3 1536 rfl))
  have hfirstTwo : (2048 / 1536 : ℝ) + 36784 / 1536 = 38832 / 1536 := by
    exact Eq.trans (div_add_div_same 2048 36784 1536)
      (congrArg (fun numerator : ℝ => numerator / 1536)
        (shiftedReciprocal_realOfNat_add_eq_of_nat_eq 2048 36784 38832 rfl))
  have hall : (38832 / 1536 : ℝ) + 37268 / 1536 = 76100 / 1536 := by
    exact Eq.trans (div_add_div_same 38832 37268 1536)
      (congrArg (fun numerator : ℝ => numerator / 1536)
        (shiftedReciprocal_realOfNat_add_eq_of_nat_eq 38832 37268 76100 rfl))
  have hright : (4 : ℝ) * (19025 / 1536) = 76100 / 1536 := by
    exact Eq.trans (mul_div_assoc 4 19025 1536).symm
      (congrArg (fun numerator : ℝ => numerator / 1536)
        (shiftedReciprocal_realOfNat_mul_eq_of_nat_eq 4 19025 76100 rfl))
  exact Eq.trans
    (congrArg₂ (fun left right : ℝ => left + right)
      (congrArg₂ (fun left right : ℝ => left + right) hfirst hsecond)
      hthird)
    (Eq.trans
      (congrArg (fun value : ℝ => value + 37268 / 1536) hfirstTwo)
      (Eq.trans hall hright.symm))

theorem Real.positiveDegreeFourCoefficient_two :
    (4 / 3 : ℝ) * 4 + (2299 / 192) * (3 / 2) =
      6 * (8945 / 2304) := by
  have hfirstRaw : (4 / 3 : ℝ) * 4 = 16 / 3 := by
    have hmul : (4 / 3 : ℝ) * (4 / 1) = 16 / 3 :=
      Eq.trans (div_mul_div_comm 4 3 4 1)
        (congrArg₂ (fun numerator denominator : ℝ => numerator / denominator)
          (shiftedReciprocal_realOfNat_mul_eq_of_nat_eq 4 4 16 rfl)
          (mul_one 3))
    exact Eq.trans
      (congrArg (fun value : ℝ => (4 / 3) * value) (div_one 4).symm)
      hmul
  have hfirst : (4 / 3 : ℝ) * 4 = 2048 / 384 :=
    Eq.trans hfirstRaw
      (shiftedReciprocal_natFraction_eq_of_cross
        16 3 2048 384
        (Nat.zero_lt_succ 2) (Nat.zero_lt_succ 383) rfl)
  have hsecond : (2299 / 192 : ℝ) * (3 / 2) = 6897 / 384 :=
    Eq.trans (div_mul_div_comm 2299 192 3 2)
      (congrArg₂ (fun numerator denominator : ℝ => numerator / denominator)
        (shiftedReciprocal_realOfNat_mul_eq_of_nat_eq 2299 3 6897 rfl)
        (shiftedReciprocal_realOfNat_mul_eq_of_nat_eq 192 2 384 rfl))
  have hsum : (2048 / 384 : ℝ) + 6897 / 384 = 8945 / 384 := by
    exact Eq.trans (div_add_div_same 2048 6897 384)
      (congrArg (fun numerator : ℝ => numerator / 384)
        (shiftedReciprocal_realOfNat_add_eq_of_nat_eq 2048 6897 8945 rfl))
  have hrightRaw : (6 : ℝ) * (8945 / 2304) = 53670 / 2304 := by
    exact Eq.trans (mul_div_assoc 6 8945 2304).symm
      (congrArg (fun numerator : ℝ => numerator / 2304)
        (shiftedReciprocal_realOfNat_mul_eq_of_nat_eq 6 8945 53670 rfl))
  have hright : (6 : ℝ) * (8945 / 2304) = 8945 / 384 :=
    Eq.trans hrightRaw
      (shiftedReciprocal_natFraction_eq_of_cross
        53670 2304 8945 384
        (Nat.zero_lt_succ 2303) (Nat.zero_lt_succ 383) rfl)
  exact Eq.trans
    (congrArg₂ (fun left right : ℝ => left + right) hfirst hsecond)
    (Eq.trans hsum hright.symm)

theorem Real.positiveDegreeFourCoefficient_three :
    (4 / 3 : ℝ) * 5 = 4 * (5 / 3) := by
  exact Eq.trans (div_mul_eq_mul_div 4 3 5)
    (mul_div_assoc 4 5 3)

theorem Real.positiveDegreeFourCoefficient_four :
    (4 / 3 : ℝ) * 2 = 8 / 3 := by
  exact Eq.trans (div_mul_eq_mul_div 4 3 2)
    (congrArg (fun numerator : ℝ => numerator / 3)
      (shiftedReciprocal_realOfNat_mul_eq_of_nat_eq 4 2 8 rfl))

theorem Real.one_add_one_half : (1 : ℝ) + 1 / 2 = 3 / 2 := by
  have htwoNe : (2 : ℝ) ≠ 0 :=
    ne_of_gt (Nat.cast_pos.mpr (Nat.zero_lt_succ 1))
  have hone : (1 : ℝ) = 2 / 2 := (div_self htwoNe).symm
  exact Eq.trans (congrArg (fun value : ℝ => value + 1 / 2) hone)
    (Eq.trans (div_add_div_same 2 1 2)
      (congrArg (fun numerator : ℝ => numerator / 2)
        two_add_one_eq_three))

theorem Real.one_add_one_third : (1 : ℝ) + 1 / 3 = 4 / 3 := by
  have hthreeNe : (3 : ℝ) ≠ 0 :=
    ne_of_gt (Nat.cast_pos.mpr (Nat.zero_lt_succ 2))
  have hone : (1 : ℝ) = 3 / 3 := (div_self hthreeNe).symm
  exact Eq.trans (congrArg (fun value : ℝ => value + 1 / 3) hone)
    (Eq.trans (div_add_div_same 3 1 3)
      (congrArg (fun numerator : ℝ => numerator / 3)
        three_add_one_eq_four))

theorem Real.reverseSquarePacketCoefficients_eq_finFive :
    Real.reverseSquarePacketCoefficients = Real.finFive 0 1 4 5 2 := by
  unfold Real.reverseSquarePacketCoefficients
  unfold Real.reverseYSquareCoefficients
  unfold Real.reverseYCoefficients
  exact funext
    (fun k : Fin 5 =>
      Fin.cases (zero_add 0)
        (fun k₁ : Fin 4 =>
          Fin.cases (zero_add 1)
            (fun k₂ : Fin 3 =>
              Fin.cases
                (Eq.trans (add_comm 1 3) three_add_one_eq_four)
                (fun k₃ : Fin 2 =>
                  Fin.cases
                    shiftedReciprocal_two_add_three_eq_five
                    (fun _k₄ : Fin 1 =>
                      one_add_one_eq_two)
                    k₃)
                k₂)
            k₁)
        k)

theorem Real.reverseCubePacketCoefficients_eq_finFive :
    Real.reverseCubePacketCoefficients = Real.finFive (1 / 2) 2 (3 / 2) 0 0 := by
  unfold Real.reverseCubePacketCoefficients
  unfold Real.reverseRSquareYCoefficients
  unfold Real.reverseRSquareCoefficients
  have hzero : (0 : ℝ) + (1 / 2) * 0 = 0 :=
    Eq.trans (congrArg (fun value : ℝ => 0 + value) (mul_zero (1 / 2)))
      (zero_add 0)
  exact funext
    (fun k : Fin 5 =>
      Fin.cases
        (Eq.trans
          (congrArg (fun value : ℝ => 0 + value) (mul_one (1 / 2)))
          (zero_add (1 / 2)))
        (fun k₁ : Fin 4 =>
          Fin.cases
            (Eq.trans
              (congrArg (fun value : ℝ => 1 + value) Real.one_half_mul_two)
              (one_add_one_eq_two))
            (fun k₂ : Fin 3 =>
              Fin.cases
                (Eq.trans
                  (congrArg (fun value : ℝ => 1 + value) (mul_one (1 / 2)))
                  Real.one_add_one_half)
                (fun k₃ : Fin 2 => Fin.cases hzero (fun _k₄ : Fin 1 => hzero) k₃)
                k₂)
            k₁)
        k)

theorem Real.reverseFourthPacketCoefficients_eq_finFive :
    Real.reverseFourthPacketCoefficients = Real.finFive (1 / 3) (4 / 3) 0 0 0 := by
  unfold Real.reverseFourthPacketCoefficients
  unfold Real.reverseRCubeYCoefficients
  unfold Real.reverseRCubeCoefficients
  have hzero : (0 : ℝ) + (1 / 3) * 0 = 0 :=
    Eq.trans (congrArg (fun value : ℝ => 0 + value) (mul_zero (1 / 3)))
      (zero_add 0)
  exact funext
    (fun k : Fin 5 =>
      Fin.cases
        (Eq.trans
          (congrArg (fun value : ℝ => 0 + value) (mul_one (1 / 3)))
          (zero_add (1 / 3)))
        (fun k₁ : Fin 4 =>
          Fin.cases
            (Eq.trans
              (congrArg (fun value : ℝ => 1 + value) (mul_one (1 / 3)))
              Real.one_add_one_third)
            (fun k₂ : Fin 3 =>
              Fin.cases hzero (fun k₃ : Fin 2 => Fin.cases hzero (fun _ : Fin 1 => hzero) k₃) k₂)
            k₁)
        k)

def Real.reversePositiveQuarticEnvelopeCoefficients : Fin 5 → ℝ :=
  Real.finFive (6171 / 512) (4 * (19025 / 1536))
    (6 * (8945 / 2304)) (4 * (5 / 3)) (8 / 3)

theorem Real.shiftedReciprocalPositiveDegreeFourCoefficients_eq_envelope :
    Real.shiftedReciprocalPositiveDegreeFourCoefficients =
      Real.reversePositiveQuarticEnvelopeCoefficients := by
  have hsquare := Real.reverseSquarePacketCoefficients_eq_finFive
  have hcube := Real.reverseCubePacketCoefficients_eq_finFive
  have hfourth := Real.reverseFourthPacketCoefficients_eq_finFive
  exact funext
    (fun k : Fin 5 =>
      have hcomponents :
          Real.shiftedReciprocalPositiveDegreeFourCoefficients k =
            (4 / 3) * (Real.finFive 0 1 4 5 2 k) +
              (2299 / 192) * (Real.finFive (1 / 2) 2 (3 / 2) 0 0 k) +
              (9317 / 512) * (Real.finFive (1 / 3) (4 / 3) 0 0 0 k) := by
        unfold Real.shiftedReciprocalPositiveDegreeFourCoefficients
        exact congrArg₂ (fun left right : ℝ => left + right)
          (congrArg₂ (fun left right : ℝ => left + right)
            (congrArg (fun value : ℝ => (4 / 3) * value)
              (congrFun hsquare k))
            (congrArg (fun value : ℝ => (2299 / 192) * value)
              (congrFun hcube k)))
          (congrArg (fun value : ℝ => (9317 / 512) * value)
            (congrFun hfourth k))
      Eq.trans hcomponents
        (Fin.cases
          (by
            have hzero : (4 / 3 : ℝ) * 0 = 0 := mul_zero _
            exact Eq.trans
              (congrArg (fun value : ℝ =>
                  value + (2299 / 192) * (1 / 2) +
                    (9317 / 512) * (1 / 3)) hzero)
              (Eq.trans
                (congrArg (fun value : ℝ =>
                    value + (9317 / 512) * (1 / 3))
                  (zero_add ((2299 / 192) * (1 / 2))))
                Real.positiveDegreeFourCoefficient_zero))
          (fun k₁ : Fin 4 =>
            Fin.cases
              (by
                exact Eq.trans
                  (congrArg (fun value : ℝ =>
                      value + (2299 / 192) * 2 +
                        (9317 / 512) * (4 / 3))
                    (mul_one (4 / 3)))
                  Real.positiveDegreeFourCoefficient_one)
              (fun k₂ : Fin 3 =>
                Fin.cases
                  (by
                    have hzero : (9317 / 512 : ℝ) * 0 = 0 := mul_zero _
                    exact Eq.trans
                      (congrArg (fun value : ℝ =>
                          (4 / 3) * 4 + (2299 / 192) * (3 / 2) + value)
                        hzero)
                      (Eq.trans
                        (add_zero ((4 / 3) * 4 + (2299 / 192) * (3 / 2)))
                        Real.positiveDegreeFourCoefficient_two))
                  (fun k₃ : Fin 2 =>
                    Fin.cases
                      (by
                        have hsecond : (2299 / 192 : ℝ) * 0 = 0 := mul_zero _
                        have hthird : (9317 / 512 : ℝ) * 0 = 0 := mul_zero _
                        exact Eq.trans
                          (congrArg₂ (fun left right : ℝ => left + right)
                            (congrArg (fun value : ℝ => (4 / 3) * 5 + value) hsecond)
                            hthird)
                          (Eq.trans
                            (congrArg (fun value : ℝ => value + 0)
                              (add_zero ((4 / 3) * 5)))
                            (Eq.trans (add_zero ((4 / 3) * 5))
                              Real.positiveDegreeFourCoefficient_three)))
                      (fun _k₄ : Fin 1 =>
                        by
                          have hsecond : (2299 / 192 : ℝ) * 0 = 0 := mul_zero _
                          have hthird : (9317 / 512 : ℝ) * 0 = 0 := mul_zero _
                          exact Eq.trans
                            (congrArg₂ (fun left right : ℝ => left + right)
                              (congrArg (fun value : ℝ => (4 / 3) * 2 + value) hsecond)
                              hthird)
                            (Eq.trans
                              (congrArg (fun value : ℝ => value + 0)
                                (add_zero ((4 / 3) * 2)))
                              (Eq.trans (add_zero ((4 / 3) * 2))
                                Real.positiveDegreeFourCoefficient_four)))
                      k₃)
                  k₂)
              k₁)
          k))

/-- Pure coefficient collection after the three barycentric degree elevations.
No analytic or order argument remains in this sink. -/
theorem Real.shiftedReciprocalPositiveDegreeFourExpansion_eq_quarticEnvelope
    (r y : ℝ) :
    Real.shiftedReciprocalPositiveDegreeFourExpansion r y =
      Real.shiftedReciprocalPositiveQuarticEnvelope r y := by
  have hexpansion := Real.reverseQuarticLinearForm_positiveDegreeFour r y
  have hcoefficients :=
    Real.shiftedReciprocalPositiveDegreeFourCoefficients_eq_envelope
  have hcoefficientTransport :
      Real.reverseQuarticLinearForm
          Real.shiftedReciprocalPositiveDegreeFourCoefficients r y =
        Real.reverseQuarticLinearForm
          Real.reversePositiveQuarticEnvelopeCoefficients r y :=
    congrArg (fun coefficients : Fin 5 → ℝ =>
      Real.reverseQuarticLinearForm coefficients r y) hcoefficients
  have hreverse :
      Real.reverseQuarticLinearForm
          Real.reversePositiveQuarticEnvelopeCoefficients r y =
        (6171 / 512) * r ^ 4 +
          (4 * (19025 / 1536)) * (r ^ 3 * y) +
          (6 * (8945 / 2304)) * (r ^ 2 * y ^ 2) +
          (4 * (5 / 3)) * (r * y ^ 3) +
          (8 / 3) * y ^ 4 := by
    unfold Real.reversePositiveQuarticEnvelopeCoefficients
    exact Real.reverseQuarticLinearForm_finFive
      (6171 / 512) (4 * (19025 / 1536))
      (6 * (8945 / 2304)) (4 * (5 / 3)) (8 / 3) r y
  have hreorder :
      (6171 / 512) * r ^ 4 +
          (4 * (19025 / 1536)) * (r ^ 3 * y) +
          (6 * (8945 / 2304)) * (r ^ 2 * y ^ 2) +
          (4 * (5 / 3)) * (r * y ^ 3) +
          (8 / 3) * y ^ 4 =
        Real.shiftedReciprocalPositiveQuarticEnvelope r y := by
    unfold Real.shiftedReciprocalPositiveQuarticEnvelope
    exact Real.reverse_five_term_sum
      ((6171 / 512) * r ^ 4)
      ((4 * (19025 / 1536)) * (r ^ 3 * y))
      ((6 * (8945 / 2304)) * (r ^ 2 * y ^ 2))
      ((4 * (5 / 3)) * (r * y ^ 3))
      ((8 / 3) * y ^ 4)
  exact Eq.trans hexpansion.symm
    (Eq.trans hcoefficientTransport (Eq.trans hreverse hreorder))

/-- Degree elevation identifies the normalized reciprocal budget with the
quartic Bernstein envelope. -/
theorem Real.shiftedReciprocalPositiveNormalizedBudget_eq_quarticEnvelope
    {r y : ℝ} (hsum : r + y = 1) :
    Real.shiftedReciprocalPositiveNormalizedBudget r y =
      Real.shiftedReciprocalPositiveQuarticEnvelope r y := by
  unfold Real.shiftedReciprocalPositiveNormalizedBudget
  have hsquare := Real.barycentric_square_packet_expansion r y hsum
  have hcube := Real.barycentric_cube_packet_expansion r y hsum
  have hfourth := Real.barycentric_fourth_packet_expansion r y hsum
  have hexpansion :
      (4 / 3) * (y ^ 2 + y) +
          (2299 / 192) * (r ^ 2 * (y + 1 / 2)) +
          (9317 / 512) * (r ^ 3 * (y + 1 / 3)) =
        Real.shiftedReciprocalPositiveDegreeFourExpansion r y := by
    unfold Real.shiftedReciprocalPositiveDegreeFourExpansion
    exact congrArg₂ (fun left right : ℝ => left + right)
      (congrArg₂ (fun left right : ℝ => left + right)
        (congrArg (fun value : ℝ => (4 / 3) * value) hsquare)
        (congrArg (fun value : ℝ => (2299 / 192) * value) hcube))
      (congrArg (fun value : ℝ => (9317 / 512) * value) hfourth)
  exact Eq.trans hexpansion
    (Real.shiftedReciprocalPositiveDegreeFourExpansion_eq_quarticEnvelope r y)

theorem Real.shiftedReciprocalPositiveNormalizedBudget_le_sixteen
    {r y : ℝ}
    (hr : 0 ≤ r) (hy : 0 ≤ y) (hsum : r + y = 1) :
    Real.shiftedReciprocalPositiveNormalizedBudget r y ≤ 16 := by
  have hquartic :=
    Real.shiftedReciprocalPositiveQuarticEnvelope_le_sixteen hr hy hsum
  exact le_trans
    (le_of_eq
      (Real.shiftedReciprocalPositiveNormalizedBudget_eq_quarticEnvelope hsum))
    hquartic

theorem Real.shiftedReciprocalPositiveNormalizedBudget_le_exactMajorant
    {r y : ℝ}
    (hr : 0 ≤ r) (hy : 0 ≤ y) (hsum : r + y = 1) :
    Real.shiftedReciprocalPositiveNormalizedBudget r y ≤
      Real.shiftedReciprocalPositiveQuarticExactMajorant := by
  have hquartic :=
    Real.shiftedReciprocalPositiveQuarticEnvelope_le_exactMajorant hr hy hsum
  exact le_trans
    (le_of_eq
      (Real.shiftedReciprocalPositiveNormalizedBudget_eq_quarticEnvelope hsum))
    hquartic

theorem Real.shiftedReciprocalPositiveBenchmarkSeriesBudget_eq
    {A c : ℝ} (hA : 0 ≤ A) (hc : 0 < c) :
    Real.shiftedReciprocalPacketSeriesBudget
        A c 48
        (6 * (11 / 4 : ℝ) ^ 2 * A ^ 2)
        (2 * (7 / 4 : ℝ) * (11 / 4 : ℝ) ^ 2 * A ^ 2)
        (3 * (7 / 4 : ℝ) * (11 / 4 : ℝ) ^ 3 * A ^ 3) =
      (48 / c ^ 2) *
          (Real.shiftedReciprocalUnitComplement A c ^ 2 +
            Real.shiftedReciprocalUnitComplement A c) +
        (((6 * (11 / 4 : ℝ) ^ 2 +
              2 * (7 / 4 : ℝ) * (11 / 4 : ℝ) ^ 2) / c) *
          (Real.shiftedReciprocalUnitRatio A c ^ 2 *
            (Real.shiftedReciprocalUnitComplement A c + 1 / 2))) +
        (((3 * (7 / 4 : ℝ) * (11 / 4 : ℝ) ^ 3) / c) *
          (Real.shiftedReciprocalUnitRatio A c ^ 3 *
            (Real.shiftedReciprocalUnitComplement A c + 1 / 3))) := by
  unfold Real.shiftedReciprocalPacketSeriesBudget
  have hsquare := Real.shiftedInverseSquareSeriesBudget_eq_unitCoordinates hA hc
  have hcube :=
    Real.shiftedInverseCubeSeriesBudget_mul_shiftSquare_eq_unitCoordinates hA hc
  have hfourth :=
    Real.shiftedInverseFourthSeriesBudget_mul_shiftCube_eq_unitCoordinates hA hc
  let y : ℝ := Real.shiftedReciprocalUnitComplement A c
  let r : ℝ := Real.shiftedReciprocalUnitRatio A c
  let squareFactor : ℝ := y ^ 2 + y
  let cubeFactor : ℝ := r ^ 2 * (y + 1 / 2)
  let fourthFactor : ℝ := r ^ 3 * (y + 1 / 3)
  let cubeFirst : ℝ := 6 * (11 / 4 : ℝ) ^ 2
  let cubeSecond : ℝ := 2 * (7 / 4 : ℝ) * (11 / 4 : ℝ) ^ 2
  let fourthCoefficient : ℝ := 3 * (7 / 4 : ℝ) * (11 / 4 : ℝ) ^ 3
  have hcubeFactored :
      A ^ 2 * Real.shiftedInverseCubeSeriesBudget A c =
        (1 / c) * cubeFactor :=
    Eq.trans hcube
      (mul_assoc (1 / c)
        (Real.shiftedReciprocalUnitRatio A c ^ 2)
        (Real.shiftedReciprocalUnitComplement A c + 1 / 2))
  have hfourthFactored :
      A ^ 3 * Real.shiftedInverseFourthSeriesBudget A c =
        (1 / c) * fourthFactor :=
    Eq.trans hfourth
      (mul_assoc (1 / c)
        (Real.shiftedReciprocalUnitRatio A c ^ 3)
        (Real.shiftedReciprocalUnitComplement A c + 1 / 3))
  have hsquareScaled :
      48 * Real.shiftedInverseSquareSeriesBudget A c =
        (48 / c ^ 2) * squareFactor := by
    exact Eq.trans
      (congrArg (fun value : ℝ => 48 * value) hsquare)
      (Real.scalar_mul_reciprocal_factor 48 (c ^ 2) squareFactor)
  have hcubeFirstScaled :
      (cubeFirst * A ^ 2) * Real.shiftedInverseCubeSeriesBudget A c =
        (cubeFirst / c) * cubeFactor := by
    exact Real.scalar_mul_shifted_factor cubeFirst (A ^ 2)
      (Real.shiftedInverseCubeSeriesBudget A c) c cubeFactor hcubeFactored
  have hcubeSecondScaled :
      (cubeSecond * A ^ 2) * Real.shiftedInverseCubeSeriesBudget A c =
        (cubeSecond / c) * cubeFactor := by
    exact Real.scalar_mul_shifted_factor cubeSecond (A ^ 2)
      (Real.shiftedInverseCubeSeriesBudget A c) c cubeFactor hcubeFactored
  have hcubeCombined :
      (cubeFirst / c) * cubeFactor + (cubeSecond / c) * cubeFactor =
        ((cubeFirst + cubeSecond) / c) * cubeFactor := by
    have hfactor :
        (cubeFirst / c) * cubeFactor + (cubeSecond / c) * cubeFactor =
          (cubeFirst / c + cubeSecond / c) * cubeFactor :=
      (add_mul (cubeFirst / c) (cubeSecond / c) cubeFactor).symm
    have hdivision : cubeFirst / c + cubeSecond / c =
        (cubeFirst + cubeSecond) / c :=
      (add_div cubeFirst cubeSecond c).symm
    exact Eq.trans hfactor
      (congrArg (fun value : ℝ => value * cubeFactor) hdivision)
  have hfourthScaled :
      (fourthCoefficient * A ^ 3) *
          Real.shiftedInverseFourthSeriesBudget A c =
        (fourthCoefficient / c) * fourthFactor := by
    exact Real.scalar_mul_shifted_factor fourthCoefficient (A ^ 3)
      (Real.shiftedInverseFourthSeriesBudget A c) c fourthFactor hfourthFactored
  calc
    48 * Real.shiftedInverseSquareSeriesBudget A c +
          (6 * (11 / 4 : ℝ) ^ 2 * A ^ 2) *
            Real.shiftedInverseCubeSeriesBudget A c +
        (2 * (7 / 4 : ℝ) * (11 / 4 : ℝ) ^ 2 * A ^ 2) *
          Real.shiftedInverseCubeSeriesBudget A c +
      (3 * (7 / 4 : ℝ) * (11 / 4 : ℝ) ^ 3 * A ^ 3) *
        Real.shiftedInverseFourthSeriesBudget A c =
      (48 / c ^ 2) *
          (Real.shiftedReciprocalUnitComplement A c ^ 2 +
            Real.shiftedReciprocalUnitComplement A c) +
        (((6 * (11 / 4 : ℝ) ^ 2 +
              2 * (7 / 4 : ℝ) * (11 / 4 : ℝ) ^ 2) / c) *
          (Real.shiftedReciprocalUnitRatio A c ^ 2 *
            (Real.shiftedReciprocalUnitComplement A c + 1 / 2))) +
        (((3 * (7 / 4 : ℝ) * (11 / 4 : ℝ) ^ 3) / c) *
          (Real.shiftedReciprocalUnitRatio A c ^ 3 *
            (Real.shiftedReciprocalUnitComplement A c + 1 / 3))) := by
      have htransported :=
        (congrArg₂ (fun left right : ℝ => left + right)
          (congrArg₂ (fun left right : ℝ => left + right)
            (congrArg₂ (fun left right : ℝ => left + right)
              hsquareScaled hcubeFirstScaled)
            hcubeSecondScaled)
          hfourthScaled)
      have hmiddle :
          ((48 / c ^ 2) * squareFactor +
              (cubeFirst / c) * cubeFactor) +
              (cubeSecond / c) * cubeFactor =
            (48 / c ^ 2) * squareFactor +
              ((cubeFirst + cubeSecond) / c) * cubeFactor :=
        Eq.trans
          (add_assoc ((48 / c ^ 2) * squareFactor)
            ((cubeFirst / c) * cubeFactor)
            ((cubeSecond / c) * cubeFactor))
          (congrArg (fun value : ℝ =>
              (48 / c ^ 2) * squareFactor + value) hcubeCombined)
      exact Eq.trans htransported
        (congrArg (fun value : ℝ =>
            value + (fourthCoefficient / c) * fourthFactor) hmiddle)

theorem Real.positiveCubeBenchmarkCoefficient_mul_one_sixth :
    (6 * (11 / 4 : ℝ) ^ 2 +
        2 * (7 / 4 : ℝ) * (11 / 4 : ℝ) ^ 2) * (1 / 6) =
      2299 / 192 := by
  have hfourNe : (4 : ℝ) ≠ 0 :=
    ne_of_gt (Nat.cast_pos.mpr (Nat.zero_lt_succ 3))
  have htwoNe : (2 : ℝ) ≠ 0 :=
    ne_of_gt (Nat.cast_pos.mpr (Nat.zero_lt_succ 1))
  have hsixNe : (6 : ℝ) ≠ 0 :=
    ne_of_gt (Nat.cast_pos.mpr (Nat.zero_lt_succ 5))
  have hqSquare : (11 / 4 : ℝ) ^ 2 = 121 / 16 := by
    have hnumerator : (11 : ℝ) ^ 2 = 121 :=
      shiftedReciprocal_realOfNat_pow_eq_of_nat_eq 11 2 121 rfl
    have hdenominator : (4 : ℝ) ^ 2 = 16 :=
      shiftedReciprocal_realOfNat_pow_eq_of_nat_eq 4 2 16 rfl
    exact Eq.trans (div_pow 11 4 2)
      (congrArg₂ (fun numerator denominator : ℝ => numerator / denominator)
        hnumerator hdenominator)
  have htwoSeven : 2 * (7 / 4 : ℝ) = 7 / 2 := by
    have hfourteen : (2 : ℝ) * 7 = 14 :=
      shiftedReciprocal_realOfNat_mul_eq_of_nat_eq 2 7 14 rfl
    have hleft : 2 * (7 / 4 : ℝ) = 14 / 4 :=
      Eq.trans (mul_div_assoc 2 7 4).symm
        (congrArg (fun numerator : ℝ => numerator / 4) hfourteen)
    have hcrossLeft : (14 : ℝ) * 2 = 28 :=
      shiftedReciprocal_realOfNat_mul_eq_of_nat_eq 14 2 28 rfl
    have hcrossRight : (7 : ℝ) * 4 = 28 :=
      shiftedReciprocal_realOfNat_mul_eq_of_nat_eq 7 4 28 rfl
    have hratio : (14 : ℝ) / 4 = 7 / 2 :=
      (div_eq_div_iff hfourNe htwoNe).mpr
        (Eq.trans hcrossLeft hcrossRight.symm)
    exact Eq.trans hleft hratio
  have hsixAsHalves : (6 : ℝ) = 12 / 2 := by
    have honeNe : (1 : ℝ) ≠ 0 := one_ne_zero
    have hleft : (6 : ℝ) * 2 = 12 :=
      shiftedReciprocal_realOfNat_mul_eq_of_nat_eq 6 2 12 rfl
    have hright : (12 : ℝ) * 1 = 12 := mul_one 12
    have hratio : (6 : ℝ) / 1 = 12 / 2 :=
      (div_eq_div_iff honeNe htwoNe).mpr
        (Eq.trans hleft hright.symm)
    exact Eq.trans (div_one 6).symm hratio
  have hsum : (6 : ℝ) + 2 * (7 / 4 : ℝ) = 19 / 2 := by
    exact Eq.trans
      (congrArg₂ (fun left right : ℝ => left + right)
        hsixAsHalves htwoSeven)
      (Eq.trans (div_add_div_same 12 7 2)
        (congrArg (fun numerator : ℝ => numerator / 2)
          (shiftedReciprocal_realOfNat_add_eq_of_nat_eq 12 7 19 rfl)))
  have hfactor :
      6 * (11 / 4 : ℝ) ^ 2 +
          2 * (7 / 4 : ℝ) * (11 / 4 : ℝ) ^ 2 =
        (6 + 2 * (7 / 4 : ℝ)) * (11 / 4 : ℝ) ^ 2 :=
    (add_mul 6 (2 * (7 / 4 : ℝ)) ((11 / 4 : ℝ) ^ 2)).symm
  have hproduct : (19 / 2 : ℝ) * (121 / 16) = 2299 / 32 := by
    have hnumerator : (19 : ℝ) * 121 = 2299 :=
      shiftedReciprocal_realOfNat_mul_eq_of_nat_eq 19 121 2299 rfl
    have hdenominator : (2 : ℝ) * 16 = 32 :=
      shiftedReciprocal_realOfNat_mul_eq_of_nat_eq 2 16 32 rfl
    exact Eq.trans (div_mul_div_comm 19 2 121 16)
      (congrArg₂ (fun numerator denominator : ℝ => numerator / denominator)
        hnumerator hdenominator)
  have hcoefficient :
      6 * (11 / 4 : ℝ) ^ 2 +
          2 * (7 / 4 : ℝ) * (11 / 4 : ℝ) ^ 2 =
        2299 / 32 :=
    Eq.trans hfactor
      (Eq.trans (congrArg (fun value : ℝ => value * (11 / 4 : ℝ) ^ 2) hsum)
        (Eq.trans (congrArg (fun value : ℝ => (19 / 2 : ℝ) * value) hqSquare)
          hproduct))
  have hlast : (2299 / 32 : ℝ) * (1 / 6) = 2299 / 192 := by
    have hdenominator : (32 : ℝ) * 6 = 192 :=
      shiftedReciprocal_realOfNat_mul_eq_of_nat_eq 32 6 192 rfl
    exact Eq.trans (div_mul_div_comm 2299 32 1 6)
      (Eq.trans
        (congrArg₂ (fun numerator denominator : ℝ => numerator / denominator)
          (mul_one 2299) hdenominator)
        rfl)
  exact Eq.trans (congrArg (fun value : ℝ => value * (1 / 6)) hcoefficient)
    hlast

theorem Real.positiveFourthBenchmarkCoefficient_mul_one_sixth :
    (3 * (7 / 4 : ℝ) * (11 / 4 : ℝ) ^ 3) * (1 / 6) =
      9317 / 512 := by
  have hfourNe : (4 : ℝ) ≠ 0 :=
    ne_of_gt (Nat.cast_pos.mpr (Nat.zero_lt_succ 3))
  have hthreeSeven : (3 : ℝ) * (7 / 4) = 21 / 4 := by
    have hnumerator : (3 : ℝ) * 7 = 21 :=
      shiftedReciprocal_realOfNat_mul_eq_of_nat_eq 3 7 21 rfl
    exact Eq.trans (mul_div_assoc 3 7 4).symm
      (congrArg (fun value : ℝ => value / 4) hnumerator)
  have hqCube : (11 / 4 : ℝ) ^ 3 = 1331 / 64 := by
    have hnumerator : (11 : ℝ) ^ 3 = 1331 :=
      shiftedReciprocal_realOfNat_pow_eq_of_nat_eq 11 3 1331 rfl
    have hdenominator : (4 : ℝ) ^ 3 = 64 :=
      shiftedReciprocal_realOfNat_pow_eq_of_nat_eq 4 3 64 rfl
    exact Eq.trans (div_pow 11 4 3)
      (congrArg₂ (fun numerator denominator : ℝ => numerator / denominator)
        hnumerator hdenominator)
  have hproduct : (21 / 4 : ℝ) * (1331 / 64) = 27951 / 256 := by
    have hnumerator : (21 : ℝ) * 1331 = 27951 :=
      shiftedReciprocal_realOfNat_mul_eq_of_nat_eq 21 1331 27951 rfl
    have hdenominator : (4 : ℝ) * 64 = 256 :=
      shiftedReciprocal_realOfNat_mul_eq_of_nat_eq 4 64 256 rfl
    exact Eq.trans (div_mul_div_comm 21 4 1331 64)
      (congrArg₂ (fun numerator denominator : ℝ => numerator / denominator)
        hnumerator hdenominator)
  have hcoefficient :
      3 * (7 / 4 : ℝ) * (11 / 4 : ℝ) ^ 3 = 27951 / 256 :=
    Eq.trans (congrArg (fun value : ℝ => value * (11 / 4 : ℝ) ^ 3) hthreeSeven)
      (Eq.trans (congrArg (fun value : ℝ => (21 / 4 : ℝ) * value) hqCube)
        hproduct)
  have hraw : (27951 / 256 : ℝ) * (1 / 6) = 27951 / 1536 := by
    have hdenominator : (256 : ℝ) * 6 = 1536 :=
      shiftedReciprocal_realOfNat_mul_eq_of_nat_eq 256 6 1536 rfl
    exact Eq.trans (div_mul_div_comm 27951 256 1 6)
      (congrArg₂ (fun numerator denominator : ℝ => numerator / denominator)
        (mul_one 27951) hdenominator)
  have hreduce : (27951 : ℝ) / 1536 = 9317 / 512 := by
    have h1536Ne : (1536 : ℝ) ≠ 0 :=
      ne_of_gt (Nat.cast_pos.mpr (Nat.zero_lt_succ 1535))
    have h512Ne : (512 : ℝ) ≠ 0 :=
      ne_of_gt (Nat.cast_pos.mpr (Nat.zero_lt_succ 511))
    have hleft : (27951 : ℝ) * 512 = 14310912 :=
      shiftedReciprocal_realOfNat_mul_eq_of_nat_eq 27951 512 14310912 rfl
    have hright : (9317 : ℝ) * 1536 = 14310912 :=
      shiftedReciprocal_realOfNat_mul_eq_of_nat_eq 9317 1536 14310912 rfl
    exact (div_eq_div_iff h1536Ne h512Ne).mpr
      (Eq.trans hleft hright.symm)
  exact Eq.trans (congrArg (fun value : ℝ => value * (1 / 6)) hcoefficient)
    (Eq.trans hraw hreduce)

/-- The exact angular lower bound `6 ≤ c` transports the complete benchmark
series to the normalized quartic without discarding its first term. -/
theorem Real.shiftedReciprocalPositiveBenchmarkSeriesBudget_le_normalized
    {A c : ℝ} (hA : 0 ≤ A) (hc : 6 ≤ c) :
    Real.shiftedReciprocalPacketSeriesBudget
        A c 48
        (6 * (11 / 4 : ℝ) ^ 2 * A ^ 2)
        (2 * (7 / 4 : ℝ) * (11 / 4 : ℝ) ^ 2 * A ^ 2)
        (3 * (7 / 4 : ℝ) * (11 / 4 : ℝ) ^ 3 * A ^ 3) ≤
      Real.shiftedReciprocalPositiveNormalizedBudget
        (Real.shiftedReciprocalUnitRatio A c)
        (Real.shiftedReciprocalUnitComplement A c) := by
  have hsixPos : (0 : ℝ) < 6 :=
    Nat.cast_pos.mpr (Nat.zero_lt_succ 5)
  have hcPos : 0 < c := lt_of_lt_of_le hsixPos hc
  have hbenchmark :=
    Real.shiftedReciprocalPositiveBenchmarkSeriesBudget_eq hA hcPos
  have hreciprocal : 1 / c ≤ (1 : ℝ) / 6 :=
    one_div_le_one_div_of_le hsixPos hc
  have hcSquare : (36 : ℝ) ≤ c ^ 2 := by
    have hsquare := mul_self_le_mul_self hsixPos.le hc
    have hsixSquare : (6 : ℝ) ^ 2 = 36 :=
      shiftedReciprocal_realOfNat_pow_eq_of_nat_eq 6 2 36 rfl
    exact le_trans (le_of_eq hsixSquare.symm)
      (le_trans (le_of_eq (pow_two 6))
        (le_trans hsquare (le_of_eq (pow_two c).symm)))
  have hcSquarePos : 0 < c ^ 2 := pow_pos hcPos 2
  have hsquareCoefficient : 48 / c ^ 2 ≤ (4 / 3 : ℝ) := by
    have hthirtySixPos : (0 : ℝ) < 36 :=
      Nat.cast_pos.mpr (Nat.zero_lt_succ 35)
    have hinverse : 1 / c ^ 2 ≤ (1 : ℝ) / 36 :=
      one_div_le_one_div_of_le hthirtySixPos hcSquare
    have hscaled := mul_le_mul_of_nonneg_left hinverse (Nat.cast_nonneg 48)
    have hleft : (48 : ℝ) * (1 / c ^ 2) = 48 / c ^ 2 :=
      (Real.div_eq_mul_one_div_transport 48 (c ^ 2)).symm
    have hthirtySixNe : (36 : ℝ) ≠ 0 := ne_of_gt hthirtySixPos
    have hthreeNe : (3 : ℝ) ≠ 0 :=
      ne_of_gt (Nat.cast_pos.mpr (Nat.zero_lt_succ 2))
    have hcrossLeft : (48 : ℝ) * 3 = 144 :=
      shiftedReciprocal_realOfNat_mul_eq_of_nat_eq 48 3 144 rfl
    have hcrossRight : (4 : ℝ) * 36 = 144 :=
      shiftedReciprocal_realOfNat_mul_eq_of_nat_eq 4 36 144 rfl
    have hratio : (48 : ℝ) / 36 = 4 / 3 :=
      (div_eq_div_iff hthirtySixNe hthreeNe).mpr
        (Eq.trans hcrossLeft hcrossRight.symm)
    have hright : (48 : ℝ) * (1 / 36) = 4 / 3 :=
      Eq.trans (Real.div_eq_mul_one_div_transport 48 36).symm hratio
    exact le_trans (le_of_eq hleft.symm)
      (le_trans hscaled (le_of_eq hright))
  have hcubeBaseNonneg :
      0 ≤ 6 * (11 / 4 : ℝ) ^ 2 +
          2 * (7 / 4 : ℝ) * (11 / 4 : ℝ) ^ 2 := by
    have hq : 0 ≤ (11 / 4 : ℝ) :=
      div_nonneg (Nat.cast_nonneg 11) (Nat.cast_nonneg 4)
    have hs : 0 ≤ (7 / 4 : ℝ) :=
      div_nonneg (Nat.cast_nonneg 7) (Nat.cast_nonneg 4)
    exact add_nonneg
      (mul_nonneg (Nat.cast_nonneg 6) (pow_nonneg hq 2))
      (mul_nonneg
        (mul_nonneg (Nat.cast_nonneg 2) hs)
        (pow_nonneg hq 2))
  have hcubeScaled :=
    mul_le_mul_of_nonneg_left hreciprocal hcubeBaseNonneg
  have hcubeCoefficient :
      (6 * (11 / 4 : ℝ) ^ 2 +
          2 * (7 / 4 : ℝ) * (11 / 4 : ℝ) ^ 2) / c ≤
        2299 / 192 := by
    exact le_trans
      (le_of_eq (Real.div_eq_mul_one_div_transport _ _))
      (le_trans hcubeScaled
        (le_of_eq Real.positiveCubeBenchmarkCoefficient_mul_one_sixth))
  have hfourthBaseNonneg :
      0 ≤ 3 * (7 / 4 : ℝ) * (11 / 4 : ℝ) ^ 3 := by
    exact mul_nonneg
      (mul_nonneg (Nat.cast_nonneg 3)
        (div_nonneg (Nat.cast_nonneg 7) (Nat.cast_nonneg 4)))
      (pow_nonneg
        (div_nonneg (Nat.cast_nonneg 11) (Nat.cast_nonneg 4)) 3)
  have hfourthScaled :=
    mul_le_mul_of_nonneg_left hreciprocal hfourthBaseNonneg
  have hfourthCoefficient :
      (3 * (7 / 4 : ℝ) * (11 / 4 : ℝ) ^ 3) / c ≤
        9317 / 512 := by
    exact le_trans
      (le_of_eq (Real.div_eq_mul_one_div_transport _ _))
      (le_trans hfourthScaled
        (le_of_eq Real.positiveFourthBenchmarkCoefficient_mul_one_sixth))
  have hy := Real.shiftedReciprocalUnitComplement_nonneg hA hcPos
  have hr := Real.shiftedReciprocalUnitRatio_nonneg hA hcPos
  have hsquareFactor :
      0 ≤ Real.shiftedReciprocalUnitComplement A c ^ 2 +
        Real.shiftedReciprocalUnitComplement A c :=
    add_nonneg (pow_nonneg hy 2) hy
  have hcubeFactor :
      0 ≤ Real.shiftedReciprocalUnitRatio A c ^ 2 *
        (Real.shiftedReciprocalUnitComplement A c + 1 / 2) :=
    mul_nonneg (pow_nonneg hr 2)
      (add_nonneg hy (div_nonneg zero_le_one (Nat.cast_nonneg 2)))
  have hfourthFactor :
      0 ≤ Real.shiftedReciprocalUnitRatio A c ^ 3 *
        (Real.shiftedReciprocalUnitComplement A c + 1 / 3) :=
    mul_nonneg (pow_nonneg hr 3)
      (add_nonneg hy (div_nonneg zero_le_one (Nat.cast_nonneg 3)))
  have hsquare := mul_le_mul_of_nonneg_right
    hsquareCoefficient hsquareFactor
  have hcube := mul_le_mul_of_nonneg_right
    hcubeCoefficient hcubeFactor
  have hfourth := mul_le_mul_of_nonneg_right
    hfourthCoefficient hfourthFactor
  have hsum := add_le_add (add_le_add hsquare hcube) hfourth
  unfold Real.shiftedReciprocalPositiveNormalizedBudget
  exact le_trans (le_of_eq hbenchmark) hsum

theorem Real.shiftedReciprocalPositiveBenchmarkSeriesBudget_le_sixteen
    {A c : ℝ} (hA : 0 ≤ A) (hc : 6 ≤ c) :
    Real.shiftedReciprocalPacketSeriesBudget
        A c 48
        (6 * (11 / 4 : ℝ) ^ 2 * A ^ 2)
        (2 * (7 / 4 : ℝ) * (11 / 4 : ℝ) ^ 2 * A ^ 2)
        (3 * (7 / 4 : ℝ) * (11 / 4 : ℝ) ^ 3 * A ^ 3) ≤ 16 := by
  have hsixPos : (0 : ℝ) < 6 :=
    Nat.cast_pos.mpr (Nat.zero_lt_succ 5)
  have hcPos : 0 < c := lt_of_lt_of_le hsixPos hc
  have hnormalized :=
    Real.shiftedReciprocalPositiveBenchmarkSeriesBudget_le_normalized hA hc
  have hquartic :=
    Real.shiftedReciprocalPositiveNormalizedBudget_le_sixteen
      (Real.shiftedReciprocalUnitRatio_nonneg hA hcPos)
      (Real.shiftedReciprocalUnitComplement_nonneg hA hcPos)
      (Real.shiftedReciprocalUnitRatio_add_complement hA hcPos)
  exact le_trans hnormalized hquartic

theorem Real.shiftedReciprocalPositiveBenchmarkSeriesBudget_le_exactMajorant
    {A c : ℝ} (hA : 0 ≤ A) (hc : 6 ≤ c) :
    Real.shiftedReciprocalPacketSeriesBudget
        A c 48
        (6 * (11 / 4 : ℝ) ^ 2 * A ^ 2)
        (2 * (7 / 4 : ℝ) * (11 / 4 : ℝ) ^ 2 * A ^ 2)
        (3 * (7 / 4 : ℝ) * (11 / 4 : ℝ) ^ 3 * A ^ 3) ≤
      Real.shiftedReciprocalPositiveQuarticExactMajorant := by
  have hsixPos : (0 : ℝ) < 6 :=
    Nat.cast_pos.mpr (Nat.zero_lt_succ 5)
  have hcPos : 0 < c := lt_of_lt_of_le hsixPos hc
  have hnormalized :=
    Real.shiftedReciprocalPositiveBenchmarkSeriesBudget_le_normalized hA hc
  have hquartic :=
    Real.shiftedReciprocalPositiveNormalizedBudget_le_exactMajorant
      (Real.shiftedReciprocalUnitRatio_nonneg hA hcPos)
      (Real.shiftedReciprocalUnitComplement_nonneg hA hcPos)
      (Real.shiftedReciprocalUnitRatio_add_complement hA hcPos)
  exact le_trans hnormalized hquartic

end

end LFunctions
end Boundary
