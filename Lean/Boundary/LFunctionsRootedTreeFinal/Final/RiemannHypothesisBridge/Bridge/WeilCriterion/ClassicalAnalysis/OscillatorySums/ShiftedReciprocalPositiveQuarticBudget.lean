import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ClassicalAnalysis.OscillatorySums.BernsteinBudget

/-!
# Quartic Bernstein envelope for a shifted reciprocal packet

After normalizing a nonnegative shift `A` by `A + c`, the complete positive
packet budget is a quartic polynomial on the unit interval.  This owner stores
its Bernstein coefficients and proves their common bound by sixteen.  The
analytic specialization that transports reciprocal terms to this polynomial
lives downstream.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open scoped BigOperators unitInterval

/-- Bernstein coefficients of the normalized positive-tail quartic. -/
def Real.shiftedReciprocalPositiveQuarticCoefficient
    (k : Fin 5) : ℝ :=
  Fin.cases (8 / 3 : ℝ)
    (fun k₁ : Fin 4 =>
      Fin.cases (5 / 3 : ℝ)
        (fun k₂ : Fin 3 =>
          Fin.cases (8945 / 2304 : ℝ)
            (fun k₃ : Fin 2 =>
              Fin.cases (19025 / 1536 : ℝ)
                (fun _k₄ : Fin 1 => 6171 / 512)
                k₃)
            k₂)
        k₁)
    k

private theorem positiveQuartic_realOfNat_mul_eq_of_nat_eq
    (a b c : ℕ) (h : a * b = c) :
    (a : ℝ) * (b : ℝ) = (c : ℝ) :=
  Eq.trans (Nat.cast_mul a b).symm
    (congrArg (fun n : ℕ => (n : ℝ)) h)

/-- Casted natural quotients are bounded by an integer majorant once the
cross-multiplied natural inequality is known. -/
theorem Real.natCast_div_natCast_le_natCast
    (numerator denominator majorant : ℕ)
    (hdenominator : 0 < denominator)
    (hcross : numerator ≤ majorant * denominator) :
    (numerator : ℝ) / (denominator : ℝ) ≤ (majorant : ℝ) := by
  have hdenominatorReal : (0 : ℝ) < (denominator : ℝ) :=
    Nat.cast_pos.mpr hdenominator
  have hcast :
      (numerator : ℝ) ≤ ((majorant * denominator : ℕ) : ℝ) :=
    Nat.cast_le.mpr hcross
  have hproduct :
      ((majorant * denominator : ℕ) : ℝ) =
        (majorant : ℝ) * (denominator : ℝ) :=
    Nat.cast_mul majorant denominator
  have htransported :
      (numerator : ℝ) ≤
        (majorant : ℝ) * (denominator : ℝ) :=
    Eq.subst
      (motive := fun right : ℝ => (numerator : ℝ) ≤ right)
      hproduct
      hcast
  exact (div_le_iff₀ hdenominatorReal).mpr htransported

theorem Real.natCast_div_natCast_le_div
    (a b c d : ℕ)
    (hb : 0 < b) (hd : 0 < d)
    (hcross : a * d ≤ c * b) :
    (a : ℝ) / (b : ℝ) ≤ (c : ℝ) / (d : ℝ) := by
  have hbReal : (0 : ℝ) < (b : ℝ) := Nat.cast_pos.mpr hb
  have hdReal : (0 : ℝ) < (d : ℝ) := Nat.cast_pos.mpr hd
  have hcast : ((a * d : ℕ) : ℝ) ≤ ((c * b : ℕ) : ℝ) :=
    Nat.cast_le.mpr hcross
  have hleft : ((a * d : ℕ) : ℝ) = (a : ℝ) * (d : ℝ) :=
    Nat.cast_mul a d
  have hright : ((c * b : ℕ) : ℝ) = (c : ℝ) * (b : ℝ) :=
    Nat.cast_mul c b
  have htransported :
      (a : ℝ) * (d : ℝ) ≤ (c : ℝ) * (b : ℝ) :=
    Eq.subst
      (motive := fun left : ℝ => left ≤ (c : ℝ) * (b : ℝ))
      hleft
      (Eq.subst
        (motive := fun right : ℝ => ((a * d : ℕ) : ℝ) ≤ right)
        hright
        hcast)
  exact (div_le_div_iff₀ hbReal hdReal).mpr htransported

private theorem positiveQuartic_eight_thirds_le_sixteen :
    (8 / 3 : ℝ) ≤ 16 := by
  exact Real.natCast_div_natCast_le_natCast 8 3 16
    (Nat.zero_lt_succ 2)
    (by
      exact Eq.subst
        (motive := fun right : ℕ => 8 ≤ right)
        (show 16 * 3 = 8 + 40 from rfl).symm
        (Nat.le_add_right 8 40))

private theorem positiveQuartic_five_thirds_le_sixteen :
    (5 / 3 : ℝ) ≤ 16 := by
  exact Real.natCast_div_natCast_le_natCast 5 3 16
    (Nat.zero_lt_succ 2)
    (by
      exact Eq.subst
        (motive := fun right : ℕ => 5 ≤ right)
        (show 16 * 3 = 5 + 43 from rfl).symm
        (Nat.le_add_right 5 43))

private theorem positiveQuartic_eightNineFourFive_le_sixteen :
    (8945 / 2304 : ℝ) ≤ 16 := by
  exact Real.natCast_div_natCast_le_natCast 8945 2304 16
    (Nat.zero_lt_succ 2303)
    (by
      exact Eq.subst
        (motive := fun right : ℕ => 8945 ≤ right)
        (show 16 * 2304 = 8945 + 27919 from rfl).symm
        (Nat.le_add_right 8945 27919))

private theorem positiveQuartic_oneNineZeroTwoFive_le_sixteen :
    (19025 / 1536 : ℝ) ≤ 16 := by
  exact Real.natCast_div_natCast_le_natCast 19025 1536 16
    (Nat.zero_lt_succ 1535)
    (by
      exact Eq.subst
        (motive := fun right : ℕ => 19025 ≤ right)
        (show 16 * 1536 = 19025 + 5551 from rfl).symm
        (Nat.le_add_right 19025 5551))

private theorem positiveQuartic_sixOneSevenOne_le_sixteen :
    (6171 / 512 : ℝ) ≤ 16 := by
  exact Real.natCast_div_natCast_le_natCast 6171 512 16
    (Nat.zero_lt_succ 511)
    (by
      exact Eq.subst
        (motive := fun right : ℕ => 6171 ≤ right)
        (show 16 * 512 = 6171 + 2021 from rfl).symm
        (Nat.le_add_right 6171 2021))

def Real.shiftedReciprocalPositiveQuarticExactMajorant : ℝ :=
  61683 / 4608

private theorem positiveQuartic_eight_thirds_le_exact :
    (8 / 3 : ℝ) ≤ Real.shiftedReciprocalPositiveQuarticExactMajorant := by
  unfold Real.shiftedReciprocalPositiveQuarticExactMajorant
  exact Real.natCast_div_natCast_le_div 8 3 61683 4608
    (Nat.zero_lt_succ 2) (Nat.zero_lt_succ 4607)
    (by
      exact Eq.subst
        (motive := fun right : ℕ => 8 * 4608 ≤ right)
        (show 61683 * 3 = 8 * 4608 + 148185 from rfl).symm
        (Nat.le_add_right (8 * 4608) 148185))

private theorem positiveQuartic_five_thirds_le_exact :
    (5 / 3 : ℝ) ≤ Real.shiftedReciprocalPositiveQuarticExactMajorant := by
  unfold Real.shiftedReciprocalPositiveQuarticExactMajorant
  exact Real.natCast_div_natCast_le_div 5 3 61683 4608
    (Nat.zero_lt_succ 2) (Nat.zero_lt_succ 4607)
    (by
      exact Eq.subst
        (motive := fun right : ℕ => 5 * 4608 ≤ right)
        (show 61683 * 3 = 5 * 4608 + 162009 from rfl).symm
        (Nat.le_add_right (5 * 4608) 162009))

private theorem positiveQuartic_eightNineFourFive_le_exact :
    (8945 / 2304 : ℝ) ≤
      Real.shiftedReciprocalPositiveQuarticExactMajorant := by
  unfold Real.shiftedReciprocalPositiveQuarticExactMajorant
  exact Real.natCast_div_natCast_le_div 8945 2304 61683 4608
    (Nat.zero_lt_succ 2303) (Nat.zero_lt_succ 4607)
    (by
      exact Eq.subst
        (motive := fun right : ℕ => 8945 * 4608 ≤ right)
        (show 61683 * 2304 = 8945 * 4608 + 100899072 from rfl).symm
        (Nat.le_add_right (8945 * 4608) 100899072))

private theorem positiveQuartic_oneNineZeroTwoFive_le_exact :
    (19025 / 1536 : ℝ) ≤
      Real.shiftedReciprocalPositiveQuarticExactMajorant := by
  unfold Real.shiftedReciprocalPositiveQuarticExactMajorant
  exact Real.natCast_div_natCast_le_div 19025 1536 61683 4608
    (Nat.zero_lt_succ 1535) (Nat.zero_lt_succ 4607)
    (by
      exact Eq.subst
        (motive := fun right : ℕ => 19025 * 4608 ≤ right)
        (show 61683 * 1536 = 19025 * 4608 + 7077888 from rfl).symm
        (Nat.le_add_right (19025 * 4608) 7077888))

private theorem positiveQuartic_sixOneSevenOne_le_exact :
    (6171 / 512 : ℝ) ≤
      Real.shiftedReciprocalPositiveQuarticExactMajorant := by
  unfold Real.shiftedReciprocalPositiveQuarticExactMajorant
  exact Real.natCast_div_natCast_le_div 6171 512 61683 4608
    (Nat.zero_lt_succ 511) (Nat.zero_lt_succ 4607)
    (by
      exact Eq.subst
        (motive := fun right : ℕ => 6171 * 4608 ≤ right)
        (show 61683 * 512 = 6171 * 4608 + 3145728 from rfl).symm
        (Nat.le_add_right (6171 * 4608) 3145728))

theorem Real.shiftedReciprocalPositiveQuarticCoefficient_le_exactMajorant
    (k : Fin 5) :
    Real.shiftedReciprocalPositiveQuarticCoefficient k ≤
      Real.shiftedReciprocalPositiveQuarticExactMajorant := by
  exact Fin.cases positiveQuartic_eight_thirds_le_exact
    (fun k₁ : Fin 4 =>
      Fin.cases positiveQuartic_five_thirds_le_exact
        (fun k₂ : Fin 3 =>
          Fin.cases positiveQuartic_eightNineFourFive_le_exact
            (fun k₃ : Fin 2 =>
              Fin.cases positiveQuartic_oneNineZeroTwoFive_le_exact
                (fun _k₄ : Fin 1 =>
                  positiveQuartic_sixOneSevenOne_le_exact)
                k₃)
            k₂)
        k₁)
    k

/-- Every coefficient of the positive-tail Bernstein quartic is below the
available constant sixteen. -/
theorem Real.shiftedReciprocalPositiveQuarticCoefficient_le_sixteen
    (k : Fin 5) :
    Real.shiftedReciprocalPositiveQuarticCoefficient k ≤ 16 := by
  exact Fin.cases positiveQuartic_eight_thirds_le_sixteen
    (fun k₁ : Fin 4 =>
      Fin.cases positiveQuartic_five_thirds_le_sixteen
        (fun k₂ : Fin 3 =>
          Fin.cases positiveQuartic_eightNineFourFive_le_sixteen
            (fun k₃ : Fin 2 =>
              Fin.cases positiveQuartic_oneNineZeroTwoFive_le_sixteen
                (fun _k₄ : Fin 1 =>
                  positiveQuartic_sixOneSevenOne_le_sixteen)
                k₃)
            k₂)
        k₁)
    k

/-- The normalized quartic Bernstein envelope is at most sixteen throughout
the unit interval. -/
theorem Real.shiftedReciprocalPositiveQuarticBernsteinBudget_le_sixteen
    (x : I) :
    (∑ k : Fin 5,
        Real.shiftedReciprocalPositiveQuarticCoefficient k *
          bernstein 4 k x) ≤ 16 := by
  exact Real.sum_bernstein_mul_le_coefficient_majorant
    4 x Real.shiftedReciprocalPositiveQuarticCoefficient 16
    Real.shiftedReciprocalPositiveQuarticCoefficient_le_sixteen

/-- Explicit degree-four Bernstein envelope.  Writing both barycentric
coordinates keeps the later reciprocal normalization free of subtraction. -/
def Real.shiftedReciprocalPositiveQuarticEnvelope
    (r y : ℝ) : ℝ :=
  (8 / 3) * y ^ 4 +
    4 * (5 / 3) * (r * y ^ 3) +
    6 * (8945 / 2304) * (r ^ 2 * y ^ 2) +
    4 * (19025 / 1536) * (r ^ 3 * y) +
    (6171 / 512) * r ^ 4

theorem Real.add_pow_four_explicit (r y : ℝ) :
    (r + y) ^ 4 =
      y ^ 4 + 4 * (r * y ^ 3) + 6 * (r ^ 2 * y ^ 2) +
        4 * (r ^ 3 * y) + r ^ 4 := by
  let f : ℕ → ℝ :=
    fun m => r ^ m * y ^ (4 - m) * (Nat.choose 4 m : ℝ)
  have hbinomial : (r + y) ^ 4 = ∑ m ∈ Finset.range 5, f m := by
    exact add_pow r y 4
  have hzero : (∑ m ∈ Finset.range 0, f m) = 0 :=
    Finset.sum_range_zero f
  have hsucc₀ : (∑ m ∈ Finset.range 1, f m) =
      (∑ m ∈ Finset.range 0, f m) + f 0 :=
    Finset.sum_range_succ f 0
  have hsucc₁ : (∑ m ∈ Finset.range 2, f m) =
      (∑ m ∈ Finset.range 1, f m) + f 1 :=
    Finset.sum_range_succ f 1
  have hsucc₂ : (∑ m ∈ Finset.range 3, f m) =
      (∑ m ∈ Finset.range 2, f m) + f 2 :=
    Finset.sum_range_succ f 2
  have hsucc₃ : (∑ m ∈ Finset.range 4, f m) =
      (∑ m ∈ Finset.range 3, f m) + f 3 :=
    Finset.sum_range_succ f 3
  have hsucc₄ : (∑ m ∈ Finset.range 5, f m) =
      (∑ m ∈ Finset.range 4, f m) + f 4 :=
    Finset.sum_range_succ f 4
  have hf₀ : f 0 = y ^ 4 := by
    unfold f
    have hyPower : y ^ (4 - 0) = y ^ 4 :=
      congrArg (fun exponent : ℕ => y ^ exponent) (Nat.sub_zero 4)
    have hchoose : ((Nat.choose 4 0 : ℕ) : ℝ) = 1 :=
      Eq.trans
        (congrArg (fun n : ℕ => (n : ℝ))
          (show Nat.choose 4 0 = 1 from rfl))
        Nat.cast_one
    have hleft : r ^ 0 * y ^ (4 - 0) = y ^ 4 :=
      Eq.trans
        (congrArg₂ (fun left right : ℝ => left * right)
          (pow_zero r) hyPower)
        (one_mul (y ^ 4))
    exact Eq.trans
      (congrArg₂ (fun left right : ℝ => left * right) hleft hchoose)
      (mul_one (y ^ 4))
  have hf₁ : f 1 = 4 * (r * y ^ 3) := by
    unfold f
    have hpower : r ^ 1 = r := pow_one r
    have hchoose : ((Nat.choose 4 1 : ℕ) : ℝ) = 4 := by
      exact congrArg (fun n : ℕ => (n : ℝ)) (show Nat.choose 4 1 = 4 from rfl)
    exact Eq.trans
      (congrArg₂ (fun left right : ℝ => left * y ^ 3 * right)
        hpower hchoose)
      (mul_comm (r * y ^ 3) 4)
  have hf₂ : f 2 = 6 * (r ^ 2 * y ^ 2) := by
    unfold f
    have hchoose : ((Nat.choose 4 2 : ℕ) : ℝ) = 6 := by
      exact congrArg (fun n : ℕ => (n : ℝ)) (show Nat.choose 4 2 = 6 from rfl)
    exact Eq.trans
      (congrArg (fun value : ℝ => r ^ 2 * y ^ 2 * value) hchoose)
      (mul_comm (r ^ 2 * y ^ 2) 6)
  have hf₃ : f 3 = 4 * (r ^ 3 * y) := by
    unfold f
    have hyPower : y ^ (4 - 3) = y := pow_one y
    have hchoose : ((Nat.choose 4 3 : ℕ) : ℝ) = 4 := by
      exact congrArg (fun n : ℕ => (n : ℝ)) (show Nat.choose 4 3 = 4 from rfl)
    exact Eq.trans
      (congrArg₂ (fun left right : ℝ => r ^ 3 * left * right)
        hyPower hchoose)
      (mul_comm (r ^ 3 * y) 4)
  have hf₄ : f 4 = r ^ 4 := by
    unfold f
    have hyPower : y ^ (4 - 4) = 1 :=
      Eq.trans
        (congrArg (fun exponent : ℕ => y ^ exponent) (Nat.sub_self 4))
        (pow_zero y)
    have hchoose : ((Nat.choose 4 4 : ℕ) : ℝ) = 1 := by
      exact Eq.trans
        (congrArg (fun n : ℕ => (n : ℝ))
          (show Nat.choose 4 4 = 1 from rfl))
        Nat.cast_one
    have hleft : r ^ 4 * y ^ (4 - 4) = r ^ 4 :=
      Eq.trans
        (congrArg (fun value : ℝ => r ^ 4 * value) hyPower)
        (mul_one (r ^ 4))
    exact Eq.trans
      (congrArg₂ (fun left right : ℝ => left * right) hleft hchoose)
      (mul_one (r ^ 4))
  have hsumExpand :
      (∑ m ∈ Finset.range 5, f m) =
        ((((f 0 + f 1) + f 2) + f 3) + f 4) := by
    exact Eq.trans hsucc₄
      (Eq.trans
        (congrArg (fun value : ℝ => value + f 4) hsucc₃)
        (Eq.trans
          (congrArg (fun value : ℝ => (value + f 3) + f 4) hsucc₂)
          (Eq.trans
            (congrArg (fun value : ℝ => ((value + f 2) + f 3) + f 4) hsucc₁)
            (Eq.trans
              (congrArg
                (fun value : ℝ => (((value + f 1) + f 2) + f 3) + f 4)
                hsucc₀)
              (Eq.trans
                (congrArg
                  (fun value : ℝ => ((((value + f 0) + f 1) + f 2) + f 3) + f 4)
                  hzero)
                (congrArg
                  (fun value : ℝ => (((value + f 1) + f 2) + f 3) + f 4)
                  (zero_add (f 0))))))))
  have hterms :
      ((((f 0 + f 1) + f 2) + f 3) + f 4) =
        y ^ 4 + 4 * (r * y ^ 3) + 6 * (r ^ 2 * y ^ 2) +
          4 * (r ^ 3 * y) + r ^ 4 :=
    congrArg₂ (fun left right : ℝ => left + right)
      (congrArg₂ (fun left right : ℝ => left + right)
        (congrArg₂ (fun left right : ℝ => left + right)
          (congrArg₂ (fun left right : ℝ => left + right) hf₀ hf₁)
          hf₂)
        hf₃)
      hf₄
  exact Eq.trans hbinomial (Eq.trans hsumExpand hterms)

theorem Real.mul_five_term_sum
    (M a b c d e : ℝ) :
    M * a + M * b + M * c + M * d + M * e =
      M * (a + b + c + d + e) := by
  have hab : M * a + M * b = M * (a + b) := (mul_add M a b).symm
  have habc : M * a + M * b + M * c = M * (a + b + c) :=
    Eq.trans (congrArg (fun value : ℝ => value + M * c) hab)
      (mul_add M (a + b) c).symm
  have habcd : M * a + M * b + M * c + M * d =
      M * (a + b + c + d) :=
    Eq.trans (congrArg (fun value : ℝ => value + M * d) habc)
      (mul_add M (a + b + c) d).symm
  exact Eq.trans (congrArg (fun value : ℝ => value + M * e) habcd)
    (mul_add M (a + b + c + d) e).symm

/-- The five degree-four Bernstein weights are nonnegative barycentric
weights and therefore transfer the coefficient bound by sixteen. -/
theorem Real.shiftedReciprocalPositiveQuarticEnvelope_le_sixteen
    {r y : ℝ}
    (hr : 0 ≤ r) (hy : 0 ≤ y)
    (hsum : r + y = 1) :
    Real.shiftedReciprocalPositiveQuarticEnvelope r y ≤ 16 := by
  have hw₀ : 0 ≤ y ^ 4 := pow_nonneg hy 4
  have hw₁ : 0 ≤ 4 * (r * y ^ 3) :=
    mul_nonneg (Nat.cast_nonneg 4)
      (mul_nonneg hr (pow_nonneg hy 3))
  have hw₂ : 0 ≤ 6 * (r ^ 2 * y ^ 2) :=
    mul_nonneg (Nat.cast_nonneg 6)
      (mul_nonneg (pow_nonneg hr 2) (pow_nonneg hy 2))
  have hw₃ : 0 ≤ 4 * (r ^ 3 * y) :=
    mul_nonneg (Nat.cast_nonneg 4)
      (mul_nonneg (pow_nonneg hr 3) hy)
  have hw₄ : 0 ≤ r ^ 4 := pow_nonneg hr 4
  have hb₀ := mul_le_mul_of_nonneg_right
    positiveQuartic_eight_thirds_le_sixteen hw₀
  have hb₁ := mul_le_mul_of_nonneg_right
    positiveQuartic_five_thirds_le_sixteen hw₁
  have hb₂ := mul_le_mul_of_nonneg_right
    positiveQuartic_eightNineFourFive_le_sixteen hw₂
  have hb₃ := mul_le_mul_of_nonneg_right
    positiveQuartic_oneNineZeroTwoFive_le_sixteen hw₃
  have hb₄ := mul_le_mul_of_nonneg_right
    positiveQuartic_sixOneSevenOne_le_sixteen hw₄
  have hleft₁ :
      4 * (5 / 3 : ℝ) * (r * y ^ 3) =
        (5 / 3) * (4 * (r * y ^ 3)) := by
    calc
      4 * (5 / 3 : ℝ) * (r * y ^ 3) =
          (5 / 3) * 4 * (r * y ^ 3) :=
        congrArg (fun value : ℝ => value * (r * y ^ 3))
          (mul_comm 4 (5 / 3 : ℝ))
      _ = (5 / 3) * (4 * (r * y ^ 3)) :=
        mul_assoc (5 / 3 : ℝ) 4 (r * y ^ 3)
  have hleft₂ :
      6 * (8945 / 2304 : ℝ) * (r ^ 2 * y ^ 2) =
        (8945 / 2304) * (6 * (r ^ 2 * y ^ 2)) := by
    calc
      6 * (8945 / 2304 : ℝ) * (r ^ 2 * y ^ 2) =
          (8945 / 2304) * 6 * (r ^ 2 * y ^ 2) :=
        congrArg (fun value : ℝ => value * (r ^ 2 * y ^ 2))
          (mul_comm 6 (8945 / 2304 : ℝ))
      _ = (8945 / 2304) * (6 * (r ^ 2 * y ^ 2)) :=
        mul_assoc (8945 / 2304 : ℝ) 6 (r ^ 2 * y ^ 2)
  have hleft₃ :
      4 * (19025 / 1536 : ℝ) * (r ^ 3 * y) =
        (19025 / 1536) * (4 * (r ^ 3 * y)) := by
    calc
      4 * (19025 / 1536 : ℝ) * (r ^ 3 * y) =
          (19025 / 1536) * 4 * (r ^ 3 * y) :=
        congrArg (fun value : ℝ => value * (r ^ 3 * y))
          (mul_comm 4 (19025 / 1536 : ℝ))
      _ = (19025 / 1536) * (4 * (r ^ 3 * y)) :=
        mul_assoc (19025 / 1536 : ℝ) 4 (r ^ 3 * y)
  have hweighted :
      Real.shiftedReciprocalPositiveQuarticEnvelope r y ≤
        16 * y ^ 4 +
          16 * (4 * (r * y ^ 3)) +
          16 * (6 * (r ^ 2 * y ^ 2)) +
          16 * (4 * (r ^ 3 * y)) +
          16 * r ^ 4 := by
    unfold Real.shiftedReciprocalPositiveQuarticEnvelope
    exact le_trans
      (le_of_eq
        (congrArg₂ (fun left right : ℝ => left + right)
          (congrArg₂ (fun left right : ℝ => left + right)
            (congrArg₂ (fun left right : ℝ => left + right)
              (congrArg₂ (fun left right : ℝ => left + right)
                rfl hleft₁)
              hleft₂)
            hleft₃)
          rfl))
      (add_le_add (add_le_add (add_le_add (add_le_add hb₀ hb₁) hb₂) hb₃) hb₄)
  have hweights :
      y ^ 4 + 4 * (r * y ^ 3) + 6 * (r ^ 2 * y ^ 2) +
          4 * (r ^ 3 * y) + r ^ 4 = 1 := by
    have hpower : (r + y) ^ 4 = (1 : ℝ) ^ 4 :=
      congrArg (fun value : ℝ => value ^ 4) hsum
    have hexpand := Real.add_pow_four_explicit r y
    exact Eq.trans hexpand.symm
      (Eq.trans hpower (one_pow 4))
  have hfactor :
      16 * y ^ 4 +
          16 * (4 * (r * y ^ 3)) +
          16 * (6 * (r ^ 2 * y ^ 2)) +
          16 * (4 * (r ^ 3 * y)) +
          16 * r ^ 4 =
        16 *
          (y ^ 4 + 4 * (r * y ^ 3) + 6 * (r ^ 2 * y ^ 2) +
            4 * (r ^ 3 * y) + r ^ 4) :=
    Real.mul_five_term_sum 16
      (y ^ 4) (4 * (r * y ^ 3)) (6 * (r ^ 2 * y ^ 2))
      (4 * (r ^ 3 * y)) (r ^ 4)
  have hnormalize :
      16 * y ^ 4 +
          16 * (4 * (r * y ^ 3)) +
          16 * (6 * (r ^ 2 * y ^ 2)) +
          16 * (4 * (r ^ 3 * y)) +
          16 * r ^ 4 = 16 :=
    Eq.trans hfactor
      (Eq.trans (congrArg (fun value : ℝ => 16 * value) hweights)
        (mul_one 16))
  exact le_trans hweighted (le_of_eq hnormalize)

/-- The quartic in fact fits below the exact positive-tail ledger, leaving the
existing global coefficient accounting unchanged. -/
theorem Real.shiftedReciprocalPositiveQuarticEnvelope_le_exactMajorant
    {r y : ℝ}
    (hr : 0 ≤ r) (hy : 0 ≤ y)
    (hsum : r + y = 1) :
    Real.shiftedReciprocalPositiveQuarticEnvelope r y ≤
      Real.shiftedReciprocalPositiveQuarticExactMajorant := by
  let M : ℝ := Real.shiftedReciprocalPositiveQuarticExactMajorant
  have hw₀ : 0 ≤ y ^ 4 := pow_nonneg hy 4
  have hw₁ : 0 ≤ 4 * (r * y ^ 3) :=
    mul_nonneg (Nat.cast_nonneg 4)
      (mul_nonneg hr (pow_nonneg hy 3))
  have hw₂ : 0 ≤ 6 * (r ^ 2 * y ^ 2) :=
    mul_nonneg (Nat.cast_nonneg 6)
      (mul_nonneg (pow_nonneg hr 2) (pow_nonneg hy 2))
  have hw₃ : 0 ≤ 4 * (r ^ 3 * y) :=
    mul_nonneg (Nat.cast_nonneg 4)
      (mul_nonneg (pow_nonneg hr 3) hy)
  have hw₄ : 0 ≤ r ^ 4 := pow_nonneg hr 4
  have hb₀ := mul_le_mul_of_nonneg_right
    positiveQuartic_eight_thirds_le_exact hw₀
  have hb₁ := mul_le_mul_of_nonneg_right
    positiveQuartic_five_thirds_le_exact hw₁
  have hb₂ := mul_le_mul_of_nonneg_right
    positiveQuartic_eightNineFourFive_le_exact hw₂
  have hb₃ := mul_le_mul_of_nonneg_right
    positiveQuartic_oneNineZeroTwoFive_le_exact hw₃
  have hb₄ := mul_le_mul_of_nonneg_right
    positiveQuartic_sixOneSevenOne_le_exact hw₄
  have hleft₁ :
      4 * (5 / 3 : ℝ) * (r * y ^ 3) =
        (5 / 3) * (4 * (r * y ^ 3)) := by
    exact Eq.trans
      (congrArg (fun value : ℝ => value * (r * y ^ 3))
        (mul_comm 4 (5 / 3 : ℝ)))
      (mul_assoc (5 / 3 : ℝ) 4 (r * y ^ 3))
  have hleft₂ :
      6 * (8945 / 2304 : ℝ) * (r ^ 2 * y ^ 2) =
        (8945 / 2304) * (6 * (r ^ 2 * y ^ 2)) := by
    exact Eq.trans
      (congrArg (fun value : ℝ => value * (r ^ 2 * y ^ 2))
        (mul_comm 6 (8945 / 2304 : ℝ)))
      (mul_assoc (8945 / 2304 : ℝ) 6 (r ^ 2 * y ^ 2))
  have hleft₃ :
      4 * (19025 / 1536 : ℝ) * (r ^ 3 * y) =
        (19025 / 1536) * (4 * (r ^ 3 * y)) := by
    exact Eq.trans
      (congrArg (fun value : ℝ => value * (r ^ 3 * y))
        (mul_comm 4 (19025 / 1536 : ℝ)))
      (mul_assoc (19025 / 1536 : ℝ) 4 (r ^ 3 * y))
  have hweighted :
      Real.shiftedReciprocalPositiveQuarticEnvelope r y ≤
        M * y ^ 4 +
          M * (4 * (r * y ^ 3)) +
          M * (6 * (r ^ 2 * y ^ 2)) +
          M * (4 * (r ^ 3 * y)) +
          M * r ^ 4 := by
    unfold Real.shiftedReciprocalPositiveQuarticEnvelope
    exact le_trans
      (le_of_eq
        (congrArg₂ (fun left right : ℝ => left + right)
          (congrArg₂ (fun left right : ℝ => left + right)
            (congrArg₂ (fun left right : ℝ => left + right)
              (congrArg₂ (fun left right : ℝ => left + right)
                rfl hleft₁)
              hleft₂)
            hleft₃)
          rfl))
      (add_le_add (add_le_add (add_le_add (add_le_add hb₀ hb₁) hb₂) hb₃) hb₄)
  have hweights :
      y ^ 4 + 4 * (r * y ^ 3) + 6 * (r ^ 2 * y ^ 2) +
          4 * (r ^ 3 * y) + r ^ 4 = 1 := by
    have hpower : (r + y) ^ 4 = (1 : ℝ) ^ 4 :=
      congrArg (fun value : ℝ => value ^ 4) hsum
    have hexpand := Real.add_pow_four_explicit r y
    exact Eq.trans hexpand.symm (Eq.trans hpower (one_pow 4))
  have hfactor :
      M * y ^ 4 +
          M * (4 * (r * y ^ 3)) +
          M * (6 * (r ^ 2 * y ^ 2)) +
          M * (4 * (r ^ 3 * y)) +
          M * r ^ 4 =
        M *
          (y ^ 4 + 4 * (r * y ^ 3) + 6 * (r ^ 2 * y ^ 2) +
            4 * (r ^ 3 * y) + r ^ 4) :=
    Real.mul_five_term_sum M
      (y ^ 4) (4 * (r * y ^ 3)) (6 * (r ^ 2 * y ^ 2))
      (4 * (r ^ 3 * y)) (r ^ 4)
  have hnormalize :
      M * y ^ 4 +
          M * (4 * (r * y ^ 3)) +
          M * (6 * (r ^ 2 * y ^ 2)) +
          M * (4 * (r ^ 3 * y)) +
          M * r ^ 4 = M :=
    Eq.trans hfactor
      (Eq.trans (congrArg (fun value : ℝ => M * value) hweights)
        (mul_one M))
  exact le_trans hweighted
    (le_trans (le_of_eq hnormalize) (le_of_eq rfl))

end

end LFunctions
end Boundary
