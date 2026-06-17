import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ClassicalAnalysis.GammaBinetStirling.BinetAbelPlanaSemicircleGraph

/-!
# Semicircle vertical partition layer for finite-height Abel-Plana collars

This file owns the vertical integral partition, uniform height mesh facts, and
the first horizontal sample-sum definitions built from the right-semicircle
graph layer.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open scoped Topology Interval
open Filter MeasureTheory

/-- The graph vertical integral splits over the staircase height partition. -/
theorem Complex.rightSemicircleGraphVerticalIntegral_eq_sum_cells
    (f : ℂ → ℂ)
    (c : ℂ)
    {ρ : ℝ}
    (hρ : 0 < ρ)
    (hcont :
      ContinuousOn f
        (Complex.rightHalfRectangleDeletedDiskCoreDomain c ρ ρ))
    (m : ℕ) :
    Complex.rightSemicircleGraphVerticalIntegral f c ρ =
      Complex.I *
        ∑ k in Finset.range (m + 1),
          ∫ y : ℝ in
            Complex.rightSemicircleStaircaseY ρ m k..
              Complex.rightSemicircleStaircaseY ρ m (k + 1),
            f (Complex.rightSemicircleGraphPoint c ρ y) := by
  let F : ℝ → ℂ := fun y => f (Complex.rightSemicircleGraphPoint c ρ y)
  let a : ℕ → ℝ := fun k => Complex.rightSemicircleStaircaseY ρ m k
  have hA : a 0 = -ρ := by
    exact Complex.rightSemicircleStaircaseY_zero ρ m
  have hB : a (m + 1) = ρ := by
    exact Complex.rightSemicircleStaircaseY_last ρ m
  have hF :
      IntervalIntegrable F volume (-ρ) ρ :=
    Complex.intervalIntegrable_rightSemicircleGraphVertical f c hρ hcont
  have hint :
      ∀ k < m + 1, IntervalIntegrable F volume (a k) (a (k + 1)) := by
    intro k hk
    have hk_cell : k ∈ Finset.range (m + 1) :=
      Finset.mem_range.mpr hk
    have hk0 : k ∈ Finset.range (m + 2) := by
      exact Complex.staircase_lower_sample_mem_range hk_cell
    have hk1 : k + 1 ∈ Finset.range (m + 2) := by
      exact Complex.staircase_upper_sample_mem_range hk_cell
    have hyk :
        a k ∈ [[-ρ, ρ]] := by
      exact Complex.rightSemicircleStaircaseY_mem_Icc hρ.le m k hk0
    have hyk1 :
        a (k + 1) ∈ [[-ρ, ρ]] := by
      exact Complex.rightSemicircleStaircaseY_mem_Icc hρ.le m (k + 1) hk1
    exact Complex.intervalIntegrable_of_mem_uIcc hF hyk hyk1
  show
    Complex.I *
      (∫ y : ℝ in (-ρ)..ρ,
        f (Complex.rightSemicircleGraphPoint c ρ y)) =
      Complex.I *
        ∑ k in Finset.range (m + 1),
          ∫ y : ℝ in
            Complex.rightSemicircleStaircaseY ρ m k..
              Complex.rightSemicircleStaircaseY ρ m (k + 1),
            f (Complex.rightSemicircleGraphPoint c ρ y)
  exact
    congrArg
      (fun z : ℂ => Complex.I * z)
      (Complex.integral_eq_sum_adjacent_intervals_of_endpoint_chain
        F a (m + 1) (-ρ) ρ hA hB hint)

/-- The staircase vertical sum is `I` times the sum of its real-parameterized
cell integrals. -/
theorem Complex.sum_rightSemicircleStaircaseVerticalIntegral_eq_I_mul_sum
    (f : ℂ → ℂ)
    (c : ℂ)
    (ρ : ℝ)
    (m : ℕ) :
    (∑ k in Finset.range (m + 1),
      Complex.rightSemicircleStaircaseVerticalIntegral f c ρ m k) =
      Complex.I *
        ∑ k in Finset.range (m + 1),
          ∫ y : ℝ in
            Complex.rightSemicircleStaircaseY ρ m k..
              Complex.rightSemicircleStaircaseY ρ m (k + 1),
            f (((c.re + Complex.rightSemicircleStaircaseSafeRe ρ m k : ℝ) : ℂ) +
              Complex.I * (((c.im + y : ℝ) : ℂ))) := by
  let cell : ℕ → ℂ :=
    fun k =>
      ∫ y : ℝ in
        Complex.rightSemicircleStaircaseY ρ m k..
          Complex.rightSemicircleStaircaseY ρ m (k + 1),
        f (((c.re + Complex.rightSemicircleStaircaseSafeRe ρ m k : ℝ) : ℂ) +
          Complex.I * (((c.im + y : ℝ) : ℂ)))
  show
    (∑ k in Finset.range (m + 1),
      Complex.I * cell k) =
      Complex.I *
        ∑ k in Finset.range (m + 1), cell k
  exact
    Eq.symm
      (Finset.mul_sum (Finset.range (m + 1)) cell Complex.I)

/-- The uniform height mesh of the staircase partition. -/
theorem Complex.rightSemicircleStaircase_cell_length
    (ρ : ℝ)
    (m k : ℕ) :
    Complex.rightSemicircleStaircaseY ρ m (k + 1) -
      Complex.rightSemicircleStaircaseY ρ m k =
        (2 * ρ) / (m + 1 : ℝ) := by
  exact Complex.rightSemicircleStaircaseY_succ_sub ρ m k

/-- The real number `2` is nonnegative. -/
theorem real_two_nonneg :
    0 ≤ (2 : ℝ) := by
  exact zero_le_two

/-- A successor natural number has positive real cast. -/
theorem real_nat_succ_cast_pos
    (m : ℕ) :
    0 < (m + 1 : ℝ) := by
  exact add_pos_of_nonneg_of_pos (Nat.cast_nonneg m) zero_lt_one

/-- A successor natural number has nonzero real cast. -/
theorem real_nat_succ_cast_ne_zero
    (m : ℕ) :
    (m + 1 : ℝ) ≠ 0 := by
  exact ne_of_gt (real_nat_succ_cast_pos m)

/-- Casting a successor denominator to `ℝ` agrees with real addition by one. -/
theorem real_nat_succ_cast_eq_add_one
    (m : ℕ) :
    ((m + 1 : ℕ) : ℝ) = (m + 1 : ℝ) := by
  calc
    ((m + 1 : ℕ) : ℝ) = (m : ℝ) + ((1 : ℕ) : ℝ) :=
      Nat.cast_add m 1
    _ = (m : ℝ) + 1 :=
      congrArg (fun r : ℝ => (m : ℝ) + r) Nat.cast_one

/-- The real number `6` is positive. -/
theorem real_six_pos : 0 < (6 : ℝ) := by
  show 0 < ((6 : ℕ) : ℝ)
  exact Nat.cast_pos.mpr (Nat.succ_pos 5)

/-- Half of `π` is nonnegative. -/
theorem real_pi_div_two_nonneg : 0 ≤ Real.pi / 2 := by
  exact div_nonneg (le_of_lt Real.pi_pos) zero_le_two

/-- Twice a positive radius is positive. -/
theorem real_two_mul_pos_of_pos
    {ρ : ℝ}
    (hρ : 0 < ρ) :
    0 < 2 * ρ := by
  exact mul_pos zero_lt_two hρ

/-- Six times a positive radius is positive. -/
theorem real_six_mul_pos_of_pos
    {ρ : ℝ}
    (hρ : 0 < ρ) :
    0 < 6 * ρ := by
  exact mul_pos real_six_pos hρ

/-- Absolute length of one uniform staircase height cell. -/
theorem Complex.rightSemicircleStaircase_cell_length_abs
    {ρ : ℝ}
    (hρ : 0 ≤ ρ)
    (m k : ℕ) :
    |Complex.rightSemicircleStaircaseY ρ m (k + 1) -
      Complex.rightSemicircleStaircaseY ρ m k| =
        (2 * ρ) / (m + 1 : ℝ) := by
  have hden_nonneg : 0 ≤ (m + 1 : ℝ) := by
    exact le_of_lt (real_nat_succ_cast_pos m)
  have hcell :
      Complex.rightSemicircleStaircaseY ρ m (k + 1) -
        Complex.rightSemicircleStaircaseY ρ m k =
          (2 * ρ) / (m + 1 : ℝ) :=
    Complex.rightSemicircleStaircase_cell_length ρ m k
  exact
    Eq.trans
      (congrArg abs hcell)
      (abs_of_nonneg
        (div_nonneg (mul_nonneg real_two_nonneg hρ) hden_nonneg))

/-- A real number below `N` is below `m+1` whenever `N ≤ m`. -/
theorem real_lt_nat_succ_of_lt_nat_of_nat_le
    {q : ℝ}
    {N m : ℕ}
    (hN : q < (N : ℝ))
    (hm : N ≤ m) :
    q < (m + 1 : ℝ) := by
  have hN_le_m : (N : ℝ) ≤ (m : ℝ) := by
    exact Nat.cast_le.mpr hm
  have hm_lt_succ : (m : ℝ) < (m + 1 : ℝ) := by
    exact lt_add_one (m : ℝ)
  exact lt_of_lt_of_le hN (le_of_lt (lt_of_le_of_lt hN_le_m hm_lt_succ))

/-- Dividing a strict product bound by a positive successor denominator. -/
theorem div_nat_succ_lt_of_lt_mul
    {A δ : ℝ}
    (hδ : 0 < δ)
    (m : ℕ)
    (hA : A < δ * (m + 1 : ℝ)) :
    A / (m + 1 : ℝ) < δ := by
  have hden : 0 < (m + 1 : ℝ) :=
    real_nat_succ_cast_pos m
  have hcomm : δ * (m + 1 : ℝ) = (m + 1 : ℝ) * δ :=
    mul_comm δ (m + 1 : ℝ)
  have hA_ordered : A < (m + 1 : ℝ) * δ :=
    Eq.subst
      (motive := fun x : ℝ => A < x)
      hcomm
      hA
  exact (div_lt_iff₀' hden).mpr hA_ordered

/-- Dividing by a positive scale and multiplying back by that scale recovers
the original quantity. -/
theorem div_mul_cancel_of_pos_right
    {ε A : ℝ}
    (hA : 0 < A) :
    (ε / A) * A = ε := by
  have hA_ne : A ≠ 0 := ne_of_gt hA
  exact div_mul_cancel₀ ε hA_ne

/-- The explicit real numeral equality used to collect three radius errors. -/
theorem real_two_add_two_add_two_eq_six :
    ((2 + 2 : ℝ) + 2) = 6 := by
  have htwo_two_cast :
      (((2 + 2 : ℕ) : ℝ)) = ((2 : ℝ) + (2 : ℝ)) :=
    Nat.cast_add 2 2
  have htwo_two_two_cast :
      ((((2 + 2 : ℕ) + 2 : ℕ) : ℝ)) =
        (((2 + 2 : ℕ) : ℝ) + (2 : ℝ)) :=
    Nat.cast_add (2 + 2) 2
  have hnat : ((2 + 2 : ℕ) + 2) = 6 :=
    rfl
  calc
    ((2 + 2 : ℝ) + 2) =
        (((2 + 2 : ℕ) : ℝ) + (2 : ℝ)) := by
      exact congrArg (fun x : ℝ => x + (2 : ℝ)) (Eq.symm htwo_two_cast)
    _ = ((((2 + 2 : ℕ) + 2 : ℕ) : ℝ)) :=
      Eq.symm htwo_two_two_cast
    _ = (6 : ℝ) :=
      congrArg (fun n : ℕ => (n : ℝ)) hnat

/-- Three error contributions of size `η * (2ρ)` are bounded by the single
scale `η * (6ρ)`. -/
theorem three_two_radius_errors_le_six_radius_error
    {η ρ : ℝ}
    (hη : 0 ≤ η)
    (hρ : 0 ≤ ρ) :
    η * (2 * ρ) + η * (2 * ρ) + η * (2 * ρ) ≤ η * (6 * ρ) := by
  have hsum :
      (2 * ρ + 2 * ρ) + 2 * ρ = 6 * ρ := by
    calc
      (2 * ρ + 2 * ρ) + 2 * ρ
          = (2 + 2 : ℝ) * ρ + 2 * ρ := by
            exact
              congrArg (fun x : ℝ => x + 2 * ρ)
                (Eq.symm (add_mul (2 : ℝ) (2 : ℝ) ρ))
        _ = ((2 + 2 : ℝ) + 2) * ρ := by
              exact Eq.symm (add_mul (2 + 2 : ℝ) (2 : ℝ) ρ)
        _ = 6 * ρ := by
              exact
                congrArg
                  (fun x : ℝ => x * ρ)
                  real_two_add_two_add_two_eq_six
  have heq :
      η * (2 * ρ) + η * (2 * ρ) + η * (2 * ρ) =
        η * (6 * ρ) := by
    calc
      η * (2 * ρ) + η * (2 * ρ) + η * (2 * ρ)
          = η * (2 * ρ + 2 * ρ) + η * (2 * ρ) := by
            exact
              congrArg (fun x : ℝ => x + η * (2 * ρ))
                (Eq.symm (mul_add η (2 * ρ) (2 * ρ)))
      _ = η * ((2 * ρ + 2 * ρ) + 2 * ρ) := by
            exact Eq.symm (mul_add η (2 * ρ + 2 * ρ) (2 * ρ))
      _ = η * (6 * ρ) := by
            exact congrArg (fun x : ℝ => η * x) hsum
  exact le_of_eq heq

/-- Two quantities each bounded by the same radius have sum bounded by twice
that radius. -/
theorem add_le_two_mul_of_each_le
    {a b ρ : ℝ}
    (ha : a ≤ ρ)
    (hb : b ≤ ρ) :
    a + b ≤ 2 * ρ := by
  calc
    a + b ≤ ρ + ρ := add_le_add ha hb
    _ = 2 * ρ := (two_mul ρ).symm

/-- The uniform staircase mesh tends to zero. -/
theorem Complex.eventually_rightSemicircleStaircase_cell_length_lt
    {ρ δ : ℝ}
    (hρ : 0 < ρ)
    (hδ : 0 < δ) :
    ∀ᶠ m : ℕ in atTop,
      ∀ k ∈ Finset.range (m + 1),
        |Complex.rightSemicircleStaircaseY ρ m (k + 1) -
          Complex.rightSemicircleStaircaseY ρ m k| < δ := by
  let ⟨N, hN⟩ := exists_nat_gt ((2 * ρ) / δ)
  filter_upwards [eventually_ge_atTop N] with m hm k hk
  have hquot_lt_succ : (2 * ρ) / δ < (m + 1 : ℝ) := by
    exact real_lt_nat_succ_of_lt_nat_of_nat_le hN hm
  have hmul_lt : 2 * ρ < δ * (m + 1 : ℝ) := by
    have hordered : 2 * ρ < (m + 1 : ℝ) * δ :=
      (div_lt_iff₀ hδ).mp hquot_lt_succ
    have hcomm : (m + 1 : ℝ) * δ = δ * (m + 1 : ℝ) :=
      mul_comm (m + 1 : ℝ) δ
    exact
      Eq.subst
        (motive := fun x : ℝ => 2 * ρ < x)
        hcomm
        hordered
  have hlen_lt : (2 * ρ) / (m + 1 : ℝ) < δ := by
    exact div_nat_succ_lt_of_lt_mul hδ m hmul_lt
  exact
    (Complex.rightSemicircleStaircase_cell_length_abs hρ.le m k).symm ▸
      hlen_lt

/-- A uniform partition with `m + 1` cells of length `2ρ / (m + 1)` has total
length `2ρ`. -/
theorem nat_succ_mul_uniform_semicircle_cell_length
    (ρ : ℝ)
    (m : ℕ) :
    (m + 1 : ℝ) * ((2 * ρ) / (m + 1 : ℝ)) = 2 * ρ := by
  have hden : (m + 1 : ℝ) ≠ 0 :=
    real_nat_succ_cast_ne_zero m
  exact mul_div_cancel₀ (2 * ρ) hden

/-- A sum over `range (m + 1)` of a constant has the real successor multiple. -/
theorem Finset.sum_range_nat_succ_const_eq_real_mul
    (m : ℕ)
    (x : ℝ) :
    (∑ _k in Finset.range (m + 1), x) = (m + 1 : ℝ) * x := by
  have hcard : (Finset.range (m + 1)).card = m + 1 :=
    Finset.card_range (m + 1)
  have hnsmul :
      (m + 1) • x = (((m + 1 : ℕ) : ℝ) * x) :=
    nsmul_eq_mul (m + 1) x
  have hcast :
      (((m + 1 : ℕ) : ℝ) * x) = ((m + 1 : ℝ) * x) :=
    congrArg (fun r : ℝ => r * x) (real_nat_succ_cast_eq_add_one m)
  exact
    Eq.trans
      (Finset.sum_const x)
      (Eq.trans
        (congrArg (fun n : ℕ => n • x) hcard)
        (Eq.trans hnsmul hcast))

/-- Total length of the uniform staircase height partition. -/
theorem Complex.sum_rightSemicircleStaircase_cell_lengths
    {ρ : ℝ}
    (hρ : 0 ≤ ρ)
    (m : ℕ) :
    (∑ k in Finset.range (m + 1),
      |Complex.rightSemicircleStaircaseY ρ m (k + 1) -
        Complex.rightSemicircleStaircaseY ρ m k|) = 2 * ρ := by
  calc
    (∑ k in Finset.range (m + 1),
      |Complex.rightSemicircleStaircaseY ρ m (k + 1) -
        Complex.rightSemicircleStaircaseY ρ m k|)
        =
      ∑ _k in Finset.range (m + 1), (2 * ρ) / (m + 1 : ℝ) := by
        exact
          Finset.sum_congr rfl
            (fun k _hk =>
              Complex.rightSemicircleStaircase_cell_length_abs hρ m k)
    _ = (m + 1 : ℝ) * ((2 * ρ) / (m + 1 : ℝ)) := by
        exact Finset.sum_range_nat_succ_const_eq_real_mul m ((2 * ρ) / (m + 1 : ℝ))
    _ = 2 * ρ :=
        nat_succ_mul_uniform_semicircle_cell_length ρ m

/-- Finite-difference sample sum for the horizontal staircase contribution. -/
noncomputable def Complex.rightSemicircleStaircaseHorizontalSampleSum
    (f : ℂ → ℂ)
    (c : ℂ)
    (ρ : ℝ)
    (m : ℕ) : ℂ :=
  (∑ k in Finset.range (m + 1),
    f (Complex.rightSemicircleGraphPoint c ρ
        (Complex.rightSemicircleStaircaseY ρ m k)) *
      (((Complex.rightSemicircleStaircaseSafeRe ρ m k -
          Complex.rightSemicircleStaircasePrevSafeRe ρ m k : ℝ) : ℂ))) +
    f (Complex.rightSemicircleGraphPoint c ρ ρ) *
      (((0 - Complex.rightSemicircleStaircaseSafeRe ρ m m : ℝ) : ℂ))

/-- Graph-coordinate finite-difference sample sum for the horizontal
component of the right semicircle.  This is the canonical Riemann-Stieltjes
sample before replacing the graph finite differences by the exterior safe
staircase finite differences. -/
noncomputable def Complex.rightSemicircleGraphHorizontalSampleSum
    (f : ℂ → ℂ)
    (c : ℂ)
    (ρ : ℝ)
    (m : ℕ) : ℂ :=
  ∑ k in Finset.range (m + 1),
    f (Complex.rightSemicircleGraphPoint c ρ
        (Complex.rightSemicircleStaircaseY ρ m k)) *
      (((Complex.rightSemicircleGraphRe ρ
            (Complex.rightSemicircleStaircaseY ρ m (k + 1)) -
          Complex.rightSemicircleGraphRe ρ
            (Complex.rightSemicircleStaircaseY ρ m k) : ℝ) : ℂ))

end

end LFunctions
end Boundary
