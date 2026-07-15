import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ClassicalAnalysis.OscillatorySums.ShiftedReciprocalPowerSpecializations

/-!
# Embedding finite frequency families into shifted reciprocal series

A finite family whose modes inject into natural indices may be bounded by a
summable nonnegative series on all natural numbers.  This owner isolates the
finite-to-infinite transport used by finite inactive packet families; the
analytic shifted reciprocal estimates remain independent of the particular
integer-frequency reindexing.
-/

namespace Boundary
namespace LFunctions

noncomputable section

theorem Finset.sum_le_tsum_of_subtype_injection
    {α : Type*} [DecidableEq α]
    (s : Finset α)
    (f : α → ℝ)
    (g : ℕ → ℝ)
    (index : {x : α // x ∈ s} → ℕ)
    (hindex : Function.Injective index)
    (hfg : ∀ x : {x : α // x ∈ s}, f x ≤ g (index x))
    (hgNonneg : ∀ n : ℕ, 0 ≤ g n)
    (hg : Summable g) :
    ∑ x ∈ s, f x ≤ ∑' n : ℕ, g n := by
  have hfinite :
      (∑' x : {x : α // x ∈ s}, f x) = ∑ x ∈ s, f x :=
    s.tsum_subtype f
  have hfSummable : Summable (fun x : {x : α // x ∈ s} => f x) :=
    summable_of_finite_support
      (Set.toFinite (Function.support
        (fun x : {x : α // x ∈ s} => f x)))
  have hsubtype :
      (∑' x : {x : α // x ∈ s}, f x) ≤ ∑' n : ℕ, g n :=
    tsum_le_tsum_of_inj index hindex
      (fun n _hn => hgNonneg n)
      hfg hfSummable hg
  exact le_trans (le_of_eq hfinite.symm) hsubtype

theorem Finset.sum_le_shiftedReciprocalPower_tsum_of_injection
    {α : Type*} [DecidableEq α]
    (s : Finset α)
    (f : α → ℝ)
    (index : {x : α // x ∈ s} → ℕ)
    (hindex : Function.Injective index)
    (A c p : ℝ)
    (hA : 0 ≤ A) (hc : 0 < c) (hp : 1 < p)
    (hfg : ∀ x : {x : α // x ∈ s},
      f x ≤ Real.shiftedReciprocalPowerSeriesTerm A c p (index x)) :
    ∑ x ∈ s, f x ≤
      ∑' n : ℕ, Real.shiftedReciprocalPowerSeriesTerm A c p n := by
  exact Finset.sum_le_tsum_of_subtype_injection
    s f (Real.shiftedReciprocalPowerSeriesTerm A c p)
    index hindex hfg
    (Real.shiftedReciprocalPowerSeriesTerm_nonneg A c p · hA hc.le)
    (Real.summable_shiftedReciprocalPowerSeriesTerm A c p hA hc hp)

theorem Finset.sum_le_shiftedReciprocalPower_seriesBudget_of_injection
    {α : Type*} [DecidableEq α]
    (s : Finset α)
    (f : α → ℝ)
    (index : {x : α // x ∈ s} → ℕ)
    (hindex : Function.Injective index)
    (A c p : ℝ)
    (hA : 0 ≤ A) (hc : 0 < c) (hp : 1 < p)
    (hfg : ∀ x : {x : α // x ∈ s},
      f x ≤ Real.shiftedReciprocalPowerSeriesTerm A c p (index x)) :
    ∑ x ∈ s, f x ≤
      Real.shiftedReciprocalPowerSeriesBudget A c p := by
  have hseries :=
    Finset.sum_le_shiftedReciprocalPower_tsum_of_injection
      s f index hindex A c p hA hc hp hfg
  have hbudget :=
    Real.tsum_shiftedReciprocalPowerSeriesTerm_le_seriesBudget
      A c p hA hc hp
  exact le_trans hseries hbudget

theorem Finset.sum_inverseSquare_le_shiftedSeriesBudget_of_injection
    {α : Type*} [DecidableEq α]
    (s : Finset α)
    (gap : α → ℝ)
    (index : {x : α // x ∈ s} → ℕ)
    (hindex : Function.Injective index)
    (A c : ℝ)
    (hA : 0 ≤ A) (hc : 0 < c)
    (hgap : ∀ x : {x : α // x ∈ s},
      A + c * ((index x : ℝ) + 1) ≤ gap x) :
    ∑ x ∈ s, 1 / (gap x) ^ 2 ≤
      Real.shiftedInverseSquareSeriesBudget A c := by
  have hbasePos : ∀ x : {x : α // x ∈ s},
      0 < A + c * ((index x : ℝ) + 1) := by
    intro x
    exact add_pos_of_nonneg_of_pos hA
      (mul_pos hc (add_pos_of_nonneg_of_pos (Nat.cast_nonneg _) zero_lt_one))
  have hpoint : ∀ x : {x : α // x ∈ s},
      1 / (gap x) ^ 2 ≤ Real.shiftedInverseSquareTerm A c (index x) := by
    intro x
    unfold Real.shiftedInverseSquareTerm
    have hpositive := hbasePos x
    have hgapNonneg := le_trans hpositive.le (hgap x)
    have hsquare := mul_le_mul (hgap x) (hgap x)
      hpositive.le hgapNonneg
    have hsquareForm :
        (A + c * ((index x : ℝ) + 1)) ^ 2 ≤ (gap x) ^ 2 :=
      le_trans
        (le_of_eq (pow_two (A + c * ((index x : ℝ) + 1))))
        (le_trans hsquare (le_of_eq (pow_two (gap x)).symm))
    have hinverse := one_div_le_one_div_of_le
      (sq_pos_of_pos hpositive) hsquareForm
    exact hinverse
  have hsum := Finset.sum_le_tsum_of_subtype_injection
    s (fun x => 1 / (gap x) ^ 2)
    (Real.shiftedInverseSquareTerm A c)
    index hindex hpoint
    (Real.shiftedInverseSquareTerm_nonneg A c hA hc)
    (Real.summable_shiftedInverseSquareTerm A c hA hc)
  have hbudget := Real.tsum_shiftedInverseSquareTerm_le A c hA hc
  exact le_trans hsum hbudget

theorem Finset.sum_inverseCube_le_shiftedSeriesBudget_of_injection
    {α : Type*} [DecidableEq α]
    (s : Finset α)
    (gap : α → ℝ)
    (index : {x : α // x ∈ s} → ℕ)
    (hindex : Function.Injective index)
    (A c : ℝ)
    (hA : 0 ≤ A) (hc : 0 < c)
    (hgapNonneg : ∀ x ∈ s, 0 ≤ gap x)
    (hpoint : ∀ x : {x : α // x ∈ s},
      1 / (gap x) ^ 3 ≤ Real.shiftedInverseCubeTerm A c (index x)) :
    ∑ x ∈ s, 1 / (gap x) ^ 3 ≤
      Real.shiftedInverseCubeSeriesBudget A c := by
  have hsum := Finset.sum_le_tsum_of_subtype_injection
    s (fun x => 1 / (gap x) ^ 3)
    (Real.shiftedInverseCubeTerm A c)
    index hindex hpoint
    (Real.shiftedInverseCubeTerm_nonneg A c hA hc)
    (Real.summable_shiftedInverseCubeTerm A c hA hc)
  have hbudget := Real.tsum_shiftedInverseCubeTerm_le A c hA hc
  exact le_trans hsum hbudget

theorem Finset.sum_inverseFourth_le_shiftedSeriesBudget_of_injection
    {α : Type*} [DecidableEq α]
    (s : Finset α)
    (gap : α → ℝ)
    (index : {x : α // x ∈ s} → ℕ)
    (hindex : Function.Injective index)
    (A c : ℝ)
    (hA : 0 ≤ A) (hc : 0 < c)
    (hgapNonneg : ∀ x ∈ s, 0 ≤ gap x)
    (hpoint : ∀ x : {x : α // x ∈ s},
      1 / (gap x) ^ 4 ≤ Real.shiftedInverseFourthTerm A c (index x)) :
    ∑ x ∈ s, 1 / (gap x) ^ 4 ≤
      Real.shiftedInverseFourthSeriesBudget A c := by
  have hsum := Finset.sum_le_tsum_of_subtype_injection
    s (fun x => 1 / (gap x) ^ 4)
    (Real.shiftedInverseFourthTerm A c)
    index hindex hpoint
    (Real.shiftedInverseFourthTerm_nonneg A c hA hc)
    (Real.summable_shiftedInverseFourthTerm A c hA hc)
  have hbudget := Real.tsum_shiftedInverseFourthTerm_le A c hA hc
  exact le_trans hsum hbudget

theorem Finset.sum_scaled_inversePower_le_scaled_budget
    {α : Type*} [DecidableEq α]
    (s : Finset α) (f : α → ℝ)
    (coefficient budget : ℝ)
    (hcoefficient : 0 ≤ coefficient)
    (hsum : ∑ x ∈ s, f x ≤ budget) :
    ∑ x ∈ s, coefficient * f x ≤ coefficient * budget := by
  have hfactor :
      (∑ x ∈ s, coefficient * f x) =
        coefficient * ∑ x ∈ s, f x := by
    exact (Finset.mul_sum s (fun x => f x) coefficient).symm
  have hscaled := mul_le_mul_of_nonneg_left hsum hcoefficient
  exact Eq.subst
    (motive := fun value : ℝ => value ≤ coefficient * budget)
    hfactor.symm hscaled

end

end LFunctions
end Boundary
