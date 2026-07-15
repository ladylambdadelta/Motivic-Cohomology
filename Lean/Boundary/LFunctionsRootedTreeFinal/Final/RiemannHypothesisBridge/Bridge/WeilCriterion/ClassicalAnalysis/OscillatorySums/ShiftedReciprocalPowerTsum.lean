import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ClassicalAnalysis.OscillatorySums.ShiftedReciprocalPowerIntegral
import Mathlib.Topology.Algebra.InfiniteSum.Real

/-!
# Infinite shifted reciprocal-power bounds

This owner closes the finite sum--integral comparison into a summable series
estimate.  The shift `A` remains visible throughout.  That retention is the
feature needed by the logarithmic B-process: phase curvature is paired with
the endpoint part of the derivative gap before the frequency variable is
summed.
-/

namespace Boundary
namespace LFunctions

noncomputable section

def Real.shiftedReciprocalPowerSeriesTerm
    (A c p : ℝ) (n : ℕ) : ℝ :=
  Real.shiftedReciprocalPowerKernel A c p ((n : ℝ) + 1)

def Real.shiftedReciprocalPowerIntegralBudget
    (A c p : ℝ) : ℝ :=
  (A + c) ^ (1 - p) / (c * (p - 1))

def Real.shiftedReciprocalPowerSeriesBudget
    (A c p : ℝ) : ℝ :=
  Real.shiftedReciprocalPowerKernel A c p 1 +
    Real.shiftedReciprocalPowerIntegralBudget A c p

theorem Real.shiftedReciprocalPowerKernel_one_eq_seriesTerm_zero
    (A c p : ℝ) :
    Real.shiftedReciprocalPowerKernel A c p 1 =
      Real.shiftedReciprocalPowerSeriesTerm A c p 0 := by
  unfold Real.shiftedReciprocalPowerSeriesTerm
  exact congrArg (Real.shiftedReciprocalPowerKernel A c p)
    (Eq.trans (zero_add (1 : ℝ)).symm
      (congrArg (fun value : ℝ => value + 1) Nat.cast_zero).symm)

theorem Real.shiftedReciprocalPowerSeriesTerm_nonneg
    (A c p : ℝ) (n : ℕ) (hA : 0 ≤ A) (hc : 0 ≤ c) :
    0 ≤ Real.shiftedReciprocalPowerSeriesTerm A c p n := by
  unfold Real.shiftedReciprocalPowerSeriesTerm
  exact Real.shiftedReciprocalPowerKernel_nonneg A c p ((n : ℝ) + 1)
    hA hc (by exact add_nonneg (Nat.cast_nonneg n) zero_le_one)

theorem Real.shiftedReciprocalPowerSeriesTerm_eq_kernel_nat_succ
    (A c p : ℝ) (n : ℕ) :
    Real.shiftedReciprocalPowerSeriesTerm A c p n =
      Real.shiftedReciprocalPowerKernel A c p (n + 1 : ℕ) := by
  unfold Real.shiftedReciprocalPowerSeriesTerm
  have hcast : (((n + 1 : ℕ) : ℝ)) = (n : ℝ) + 1 := by
    exact Eq.trans (Nat.cast_add n 1)
      (congrArg (fun value : ℝ => (n : ℝ) + value) Nat.cast_one)
  exact congrArg (Real.shiftedReciprocalPowerKernel A c p) hcast.symm

theorem Real.sum_range_shiftedReciprocalPowerSeriesTerm_eq_Ico
    (A c p : ℝ) (N : ℕ) :
    (∑ n ∈ Finset.range N,
      Real.shiftedReciprocalPowerSeriesTerm A c p n) =
      ∑ k ∈ Finset.Ico 1 (N + 1),
        Real.shiftedReciprocalPowerKernel A c p k := by
  have hterms :
      (∑ n ∈ Finset.range N,
        Real.shiftedReciprocalPowerSeriesTerm A c p n) =
      ∑ n ∈ Finset.range N,
        Real.shiftedReciprocalPowerKernel A c p (n + 1 : ℕ) := by
    exact Finset.sum_congr rfl
      (fun n _hn =>
        Real.shiftedReciprocalPowerSeriesTerm_eq_kernel_nat_succ A c p n)
  have hrangeIco :
      (∑ n ∈ Finset.range N,
        Real.shiftedReciprocalPowerKernel A c p (n + 1 : ℕ)) =
      ∑ n ∈ Finset.Ico 0 N,
        Real.shiftedReciprocalPowerKernel A c p (n + 1 : ℕ) := by
    exact congrArg
      (fun indices : Finset ℕ => ∑ n ∈ indices,
        Real.shiftedReciprocalPowerKernel A c p (n + 1 : ℕ))
      (congrFun Nat.Ico_zero_eq_range N).symm
  have hshift :
      (∑ n ∈ Finset.Ico 0 N,
        Real.shiftedReciprocalPowerKernel A c p (n + 1 : ℕ)) =
      ∑ k ∈ Finset.Ico 1 (N + 1),
        Real.shiftedReciprocalPowerKernel A c p k := by
    exact Finset.sum_Ico_add'
      (fun k : ℕ => Real.shiftedReciprocalPowerKernel A c p k)
      0 N 1
  exact Eq.trans hterms (Eq.trans hrangeIco hshift)

theorem Real.sum_range_succ_shiftedReciprocalPowerSeriesTerm_le_first_add_integral
    (A c p : ℝ) (N : ℕ)
    (hA : 0 ≤ A) (hc : 0 < c) (hp : 0 ≤ p) :
    (∑ n ∈ Finset.range (N + 1),
      Real.shiftedReciprocalPowerSeriesTerm A c p n) ≤
      Real.shiftedReciprocalPowerKernel A c p 1 +
        ∫ x in (0 : ℝ)..(N : ℝ),
          Real.shiftedReciprocalPowerKernel A c p (x + 1) := by
  have hfinite :=
    Real.sum_shiftedReciprocalPowerKernel_le_first_add_integral
      A c p N hA hc hp
  have hidentify :=
    Real.sum_range_shiftedReciprocalPowerSeriesTerm_eq_Ico
      A c p (N + 1)
  exact le_trans (le_of_eq hidentify) hfinite

theorem Real.shiftedReciprocalPowerIntegral_eq_endpointDifference
    (A c p N : ℝ)
    (hA : 0 ≤ A) (hc : 0 < c) (hN : 0 ≤ N)
    (hp : p ≠ 1) :
    (∫ x in (0 : ℝ)..N,
      Real.shiftedReciprocalPowerKernel A c p (x + 1)) =
      (((c * N + (A + c)) ^ (1 - p) -
          (A + c) ^ (1 - p)) / (1 - p)) / c := by
  have hscaled :=
    Real.integral_shiftedReciprocalPowerKernel_eq_rpow_endpoints
      A c p N hA hc hN hp
  have hcne : c ≠ 0 := ne_of_gt hc
  have hdivide := congrArg (fun value : ℝ => value / c) hscaled
  have hcancel :
      (c * (∫ x in (0 : ℝ)..N,
        Real.shiftedReciprocalPowerKernel A c p (x + 1))) / c =
      ∫ x in (0 : ℝ)..N,
        Real.shiftedReciprocalPowerKernel A c p (x + 1) := by
    exact mul_div_cancel_left₀ _ hcne
  exact Eq.trans hcancel.symm hdivide

theorem Real.endpointDifference_le_shiftedReciprocalPowerIntegralBudget
    (A c p N : ℝ)
    (hA : 0 ≤ A) (hc : 0 < c) (hN : 0 ≤ N)
    (hp : 1 < p) :
    (((c * N + (A + c)) ^ (1 - p) -
          (A + c) ^ (1 - p)) / (1 - p)) / c ≤
      Real.shiftedReciprocalPowerIntegralBudget A c p := by
  have hbasePos : 0 < A + c := add_pos_of_nonneg_of_pos hA hc
  have htopPos : 0 < c * N + (A + c) :=
    add_pos_of_nonneg_of_pos (mul_nonneg hc.le hN) hbasePos
  have hexponentNeg : 1 - p < 0 := sub_neg.mpr hp
  have htopNonneg : 0 ≤
      (c * N + (A + c)) ^ (1 - p) :=
    Real.rpow_nonneg htopPos.le (1 - p)
  have hdrop :
      -((c * N + (A + c)) ^ (1 - p)) ≤ 0 :=
    neg_nonpos.mpr htopNonneg
  have hdenominatorPos : 0 < p - 1 := sub_pos.mpr hp
  have hcMulPos : 0 < c * (p - 1) := mul_pos hc hdenominatorPos
  have hnegNormalize : 1 - p = -(p - 1) := by
    exact (neg_sub p 1).symm
  have hnumeratorNormalize :
      (c * N + (A + c)) ^ (1 - p) - (A + c) ^ (1 - p) =
      -((A + c) ^ (1 - p) -
        (c * N + (A + c)) ^ (1 - p)) := by
    exact (neg_sub _ _).symm
  have hpositiveDifference :
      (A + c) ^ (1 - p) -
          (c * N + (A + c)) ^ (1 - p) ≤
        (A + c) ^ (1 - p) := by
    exact sub_le_self _ htopNonneg
  have hdivide := div_le_div_of_nonneg_right
    hpositiveDifference hcMulPos.le
  unfold Real.shiftedReciprocalPowerIntegralBudget
  have hleftNormalize :
      (((c * N + (A + c)) ^ (1 - p) -
          (A + c) ^ (1 - p)) / (1 - p)) / c =
        ((A + c) ^ (1 - p) -
          (c * N + (A + c)) ^ (1 - p)) /
            (c * (p - 1)) := by
    exact Eq.trans
      (congrArg (fun value : ℝ => (value / (1 - p)) / c)
        hnumeratorNormalize)
      (Eq.trans
        (congrArg (fun denominator : ℝ =>
          (-((A + c) ^ (1 - p) -
            (c * N + (A + c)) ^ (1 - p)) / denominator) / c)
          hnegNormalize)
        (Eq.trans
          (congrArg (fun quotient : ℝ => quotient / c)
            (neg_div_neg_eq
              ((A + c) ^ (1 - p) -
                (c * N + (A + c)) ^ (1 - p))
              (p - 1)))
          (Eq.trans
            (div_div
              ((A + c) ^ (1 - p) -
                (c * N + (A + c)) ^ (1 - p))
              (p - 1) c)
            (congrArg (fun denominator : ℝ =>
              ((A + c) ^ (1 - p) -
                (c * N + (A + c)) ^ (1 - p)) / denominator)
              (mul_comm (p - 1) c)))))
  exact le_trans (le_of_eq hleftNormalize) hdivide

theorem Real.shiftedReciprocalPowerSeriesBudget_nonneg
    (A c p : ℝ)
    (hA : 0 ≤ A) (hc : 0 < c) (hp : 1 < p) :
    0 ≤ Real.shiftedReciprocalPowerSeriesBudget A c p := by
  have hfirst := Real.shiftedReciprocalPowerKernel_nonneg
    A c p 1 hA hc.le zero_le_one
  unfold Real.shiftedReciprocalPowerSeriesBudget
  unfold Real.shiftedReciprocalPowerIntegralBudget
  have hbase : 0 < A + c := add_pos_of_nonneg_of_pos hA hc
  have hintegralNumerator : 0 ≤ (A + c) ^ (1 - p) :=
    Real.rpow_nonneg hbase.le (1 - p)
  have hfactor : 0 < p - 1 := sub_pos.mpr hp
  have hdenominator : 0 < c * (p - 1) := mul_pos hc hfactor
  have hintegral : 0 ≤ (A + c) ^ (1 - p) / (c * (p - 1)) :=
    div_nonneg hintegralNumerator hdenominator.le
  exact add_nonneg hfirst hintegral

theorem Real.sum_range_shiftedReciprocalPowerSeriesTerm_le_seriesBudget
    (A c p : ℝ) (N : ℕ)
    (hA : 0 ≤ A) (hc : 0 < c) (hp : 1 < p) :
    (∑ n ∈ Finset.range N,
      Real.shiftedReciprocalPowerSeriesTerm A c p n) ≤
      Real.shiftedReciprocalPowerSeriesBudget A c p := by
  match N with
  | 0 =>
      have hzero :
          (∑ n ∈ Finset.range 0,
            Real.shiftedReciprocalPowerSeriesTerm A c p n) = 0 :=
        Finset.sum_range_zero _
      have hbudget :=
        Real.shiftedReciprocalPowerSeriesBudget_nonneg A c p hA hc hp
      exact Eq.subst
        (motive := fun value : ℝ =>
          value ≤ Real.shiftedReciprocalPowerSeriesBudget A c p)
        hzero.symm hbudget
  | N + 1 =>
      have hsum :=
        Real.sum_range_succ_shiftedReciprocalPowerSeriesTerm_le_first_add_integral
          A c p N hA hc (le_trans zero_lt_one.le hp.le)
      have hintegralEq :=
        Real.shiftedReciprocalPowerIntegral_eq_endpointDifference
          A c p N hA hc (Nat.cast_nonneg N) (ne_of_gt hp)
      have hend :=
        Real.endpointDifference_le_shiftedReciprocalPowerIntegralBudget
          A c p N hA hc (Nat.cast_nonneg N) hp
      have hintegralBudget :=
        le_trans (le_of_eq hintegralEq) hend
      have hfirstIntegral := add_le_add_left hintegralBudget
        (Real.shiftedReciprocalPowerKernel A c p 1)
      unfold Real.shiftedReciprocalPowerSeriesBudget
      exact le_trans hsum hfirstIntegral

theorem Real.summable_shiftedReciprocalPowerSeriesTerm
    (A c p : ℝ)
    (hA : 0 ≤ A) (hc : 0 < c) (hp : 1 < p) :
    Summable (Real.shiftedReciprocalPowerSeriesTerm A c p) := by
  exact summable_of_sum_range_le
    (Real.shiftedReciprocalPowerSeriesTerm_nonneg A c p · hA hc.le)
    (Real.sum_range_shiftedReciprocalPowerSeriesTerm_le_seriesBudget
      A c p · hA hc hp)

theorem Real.tsum_shiftedReciprocalPowerSeriesTerm_le_seriesBudget
    (A c p : ℝ)
    (hA : 0 ≤ A) (hc : 0 < c) (hp : 1 < p) :
    (∑' n : ℕ, Real.shiftedReciprocalPowerSeriesTerm A c p n) ≤
      Real.shiftedReciprocalPowerSeriesBudget A c p := by
  exact Real.tsum_le_of_sum_range_le
    (Real.shiftedReciprocalPowerSeriesTerm_nonneg A c p · hA hc.le)
    (Real.sum_range_shiftedReciprocalPowerSeriesTerm_le_seriesBudget
      A c p · hA hc hp)

end
end LFunctions
end Boundary
