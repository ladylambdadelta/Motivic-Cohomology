import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ClassicalAnalysis.GammaBinetStirling.BinetAbelPlanaSemicircleStaircaseSafeBounds

/-!
# Variation bounds for right semicircle staircases

This file owns the finite adjacent-difference telescope and unimodal
variation estimates used by the right semicircle staircase geometry.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open scoped Topology Interval
open Filter MeasureTheory


/-- Adjacent absolute differences telescope on a monotone finite prefix. -/
theorem sum_abs_adjacent_of_monotone_prefix
    (s : ℕ → ℝ)
    (j : ℕ)
    (hmono : ∀ k : ℕ, k < j → s k ≤ s (k + 1)) :
    (∑ k in Finset.range j, |s (k + 1) - s k|) = s j - s 0 := by
  induction j with
  | zero =>
      calc
        (∑ k in Finset.range 0, |s (k + 1) - s k|) = 0 :=
          Finset.sum_range_zero (fun k : ℕ => |s (k + 1) - s k|)
        _ = s 0 - s 0 := Eq.symm (sub_self (s 0))
  | succ j ih =>
      have hmono_prefix : ∀ k : ℕ, k < j → s k ≤ s (k + 1) := by
        intro k hk
        exact hmono k (Nat.lt_trans hk (Nat.lt_succ_self j))
      have hlast_nonneg : 0 ≤ s (j + 1) - s j :=
        sub_nonneg.mpr (hmono j (Nat.lt_succ_self j))
      calc
        (∑ k in Finset.range (j + 1), |s (k + 1) - s k|)
            =
          (∑ k in Finset.range j, |s (k + 1) - s k|) +
            |s (j + 1) - s j| :=
          Finset.sum_range_succ
            (fun k : ℕ => |s (k + 1) - s k|) j
        _ = (s j - s 0) + (s (j + 1) - s j) := by
          exact congrArg₂ (fun x y : ℝ => x + y) (ih hmono_prefix)
            (abs_of_nonneg hlast_nonneg)
        _ = s (j + 1) - s 0 :=
          Real.forward_difference_telescope_step (s 0) (s j) (s (j + 1))

/-- Adjacent absolute differences telescope on an antitone finite suffix. -/
theorem sum_abs_adjacent_of_antitone_suffix
    (s : ℕ → ℝ)
    (j n : ℕ)
    (hanti :
      ∀ k : ℕ, k < n → s ((j + k) + 1) ≤ s (j + k)) :
    (∑ k in Finset.range n, |s ((j + k) + 1) - s (j + k)|) =
      s j - s (j + n) := by
  induction n with
  | zero =>
      calc
        (∑ k in Finset.range 0, |s ((j + k) + 1) - s (j + k)|) = 0 :=
          Finset.sum_range_zero
            (fun k : ℕ => |s ((j + k) + 1) - s (j + k)|)
        _ = s j - s (j + 0) := by
          exact Eq.symm (sub_self (s j))
  | succ n ih =>
      have hanti_prefix :
          ∀ k : ℕ, k < n → s ((j + k) + 1) ≤ s (j + k) := by
        intro k hk
        exact hanti k (Nat.lt_trans hk (Nat.lt_succ_self n))
      have hlast_nonneg : 0 ≤ s (j + n) - s ((j + n) + 1) :=
        sub_nonneg.mpr (hanti n (Nat.lt_succ_self n))
      have hlast_abs :
          |s ((j + n) + 1) - s (j + n)| =
            s (j + n) - s ((j + n) + 1) := by
        calc
          |s ((j + n) + 1) - s (j + n)| =
              |-(s (j + n) - s ((j + n) + 1))| := by
            exact congrArg abs
              (Eq.symm (neg_sub (s (j + n)) (s ((j + n) + 1))))
          _ = |s (j + n) - s ((j + n) + 1)| :=
            abs_neg (s (j + n) - s ((j + n) + 1))
          _ = s (j + n) - s ((j + n) + 1) :=
            abs_of_nonneg hlast_nonneg
      calc
        (∑ k in Finset.range (n + 1), |s ((j + k) + 1) - s (j + k)|)
            =
          (∑ k in Finset.range n, |s ((j + k) + 1) - s (j + k)|) +
            |s ((j + n) + 1) - s (j + n)| :=
          Finset.sum_range_succ
            (fun k : ℕ => |s ((j + k) + 1) - s (j + k)|) n
        _ = (s j - s (j + n)) + (s (j + n) - s ((j + n) + 1)) := by
          exact congrArg₂ (fun x y : ℝ => x + y) (ih hanti_prefix)
            hlast_abs
        _ = s j - s ((j + n) + 1) :=
          Real.backward_difference_telescope_step
            (s j) (s (j + n)) (s ((j + n) + 1))

/-- Split an adjacent-difference sum at a chosen index. -/
theorem sum_abs_adjacent_split_at
    (s : ℕ → ℝ)
    {m j : ℕ}
    (hjm : j ≤ m) :
    (∑ k in Finset.range m, |s (k + 1) - s k|) =
      (∑ k in Finset.range j, |s (k + 1) - s k|) +
        ∑ k in Finset.range (m - j),
          |s ((j + k) + 1) - s (j + k)| := by
  have hm_decomp : j + (m - j) = m :=
    Nat.add_sub_of_le hjm
  calc
    (∑ k in Finset.range m, |s (k + 1) - s k|)
        =
      ∑ k in Finset.range (j + (m - j)), |s (k + 1) - s k| := by
      exact congrArg
        (fun n : ℕ => ∑ k in Finset.range n, |s (k + 1) - s k|)
        (Eq.symm hm_decomp)
    _ =
      (∑ k in Finset.range j, |s (k + 1) - s k|) +
        ∑ k in Finset.range (m - j),
          |s ((j + k) + 1) - s (j + k)| :=
      Finset.sum_range_add
        (fun k : ℕ => |s (k + 1) - s k|) j (m - j)

/-- The zero-index predecessor expression is the first jump from zero. -/
theorem abs_sub_prev_zero_eq_abs_first
    (s : ℕ → ℝ) :
    |s 0 - if 0 = 0 then (0 : ℝ) else s (0 - 1)| = |s 0| := by
  have hif : (if 0 = 0 then (0 : ℝ) else s (0 - 1)) = 0 :=
    if_pos rfl
  calc
    |s 0 - if 0 = 0 then (0 : ℝ) else s (0 - 1)| =
        |s 0 - 0| :=
      congrArg (fun x : ℝ => |s 0 - x|) hif
    _ = |s 0| :=
      congrArg abs (sub_zero (s 0))

/-- If the sequence starts at zero, the zero-index predecessor expression
vanishes. -/
theorem abs_sub_prev_zero_eq_zero_of_start_zero
    (s : ℕ → ℝ)
    (h0 : s 0 = 0) :
    |s 0 - if 0 = 0 then (0 : ℝ) else s (0 - 1)| = 0 := by
  calc
    |s 0 - if 0 = 0 then (0 : ℝ) else s (0 - 1)| = |s 0| :=
      abs_sub_prev_zero_eq_abs_first s
    _ = |0| :=
      congrArg abs h0
    _ = 0 :=
      abs_zero

/-- At a successor index, the predecessor expression is the adjacent
difference. -/
theorem abs_sub_prev_succ_eq_abs_adjacent
    (s : ℕ → ℝ)
    (k : ℕ) :
    |s (k + 1) - if k + 1 = 0 then (0 : ℝ) else s ((k + 1) - 1)| =
      |s (k + 1) - s k| := by
  have hif :
      (if k + 1 = 0 then (0 : ℝ) else s ((k + 1) - 1)) = s k := by
    calc
      (if k + 1 = 0 then (0 : ℝ) else s ((k + 1) - 1)) =
          s ((k + 1) - 1) :=
        if_neg (Nat.succ_ne_zero k)
      _ = s k :=
        congrArg s (Nat.succ_sub_one k)
  exact congrArg (fun x : ℝ => |s (k + 1) - x|) hif

/-- The successor tail of the predecessor-expression variation is the
ordinary adjacent-difference variation. -/
theorem sum_range_abs_sub_prev_succ_eq_sum_abs_adjacent
    (s : ℕ → ℝ)
    (m : ℕ) :
    (∑ k in Finset.range m,
      |s (k + 1) - if k + 1 = 0 then (0 : ℝ) else s ((k + 1) - 1)|) =
      ∑ k in Finset.range m, |s (k + 1) - s k| :=
  Finset.sum_congr rfl
    (fun k _hk => abs_sub_prev_succ_eq_abs_adjacent s k)

/-- Pulling off the initial zero rewrites the `prev`-style variation as the
ordinary adjacent-difference variation. -/
theorem sum_abs_sub_prev_eq_sum_abs_adjacent
    (s : ℕ → ℝ)
    (m : ℕ)
    (h0 : s 0 = 0) :
    (∑ k in Finset.range (m + 1),
      |s k - if k = 0 then (0 : ℝ) else s (k - 1)|) =
      ∑ k in Finset.range m, |s (k + 1) - s k| := by
  calc
    (∑ k in Finset.range (m + 1),
      |s k - if k = 0 then (0 : ℝ) else s (k - 1)|) =
        |s 0 - if 0 = 0 then (0 : ℝ) else s (0 - 1)| +
          ∑ k in Finset.range m,
            |s (k + 1) -
              if k + 1 = 0 then (0 : ℝ) else s ((k + 1) - 1)| :=
      calc
        (∑ k in Finset.range (m + 1),
          |s k - if k = 0 then (0 : ℝ) else s (k - 1)|) =
            (∑ k in Finset.range m,
                |s (k + 1) -
                  if k + 1 = 0 then (0 : ℝ) else s ((k + 1) - 1)|) +
              |s 0 - if 0 = 0 then (0 : ℝ) else s (0 - 1)| :=
          Finset.sum_range_succ'
            (fun k : ℕ => |s k - if k = 0 then (0 : ℝ) else s (k - 1)|) m
        _ =
            |s 0 - if 0 = 0 then (0 : ℝ) else s (0 - 1)| +
              ∑ k in Finset.range m,
                |s (k + 1) -
                  if k + 1 = 0 then (0 : ℝ) else s ((k + 1) - 1)| :=
          add_comm
            (∑ k in Finset.range m,
              |s (k + 1) -
                if k + 1 = 0 then (0 : ℝ) else s ((k + 1) - 1)|)
            |s 0 - if 0 = 0 then (0 : ℝ) else s (0 - 1)|
    _ =
        0 +
          ∑ k in Finset.range m,
            |s (k + 1) -
              if k + 1 = 0 then (0 : ℝ) else s ((k + 1) - 1)| := by
      exact congrArg
        (fun x : ℝ =>
          x +
            ∑ k in Finset.range m,
              |s (k + 1) -
                if k + 1 = 0 then (0 : ℝ) else s ((k + 1) - 1)|)
        (abs_sub_prev_zero_eq_zero_of_start_zero s h0)
    _ =
        ∑ k in Finset.range m,
          |s (k + 1) -
            if k + 1 = 0 then (0 : ℝ) else s ((k + 1) - 1)| :=
      zero_add _
    _ =
        ∑ k in Finset.range m, |s (k + 1) - s k| :=
      sum_range_abs_sub_prev_succ_eq_sum_abs_adjacent s m

/-- The `prev`-style variation is the first jump from zero together with the
ordinary adjacent-difference variation. -/
theorem sum_abs_sub_prev_eq_abs_first_add_sum_abs_adjacent
    (s : ℕ → ℝ)
    (m : ℕ) :
    (∑ k in Finset.range (m + 1),
      |s k - if k = 0 then (0 : ℝ) else s (k - 1)|) =
      |s 0| + ∑ k in Finset.range m, |s (k + 1) - s k| := by
  calc
    (∑ k in Finset.range (m + 1),
      |s k - if k = 0 then (0 : ℝ) else s (k - 1)|) =
        |s 0 - if 0 = 0 then (0 : ℝ) else s (0 - 1)| +
          ∑ k in Finset.range m,
            |s (k + 1) -
              if k + 1 = 0 then (0 : ℝ) else s ((k + 1) - 1)| :=
      calc
        (∑ k in Finset.range (m + 1),
          |s k - if k = 0 then (0 : ℝ) else s (k - 1)|) =
            (∑ k in Finset.range m,
                |s (k + 1) -
                  if k + 1 = 0 then (0 : ℝ) else s ((k + 1) - 1)|) +
              |s 0 - if 0 = 0 then (0 : ℝ) else s (0 - 1)| :=
          Finset.sum_range_succ'
            (fun k : ℕ => |s k - if k = 0 then (0 : ℝ) else s (k - 1)|) m
        _ =
            |s 0 - if 0 = 0 then (0 : ℝ) else s (0 - 1)| +
              ∑ k in Finset.range m,
                |s (k + 1) -
                  if k + 1 = 0 then (0 : ℝ) else s ((k + 1) - 1)| :=
          add_comm
            (∑ k in Finset.range m,
              |s (k + 1) -
                if k + 1 = 0 then (0 : ℝ) else s ((k + 1) - 1)|)
            |s 0 - if 0 = 0 then (0 : ℝ) else s (0 - 1)|
    _ =
        |s 0| +
          ∑ k in Finset.range m,
            |s (k + 1) -
              if k + 1 = 0 then (0 : ℝ) else s ((k + 1) - 1)| := by
      exact congrArg
        (fun x : ℝ =>
          x +
            ∑ k in Finset.range m,
              |s (k + 1) -
                if k + 1 = 0 then (0 : ℝ) else s ((k + 1) - 1)|)
        (abs_sub_prev_zero_eq_abs_first s)
    _ =
        |s 0| + ∑ k in Finset.range m, |s (k + 1) - s k| := by
      exact congrArg
        (fun x : ℝ => |s 0| + x)
        (sum_range_abs_sub_prev_succ_eq_sum_abs_adjacent s m)

/-- Scalar algebra behind the unimodal variation estimate when the sequence
starts at zero. -/
theorem unimodal_variation_zero_start_scalar_le
    {ρ s0 sj sm : ℝ}
    (hs0 : s0 = 0)
    (hsj : sj ≤ ρ) :
    ((sj - s0) + (sj - sm)) + sm ≤ 2 * ρ := by
  calc
    ((sj - s0) + (sj - sm)) + sm = 2 * sj :=
      Real.unimodal_zero_start_scalar_collapse hs0
    _ ≤ 2 * ρ := by
      exact mul_le_mul_of_nonneg_left hsj
        Real.rightSemicircleStaircase_two_nonneg

/-- Scalar algebra behind the bounded unimodal variation estimate. -/
theorem unimodal_variation_bounded_scalar_le
    {ρ s0 sj sm : ℝ}
    (hsj : sj ≤ ρ) :
    s0 + ((sj - s0) + (sj - sm)) + sm ≤ 2 * ρ := by
  calc
    s0 + ((sj - s0) + (sj - sm)) + sm = 2 * sj :=
      Real.unimodal_bounded_scalar_collapse s0 sj sm
    _ ≤ 2 * ρ := by
      exact mul_le_mul_of_nonneg_left hsj
        Real.rightSemicircleStaircase_two_nonneg

/-- A finite real sequence starting at zero, staying in `[0,ρ]`, increasing up
to a peak index and decreasing after it has total horizontal variation,
including the return from the final value to zero, bounded by `2ρ`. -/
theorem sum_abs_sub_prev_add_top_le_two_mul_of_unimodal
    {ρ : ℝ}
    (s : ℕ → ℝ)
    (m j : ℕ)
    (hjm : j ≤ m)
    (h0 : s 0 = 0)
    (hbounds : ∀ k : ℕ, k ≤ m → 0 ≤ s k ∧ s k ≤ ρ)
    (hmono : ∀ k : ℕ, k < j → s k ≤ s (k + 1))
    (hanti : ∀ k : ℕ, j ≤ k → k < m → s (k + 1) ≤ s k) :
    (∑ k in Finset.range (m + 1),
        |s k - if k = 0 then (0 : ℝ) else s (k - 1)|) +
      |(0 : ℝ) - s m| ≤ 2 * ρ := by
  have hprev :
      (∑ k in Finset.range (m + 1),
        |s k - if k = 0 then (0 : ℝ) else s (k - 1)|) =
        ∑ k in Finset.range m, |s (k + 1) - s k| :=
    sum_abs_sub_prev_eq_sum_abs_adjacent s m h0
  have hm_decomp : j + (m - j) = m :=
    Nat.add_sub_of_le hjm
  have hsplit :
      (∑ k in Finset.range m, |s (k + 1) - s k|) =
        (∑ k in Finset.range j, |s (k + 1) - s k|) +
          ∑ k in Finset.range (m - j),
            |s ((j + k) + 1) - s (j + k)| :=
    sum_abs_adjacent_split_at s hjm
  have hprefix :
      (∑ k in Finset.range j, |s (k + 1) - s k|) = s j - s 0 :=
    sum_abs_adjacent_of_monotone_prefix s j hmono
  have hsuffix :
      (∑ k in Finset.range (m - j),
        |s ((j + k) + 1) - s (j + k)|) = s j - s m := by
    have hanti_shift :
        ∀ k : ℕ, k < m - j → s ((j + k) + 1) ≤ s (j + k) := by
      intro k hk
      exact hanti (j + k) (Nat.le_add_right j k)
        (Nat.lt_sub_iff_add_lt'.mp hk)
    have htel :=
      sum_abs_adjacent_of_antitone_suffix s j (m - j) hanti_shift
    have hendpoint : s (j + (m - j)) = s m :=
      congrArg s hm_decomp
    calc
      (∑ k in Finset.range (m - j),
        |s ((j + k) + 1) - s (j + k)|) = s j - s (j + (m - j)) :=
        htel
      _ = s j - s m :=
        congrArg (fun x : ℝ => s j - x) hendpoint
  have htop : |(0 : ℝ) - s m| = s m := by
    have hsm_nonneg : 0 ≤ s m := (hbounds m le_rfl).1
    calc
      |(0 : ℝ) - s m| = |-s m| := congrArg abs (zero_sub (s m))
      _ = |s m| := abs_neg (s m)
      _ = s m := abs_of_nonneg hsm_nonneg
  have hsj_le : s j ≤ ρ := (hbounds j hjm).2
  calc
    (∑ k in Finset.range (m + 1),
        |s k - if k = 0 then (0 : ℝ) else s (k - 1)|) +
      |(0 : ℝ) - s m|
        =
      ((s j - s 0) + (s j - s m)) + s m := by
        calc
          (∑ k in Finset.range (m + 1),
              |s k - if k = 0 then (0 : ℝ) else s (k - 1)|) +
            |(0 : ℝ) - s m|
              =
            (∑ k in Finset.range m, |s (k + 1) - s k|) +
              |(0 : ℝ) - s m| := by
            exact congrArg (fun x : ℝ => x + |(0 : ℝ) - s m|) hprev
          _ =
            ((∑ k in Finset.range j, |s (k + 1) - s k|) +
                ∑ k in Finset.range (m - j),
                  |s ((j + k) + 1) - s (j + k)|) +
              |(0 : ℝ) - s m| := by
            exact congrArg (fun x : ℝ => x + |(0 : ℝ) - s m|) hsplit
          _ = ((s j - s 0) +
                ∑ k in Finset.range (m - j),
                  |s ((j + k) + 1) - s (j + k)|) +
              |(0 : ℝ) - s m| := by
            exact congrArg
              (fun x : ℝ =>
                (x +
                  ∑ k in Finset.range (m - j),
                    |s ((j + k) + 1) - s (j + k)|) +
                  |(0 : ℝ) - s m|)
              hprefix
          _ = ((s j - s 0) + (s j - s m)) + |(0 : ℝ) - s m| := by
            exact congrArg
              (fun x : ℝ => ((s j - s 0) + x) + |(0 : ℝ) - s m|)
              hsuffix
          _ = ((s j - s 0) + (s j - s m)) + s m := by
            exact congrArg
              (fun x : ℝ => ((s j - s 0) + (s j - s m)) + x)
              htop
    _ ≤ 2 * ρ :=
        unimodal_variation_zero_start_scalar_le h0 hsj_le

/-- A finite real sequence staying in `[0,ρ]`, increasing up to a peak index
and decreasing after it has total horizontal variation from the left endpoint
`0` through the sequence and back to `0` bounded by `2ρ`. -/
theorem sum_abs_sub_prev_add_top_le_two_mul_of_bounded_unimodal
    {ρ : ℝ}
    (s : ℕ → ℝ)
    (m j : ℕ)
    (hjm : j ≤ m)
    (hbounds : ∀ k : ℕ, k ≤ m → 0 ≤ s k ∧ s k ≤ ρ)
    (hmono : ∀ k : ℕ, k < j → s k ≤ s (k + 1))
    (hanti : ∀ k : ℕ, j ≤ k → k < m → s (k + 1) ≤ s k) :
    (∑ k in Finset.range (m + 1),
        |s k - if k = 0 then (0 : ℝ) else s (k - 1)|) +
      |(0 : ℝ) - s m| ≤ 2 * ρ := by
  have hprev :
      (∑ k in Finset.range (m + 1),
        |s k - if k = 0 then (0 : ℝ) else s (k - 1)|) =
        |s 0| + ∑ k in Finset.range m, |s (k + 1) - s k| :=
    sum_abs_sub_prev_eq_abs_first_add_sum_abs_adjacent s m
  have hm_decomp : j + (m - j) = m :=
    Nat.add_sub_of_le hjm
  have hsplit :
      (∑ k in Finset.range m, |s (k + 1) - s k|) =
        (∑ k in Finset.range j, |s (k + 1) - s k|) +
          ∑ k in Finset.range (m - j),
            |s ((j + k) + 1) - s (j + k)| :=
    sum_abs_adjacent_split_at s hjm
  have hprefix :
      (∑ k in Finset.range j, |s (k + 1) - s k|) = s j - s 0 :=
    sum_abs_adjacent_of_monotone_prefix s j hmono
  have hsuffix :
      (∑ k in Finset.range (m - j),
        |s ((j + k) + 1) - s (j + k)|) = s j - s m := by
    have hanti_shift :
        ∀ k : ℕ, k < m - j → s ((j + k) + 1) ≤ s (j + k) := by
      intro k hk
      exact hanti (j + k) (Nat.le_add_right j k)
        (Nat.lt_sub_iff_add_lt'.mp hk)
    have htel :=
      sum_abs_adjacent_of_antitone_suffix s j (m - j) hanti_shift
    have hendpoint : s (j + (m - j)) = s m :=
      congrArg s hm_decomp
    calc
      (∑ k in Finset.range (m - j),
        |s ((j + k) + 1) - s (j + k)|) = s j - s (j + (m - j)) :=
        htel
      _ = s j - s m :=
        congrArg (fun x : ℝ => s j - x) hendpoint
  have hfirst : |s 0| = s 0 := by
    exact abs_of_nonneg ((hbounds 0 (Nat.zero_le m)).1)
  have htop : |(0 : ℝ) - s m| = s m := by
    have hsm_nonneg : 0 ≤ s m := (hbounds m le_rfl).1
    calc
      |(0 : ℝ) - s m| = |-s m| := congrArg abs (zero_sub (s m))
      _ = |s m| := abs_neg (s m)
      _ = s m := abs_of_nonneg hsm_nonneg
  have hsj_le : s j ≤ ρ := (hbounds j hjm).2
  calc
    (∑ k in Finset.range (m + 1),
        |s k - if k = 0 then (0 : ℝ) else s (k - 1)|) +
      |(0 : ℝ) - s m|
        =
      s 0 + ((s j - s 0) + (s j - s m)) + s m := by
        calc
          (∑ k in Finset.range (m + 1),
              |s k - if k = 0 then (0 : ℝ) else s (k - 1)|) +
            |(0 : ℝ) - s m|
              =
            (|s 0| + ∑ k in Finset.range m, |s (k + 1) - s k|) +
              |(0 : ℝ) - s m| := by
            exact congrArg (fun x : ℝ => x + |(0 : ℝ) - s m|) hprev
          _ =
            (|s 0| +
              ((∑ k in Finset.range j, |s (k + 1) - s k|) +
                ∑ k in Finset.range (m - j),
                  |s ((j + k) + 1) - s (j + k)|)) +
              |(0 : ℝ) - s m| := by
            exact congrArg
              (fun x : ℝ => (|s 0| + x) + |(0 : ℝ) - s m|)
              hsplit
          _ =
            (s 0 +
              ((∑ k in Finset.range j, |s (k + 1) - s k|) +
                ∑ k in Finset.range (m - j),
                  |s ((j + k) + 1) - s (j + k)|)) +
              |(0 : ℝ) - s m| := by
            exact congrArg
              (fun x : ℝ =>
                (x +
                  ((∑ k in Finset.range j, |s (k + 1) - s k|) +
                    ∑ k in Finset.range (m - j),
                      |s ((j + k) + 1) - s (j + k)|)) +
                  |(0 : ℝ) - s m|)
              hfirst
          _ =
            (s 0 +
              ((s j - s 0) +
                ∑ k in Finset.range (m - j),
                  |s ((j + k) + 1) - s (j + k)|)) +
              |(0 : ℝ) - s m| := by
            exact congrArg
              (fun x : ℝ =>
                (s 0 +
                  (x +
                    ∑ k in Finset.range (m - j),
                      |s ((j + k) + 1) - s (j + k)|)) +
                  |(0 : ℝ) - s m|)
              hprefix
          _ =
            (s 0 + ((s j - s 0) + (s j - s m))) +
              |(0 : ℝ) - s m| := by
            exact congrArg
              (fun x : ℝ =>
                (s 0 + ((s j - s 0) + x)) + |(0 : ℝ) - s m|)
              hsuffix
          _ = (s 0 + ((s j - s 0) + (s j - s m))) + s m := by
            exact congrArg
              (fun x : ℝ => (s 0 + ((s j - s 0) + (s j - s m))) + x)
              htop
    _ ≤ 2 * ρ :=
        unimodal_variation_bounded_scalar_le hsj_le

/-- If the safe staircase real coordinates are unimodal, then their full
horizontal variation from the lower tangent point back to the upper tangent
point is bounded by `2ρ`. -/
theorem Complex.rightSemicircleStaircaseSafeRe_totalHorizontalVariation_le_two_radius_of_unimodal
    {ρ : ℝ}
    (hρ : 0 ≤ ρ)
    (m j : ℕ)
    (hjm : j ≤ m)
    (hmono :
      ∀ k : ℕ, k < j →
        Complex.rightSemicircleStaircaseSafeRe ρ m k ≤
          Complex.rightSemicircleStaircaseSafeRe ρ m (k + 1))
    (hanti :
      ∀ k : ℕ, j ≤ k → k < m →
        Complex.rightSemicircleStaircaseSafeRe ρ m (k + 1) ≤
      Complex.rightSemicircleStaircaseSafeRe ρ m k) :
    (∑ k in Finset.range (m + 1),
        |Complex.rightSemicircleStaircaseSafeRe ρ m k -
          Complex.rightSemicircleStaircasePrevSafeRe ρ m k|) +
      |(0 : ℝ) - Complex.rightSemicircleStaircaseSafeRe ρ m m| ≤ 2 * ρ := by
  let s : ℕ → ℝ := fun k =>
    Complex.rightSemicircleStaircaseSafeRe ρ m k
  have hbounds : ∀ k : ℕ, k ≤ m → 0 ≤ s k ∧ s k ≤ ρ := by
    intro k hk
    have hcell : k ∈ Finset.range (m + 1) := by
      exact Finset.mem_range.mpr (Nat.lt_succ_iff.mpr hk)
    have hleft :
        0 ≤ Complex.rightSemicircleStaircaseSafeRe ρ m k :=
      Complex.rightSemicircleStaircaseSafeRe_nonneg hρ m k
    have hright :
        Complex.rightSemicircleStaircaseSafeRe ρ m k ≤ ρ :=
      Complex.rightSemicircleStaircaseSafeRe_le_radius hρ hcell
    exact And.intro hleft hright
  have hgeneric :
      (∑ k in Finset.range (m + 1),
          |s k - if k = 0 then (0 : ℝ) else s (k - 1)|) +
        |(0 : ℝ) - s m| ≤ 2 * ρ :=
    sum_abs_sub_prev_add_top_le_two_mul_of_bounded_unimodal
      s m j hjm hbounds
      (by
        intro k hk
        exact hmono k hk)
      (by
        intro k hjk hkm
        exact hanti k hjk hkm)
  change
    (∑ k in Finset.range (m + 1),
        |s k - if k = 0 then (0 : ℝ) else s (k - 1)|) +
      |(0 : ℝ) - s m| ≤ 2 * ρ
  exact hgeneric

end

end LFunctions
end Boundary
