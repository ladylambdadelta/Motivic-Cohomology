import Mathlib.Analysis.SumIntegralComparisons
import Mathlib.Analysis.PSeries

/-!
# Shifted reciprocal-power series

This owner supplies the monotone kernel and finite sum–integral comparison for
series of `(A + c n)^{-p}` with nonnegative shift and positive scale.
-/

namespace Boundary
namespace LFunctions

noncomputable section

def Real.shiftedReciprocalPowerKernel
    (A c p : ℝ) (x : ℝ) : ℝ :=
  1 / (A + c * x) ^ p

theorem Real.shiftedReciprocalPowerKernel_nonneg
    (A c p x : ℝ) (hA : 0 ≤ A) (hc : 0 ≤ c) (hx : 0 ≤ x) :
    0 ≤ Real.shiftedReciprocalPowerKernel A c p x := by
  unfold Real.shiftedReciprocalPowerKernel
  have hbase : 0 ≤ A + c * x :=
    add_nonneg hA (mul_nonneg hc hx)
  exact div_nonneg zero_le_one (Real.rpow_nonneg hbase _)

theorem Real.shiftedAffine_mono
    {A c x y : ℝ}
    (hc : 0 ≤ c) (hxy : x ≤ y) :
    A + c * x ≤ A + c * y := by
  exact add_le_add_left (mul_le_mul_of_nonneg_left hxy hc) A

theorem Real.shiftedAffine_pos
    {A c x : ℝ}
    (hA : 0 ≤ A) (hc : 0 < c) (hx : 0 < x) :
    0 < A + c * x := by
  exact add_pos_of_nonneg_of_pos hA (mul_pos hc hx)

theorem Real.shiftedReciprocalPowerKernel_antitoneOn
    (A c p : ℝ)
    (hA : 0 ≤ A) (hc : 0 < c) (hp : 0 ≤ p) :
    AntitoneOn (Real.shiftedReciprocalPowerKernel A c p) (Set.Ici 1) := by
  intro x hx y hy hxy
  unfold Real.shiftedReciprocalPowerKernel
  have hxPos : 0 < x := lt_of_lt_of_le zero_lt_one hx
  have hyPos : 0 < y := lt_of_lt_of_le zero_lt_one hy
  have hax := Real.shiftedAffine_pos hA hc hxPos
  have hay := Real.shiftedAffine_pos hA hc hyPos
  have haffine := Real.shiftedAffine_mono (A := A) hc.le hxy
  have hpower := Real.rpow_le_rpow hax.le haffine hp
  have hpower_pos : 0 < (A + c * x) ^ p :=
    Real.rpow_pos_of_pos hax p
  exact one_div_le_one_div_of_le hpower_pos hpower

theorem Real.shiftedReciprocalPowerKernel_antitoneOn_Icc
    (A c p left right : ℝ)
    (hA : 0 ≤ A) (hc : 0 < c) (hp : 0 ≤ p)
    (hleft : 1 ≤ left) :
    AntitoneOn (Real.shiftedReciprocalPowerKernel A c p)
      (Set.Icc left right) := by
  have hsubset : Set.Icc left right ⊆ Set.Ici 1 :=
    fun x hx => le_trans hleft hx.1
  exact (Real.shiftedReciprocalPowerKernel_antitoneOn A c p hA hc hp).mono hsubset

theorem Real.shiftedReciprocalPowerKernel_continuousOn_Ici
    (A c p : ℝ)
    (hA : 0 ≤ A) (hc : 0 < c) :
    ContinuousOn (Real.shiftedReciprocalPowerKernel A c p) (Set.Ici 1) := by
  intro x hx
  have hxPos : 0 < x := lt_of_lt_of_le zero_lt_one hx
  have hdenominator := Real.shiftedAffine_pos hA hc hxPos
  unfold Real.shiftedReciprocalPowerKernel
  have haffine : ContinuousAt (fun y : ℝ => A + c * y) x :=
    continuousAt_const.add (continuousAt_const.mul continuousAt_id)
  have hpower := haffine.rpow_const (p := p)
    (Or.inl (ne_of_gt hdenominator))
  have hpower_ne : (A + c * x) ^ p ≠ 0 :=
    ne_of_gt (Real.rpow_pos_of_pos hdenominator p)
  exact (continuousAt_const.div hpower hpower_ne).continuousWithinAt

theorem Real.shiftedReciprocalPowerKernel_intervalIntegrable
    (A c p left right : ℝ)
    (hA : 0 ≤ A) (hc : 0 < c) (hleft : 1 ≤ left)
    (hleft_right : left ≤ right) :
    IntervalIntegrable
      (Real.shiftedReciprocalPowerKernel A c p)
      MeasureTheory.volume left right := by
  have hcontinuous :
      ContinuousOn (Real.shiftedReciprocalPowerKernel A c p)
        (Set.Icc left right) :=
    (Real.shiftedReciprocalPowerKernel_continuousOn_Ici A c p hA hc).mono
      (fun x hx => le_trans hleft hx.1)
  have hcontinuous_uIcc :
      ContinuousOn (Real.shiftedReciprocalPowerKernel A c p) (Set.uIcc left right) :=
    by
      intro x hx
      have hxIcc : x ∈ Set.Icc left right :=
        (Set.uIcc_of_le hleft_right).symm ▸ hx
      exact Eq.subst
        (motive := fun s : Set ℝ => ContinuousWithinAt
          (Real.shiftedReciprocalPowerKernel A c p) s x)
        (Set.uIcc_of_le hleft_right).symm
        (hcontinuous x hxIcc)
  exact hcontinuous_uIcc.intervalIntegrable

theorem Real.sum_shiftedReciprocalPowerKernel_le_first_add_integral
    (A c p : ℝ) (N : ℕ)
    (hA : 0 ≤ A) (hc : 0 < c) (hp : 0 ≤ p) :
    (∑ n ∈ Finset.Ico 1 (N + 2),
      Real.shiftedReciprocalPowerKernel A c p n) ≤
      Real.shiftedReciprocalPowerKernel A c p 1 +
        ∫ x in (0 : ℝ)..(N : ℝ),
          Real.shiftedReciprocalPowerKernel A c p (x + 1) := by
  have hmono_base :=
    Real.shiftedReciprocalPowerKernel_antitoneOn A c p hA hc hp
  have hmono_shifted :
      AntitoneOn
        (fun x : ℝ => Real.shiftedReciprocalPowerKernel A c p (x + 1))
        (Set.Icc ((0 : ℕ) : ℝ) (N : ℝ)) := by
    intro x hx y hy hxy
    have hx_one : (1 : ℝ) ≤ x + 1 := by
      exact le_trans (Eq.le (zero_add (1 : ℝ)).symm)
        (Eq.subst (motive := fun z : ℝ => z + 1 ≤ x + 1)
          (Nat.cast_zero : ((0 : ℕ) : ℝ) = 0)
          (add_le_add_right hx.1 1))
    have hy_one : (1 : ℝ) ≤ y + 1 := by
      exact le_trans (Eq.le (zero_add (1 : ℝ)).symm)
        (Eq.subst (motive := fun z : ℝ => z + 1 ≤ y + 1)
          (Nat.cast_zero : ((0 : ℕ) : ℝ) = 0)
          (add_le_add_right hy.1 1))
    have hxy_one : x + 1 ≤ y + 1 :=
      add_le_add_right hxy 1
    exact hmono_base hx_one hy_one hxy_one
  have htailRaw := hmono_shifted.sum_le_integral_Ico
    (Nat.zero_le N)
  have htailTerms :
      (∑ n ∈ Finset.Ico 0 N,
        Real.shiftedReciprocalPowerKernel A c p
          (((n + 1 : ℕ) : ℝ) + 1)) =
      ∑ n ∈ Finset.Ico 0 N,
        Real.shiftedReciprocalPowerKernel A c p (n + 2 : ℕ) := by
    exact Finset.sum_congr rfl
      (fun n _hn =>
        congrArg (Real.shiftedReciprocalPowerKernel A c p)
          (Eq.trans
            (congrArg (fun value : ℝ => ((n + 1 : ℕ) : ℝ) + value)
              (Nat.cast_one.symm))
            (Eq.trans
              (Nat.cast_add (n + 1) 1).symm
              (congrArg (fun value : ℕ => (value : ℝ))
                (show (n + 1) + 1 = n + 2 from rfl)))))
  have htailShift :
      (∑ n ∈ Finset.Ico 0 N,
        Real.shiftedReciprocalPowerKernel A c p (n + 2 : ℕ)) =
      ∑ n ∈ Finset.Ico 2 (N + 2),
        Real.shiftedReciprocalPowerKernel A c p n := by
    exact Finset.sum_Ico_add'
      (fun n : ℕ => Real.shiftedReciprocalPowerKernel A c p n)
      0 N 2
  have htail :
      (∑ n ∈ Finset.Ico 2 (N + 2),
        Real.shiftedReciprocalPowerKernel A c p n) ≤
      ∫ x in (0 : ℝ)..(N : ℝ),
        Real.shiftedReciprocalPowerKernel A c p (x + 1) := by
    have htailOrder := le_of_eq (Eq.trans htailTerms htailShift).symm
    have htailRawNormalized :
        (∑ n ∈ Finset.Ico 0 N,
          Real.shiftedReciprocalPowerKernel A c p
            (((n + 1 : ℕ) : ℝ) + 1)) ≤
        ∫ x in (0 : ℝ)..(N : ℝ),
          Real.shiftedReciprocalPowerKernel A c p (x + 1) := by
      exact Eq.subst
        (motive := fun lower : ℝ =>
          (∑ n ∈ Finset.Ico 0 N,
            Real.shiftedReciprocalPowerKernel A c p
              (((n + 1 : ℕ) : ℝ) + 1)) ≤
          ∫ x in lower..(N : ℝ),
            Real.shiftedReciprocalPowerKernel A c p (x + 1))
        (Nat.cast_zero) htailRaw
    exact le_trans htailOrder htailRawNormalized
  have hfirstTail := add_le_add_left htail
    (Real.shiftedReciprocalPowerKernel A c p 1)
  have honeLt : 1 < N + 2 :=
    Nat.succ_lt_succ (Nat.zero_lt_succ N)
  have hsumDecompose := Finset.sum_eq_sum_Ico_succ_bot honeLt
    (fun n : ℕ => Real.shiftedReciprocalPowerKernel A c p n)
  have hsumDecomposeNormalized :
      (∑ n ∈ Finset.Ico 1 (N + 2),
        Real.shiftedReciprocalPowerKernel A c p n) =
      Real.shiftedReciprocalPowerKernel A c p 1 +
        ∑ n ∈ Finset.Ico 2 (N + 2),
          Real.shiftedReciprocalPowerKernel A c p n := by
    exact Eq.trans hsumDecompose
      (congrArg₂ (fun first tail : ℝ => first + tail)
        (congrArg (Real.shiftedReciprocalPowerKernel A c p) Nat.cast_one)
        (congrArg
          (fun lower : ℕ => ∑ n ∈ Finset.Ico lower (N + 2),
            Real.shiftedReciprocalPowerKernel A c p n)
          (show 1 + 1 = 2 from rfl)))
  exact Eq.subst
    (motive := fun value : ℝ => value ≤
      Real.shiftedReciprocalPowerKernel A c p 1 +
        ∫ x in (0 : ℝ)..(N : ℝ),
          Real.shiftedReciprocalPowerKernel A c p (x + 1))
    hsumDecomposeNormalized.symm hfirstTail

end
end LFunctions
end Boundary
