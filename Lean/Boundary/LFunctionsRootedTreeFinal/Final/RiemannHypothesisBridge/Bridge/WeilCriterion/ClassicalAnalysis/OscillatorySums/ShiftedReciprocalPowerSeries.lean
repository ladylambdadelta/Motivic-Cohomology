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
    (A c p x : ℝ) :
    0 ≤ Real.shiftedReciprocalPowerKernel A c p x := by
  unfold Real.shiftedReciprocalPowerKernel
  exact div_nonneg zero_le_one (Real.rpow_nonneg _ _)

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
  have haffine := Real.shiftedAffine_mono hc.le hxy
  have hpower := Real.rpow_le_rpow hax.le haffine hp
  exact one_div_le_one_div_of_le hax hpower

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
  have hpower := haffine.rpow_const (Or.inl (ne_of_gt hdenominator))
  exact (continuousAt_const.div hpower
    (Real.rpow_ne_zero_of_pos hdenominator p)).continuousWithinAt

theorem Real.shiftedReciprocalPowerKernel_intervalIntegrable
    (A c p left right : ℝ)
    (hA : 0 ≤ A) (hc : 0 < c) (hleft : 1 ≤ left) :
    IntervalIntegrable
      (Real.shiftedReciprocalPowerKernel A c p)
      MeasureTheory.volume left right := by
  have hcontinuous :=
    (Real.shiftedReciprocalPowerKernel_continuousOn_Ici A c p hA hc).mono
      (fun x hx => le_trans hleft hx.1)
  exact hcontinuous.intervalIntegrable

theorem Real.sum_shiftedReciprocalPowerKernel_le_integral
    (A c p : ℝ) (N : ℕ)
    (hA : 0 ≤ A) (hc : 0 < c) (hp : 0 ≤ p) :
    (∑ n ∈ Finset.Ico 1 (N + 1),
      Real.shiftedReciprocalPowerKernel A c p n) ≤
      ∫ x in (0 : ℝ)..(N : ℝ),
        Real.shiftedReciprocalPowerKernel A c p (x + 1) := by
  have hmono :=
    Real.shiftedReciprocalPowerKernel_antitoneOn_Icc
      A c p 1 (N : ℝ) hA hc hp (le_refl 1)
  exact hmono.sum_le_integral_Ico
    (Nat.cast_nonneg N)

end
end LFunctions
end Boundary
