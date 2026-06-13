import Mathlib.NumberTheory.LSeries.RiemannZeta

/-!
# Boundary centered completed zeta normalization

This file fixes the centered completed-zeta object at the critical line and
records the direct decomposition available from mathlib:
the entire part plus the two pole correction terms.
-/

namespace Boundary
namespace LFunctions

noncomputable section

/-- The completed zeta function centered at the critical line. -/
def centeredCompletedRiemannZeta (s : ℂ) : ℂ :=
  completedRiemannZeta (1 / 2 + s)

/-- The entire part of the centered completed zeta function. -/
def centeredCompletedRiemannZeta₀ (s : ℂ) : ℂ :=
  completedRiemannZeta₀ (1 / 2 + s)

theorem centeredCompletedRiemannZeta_eq (s : ℂ) :
    centeredCompletedRiemannZeta s =
      centeredCompletedRiemannZeta₀ s -
        1 / (1 / 2 + s) - 1 / (1 - (1 / 2 + s)) := by
  exact completedRiemannZeta_eq (1 / 2 + s)

theorem centeredCompletedRiemannZeta_neg (s : ℂ) :
    centeredCompletedRiemannZeta (-s) = centeredCompletedRiemannZeta s := by
  have hsub : (1 : ℂ) - (1 / 2 + s) = 1 / 2 - s := by
    ring
  have hsymm :
      completedRiemannZeta (1 / 2 - s) = completedRiemannZeta (1 - (1 / 2 + s)) := by
    exact congrArg completedRiemannZeta hsub.symm
  exact hsymm.trans (completedRiemannZeta_one_sub (1 / 2 + s))

theorem centeredCompletedRiemannZeta₀_neg (s : ℂ) :
    centeredCompletedRiemannZeta₀ (-s) = centeredCompletedRiemannZeta₀ s := by
  have hsub : (1 : ℂ) - (1 / 2 + s) = 1 / 2 - s := by
    ring
  have hsymm :
      completedRiemannZeta₀ (1 / 2 - s) = completedRiemannZeta₀ (1 - (1 / 2 + s)) := by
    exact congrArg completedRiemannZeta₀ hsub.symm
  exact hsymm.trans (completedRiemannZeta₀_one_sub (1 / 2 + s))

theorem centeredCompletedRiemannZeta_correction_symm (s : ℂ) :
    1 / (1 / 2 + (-s)) + 1 / (1 - (1 / 2 + (-s))) =
      1 / (1 / 2 + s) + 1 / (1 - (1 / 2 + s)) := by
  have h1 : (1 / 2 : ℂ) + (-s) = (1 / 2 : ℂ) - s := by
    exact sub_eq_add_neg (1 / 2) s
  have h2 : (1 : ℂ) - ((1 / 2 : ℂ) - s) = (1 / 2 : ℂ) + s := by
    ring
  have h3 : (1 : ℂ) - (1 / 2 + s) = (1 / 2 : ℂ) - s := by
    ring
  calc
    1 / (1 / 2 + (-s)) + 1 / (1 - (1 / 2 + (-s))) =
        1 / ((1 / 2 : ℂ) - s) + 1 / (1 - ((1 / 2 : ℂ) - s)) := by
      exact congrArg (fun x : ℂ => 1 / x + 1 / (1 - x)) h1
    _ = 1 / ((1 / 2 : ℂ) - s) + 1 / (1 / 2 + s) := by
      exact congrArg (fun x : ℂ => 1 / ((1 / 2 : ℂ) - s) + x)
        (congrArg (fun x : ℂ => 1 / x) h2)
    _ = 1 / (1 / 2 + s) + 1 / ((1 / 2 : ℂ) - s) := by
      exact add_comm (1 / ((1 / 2 : ℂ) - s)) (1 / (1 / 2 + s))
    _ = 1 / (1 / 2 + s) + 1 / (1 - (1 / 2 + s)) := by
      exact congrArg (fun x : ℂ => 1 / (1 / 2 + s) + x)
        (congrArg (fun x : ℂ => 1 / x) h3.symm)

/-- Completed zeta has no zeros in the left half-plane. -/
theorem completedRiemannZeta_ne_zero_of_re_lt_zero
    (s : ℂ)
    (hsre : s.re < 0) :
    completedRiemannZeta s ≠ 0 := by
  sorry

/-- Completed zeta has no zeros in the half-plane to the right of `1`. -/
theorem completedRiemannZeta_ne_zero_of_one_lt_re
    (s : ℂ)
    (hsre : 1 < s.re) :
    completedRiemannZeta s ≠ 0 := by
  sorry

/-- Completed-zeta zeros lie in the ordinary critical strip.

This is the standard unconditional critical-strip theorem for zeros of the
completed Riemann zeta normalization. -/
theorem completedRiemannZeta_zero_re_mem_criticalStrip
    (s : ℂ)
    (hs : completedRiemannZeta s = 0) :
    0 ≤ s.re ∧ s.re ≤ (1 : ℝ) := by
  have hnot_left : ¬ s.re < 0 := by
    intro hsre
    exact completedRiemannZeta_ne_zero_of_re_lt_zero s hsre hs
  have hnot_right : ¬ (1 : ℝ) < s.re := by
    intro hsre
    exact completedRiemannZeta_ne_zero_of_one_lt_re s hsre hs
  exact ⟨le_of_not_gt hnot_left, le_of_not_gt hnot_right⟩

/-- The real coordinate of the uncentered argument is the centered real
coordinate shifted by `1/2`. -/
theorem centeredCompletedRiemannZeta_uncenter_re
    (s : ℂ) :
    ((1 / 2 : ℂ) + s).re = (1 / 2 : ℝ) + s.re := by
  calc
    ((1 / 2 : ℂ) + s).re = (1 / 2 : ℂ).re + s.re := by
      exact Complex.add_re (1 / 2 : ℂ) s
    _ = (1 / 2 : ℝ) + s.re := by
      exact congrArg (fun x : ℝ => x + s.re) Complex.ofReal_re

/-- If the uncentered coordinate lies in `[0,1]`, the centered coordinate lies
in `[-1/2,1/2]`. -/
theorem centered_re_mem_centeredCriticalStrip_of_uncentered_re_mem_criticalStrip
    {x : ℝ}
    (hleft : 0 ≤ (1 / 2 : ℝ) + x)
    (hright : (1 / 2 : ℝ) + x ≤ 1) :
    -(1 / 2 : ℝ) ≤ x ∧ x ≤ (1 / 2 : ℝ) := by
  have hleft' :
      -(1 / 2 : ℝ) ≤ x :=
    (neg_le_iff_add_nonneg).2 hleft
  have hright_comm :
      x + (1 / 2 : ℝ) ≤ 1 :=
    Eq.subst
      (motive := fun y : ℝ => y ≤ 1)
      (add_comm (1 / 2 : ℝ) x)
      hright
  have hright_sub :
      x ≤ (1 : ℝ) - (1 / 2 : ℝ) :=
    (le_sub_iff_add_le).2 hright_comm
  have hhalf :
      (1 : ℝ) - (1 / 2 : ℝ) = (1 / 2 : ℝ) :=
    sub_half (1 : ℝ)
  have hright' :
      x ≤ (1 / 2 : ℝ) :=
    Eq.subst
      (motive := fun y : ℝ => x ≤ y)
      hhalf
      hright_sub
  exact ⟨hleft', hright'⟩

/-- Centered completed-zeta zeros lie in the centered critical strip.

This is the standard unconditional critical-strip theorem for nontrivial zeta
zeros, expressed in the centered completed-zeta normalization used by the
zero-side explicit formula. -/
theorem centeredCompletedRiemannZeta_zero_re_mem_centeredCriticalStrip
    (s : ℂ)
    (hs : centeredCompletedRiemannZeta s = 0) :
    -(1 / 2 : ℝ) ≤ s.re ∧ s.re ≤ (1 / 2 : ℝ) := by
  have huncentered_zero :
      completedRiemannZeta ((1 / 2 : ℂ) + s) = 0 := by
    exact hs
  have hstrip :
      0 ≤ ((1 / 2 : ℂ) + s).re ∧
        ((1 / 2 : ℂ) + s).re ≤ (1 : ℝ) :=
    completedRiemannZeta_zero_re_mem_criticalStrip
      ((1 / 2 : ℂ) + s)
      huncentered_zero
  have hre :
      ((1 / 2 : ℂ) + s).re = (1 / 2 : ℝ) + s.re :=
    centeredCompletedRiemannZeta_uncenter_re s
  have hleft :
      0 ≤ (1 / 2 : ℝ) + s.re :=
    Eq.subst
      (motive := fun x : ℝ => 0 ≤ x)
      hre
      hstrip.1
  have hright :
      (1 / 2 : ℝ) + s.re ≤ 1 :=
    Eq.subst
      (motive := fun x : ℝ => x ≤ (1 : ℝ))
      hre
      hstrip.2
  exact centered_re_mem_centeredCriticalStrip_of_uncentered_re_mem_criticalStrip
    hleft
    hright

end
end LFunctions
end Boundary
