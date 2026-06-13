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

/-- Centered completed-zeta zeros lie in the centered critical strip.

This is the standard unconditional critical-strip theorem for nontrivial zeta
zeros, expressed in the centered completed-zeta normalization used by the
zero-side explicit formula. -/
theorem centeredCompletedRiemannZeta_zero_re_mem_centeredCriticalStrip
    (s : ℂ)
    (hs : centeredCompletedRiemannZeta s = 0) :
    -(1 / 2 : ℝ) ≤ s.re ∧ s.re ≤ (1 / 2 : ℝ) := by
  sorry

end
end LFunctions
end Boundary
