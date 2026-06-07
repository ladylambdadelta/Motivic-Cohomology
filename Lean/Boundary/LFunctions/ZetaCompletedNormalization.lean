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
  unfold centeredCompletedRiemannZeta centeredCompletedRiemannZeta₀
  rw [completedRiemannZeta_eq]

theorem centeredCompletedRiemannZeta_neg (s : ℂ) :
    centeredCompletedRiemannZeta (-s) = centeredCompletedRiemannZeta s := by
  unfold centeredCompletedRiemannZeta
  rw [← completedRiemannZeta_one_sub]
  congr
  rw [sub_eq_add_neg]
  rw [neg_add, neg_neg]
  rw [← add_assoc]
  rw [show (1 : ℂ) + -(1 / 2) = (1 / 2 : ℂ) by
    rw [← sub_eq_add_neg, sub_half]]

theorem centeredCompletedRiemannZeta₀_neg (s : ℂ) :
    centeredCompletedRiemannZeta₀ (-s) = centeredCompletedRiemannZeta₀ s := by
  unfold centeredCompletedRiemannZeta₀
  rw [← completedRiemannZeta₀_one_sub]
  congr
  rw [sub_eq_add_neg]
  rw [neg_add, neg_neg]
  rw [← add_assoc]
  rw [show (1 : ℂ) + -(1 / 2) = (1 / 2 : ℂ) by
    rw [← sub_eq_add_neg, sub_half]]

theorem centeredCompletedRiemannZeta_correction_symm (s : ℂ) :
    1 / (1 / 2 + (-s)) + 1 / (1 - (1 / 2 + (-s))) =
      1 / (1 / 2 + s) + 1 / (1 - (1 / 2 + s)) := by
  have h1 : (1 / 2 : ℂ) + (-s) = (1 / 2 : ℂ) - s := rfl
  have h2 : (1 : ℂ) - ((1 / 2 : ℂ) - s) = (1 / 2 : ℂ) + s := by
    rw [sub_eq_add_neg, sub_eq_add_neg, neg_add, neg_neg]
    rw [← add_assoc]
    rw [show (1 : ℂ) + -(1 / 2) = (1 / 2 : ℂ) by
      rw [← sub_eq_add_neg, sub_half]]
  have h3 : (1 : ℂ) - ((1 / 2 : ℂ) + s) = (1 / 2 : ℂ) - s := by
    rw [sub_eq_add_neg, neg_add]
    rw [← add_assoc]
    rw [show (1 : ℂ) + -(1 / 2) = (1 / 2 : ℂ) by
      rw [← sub_eq_add_neg, sub_half]]
    rfl
  rw [h1, h2, h3]
  ac_rfl

end
end LFunctions
end Boundary
