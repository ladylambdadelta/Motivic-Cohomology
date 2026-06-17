import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaAdmissibleSpectralInterpolation.ZetaAdmissiblePaleyWiener.SupportInterval.Owner

/-!
# Paley-Wiener vertical weights

This file owns the low-level vertical-strip weight and the elementary
low/high-frequency comparison inequalities used by the Paley-Wiener decay
package. It is copy-first extracted from the current Paley-Wiener owner file
and is not imported by that parent yet, so declaration names intentionally
match the existing owner surface.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open scoped ContDiff

namespace ZetaAdmissibleFunction

/-- The Paley-Wiener vertical-strip weight used by the admissible transform estimates. -/
def zetaPaleyWienerVerticalWeight (z : ℂ) (N : ℕ) : ℝ :=
  (1 + ‖z.im‖) ^ (-(N : ℤ))

/-- The strip membership predicate used by the Paley-Wiener estimate. -/
def zetaPaleyWienerInVerticalStrip (a b : ℝ) (z : ℂ) : Prop :=
  a ≤ z.re ∧ z.re ≤ b

/-- The Paley-Wiener vertical weight is nonnegative. -/
theorem zetaPaleyWienerVerticalWeight_nonnegative (z : ℂ) (N : ℕ) :
    0 ≤ zetaPaleyWienerVerticalWeight z N := by
  unfold zetaPaleyWienerVerticalWeight
  have hbase : 0 ≤ 1 + ‖z.im‖ :=
    add_nonneg zero_le_one (norm_nonneg z.im)
  exact zpow_nonneg hbase (-(N : ℤ))

/-- Low-frequency weight comparison for one Paley-Wiener successor step. -/
theorem zetaPaleyWienerVerticalWeight_le_successor_lowFrequency
    (z : ℂ) (N : ℕ) (hz : ‖z.im‖ ≤ 1) :
    zetaPaleyWienerVerticalWeight z N ≤
      2 * zetaPaleyWienerVerticalWeight z (N + 1) := by
  let X : ℝ := 1 + ‖z.im‖
  have hX_nonzero : X ≠ 0 := by
    have hX_pos : 0 < X :=
      lt_of_lt_of_le zero_lt_one
        (le_add_of_nonneg_right (norm_nonneg z.im))
    exact ne_of_gt hX_pos
  have hX_le_two : X ≤ 2 := by
    calc
      X = 1 + ‖z.im‖ := rfl
      _ ≤ 1 + 1 := add_le_add_left hz 1
      _ = 2 := one_add_one_eq_two
  have hweight_nonneg :
      0 ≤ X ^ (-(N + 1 : ℤ)) :=
    zpow_nonneg (le_trans zero_le_one
      (le_add_of_nonneg_right (norm_nonneg z.im))) (-(N + 1 : ℤ))
  have hexp :
      (1 : ℤ) + (-(N + 1 : ℤ)) = -(N : ℤ) := by
    show (1 : ℤ) + (-(N + 1 : ℤ)) = -(N : ℤ)
    have h1 : (1 : ℤ) + (-(N + 1 : ℤ)) = 1 - N - 1 := by
      calc (1 : ℤ) + (-(N + 1 : ℤ))
          = 1 + (-(N + 1)) := rfl
        _ = 1 - (N + 1) := by exact (Int.add_neg_eq_sub 1 (N + 1)).symm
        _ = 1 - N - 1 := (Int.sub_sub 1 N 1).symm
    have h2 : (1 : ℤ) - N - 1 = -N := by
      calc (1 : ℤ) - N - 1
          = (1 - 1) - N := by exact Int.sub_sub_cancel 1 1 N
        _ = 0 - N := by exact congrArg (· - N) (Int.sub_self 1)
        _ = -N := by exact Int.zero_sub N
    exact h1.trans h2
  have hcombine :
      X * X ^ (-(N + 1 : ℤ)) = X ^ (-(N : ℤ)) := by
    calc
      X * X ^ (-(N + 1 : ℤ)) =
          X ^ (1 : ℤ) * X ^ (-(N + 1 : ℤ)) := by
        exact congrArg
          (fun y : ℝ => y * X ^ (-(N + 1 : ℤ)))
          (zpow_one X).symm
      _ = X ^ ((1 : ℤ) + (-(N + 1 : ℤ))) := by
        exact (zpow_add₀ hX_nonzero (1 : ℤ) (-(N + 1 : ℤ))).symm
      _ = X ^ (-(N : ℤ)) := by
        exact congrArg (fun e : ℤ => X ^ e) hexp
  have hscaled :
      X * X ^ (-(N + 1 : ℤ)) ≤
        2 * X ^ (-(N + 1 : ℤ)) :=
    mul_le_mul_of_nonneg_right hX_le_two hweight_nonneg
  unfold zetaPaleyWienerVerticalWeight
  change X ^ (-(N : ℤ)) ≤ 2 * X ^ (-(N + 1 : ℤ))
  exact Eq.subst
    (motive := fun y : ℝ => y ≤ 2 * X ^ (-(N + 1 : ℤ)))
    hcombine
    hscaled

/-- Base high-frequency inverse estimate for the vertical variable. -/
theorem zetaPaleyWiener_inverseIm_times_verticalBase_le_two_highFrequency
    (z : ℂ) (hz : 1 ≤ ‖z.im‖) :
    ‖(z.im : ℂ)⁻¹‖ * (1 + ‖z.im‖) ≤ 2 := by
  let r : ℝ := ‖z.im‖
  have hr_pos : 0 < r :=
    lt_of_lt_of_le zero_lt_one hz
  have hr_ne_zero : r ≠ 0 :=
    ne_of_gt hr_pos
  have hr_inv_nonneg : 0 ≤ r⁻¹ :=
    inv_nonneg.mpr (le_of_lt hr_pos)
  have hnorm_inv :
      ‖(z.im : ℂ)⁻¹‖ = r⁻¹ := by
    calc
      ‖(z.im : ℂ)⁻¹‖ = ‖(z.im : ℂ)‖⁻¹ := by
        exact norm_inv (z.im : ℂ)
      _ = r⁻¹ := by
        exact congrArg Inv.inv (RCLike.norm_ofReal z.im)
  have hinv_le_one : r⁻¹ ≤ 1 := by
    have hscaled :
        r⁻¹ * 1 ≤ r⁻¹ * r :=
      mul_le_mul_of_nonneg_left hz hr_inv_nonneg
    have hleft : r⁻¹ * 1 = r⁻¹ :=
      mul_one r⁻¹
    have hright : r⁻¹ * r = 1 :=
      inv_mul_cancel₀ hr_ne_zero
    exact Eq.subst
      (motive := fun x : ℝ => x ≤ 1)
      hleft
      (Eq.subst
        (motive := fun x : ℝ => r⁻¹ * 1 ≤ x)
        hright
        hscaled)
  have hbase :
      r⁻¹ * (1 + r) ≤ 2 := by
    have hdistrib :
        r⁻¹ * (1 + r) = r⁻¹ + 1 := by
      calc
        r⁻¹ * (1 + r) = r⁻¹ * 1 + r⁻¹ * r := by
          exact mul_add r⁻¹ 1 r
        _ = r⁻¹ + r⁻¹ * r := by
          exact congrArg (fun x : ℝ => x + r⁻¹ * r) (mul_one r⁻¹)
        _ = r⁻¹ + 1 := by
          exact congrArg (fun x : ℝ => r⁻¹ + x) (inv_mul_cancel₀ hr_ne_zero)
    have hsum :
        r⁻¹ + 1 ≤ 2 := by
      calc
        r⁻¹ + 1 ≤ 1 + 1 := by
          exact add_le_add_right hinv_le_one 1
        _ = 2 := one_add_one_eq_two
    exact Eq.subst
      (motive := fun x : ℝ => x ≤ 2)
      hdistrib.symm
      hsum
  exact Eq.subst
    (motive := fun x : ℝ => x * (1 + ‖z.im‖) ≤ 2)
    hnorm_inv.symm
    hbase

/-- High-frequency inverse weight comparison for one Paley-Wiener successor step. -/
theorem zetaPaleyWiener_inverseIm_mul_weight_le_successor_highFrequency
    (z : ℂ) (N : ℕ) (hz : 1 ≤ ‖z.im‖) :
    ‖(z.im : ℂ)⁻¹‖ * zetaPaleyWienerVerticalWeight z N ≤
      2 * zetaPaleyWienerVerticalWeight z (N + 1) := by
  let X : ℝ := 1 + ‖z.im‖
  have hX_nonzero : X ≠ 0 := by
    have hX_pos : 0 < X :=
      lt_of_lt_of_le zero_lt_one
        (le_add_of_nonneg_right (norm_nonneg z.im))
    exact ne_of_gt hX_pos
  have hweight_nonneg :
      0 ≤ X ^ (-(N + 1 : ℤ)) :=
    zpow_nonneg (le_trans zero_le_one
      (le_add_of_nonneg_right (norm_nonneg z.im))) (-(N + 1 : ℤ))
  have hexp :
      (1 : ℤ) + (-(N + 1 : ℤ)) = -(N : ℤ) := by
    show (1 : ℤ) + (-(N + 1 : ℤ)) = -(N : ℤ)
    have h1 : (1 : ℤ) + (-(N + 1 : ℤ)) = 1 - N - 1 := by
      calc (1 : ℤ) + (-(N + 1 : ℤ))
          = 1 + (-(N + 1)) := rfl
        _ = 1 - (N + 1) := by exact (Int.add_neg_eq_sub 1 (N + 1)).symm
        _ = 1 - N - 1 := (Int.sub_sub 1 N 1).symm
    have h2 : (1 : ℤ) - N - 1 = -N := by
      calc (1 : ℤ) - N - 1
          = (1 - 1) - N := by exact Int.sub_sub_cancel 1 1 N
        _ = 0 - N := by exact congrArg (· - N) (Int.sub_self 1)
        _ = -N := by exact Int.zero_sub N
    exact h1.trans h2
  have hcombine :
      X * X ^ (-(N + 1 : ℤ)) = X ^ (-(N : ℤ)) := by
    calc
      X * X ^ (-(N + 1 : ℤ)) =
          X ^ (1 : ℤ) * X ^ (-(N + 1 : ℤ)) := by
        exact congrArg
          (fun y : ℝ => y * X ^ (-(N + 1 : ℤ)))
          (zpow_one X).symm
      _ = X ^ ((1 : ℤ) + (-(N + 1 : ℤ))) := by
        exact (zpow_add₀ hX_nonzero (1 : ℤ) (-(N + 1 : ℤ))).symm
      _ = X ^ (-(N : ℤ)) := by
        exact congrArg (fun e : ℤ => X ^ e) hexp
  have hbase :
      ‖(z.im : ℂ)⁻¹‖ * X ≤ 2 :=
    zetaPaleyWiener_inverseIm_times_verticalBase_le_two_highFrequency z hz
  have hscaled :
      (‖(z.im : ℂ)⁻¹‖ * X) * X ^ (-(N + 1 : ℤ)) ≤
        2 * X ^ (-(N + 1 : ℤ)) :=
    mul_le_mul_of_nonneg_right hbase hweight_nonneg
  have hrearrange :
      ‖(z.im : ℂ)⁻¹‖ * X ^ (-(N : ℤ)) =
        (‖(z.im : ℂ)⁻¹‖ * X) * X ^ (-(N + 1 : ℤ)) := by
    calc
      ‖(z.im : ℂ)⁻¹‖ * X ^ (-(N : ℤ)) =
          ‖(z.im : ℂ)⁻¹‖ * (X * X ^ (-(N + 1 : ℤ))) := by
        exact congrArg (fun y : ℝ => ‖(z.im : ℂ)⁻¹‖ * y) hcombine.symm
      _ = (‖(z.im : ℂ)⁻¹‖ * X) * X ^ (-(N + 1 : ℤ)) := by
        exact (mul_assoc ‖(z.im : ℂ)⁻¹‖ X
          (X ^ (-(N + 1 : ℤ)))).symm
  unfold zetaPaleyWienerVerticalWeight
  change ‖(z.im : ℂ)⁻¹‖ * X ^ (-(N : ℤ)) ≤
    2 * X ^ (-(N + 1 : ℤ))
  exact Eq.subst
    (motive := fun y : ℝ => y ≤ 2 * X ^ (-(N + 1 : ℤ)))
    hrearrange
    hscaled

end ZetaAdmissibleFunction

end
end LFunctions
end Boundary
