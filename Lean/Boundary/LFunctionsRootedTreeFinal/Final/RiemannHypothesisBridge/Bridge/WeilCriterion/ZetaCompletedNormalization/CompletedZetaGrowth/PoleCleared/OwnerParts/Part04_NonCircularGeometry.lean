import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalization.CompletedZetaGrowth.PoleCleared.OwnerParts.Part08_RightCriticalGrowth

/-!
# Pole-cleared zeta noncircular zero-one strip leaf
-/

namespace Boundary
namespace LFunctions

noncomputable section

open scoped Filter Topology
local notation "π" => Real.pi

/-! ### The noncircular zero-one strip leaf -/

/-- The direct Euler--Maclaurin estimate is an ordinary finite-order envelope
on the positive half of the zero-one strip. -/
theorem poleClearedRiemannZeta_positiveHalfStrip_verticalTail_finiteOrder :
    ∃ A : ℝ, ∃ B : ℝ, ∃ m : ℕ,
      0 < A ∧
      0 < B ∧
      ∀ z : ℂ,
        (1 / 2 : ℝ) ≤ z.re →
        z.re ≤ 1 →
        1 ≤ ‖z.im‖ →
        ‖poleClearedRiemannZeta z‖ ≤
          A * Real.exp (B * (1 + ‖z‖) ^ m) := by
  let A : ℝ := (((3 : ℝ) + 2) + 1 + 2)
  have hA_pos : 0 < A := by
    exact add_pos (add_pos (add_pos zero_lt_three zero_lt_two) zero_lt_one) zero_lt_two
  exact
    ⟨A, 1, 2, hA_pos, zero_lt_one,
      fun z hz_half hz_one hz_tail =>
        let H : ℝ := 1 + ‖z‖
        have hraw :
            ‖poleClearedRiemannZeta z‖ ≤ A * H ^ (2 : ℕ) :=
          poleClearedRiemannZeta_norm_le_componentBudget_mul_height_sq_positiveHalfStrip
            z hz_half hz_one hz_tail
        have hpow_nonneg : 0 ≤ H ^ (2 : ℕ) :=
          pow_nonneg (le_trans zero_le_one (le_add_of_nonneg_right (norm_nonneg z))) 2
        have hpow_le_exp : H ^ (2 : ℕ) ≤ Real.exp (H ^ (2 : ℕ)) :=
          Real.self_le_exp_of_nonneg hpow_nonneg
        have hone_mul : (1 : ℝ) * H ^ (2 : ℕ) = H ^ (2 : ℕ) :=
          one_mul (H ^ (2 : ℕ))
        have hexp_eq :
            Real.exp (H ^ (2 : ℕ)) =
              Real.exp ((1 : ℝ) * H ^ (2 : ℕ)) :=
          congrArg Real.exp hone_mul.symm
        have henlarge :
            A * H ^ (2 : ℕ) ≤
              A * Real.exp ((1 : ℝ) * H ^ (2 : ℕ)) :=
          mul_le_mul_of_nonneg_left
            (le_trans hpow_le_exp (le_of_eq hexp_eq))
            (le_of_lt hA_pos)
        le_trans hraw henlarge⟩

/-- Reflection across the center of the critical strip acts on the real
coordinate by subtraction from one. -/
private theorem oneSubComplex_real_coordinate (z : ℂ) :
    ((1 : ℂ) - z).re = 1 - z.re := by
  exact Eq.trans (Complex.sub_re (1 : ℂ) z)
    (congrArg (fun value : ℝ => value - z.re) Complex.one_re)

/-- A point in the left half reflects into the positive half. -/
private theorem oneSubComplex_positiveHalf_real_lower
    (z : ℂ)
    (hz_half : z.re ≤ (1 / 2 : ℝ)) :
    (1 / 2 : ℝ) ≤ ((1 : ℂ) - z).re := by
  have hsum : (1 / 2 : ℝ) + z.re ≤ 1 :=
    le_trans (add_le_add_left hz_half (1 / 2 : ℝ))
      (le_of_eq (add_halves (1 : ℝ)))
  have hsub : (1 / 2 : ℝ) ≤ 1 - z.re :=
    (le_sub_iff_add_le).mpr hsum
  exact Eq.subst
    (motive := fun value : ℝ => (1 / 2 : ℝ) ≤ value)
    (oneSubComplex_real_coordinate z).symm
    hsub

/-- A nonnegative real coordinate reflects to a real coordinate at most one. -/
private theorem oneSubComplex_positiveHalf_real_upper
    (z : ℂ)
    (hz_zero : 0 ≤ z.re) :
    ((1 : ℂ) - z).re ≤ 1 := by
  have hsub : 1 - z.re ≤ 1 :=
    sub_le_self 1 hz_zero
  exact Eq.subst
    (motive := fun value : ℝ => value ≤ 1)
    (oneSubComplex_real_coordinate z).symm
    hsub

/-- Reflection preserves the norm of the imaginary coordinate. -/
private theorem oneSubComplex_imaginary_norm (z : ℂ) :
    ‖((1 : ℂ) - z).im‖ = ‖z.im‖ := by
  have him_subtraction : ((1 : ℂ) - z).im = (1 : ℂ).im - z.im :=
    Complex.sub_im (1 : ℂ) z
  have him_one : (1 : ℂ).im - z.im = 0 - z.im :=
    congrArg (fun value : ℝ => value - z.im) Complex.one_im
  have him_zero : 0 - z.im = -z.im := zero_sub z.im
  have him : ((1 : ℂ) - z).im = -z.im :=
    Eq.trans him_subtraction (Eq.trans him_one him_zero)
  exact Eq.trans (congrArg norm him) (norm_neg z.im)

/-- Reflection has norm at most the standard height base. -/
private theorem oneSubComplex_norm_le_height (z : ℂ) :
    ‖(1 : ℂ) - z‖ ≤ 1 + ‖z‖ := by
  have htriangle : ‖(1 : ℂ) - z‖ ≤ ‖(1 : ℂ)‖ + ‖z‖ :=
    norm_sub_le (1 : ℂ) z
  have hone_norm : ‖(1 : ℂ)‖ + ‖z‖ = 1 + ‖z‖ :=
    congrArg (fun value : ℝ => value + ‖z‖) norm_one
  exact Eq.subst
    (motive := fun value : ℝ => ‖(1 : ℂ) - z‖ ≤ value)
    hone_norm
    htriangle

/-- The reflected standard height base is at most twice the original base. -/
private theorem oneSubComplex_height_le_two_mul_height (z : ℂ) :
    1 + ‖(1 : ℂ) - z‖ ≤ 2 * (1 + ‖z‖) := by
  have hreflected : 1 + ‖(1 : ℂ) - z‖ ≤ 1 + (1 + ‖z‖) :=
    add_le_add_left (oneSubComplex_norm_le_height z) 1
  have hfirst_regroup : 1 + (1 + ‖z‖) = 2 + ‖z‖ :=
    Eq.trans (add_assoc 1 1 ‖z‖).symm
      (congrArg (fun value : ℝ => value + ‖z‖) one_add_one_eq_two)
  have hnorm_scale : 2 + ‖z‖ ≤ 2 + 2 * ‖z‖ :=
    add_le_add_left
      (le_mul_of_one_le_left (norm_nonneg z) poleCleared_one_le_two) 2
  have hsecond_regroup : 2 + 2 * ‖z‖ = 2 * (1 + ‖z‖) :=
    Eq.trans
      (congrArg (fun value : ℝ => value + 2 * ‖z‖) (mul_one 2).symm)
      (mul_add 2 1 ‖z‖).symm
  have hreflected_regrouped : 1 + ‖(1 : ℂ) - z‖ ≤ 2 + ‖z‖ :=
    Eq.subst
      (motive := fun value : ℝ => 1 + ‖(1 : ℂ) - z‖ ≤ value)
      hfirst_regroup
      hreflected
  have hscaled : 1 + ‖(1 : ℂ) - z‖ ≤ 2 + 2 * ‖z‖ :=
    le_trans hreflected_regrouped hnorm_scale
  exact Eq.subst
    (motive := fun value : ℝ => 1 + ‖(1 : ℂ) - z‖ ≤ value)
    hsecond_regroup
    hscaled

/-- Reflection sends the left half of the zero-one strip into its positive
half and changes the height base by at most a factor of two. -/
theorem poleClearedRiemannZeta_leftHalf_reflectedValue_verticalTail_finiteOrder :
    ∃ A : ℝ, ∃ B : ℝ, ∃ m : ℕ,
      0 < A ∧
      0 < B ∧
      ∀ z : ℂ,
        0 ≤ z.re →
        z.re ≤ (1 / 2 : ℝ) →
        1 ≤ ‖z.im‖ →
        ‖poleClearedRiemannZeta ((1 : ℂ) - z)‖ ≤
          A * Real.exp (B * (1 + ‖z‖) ^ m) := by
  match poleClearedRiemannZeta_positiveHalfStrip_verticalTail_finiteOrder with
  | ⟨A, B, m, hA_pos, hB_pos, hbound⟩ =>
      exact
        ⟨A, B * (2 : ℝ) ^ m, m, hA_pos,
          mul_pos hB_pos (pow_pos zero_lt_two m),
          fun z hz_zero hz_half hz_tail =>
            let w : ℂ := (1 : ℂ) - z
            let H : ℝ := 1 + ‖z‖
            have hw_half : (1 / 2 : ℝ) ≤ w.re :=
              oneSubComplex_positiveHalf_real_lower z hz_half
            have hw_one : w.re ≤ 1 :=
              oneSubComplex_positiveHalf_real_upper z hz_zero
            have hw_tail : 1 ≤ ‖w.im‖ :=
              Eq.subst
                (motive := fun value : ℝ => 1 ≤ value)
                (oneSubComplex_imaginary_norm z).symm
                hz_tail
            have hbase_nonneg : 0 ≤ 1 + ‖w‖ :=
              le_trans zero_le_one (le_add_of_nonneg_right (norm_nonneg w))
            have hbase_le : 1 + ‖w‖ ≤ 2 * H := by
              exact oneSubComplex_height_le_two_mul_height z
            have hpow_le : (1 + ‖w‖) ^ m ≤ (2 * H) ^ m :=
              pow_le_pow_left₀ hbase_nonneg hbase_le m
            have hpow_target :
                (1 + ‖w‖) ^ m ≤ (2 : ℝ) ^ m * H ^ m :=
              Eq.subst
                (motive := fun x : ℝ => (1 + ‖w‖) ^ m ≤ x)
                (mul_pow 2 H m)
                hpow_le
            have harg :
                B * (1 + ‖w‖) ^ m ≤ (B * (2 : ℝ) ^ m) * H ^ m := by
              exact le_trans
                (mul_le_mul_of_nonneg_left hpow_target (le_of_lt hB_pos))
                (le_of_eq (mul_assoc B ((2 : ℝ) ^ m) (H ^ m)).symm)
            have hraw :
                ‖poleClearedRiemannZeta w‖ ≤
                  A * Real.exp (B * (1 + ‖w‖) ^ m) :=
              hbound w hw_half hw_one hw_tail
            have hexp :
                Real.exp (B * (1 + ‖w‖) ^ m) ≤
                  Real.exp ((B * (2 : ℝ) ^ m) * H ^ m) :=
              Real.exp_le_exp.mpr harg
            le_trans hraw
              (mul_le_mul_of_nonneg_left hexp (le_of_lt hA_pos))⟩
end
end LFunctions
end Boundary
