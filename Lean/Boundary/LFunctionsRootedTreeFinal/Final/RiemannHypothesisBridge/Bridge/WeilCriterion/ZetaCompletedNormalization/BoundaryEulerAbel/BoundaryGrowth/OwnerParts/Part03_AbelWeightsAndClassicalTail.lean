import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalization.BoundaryEulerAbel.BoundaryGrowth.OwnerParts.Part02_LogPhasePostCutoff

/-!
# Boundary growth owner part 3

This file is a mechanical forward-order split of `BoundaryGrowth.Owner`.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open scoped Filter Topology
local notation "π" => Real.pi

/-- Nonnegativity of the Abel coefficient weight `|t| / (n - 1)` on the
post-cutoff right-endpoint range. -/
theorem boundaryLineOnePointRealParam_phaseDrift_coefficientWeight_nonneg
    (t : ℝ)
    (n : ℕ) :
    0 ≤ ‖t‖ / ((((n - 1 : ℕ) : ℕ) : ℝ)) := by
  exact div_nonneg (norm_nonneg t) (Nat.cast_nonneg (n - 1))

/-- Antitonicity of the Abel coefficient weight `|t| / (n - 1)` after the
canonical cutoff. -/
theorem boundaryLineOnePointRealParam_phaseDrift_coefficientWeight_antitone
    (t : ℝ)
    {k l : ℕ}
    (hk : ⌊2 + ‖t‖⌋₊ < k)
    (hkl : k ≤ l) :
    ‖t‖ / ((((l - 1 : ℕ) : ℕ) : ℝ)) ≤
      ‖t‖ / ((((k - 1 : ℕ) : ℕ) : ℝ)) := by
  have hcutoff_pos : 0 < ⌊2 + ‖t‖⌋₊ :=
    boundaryLineOnePointRealParam_cutoff_pos t
  have hone_le_cutoff : 1 ≤ ⌊2 + ‖t‖⌋₊ :=
    Nat.succ_le_of_lt hcutoff_pos
  have hone_lt_k : 1 < k :=
    lt_of_le_of_lt hone_le_cutoff hk
  have hk_pred_pos_nat : 0 < k - 1 :=
    Nat.sub_pos_of_lt hone_lt_k
  have hk_pred_pos : 0 < (((k - 1 : ℕ) : ℝ)) :=
    Nat.cast_pos.mpr hk_pred_pos_nat
  have hpred_le : k - 1 ≤ l - 1 :=
    Nat.sub_le_sub_right hkl 1
  have hpred_le_real :
      (((k - 1 : ℕ) : ℝ)) ≤ (((l - 1 : ℕ) : ℝ)) :=
    Nat.cast_le.mpr hpred_le
  exact
    div_le_div_of_nonneg_left
      (norm_nonneg t)
      hk_pred_pos
      hpred_le_real

/-- Finite variation of the Abel coefficient weight `|t| / (n - 1)` on the
post-cutoff right-endpoint range is at most one. -/
theorem boundaryLineOnePointRealParam_phaseDrift_coefficientWeight_variation_le_one
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    {M : ℕ}
    (hM : ⌊2 + ‖t‖⌋₊ ≤ M) :
    (‖t‖ / ((((M + 1 - 1 : ℕ) : ℕ) : ℝ))) +
        ∑ k ∈ Finset.Ioc ⌊2 + ‖t‖⌋₊ M,
          (‖t‖ / ((((k - 1 : ℕ) : ℕ) : ℝ)) -
            ‖t‖ / (((((k + 1) - 1 : ℕ) : ℕ) : ℝ))) ≤
      1 := by
  let C : ℕ := ⌊2 + ‖t‖⌋₊
  let w : ℕ → ℝ := fun n => ‖t‖ / ((((n - 1 : ℕ) : ℕ) : ℝ))
  have htelescopes :
      w (M + 1) + ∑ k ∈ Finset.Ioc C M, (w k - w (k + 1)) =
        w (C + 1) :=
    finset_Ioc_adjacent_difference_telescope w C M hM
  have hC_succ :
      C + 1 - 1 = C :=
    Nat.add_sub_cancel C 1
  have hfirst :
      w (C + 1) = ‖t‖ * ((((C : ℕ) : ℝ))⁻¹) := by
    calc
      w (C + 1) =
          ‖t‖ / ((((C + 1 - 1 : ℕ) : ℕ) : ℝ)) := rfl
      _ = ‖t‖ / (((C : ℕ) : ℝ)) := by
        exact congrArg (fun n : ℕ => ‖t‖ / (((n : ℕ) : ℝ))) hC_succ
      _ = ‖t‖ * ((((C : ℕ) : ℝ))⁻¹) := by
        exact div_eq_mul_inv ‖t‖ (((C : ℕ) : ℝ))
  have hfirst_le_one :
      w (C + 1) ≤ 1 :=
    Eq.subst
      (motive := fun r : ℝ => r ≤ 1)
      hfirst.symm
      (boundaryLineOnePointRealParam_logarithmicPhase_postCutoff_norm_mul_cutoff_inv_le_one
        t ht)
  exact
    Eq.subst
      (motive := fun r : ℝ => r ≤ 1)
      htelescopes.symm
      hfirst_le_one

/-- One-step reciprocal-square domination by the adjacent reciprocal
difference.

This is the local scalar telescope used for the reciprocal-drift half of the
normalized Bernoulli block cancellation.  For the post-cutoff blocks the
left endpoint is at least two, so the inverse-square term at `m + 1` is
absorbed by `1 / m - 1 / (m + 1)`. -/
theorem boundaryLineOnePointRealParam_reciprocalSquare_le_adjacent_reciprocal_difference
    {m : ℕ}
    (hm : 0 < m) :
    (1 : ℝ) / (((m + 1 : ℕ) : ℝ) * (((m + 1 : ℕ) : ℝ))) ≤
      (1 : ℝ) / ((m : ℕ) : ℝ) -
        (1 : ℝ) / (((m + 1 : ℕ) : ℝ)) := by
  let a : ℝ := ((m : ℕ) : ℝ)
  let b : ℝ := (((m + 1 : ℕ) : ℝ))
  have ha_pos : 0 < a :=
    Nat.cast_pos.mpr hm
  have hb_pos : 0 < b :=
    Nat.cast_pos.mpr (Nat.succ_pos m)
  have ha_le_b : a ≤ b :=
    Nat.cast_le.mpr (Nat.le_succ m)
  have hden_pos : 0 < a * b :=
    mul_pos ha_pos hb_pos
  have hsq_pos : 0 < b * b :=
    mul_pos hb_pos hb_pos
  have hden_le_sq : a * b ≤ b * b :=
    mul_le_mul_of_nonneg_right ha_le_b (le_of_lt hb_pos)
  have hinv_le :
      (1 : ℝ) / (b * b) ≤ (1 : ℝ) / (a * b) :=
    one_div_le_one_div_of_le hden_pos hden_le_sq
  have hdiff :
      (1 : ℝ) / a - (1 : ℝ) / b = (1 : ℝ) / (a * b) := by
    have hleft :
        (1 : ℝ) / a = b / (a * b) := by
      have hcancel : b / (a * b) = (1 : ℝ) / a := by
        calc
          b / (a * b) = b * (a * b)⁻¹ := by
            exact div_eq_mul_inv b (a * b)
          _ = b * (b⁻¹ * a⁻¹) := by
            exact congrArg (fun r : ℝ => b * r) (mul_inv_rev a b)
          _ = (b * b⁻¹) * a⁻¹ := by
            exact (mul_assoc b b⁻¹ a⁻¹).symm
          _ = 1 * a⁻¹ := by
            exact congrArg (fun r : ℝ => r * a⁻¹) (mul_inv_cancel₀ hb_pos.ne')
          _ = a⁻¹ := by
            exact one_mul a⁻¹
          _ = (1 : ℝ) / a := by
            exact (one_div a).symm
      exact hcancel.symm
    have hright :
        (1 : ℝ) / b = a / (a * b) := by
      have hcancel : a / (a * b) = (1 : ℝ) / b := by
        calc
          a / (a * b) = a * (a * b)⁻¹ := by
            exact div_eq_mul_inv a (a * b)
          _ = a * (a⁻¹ * b⁻¹) := by
            exact congrArg (fun r : ℝ => a * r)
              (Eq.trans (mul_inv_rev a b) (mul_comm b⁻¹ a⁻¹))
          _ = (a * a⁻¹) * b⁻¹ := by
            exact (mul_assoc a a⁻¹ b⁻¹).symm
          _ = 1 * b⁻¹ := by
            exact congrArg (fun r : ℝ => r * b⁻¹) (mul_inv_cancel₀ ha_pos.ne')
          _ = b⁻¹ := by
            exact one_mul b⁻¹
          _ = (1 : ℝ) / b := by
            exact (one_div b).symm
      exact hcancel.symm
    calc
      (1 : ℝ) / a - (1 : ℝ) / b =
          b / (a * b) - (1 : ℝ) / b := by
        exact congrArg (fun r : ℝ => r - (1 : ℝ) / b) hleft
      _ = b / (a * b) - a / (a * b) := by
        exact congrArg (fun r : ℝ => b / (a * b) - r) hright
      _ = (b - a) / (a * b) := by
        exact (sub_div b a (a * b)).symm
      _ = (1 : ℝ) / (a * b) := by
        have hsucc : b = a + 1 := by
          exact Nat.cast_add_one m
        have hsub_one : b - a = (1 : ℝ) := by
          calc
            b - a = (a + 1) - a := by
              exact congrArg (fun r : ℝ => r - a) hsucc
            _ = 1 := by
              exact add_sub_cancel_left a 1
        exact congrArg (fun r : ℝ => r / (a * b)) hsub_one
  exact Eq.subst
    (motive := fun r : ℝ => (1 : ℝ) / (b * b) ≤ r)
    hdiff.symm
    hinv_le

/-- Finite reciprocal-square tails are bounded by the first reciprocal via
the adjacent-difference telescope. -/
theorem boundaryLineOnePointRealParam_reciprocalSquare_Ioc_sum_le_reciprocal_start
    {C M : ℕ}
    (hC : 0 < C)
    (hM : C ≤ M) :
    (∑ k ∈ Finset.Ioc C M,
        (1 : ℝ) / (((k + 1 : ℕ) : ℝ) * (((k + 1 : ℕ) : ℝ)))) ≤
      (1 : ℝ) / ((C : ℕ) : ℝ) := by
  let u : ℕ → ℝ := fun k : ℕ =>
    (1 : ℝ) / (((k + 1 : ℕ) : ℝ) * (((k + 1 : ℕ) : ℝ)))
  let v : ℕ → ℝ := fun k : ℕ =>
    (1 : ℝ) / ((k : ℕ) : ℝ)
  have hpoint :
      ∀ k : ℕ, k ∈ Finset.Ioc C M → u k ≤ v k - v (k + 1) := by
    intro k hk
    have hC_lt_k : C < k :=
      (Finset.mem_Ioc.mp hk).left
    have hk_pos : 0 < k :=
      lt_of_lt_of_le hC (Nat.le_of_lt hC_lt_k)
    exact
      boundaryLineOnePointRealParam_reciprocalSquare_le_adjacent_reciprocal_difference
        hk_pos
  have hsum :
      (∑ k ∈ Finset.Ioc C M, u k) ≤
        ∑ k ∈ Finset.Ioc C M, (v k - v (k + 1)) :=
    Finset.sum_le_sum (fun k hk => hpoint k hk)
  have htelescopes :
      v (M + 1) + ∑ k ∈ Finset.Ioc C M, (v k - v (k + 1)) =
        v (C + 1) :=
    finset_Ioc_adjacent_difference_telescope v C M hM
  have htail_nonneg :
      0 ≤ v (M + 1) := by
    have hsucc_pos : 0 < (M + 1 : ℕ) :=
      Nat.succ_pos M
    have hcast_pos : 0 < (((M + 1 : ℕ) : ℝ)) :=
      Nat.cast_pos.mpr hsucc_pos
    exact one_div_nonneg.mpr (le_of_lt hcast_pos)
  have htelescoped_le :
      ∑ k ∈ Finset.Ioc C M, (v k - v (k + 1)) ≤ v (C + 1) := by
    calc
      ∑ k ∈ Finset.Ioc C M, (v k - v (k + 1)) ≤
          v (M + 1) + ∑ k ∈ Finset.Ioc C M, (v k - v (k + 1)) :=
        le_add_of_nonneg_left htail_nonneg
      _ = v (C + 1) := htelescopes
  have hstart_le :
      v (C + 1) ≤ (1 : ℝ) / ((C : ℕ) : ℝ) := by
    have hC_cast_pos : 0 < ((C : ℕ) : ℝ) :=
      Nat.cast_pos.mpr hC
    have hC_le_succ : ((C : ℕ) : ℝ) ≤ (((C + 1 : ℕ) : ℝ)) :=
      Nat.cast_le.mpr (Nat.le_succ C)
    exact one_div_le_one_div_of_le hC_cast_pos hC_le_succ
  exact le_trans hsum (le_trans htelescoped_le hstart_le)

/-- The predecessor of the canonical cutoff still absorbs the logarithmic
frequency.

This is the endpoint scalar estimate needed after the reciprocal-square
telescope is shifted to the right-endpoint local blocks: the block indexed by
`n` has left endpoint `n - 1`, so the reciprocal-square tail starts at
`⌊2 + |t|⌋₊ - 1`. -/
theorem boundaryLineOnePointRealParam_logarithmicPhase_postCutoff_norm_mul_pred_cutoff_inv_le_one
    (t : ℝ)
    (ht : 1 ≤ ‖t‖) :
    ‖t‖ * (((((⌊2 + ‖t‖⌋₊ - 1 : ℕ) : ℕ) : ℝ))⁻¹) ≤
      1 := by
  let C : ℕ := ⌊2 + ‖t‖⌋₊
  have hcutoff_ge :
      (1 : ℝ) + ‖t‖ ≤ ((C : ℕ) : ℝ) :=
    boundaryLineOnePointRealParam_postCutoff_one_add_norm_le_cutoff t
  have htwo_le_one_add_norm :
      (2 : ℝ) ≤ (1 : ℝ) + ‖t‖ := by
    calc
      (2 : ℝ) = 1 + 1 := by
        exact (one_add_one_eq_two : (1 : ℝ) + 1 = 2).symm
      _ ≤ 1 + ‖t‖ := by
        exact add_le_add_left ht 1
  have htwo_le_C_real : (2 : ℝ) ≤ ((C : ℕ) : ℝ) :=
    le_trans htwo_le_one_add_norm hcutoff_ge
  have htwo_le_C_nat : 2 ≤ C := by
    have hcast :
        ((2 : ℕ) : ℝ) ≤ ((C : ℕ) : ℝ) :=
      htwo_le_C_real
    exact Nat.cast_le.mp hcast
  have hone_le_C_nat : 1 ≤ C :=
    le_trans
      (show 1 ≤ 2 from Nat.succ_le_succ (Nat.zero_le 1))
      htwo_le_C_nat
  have hpred_cast :
      (((C - 1 : ℕ) : ℝ)) = ((C : ℕ) : ℝ) - 1 :=
    Eq.trans
      (Nat.cast_sub hone_le_C_nat)
      (congrArg (fun r : ℝ => ((C : ℕ) : ℝ) - r)
        boundaryGrowth_natCast_one_eq_real_one)
  have hnorm_eq_sub :
      ‖t‖ = ((1 : ℝ) + ‖t‖) - 1 := by
    exact (add_sub_cancel_left 1 ‖t‖).symm
  have hnorm_le_pred :
      ‖t‖ ≤ (((C - 1 : ℕ) : ℝ)) := by
    have hsub_le :
        ((1 : ℝ) + ‖t‖) - 1 ≤ ((C : ℕ) : ℝ) - 1 :=
      sub_le_sub_right hcutoff_ge 1
    exact Eq.subst
      (motive := fun r : ℝ => ‖t‖ ≤ r)
      hpred_cast.symm
      (Eq.subst
        (motive := fun r : ℝ => r ≤ ((C : ℕ) : ℝ) - 1)
        hnorm_eq_sub.symm
        hsub_le)
  have hpred_pos :
      0 < (((C - 1 : ℕ) : ℝ)) :=
    lt_of_lt_of_le
      (lt_of_lt_of_le zero_lt_one ht)
      hnorm_le_pred
  have hratio :
      ‖t‖ / (((C - 1 : ℕ) : ℝ)) ≤ 1 :=
    (div_le_one₀ hpred_pos).mpr hnorm_le_pred
  exact Eq.subst
    (motive := fun r : ℝ => r ≤ 1)
    (div_eq_mul_inv ‖t‖ (((C - 1 : ℕ) : ℝ)))
    hratio

/-- Right-endpoint reciprocal-square tails are bounded by the reciprocal of
the predecessor of the first endpoint.

This is the shifted telescope used by the selected reciprocal-variation
estimate: for blocks `n ∈ (C,M]`, the reciprocal movement is controlled by
the square of the left endpoint `n - 1`. -/
theorem boundaryLineOnePointRealParam_reciprocalSquare_Ioc_pred_sum_le_reciprocal_pred_start
    {C M : ℕ}
    (hC : 1 < C)
    (hM : C ≤ M) :
    (∑ n ∈ Finset.Ioc C M,
        (1 : ℝ) /
          (((n - 1 : ℕ) : ℝ) * (((n - 1 : ℕ) : ℝ)))) ≤
      (1 : ℝ) / (((C - 1 : ℕ) : ℝ)) := by
  let u : ℕ → ℝ := fun n : ℕ =>
    (1 : ℝ) /
      (((n - 1 : ℕ) : ℝ) * (((n - 1 : ℕ) : ℝ)))
  let v : ℕ → ℝ := fun n : ℕ =>
    (1 : ℝ) / (((n - 2 : ℕ) : ℝ))
  have hpoint :
      ∀ n : ℕ, n ∈ Finset.Ioc C M → u n ≤ v n - v (n + 1) := by
    intro n hn
    have hC_lt_n : C < n :=
      (Finset.mem_Ioc.mp hn).left
    have htwo_le_C : 2 ≤ C :=
      Nat.succ_le_of_lt hC
    have htwo_lt_n : 2 < n :=
      lt_of_le_of_lt htwo_le_C hC_lt_n
    have htwo_le_n : 2 ≤ n :=
      Nat.le_of_lt htwo_lt_n
    have hpred_pos : 0 < n - 2 :=
      Nat.sub_pos_of_lt htwo_lt_n
    have hsucc_left_raw :
        n + 1 - 2 = n - 2 + 1 :=
      Nat.succ_sub htwo_le_n
    have hsucc_right :
        n + 1 - 2 = n - 1 :=
      Nat.add_sub_add_right n 1 1
    have hsucc_pred :
        n - 2 + 1 = n - 1 := by
      exact Eq.trans hsucc_left_raw.symm hsucc_right
    have hraw :
        (1 : ℝ) /
            ((((n - 2) + 1 : ℕ) : ℝ) *
              ((((n - 2) + 1 : ℕ) : ℝ))) ≤
          (1 : ℝ) / (((n - 2 : ℕ) : ℝ)) -
            (1 : ℝ) / (((((n - 2) + 1 : ℕ) : ℕ) : ℝ)) :=
      boundaryLineOnePointRealParam_reciprocalSquare_le_adjacent_reciprocal_difference
        hpred_pos
    have hleft :
        (1 : ℝ) /
            ((((n - 2) + 1 : ℕ) : ℝ) *
              ((((n - 2) + 1 : ℕ) : ℝ))) =
          u n := by
      exact congrArg
        (fun k : ℕ =>
          (1 : ℝ) / (((k : ℕ) : ℝ) * (((k : ℕ) : ℝ))))
        hsucc_pred
    have hright :
        (1 : ℝ) / (((n - 2 : ℕ) : ℝ)) -
            (1 : ℝ) / (((((n - 2) + 1 : ℕ) : ℕ) : ℝ)) =
          v n - v (n + 1) := by
      exact congrArg
        (fun k : ℕ =>
          (1 : ℝ) / (((n - 2 : ℕ) : ℝ)) -
            (1 : ℝ) / (((k : ℕ) : ℝ)))
        (Eq.trans hsucc_pred hsucc_right.symm)
    have hleft_transport :
        u n ≤
          (1 : ℝ) / (((n - 2 : ℕ) : ℝ)) -
            (1 : ℝ) / (((((n - 2) + 1 : ℕ) : ℕ) : ℝ)) :=
      Eq.subst
        (motive := fun r : ℝ =>
          r ≤
            (1 : ℝ) / (((n - 2 : ℕ) : ℝ)) -
              (1 : ℝ) / (((((n - 2) + 1 : ℕ) : ℕ) : ℝ)))
        hleft
        hraw
    exact Eq.subst
      (motive := fun r : ℝ => u n ≤ r)
      hright
      hleft_transport
  have hsum :
      (∑ n ∈ Finset.Ioc C M, u n) ≤
        ∑ n ∈ Finset.Ioc C M, (v n - v (n + 1)) :=
    Finset.sum_le_sum (fun n hn => hpoint n hn)
  have htelescopes :
      v (M + 1) + ∑ n ∈ Finset.Ioc C M, (v n - v (n + 1)) =
        v (C + 1) :=
    finset_Ioc_adjacent_difference_telescope v C M hM
  have htail_nonneg :
      0 ≤ v (M + 1) := by
    exact one_div_nonneg.mpr (Nat.cast_nonneg (M + 1 - 2))
  have htelescoped_le :
      ∑ n ∈ Finset.Ioc C M, (v n - v (n + 1)) ≤ v (C + 1) := by
    calc
      ∑ n ∈ Finset.Ioc C M, (v n - v (n + 1)) ≤
          v (M + 1) + ∑ n ∈ Finset.Ioc C M, (v n - v (n + 1)) :=
        le_add_of_nonneg_left htail_nonneg
      _ = v (C + 1) := htelescopes
  have hstart :
      v (C + 1) = (1 : ℝ) / (((C - 1 : ℕ) : ℝ)) := by
    have hnat : C + 1 - 2 = C - 1 := by
      exact Nat.add_sub_add_right C 1 1
    exact congrArg
      (fun k : ℕ => (1 : ℝ) / (((k : ℕ) : ℝ)))
      hnat
  exact le_trans hsum
    (Eq.subst
      (motive := fun r : ℝ =>
        ∑ n ∈ Finset.Ioc C M, (v n - v (n + 1)) ≤ r)
      hstart
      htelescoped_le)

/-- Canonical post-cutoff reciprocal-variation scalar sum.

After multiplying the shifted reciprocal-square telescope by `|t|`, the
predecessor-cutoff endpoint estimate absorbs the whole selected local
reciprocal-variation contribution into `1`. -/
theorem boundaryLineOnePointRealParam_reciprocalVariation_selected_Ioc_sum_le_one
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    {M : ℕ}
    (hM : ⌊2 + ‖t‖⌋₊ ≤ M) :
    (∑ n ∈ Finset.Ioc ⌊2 + ‖t‖⌋₊ M,
        ‖t‖ *
          ((1 : ℝ) /
            (((n - 1 : ℕ) : ℝ) * (((n - 1 : ℕ) : ℝ))))) ≤
      1 := by
  let C : ℕ := ⌊2 + ‖t‖⌋₊
  let u : ℕ → ℝ := fun n : ℕ =>
    (1 : ℝ) /
      (((n - 1 : ℕ) : ℝ) * (((n - 1 : ℕ) : ℝ)))
  have hcutoff_ge :
      (1 : ℝ) + ‖t‖ ≤ ((C : ℕ) : ℝ) :=
    boundaryLineOnePointRealParam_postCutoff_one_add_norm_le_cutoff t
  have htwo_le_one_add_norm :
      (2 : ℝ) ≤ (1 : ℝ) + ‖t‖ := by
    calc
      (2 : ℝ) = 1 + 1 := by
        exact (one_add_one_eq_two : (1 : ℝ) + 1 = 2).symm
      _ ≤ 1 + ‖t‖ := by
        exact add_le_add_left ht 1
  have htwo_le_C_real : (2 : ℝ) ≤ ((C : ℕ) : ℝ) :=
    le_trans htwo_le_one_add_norm hcutoff_ge
  have htwo_le_C_nat : 2 ≤ C := by
    have hcast :
        ((2 : ℕ) : ℝ) ≤ ((C : ℕ) : ℝ) :=
      htwo_le_C_real
    exact Nat.cast_le.mp hcast
  have hone_lt_C : 1 < C :=
    lt_of_lt_of_le (show 1 < 2 from Nat.lt.base 1) htwo_le_C_nat
  have hsum_u :
      (∑ n ∈ Finset.Ioc C M, u n) ≤
        (1 : ℝ) / (((C - 1 : ℕ) : ℝ)) :=
    boundaryLineOnePointRealParam_reciprocalSquare_Ioc_pred_sum_le_reciprocal_pred_start
      hone_lt_C hM
  have hsum_mul :
      (∑ n ∈ Finset.Ioc C M, ‖t‖ * u n) =
        ‖t‖ * (∑ n ∈ Finset.Ioc C M, u n) :=
    (Finset.mul_sum (Finset.Ioc C M) (fun n : ℕ => u n) ‖t‖).symm
  have hmul_le :
      ‖t‖ * (∑ n ∈ Finset.Ioc C M, u n) ≤
        ‖t‖ * ((1 : ℝ) / (((C - 1 : ℕ) : ℝ))) :=
    mul_le_mul_of_nonneg_left hsum_u (norm_nonneg t)
  have hendpoint :
      ‖t‖ * ((1 : ℝ) / (((C - 1 : ℕ) : ℝ))) ≤ 1 := by
    have hdiv :
        (1 : ℝ) / (((C - 1 : ℕ) : ℝ)) =
          ((((C - 1 : ℕ) : ℝ))⁻¹) := by
      exact one_div (((C - 1 : ℕ) : ℝ))
    exact Eq.subst
      (motive := fun r : ℝ => ‖t‖ * r ≤ 1)
      hdiv.symm
      (boundaryLineOnePointRealParam_logarithmicPhase_postCutoff_norm_mul_pred_cutoff_inv_le_one
        t ht)
  exact Eq.subst
    (motive := fun r : ℝ => r ≤ 1)
    hsum_mul.symm
    (le_trans hmul_le hendpoint)

/-- Finite Abel/Dirichlet coefficient absorption for the phase-drift weight
`|t| / (n - 1)`.

If the unweighted phase-block partial sums are bounded by `B` on every
post-cutoff prefix, then weighting those blocks by the decreasing coefficient
`|t|/(n-1)` preserves the same bound. -/
theorem boundaryLineOnePointRealParam_phaseDrift_coefficientWeight_finite_sum_norm_le
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    {M : ℕ}
    (hM : ⌊2 + ‖t‖⌋₊ ≤ M)
    {B : ℝ}
    (u : ℕ → ℂ)
    (hpartial :
      ∀ K : ℕ,
        ⌊2 + ‖t‖⌋₊ ≤ K →
          ‖∑ k ∈ Finset.Ioc ⌊2 + ‖t‖⌋₊ K, u k‖ ≤ B) :
    ‖∑ k ∈ Finset.Ioc ⌊2 + ‖t‖⌋₊ M,
        (((‖t‖ / ((((k - 1 : ℕ) : ℕ) : ℝ)) : ℝ) : ℂ) * u k)‖ ≤
      B := by
  exact
    abel_positive_weighted_tail_finite_norm_le_of_bounded_partial_sums
      (u := u)
      (w := fun k : ℕ => ‖t‖ / ((((k - 1 : ℕ) : ℕ) : ℝ)))
      (N := ⌊2 + ‖t‖⌋₊)
      (M := M)
      (C := B)
      hM
      hpartial
      (fun k _hk =>
        boundaryLineOnePointRealParam_phaseDrift_coefficientWeight_nonneg t k)
      (fun k l hk hkl =>
        boundaryLineOnePointRealParam_phaseDrift_coefficientWeight_antitone
          t hk hkl)
      (boundaryLineOnePointRealParam_phaseDrift_coefficientWeight_variation_le_one
        t ht hM)

/-- Local-terminal finite Abel/Dirichlet coefficient absorption for the
phase-drift weight `|t| / (n - 1)`.

Only post-cutoff prefixes ending at `K ≤ M` are needed to bound the finite sum
up to `M`; this is the version used with a bound whose logarithmic scale
depends on the terminal endpoint `M`. -/
theorem boundaryLineOnePointRealParam_phaseDrift_coefficientWeight_finite_sum_norm_le_of_local
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    {M : ℕ}
    (hM : ⌊2 + ‖t‖⌋₊ ≤ M)
    {B : ℝ}
    (u : ℕ → ℂ)
    (hpartial :
      ∀ K : ℕ,
        ⌊2 + ‖t‖⌋₊ ≤ K →
        K ≤ M →
          ‖∑ k ∈ Finset.Ioc ⌊2 + ‖t‖⌋₊ K, u k‖ ≤ B) :
    ‖∑ k ∈ Finset.Ioc ⌊2 + ‖t‖⌋₊ M,
        (((‖t‖ / ((((k - 1 : ℕ) : ℕ) : ℝ)) : ℝ) : ℂ) * u k)‖ ≤
      B := by
  let N : ℕ := ⌊2 + ‖t‖⌋₊
  let w : ℕ → ℝ := fun k => ‖t‖ / ((((k - 1 : ℕ) : ℕ) : ℝ))
  have hC_nonneg : 0 ≤ B := by
    have hnorm_nonneg :
        0 ≤ ‖∑ k ∈ Finset.Ioc N M, u k‖ :=
      norm_nonneg (∑ k ∈ Finset.Ioc N M, u k)
    exact le_trans hnorm_nonneg (hpartial M hM le_rfl)
  have hidentity :
      (∑ k ∈ Finset.Ioc N M, ((w k : ℝ) : ℂ) * u k) =
        ((w (M + 1) : ℝ) : ℂ) *
            (∑ k ∈ Finset.Ioc N M, u k) +
          ∑ k ∈ Finset.Ioc N M,
            (((w k - w (k + 1) : ℝ) : ℂ) *
              (∑ j ∈ Finset.Ioc N k, u j)) :=
    abel_positive_weighted_tail_finite_summation_by_parts hM
  have hw_nonneg : ∀ k : ℕ, N < k → 0 ≤ w k := by
    intro k _hk
    exact boundaryLineOnePointRealParam_phaseDrift_coefficientWeight_nonneg t k
  have hw_antitone :
      ∀ k l : ℕ, N < k → k ≤ l → w l ≤ w k := by
    intro k l hk hkl
    exact
      boundaryLineOnePointRealParam_phaseDrift_coefficientWeight_antitone
        t hk hkl
  have hterminal_nonneg : 0 ≤ w (M + 1) :=
    hw_nonneg (M + 1) (Nat.lt_succ_of_le hM)
  have hterminal_norm :
      ‖((w (M + 1) : ℝ) : ℂ) *
          (∑ k ∈ Finset.Ioc N M, u k)‖ ≤
        w (M + 1) * B := by
    have hmul :
        ‖((w (M + 1) : ℝ) : ℂ) *
            (∑ k ∈ Finset.Ioc N M, u k)‖ =
          ‖((w (M + 1) : ℝ) : ℂ)‖ *
            ‖∑ k ∈ Finset.Ioc N M, u k‖ :=
      norm_mul ((w (M + 1) : ℝ) : ℂ)
        (∑ k ∈ Finset.Ioc N M, u k)
    have hreal_norm :
        ‖((w (M + 1) : ℝ) : ℂ)‖ = w (M + 1) := by
      have hcomplex_real :
          ‖((w (M + 1) : ℝ) : ℂ)‖ = ‖w (M + 1)‖ :=
        RCLike.norm_ofReal (w (M + 1))
      have hreal_abs : ‖w (M + 1)‖ = w (M + 1) :=
        Real.norm_of_nonneg hterminal_nonneg
      exact Eq.trans hcomplex_real hreal_abs
    have hscaled :
        w (M + 1) * ‖∑ k ∈ Finset.Ioc N M, u k‖ ≤
          w (M + 1) * B :=
      mul_le_mul_of_nonneg_left
        (hpartial M hM le_rfl)
        hterminal_nonneg
    have hleft_eq :
        ‖((w (M + 1) : ℝ) : ℂ)‖ *
            ‖∑ k ∈ Finset.Ioc N M, u k‖ =
          w (M + 1) * ‖∑ k ∈ Finset.Ioc N M, u k‖ :=
      congrArg
        (fun a : ℝ => a * ‖∑ k ∈ Finset.Ioc N M, u k‖)
        hreal_norm
    exact Eq.subst
      (motive := fun x : ℝ => x ≤ w (M + 1) * B)
      hmul.symm
      (Eq.subst
        (motive := fun x : ℝ => x ≤ w (M + 1) * B)
        hleft_eq.symm
        hscaled)
  have hsum_norm :
      ‖∑ k ∈ Finset.Ioc N M,
            (((w k - w (k + 1) : ℝ) : ℂ) *
              (∑ j ∈ Finset.Ioc N k, u j))‖ ≤
        (∑ k ∈ Finset.Ioc N M, (w k - w (k + 1))) * B := by
    have hterm :
        ∀ k ∈ Finset.Ioc N M,
          ‖(((w k - w (k + 1) : ℝ) : ℂ) *
              (∑ j ∈ Finset.Ioc N k, u j))‖ ≤
            (w k - w (k + 1)) * B := by
      intro k hk_mem
      have hk_tail : N < k :=
        (Finset.mem_Ioc.mp hk_mem).1
      have hk_le_M : k ≤ M :=
        (Finset.mem_Ioc.mp hk_mem).2
      have hdiff_nonneg : 0 ≤ w k - w (k + 1) :=
        abel_positive_weighted_tail_weight_difference_nonneg
          hw_antitone hk_tail
      have hmul :
          ‖(((w k - w (k + 1) : ℝ) : ℂ) *
              (∑ j ∈ Finset.Ioc N k, u j))‖ =
            ‖((w k - w (k + 1) : ℝ) : ℂ)‖ *
              ‖∑ j ∈ Finset.Ioc N k, u j‖ :=
        norm_mul ((w k - w (k + 1) : ℝ) : ℂ)
          (∑ j ∈ Finset.Ioc N k, u j)
      have hreal_norm :
          ‖((w k - w (k + 1) : ℝ) : ℂ)‖ =
            w k - w (k + 1) := by
        have hcomplex_real :
            ‖((w k - w (k + 1) : ℝ) : ℂ)‖ =
              ‖w k - w (k + 1)‖ :=
          RCLike.norm_ofReal (w k - w (k + 1))
        have hreal_abs : ‖w k - w (k + 1)‖ = w k - w (k + 1) :=
          Real.norm_of_nonneg hdiff_nonneg
        exact Eq.trans hcomplex_real hreal_abs
      have hscaled :
          (w k - w (k + 1)) *
              ‖∑ j ∈ Finset.Ioc N k, u j‖ ≤
            (w k - w (k + 1)) * B :=
        mul_le_mul_of_nonneg_left
          (hpartial k (Nat.le_of_lt hk_tail) hk_le_M)
          hdiff_nonneg
      have hleft_eq :
          ‖((w k - w (k + 1) : ℝ) : ℂ)‖ *
              ‖∑ j ∈ Finset.Ioc N k, u j‖ =
            (w k - w (k + 1)) *
              ‖∑ j ∈ Finset.Ioc N k, u j‖ :=
        congrArg
          (fun a : ℝ => a * ‖∑ j ∈ Finset.Ioc N k, u j‖)
          hreal_norm
      exact Eq.subst
        (motive := fun x : ℝ => x ≤ (w k - w (k + 1)) * B)
        hmul.symm
        (Eq.subst
          (motive := fun x : ℝ => x ≤ (w k - w (k + 1)) * B)
          hleft_eq.symm
          hscaled)
    have hsum_le :
        ‖∑ k ∈ Finset.Ioc N M,
            (((w k - w (k + 1) : ℝ) : ℂ) *
              (∑ j ∈ Finset.Ioc N k, u j))‖ ≤
          ∑ k ∈ Finset.Ioc N M,
            ‖(((w k - w (k + 1) : ℝ) : ℂ) *
              (∑ j ∈ Finset.Ioc N k, u j))‖ :=
      norm_sum_le
        (Finset.Ioc N M)
        (fun k : ℕ =>
          (((w k - w (k + 1) : ℝ) : ℂ) *
            (∑ j ∈ Finset.Ioc N k, u j)))
    have hsum_bound :
        (∑ k ∈ Finset.Ioc N M,
            ‖(((w k - w (k + 1) : ℝ) : ℂ) *
              (∑ j ∈ Finset.Ioc N k, u j))‖) ≤
          ∑ k ∈ Finset.Ioc N M, (w k - w (k + 1)) * B :=
      Finset.sum_le_sum hterm
    have hfactor :
        (∑ k ∈ Finset.Ioc N M, (w k - w (k + 1)) * B) =
          (∑ k ∈ Finset.Ioc N M, (w k - w (k + 1))) * B := by
      exact (Finset.sum_mul (Finset.Ioc N M)
        (fun k : ℕ => w k - w (k + 1)) B).symm
    exact le_trans hsum_le (hsum_bound.trans_eq hfactor)
  have htriangle :
      ‖((w (M + 1) : ℝ) : ℂ) *
            (∑ k ∈ Finset.Ioc N M, u k) +
          ∑ k ∈ Finset.Ioc N M,
            (((w k - w (k + 1) : ℝ) : ℂ) *
              (∑ j ∈ Finset.Ioc N k, u j))‖ ≤
        w (M + 1) * B +
          (∑ k ∈ Finset.Ioc N M, (w k - w (k + 1))) * B :=
    (norm_add_le
      (((w (M + 1) : ℝ) : ℂ) *
        (∑ k ∈ Finset.Ioc N M, u k))
      (∑ k ∈ Finset.Ioc N M,
        (((w k - w (k + 1) : ℝ) : ℂ) *
          (∑ j ∈ Finset.Ioc N k, u j)))).trans
      (add_le_add hterminal_norm hsum_norm)
  have hw_variation :
      w (M + 1) + ∑ k ∈ Finset.Ioc N M, (w k - w (k + 1)) ≤ 1 :=
    boundaryLineOnePointRealParam_phaseDrift_coefficientWeight_variation_le_one
      t ht hM
  have hvariation_mul :
      w (M + 1) * B +
          (∑ k ∈ Finset.Ioc N M, (w k - w (k + 1))) * B ≤
        B := by
    have hfactor :
        w (M + 1) * B +
            (∑ k ∈ Finset.Ioc N M, (w k - w (k + 1))) * B =
          (w (M + 1) +
            ∑ k ∈ Finset.Ioc N M, (w k - w (k + 1))) * B := by
      exact (add_mul (w (M + 1))
        (∑ k ∈ Finset.Ioc N M, (w k - w (k + 1))) B).symm
    have hscaled :
        (w (M + 1) +
            ∑ k ∈ Finset.Ioc N M, (w k - w (k + 1))) * B ≤
          1 * B :=
      mul_le_mul_of_nonneg_right hw_variation hC_nonneg
    exact Eq.subst
      (motive := fun x : ℝ => x ≤ B)
      hfactor.symm
      (hscaled.trans_eq (one_mul B))
  exact Eq.subst
    (motive := fun z : ℂ => ‖z‖ ≤ B)
    hidentity.symm
    (le_trans htriangle hvariation_mul)

/-- The fixed complex direction of the phase-drift coefficient has unit norm. -/
theorem boundaryLineOnePointRealParam_phaseDrift_coefficientDirection_norm_eq_one
    (t : ℝ)
    (ht : 1 ≤ ‖t‖) :
    ‖((-(t : ℂ) * Complex.I) / ((‖t‖ : ℝ) : ℂ))‖ = (1 : ℝ) := by
  let A : ℂ := -(t : ℂ) * Complex.I
  let T : ℂ := ((‖t‖ : ℝ) : ℂ)
  have hA_norm : ‖A‖ = ‖t‖ :=
    logarithmicPhaseFunction_derivative_numerator_norm t
  have hT_norm : ‖T‖ = ‖t‖ := by
    exact Eq.trans (RCLike.norm_ofReal ‖t‖) (abs_of_nonneg (norm_nonneg t))
  have hnorm_div :
      ‖A / T‖ = ‖A‖ / ‖T‖ :=
    norm_div A T
  have ht_pos : 0 < ‖t‖ :=
    lt_of_lt_of_le zero_lt_one ht
  have hquot :
      ‖A‖ / ‖T‖ = (1 : ℝ) := by
    calc
      ‖A‖ / ‖T‖ = ‖t‖ / ‖T‖ := by
        exact congrArg (fun r : ℝ => r / ‖T‖) hA_norm
      _ = ‖t‖ / ‖t‖ := by
        exact congrArg (fun r : ℝ => ‖t‖ / r) hT_norm
      _ = 1 := by
        exact div_self (ne_of_gt ht_pos)
  exact Eq.trans hnorm_div hquot

/-- Norm of the concrete phase-drift coefficient at a positive left endpoint. -/
theorem boundaryLineOnePointRealParam_phaseDrift_leftEndpointCoefficient_norm_eq_weight
    (t : ℝ)
    {m : ℕ}
    (hm : 0 < m) :
    ‖((-(t : ℂ) * Complex.I) *
        (((((m : ℕ) : ℝ) : ℂ)⁻¹)))‖ =
      ‖t‖ / (((m : ℕ) : ℝ)) := by
  let A : ℂ := -(t : ℂ) * Complex.I
  let mr : ℝ := ((m : ℕ) : ℝ)
  have hmr_pos : 0 < mr :=
    Nat.cast_pos.mpr hm
  have hA_norm : ‖A‖ = ‖t‖ :=
    logarithmicPhaseFunction_derivative_numerator_norm t
  have hinv_norm : ‖((mr : ℂ)⁻¹)‖ = mr⁻¹ := by
    have hnorm_inv :
        ‖((mr : ℂ)⁻¹)‖ = (‖(mr : ℂ)‖)⁻¹ :=
      norm_inv (mr : ℂ)
    have hnorm_real :
        ‖(mr : ℂ)‖ = mr := by
      exact Eq.trans (RCLike.norm_ofReal mr) (abs_of_pos hmr_pos)
    exact Eq.trans hnorm_inv (congrArg Inv.inv hnorm_real)
  calc
    ‖((-(t : ℂ) * Complex.I) * ((mr : ℂ)⁻¹))‖ =
        ‖A‖ * ‖((mr : ℂ)⁻¹)‖ := by
      exact norm_mul A ((mr : ℂ)⁻¹)
    _ = ‖t‖ * ‖((mr : ℂ)⁻¹)‖ := by
      exact congrArg (fun r : ℝ => r * ‖((mr : ℂ)⁻¹)‖) hA_norm
    _ = ‖t‖ * mr⁻¹ := by
      exact congrArg (fun r : ℝ => ‖t‖ * r) hinv_norm
    _ = ‖t‖ / mr := by
      exact (div_eq_mul_inv ‖t‖ mr).symm

/-- Right-endpoint form of the concrete phase-drift coefficient norm. -/
theorem boundaryLineOnePointRealParam_phaseDrift_rightEndpointCoefficient_norm_eq_weight
    (t : ℝ)
    {M n : ℕ}
    (hn : n ∈ Finset.Ioc ⌊2 + ‖t‖⌋₊ M) :
    ‖((-(t : ℂ) * Complex.I) *
        ((((((n - 1 : ℕ) : ℕ) : ℝ) : ℂ)⁻¹)))‖ =
      ‖t‖ / (((((n - 1 : ℕ) : ℕ) : ℝ))) := by
  have hcutoff_lt_n : ⌊2 + ‖t‖⌋₊ < n :=
    (Finset.mem_Ioc.mp hn).1
  have hcutoff_pos : 0 < ⌊2 + ‖t‖⌋₊ :=
    boundaryLineOnePointRealParam_cutoff_pos t
  have hn_pos : 0 < n :=
    lt_trans hcutoff_pos hcutoff_lt_n
  have hm_pos : 0 < n - 1 :=
    Nat.sub_pos_of_lt
      (lt_of_le_of_lt
        (Nat.succ_le_of_lt hcutoff_pos)
        hcutoff_lt_n)
  exact
    boundaryLineOnePointRealParam_phaseDrift_leftEndpointCoefficient_norm_eq_weight
      t hm_pos

/-- Factor the concrete phase-drift coefficient into a fixed unit direction
and the positive Abel weight `|t| / m`. -/
theorem boundaryLineOnePointRealParam_phaseDrift_leftEndpointCoefficient_eq_direction_mul_weight
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    {m : ℕ}
    (hm : 0 < m) :
    ((-(t : ℂ) * Complex.I) *
        (((((m : ℕ) : ℝ) : ℂ)⁻¹))) =
      ((-(t : ℂ) * Complex.I) / ((‖t‖ : ℝ) : ℂ)) *
        (((‖t‖ / (((m : ℕ) : ℝ)) : ℝ) : ℂ)) := by
  let A : ℂ := -(t : ℂ) * Complex.I
  let T : ℂ := ((‖t‖ : ℝ) : ℂ)
  let R : ℂ := ((((m : ℕ) : ℝ) : ℂ))
  have ht_pos : 0 < ‖t‖ :=
    lt_of_lt_of_le zero_lt_one ht
  have hT_ne : T ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (ne_of_gt ht_pos)
  have hR_ne : R ≠ 0 :=
    Complex.ofReal_ne_zero.mpr
      (ne_of_gt (Nat.cast_pos.mpr hm : 0 < ((m : ℕ) : ℝ)))
  have hweight :
      (((‖t‖ / (((m : ℕ) : ℝ)) : ℝ) : ℂ)) = T / R := by
    exact Complex.ofReal_div ‖t‖ (((m : ℕ) : ℝ))
  have hcancel : T⁻¹ * T = (1 : ℂ) :=
    inv_mul_cancel₀ hT_ne
  calc
    A * R⁻¹ =
        (A * (1 : ℂ)) * R⁻¹ := by
      exact congrArg (fun z : ℂ => z * R⁻¹) (mul_one A).symm
    _ = (A * (T⁻¹ * T)) * R⁻¹ := by
      exact congrArg (fun z : ℂ => (A * z) * R⁻¹) hcancel.symm
    _ = ((A * T⁻¹) * T) * R⁻¹ := by
      exact congrArg (fun z : ℂ => z * R⁻¹) (mul_assoc A T⁻¹ T).symm
    _ = (A * T⁻¹) * (T * R⁻¹) := by
      exact mul_assoc (A * T⁻¹) T R⁻¹
    _ = (A / T) * (T / R) := by
      exact congrArg₂ (fun x y : ℂ => x * y)
        (div_eq_mul_inv A T).symm
        (div_eq_mul_inv T R).symm
    _ = (A / T) * (((‖t‖ / (((m : ℕ) : ℝ)) : ℝ) : ℂ)) := by
      exact congrArg (fun z : ℂ => (A / T) * z) hweight.symm

/-- Right-endpoint form of the phase-drift coefficient factorization. -/
theorem boundaryLineOnePointRealParam_phaseDrift_rightEndpointCoefficient_eq_direction_mul_weight
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    {M n : ℕ}
    (hn : n ∈ Finset.Ioc ⌊2 + ‖t‖⌋₊ M) :
    ((-(t : ℂ) * Complex.I) *
        ((((((n - 1 : ℕ) : ℕ) : ℝ) : ℂ)⁻¹))) =
      ((-(t : ℂ) * Complex.I) / ((‖t‖ : ℝ) : ℂ)) *
        (((‖t‖ / (((((n - 1 : ℕ) : ℕ) : ℝ))) : ℝ) : ℂ)) := by
  have hcutoff_lt_n : ⌊2 + ‖t‖⌋₊ < n :=
    (Finset.mem_Ioc.mp hn).1
  have hcutoff_pos : 0 < ⌊2 + ‖t‖⌋₊ :=
    boundaryLineOnePointRealParam_cutoff_pos t
  have hone_le_cutoff : 1 ≤ ⌊2 + ‖t‖⌋₊ :=
    Nat.succ_le_of_lt hcutoff_pos
  have hone_lt_n : 1 < n :=
    lt_of_le_of_lt hone_le_cutoff hcutoff_lt_n
  have hm_pos : 0 < n - 1 :=
    Nat.sub_pos_of_lt hone_lt_n
  exact
    boundaryLineOnePointRealParam_phaseDrift_leftEndpointCoefficient_eq_direction_mul_weight
      t ht hm_pos

theorem boundaryLineOnePointRealParam_logarithmicPhase_postCutoff_inverseSquareEndpointDifference_le_one_ownerGap
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    {M : ℕ}
    (hM : ⌊2 + ‖t‖⌋₊ ≤ M) :
    (1 + ‖t‖) *
        ((((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ))⁻¹ - (((M : ℕ) : ℝ))⁻¹) ≤
      1 := by
  exact le_trans
    (boundaryLineOnePointRealParam_logarithmicPhase_postCutoff_inverseSquareEndpointDifference_le_cutoffRatio_ownerGap
      t ht hM)
    (boundaryLineOnePointRealParam_logarithmicPhase_postCutoff_cutoffRatio_le_one_ownerGap
      t ht)

theorem boundaryLineOnePointRealParam_logarithmicPhase_postCutoff_bernoulliRemainder_realMajorant_le_one_ownerGap
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    {M : ℕ}
    (hM : ⌊2 + ‖t‖⌋₊ ≤ M) :
    (∫ x in Set.Ioc (((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ)) (((M : ℕ) : ℝ)),
        (1 + ‖t‖) / x ^ 2) ≤
      1 := by
  have hcalc :
      (∫ x in Set.Ioc (((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ)) (((M : ℕ) : ℝ)),
          (1 + ‖t‖) / x ^ 2) =
        (1 + ‖t‖) *
          ((((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ))⁻¹ - (((M : ℕ) : ℝ))⁻¹) :=
    boundaryLineOnePointRealParam_logarithmicPhase_postCutoff_inverseSquareMajorant_eq_endpointDifference_ownerGap
      t ht hM
  have hendpoint :
      (1 + ‖t‖) *
          ((((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ))⁻¹ - (((M : ℕ) : ℝ))⁻¹) ≤
        1 :=
    boundaryLineOnePointRealParam_logarithmicPhase_postCutoff_inverseSquareEndpointDifference_le_one_ownerGap
      t ht hM
  exact Eq.subst
    (motive := fun y : ℝ => y ≤ 1)
    hcalc.symm
    hendpoint

/-- Real-variable cutoff estimate for the Bernoulli-remainder derivative
majorant. -/
theorem boundaryLineOnePointRealParam_logarithmicPhase_postCutoff_bernoulliRemainder_realMajorant_le_ownerGap
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    {M : ℕ}
    (hM : ⌊2 + ‖t‖⌋₊ ≤ M) :
    (∫ x in Set.Ioc (((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ)) (((M : ℕ) : ℝ)),
        (1 + ‖t‖) / x ^ 2) ≤
      1 + 16 * Real.log (3 + ‖t‖) := by
  have hmajorant_le_one :
      (∫ x in Set.Ioc (((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ)) (((M : ℕ) : ℝ)),
          (1 + ‖t‖) / x ^ 2) ≤
        1 :=
    boundaryLineOnePointRealParam_logarithmicPhase_postCutoff_bernoulliRemainder_realMajorant_le_one_ownerGap
      t ht hM
  have hlog_nonneg : 0 ≤ Real.log (3 + ‖t‖) := by
    have hone_le_arg : (1 : ℝ) ≤ 3 + ‖t‖ := by
      calc
        (1 : ℝ) ≤ 3 := by
          exact boundaryGrowth_real_one_le_three
        _ ≤ 3 + ‖t‖ :=
          le_add_of_nonneg_right (norm_nonneg t)
    exact Real.log_nonneg hone_le_arg
  have htail_nonneg : 0 ≤ 16 * Real.log (3 + ‖t‖) :=
    mul_nonneg (show (0 : ℝ) ≤ 16 from Nat.cast_nonneg 16) hlog_nonneg
  exact le_trans hmajorant_le_one
    (le_add_of_nonneg_right htail_nonneg)

/-- Owner sink for the first-periodic-Bernoulli remainder estimate after the
canonical cutoff. -/
theorem boundaryLineOnePointRealParam_logarithmicPhase_postCutoff_bernoulliRemainder_norm_le_ownerGap
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    {M : ℕ}
    (hM : ⌊2 + ‖t‖⌋₊ ≤ M) :
    ‖∫ x in Set.Ioc (((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ)) (((M : ℕ) : ℝ)),
        ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) *
          (-boundaryLineOnePointRealParam t *
            (((x : ℝ) : ℂ) ^
              (-(boundaryLineOnePointRealParam t + 1))))‖ ≤
      1 + 16 * Real.log (3 + ‖t‖) := by
  exact le_trans
    (boundaryLineOnePointRealParam_logarithmicPhase_postCutoff_bernoulliRemainder_norm_le_realMajorant_ownerGap
      t ht hM)
    (boundaryLineOnePointRealParam_logarithmicPhase_postCutoff_bernoulliRemainder_realMajorant_le_ownerGap
      t ht hM)

/-- Public Bernoulli-remainder component bound. -/
theorem boundaryLineOnePointRealParam_logarithmicPhase_postCutoff_bernoulliRemainder_norm_le
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    {M : ℕ}
    (hM : ⌊2 + ‖t‖⌋₊ ≤ M) :
    ‖∫ x in Set.Ioc (((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ)) (((M : ℕ) : ℝ)),
        ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) *
          (-boundaryLineOnePointRealParam t *
            (((x : ℝ) : ℂ) ^
              (-(boundaryLineOnePointRealParam t + 1))))‖ ≤
      1 + 16 * Real.log (3 + ‖t‖) := by
  exact
    boundaryLineOnePointRealParam_logarithmicPhase_postCutoff_bernoulliRemainder_norm_le_ownerGap
      t ht hM


end
end LFunctions
end Boundary
