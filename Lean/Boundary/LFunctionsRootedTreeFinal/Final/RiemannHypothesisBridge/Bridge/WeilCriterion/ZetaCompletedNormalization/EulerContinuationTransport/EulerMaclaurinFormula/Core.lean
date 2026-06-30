import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ClassicalAnalysis.PuncturedVerticalStrip.Geometry

/-!
# Euler-Maclaurin finite-window core

This file owns the cutoff, finite-window, and polynomial-control lemmas for the
pole-cleared Euler-Maclaurin continuation. The remainder and punctured-strip
continuation proofs live in the owner file.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open scoped Filter Topology
local notation "π" => Real.pi

noncomputable def eulerMaclaurinPoleClearedZetaCutoff
    (z : ℂ) : ℕ :=
  ⌊2 + ‖z‖⌋₊

noncomputable def eulerMaclaurinPoleClearedZetaFinitePart
    (z : ℂ) : ℂ :=
  (z - 1) *
    ∑ n ∈ Finset.Icc 1 (eulerMaclaurinPoleClearedZetaCutoff z),
      1 / (((n : ℕ) : ℂ) ^ z)

noncomputable def eulerMaclaurinPoleClearedZetaMainTerm
    (z : ℂ) : ℂ :=
  ((eulerMaclaurinPoleClearedZetaCutoff z : ℕ) : ℂ) ^ ((1 : ℂ) - z)

noncomputable def eulerMaclaurinPoleClearedZetaEndpointTerm
    (z : ℂ) : ℂ :=
  (-((z - 1) / 2)) *
    (1 / (((eulerMaclaurinPoleClearedZetaCutoff z : ℕ) : ℂ) ^ z))

noncomputable def eulerMaclaurinZetaFinitePart
    (z : ℂ) : ℂ :=
  ∑ n ∈ Finset.Icc 1 (eulerMaclaurinPoleClearedZetaCutoff z),
    1 / (((n : ℕ) : ℂ) ^ z)

noncomputable def eulerMaclaurinZetaMainTerm
    (z : ℂ) : ℂ :=
  (((eulerMaclaurinPoleClearedZetaCutoff z : ℕ) : ℂ) ^ ((1 : ℂ) - z)) /
    (z - 1)

noncomputable def eulerMaclaurinZetaEndpointTerm
    (z : ℂ) : ℂ :=
  (-(1 / 2 : ℂ)) *
    (1 / (((eulerMaclaurinPoleClearedZetaCutoff z : ℕ) : ℂ) ^ z))

theorem eulerMaclaurinPoleClearedZetaCutoff_pos
    (z : ℂ) :
    0 < eulerMaclaurinPoleClearedZetaCutoff z := by
  have hone_le_two : (1 : ℝ) ≤ 2 := by
    calc
      (1 : ℝ) ≤ 1 + 1 := le_add_of_nonneg_right zero_le_one
      _ = 2 := one_add_one_eq_two
  have hone_le : (1 : ℝ) ≤ 2 + ‖z‖ :=
    le_trans hone_le_two (le_add_of_nonneg_right (norm_nonneg z))
  exact (Nat.one_le_floor_iff (2 + ‖z‖)).mpr hone_le

theorem one_le_eulerMaclaurinPoleClearedZetaCutoff_real
    (z : ℂ) :
    (1 : ℝ) ≤ (eulerMaclaurinPoleClearedZetaCutoff z : ℝ) := by
  have hnat :
      ((1 : ℕ) : ℝ) ≤ (eulerMaclaurinPoleClearedZetaCutoff z : ℝ) :=
    Nat.cast_le.mpr
      (Nat.succ_le_iff.mpr (eulerMaclaurinPoleClearedZetaCutoff_pos z))
  exact
    Eq.subst
      (motive := fun x : ℝ => x ≤ (eulerMaclaurinPoleClearedZetaCutoff z : ℝ))
      (Nat.cast_one : ((1 : ℕ) : ℝ) = (1 : ℝ))
      hnat

theorem eulerMaclaurinPoleClearedZetaMainTerm_norm_le_one
    (z : ℂ)
    (hz_one : 1 ≤ z.re) :
    ‖eulerMaclaurinPoleClearedZetaMainTerm z‖ ≤ 1 := by
  unfold eulerMaclaurinPoleClearedZetaMainTerm
  let N : ℕ := eulerMaclaurinPoleClearedZetaCutoff z
  have hN_pos : 0 < N := eulerMaclaurinPoleClearedZetaCutoff_pos z
  have hN_one : (1 : ℝ) ≤ (N : ℝ) :=
    one_le_eulerMaclaurinPoleClearedZetaCutoff_real z
  have hnorm :
      ‖((N : ℕ) : ℂ) ^ ((1 : ℂ) - z)‖ =
        (N : ℝ) ^ (((1 : ℂ) - z).re) :=
    Complex.norm_natCast_cpow_of_pos hN_pos ((1 : ℂ) - z)
  have hre :
      (((1 : ℂ) - z).re) = 1 - z.re := by
    calc
      (((1 : ℂ) - z).re) = (1 : ℂ).re - z.re := Complex.sub_re (1 : ℂ) z
      _ = 1 - z.re := by
        exact congrArg (fun x : ℝ => x - z.re) Complex.one_re
  have hexponent_nonpos : 1 - z.re ≤ 0 := sub_nonpos.mpr hz_one
  have hpow_le :
      (N : ℝ) ^ (((1 : ℂ) - z).re) ≤ 1 :=
    Eq.subst
      (motive := fun e : ℝ => (N : ℝ) ^ e ≤ 1)
      hre.symm
      (Real.rpow_le_one_of_one_le_of_nonpos hN_one hexponent_nonpos)
  exact Eq.subst (motive := fun x : ℝ => x ≤ 1) hnorm.symm hpow_le

theorem eulerMaclaurinPoleClearedZetaEndpointReciprocal_norm_le_one
    (z : ℂ)
    (hz_one : 1 ≤ z.re) :
    ‖1 / (((eulerMaclaurinPoleClearedZetaCutoff z : ℕ) : ℂ) ^ z)‖ ≤ 1 := by
  let N : ℕ := eulerMaclaurinPoleClearedZetaCutoff z
  have hN_pos : 0 < N := eulerMaclaurinPoleClearedZetaCutoff_pos z
  have hN_one : (1 : ℝ) ≤ (N : ℝ) :=
    one_le_eulerMaclaurinPoleClearedZetaCutoff_real z
  have hnorm_cpow :
      ‖((N : ℕ) : ℂ) ^ z‖ = (N : ℝ) ^ z.re :=
    Complex.norm_natCast_cpow_of_pos hN_pos z
  have hz_nonneg : 0 ≤ z.re := le_trans zero_le_one hz_one
  have hpow_one : 1 ≤ (N : ℝ) ^ z.re := Real.one_le_rpow hN_one hz_nonneg
  have hpow_pos : 0 < (N : ℝ) ^ z.re :=
    Real.rpow_pos_of_pos (Nat.cast_pos.mpr hN_pos) z.re
  have hnorm_pos : 0 < ‖((N : ℕ) : ℂ) ^ z‖ :=
    Eq.subst (motive := fun x : ℝ => 0 < x) hnorm_cpow.symm hpow_pos
  have hnorm_one : 1 ≤ ‖((N : ℕ) : ℂ) ^ z‖ :=
    Eq.subst (motive := fun x : ℝ => 1 ≤ x) hnorm_cpow.symm hpow_one
  have hnorm_inv :
      ‖1 / (((N : ℕ) : ℂ) ^ z)‖ =
        1 / ‖((N : ℕ) : ℂ) ^ z‖ := by
    calc
      ‖1 / (((N : ℕ) : ℂ) ^ z)‖ =
          ‖(1 : ℂ)‖ / ‖((N : ℕ) : ℂ) ^ z‖ := by
        exact norm_div (1 : ℂ) (((N : ℕ) : ℂ) ^ z)
      _ = 1 / ‖((N : ℕ) : ℂ) ^ z‖ := by
        exact congrArg (fun x : ℝ => x / ‖((N : ℕ) : ℂ) ^ z‖)
          (norm_one : ‖(1 : ℂ)‖ = (1 : ℝ))
  have hinv_le :
      1 / ‖((N : ℕ) : ℂ) ^ z‖ ≤ 1 :=
    le_trans
      (one_div_le_one_div_of_le zero_lt_one hnorm_one)
      (le_of_eq (div_one (1 : ℝ)))
  exact Eq.subst (motive := fun x : ℝ => x ≤ 1) hnorm_inv.symm hinv_le

theorem eulerMaclaurinPoleClearedZetaFinitePart_summand_norm_le_one
    (z : ℂ)
    {n : ℕ}
    (hn : 1 ≤ n)
    (hz_one : 1 ≤ z.re) :
    ‖1 / (((n : ℕ) : ℂ) ^ z)‖ ≤ 1 := by
  have hn_pos : 0 < n := Nat.lt_of_succ_le hn
  have hn_real_one : (1 : ℝ) ≤ (n : ℝ) := by
    have hnat : ((1 : ℕ) : ℝ) ≤ (n : ℝ) := Nat.cast_le.mpr hn
    exact
      Eq.subst
        (motive := fun x : ℝ => x ≤ (n : ℝ))
        (Nat.cast_one : ((1 : ℕ) : ℝ) = (1 : ℝ))
        hnat
  have hnorm_cpow :
      ‖((n : ℕ) : ℂ) ^ z‖ = (n : ℝ) ^ z.re :=
    Complex.norm_natCast_cpow_of_pos hn_pos z
  have hz_nonneg : 0 ≤ z.re := le_trans zero_le_one hz_one
  have hpow_one : 1 ≤ (n : ℝ) ^ z.re := Real.one_le_rpow hn_real_one hz_nonneg
  have hnorm_one : 1 ≤ ‖((n : ℕ) : ℂ) ^ z‖ :=
    Eq.subst (motive := fun x : ℝ => 1 ≤ x) hnorm_cpow.symm hpow_one
  have hnorm_inv :
      ‖1 / (((n : ℕ) : ℂ) ^ z)‖ =
        1 / ‖((n : ℕ) : ℂ) ^ z‖ := by
    calc
      ‖1 / (((n : ℕ) : ℂ) ^ z)‖ =
          ‖(1 : ℂ)‖ / ‖((n : ℕ) : ℂ) ^ z‖ := by
        exact norm_div (1 : ℂ) (((n : ℕ) : ℂ) ^ z)
      _ = 1 / ‖((n : ℕ) : ℂ) ^ z‖ := by
        exact congrArg (fun x : ℝ => x / ‖((n : ℕ) : ℂ) ^ z‖)
          (norm_one : ‖(1 : ℂ)‖ = (1 : ℝ))
  have hinv_le :
      1 / ‖((n : ℕ) : ℂ) ^ z‖ ≤ 1 :=
    le_trans
      (one_div_le_one_div_of_le zero_lt_one hnorm_one)
      (le_of_eq (div_one (1 : ℝ)))
  exact Eq.subst (motive := fun x : ℝ => x ≤ 1) hnorm_inv.symm hinv_le

theorem eulerMaclaurinPoleClearedZetaFinitePart_sum_norm_le_card
    (z : ℂ)
    (hz_one : 1 ≤ z.re) :
    ‖∑ n ∈ Finset.Icc 1 (eulerMaclaurinPoleClearedZetaCutoff z),
        1 / (((n : ℕ) : ℂ) ^ z)‖ ≤
      ((Finset.Icc 1 (eulerMaclaurinPoleClearedZetaCutoff z)).card : ℝ) := by
  have hsum_norm :
      ‖∑ n ∈ Finset.Icc 1 (eulerMaclaurinPoleClearedZetaCutoff z),
          1 / (((n : ℕ) : ℂ) ^ z)‖ ≤
        ∑ n ∈ Finset.Icc 1 (eulerMaclaurinPoleClearedZetaCutoff z),
          ‖1 / (((n : ℕ) : ℂ) ^ z)‖ :=
    norm_sum_le _ _
  have hterms :
      (∑ n ∈ Finset.Icc 1 (eulerMaclaurinPoleClearedZetaCutoff z),
          ‖1 / (((n : ℕ) : ℂ) ^ z)‖) ≤
        ∑ n ∈ Finset.Icc 1 (eulerMaclaurinPoleClearedZetaCutoff z), (1 : ℝ) := by
    exact Finset.sum_le_sum
      (fun n hn =>
        eulerMaclaurinPoleClearedZetaFinitePart_summand_norm_le_one
          z (Finset.mem_Icc.mp hn).1 hz_one)
  have hcard :
      (∑ n ∈ Finset.Icc 1 (eulerMaclaurinPoleClearedZetaCutoff z), (1 : ℝ)) =
        ((Finset.Icc 1 (eulerMaclaurinPoleClearedZetaCutoff z)).card : ℝ) :=
    calc
      (∑ n ∈ Finset.Icc 1 (eulerMaclaurinPoleClearedZetaCutoff z), (1 : ℝ)) =
          (Finset.Icc 1 (eulerMaclaurinPoleClearedZetaCutoff z)).card • (1 : ℝ) := by
        exact Finset.sum_const (1 : ℝ)
      _ = ((Finset.Icc 1 (eulerMaclaurinPoleClearedZetaCutoff z)).card : ℝ) := by
        calc
          (Finset.Icc 1 (eulerMaclaurinPoleClearedZetaCutoff z)).card • (1 : ℝ) =
              ((Finset.Icc 1 (eulerMaclaurinPoleClearedZetaCutoff z)).card : ℝ) * 1 := by
            exact
              nsmul_eq_mul
                (Finset.Icc 1 (eulerMaclaurinPoleClearedZetaCutoff z)).card
                (1 : ℝ)
          _ = ((Finset.Icc 1 (eulerMaclaurinPoleClearedZetaCutoff z)).card : ℝ) := by
            exact mul_one _
  exact le_trans hsum_norm (le_trans hterms (le_of_eq hcard))

theorem eulerMaclaurinPoleClearedZetaFinitePart_card_le_three_mul_height
    (z : ℂ) :
    ((Finset.Icc 1 (eulerMaclaurinPoleClearedZetaCutoff z)).card : ℝ) ≤
      3 * (1 + ‖z‖) := by
  let N : ℕ := eulerMaclaurinPoleClearedZetaCutoff z
  have hsubset : Finset.Icc 1 N ⊆ Finset.Icc 0 N := by
    intro n hn
    exact Finset.mem_Icc.mpr ⟨Nat.zero_le n, (Finset.mem_Icc.mp hn).2⟩
  have hcard_nat :
      (Finset.Icc 1 N).card ≤ (Finset.Icc 0 N).card :=
    Finset.card_le_card hsubset
  have hcard_zero : (Finset.Icc 0 N).card = N + 1 := by
    calc
      (Finset.Icc 0 N).card = N + 1 - 0 := Nat.card_Icc 0 N
      _ = N + 1 := Nat.sub_zero (N + 1)
  have hcard_le_nat : ((Finset.Icc 1 N).card : ℝ) ≤ (N + 1 : ℝ) := by
    have hcast :
        ((Finset.Icc 1 N).card : ℝ) ≤ ((N + 1 : ℕ) : ℝ) :=
      Nat.cast_le.mpr (le_trans hcard_nat (le_of_eq hcard_zero))
    have htarget : ((N + 1 : ℕ) : ℝ) = (N : ℝ) + 1 := by
      exact
        Eq.trans
          (Nat.cast_add N 1)
          (congrArg (fun x : ℝ => (N : ℝ) + x) Nat.cast_one)
    exact Eq.subst (motive := fun x : ℝ => ((Finset.Icc 1 N).card : ℝ) ≤ x) htarget hcast
  have hN_le : (N : ℝ) ≤ 2 + ‖z‖ := by
    unfold N
    unfold eulerMaclaurinPoleClearedZetaCutoff
    have hnonneg : 0 ≤ 2 + ‖z‖ :=
      le_trans zero_le_one
        (le_trans (by
          calc
            (1 : ℝ) ≤ 2 := one_le_two) (le_add_of_nonneg_right (norm_nonneg z)))
    exact Nat.floor_le hnonneg
  have hN_add_le : (N + 1 : ℝ) ≤ 3 + ‖z‖ := by
    calc
      (N + 1 : ℝ) = (N : ℝ) + 1 := by
        rfl
      _ ≤ (2 + ‖z‖) + 1 :=
        add_le_add_right hN_le 1
      _ = 3 + ‖z‖ := by
        calc
          (2 + ‖z‖) + 1 = (2 + 1) + ‖z‖ := by
            exact add_right_comm 2 ‖z‖ 1
          _ = 3 + ‖z‖ := by
            exact congrArg (fun x : ℝ => x + ‖z‖) two_add_one_eq_three
  have hthree_height : 3 + ‖z‖ ≤ 3 * (1 + ‖z‖) := by
    calc
      3 + ‖z‖ ≤ 3 + 3 * ‖z‖ :=
        add_le_add_left
          (calc
            ‖z‖ ≤ 3 * ‖z‖ := by
              have hone_le_three : (1 : ℝ) ≤ 3 :=
                le_trans
                  (show (1 : ℝ) ≤ 2 from one_le_two)
                  (le_of_lt (Nat.cast_lt.mpr (Nat.lt_succ_self 2)))
              exact le_mul_of_one_le_left (norm_nonneg z) hone_le_three)
          3
      _ = 3 * (1 + ‖z‖) := by
        calc
          3 + 3 * ‖z‖ = 3 * 1 + 3 * ‖z‖ := by
            exact congrArg (fun x : ℝ => x + 3 * ‖z‖) (mul_one 3).symm
          _ = 3 * (1 + ‖z‖) := by
            exact (mul_add 3 1 ‖z‖).symm
  exact le_trans hcard_le_nat (le_trans hN_add_le hthree_height)

theorem eulerMaclaurinPoleClearedZetaFinitePart_poleFactor_norm_le_height
    (z : ℂ) :
    ‖z - 1‖ ≤ 1 + ‖z‖ := by
  calc
    ‖z - 1‖ ≤ ‖z‖ + ‖(1 : ℂ)‖ := norm_sub_le z (1 : ℂ)
    _ = ‖z‖ + 1 := by
      exact congrArg (fun x : ℝ => ‖z‖ + x) (norm_one : ‖(1 : ℂ)‖ = (1 : ℝ))
    _ = 1 + ‖z‖ := by
      exact add_comm ‖z‖ 1

theorem eulerMaclaurinPoleClearedZetaFinitePart_sum_cardinality_polynomial_bound :
    ∃ C : ℝ, ∃ m : ℕ,
      0 < C ∧
      ∀ z : ℂ,
        1 ≤ z.re →
        z.re ≤ 2 →
        ‖eulerMaclaurinPoleClearedZetaFinitePart z‖ ≤ C * (1 + ‖z‖) ^ m := by
  refine ⟨3, 2, ?_, ?_⟩
  · exact
      lt_of_lt_of_le
        (zero_lt_one : (0 : ℝ) < 1)
        (le_trans
          (show (1 : ℝ) ≤ 2 from one_le_two)
          (le_of_lt (Nat.cast_lt.mpr (Nat.lt_succ_self 2))))
  intro z hz_one _hz_two
  unfold eulerMaclaurinPoleClearedZetaFinitePart
  let H : ℝ := 1 + ‖z‖
  have hH_nonneg : 0 ≤ H := le_trans zero_le_one (le_add_of_nonneg_right (norm_nonneg z))
  have hpole : ‖z - 1‖ ≤ H :=
    eulerMaclaurinPoleClearedZetaFinitePart_poleFactor_norm_le_height z
  have hsum_card :
      ‖∑ n ∈ Finset.Icc 1 (eulerMaclaurinPoleClearedZetaCutoff z),
          1 / (((n : ℕ) : ℂ) ^ z)‖ ≤
        ((Finset.Icc 1 (eulerMaclaurinPoleClearedZetaCutoff z)).card : ℝ) :=
    eulerMaclaurinPoleClearedZetaFinitePart_sum_norm_le_card z hz_one
  have hcard :
      ((Finset.Icc 1 (eulerMaclaurinPoleClearedZetaCutoff z)).card : ℝ) ≤
        3 * H :=
    eulerMaclaurinPoleClearedZetaFinitePart_card_le_three_mul_height z
  have hsum : ‖∑ n ∈ Finset.Icc 1 (eulerMaclaurinPoleClearedZetaCutoff z),
          1 / (((n : ℕ) : ℂ) ^ z)‖ ≤ 3 * H :=
    le_trans hsum_card hcard
  have hprod :
      ‖(z - 1) *
          ∑ n ∈ Finset.Icc 1 (eulerMaclaurinPoleClearedZetaCutoff z),
            1 / (((n : ℕ) : ℂ) ^ z)‖ ≤
        H * (3 * H) := by
    calc
      ‖(z - 1) *
          ∑ n ∈ Finset.Icc 1 (eulerMaclaurinPoleClearedZetaCutoff z),
            1 / (((n : ℕ) : ℂ) ^ z)‖ =
          ‖z - 1‖ *
            ‖∑ n ∈ Finset.Icc 1 (eulerMaclaurinPoleClearedZetaCutoff z),
              1 / (((n : ℕ) : ℂ) ^ z)‖ := by
        exact norm_mul (z - 1)
          (∑ n ∈ Finset.Icc 1 (eulerMaclaurinPoleClearedZetaCutoff z),
            1 / (((n : ℕ) : ℂ) ^ z))
      _ ≤ H * (3 * H) :=
        mul_le_mul hpole hsum
          (norm_nonneg
            (∑ n ∈ Finset.Icc 1 (eulerMaclaurinPoleClearedZetaCutoff z),
              1 / (((n : ℕ) : ℂ) ^ z)))
          hH_nonneg
  have hcollapse : H * (3 * H) = 3 * H ^ (2 : ℕ) := by
    calc
      H * (3 * H) = (H * 3) * H := by
        exact (mul_assoc H 3 H).symm
      _ = (3 * H) * H := by
        exact congrArg (fun x : ℝ => x * H) (mul_comm H 3)
      _ = 3 * (H * H) := by
        exact mul_assoc 3 H H
      _ = 3 * H ^ (2 : ℕ) := by
        exact congrArg (fun x : ℝ => 3 * x) (pow_two H).symm
  have htarget : 3 * H ^ (2 : ℕ) = 3 * (1 + ‖z‖) ^ (2 : ℕ) := rfl
  exact le_trans hprod (le_of_eq (hcollapse.trans htarget))

end
end LFunctions
end Boundary
