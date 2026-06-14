import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ClassicalAnalysis.PuncturedVerticalStrip.Geometry
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalization.EulerContinuationTransport.FiniteOrderPL.Owner

/-!
# Euler-Maclaurin formula and punctured-strip continuation

This file is a sequential owner sublayer split out of
`ZetaCompletedNormalization.EulerContinuationTransport.Owner`.  Declaration order is preserved.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open scoped Filter Topology
local notation "π" => Real.pi

noncomputable def eulerMaclaurinPoleClearedZetaCutoff
    (z : ℂ) : ℕ :=
  ⌊2 + ‖z‖⌋₊

/-- Finite Dirichlet-polynomial part of the Euler-Maclaurin continuation for
`ζ(s)`, after multiplying by the pole-clearing factor `s - 1`. -/
noncomputable def eulerMaclaurinPoleClearedZetaFinitePart
    (z : ℂ) : ℂ :=
  (z - 1) *
    ∑ n ∈ Finset.Icc 1 (eulerMaclaurinPoleClearedZetaCutoff z),
      1 / (((n : ℕ) : ℂ) ^ z)

/-- Pole-cancelling main term `(s - 1) · N^(1-s)/(s-1) = N^(1-s)` in the
Euler-Maclaurin continuation. -/
noncomputable def eulerMaclaurinPoleClearedZetaMainTerm
    (z : ℂ) : ℂ :=
  ((eulerMaclaurinPoleClearedZetaCutoff z : ℕ) : ℂ) ^ ((1 : ℂ) - z)

/-- Endpoint correction in the pole-cleared Euler-Maclaurin continuation. -/
noncomputable def eulerMaclaurinPoleClearedZetaEndpointTerm
    (z : ℂ) : ℂ :=
  ((z - 1) / 2) *
    (1 / (((eulerMaclaurinPoleClearedZetaCutoff z : ℕ) : ℂ) ^ z))

/-- Finite Dirichlet-polynomial part in the raw first-order Euler-Maclaurin
formula for `ζ(s)` at the owner cutoff. -/
noncomputable def eulerMaclaurinZetaFinitePart
    (z : ℂ) : ℂ :=
  ∑ n ∈ Finset.Icc 1 (eulerMaclaurinPoleClearedZetaCutoff z),
    1 / (((n : ℕ) : ℂ) ^ z)

/-- Integral main term `N^(1-s)/(s-1)` in the raw Euler-Maclaurin formula
away from the pole. -/
noncomputable def eulerMaclaurinZetaMainTerm
    (z : ℂ) : ℂ :=
  (((eulerMaclaurinPoleClearedZetaCutoff z : ℕ) : ℂ) ^ ((1 : ℂ) - z)) /
    (z - 1)

/-- Endpoint correction `1/2 · N^{-s}` in the raw Euler-Maclaurin formula. -/
noncomputable def eulerMaclaurinZetaEndpointTerm
    (z : ℂ) : ℂ :=
  (1 / 2 : ℂ) *
    (1 / (((eulerMaclaurinPoleClearedZetaCutoff z : ℕ) : ℂ) ^ z))

/-- The bounded-strip Euler-Maclaurin cutoff is always at least one. -/
theorem eulerMaclaurinPoleClearedZetaCutoff_pos
    (z : ℂ) :
    0 < eulerMaclaurinPoleClearedZetaCutoff z := by
  have hone_le_two : (1 : ℝ) ≤ 2 := by
    calc
      (1 : ℝ) ≤ 1 + 1 :=
        le_add_of_nonneg_right zero_le_one
      _ = 2 := rfl
  have hone_le : (1 : ℝ) ≤ 2 + ‖z‖ :=
    le_trans hone_le_two (le_add_of_nonneg_right (norm_nonneg z))
  exact (Nat.one_le_floor_iff zero_lt_one).mpr hone_le

/-- The bounded-strip Euler-Maclaurin cutoff is at least one as a real number. -/
theorem one_le_eulerMaclaurinPoleClearedZetaCutoff_real
    (z : ℂ) :
    (1 : ℝ) ≤ (eulerMaclaurinPoleClearedZetaCutoff z : ℝ) :=
  Nat.cast_le.mpr (Nat.succ_le_iff.mpr (eulerMaclaurinPoleClearedZetaCutoff_pos z))

/-- The cutoff main Euler-Maclaurin power has norm at most one on `1 ≤ Re z`. -/
theorem eulerMaclaurinPoleClearedZetaMainTerm_norm_le_one
    (z : ℂ)
    (hz_one : 1 ≤ z.re) :
    ‖eulerMaclaurinPoleClearedZetaMainTerm z‖ ≤ 1 := by
  unfold eulerMaclaurinPoleClearedZetaMainTerm
  let N : ℕ := eulerMaclaurinPoleClearedZetaCutoff z
  have hN_pos : 0 < N :=
    eulerMaclaurinPoleClearedZetaCutoff_pos z
  have hN_one : (1 : ℝ) ≤ (N : ℝ) :=
    one_le_eulerMaclaurinPoleClearedZetaCutoff_real z
  have hnorm :
      ‖((N : ℕ) : ℂ) ^ ((1 : ℂ) - z)‖ =
        (N : ℝ) ^ (((1 : ℂ) - z).re) :=
    Complex.norm_natCast_cpow_of_pos hN_pos ((1 : ℂ) - z)
  have hre :
      (((1 : ℂ) - z).re) = 1 - z.re := by
    calc
      (((1 : ℂ) - z).re) = (1 : ℂ).re - z.re :=
        Complex.sub_re (1 : ℂ) z
      _ = 1 - z.re := by
        exact congrArg (fun x : ℝ => x - z.re) Complex.one_re
  have hexponent_nonpos : 1 - z.re ≤ 0 :=
    sub_nonpos.mpr hz_one
  have hpow_le :
      (N : ℝ) ^ (((1 : ℂ) - z).re) ≤ 1 :=
    Eq.subst
      (motive := fun e : ℝ => (N : ℝ) ^ e ≤ 1)
      hre.symm
      (Real.rpow_le_one_of_one_le_of_nonpos hN_one hexponent_nonpos)
  exact Eq.subst
    (motive := fun x : ℝ => x ≤ 1)
    hnorm.symm
    hpow_le

/-- The reciprocal cutoff power in the endpoint correction is bounded by one
on `1 ≤ Re z`. -/
theorem eulerMaclaurinPoleClearedZetaEndpointReciprocal_norm_le_one
    (z : ℂ)
    (hz_one : 1 ≤ z.re) :
    ‖1 / (((eulerMaclaurinPoleClearedZetaCutoff z : ℕ) : ℂ) ^ z)‖ ≤ 1 := by
  let N : ℕ := eulerMaclaurinPoleClearedZetaCutoff z
  have hN_pos : 0 < N :=
    eulerMaclaurinPoleClearedZetaCutoff_pos z
  have hN_one : (1 : ℝ) ≤ (N : ℝ) :=
    one_le_eulerMaclaurinPoleClearedZetaCutoff_real z
  have hnorm_cpow :
      ‖((N : ℕ) : ℂ) ^ z‖ = (N : ℝ) ^ z.re :=
    Complex.norm_natCast_cpow_of_pos hN_pos z
  have hpow_one : 1 ≤ (N : ℝ) ^ z.re :=
    Real.one_le_rpow hN_one hz_one
  have hpow_pos : 0 < (N : ℝ) ^ z.re :=
    Real.rpow_pos_of_pos (Nat.cast_pos.mpr hN_pos) z.re
  have hnorm_pos : 0 < ‖((N : ℕ) : ℂ) ^ z‖ :=
    Eq.subst
      (motive := fun x : ℝ => 0 < x)
      hnorm_cpow.symm
      hpow_pos
  have hnorm_one : 1 ≤ ‖((N : ℕ) : ℂ) ^ z‖ :=
    Eq.subst
      (motive := fun x : ℝ => 1 ≤ x)
      hnorm_cpow.symm
      hpow_one
  have hnorm_inv :
      ‖1 / (((N : ℕ) : ℂ) ^ z)‖ =
        1 / ‖((N : ℕ) : ℂ) ^ z‖ := by
    calc
      ‖1 / (((N : ℕ) : ℂ) ^ z)‖ =
          ‖(1 : ℂ)‖ / ‖((N : ℕ) : ℂ) ^ z‖ := by
        exact norm_div (1 : ℂ) (((N : ℕ) : ℂ) ^ z)
      _ = 1 / ‖((N : ℕ) : ℂ) ^ z‖ := by
        exact congrArg
          (fun x : ℝ => x / ‖((N : ℕ) : ℂ) ^ z‖)
          (norm_one : ‖(1 : ℂ)‖ = (1 : ℝ))
  have hinv_le :
      1 / ‖((N : ℕ) : ℂ) ^ z‖ ≤ 1 :=
    le_trans
      (one_div_le_one_div_of_le zero_lt_one hnorm_one)
      (le_of_eq (div_one (1 : ℝ)))
  exact Eq.subst
    (motive := fun x : ℝ => x ≤ 1)
    hnorm_inv.symm
    hinv_le

/-- Each finite-window Euler-Maclaurin Dirichlet summand has norm at most one
on the strip `1 ≤ Re z`. -/
theorem eulerMaclaurinPoleClearedZetaFinitePart_summand_norm_le_one
    (z : ℂ)
    {n : ℕ}
    (hn : 1 ≤ n)
    (hz_one : 1 ≤ z.re) :
    ‖1 / (((n : ℕ) : ℂ) ^ z)‖ ≤ 1 := by
  have hn_pos : 0 < n :=
    Nat.lt_of_succ_le hn
  have hn_real_one : (1 : ℝ) ≤ (n : ℝ) :=
    Nat.cast_le.mpr hn
  have hnorm_cpow :
      ‖((n : ℕ) : ℂ) ^ z‖ = (n : ℝ) ^ z.re :=
    Complex.norm_natCast_cpow_of_pos hn_pos z
  have hpow_one : 1 ≤ (n : ℝ) ^ z.re :=
    Real.one_le_rpow hn_real_one hz_one
  have hnorm_one : 1 ≤ ‖((n : ℕ) : ℂ) ^ z‖ :=
    Eq.subst
      (motive := fun x : ℝ => 1 ≤ x)
      hnorm_cpow.symm
      hpow_one
  have hnorm_inv :
      ‖1 / (((n : ℕ) : ℂ) ^ z)‖ =
        1 / ‖((n : ℕ) : ℂ) ^ z‖ := by
    calc
      ‖1 / (((n : ℕ) : ℂ) ^ z)‖ =
          ‖(1 : ℂ)‖ / ‖((n : ℕ) : ℂ) ^ z‖ := by
        exact norm_div (1 : ℂ) (((n : ℕ) : ℂ) ^ z)
      _ = 1 / ‖((n : ℕ) : ℂ) ^ z‖ := by
        exact congrArg
          (fun x : ℝ => x / ‖((n : ℕ) : ℂ) ^ z‖)
          (norm_one : ‖(1 : ℂ)‖ = (1 : ℝ))
  have hinv_le :
      1 / ‖((n : ℕ) : ℂ) ^ z‖ ≤ 1 :=
    le_trans
      (one_div_le_one_div_of_le zero_lt_one hnorm_one)
      (le_of_eq (div_one (1 : ℝ)))
  exact Eq.subst
    (motive := fun x : ℝ => x ≤ 1)
    hnorm_inv.symm
    hinv_le

/-- The norm of the finite Euler-Maclaurin Dirichlet window is bounded by its
cardinality. -/
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
    Finset.sum_const_nat (Finset.Icc 1 (eulerMaclaurinPoleClearedZetaCutoff z)) 1
  exact le_trans hsum_norm (le_trans hterms (le_of_eq hcard))

/-- The finite Euler-Maclaurin window cardinality is controlled by the
height-comparable cutoff. -/
theorem eulerMaclaurinPoleClearedZetaFinitePart_card_le_three_mul_height
    (z : ℂ) :
    ((Finset.Icc 1 (eulerMaclaurinPoleClearedZetaCutoff z)).card : ℝ) ≤
      3 * (1 + ‖z‖) := by
  let N : ℕ := eulerMaclaurinPoleClearedZetaCutoff z
  have hsubset : Finset.Icc 1 N ⊆ Finset.Icc 0 N := by
    intro n hn
    exact ⟨Nat.zero_le n, (Finset.mem_Icc.mp hn).2⟩
  have hcard_nat :
      (Finset.Icc 1 N).card ≤ (Finset.Icc 0 N).card :=
    Finset.card_le_card hsubset
  have hcard_zero :
      (Finset.Icc 0 N).card = N + 1 :=
    Finset.card_Icc 0 N
  have hcard_le_nat :
      ((Finset.Icc 1 N).card : ℝ) ≤ (N + 1 : ℝ) := by
    exact Nat.cast_le.mpr
      (le_trans hcard_nat (le_of_eq hcard_zero))
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
        exact Nat.cast_add N 1
      _ ≤ (2 + ‖z‖) + 1 :=
        add_le_add_right hN_le 1
      _ = 3 + ‖z‖ := by
        calc
          (2 + ‖z‖) + 1 = (2 + 1) + ‖z‖ := by
            exact add_right_comm 2 ‖z‖ 1
          _ = 3 + ‖z‖ := rfl
  have hthree_height : 3 + ‖z‖ ≤ 3 * (1 + ‖z‖) := by
    calc
      3 + ‖z‖ ≤ 3 + 3 * ‖z‖ :=
        add_le_add_left
          (calc
            ‖z‖ ≤ 3 * ‖z‖ := by
              exact le_mul_of_one_le_left (norm_nonneg z) one_le_three)
          3
      _ = 3 * (1 + ‖z‖) := by
        calc
          3 + 3 * ‖z‖ = 3 * 1 + 3 * ‖z‖ := by
            exact congrArg (fun x : ℝ => x + 3 * ‖z‖) (mul_one 3).symm
          _ = 3 * (1 + ‖z‖) := by
            exact (mul_add 3 1 ‖z‖).symm
  exact le_trans hcard_le_nat (le_trans hN_add_le hthree_height)

/-- The pole-clearing factor in the finite Euler-Maclaurin part contributes at
most one factor of the height envelope. -/
theorem eulerMaclaurinPoleClearedZetaFinitePart_poleFactor_norm_le_height
    (z : ℂ) :
    ‖z - 1‖ ≤ 1 + ‖z‖ := by
  calc
    ‖z - 1‖ ≤ ‖z‖ + ‖(1 : ℂ)‖ :=
      norm_sub_le z (1 : ℂ)
    _ = ‖z‖ + 1 := by
      exact congrArg (fun x : ℝ => ‖z‖ + x) (norm_one : ‖(1 : ℂ)‖ = (1 : ℝ))
    _ = 1 + ‖z‖ := by
      exact add_comm ‖z‖ 1

/-- Uniform polynomial control for the finite Euler-Maclaurin Dirichlet window.

This is the canonical finite-window estimate: on `1 ≤ Re z ≤ 2`, each summand
`n^{-z}` has norm at most `1` for `1 ≤ n`, the window cardinality is controlled
by the height-comparable cutoff `⌊2 + ‖z‖⌋₊`, and the pole-clearing factor
`z - 1` contributes only one more power of `1 + ‖z‖`. -/
theorem eulerMaclaurinPoleClearedZetaFinitePart_sum_cardinality_polynomial_bound :
    ∃ C : ℝ, ∃ m : ℕ,
      0 < C ∧
      ∀ z : ℂ,
        1 ≤ z.re →
        z.re ≤ 2 →
        ‖eulerMaclaurinPoleClearedZetaFinitePart z‖ ≤ C * (1 + ‖z‖) ^ m := by
  refine ⟨3, 2, zero_lt_three, ?_⟩
  intro z hz_one _hz_two
  unfold eulerMaclaurinPoleClearedZetaFinitePart
  let H : ℝ := 1 + ‖z‖
  have hH_nonneg : 0 ≤ H :=
    le_trans zero_le_one (le_add_of_nonneg_right (norm_nonneg z))
  have hpole :
      ‖z - 1‖ ≤ H :=
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
        exact mul_assoc H 3 H
      _ = (3 * H) * H := by
        exact congrArg (fun x : ℝ => x * H) (mul_comm H 3)
      _ = 3 * (H * H) := by
        exact (mul_assoc 3 H H).symm
      _ = 3 * H ^ (2 : ℕ) := by
        exact congrArg (fun x : ℝ => 3 * x) (pow_two H).symm
  have htarget : 3 * H ^ (2 : ℕ) = 3 * (1 + ‖z‖) ^ (2 : ℕ) := rfl
  exact le_trans hprod (le_of_eq (hcollapse.trans htarget))

/-- Bernoulli-periodic remainder term in the pole-cleared Euler-Maclaurin
continuation.

This name isolates the standard remainder estimate.  The exact analytic
construction is the usual `B₁({x})` integral after multiplying by `s - 1`; the
owner theorem below records the formula identity and the polynomial bound used
by the finite-order chain. -/
noncomputable def eulerMaclaurinPoleClearedZetaRemainderTerm
    (z : ℂ) : ℂ :=
  poleClearedRiemannZeta z -
    (eulerMaclaurinPoleClearedZetaFinitePart z +
      eulerMaclaurinPoleClearedZetaMainTerm z +
      eulerMaclaurinPoleClearedZetaEndpointTerm z)

/-- First periodic Bernoulli factor in the Euler-Maclaurin zeta remainder.

This is the sawtooth `B₁({x}) = {x} - 1/2`, written with `Int.fract`. -/
noncomputable def eulerMaclaurinFirstPeriodicBernoulli
    (x : ℝ) : ℝ :=
  Int.fract x - 1 / 2

/-- The bare Bernoulli-periodic tail integral in the Euler-Maclaurin zeta
remainder, before multiplication by `-(z - 1) z`. -/
noncomputable def eulerMaclaurinPoleClearedZetaBernoulliIntegralCore
    (z : ℂ) : ℂ :=
  ∫ x in Set.Ioi (((eulerMaclaurinPoleClearedZetaCutoff z : ℕ) : ℝ)),
    ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) *
      (((x : ℝ) : ℂ) ^ (-(z + 1)))

/-- Raw first-order Euler-Maclaurin Bernoulli-periodic remainder
`-s ∫_N^∞ B₁({x}) x^{-s-1} dx`. -/
noncomputable def eulerMaclaurinZetaBernoulliIntegralRemainder
    (z : ℂ) : ℂ :=
  -z * eulerMaclaurinPoleClearedZetaBernoulliIntegralCore z

/-- Explicit Bernoulli-periodic integral remainder for the pole-cleared zeta
Euler-Maclaurin formula.

With `N = ⌊2 + ‖z‖⌋₊`, this is
`-(z - 1) z ∫_N^∞ B₁({x}) x^{-z-1} dx`, the standard first-order
Euler-Maclaurin remainder after multiplying by the pole-clearing factor. -/
noncomputable def eulerMaclaurinPoleClearedZetaBernoulliIntegralRemainder
    (z : ℂ) : ℂ :=
  -((z - 1) * z) *
    eulerMaclaurinPoleClearedZetaBernoulliIntegralCore z

/-- The pole-cleared finite Euler-Maclaurin term is `(s - 1)` times the raw
finite Dirichlet window. -/
theorem eulerMaclaurinPoleClearedZetaFinitePart_eq_mul_raw
    (z : ℂ) :
    eulerMaclaurinPoleClearedZetaFinitePart z =
      (z - 1) * eulerMaclaurinZetaFinitePart z := by
  unfold eulerMaclaurinPoleClearedZetaFinitePart
  unfold eulerMaclaurinZetaFinitePart
  rfl

/-- Away from `s = 1`, the pole-cleared main term is `(s - 1)` times the raw
Euler-Maclaurin integral main term. -/
theorem eulerMaclaurinPoleClearedZetaMainTerm_eq_mul_raw
    {z : ℂ}
    (hz_ne_one : z ≠ 1) :
    eulerMaclaurinPoleClearedZetaMainTerm z =
      (z - 1) * eulerMaclaurinZetaMainTerm z := by
  unfold eulerMaclaurinPoleClearedZetaMainTerm
  unfold eulerMaclaurinZetaMainTerm
  let A : ℂ :=
    ((eulerMaclaurinPoleClearedZetaCutoff z : ℕ) : ℂ) ^ ((1 : ℂ) - z)
  have hden_ne : z - 1 ≠ 0 :=
    sub_ne_zero.mpr hz_ne_one
  calc
    A = A := rfl
    _ = (z - 1) * (A / (z - 1)) := by
      exact (mul_div_cancel₀ A hden_ne).symm

/-- The pole-cleared endpoint correction is `(s - 1)` times the raw endpoint
correction. -/
theorem eulerMaclaurinPoleClearedZetaEndpointTerm_eq_mul_raw
    (z : ℂ) :
    eulerMaclaurinPoleClearedZetaEndpointTerm z =
      (z - 1) * eulerMaclaurinZetaEndpointTerm z := by
  unfold eulerMaclaurinPoleClearedZetaEndpointTerm
  unfold eulerMaclaurinZetaEndpointTerm
  let U : ℂ :=
    1 / (((eulerMaclaurinPoleClearedZetaCutoff z : ℕ) : ℂ) ^ z)
  calc
    ((z - 1) / 2) * U =
        ((z - 1) * (1 / 2 : ℂ)) * U := by
      exact congrArg (fun w : ℂ => w * U) (div_eq_mul_inv (z - 1) 2)
    _ = (z - 1) * ((1 / 2 : ℂ) * U) := by
      exact (mul_assoc (z - 1) (1 / 2 : ℂ) U).symm

/-- The pole-cleared Bernoulli remainder is `(s - 1)` times the raw
Euler-Maclaurin Bernoulli remainder. -/
theorem eulerMaclaurinPoleClearedZetaBernoulliIntegralRemainder_eq_mul_raw
    (z : ℂ) :
    eulerMaclaurinPoleClearedZetaBernoulliIntegralRemainder z =
      (z - 1) * eulerMaclaurinZetaBernoulliIntegralRemainder z := by
  unfold eulerMaclaurinPoleClearedZetaBernoulliIntegralRemainder
  unfold eulerMaclaurinZetaBernoulliIntegralRemainder
  let I : ℂ := eulerMaclaurinPoleClearedZetaBernoulliIntegralCore z
  calc
    -((z - 1) * z) * I =
        ((z - 1) * -z) * I := by
      exact congrArg (fun w : ℂ => w * I) (mul_neg (z - 1) z).symm
    _ = (z - 1) * (-z * I) := by
      exact (mul_assoc (z - 1) (-z) I).symm

/-- Adding back a subtracted term. -/
theorem complex_eq_add_of_sub_eq
    {A B C : ℂ}
    (h : A - B = C) :
    A = B + C := by
  have hcancel : B + (A - B) = A := by
    calc
      B + (A - B) = B + (A + -B) := by
        exact congrArg (fun w : ℂ => B + w) (sub_eq_add_neg A B)
      _ = B + A + -B := by
        exact (add_assoc B A (-B)).symm
      _ = A + B + -B := by
        exact congrArg (fun w : ℂ => w + -B) (add_comm B A)
      _ = A + (B + -B) := by
        exact add_assoc A B (-B)
      _ = A + 0 := by
        exact congrArg (fun w : ℂ => A + w) (add_neg_cancel B)
      _ = A := by
        exact add_zero A
  calc
    A = B + (A - B) := by
      exact hcancel.symm
    _ = B + C := by
      exact congrArg (fun w : ℂ => B + w) h

/-- The zeroth Dirichlet monomial vanishes in the convergent half-plane. -/
theorem riemannZeta_dirichletTerm_zero_of_one_lt_re
    {z : ℂ}
    (hz : 1 < z.re) :
    (1 : ℂ) / ((0 : ℂ) ^ z) = 0 := by
  have hz_ne_zero : z ≠ 0 :=
    Complex.ne_zero_of_one_lt_re hz
  have hpow_zero : (0 : ℂ) ^ z = 0 :=
    (cpow_eq_zero_iff).mpr ⟨rfl, hz_ne_zero⟩
  calc
    (1 : ℂ) / ((0 : ℂ) ^ z) = (1 : ℂ) / 0 := by
      exact congrArg (fun w : ℂ => (1 : ℂ) / w) hpow_zero
    _ = 0 := by
      exact div_zero (1 : ℂ)

/-- In the convergent half-plane, removing the finite Dirichlet window from
`ζ(s)` leaves the post-cutoff Dirichlet tail as a `HasSum`. -/
theorem eulerMaclaurin_riemannZeta_halfPlane_finite_split_tail_hasSum
    (z : ℂ)
    (hz : 1 < z.re) :
    HasSum
      (fun n : ℕ =>
        if eulerMaclaurinPoleClearedZetaCutoff z < n then
          (1 : ℂ) / ((n : ℂ) ^ z)
        else
          0)
      (riemannZeta z - eulerMaclaurinZetaFinitePart z) := by
  let N : ℕ := eulerMaclaurinPoleClearedZetaCutoff z
  let f : ℕ → ℂ := fun n : ℕ => (1 : ℂ) / ((n : ℂ) ^ z)
  have hf_summable : Summable f :=
    (Complex.summable_one_div_nat_cpow (p := z)).mpr hz
  have hζ_eq : riemannZeta z = ∑' n : ℕ, f n :=
    zeta_eq_tsum_one_div_nat_cpow hz
  have hf_has_tsum : HasSum f (∑' n : ℕ, f n) :=
    hf_summable.hasSum
  have hf_has_zeta : HasSum f (riemannZeta z) :=
    Eq.subst
      (motive := fun S : ℂ => HasSum f S)
      hζ_eq.symm
      hf_has_tsum
  have htail_compl :
      HasSum
        (fun x : {n : ℕ // n ∉ Finset.Icc 1 N} => f x)
        (riemannZeta z - ∑ n ∈ Finset.Icc 1 N, f n) :=
    ((Finset.Icc 1 N).hasSum_iff_compl).mp hf_has_zeta
  have htail_indicator :
      HasSum
        ({n : ℕ | n ∉ Finset.Icc 1 N}.indicator f)
        (riemannZeta z - ∑ n ∈ Finset.Icc 1 N, f n) := by
    exact
      (hasSum_subtype_iff_indicator
        (s := {n : ℕ | n ∉ Finset.Icc 1 N})
        (f := f)).mp
        htail_compl
  have hf_zero : f 0 = 0 := by
    exact riemannZeta_dirichletTerm_zero_of_one_lt_re hz
  have hindicator :
      ({n : ℕ | n ∉ Finset.Icc 1 N}.indicator f) =
        (fun k : ℕ => if N < k then f k else 0) :=
    funext
      (fun n : ℕ =>
        nat_not_Icc_one_indicator_eq_cutoff_if_of_zero f N n hf_zero)
  have htail_if :
      HasSum
        (fun k : ℕ => if N < k then f k else 0)
        (riemannZeta z - ∑ n ∈ Finset.Icc 1 N, f n) :=
    Eq.subst
      (motive := fun g : ℕ → ℂ =>
        HasSum g (riemannZeta z - ∑ n ∈ Finset.Icc 1 N, f n))
      hindicator
      htail_indicator
  unfold eulerMaclaurinZetaFinitePart
  exact htail_if

/-- The exponent `-z` is integrable at infinity exactly in the half-plane
`1 < Re z`. -/
theorem eulerMaclaurin_cpow_neg_re_lt_neg_one_of_one_lt_re
    {z : ℂ}
    (hhalf_plane : 1 < z.re) :
    (-z).re < -1 := by
  have hneg : -z.re < -1 :=
    neg_lt_neg hhalf_plane
  exact
    Eq.subst
      (motive := fun x : ℝ => x < -1)
      (Complex.neg_re z).symm
      hneg

/-- The Euler-Maclaurin cutoff is a positive lower endpoint for improper
integrals. -/
theorem eulerMaclaurinPoleClearedZetaCutoff_real_pos
    (z : ℂ) :
    0 < (((eulerMaclaurinPoleClearedZetaCutoff z : ℕ) : ℝ)) := by
  exact Nat.cast_pos.mpr (eulerMaclaurinPoleClearedZetaCutoff_pos z)

/-- Mathlib's improper-integral formula applied to the zeta tail exponent
`-z`. -/
theorem eulerMaclaurin_riemannZeta_postCutoffTail_integral_cpow_neg_formula
    (z : ℂ)
    (hhalf_plane : 1 < z.re) :
    (∫ x in Set.Ioi (((eulerMaclaurinPoleClearedZetaCutoff z : ℕ) : ℝ)),
        (((x : ℝ) : ℂ) ^ (-z))) =
      -((((eulerMaclaurinPoleClearedZetaCutoff z : ℕ) : ℝ) : ℂ) ^
          ((-z) + 1)) /
        ((-z) + 1) := by
  exact
    integral_Ioi_cpow_of_lt
      (eulerMaclaurin_cpow_neg_re_lt_neg_one_of_one_lt_re hhalf_plane)
      (eulerMaclaurinPoleClearedZetaCutoff_real_pos z)

/-- Algebraic normalization of the improper-integral value.

This is the remaining `cpow` and division transport from mathlib's
`-N^((-z)+1)/((-z)+1)` to the owner term `N^(1-z)/(z-1)`. -/
theorem eulerMaclaurin_riemannZeta_postCutoffTail_integralFormula_eq_mainTerm
    (z : ℂ) :
    -((((eulerMaclaurinPoleClearedZetaCutoff z : ℕ) : ℝ) : ℂ) ^
          ((-z) + 1)) /
        ((-z) + 1) =
      eulerMaclaurinZetaMainTerm z := by
  unfold eulerMaclaurinZetaMainTerm
  let N : ℕ := eulerMaclaurinPoleClearedZetaCutoff z
  let A : ℂ := ((N : ℕ) : ℂ)
  have hbase :
      (((N : ℕ) : ℝ) : ℂ) = A :=
    Complex.ofReal_natCast N
  have hexponent :
      (-z) + 1 = (1 : ℂ) - z := by
    calc
      (-z) + 1 = (1 : ℂ) + (-z) := by
        exact add_comm (-z) (1 : ℂ)
      _ = (1 : ℂ) - z := by
        exact (sub_eq_add_neg (1 : ℂ) z).symm
  have hden :
      (-z) + 1 = -((z - 1)) := by
    calc
      (-z) + 1 = (1 : ℂ) - z :=
        hexponent
      _ = -(z - 1) := by
        exact (neg_sub z (1 : ℂ)).symm
  have hpow :
      ((((N : ℕ) : ℝ) : ℂ) ^ ((-z) + 1)) =
        A ^ ((1 : ℂ) - z) := by
    exact congrArg₂ (fun b e : ℂ => b ^ e) hbase hexponent
  calc
    -((((N : ℕ) : ℝ) : ℂ) ^ ((-z) + 1)) / ((-z) + 1) =
        -(A ^ ((1 : ℂ) - z)) / ((-z) + 1) := by
      exact congrArg
        (fun W : ℂ => -W / ((-z) + 1))
        hpow
    _ = -(A ^ ((1 : ℂ) - z)) / (-(z - 1)) := by
      exact congrArg
        (fun D : ℂ => -(A ^ ((1 : ℂ) - z)) / D)
        hden
    _ = A ^ ((1 : ℂ) - z) / (z - 1) := by
      exact neg_div_neg_eq (A ^ ((1 : ℂ) - z)) (z - 1)

/-- The Euler-Maclaurin integral main term for the post-cutoff tail.

For `N = ⌊2 + ‖z‖⌋₊`, mathlib's improper-integral formula for
`∫_N^∞ x^{-z} dx` gives `N^(1-z)/(z-1)` when `1 < Re z`.  This lemma records
the normalization used by the zeta owner definitions; the remaining work is
the standard `cpow` exponent arithmetic transporting
`integral_Ioi_cpow_of_lt` from exponent `-z`. -/
theorem eulerMaclaurin_riemannZeta_postCutoffTail_integralMain_eq_mainTerm_standard
    (z : ℂ)
    (hhalf_plane : 1 < z.re) :
    (∫ x in Set.Ioi (((eulerMaclaurinPoleClearedZetaCutoff z : ℕ) : ℝ)),
        (((x : ℝ) : ℂ) ^ (-z))) =
      eulerMaclaurinZetaMainTerm z := by
  exact
    Eq.trans
      (eulerMaclaurin_riemannZeta_postCutoffTail_integral_cpow_neg_formula
        z hhalf_plane)
      (eulerMaclaurin_riemannZeta_postCutoffTail_integralFormula_eq_mainTerm z)

/-- Endpoint normalization for the first-order Euler-Maclaurin tail.

The endpoint correction is exactly `(1/2)N^{-z}` in the owner notation. -/
theorem eulerMaclaurin_riemannZeta_postCutoffTail_endpoint_eq_endpointTerm
    (z : ℂ) :
    (1 / 2 : ℂ) *
        (1 / (((eulerMaclaurinPoleClearedZetaCutoff z : ℕ) : ℂ) ^ z)) =
      eulerMaclaurinZetaEndpointTerm z := by
  unfold eulerMaclaurinZetaEndpointTerm
  rfl

/-- Remainder-sign normalization for the first-order Euler-Maclaurin tail.

With `B₁({x}) = {x} - 1/2`, the first-order remainder for
`f(x) = x^{-z}` is
`-z ∫_N^∞ B₁({x}) x^{-z-1} dx`, matching the raw owner remainder. -/
theorem eulerMaclaurin_riemannZeta_postCutoffTail_remainderSign_eq_remainderTerm
    (z : ℂ) :
    -z * eulerMaclaurinPoleClearedZetaBernoulliIntegralCore z =
      eulerMaclaurinZetaBernoulliIntegralRemainder z := by
  unfold eulerMaclaurinZetaBernoulliIntegralRemainder
  rfl

/-- Derivative of the complex power profile used in the zeta tail.

On the positive real ray, the derivative of `x ↦ x^{-z}` is
`-z · x^{-z-1}`.  This is the calculus input in the first-order
Euler-Maclaurin formula. -/
theorem eulerMaclaurin_cpow_neg_deriv_eq
    (z : ℂ)
    {x : ℝ}
    (hx : 0 < x) :
    deriv (fun t : ℝ => (((t : ℝ) : ℂ) ^ (-z))) x =
      -z * (((x : ℝ) : ℂ) ^ (-(z + 1))) := by
  have hslit : ((x : ℂ) : ℂ) ∈ slitPlane :=
    ofReal_mem_slitPlane.mpr hx
  have hcomplex :
      HasDerivAt
        (fun w : ℂ => w ^ (-z))
        ((-z) * ((x : ℂ) ^ ((-z) - 1)) * 1)
        (x : ℂ) :=
    (hasDerivAt_id (x : ℂ)).cpow_const hslit
  have hreal :
      HasDerivAt
        (fun t : ℝ => (((t : ℝ) : ℂ) ^ (-z)))
        ((-z) * ((x : ℂ) ^ ((-z) - 1)) * 1)
        x :=
    hcomplex.comp_ofReal
  have hexponent :
      ((-z) - 1) = -(z + 1) := by
    calc
      ((-z) - 1) = (-z) + (-(1 : ℂ)) := by
        exact sub_eq_add_neg (-z) (1 : ℂ)
      _ = -(z + 1) := by
        exact (neg_add z (1 : ℂ)).symm
  have hvalue :
      ((-z) * ((x : ℂ) ^ ((-z) - 1)) * 1) =
        -z * (((x : ℝ) : ℂ) ^ (-(z + 1))) := by
    calc
      ((-z) * ((x : ℂ) ^ ((-z) - 1)) * 1) =
          (-z) * ((x : ℂ) ^ ((-z) - 1)) := by
        exact mul_one ((-z) * ((x : ℂ) ^ ((-z) - 1)))
      _ = -z * (((x : ℝ) : ℂ) ^ (-(z + 1))) := by
        exact congrArg
          (fun W : ℂ => -z * W)
          (congrArg (fun E : ℂ => ((x : ℂ) ^ E)) hexponent)
  exact Eq.trans hreal.deriv hvalue

/-- Positive natural reciprocal as a negative complex power.

This is the pointwise bridge between the Dirichlet summand notation
`1 / n^z` and the Euler-Maclaurin function notation `n^{-z}`. -/
theorem eulerMaclaurin_positiveNat_one_div_cpow_eq_cpow_neg
    (z : ℂ)
    {n : ℕ}
    (hn : 0 < n) :
    (1 : ℂ) / ((n : ℂ) ^ z) = (n : ℂ) ^ (-z) := by
  have hn_ne : (n : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.ne_of_gt hn)
  calc
    (1 : ℂ) / ((n : ℂ) ^ z) = (((n : ℂ) ^ z)⁻¹) := by
      exact one_div (((n : ℂ) ^ z))
    _ = (n : ℂ) ^ (-z) := by
      exact (Complex.cpow_neg (n : ℂ) z).symm

/-- Pointwise transport between the Euler-Maclaurin function-tail notation and
the Dirichlet reciprocal notation after a positive cutoff. -/
theorem eulerMaclaurin_cpow_neg_postCutoffTail_terms_eq_one_div
    (z : ℂ)
    (N : ℕ)
    (hN : 0 < N) :
    (fun n : ℕ =>
      if N < n then (((n : ℕ) : ℝ) : ℂ) ^ (-z) else 0) =
      (fun n : ℕ =>
        if N < n then (1 : ℂ) / ((n : ℂ) ^ z) else 0) := by
  exact funext
    (fun n : ℕ => by
      by_cases hn : N < n
      · have hn_pos : 0 < n :=
          lt_trans hN hn
        have hif_left :
            (if N < n then (((n : ℕ) : ℝ) : ℂ) ^ (-z) else 0) =
              (((n : ℕ) : ℝ) : ℂ) ^ (-z) :=
          if_pos hn
        have hif_right :
            (if N < n then (1 : ℂ) / ((n : ℂ) ^ z) else 0) =
              (1 : ℂ) / ((n : ℂ) ^ z) :=
          if_pos hn
        have hcast : (((n : ℕ) : ℝ) : ℂ) = (n : ℂ) :=
          Complex.ofReal_natCast n
        have hpow :
            (((n : ℕ) : ℝ) : ℂ) ^ (-z) =
              (n : ℂ) ^ (-z) :=
          congrArg (fun w : ℂ => w ^ (-z)) hcast
        have hrecip :
            (1 : ℂ) / ((n : ℂ) ^ z) = (n : ℂ) ^ (-z) :=
          eulerMaclaurin_positiveNat_one_div_cpow_eq_cpow_neg z hn_pos
        exact Eq.trans hif_left
          (Eq.trans hpow (Eq.trans hrecip.symm hif_right.symm))
      · have hif_left :
            (if N < n then (((n : ℕ) : ℝ) : ℂ) ^ (-z) else 0) = 0 :=
          if_neg hn
        have hif_right :
            (if N < n then (1 : ℂ) / ((n : ℂ) ^ z) else 0) = 0 :=
          if_neg hn
        exact Eq.trans hif_left hif_right.symm)

/-- `HasSum` transport between the Euler-Maclaurin function-tail notation and
the Dirichlet reciprocal notation after a positive cutoff. -/
theorem eulerMaclaurin_cpow_neg_postCutoffTail_hasSum_iff_one_div
    (z : ℂ)
    (N : ℕ)
    (hN : 0 < N)
    (S : ℂ) :
    HasSum
      (fun n : ℕ =>
        if N < n then (((n : ℕ) : ℝ) : ℂ) ^ (-z) else 0)
      S ↔
    HasSum
      (fun n : ℕ =>
        if N < n then (1 : ℂ) / ((n : ℂ) ^ z) else 0)
      S := by
  have hterms :
      (fun n : ℕ =>
        if N < n then (((n : ℕ) : ℝ) : ℂ) ^ (-z) else 0) =
        (fun n : ℕ =>
          if N < n then (1 : ℂ) / ((n : ℂ) ^ z) else 0) :=
    eulerMaclaurin_cpow_neg_postCutoffTail_terms_eq_one_div z N hN
  constructor
  · intro hsum
    exact Eq.subst
      (motive := fun f : ℕ → ℂ => HasSum f S)
      hterms
      hsum
  · intro hsum
    exact Eq.subst
      (motive := fun f : ℕ → ℂ => HasSum f S)
      hterms.symm
      hsum

/-- On a unit interval between consecutive natural numbers, the first periodic
Bernoulli sawtooth is the affine function `x - n - 1/2`. -/
theorem eulerMaclaurinFirstPeriodicBernoulli_eq_sub_nat_sub_half_on_Ioo
    (n : ℕ)
    {x : ℝ}
    (hx : x ∈ Set.Ioo (((n : ℕ) : ℝ)) (((n + 1 : ℕ) : ℝ))) :
    eulerMaclaurinFirstPeriodicBernoulli x =
      x - ((n : ℕ) : ℝ) - 1 / 2 := by
  unfold eulerMaclaurinFirstPeriodicBernoulli
  have hfract_shift :
      Int.fract (x - ((n : ℕ) : ℝ)) = Int.fract x :=
    Int.fract_sub_nat x n
  have hshift_nonneg : 0 ≤ x - ((n : ℕ) : ℝ) :=
    le_of_lt (sub_pos.mpr hx.1)
  have hshift_lt_one : x - ((n : ℕ) : ℝ) < 1 := by
    have hsucc :
        (((n + 1 : ℕ) : ℝ)) = ((n : ℕ) : ℝ) + 1 := by
      exact Nat.cast_add_one n
    calc
      x - ((n : ℕ) : ℝ) <
          (((n + 1 : ℕ) : ℝ)) - ((n : ℕ) : ℝ) := by
        exact sub_lt_sub_right hx.2 (((n : ℕ) : ℝ))
      _ = (((n : ℕ) : ℝ) + 1) - ((n : ℕ) : ℝ) := by
        exact congrArg (fun t : ℝ => t - ((n : ℕ) : ℝ)) hsucc
      _ = 1 := by
        exact add_sub_cancel_left 1 (((n : ℕ) : ℝ))
  have hfract_self :
      Int.fract (x - ((n : ℕ) : ℝ)) =
        x - ((n : ℕ) : ℝ) :=
    (Int.fract_eq_self).mpr ⟨hshift_nonneg, hshift_lt_one⟩
  calc
    Int.fract x - 1 / 2 =
        Int.fract (x - ((n : ℕ) : ℝ)) - 1 / 2 := by
      exact congrArg (fun t : ℝ => t - 1 / 2) hfract_shift.symm
    _ = x - ((n : ℕ) : ℝ) - 1 / 2 := by
      exact congrArg (fun t : ℝ => t - 1 / 2) hfract_self

/-- One-unit-interval integration-by-parts identity for the first periodic
Bernoulli factor.

On `(n, n+1]`, `Int.fract x = x - n`, so the sawtooth is
`x - n - 1/2`.  Integrating by parts against `f'` gives the local
Euler-Maclaurin correction with the strict-right endpoint convention
`+ f(n)/2 - f(n+1)/2`. -/
theorem eulerMaclaurin_firstPeriodicBernoulli_oneInterval_integrationByParts
    (f f' : ℝ → ℂ)
    (n : ℕ)
    (hf_cont : ContinuousOn f
      (Set.Icc (((n : ℕ) : ℝ)) (((n + 1 : ℕ) : ℝ))))
    (hf_deriv : ∀ x : ℝ,
      x ∈ Set.Ioo (((n : ℕ) : ℝ)) (((n + 1 : ℕ) : ℝ)) →
        HasDerivAt f (f' x) x)
    (hf'_int : IntegrableOn f'
      (Set.Ioc (((n : ℕ) : ℝ)) (((n + 1 : ℕ) : ℝ)))) :
    f (((n + 1 : ℕ) : ℝ)) =
      (∫ x in Set.Ioc (((n : ℕ) : ℝ)) (((n + 1 : ℕ) : ℝ)), f x) +
        ((1 / 2 : ℂ) * f (((n : ℕ) : ℝ))) +
        (-(1 / 2 : ℂ) * f (((n + 1 : ℕ) : ℝ))) +
        (∫ x in Set.Ioc (((n : ℕ) : ℝ)) (((n + 1 : ℕ) : ℝ)),
          ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) * f' x) := by
  sorry

/-- Finite summation of the one-interval first-periodic-Bernoulli
integration-by-parts identities over a natural `Ioc` interval.

Summing the local formula over `n = N, ..., M - 1` telescopes the half-endpoint
terms to `+ f(N)/2 - f(M)/2`, matching the strict post-cutoff convention
`N < n ≤ M`. -/
theorem eulerMaclaurin_firstPeriodicBernoulli_sum_oneInterval_Ioc
    (f f' : ℝ → ℂ)
    (N M : ℕ)
    (hNM : N ≤ M)
    (hf_cont : ContinuousOn f
      (Set.Icc (((N : ℕ) : ℝ)) (((M : ℕ) : ℝ))))
    (hf_deriv : ∀ x : ℝ,
      x ∈ Set.Ioo (((N : ℕ) : ℝ)) (((M : ℕ) : ℝ)) →
        HasDerivAt f (f' x) x)
    (hf'_int : IntegrableOn f'
      (Set.Ioc (((N : ℕ) : ℝ)) (((M : ℕ) : ℝ)))) :
    (∑ n in Finset.Ioc N M, f ((n : ℕ) : ℝ)) =
      (∫ x in Set.Ioc (((N : ℕ) : ℝ)) (((M : ℕ) : ℝ)), f x) +
        ((1 / 2 : ℂ) * f (((N : ℕ) : ℝ))) +
        (-(1 / 2 : ℂ) * f (((M : ℕ) : ℝ))) +
        (∫ x in Set.Ioc (((N : ℕ) : ℝ)) (((M : ℕ) : ℝ)),
          ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) * f' x) := by
  sorry

/-- First-periodic-Bernoulli integration-by-parts form of the finite
first-order Euler-Maclaurin formula on a natural `Ioc` interval.

This is the genuine finite calculus theorem behind the owner formula: on each
unit interval the derivative of `x - n - 1/2` is `1`, and summing the resulting
integration-by-parts identities gives the `Ioc` endpoint signs. -/
theorem eulerMaclaurin_firstPeriodicBernoulli_integrationByParts_Ioc
    (f f' : ℝ → ℂ)
    (N M : ℕ)
    (hNM : N ≤ M)
    (hf_cont : ContinuousOn f
      (Set.Icc (((N : ℕ) : ℝ)) (((M : ℕ) : ℝ))))
    (hf_deriv : ∀ x : ℝ,
      x ∈ Set.Ioo (((N : ℕ) : ℝ)) (((M : ℕ) : ℝ)) →
        HasDerivAt f (f' x) x)
    (hf'_int : IntegrableOn f'
      (Set.Ioc (((N : ℕ) : ℝ)) (((M : ℕ) : ℝ)))) :
    (∑ n in Finset.Ioc N M, f ((n : ℕ) : ℝ)) =
      (∫ x in Set.Ioc (((N : ℕ) : ℝ)) (((M : ℕ) : ℝ)), f x) +
        ((1 / 2 : ℂ) * f (((N : ℕ) : ℝ))) +
        (-(1 / 2 : ℂ) * f (((M : ℕ) : ℝ))) +
        (∫ x in Set.Ioc (((N : ℕ) : ℝ)) (((M : ℕ) : ℝ)),
          ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) * f' x) := by
  exact
    eulerMaclaurin_firstPeriodicBernoulli_sum_oneInterval_Ioc
      f f' N M hNM hf_cont hf_deriv hf'_int

/-- Generic finite first-order Euler-Maclaurin identity on a natural `Ioc`
interval, with the first periodic Bernoulli remainder.

This is the exact finite calculus theorem needed by the zeta specialization:
the function is continuous on the compact interval, has the stated derivative
on the open interval, and the derivative is integrable. -/
theorem eulerMaclaurin_firstOrder_finite_Ioc_identity_of_hasDerivAt
    (f f' : ℝ → ℂ)
    (N M : ℕ)
    (hNM : N ≤ M)
    (hf_cont : ContinuousOn f
      (Set.Icc (((N : ℕ) : ℝ)) (((M : ℕ) : ℝ))))
    (hf_deriv : ∀ x : ℝ,
      x ∈ Set.Ioo (((N : ℕ) : ℝ)) (((M : ℕ) : ℝ)) →
        HasDerivAt f (f' x) x)
    (hf'_int : IntegrableOn f'
      (Set.Ioc (((N : ℕ) : ℝ)) (((M : ℕ) : ℝ)))) :
    (∑ n in Finset.Ioc N M, f ((n : ℕ) : ℝ)) =
      (∫ x in Set.Ioc (((N : ℕ) : ℝ)) (((M : ℕ) : ℝ)), f x) +
        ((1 / 2 : ℂ) * f (((N : ℕ) : ℝ))) +
        (-(1 / 2 : ℂ) * f (((M : ℕ) : ℝ))) +
        (∫ x in Set.Ioc (((N : ℕ) : ℝ)) (((M : ℕ) : ℝ)),
          ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) * f' x) := by
  exact
    eulerMaclaurin_firstPeriodicBernoulli_integrationByParts_Ioc
      f f' N M hNM hf_cont hf_deriv hf'_int

/-- Continuity of the zeta complex-power profile on a positive finite real
interval. -/
theorem eulerMaclaurin_cpow_neg_continuousOn_Icc_nat
    (z : ℂ)
    (N M : ℕ)
    (hN : 0 < N) :
    ContinuousOn
      (fun x : ℝ => (((x : ℝ) : ℂ) ^ (-z)))
      (Set.Icc (((N : ℕ) : ℝ)) (((M : ℕ) : ℝ))) := by
  intro x hx
  have hx_pos : 0 < x :=
    lt_of_lt_of_le (Nat.cast_pos.mpr hN) hx.1
  exact
    (Complex.continuousAt_ofReal_cpow_const x (-z)
      (Or.inr (ne_of_gt hx_pos))).continuousWithinAt

/-- Pointwise derivative of the zeta complex-power profile on a positive
finite real interval. -/
theorem eulerMaclaurin_cpow_neg_hasDerivAt_on_Ioo_nat
    (z : ℂ)
    (N M : ℕ)
    (hN : 0 < N) :
    ∀ x : ℝ,
      x ∈ Set.Ioo (((N : ℕ) : ℝ)) (((M : ℕ) : ℝ)) →
        HasDerivAt
          (fun t : ℝ => (((t : ℝ) : ℂ) ^ (-z)))
          (-z * (((x : ℝ) : ℂ) ^ (-(z + 1))))
          x := by
  intro x hx
  have hx_pos : 0 < x :=
    lt_trans (Nat.cast_pos.mpr hN) hx.1
  have hslit : ((x : ℂ) : ℂ) ∈ slitPlane :=
    ofReal_mem_slitPlane.mpr hx_pos
  have hcomplex :
      HasDerivAt
        (fun w : ℂ => w ^ (-z))
        ((-z) * ((x : ℂ) ^ ((-z) - 1)) * 1)
        (x : ℂ) :=
    (hasDerivAt_id (x : ℂ)).cpow_const hslit
  have hreal :
      HasDerivAt
        (fun t : ℝ => (((t : ℝ) : ℂ) ^ (-z)))
        ((-z) * ((x : ℂ) ^ ((-z) - 1)) * 1)
        x :=
    hcomplex.comp_ofReal
  have hexponent :
      ((-z) - 1) = -(z + 1) := by
    calc
      ((-z) - 1) = (-z) + (-(1 : ℂ)) := by
        exact sub_eq_add_neg (-z) (1 : ℂ)
      _ = -(z + 1) := by
        exact (neg_add z (1 : ℂ)).symm
  have hvalue :
      ((-z) * ((x : ℂ) ^ ((-z) - 1)) * 1) =
        -z * (((x : ℝ) : ℂ) ^ (-(z + 1))) := by
    calc
      ((-z) * ((x : ℂ) ^ ((-z) - 1)) * 1) =
          (-z) * ((x : ℂ) ^ ((-z) - 1)) := by
        exact mul_one ((-z) * ((x : ℂ) ^ ((-z) - 1)))
      _ = -z * (((x : ℝ) : ℂ) ^ (-(z + 1))) := by
        exact congrArg
          (fun W : ℂ => -z * W)
          (congrArg (fun E : ℂ => ((x : ℂ) ^ E)) hexponent)
  exact hreal.congr_deriv hvalue

/-- Integrability of the derivative profile on a positive finite real
interval. -/
theorem eulerMaclaurin_cpow_neg_derivative_integrableOn_Ioc_nat
    (z : ℂ)
    (N M : ℕ)
    (hN : 0 < N) :
    IntegrableOn
      (fun x : ℝ => -z * (((x : ℝ) : ℂ) ^ (-(z + 1))))
      (Set.Ioc (((N : ℕ) : ℝ)) (((M : ℕ) : ℝ))) := by
  have hcont :
      ContinuousOn
        (fun x : ℝ => -z * (((x : ℝ) : ℂ) ^ (-(z + 1))))
        (Set.Icc (((N : ℕ) : ℝ)) (((M : ℕ) : ℝ))) := by
    intro x hx
    have hx_pos : 0 < x :=
      lt_of_lt_of_le (Nat.cast_pos.mpr hN) hx.1
    exact
      ((Complex.continuousAt_ofReal_cpow_const x (-(z + 1))
        (Or.inr (ne_of_gt hx_pos))).const_mul (-z)).continuousWithinAt
  have hcompact : IsCompact (Set.Icc (((N : ℕ) : ℝ)) (((M : ℕ) : ℝ))) :=
    isCompact_Icc
  have hsubset :
      Set.Ioc (((N : ℕ) : ℝ)) (((M : ℕ) : ℝ)) ⊆
        Set.Icc (((N : ℕ) : ℝ)) (((M : ℕ) : ℝ)) := by
    intro x hx
    exact ⟨le_of_lt hx.1, hx.2⟩
  exact (hcompact.integrableOn hcont).mono_set hsubset

/-- Finite first-order Euler-Maclaurin identity for the strict post-cutoff
complex-power tail.

This is the finite owner construction missing from the local file: for
`f(x) = x^{-z}` and positive cutoffs `N ≤ M`, the finite strict tail
`N < n ≤ M` is expressed as the finite integral, the two half-endpoint
corrections, and the first-periodic-Bernoulli derivative remainder.  The
infinite post-cutoff formula below is obtained by sending `M → ∞` in this
identity. -/
theorem eulerMaclaurin_firstOrder_cpow_neg_finite_postCutoffTail_identity_standard
    (z : ℂ)
    (N M : ℕ)
    (hN : 0 < N)
    (hNM : N ≤ M) :
    (∑ n in Finset.Ioc N M, (((n : ℕ) : ℝ) : ℂ) ^ (-z)) =
      (∫ x in Set.Ioc (((N : ℕ) : ℝ)) (((M : ℕ) : ℝ)),
          (((x : ℝ) : ℂ) ^ (-z))) +
        ((1 / 2 : ℂ) * ((((N : ℕ) : ℝ) : ℂ) ^ (-z))) +
        (-(1 / 2 : ℂ) * ((((M : ℕ) : ℝ) : ℂ) ^ (-z))) +
        (∫ x in Set.Ioc (((N : ℕ) : ℝ)) (((M : ℕ) : ℝ)),
          ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) *
            (-z * (((x : ℝ) : ℂ) ^ (-(z + 1))))) := by
  let f : ℝ → ℂ := fun x : ℝ => (((x : ℝ) : ℂ) ^ (-z))
  let f' : ℝ → ℂ := fun x : ℝ => -z * (((x : ℝ) : ℂ) ^ (-(z + 1)))
  have hf_cont :
      ContinuousOn f
        (Set.Icc (((N : ℕ) : ℝ)) (((M : ℕ) : ℝ))) :=
    eulerMaclaurin_cpow_neg_continuousOn_Icc_nat z N M hN
  have hf_deriv :
      ∀ x : ℝ,
        x ∈ Set.Ioo (((N : ℕ) : ℝ)) (((M : ℕ) : ℝ)) →
          HasDerivAt f (f' x) x :=
    eulerMaclaurin_cpow_neg_hasDerivAt_on_Ioo_nat z N M hN
  have hf'_int :
      IntegrableOn f'
        (Set.Ioc (((N : ℕ) : ℝ)) (((M : ℕ) : ℝ))) :=
    eulerMaclaurin_cpow_neg_derivative_integrableOn_Ioc_nat z N M hN
  exact
    eulerMaclaurin_firstOrder_finite_Ioc_identity_of_hasDerivAt
      f f' N M hNM hf_cont hf_deriv hf'_int

/-- The upper endpoint correction in the finite post-cutoff complex-power
Euler-Maclaurin identity vanishes as the upper cutoff tends to infinity. -/
theorem eulerMaclaurin_cpow_neg_upperEndpoint_tendsto_zero
    (z : ℂ)
    (hhalf_plane : 1 < z.re) :
    Tendsto
      (fun M : ℕ => (-(1 / 2 : ℂ) * ((((M : ℕ) : ℝ) : ℂ) ^ (-z))))
      atTop
      (𝓝 0) := by
  let f : ℕ → ℂ := fun M : ℕ => (1 : ℂ) / ((M : ℂ) ^ z)
  have hf_summable : Summable f :=
    (Complex.summable_one_div_nat_cpow (p := z)).mpr hhalf_plane
  have hf_tendsto : Tendsto f atTop (𝓝 0) :=
    hf_summable.tendsto_atTop_zero
  have hterms :
      f =ᶠ[atTop]
        (fun M : ℕ => ((((M : ℕ) : ℝ) : ℂ) ^ (-z))) := by
    filter_upwards [eventually_gt_atTop (0 : ℕ)] with M hM
    have hM_pos : 0 < M :=
      hM
    have hcast : (((M : ℕ) : ℝ) : ℂ) = (M : ℂ) :=
      Complex.ofReal_natCast M
    have hrecip :
        (1 : ℂ) / ((M : ℂ) ^ z) = (M : ℂ) ^ (-z) :=
      eulerMaclaurin_positiveNat_one_div_cpow_eq_cpow_neg z hM_pos
    exact Eq.trans hrecip (congrArg (fun w : ℂ => w ^ (-z)) hcast.symm)
  have hpow_tendsto :
      Tendsto
        (fun M : ℕ => ((((M : ℕ) : ℝ) : ℂ) ^ (-z)))
        atTop
        (𝓝 0) :=
    hf_tendsto.congr' hterms
  have hmul :
      Tendsto
        (fun M : ℕ => (-(1 / 2 : ℂ)) *
          ((((M : ℕ) : ℝ) : ℂ) ^ (-z)))
        atTop
        (𝓝 ((-(1 / 2 : ℂ)) * 0)) :=
    tendsto_const_nhds.mul hpow_tendsto
  exact
    Eq.subst
      (motive := fun L : ℂ =>
        Tendsto
          (fun M : ℕ => (-(1 / 2 : ℂ)) *
            ((((M : ℕ) : ℝ) : ℂ) ^ (-z)))
          atTop
          (𝓝 L))
      (mul_zero (-(1 / 2 : ℂ)))
      hmul

/-- The finite main integral over `(N, M]` tends to the improper main integral
over `(N, ∞)`. -/
theorem eulerMaclaurin_cpow_neg_integral_Ioc_tendsto_integral_Ioi
    (z : ℂ)
    (N : ℕ)
    (hN : 0 < N)
    (hhalf_plane : 1 < z.re) :
    Tendsto
      (fun M : ℕ =>
        ∫ x in Set.Ioc (((N : ℕ) : ℝ)) (((M : ℕ) : ℝ)),
          (((x : ℝ) : ℂ) ^ (-z)))
      atTop
      (𝓝
        (∫ x in Set.Ioi (((N : ℕ) : ℝ)),
          (((x : ℝ) : ℂ) ^ (-z)))) := by
  let a : ℝ := ((N : ℕ) : ℝ)
  let f : ℝ → ℂ := fun x : ℝ => (((x : ℝ) : ℂ) ^ (-z))
  have ha_pos : 0 < a := by
    unfold a
    exact Nat.cast_pos.mpr hN
  have hf_int : IntegrableOn f (Set.Ioi a) :=
    integrableOn_Ioi_cpow_of_lt
      (eulerMaclaurin_cpow_neg_re_lt_neg_one_of_one_lt_re hhalf_plane)
      ha_pos
  have h_interval :
      Tendsto
        (fun M : ℕ => ∫ x in a..((M : ℕ) : ℝ), f x)
        atTop
        (𝓝 (∫ x in Set.Ioi a, f x)) :=
    intervalIntegral_tendsto_integral_Ioi
      a hf_int tendsto_natCast_atTop_atTop
  have hset_eq :
      (fun M : ℕ =>
        ∫ x in Set.Ioc (((N : ℕ) : ℝ)) (((M : ℕ) : ℝ)),
          (((x : ℝ) : ℂ) ^ (-z))) =ᶠ[atTop]
        (fun M : ℕ => ∫ x in a..((M : ℕ) : ℝ), f x) := by
    filter_upwards [eventually_ge_atTop N] with M hNM
    have hle : a ≤ ((M : ℕ) : ℝ) := by
      unfold a
      exact_mod_cast hNM
    have hinterval :
        (∫ x in a..((M : ℕ) : ℝ), f x) =
          ∫ x in Set.Ioc a (((M : ℕ) : ℝ)), f x :=
      intervalIntegral.integral_of_le hle
    exact hinterval.symm
  exact h_interval.congr' hset_eq.symm

/-- Integrability of the unfactored Bernoulli/cpow kernel on a positive
post-cutoff tail in the convergent half-plane.

The proof is the direct majorant estimate
`|B₁({x}) x^{-(z+1)}| ≤ x^{-(Re z + 1)}` on `x ≥ N ≥ 1`, followed by the
standard real-power tail integrability for exponent below `-1`. -/
theorem eulerMaclaurin_cpow_neg_bernoulliKernel_integrableOn_Ioi
    (z : ℂ)
    (N : ℕ)
    (hN : 0 < N)
    (hhalf_plane : 1 < z.re) :
    IntegrableOn
      (fun x : ℝ =>
        ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) *
          (((x : ℝ) : ℂ) ^ (-(z + 1))))
      (Set.Ioi (((N : ℕ) : ℝ))) := by
  let s : Set ℝ := Set.Ioi (((N : ℕ) : ℝ))
  let f : ℝ → ℂ := fun x : ℝ =>
    ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) *
      (((x : ℝ) : ℂ) ^ (-(z + 1)))
  let g : ℝ → ℝ := fun x : ℝ => x ^ (-(z.re + 1))
  have hN_one_nat : 1 ≤ N :=
    Nat.succ_le_of_lt hN
  have hN_one_real : (1 : ℝ) ≤ ((N : ℕ) : ℝ) := by
    exact_mod_cast hN_one_nat
  have hN_pos_real : 0 < (((N : ℕ) : ℝ)) := by
    exact_mod_cast hN
  have htwo_le : (2 : ℝ) ≤ z.re + 1 := by
    have hone_le : (1 : ℝ) ≤ z.re :=
      le_of_lt hhalf_plane
    calc
      (2 : ℝ) = 1 + 1 := by
        exact (one_add_one_eq_two : (1 : ℝ) + 1 = 2).symm
      _ ≤ z.re + 1 :=
        add_le_add hone_le le_rfl
  have hone_lt : (1 : ℝ) < z.re + 1 :=
    lt_of_lt_of_le one_lt_two htwo_le
  have hexponent_lt : -(z.re + 1) < -(1 : ℝ) :=
    neg_lt_neg hone_lt
  have hg_integrable : IntegrableOn g s :=
    integrableOn_Ioi_rpow_of_lt hexponent_lt hN_pos_real
  have hf_meas :
      AEStronglyMeasurable f (volume.restrict s) := by
    simpa [f, s] using
      eulerMaclaurinBernoulliKernel_aestronglyMeasurable N hN z
  have hbound :
      ∀ᵐ x ∂volume.restrict s, ‖f x‖ ≤ g x := by
    exact (ae_restrict_mem measurableSet_Ioi).mono
      (fun x hx_tail => by
        have hx_one : 1 ≤ x :=
          le_trans hN_one_real (le_of_lt hx_tail)
        have hx_pos : 0 < x :=
          lt_of_lt_of_le zero_lt_one hx_one
        have hB :
            ‖((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ)‖ ≤ 1 :=
          eulerMaclaurinFirstPeriodicBernoulli_norm_cast_le_one_local x
        have hcpow :
            ‖((x : ℝ) : ℂ) ^ (-(z + 1))‖ ≤ g x :=
          eulerMaclaurin_norm_real_cpow_le_rpow_of_re_lower
            hx_pos hx_one z (le_of_lt hhalf_plane)
        have hmul :
            ‖f x‖ =
              ‖((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ)‖ *
                ‖((x : ℝ) : ℂ) ^ (-(z + 1))‖ := by
          exact norm_mul
            ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ)
            (((x : ℝ) : ℂ) ^ (-(z + 1)))
        have hg_nonneg : 0 ≤ g x :=
          Real.rpow_nonneg (le_of_lt hx_pos) (-(z.re + 1))
        have hproduct :
            ‖((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ)‖ *
                ‖((x : ℝ) : ℂ) ^ (-(z + 1))‖ ≤
              1 * g x :=
          mul_le_mul hB hcpow
            (norm_nonneg (((x : ℝ) : ℂ) ^ (-(z + 1))))
            hg_nonneg
        exact Eq.subst
          (motive := fun y : ℝ => y ≤ g x)
          hmul.symm
          (Eq.subst
            (motive := fun y : ℝ =>
              ‖((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ)‖ *
                  ‖((x : ℝ) : ℂ) ^ (-(z + 1))‖ ≤ y)
            (one_mul (g x)).symm
            hproduct))
  exact Integrable.mono' hg_integrable hf_meas hbound

/-- Integrability of the first-order Bernoulli derivative remainder tail in
the convergent zeta half-plane. -/
theorem eulerMaclaurin_cpow_neg_bernoulliRemainder_integrableOn_Ioi
    (z : ℂ)
    (N : ℕ)
    (hN : 0 < N)
    (hhalf_plane : 1 < z.re) :
    IntegrableOn
      (fun x : ℝ =>
        ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) *
          (-z * (((x : ℝ) : ℂ) ^ (-(z + 1)))))
      (Set.Ioi (((N : ℕ) : ℝ))) := by
  let f : ℝ → ℂ := fun x : ℝ =>
    ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) *
      (((x : ℝ) : ℂ) ^ (-(z + 1)))
  have hf_int : IntegrableOn f (Set.Ioi (((N : ℕ) : ℝ))) :=
    eulerMaclaurin_cpow_neg_bernoulliKernel_integrableOn_Ioi
      z N hN hhalf_plane
  have hpoint :
      (fun x : ℝ =>
        ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) *
          (-z * (((x : ℝ) : ℂ) ^ (-(z + 1))))) =
      (fun x : ℝ => -z * f x) := by
    exact funext
      (fun x : ℝ => by
        let a : ℂ := ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ)
        let b : ℂ := (((x : ℝ) : ℂ) ^ (-(z + 1)))
        calc
          a * (-z * b) = (a * -z) * b := by
            exact (mul_assoc a (-z) b).symm
          _ = (-z * a) * b := by
            exact congrArg (fun y : ℂ => y * b) (mul_comm a (-z))
          _ = -z * (a * b) := by
            exact mul_assoc (-z) a b)
  have hconst :
      IntegrableOn
        (fun x : ℝ => -z * f x)
        (Set.Ioi (((N : ℕ) : ℝ))) :=
    hf_int.const_mul (-z)
  exact Eq.subst
    (motive := fun F : ℝ → ℂ =>
      IntegrableOn F (Set.Ioi (((N : ℕ) : ℝ))))
    hpoint.symm
    hconst

/-- The finite Bernoulli remainder integral over `(N, M]` tends to the
improper Bernoulli remainder integral over `(N, ∞)`. -/
theorem eulerMaclaurin_cpow_neg_bernoulliRemainder_Ioc_tendsto_integral_Ioi
    (z : ℂ)
    (N : ℕ)
    (hN : 0 < N)
    (hhalf_plane : 1 < z.re) :
    Tendsto
      (fun M : ℕ =>
        ∫ x in Set.Ioc (((N : ℕ) : ℝ)) (((M : ℕ) : ℝ)),
          ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) *
            (-z * (((x : ℝ) : ℂ) ^ (-(z + 1)))))
      atTop
      (𝓝
        (∫ x in Set.Ioi (((N : ℕ) : ℝ)),
          ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) *
            (-z * (((x : ℝ) : ℂ) ^ (-(z + 1)))))) := by
  let a : ℝ := ((N : ℕ) : ℝ)
  let f : ℝ → ℂ := fun x : ℝ =>
    ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) *
      (-z * (((x : ℝ) : ℂ) ^ (-(z + 1))))
  have hf_int : IntegrableOn f (Set.Ioi a) :=
    eulerMaclaurin_cpow_neg_bernoulliRemainder_integrableOn_Ioi
      z N hN hhalf_plane
  have h_interval :
      Tendsto
        (fun M : ℕ => ∫ x in a..((M : ℕ) : ℝ), f x)
        atTop
        (𝓝 (∫ x in Set.Ioi a, f x)) :=
    intervalIntegral_tendsto_integral_Ioi
      a hf_int tendsto_natCast_atTop_atTop
  have hset_eq :
      (fun M : ℕ =>
        ∫ x in Set.Ioc (((N : ℕ) : ℝ)) (((M : ℕ) : ℝ)),
          ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) *
            (-z * (((x : ℝ) : ℂ) ^ (-(z + 1))))) =ᶠ[atTop]
        (fun M : ℕ => ∫ x in a..((M : ℕ) : ℝ), f x) := by
    filter_upwards [eventually_ge_atTop N] with M hNM
    have hle : a ≤ ((M : ℕ) : ℝ) := by
      unfold a
      exact_mod_cast hNM
    have hinterval :
        (∫ x in a..((M : ℕ) : ℝ), f x) =
          ∫ x in Set.Ioc a (((M : ℕ) : ℝ)), f x :=
      intervalIntegral.integral_of_le hle
    exact hinterval.symm
  exact h_interval.congr' hset_eq.symm

/-- Range partial sums of a zero-extended strict tail are the corresponding
`Ioc` sums. -/
theorem sum_range_succ_strictTail_eq_sum_Ioc
    (f : ℕ → ℂ)
    (N M : ℕ) :
    (∑ n in Finset.range (M + 1), if N < n then f n else 0) =
      ∑ n in Finset.Ioc N M, f n := by
  classical
  calc
    (∑ n in Finset.range (M + 1), if N < n then f n else 0) =
        ∑ n in (Finset.range (M + 1)).filter (fun n : ℕ => N < n), f n := by
      exact (Finset.sum_filter (s := Finset.range (M + 1))
        (p := fun n : ℕ => N < n) (f := f)).symm
    _ = ∑ n in Finset.Ioc N M, f n := by
      have hset :
          (Finset.range (M + 1)).filter (fun n : ℕ => N < n) =
            Finset.Ioc N M := by
        ext n
        constructor
        · intro hn
          have hn_range : n ∈ Finset.range (M + 1) :=
            (Finset.mem_filter.mp hn).1
          have hn_gt : N < n :=
            (Finset.mem_filter.mp hn).2
          have hn_le : n ≤ M :=
            Nat.lt_succ_iff.mp (Finset.mem_range.mp hn_range)
          exact Finset.mem_Ioc.mpr ⟨hn_gt, hn_le⟩
        · intro hn
          have hn_gt : N < n :=
            (Finset.mem_Ioc.mp hn).1
          have hn_le : n ≤ M :=
            (Finset.mem_Ioc.mp hn).2
          have hn_range : n ∈ Finset.range (M + 1) :=
            Finset.mem_range.mpr (Nat.lt_succ_iff.mpr hn_le)
          exact Finset.mem_filter.mpr ⟨hn_range, hn_gt⟩
      exact congrArg (fun s : Finset ℕ => ∑ n in s, f n) hset

/-- Ordered finite strict-tail sums over `Ioc N M` give the unconditional
`HasSum` of the zero-extended post-cutoff sequence once the latter is
absolutely summable.

This is the index bridge between the sequential Euler-Maclaurin finite-window
limit and mathlib's unordered `HasSum` over `ℕ`. -/
theorem hasSum_of_Ioc_strictTail_tendsto_of_summable_norm
    (f : ℕ → ℂ)
    (N : ℕ)
    (S : ℂ)
    (hsummable_norm : Summable
      (fun n : ℕ => ‖if N < n then f n else 0‖))
    (htendsto :
      Tendsto
        (fun M : ℕ => ∑ n in Finset.Ioc N M, f n)
        atTop
        (𝓝 S)) :
    HasSum
      (fun n : ℕ => if N < n then f n else 0)
      S := by
  let g : ℕ → ℂ := fun n : ℕ => if N < n then f n else 0
  have hshift :
      Tendsto
        (fun M : ℕ => ∑ n in Finset.range (M + 1), g n)
        atTop
        (𝓝 S) := by
    have hpoint :
        (fun M : ℕ => ∑ n in Finset.range (M + 1), g n) =
        (fun M : ℕ => ∑ n in Finset.Ioc N M, f n) := by
      exact funext
        (fun M : ℕ => by
          unfold g
          exact sum_range_succ_strictTail_eq_sum_Ioc f N M)
    exact Eq.subst
      (motive := fun F : ℕ → ℂ => Tendsto F atTop (𝓝 S))
      hpoint.symm
      htendsto
  have hunshift :
      Tendsto
        (fun M : ℕ => ∑ n in Finset.range M, g n)
        atTop
        (𝓝 S) := by
    exact (tendsto_add_atTop_iff_nat (f :=
      fun M : ℕ => ∑ n in Finset.range M, g n) 1).mp hshift
  have hhas :
      HasSum g S :=
    (hasSum_iff_tendsto_nat_of_summable_norm hsummable_norm).mpr
      hunshift
  exact hhas

/-- Limit passage from the finite strict-tail Euler-Maclaurin identity to the
improper post-cutoff `HasSum`.

The analytic inputs are exactly the finite identity above, decay in the
half-plane `1 < Re z`, and integrability of the Bernoulli derivative tail. -/
theorem eulerMaclaurin_firstOrder_cpow_neg_finite_postCutoffTail_tendsto_hasSum
    (z : ℂ)
    (N : ℕ)
    (hN : 0 < N)
    (hhalf_plane : 1 < z.re) :
    HasSum
      (fun n : ℕ =>
        if N < n then (((n : ℕ) : ℝ) : ℂ) ^ (-z) else 0)
      ((∫ x in Set.Ioi (((N : ℕ) : ℝ)),
          (((x : ℝ) : ℂ) ^ (-z))) +
        ((1 / 2 : ℂ) * ((((N : ℕ) : ℝ) : ℂ) ^ (-z))) +
        (∫ x in Set.Ioi (((N : ℕ) : ℝ)),
          ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) *
            (-z * (((x : ℝ) : ℂ) ^ (-(z + 1)))))) := by
  have hfinite :
      ∀ M : ℕ, N ≤ M →
        (∑ n in Finset.Ioc N M, (((n : ℕ) : ℝ) : ℂ) ^ (-z)) =
          (∫ x in Set.Ioc (((N : ℕ) : ℝ)) (((M : ℕ) : ℝ)),
              (((x : ℝ) : ℂ) ^ (-z))) +
            ((1 / 2 : ℂ) * ((((N : ℕ) : ℝ) : ℂ) ^ (-z))) +
            (-(1 / 2 : ℂ) * ((((M : ℕ) : ℝ) : ℂ) ^ (-z))) +
            (∫ x in Set.Ioc (((N : ℕ) : ℝ)) (((M : ℕ) : ℝ)),
              ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) *
                (-z * (((x : ℝ) : ℂ) ^ (-(z + 1))))) := by
    intro M hNM
    exact
      eulerMaclaurin_firstOrder_cpow_neg_finite_postCutoffTail_identity_standard
        z N M hN hNM
  have hendpoint :
      Tendsto
        (fun M : ℕ => (-(1 / 2 : ℂ) * ((((M : ℕ) : ℝ) : ℂ) ^ (-z))))
        atTop
        (𝓝 0) :=
    eulerMaclaurin_cpow_neg_upperEndpoint_tendsto_zero z hhalf_plane
  have hmain :
      Tendsto
        (fun M : ℕ =>
          ∫ x in Set.Ioc (((N : ℕ) : ℝ)) (((M : ℕ) : ℝ)),
            (((x : ℝ) : ℂ) ^ (-z)))
        atTop
        (𝓝
          (∫ x in Set.Ioi (((N : ℕ) : ℝ)),
            (((x : ℝ) : ℂ) ^ (-z)))) :=
    eulerMaclaurin_cpow_neg_integral_Ioc_tendsto_integral_Ioi
      z N hN hhalf_plane
  have hremainder :
      Tendsto
        (fun M : ℕ =>
          ∫ x in Set.Ioc (((N : ℕ) : ℝ)) (((M : ℕ) : ℝ)),
            ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) *
              (-z * (((x : ℝ) : ℂ) ^ (-(z + 1)))))
        atTop
        (𝓝
          (∫ x in Set.Ioi (((N : ℕ) : ℝ)),
            ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) *
              (-z * (((x : ℝ) : ℂ) ^ (-(z + 1)))))) :=
    eulerMaclaurin_cpow_neg_bernoulliRemainder_Ioc_tendsto_integral_Ioi
      z N hN hhalf_plane
  let A : ℂ :=
    ∫ x in Set.Ioi (((N : ℕ) : ℝ)),
      (((x : ℝ) : ℂ) ^ (-z))
  let B : ℂ :=
    (1 / 2 : ℂ) * ((((N : ℕ) : ℝ) : ℂ) ^ (-z))
  let C : ℂ :=
    ∫ x in Set.Ioi (((N : ℕ) : ℝ)),
      ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) *
        (-z * (((x : ℝ) : ℂ) ^ (-(z + 1))))
  have hfinite_tendsto :
      Tendsto
        (fun M : ℕ =>
          ∑ n in Finset.Ioc N M, (((n : ℕ) : ℝ) : ℂ) ^ (-z))
        atTop
        (𝓝 (A + B + C)) := by
    have hfinite_eventually :
        (fun M : ℕ =>
          ∑ n in Finset.Ioc N M, (((n : ℕ) : ℝ) : ℂ) ^ (-z))
          =ᶠ[atTop]
        (fun M : ℕ =>
          (∫ x in Set.Ioc (((N : ℕ) : ℝ)) (((M : ℕ) : ℝ)),
              (((x : ℝ) : ℂ) ^ (-z))) +
            B +
            (-(1 / 2 : ℂ) * ((((M : ℕ) : ℝ) : ℂ) ^ (-z))) +
            (∫ x in Set.Ioc (((N : ℕ) : ℝ)) (((M : ℕ) : ℝ)),
              ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) *
                (-z * (((x : ℝ) : ℂ) ^ (-(z + 1)))))) := by
      filter_upwards [eventually_ge_atTop N] with M hNM
      exact hfinite M hNM
    have hassembled :
        Tendsto
          (fun M : ℕ =>
            (∫ x in Set.Ioc (((N : ℕ) : ℝ)) (((M : ℕ) : ℝ)),
                (((x : ℝ) : ℂ) ^ (-z))) +
              B +
              (-(1 / 2 : ℂ) * ((((M : ℕ) : ℝ) : ℂ) ^ (-z))) +
              (∫ x in Set.Ioc (((N : ℕ) : ℝ)) (((M : ℕ) : ℝ)),
                ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) *
                  (-z * (((x : ℝ) : ℂ) ^ (-(z + 1))))))
          atTop
          (𝓝 (A + B + 0 + C)) := by
      exact
        (((hmain.add tendsto_const_nhds).add hendpoint).add hremainder)
    have htarget : A + B + 0 + C = A + B + C := by
      calc
        A + B + 0 + C = A + B + C := by
          exact congrArg (fun x : ℂ => x + C) (add_zero (A + B))
    exact
      Eq.subst
        (motive := fun T : ℂ =>
          Tendsto
            (fun M : ℕ =>
              ∑ n in Finset.Ioc N M,
                (((n : ℕ) : ℝ) : ℂ) ^ (-z))
            atTop
            (𝓝 T))
        htarget
        (hassembled.congr' hfinite_eventually.symm)
  have hsummable_tail :
      Summable
        (fun n : ℕ =>
          if N < n then (((n : ℕ) : ℝ) : ℂ) ^ (-z) else 0) := by
    have hone_div_summable :
        Summable
          (fun n : ℕ =>
            if N < n then (1 : ℂ) / ((n : ℂ) ^ z) else 0) := by
      let f : ℕ → ℂ := fun n : ℕ => (1 : ℂ) / ((n : ℂ) ^ z)
      have hf_summable : Summable f :=
        (Complex.summable_one_div_nat_cpow (p := z)).mpr hhalf_plane
      exact hf_summable.indicator (fun n : ℕ => N < n)
    have hterms :
        (fun n : ℕ =>
          if N < n then (((n : ℕ) : ℝ) : ℂ) ^ (-z) else 0) =
        (fun n : ℕ =>
          if N < n then (1 : ℂ) / ((n : ℂ) ^ z) else 0) :=
      eulerMaclaurin_cpow_neg_postCutoffTail_terms_eq_one_div z N hN
    exact Eq.subst
      (motive := fun F : ℕ → ℂ => Summable F)
      hterms.symm
      hone_div_summable
  have hsummable_norm :
      Summable
        (fun n : ℕ =>
          ‖if N < n then (((n : ℕ) : ℝ) : ℂ) ^ (-z) else 0‖) :=
    summable_norm_iff.mpr hsummable_tail
  exact
    hasSum_of_Ioc_strictTail_tendsto_of_summable_norm
      (fun n : ℕ => (((n : ℕ) : ℝ) : ℂ) ^ (-z))
      N
      (A + B + C)
      hsummable_norm
      hfinite_tendsto

/-- Standard first-order Euler-Maclaurin formula for the zeta complex-power
post-cutoff tail in function notation.

The earlier arbitrary-function version of this statement is false without
decay and integrability hypotheses.  The owner statement here is the actual
zeta specialization used downstream: for `1 < Re z`, the function
`x ↦ x^{-z}` has enough decay for the infinite first-order
Euler-Maclaurin formula. -/
theorem eulerMaclaurin_firstOrder_postCutoffTail_hasSum_standard
    (z : ℂ)
    (N : ℕ)
    (hN : 0 < N)
    (hhalf_plane : 1 < z.re) :
    HasSum
      (fun n : ℕ =>
        if N < n then (((n : ℕ) : ℝ) : ℂ) ^ (-z) else 0)
      ((∫ x in Set.Ioi (((N : ℕ) : ℝ)),
          (((x : ℝ) : ℂ) ^ (-z))) +
        ((1 / 2 : ℂ) * ((((N : ℕ) : ℝ) : ℂ) ^ (-z))) +
        (∫ x in Set.Ioi (((N : ℕ) : ℝ)),
          ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) *
            (-z * (((x : ℝ) : ℂ) ^ (-(z + 1)))))) := by
  exact
    eulerMaclaurin_firstOrder_cpow_neg_finite_postCutoffTail_tendsto_hasSum
      z N hN hhalf_plane

/-- Specialization of the first-order Euler-Maclaurin theorem to
`f(x)=x^{-z}` in function notation. -/
theorem eulerMaclaurin_cpow_neg_postCutoffTail_function_hasSum_standard
    (z : ℂ)
    (N : ℕ)
    (hN : 0 < N)
    (hhalf_plane : 1 < z.re) :
    HasSum
      (fun n : ℕ =>
        if N < n then (((n : ℕ) : ℝ) : ℂ) ^ (-z) else 0)
      ((∫ x in Set.Ioi (((N : ℕ) : ℝ)),
          (((x : ℝ) : ℂ) ^ (-z))) +
        ((1 / 2 : ℂ) * ((((N : ℕ) : ℝ) : ℂ) ^ (-z))) +
        (∫ x in Set.Ioi (((N : ℕ) : ℝ)),
          ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) *
            (-z * (((x : ℝ) : ℂ) ^ (-(z + 1)))))) := by
  exact
    eulerMaclaurin_firstOrder_postCutoffTail_hasSum_standard
      z N hN hhalf_plane

/-- Fold the derivative into the periodic-Bernoulli integral for
`f(x)=x^{-z}`. -/
theorem eulerMaclaurin_cpow_neg_derivative_integral_eq_factored_remainder
    (z : ℂ)
    (N : ℕ) :
    (∫ x in Set.Ioi (((N : ℕ) : ℝ)),
      ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) *
        (-z * (((x : ℝ) : ℂ) ^ (-(z + 1))))) =
      -z *
        (∫ x in Set.Ioi (((N : ℕ) : ℝ)),
          ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) *
            (((x : ℝ) : ℂ) ^ (-(z + 1)))) := by
  let g : ℝ → ℂ := fun x : ℝ =>
    ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) *
      (((x : ℝ) : ℂ) ^ (-(z + 1)))
  have hpoint :
      (fun x : ℝ =>
        ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) *
          (-z * (((x : ℝ) : ℂ) ^ (-(z + 1))))) =
        (fun x : ℝ => -z * g x) := by
    exact funext
      (fun x : ℝ => by
        let a : ℂ := ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ)
        let b : ℂ := (((x : ℝ) : ℂ) ^ (-(z + 1)))
        calc
          a * (-z * b) = (a * -z) * b := by
            exact (mul_assoc a (-z) b).symm
          _ = (-z * a) * b := by
            exact congrArg (fun w : ℂ => w * b) (mul_comm a (-z))
          _ = -z * (a * b) := by
            exact mul_assoc (-z) a b)
  have hintegral_point :
      (∫ x in Set.Ioi (((N : ℕ) : ℝ)),
        ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) *
          (-z * (((x : ℝ) : ℂ) ^ (-(z + 1))))) =
        ∫ x in Set.Ioi (((N : ℕ) : ℝ)), -z * g x := by
    exact congrArg
      (fun F : ℝ → ℂ => ∫ x in Set.Ioi (((N : ℕ) : ℝ)), F x)
      hpoint
  have hlinear :
      (∫ x in Set.Ioi (((N : ℕ) : ℝ)), -z * g x) =
        -z *
          (∫ x in Set.Ioi (((N : ℕ) : ℝ)), g x) := by
    exact integral_mul_left (-z) g
  exact Eq.trans hintegral_point hlinear

/-- Generic first-order Euler-Maclaurin formula for the infinite post-cutoff
tail of `x ↦ x^{-z}`.

For any positive natural cutoff `N` and `1 < Re z`, the Dirichlet tail after
`N` has sum equal to the improper integral, the endpoint correction, and the
periodic Bernoulli derivative remainder.  This is the canonical non-zeta
Euler-Maclaurin owner theorem consumed by the zeta cutoff specialization. -/
theorem eulerMaclaurin_cpow_neg_postCutoffTail_firstOrder_hasSum_standard
    (z : ℂ)
    (N : ℕ)
    (hN : 0 < N)
    (hhalf_plane : 1 < z.re) :
    HasSum
      (fun n : ℕ =>
        if N < n then
          (1 : ℂ) / ((n : ℂ) ^ z)
        else
          0)
      ((∫ x in Set.Ioi (((N : ℕ) : ℝ)),
          (((x : ℝ) : ℂ) ^ (-z))) +
        ((1 / 2 : ℂ) * (1 / (((N : ℕ) : ℂ) ^ z))) +
        (-z *
          (∫ x in Set.Ioi (((N : ℕ) : ℝ)),
            ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) *
              (((x : ℝ) : ℂ) ^ (-(z + 1))))) := by
  have hfunction :
      HasSum
        (fun n : ℕ =>
          if N < n then (((n : ℕ) : ℝ) : ℂ) ^ (-z) else 0)
        ((∫ x in Set.Ioi (((N : ℕ) : ℝ)),
            (((x : ℝ) : ℂ) ^ (-z))) +
          ((1 / 2 : ℂ) * ((((N : ℕ) : ℝ) : ℂ) ^ (-z))) +
          (∫ x in Set.Ioi (((N : ℕ) : ℝ)),
            ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) *
              (-z * (((x : ℝ) : ℂ) ^ (-(z + 1)))))) :=
    eulerMaclaurin_cpow_neg_postCutoffTail_function_hasSum_standard
      z N hN hhalf_plane
  have hterm_eq :
      (fun n : ℕ =>
        if N < n then (((n : ℕ) : ℝ) : ℂ) ^ (-z) else 0) =
        (fun n : ℕ =>
          if N < n then
            (1 : ℂ) / ((n : ℂ) ^ z)
          else
            0) :=
    eulerMaclaurin_cpow_neg_postCutoffTail_terms_eq_one_div z N hN
  have hsum_eq :
      ((∫ x in Set.Ioi (((N : ℕ) : ℝ)),
          (((x : ℝ) : ℂ) ^ (-z))) +
        ((1 / 2 : ℂ) * ((((N : ℕ) : ℝ) : ℂ) ^ (-z))) +
        (∫ x in Set.Ioi (((N : ℕ) : ℝ)),
          ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) *
            (-z * (((x : ℝ) : ℂ) ^ (-(z + 1)))))) =
        ((∫ x in Set.Ioi (((N : ℕ) : ℝ)),
          (((x : ℝ) : ℂ) ^ (-z))) +
        ((1 / 2 : ℂ) * (1 / (((N : ℕ) : ℂ) ^ z))) +
        (-z *
          (∫ x in Set.Ioi (((N : ℕ) : ℝ)),
            ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) *
              (((x : ℝ) : ℂ) ^ (-(z + 1)))))) := by
    have hendpoint :
        ((1 / 2 : ℂ) * ((((N : ℕ) : ℝ) : ℂ) ^ (-z))) =
          ((1 / 2 : ℂ) * (1 / (((N : ℕ) : ℂ) ^ z))) := by
      have hcast : (((N : ℕ) : ℝ) : ℂ) = (N : ℂ) :=
        Complex.ofReal_natCast N
      have hpow :
          ((((N : ℕ) : ℝ) : ℂ) ^ (-z)) =
            (N : ℂ) ^ (-z) :=
        congrArg (fun w : ℂ => w ^ (-z)) hcast
      have hrecip :
          (1 : ℂ) / ((N : ℂ) ^ z) = (N : ℂ) ^ (-z) :=
        eulerMaclaurin_positiveNat_one_div_cpow_eq_cpow_neg z hN
      exact congrArg (fun W : ℂ => (1 / 2 : ℂ) * W)
        (Eq.trans hpow hrecip.symm)
    have hremainder :
        (∫ x in Set.Ioi (((N : ℕ) : ℝ)),
          ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) *
            (-z * (((x : ℝ) : ℂ) ^ (-(z + 1))))) =
          -z *
            (∫ x in Set.Ioi (((N : ℕ) : ℝ)),
              ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) *
                (((x : ℝ) : ℂ) ^ (-(z + 1)))) :=
      eulerMaclaurin_cpow_neg_derivative_integral_eq_factored_remainder z N
    exact congrArg₂
      (fun A B : ℂ =>
        (∫ x in Set.Ioi (((N : ℕ) : ℝ)),
          (((x : ℝ) : ℂ) ^ (-z))) + A + B)
      hendpoint
      hremainder
  exact
    Eq.subst
      (motive := fun p : (ℕ → ℂ) × ℂ => HasSum p.1 p.2)
      (Prod.ext hterm_eq hsum_eq)
      hfunction

/-- Specialization of the generic Euler-Maclaurin tail formula to the owner
cutoff `⌊2 + ‖z‖⌋₊`, before folding the Bernoulli integral into the named core. -/
theorem eulerMaclaurin_riemannZeta_postCutoffTail_firstOrder_unfolded_hasSum
    (z : ℂ)
    (hhalf_plane : 1 < z.re) :
    HasSum
      (fun n : ℕ =>
        if eulerMaclaurinPoleClearedZetaCutoff z < n then
          (1 : ℂ) / ((n : ℂ) ^ z)
        else
          0)
      ((∫ x in Set.Ioi (((eulerMaclaurinPoleClearedZetaCutoff z : ℕ) : ℝ)),
          (((x : ℝ) : ℂ) ^ (-z))) +
        ((1 / 2 : ℂ) *
          (1 / (((eulerMaclaurinPoleClearedZetaCutoff z : ℕ) : ℂ) ^ z)) +
        (-z *
          (∫ x in Set.Ioi
            (((eulerMaclaurinPoleClearedZetaCutoff z : ℕ) : ℝ)),
            ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) *
              (((x : ℝ) : ℂ) ^ (-(z + 1)))))) := by
  exact
    eulerMaclaurin_cpow_neg_postCutoffTail_firstOrder_hasSum_standard
      z
      (eulerMaclaurinPoleClearedZetaCutoff z)
      (eulerMaclaurinPoleClearedZetaCutoff_pos z)
      hhalf_plane

/-- Standard first-order Euler-Maclaurin formula for the convergent
post-cutoff Dirichlet tail of `x ↦ x^{-z}`.

This is the canonical analytic owner theorem: for `1 < Re z` and
`N = ⌊2 + ‖z‖⌋₊`, the post-cutoff Dirichlet tail has sum equal to the
improper integral main term, the endpoint correction, and the periodic
Bernoulli remainder.  It is the precise theorem supplied by the classical
Euler-Maclaurin formula with periodic Bernoulli function `B₁`; cf. Apostol,
Analytic Number Theory, Ch. 3. -/
theorem eulerMaclaurin_riemannZeta_postCutoffTail_firstOrder_hasSum_standard
    (z : ℂ)
    (hhalf_plane : 1 < z.re) :
    HasSum
      (fun n : ℕ =>
        if eulerMaclaurinPoleClearedZetaCutoff z < n then
          (1 : ℂ) / ((n : ℂ) ^ z)
        else
          0)
      ((∫ x in Set.Ioi (((eulerMaclaurinPoleClearedZetaCutoff z : ℕ) : ℝ)),
          (((x : ℝ) : ℂ) ^ (-z))) +
        ((1 / 2 : ℂ) *
          (1 / (((eulerMaclaurinPoleClearedZetaCutoff z : ℕ) : ℂ) ^ z)) +
        (-z * eulerMaclaurinPoleClearedZetaBernoulliIntegralCore z)) := by
  unfold eulerMaclaurinPoleClearedZetaBernoulliIntegralCore
  exact
    eulerMaclaurin_riemannZeta_postCutoffTail_firstOrder_unfolded_hasSum
      z hhalf_plane

/-- Transport the standard first-order Euler-Maclaurin tail formula into the
raw owner terms `MainTerm`, `EndpointTerm`, and
`BernoulliIntegralRemainder`. -/
theorem eulerMaclaurin_riemannZeta_postCutoffTail_ownerTerms_hasSum
    (z : ℂ)
    (hhalf_plane : 1 < z.re) :
    HasSum
      (fun n : ℕ =>
        if eulerMaclaurinPoleClearedZetaCutoff z < n then
          (1 : ℂ) / ((n : ℂ) ^ z)
        else
          0)
      (eulerMaclaurinZetaMainTerm z +
        eulerMaclaurinZetaEndpointTerm z +
        eulerMaclaurinZetaBernoulliIntegralRemainder z) := by
  have hstandard :
      HasSum
        (fun n : ℕ =>
          if eulerMaclaurinPoleClearedZetaCutoff z < n then
            (1 : ℂ) / ((n : ℂ) ^ z)
          else
            0)
        ((∫ x in Set.Ioi (((eulerMaclaurinPoleClearedZetaCutoff z : ℕ) : ℝ)),
            (((x : ℝ) : ℂ) ^ (-z))) +
          ((1 / 2 : ℂ) *
            (1 / (((eulerMaclaurinPoleClearedZetaCutoff z : ℕ) : ℂ) ^ z)) +
          (-z * eulerMaclaurinPoleClearedZetaBernoulliIntegralCore z)) :=
    eulerMaclaurin_riemannZeta_postCutoffTail_firstOrder_hasSum_standard
      z hhalf_plane
  have hmain :
      (∫ x in Set.Ioi (((eulerMaclaurinPoleClearedZetaCutoff z : ℕ) : ℝ)),
          (((x : ℝ) : ℂ) ^ (-z))) =
        eulerMaclaurinZetaMainTerm z :=
    eulerMaclaurin_riemannZeta_postCutoffTail_integralMain_eq_mainTerm_standard
      z hhalf_plane
  have hendpoint :
      (1 / 2 : ℂ) *
          (1 / (((eulerMaclaurinPoleClearedZetaCutoff z : ℕ) : ℂ) ^ z)) =
        eulerMaclaurinZetaEndpointTerm z :=
    eulerMaclaurin_riemannZeta_postCutoffTail_endpoint_eq_endpointTerm z
  have hremainder :
      -z * eulerMaclaurinPoleClearedZetaBernoulliIntegralCore z =
        eulerMaclaurinZetaBernoulliIntegralRemainder z :=
    eulerMaclaurin_riemannZeta_postCutoffTail_remainderSign_eq_remainderTerm z
  have hsum_eq :
      (∫ x in Set.Ioi (((eulerMaclaurinPoleClearedZetaCutoff z : ℕ) : ℝ)),
          (((x : ℝ) : ℂ) ^ (-z))) +
          ((1 / 2 : ℂ) *
              (1 / (((eulerMaclaurinPoleClearedZetaCutoff z : ℕ) : ℂ) ^ z)) +
            (-z * eulerMaclaurinPoleClearedZetaBernoulliIntegralCore z)) =
        eulerMaclaurinZetaMainTerm z +
          eulerMaclaurinZetaEndpointTerm z +
          eulerMaclaurinZetaBernoulliIntegralRemainder z := by
    exact congrArg₂
      (fun A B : ℂ => A + B)
      hmain
      (congrArg₂
        (fun A B : ℂ => A + B)
        hendpoint
        hremainder)
  exact
    Eq.subst
      (motive := fun S : ℂ =>
        HasSum
          (fun n : ℕ =>
            if eulerMaclaurinPoleClearedZetaCutoff z < n then
              (1 : ℂ) / ((n : ℂ) ^ z)
            else
              0)
          S)
      hsum_eq
      hstandard

/-- Defect of the raw zeta Euler-Maclaurin tail identity.  The boundary-line
continuation theorem is stated as vanishing of this holomorphic defect. -/
noncomputable def eulerMaclaurin_riemannZeta_tailIdentityDefect
    (z : ℂ) : ℂ :=
  (riemannZeta z - eulerMaclaurinZetaFinitePart z) -
    (eulerMaclaurinZetaMainTerm z +
      eulerMaclaurinZetaEndpointTerm z +
      eulerMaclaurinZetaBernoulliIntegralRemainder z)

/-- Fixed-cutoff finite Dirichlet window.  This is the holomorphic object used
in the identity theorem; unlike the height-dependent owner cutoff, `N` is a
parameter and therefore does not introduce floor-jump discontinuities. -/
noncomputable def eulerMaclaurinZetaFinitePartWithCutoff
    (N : ℕ)
    (z : ℂ) : ℂ :=
  ∑ n ∈ Finset.Icc 1 N, 1 / (((n : ℕ) : ℂ) ^ z)

/-- Fixed-cutoff integral main term for the raw zeta Euler-Maclaurin formula. -/
noncomputable def eulerMaclaurinZetaMainTermWithCutoff
    (N : ℕ)
    (z : ℂ) : ℂ :=
  (((N : ℕ) : ℂ) ^ ((1 : ℂ) - z)) / (z - 1)

/-- Fixed-cutoff endpoint term for the raw zeta Euler-Maclaurin formula. -/
noncomputable def eulerMaclaurinZetaEndpointTermWithCutoff
    (N : ℕ)
    (z : ℂ) : ℂ :=
  (1 / 2 : ℂ) * (1 / (((N : ℕ) : ℂ) ^ z))

/-- Fixed-cutoff Bernoulli integral core. -/
noncomputable def eulerMaclaurinZetaBernoulliIntegralCoreWithCutoff
    (N : ℕ)
    (z : ℂ) : ℂ :=
  ∫ x in Set.Ioi (((N : ℕ) : ℝ)),
    ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) *
      (((x : ℝ) : ℂ) ^ (-(z + 1)))

/-- Fixed-cutoff Bernoulli remainder for the raw zeta Euler-Maclaurin formula. -/
noncomputable def eulerMaclaurinZetaBernoulliIntegralRemainderWithCutoff
    (N : ℕ)
    (z : ℂ) : ℂ :=
  -z * eulerMaclaurinZetaBernoulliIntegralCoreWithCutoff N z

/-- Fixed-cutoff Euler-Maclaurin tail defect.  This is the correct object for
holomorphic identity-theorem arguments. -/
noncomputable def eulerMaclaurin_riemannZeta_fixedCutoffTailIdentityDefect
    (N : ℕ)
    (z : ℂ) : ℂ :=
  (riemannZeta z - eulerMaclaurinZetaFinitePartWithCutoff N z) -
    (eulerMaclaurinZetaMainTermWithCutoff N z +
      eulerMaclaurinZetaEndpointTermWithCutoff N z +
      eulerMaclaurinZetaBernoulliIntegralRemainderWithCutoff N z)

/-- The height-dependent owner defect agrees pointwise with the fixed-cutoff
defect at the cutoff chosen by that point. -/
theorem eulerMaclaurin_riemannZeta_tailIdentityDefect_eq_fixedCutoffDefect
    (z : ℂ) :
    eulerMaclaurin_riemannZeta_tailIdentityDefect z =
      eulerMaclaurin_riemannZeta_fixedCutoffTailIdentityDefect
        (eulerMaclaurinPoleClearedZetaCutoff z) z := by
  unfold eulerMaclaurin_riemannZeta_tailIdentityDefect
  unfold eulerMaclaurin_riemannZeta_fixedCutoffTailIdentityDefect
  unfold eulerMaclaurinZetaFinitePartWithCutoff
  unfold eulerMaclaurinZetaMainTermWithCutoff
  unfold eulerMaclaurinZetaEndpointTermWithCutoff
  unfold eulerMaclaurinZetaBernoulliIntegralRemainderWithCutoff
  unfold eulerMaclaurinZetaBernoulliIntegralCoreWithCutoff
  unfold eulerMaclaurinZetaFinitePart
  unfold eulerMaclaurinZetaMainTerm
  unfold eulerMaclaurinZetaEndpointTerm
  unfold eulerMaclaurinZetaBernoulliIntegralRemainder
  unfold eulerMaclaurinPoleClearedZetaBernoulliIntegralCore
  rfl

/-- In the convergent half-plane, removing a fixed finite Dirichlet window from
`ζ(s)` leaves the fixed post-cutoff Dirichlet tail as a `HasSum`. -/
theorem eulerMaclaurin_riemannZeta_fixedCutoff_halfPlane_finite_split_tail_hasSum
    (N : ℕ)
    (z : ℂ)
    (hz : 1 < z.re) :
    HasSum
      (fun n : ℕ =>
        if N < n then
          (1 : ℂ) / ((n : ℂ) ^ z)
        else
          0)
      (riemannZeta z - eulerMaclaurinZetaFinitePartWithCutoff N z) := by
  let f : ℕ → ℂ := fun n : ℕ => (1 : ℂ) / ((n : ℂ) ^ z)
  have hf_summable : Summable f :=
    (Complex.summable_one_div_nat_cpow (p := z)).mpr hz
  have hζ_eq : riemannZeta z = ∑' n : ℕ, f n :=
    zeta_eq_tsum_one_div_nat_cpow hz
  have hf_has_tsum : HasSum f (∑' n : ℕ, f n) :=
    hf_summable.hasSum
  have hf_has_zeta : HasSum f (riemannZeta z) :=
    Eq.subst
      (motive := fun S : ℂ => HasSum f S)
      hζ_eq.symm
      hf_has_tsum
  have htail_compl :
      HasSum
        (fun x : {n : ℕ // n ∉ Finset.Icc 1 N} => f x)
        (riemannZeta z - ∑ n ∈ Finset.Icc 1 N, f n) :=
    ((Finset.Icc 1 N).hasSum_iff_compl).mp hf_has_zeta
  have htail_indicator :
      HasSum
        ({n : ℕ | n ∉ Finset.Icc 1 N}.indicator f)
        (riemannZeta z - ∑ n ∈ Finset.Icc 1 N, f n) := by
    exact
      (hasSum_subtype_iff_indicator
        (s := {n : ℕ | n ∉ Finset.Icc 1 N})
        (f := f)).mp
        htail_compl
  have hf_zero : f 0 = 0 := by
    exact riemannZeta_dirichletTerm_zero_of_one_lt_re hz
  have hindicator :
      ({n : ℕ | n ∉ Finset.Icc 1 N}.indicator f) =
        (fun k : ℕ => if N < k then f k else 0) :=
    funext
      (fun n : ℕ =>
        nat_not_Icc_one_indicator_eq_cutoff_if_of_zero f N n hf_zero)
  have htail_if :
      HasSum
        (fun k : ℕ => if N < k then f k else 0)
        (riemannZeta z - ∑ n ∈ Finset.Icc 1 N, f n) :=
    Eq.subst
      (motive := fun g : ℕ → ℂ =>
        HasSum g (riemannZeta z - ∑ n ∈ Finset.Icc 1 N, f n))
      hindicator
      htail_indicator
  unfold eulerMaclaurinZetaFinitePartWithCutoff
  exact htail_if

/-- Fixed-cutoff improper-integral main term in owner normalization. -/
theorem eulerMaclaurin_fixedCutoff_integralMain_eq_mainTerm
    (N : ℕ)
    (hN : 0 < N)
    (z : ℂ)
    (hhalf_plane : 1 < z.re) :
    (∫ x in Set.Ioi (((N : ℕ) : ℝ)),
        (((x : ℝ) : ℂ) ^ (-z))) =
      eulerMaclaurinZetaMainTermWithCutoff N z := by
  unfold eulerMaclaurinZetaMainTermWithCutoff
  have hformula :
      (∫ x in Set.Ioi (((N : ℕ) : ℝ)),
          (((x : ℝ) : ℂ) ^ (-z))) =
        -((((N : ℕ) : ℝ) : ℂ) ^ ((-z) + 1)) / ((-z) + 1) := by
    exact
      integral_Ioi_cpow_of_lt
        (eulerMaclaurin_cpow_neg_re_lt_neg_one_of_one_lt_re hhalf_plane)
        (Nat.cast_pos.mpr hN)
  let A : ℂ := ((N : ℕ) : ℂ)
  have hbase :
      (((N : ℕ) : ℝ) : ℂ) = A :=
    Complex.ofReal_natCast N
  have hexponent :
      (-z) + 1 = (1 : ℂ) - z := by
    calc
      (-z) + 1 = (1 : ℂ) + (-z) := by
        exact add_comm (-z) (1 : ℂ)
      _ = (1 : ℂ) - z := by
        exact (sub_eq_add_neg (1 : ℂ) z).symm
  have hden :
      (-z) + 1 = -((z - 1)) := by
    calc
      (-z) + 1 = (1 : ℂ) - z :=
        hexponent
      _ = -(z - 1) := by
        exact (neg_sub z (1 : ℂ)).symm
  have hpow :
      ((((N : ℕ) : ℝ) : ℂ) ^ ((-z) + 1)) =
        A ^ ((1 : ℂ) - z) := by
    exact congrArg₂ (fun b e : ℂ => b ^ e) hbase hexponent
  have hnormal :
      -((((N : ℕ) : ℝ) : ℂ) ^ ((-z) + 1)) / ((-z) + 1) =
        A ^ ((1 : ℂ) - z) / (z - 1) := by
    calc
      -((((N : ℕ) : ℝ) : ℂ) ^ ((-z) + 1)) / ((-z) + 1) =
          -(A ^ ((1 : ℂ) - z)) / ((-z) + 1) := by
        exact congrArg
          (fun W : ℂ => -W / ((-z) + 1))
          hpow
      _ = -(A ^ ((1 : ℂ) - z)) / (-(z - 1)) := by
        exact congrArg
          (fun D : ℂ => -(A ^ ((1 : ℂ) - z)) / D)
          hden
      _ = A ^ ((1 : ℂ) - z) / (z - 1) := by
        exact neg_div_neg_eq (A ^ ((1 : ℂ) - z)) (z - 1)
  exact Eq.trans hformula hnormal

/-- Fixed-cutoff Euler-Maclaurin tail formula in owner term notation. -/
theorem eulerMaclaurin_riemannZeta_fixedCutoff_postCutoffTail_ownerTerms_hasSum
    (N : ℕ)
    (hN : 0 < N)
    (z : ℂ)
    (hhalf_plane : 1 < z.re) :
    HasSum
      (fun n : ℕ =>
        if N < n then
          (1 : ℂ) / ((n : ℂ) ^ z)
        else
          0)
      (eulerMaclaurinZetaMainTermWithCutoff N z +
        eulerMaclaurinZetaEndpointTermWithCutoff N z +
        eulerMaclaurinZetaBernoulliIntegralRemainderWithCutoff N z) := by
  have hstandard :
      HasSum
        (fun n : ℕ =>
          if N < n then
            (1 : ℂ) / ((n : ℂ) ^ z)
          else
            0)
        ((∫ x in Set.Ioi (((N : ℕ) : ℝ)),
            (((x : ℝ) : ℂ) ^ (-z))) +
          ((1 / 2 : ℂ) * (1 / (((N : ℕ) : ℂ) ^ z))) +
          (-z *
            (∫ x in Set.Ioi (((N : ℕ) : ℝ)),
              ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) *
                (((x : ℝ) : ℂ) ^ (-(z + 1)))))) :=
    eulerMaclaurin_cpow_neg_postCutoffTail_firstOrder_hasSum_standard
      z N hN hhalf_plane
  have hmain :
      (∫ x in Set.Ioi (((N : ℕ) : ℝ)),
          (((x : ℝ) : ℂ) ^ (-z))) =
        eulerMaclaurinZetaMainTermWithCutoff N z :=
    eulerMaclaurin_fixedCutoff_integralMain_eq_mainTerm N hN z hhalf_plane
  have hendpoint :
      ((1 / 2 : ℂ) * (1 / (((N : ℕ) : ℂ) ^ z))) =
        eulerMaclaurinZetaEndpointTermWithCutoff N z := by
    unfold eulerMaclaurinZetaEndpointTermWithCutoff
    rfl
  have hremainder :
      (-z *
        (∫ x in Set.Ioi (((N : ℕ) : ℝ)),
          ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) *
            (((x : ℝ) : ℂ) ^ (-(z + 1))))) =
        eulerMaclaurinZetaBernoulliIntegralRemainderWithCutoff N z := by
    unfold eulerMaclaurinZetaBernoulliIntegralRemainderWithCutoff
    unfold eulerMaclaurinZetaBernoulliIntegralCoreWithCutoff
    rfl
  have hsum_eq :
      ((∫ x in Set.Ioi (((N : ℕ) : ℝ)),
          (((x : ℝ) : ℂ) ^ (-z))) +
          ((1 / 2 : ℂ) * (1 / (((N : ℕ) : ℂ) ^ z))) +
          (-z *
            (∫ x in Set.Ioi (((N : ℕ) : ℝ)),
              ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) *
                (((x : ℝ) : ℂ) ^ (-(z + 1)))))) =
        eulerMaclaurinZetaMainTermWithCutoff N z +
          eulerMaclaurinZetaEndpointTermWithCutoff N z +
          eulerMaclaurinZetaBernoulliIntegralRemainderWithCutoff N z := by
    exact congrArg₂
      (fun A B : ℂ => A + B)
      hmain
      (congrArg₂
        (fun A B : ℂ => A + B)
        hendpoint
        hremainder)
  exact
    Eq.subst
      (motive := fun S : ℂ =>
        HasSum
          (fun n : ℕ =>
            if N < n then
              (1 : ℂ) / ((n : ℂ) ^ z)
            else
              0)
          S)
      hsum_eq
      hstandard

/-- Vanishing of the Euler-Maclaurin tail defect is exactly the desired
tail identity. -/
theorem eulerMaclaurin_riemannZeta_tailIdentity_of_defect_eq_zero
    {z : ℂ}
    (hdefect : eulerMaclaurin_riemannZeta_tailIdentityDefect z = 0) :
    riemannZeta z - eulerMaclaurinZetaFinitePart z =
      eulerMaclaurinZetaMainTerm z +
        eulerMaclaurinZetaEndpointTerm z +
        eulerMaclaurinZetaBernoulliIntegralRemainder z := by
  unfold eulerMaclaurin_riemannZeta_tailIdentityDefect at hdefect
  exact sub_eq_zero.mp hdefect

/-- In the convergent half-plane, the Euler-Maclaurin tail defect vanishes by
uniqueness of the post-cutoff `HasSum`: the Dirichlet split and the
Euler-Maclaurin tail formula have the same summand. -/
theorem eulerMaclaurin_riemannZeta_tailIdentityDefect_eq_zero_on_halfPlane
    (z : ℂ)
    (hhalf_plane : 1 < z.re) :
    eulerMaclaurin_riemannZeta_tailIdentityDefect z = 0 := by
  have hsplit :
      HasSum
        (fun n : ℕ =>
          if eulerMaclaurinPoleClearedZetaCutoff z < n then
            (1 : ℂ) / ((n : ℂ) ^ z)
          else
            0)
        (riemannZeta z - eulerMaclaurinZetaFinitePart z) :=
    eulerMaclaurin_riemannZeta_halfPlane_finite_split_tail_hasSum
      z hhalf_plane
  have htail :
      HasSum
        (fun n : ℕ =>
          if eulerMaclaurinPoleClearedZetaCutoff z < n then
            (1 : ℂ) / ((n : ℂ) ^ z)
          else
            0)
        (eulerMaclaurinZetaMainTerm z +
          eulerMaclaurinZetaEndpointTerm z +
          eulerMaclaurinZetaBernoulliIntegralRemainder z) :=
    eulerMaclaurin_riemannZeta_postCutoffTail_ownerTerms_hasSum
      z hhalf_plane
  have hidentity :
      riemannZeta z - eulerMaclaurinZetaFinitePart z =
        eulerMaclaurinZetaMainTerm z +
          eulerMaclaurinZetaEndpointTerm z +
          eulerMaclaurinZetaBernoulliIntegralRemainder z :=
    hsplit.unique htail
  unfold eulerMaclaurin_riemannZeta_tailIdentityDefect
  exact sub_eq_zero.mpr hidentity

/-- First-order Euler-Maclaurin evaluation of the convergent post-cutoff
Dirichlet tail.

This is the standard Euler-Maclaurin theorem for `x ↦ x^{-z}` on the ray
`[N,∞)`, with `N = eulerMaclaurinPoleClearedZetaCutoff z`:
the post-cutoff Dirichlet tail has sum
`N^(1-z)/(z-1) + (1/2)N^{-z} - z∫_N^∞ B₁({x})x^{-z-1}dx`. -/
theorem eulerMaclaurin_riemannZeta_postCutoffTail_eulerMaclaurin_hasSum_standard
    (z : ℂ)
    (hz_one : 1 ≤ z.re)
    (hz_two : z.re ≤ 2)
    (hhalf_plane : 1 < z.re) :
    HasSum
      (fun n : ℕ =>
        if eulerMaclaurinPoleClearedZetaCutoff z < n then
          (1 : ℂ) / ((n : ℂ) ^ z)
        else
          0)
      (eulerMaclaurinZetaMainTerm z +
        eulerMaclaurinZetaEndpointTerm z +
        eulerMaclaurinZetaBernoulliIntegralRemainder z) := by
  exact
    eulerMaclaurin_riemannZeta_postCutoffTail_ownerTerms_hasSum
      z hhalf_plane

/-- `ζ` is holomorphic on the fixed-cutoff punctured strip, where the pole
point `1` is excluded. -/
theorem eulerMaclaurin_riemannZeta_holomorphicOn_fixedCutoff_puncturedStrip :
    DifferentiableOn ℂ
      riemannZeta
      ({z : ℂ | 0 < z.re ∧ z.re < 2 ∧ z ≠ 1}) := by
  intro z hz
  exact (differentiableAt_riemannZeta hz.2.2).differentiableWithinAt

/-- Fixed finite Dirichlet polynomial is holomorphic in the complex variable. -/
theorem eulerMaclaurinZetaFinitePartWithCutoff_holomorphicOn_puncturedStrip
    (N : ℕ) :
    DifferentiableOn ℂ
      (eulerMaclaurinZetaFinitePartWithCutoff N)
      ({z : ℂ | 0 < z.re ∧ z.re < 2 ∧ z ≠ 1}) := by
  unfold eulerMaclaurinZetaFinitePartWithCutoff
  exact
    DifferentiableOn.sum
      (fun n hn => by
        have hn_bounds : n ∈ Finset.Icc 1 N := hn
        have hn_one : 1 ≤ n := (Finset.mem_Icc.mp hn_bounds).1
        have hn_pos : 0 < n := lt_of_lt_of_le Nat.zero_lt_one hn_one
        have hbase_ne : ((n : ℕ) : ℂ) ≠ 0 :=
          Nat.cast_ne_zero.mpr (Nat.ne_of_gt hn_pos)
        have hden :
            DifferentiableOn ℂ
              (fun z : ℂ => (((n : ℕ) : ℂ) ^ z))
              ({z : ℂ | 0 < z.re ∧ z.re < 2 ∧ z ≠ 1}) :=
          differentiableOn_id.const_cpow (Or.inl hbase_ne)
        have hnum :
            DifferentiableOn ℂ
              (fun _ : ℂ => (1 : ℂ))
              ({z : ℂ | 0 < z.re ∧ z.re < 2 ∧ z ≠ 1}) :=
          differentiableOn_const (1 : ℂ)
        exact
          hnum.div hden
            (fun z hz => by
              intro hzero
              have hbase_zero : ((n : ℕ) : ℂ) = 0 :=
                (Complex.cpow_eq_zero_iff ((n : ℕ) : ℂ) z).mp hzero |>.1
              exact hbase_ne hbase_zero))

/-- Fixed-cutoff main term is holomorphic on the punctured strip. -/
theorem eulerMaclaurinZetaMainTermWithCutoff_holomorphicOn_puncturedStrip
    (N : ℕ)
    (hN : 0 < N) :
    DifferentiableOn ℂ
      (eulerMaclaurinZetaMainTermWithCutoff N)
      ({z : ℂ | 0 < z.re ∧ z.re < 2 ∧ z ≠ 1}) := by
  unfold eulerMaclaurinZetaMainTermWithCutoff
  have hbase_ne : ((N : ℕ) : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.ne_of_gt hN)
  have hone :
      DifferentiableOn ℂ
        (fun _ : ℂ => (1 : ℂ))
        ({z : ℂ | 0 < z.re ∧ z.re < 2 ∧ z ≠ 1}) :=
    differentiableOn_const (1 : ℂ)
  have hid :
      DifferentiableOn ℂ
        (fun z : ℂ => z)
        ({z : ℂ | 0 < z.re ∧ z.re < 2 ∧ z ≠ 1}) :=
    differentiableOn_id
  have hexponent :
      DifferentiableOn ℂ
        (fun z : ℂ => (1 : ℂ) - z)
        ({z : ℂ | 0 < z.re ∧ z.re < 2 ∧ z ≠ 1}) :=
    hone.sub hid
  have hnum :
      DifferentiableOn ℂ
        (fun z : ℂ => ((N : ℕ) : ℂ) ^ ((1 : ℂ) - z))
        ({z : ℂ | 0 < z.re ∧ z.re < 2 ∧ z ≠ 1}) :=
    hexponent.const_cpow (Or.inl hbase_ne)
  have hden :
      DifferentiableOn ℂ
        (fun z : ℂ => z - 1)
        ({z : ℂ | 0 < z.re ∧ z.re < 2 ∧ z ≠ 1}) :=
    hid.sub hone
  exact
    hnum.div hden
      (fun z hz => sub_ne_zero.mpr hz.2.2)

/-- Fixed-cutoff endpoint term is holomorphic on the punctured strip. -/
theorem eulerMaclaurinZetaEndpointTermWithCutoff_holomorphicOn_puncturedStrip
    (N : ℕ)
    (hN : 0 < N) :
    DifferentiableOn ℂ
      (eulerMaclaurinZetaEndpointTermWithCutoff N)
      ({z : ℂ | 0 < z.re ∧ z.re < 2 ∧ z ≠ 1}) := by
  unfold eulerMaclaurinZetaEndpointTermWithCutoff
  have hbase_ne : ((N : ℕ) : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.ne_of_gt hN)
  have hid :
      DifferentiableOn ℂ
        (fun z : ℂ => z)
        ({z : ℂ | 0 < z.re ∧ z.re < 2 ∧ z ≠ 1}) :=
    differentiableOn_id
  have hden :
      DifferentiableOn ℂ
        (fun z : ℂ => (((N : ℕ) : ℂ) ^ z))
        ({z : ℂ | 0 < z.re ∧ z.re < 2 ∧ z ≠ 1}) :=
    hid.const_cpow (Or.inl hbase_ne)
  have hrecip :
      DifferentiableOn ℂ
        (fun z : ℂ => (1 : ℂ) / (((N : ℕ) : ℂ) ^ z))
        ({z : ℂ | 0 < z.re ∧ z.re < 2 ∧ z ≠ 1}) :=
    (differentiableOn_const (1 : ℂ)).div hden
      (fun z hz => by
        intro hzero
        have hbase_zero : ((N : ℕ) : ℂ) = 0 :=
          (Complex.cpow_eq_zero_iff ((N : ℕ) : ℂ) z).mp hzero |>.1
        exact hbase_ne hbase_zero)
  have hhalf :
      DifferentiableOn ℂ
        (fun _ : ℂ => (1 / 2 : ℂ))
        ({z : ℂ | 0 < z.re ∧ z.re < 2 ∧ z ≠ 1}) :=
    differentiableOn_const (1 / 2 : ℂ)
  exact hhalf.mul hrecip

/-- Pointwise parameter-holomorphicity of the fixed-cutoff Bernoulli kernel.

For each positive real `x`, the parameter dependence
`z ↦ B₁({x}) x^(-(z+1))` is entire.  This is the local kernel theorem used
before applying differentiation under the improper integral. -/
theorem eulerMaclaurinBernoulliKernel_parameter_differentiableOn
    (x : ℝ)
    (hx : 0 < x) :
    DifferentiableOn ℂ
      (fun z : ℂ =>
        ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) *
          (((x : ℝ) : ℂ) ^ (-(z + 1))))
      ({z : ℂ | 0 < z.re ∧ z.re < 2 ∧ z ≠ 1}) := by
  have hbase_ne : ((x : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (ne_of_gt hx)
  have hid :
      DifferentiableOn ℂ
        (fun z : ℂ => z)
        ({z : ℂ | 0 < z.re ∧ z.re < 2 ∧ z ≠ 1}) :=
    differentiableOn_id
  have hone :
      DifferentiableOn ℂ
        (fun _ : ℂ => (1 : ℂ))
        ({z : ℂ | 0 < z.re ∧ z.re < 2 ∧ z ≠ 1}) :=
    differentiableOn_const (1 : ℂ)
  have hexponent :
      DifferentiableOn ℂ
        (fun z : ℂ => -(z + 1))
        ({z : ℂ | 0 < z.re ∧ z.re < 2 ∧ z ≠ 1}) :=
    (hid.add hone).neg
  have hpow :
      DifferentiableOn ℂ
        (fun z : ℂ => (((x : ℝ) : ℂ) ^ (-(z + 1))))
        ({z : ℂ | 0 < z.re ∧ z.re < 2 ∧ z ≠ 1}) :=
    hexponent.const_cpow (Or.inl hbase_ne)
  have hfactor :
      DifferentiableOn ℂ
        (fun _ : ℂ => ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ))
        ({z : ℂ | 0 < z.re ∧ z.re < 2 ∧ z ≠ 1}) :=
    differentiableOn_const
      (((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ))
  exact hfactor.mul hpow

/-- Local version of the first periodic Bernoulli bound, placed before the
punctured-strip majorant so the local proof does not depend on later
closed-strip estimates. -/
theorem eulerMaclaurinFirstPeriodicBernoulli_norm_cast_le_one_local
    (x : ℝ) :
    ‖((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ)‖ ≤ 1 := by
  unfold eulerMaclaurinFirstPeriodicBernoulli
  have hfract_nonneg : 0 ≤ Int.fract x :=
    Int.fract_nonneg x
  have hfract_le_one : Int.fract x ≤ 1 :=
    le_of_lt (Int.fract_lt_one x)
  have hlower : -(1 : ℝ) ≤ Int.fract x - 1 / 2 := by
    have hneg_half : -(1 : ℝ) ≤ -(1 / 2 : ℝ) := by
      exact neg_le_neg one_half_le_one
    have hshift : -(1 / 2 : ℝ) ≤ Int.fract x - 1 / 2 := by
      calc
        -(1 / 2 : ℝ) = 0 - 1 / 2 := by
          exact (zero_sub (1 / 2 : ℝ)).symm
        _ ≤ Int.fract x - 1 / 2 :=
          sub_le_sub_right hfract_nonneg (1 / 2 : ℝ)
    exact le_trans hneg_half hshift
  have hupper : Int.fract x - 1 / 2 ≤ 1 := by
    have hhalf_nonneg : 0 ≤ (1 / 2 : ℝ) :=
      one_half_nonneg
    calc
      Int.fract x - 1 / 2 ≤ Int.fract x :=
        sub_le_self (Int.fract x) hhalf_nonneg
      _ ≤ 1 :=
        hfract_le_one
  have habs :
      |Int.fract x - 1 / 2| ≤ 1 :=
    abs_le.mpr ⟨hlower, hupper⟩
  have hnorm :
      ‖((Int.fract x - 1 / 2 : ℝ) : ℂ)‖ =
        |Int.fract x - 1 / 2| :=
    Complex.norm_ofReal (Int.fract x - 1 / 2)
  exact Eq.subst
    (motive := fun t : ℝ => t ≤ 1)
    hnorm.symm
    habs

/-- The first periodic Bernoulli sawtooth is measurable. -/
theorem eulerMaclaurinFirstPeriodicBernoulli_measurable :
    Measurable eulerMaclaurinFirstPeriodicBernoulli := by
  unfold eulerMaclaurinFirstPeriodicBernoulli
  exact measurable_fract.sub measurable_const

/-- The complex-valued first periodic Bernoulli factor is strongly measurable
on every measurable restricted tail. -/
theorem eulerMaclaurinFirstPeriodicBernoulli_cast_aestronglyMeasurable_restrict
    (s : Set ℝ)
    (hs : MeasurableSet s) :
    AEStronglyMeasurable
      (fun x : ℝ => ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ))
      (volume.restrict s) := by
  exact
    ((Complex.continuous_ofReal.measurable.comp
      eulerMaclaurinFirstPeriodicBernoulli_measurable).aestronglyMeasurable)

/-- The positive-tail complex-power kernel is continuous on any positive
cutoff tail. -/
theorem eulerMaclaurin_cpow_tail_continuousOn_Ioi
    (N : ℕ)
    (hN : 0 < N)
    (z : ℂ) :
    ContinuousOn
      (fun x : ℝ => (((x : ℝ) : ℂ) ^ (-(z + 1))))
      (Set.Ioi (((N : ℕ) : ℝ))) := by
  intro x hx
  have hx_pos : 0 < x :=
    lt_trans (Nat.cast_pos.mpr hN) hx
  exact
    (Complex.continuousAt_ofReal_cpow_const x (-(z + 1))
      (Or.inr (ne_of_gt hx_pos))).continuousWithinAt

/-- The positive-tail complex-power kernel is a.e.-strongly measurable on a
fixed positive cutoff tail. -/
theorem eulerMaclaurin_cpow_tail_aestronglyMeasurable
    (N : ℕ)
    (hN : 0 < N)
    (z : ℂ) :
    AEStronglyMeasurable
      (fun x : ℝ => (((x : ℝ) : ℂ) ^ (-(z + 1))))
      (volume.restrict (Set.Ioi (((N : ℕ) : ℝ)))) :=
  (eulerMaclaurin_cpow_tail_continuousOn_Ioi N hN z).aestronglyMeasurable
    measurableSet_Ioi

/-- The fixed-parameter Bernoulli/cpow kernel is a.e.-strongly measurable on
a positive cutoff tail. -/
theorem eulerMaclaurinBernoulliKernel_aestronglyMeasurable
    (N : ℕ)
    (hN : 0 < N)
    (z : ℂ) :
    AEStronglyMeasurable
      (fun x : ℝ =>
        ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) *
          (((x : ℝ) : ℂ) ^ (-(z + 1))))
      (volume.restrict (Set.Ioi (((N : ℕ) : ℝ)))) := by
  exact
    (eulerMaclaurinFirstPeriodicBernoulli_cast_aestronglyMeasurable_restrict
      (Set.Ioi (((N : ℕ) : ℝ))) measurableSet_Ioi).mul
      (eulerMaclaurin_cpow_tail_aestronglyMeasurable N hN z)

/-- A positive natural cutoff tail starts at least at one. -/
theorem eulerMaclaurin_one_le_of_mem_Ioi_nat_cast
    (N : ℕ)
    (hN : 0 < N)
    {x : ℝ}
    (hx : x ∈ Set.Ioi (((N : ℕ) : ℝ))) :
    1 ≤ x := by
  have hN_one_nat : 1 ≤ N :=
    Nat.succ_le_of_lt hN
  have hN_one_real : (1 : ℝ) ≤ ((N : ℕ) : ℝ) := by
    exact_mod_cast hN_one_nat
  exact le_trans hN_one_real (le_of_lt hx)

/-- Positive-real complex powers in the local Euler-Maclaurin tail have the
expected real-power norm. -/
theorem eulerMaclaurin_norm_real_cpow_neg_add_one_eq_rpow
    {x : ℝ}
    (hx : 0 < x)
    (z : ℂ) :
    ‖((x : ℝ) : ℂ) ^ (-(z + 1))‖ = x ^ (-(z.re + 1)) := by
  have hnorm :
      ‖((x : ℝ) : ℂ) ^ (-(z + 1))‖ =
        Complex.abs (((x : ℝ) : ℂ) ^ (-(z + 1))) := by
    exact Complex.norm_eq_abs (((x : ℝ) : ℂ) ^ (-(z + 1)))
  have habs :
      Complex.abs (((x : ℝ) : ℂ) ^ (-(z + 1))) =
        x ^ (-(z + 1)).re :=
    Complex.abs_cpow_eq_rpow_re_of_pos hx (-(z + 1))
  have hre : (-(z + 1)).re = -(z.re + 1) := by
    calc
      (-(z + 1)).re = -((z + 1).re) := by
        exact Complex.neg_re (z + 1)
      _ = -(z.re + (1 : ℂ).re) := by
        exact congrArg Neg.neg (Complex.add_re z 1)
      _ = -(z.re + 1) := by
        exact congrArg (fun t : ℝ => -(z.re + t)) Complex.one_re
  exact Eq.trans (Eq.trans hnorm habs) (congrArg (fun e : ℝ => x ^ e) hre)

/-- If `δ ≤ re z`, then on a tail with `x ≥ 1` the local complex-power norm
is bounded by `x ^ (-(δ + 1))`. -/
theorem eulerMaclaurin_norm_real_cpow_le_rpow_of_re_lower
    {x δ : ℝ}
    (hx_pos : 0 < x)
    (hx_one : 1 ≤ x)
    (z : ℂ)
    (hδz : δ ≤ z.re) :
    ‖((x : ℝ) : ℂ) ^ (-(z + 1))‖ ≤ x ^ (-(δ + 1)) := by
  have hnorm :
      ‖((x : ℝ) : ℂ) ^ (-(z + 1))‖ =
        x ^ (-(z.re + 1)) :=
    eulerMaclaurin_norm_real_cpow_neg_add_one_eq_rpow hx_pos z
  have hexponent :
      -(z.re + 1) ≤ -(δ + 1) := by
    exact neg_le_neg (add_le_add_right hδz 1)
  have hpow :
      x ^ (-(z.re + 1)) ≤ x ^ (-(δ + 1)) :=
    Real.rpow_le_rpow_of_exponent_le hx_one hexponent
  exact Eq.subst
    (motive := fun t : ℝ => t ≤ x ^ (-(δ + 1)))
    hnorm.symm
    hpow

/-- A small complex ball around a point with positive real part has a uniform
positive lower bound on real parts.

The intended radius and lower bound are both `z₀.re / 2`.  This is the local
geometric input needed for Euler-Maclaurin dominated estimates on the full
punctured strip `0 < re z < 2`, where no global `1 ≤ re z` lower bound is
available. -/
theorem eulerMaclaurin_ball_realPart_lowerBound_of_pos_re
    (z₀ : ℂ)
    (hz₀_pos : 0 < z₀.re) :
    ∃ r δ : ℝ, 0 < r ∧ 0 < δ ∧
      ∀ z : ℂ, z ∈ Metric.ball z₀ r → δ ≤ z.re := by
  let r : ℝ := z₀.re / 2
  let δ : ℝ := z₀.re / 2
  have hr_pos : 0 < r := by
    exact half_pos hz₀_pos
  have hδ_pos : 0 < δ := by
    exact half_pos hz₀_pos
  refine ⟨r, δ, hr_pos, hδ_pos, ?_⟩
  intro z hz
  have hdist : dist z z₀ < r :=
    hz
  have hnorm : ‖z - z₀‖ < r := by
    exact Eq.subst
      (motive := fun t : ℝ => t < r)
      (dist_eq_norm z z₀)
      hdist
  have habs_re :
      |(z - z₀).re| < r := by
    have hle_abs :
        |(z - z₀).re| ≤ Complex.abs (z - z₀) :=
      Complex.abs_re_le_abs (z - z₀)
    have habs_norm :
        Complex.abs (z - z₀) = ‖z - z₀‖ := by
      exact (Complex.norm_eq_abs (z - z₀)).symm
    exact lt_of_le_of_lt hle_abs
      (Eq.subst
        (motive := fun t : ℝ => t < r)
        habs_norm.symm
        hnorm)
  have hre_sub_lt : z₀.re - z.re < r := by
    have hneg :
        -(z.re - z₀.re) ≤ |z.re - z₀.re| :=
      neg_le_abs (z.re - z₀.re)
    have hsub_re :
        (z - z₀).re = z.re - z₀.re := by
      exact Complex.sub_re z z₀
    have hrewrite :
        |(z - z₀).re| = |z.re - z₀.re| := by
      exact congrArg abs hsub_re
    have hneg_lt :
        -(z.re - z₀.re) < r :=
      lt_of_le_of_lt hneg
        (Eq.subst
          (motive := fun t : ℝ => t < r)
          hrewrite
          habs_re)
    calc
      z₀.re - z.re = -(z.re - z₀.re) := by
        exact (neg_sub z.re z₀.re).symm
      _ < r := hneg_lt
  have hre_lower : z₀.re - r < z.re := by
    exact sub_lt_iff_lt_add.mp hre_sub_lt
  have hdelta_eq : δ = z₀.re - r := by
    unfold δ r
    calc
      z₀.re / 2 = z₀.re - z₀.re / 2 := by
        exact (eq_sub_iff_add_eq.mpr (add_halves z₀.re).symm).symm
  exact le_of_lt
    (Eq.subst
      (motive := fun t : ℝ => t < z.re)
      hdelta_eq
      hre_lower)

/-- The real power tail with exponent `-(δ + 1)` is integrable on any positive
Euler-Maclaurin cutoff tail when `δ > 0`. -/
theorem eulerMaclaurin_integrableOn_Ioi_rpow_neg_delta_add_one
    (N : ℕ)
    (hN : 0 < N)
    (δ : ℝ)
    (hδ : 0 < δ) :
    IntegrableOn
      (fun x : ℝ => x ^ (-(δ + 1)))
      (Set.Ioi (((N : ℕ) : ℝ))) := by
  have hcutoff_pos : 0 < (((N : ℕ) : ℝ)) := by
    exact_mod_cast hN
  have hexponent_lt :
      -(δ + 1) < -(1 : ℝ) := by
    exact neg_lt_neg (lt_add_of_pos_left 1 hδ)
  exact integrableOn_Ioi_rpow_of_lt hexponent_lt hcutoff_pos

/-- On a parameter ball with `δ ≤ re z`, the fixed-cutoff Bernoulli kernel is
dominated on the tail by the scalar integrable power `x ^ (-(δ + 1))`.

This is the analytic sink for the local punctured-strip majorant: it combines
`|B₁({x})| ≤ 1`, positivity of the real tail variable, the positive-real
`cpow` norm formula, and monotonicity of `x ^ s` in the exponent for `x ≥ N ≥ 1`.
It deliberately uses only the local lower bound `δ > 0`, not the later
closed-strip hypothesis `1 ≤ re z`. -/
theorem eulerMaclaurinBernoulliKernel_ae_le_rpow_majorant_of_ball_re_lower
    (N : ℕ)
    (hN : 0 < N)
    (z₀ : ℂ)
    (r δ : ℝ)
    (hδ : 0 < δ)
    (hre_lower : ∀ z : ℂ, z ∈ Metric.ball z₀ r → δ ≤ z.re) :
    ∀ z : ℂ, z ∈ Metric.ball z₀ r →
      ∀ᵐ x ∂volume.restrict (Set.Ioi (((N : ℕ) : ℝ))),
        ‖((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) *
          (((x : ℝ) : ℂ) ^ (-(z + 1)))‖ ≤
            x ^ (-(δ + 1)) := by
  intro z hz_ball
  exact ae_restrict_of_forall_mem measurableSet_Ioi
    (fun x hx_tail => by
      have hx_one : 1 ≤ x :=
        eulerMaclaurin_one_le_of_mem_Ioi_nat_cast N hN hx_tail
      have hx_pos : 0 < x :=
        lt_of_lt_of_le zero_lt_one hx_one
      have hδz : δ ≤ z.re :=
        hre_lower z hz_ball
      have hB :
          ‖((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ)‖ ≤ 1 :=
        eulerMaclaurinFirstPeriodicBernoulli_norm_cast_le_one_local x
      have hcpow :
          ‖((x : ℝ) : ℂ) ^ (-(z + 1))‖ ≤ x ^ (-(δ + 1)) :=
        eulerMaclaurin_norm_real_cpow_le_rpow_of_re_lower
          hx_pos hx_one z hδz
      have hcpow_nonneg :
          0 ≤ ‖((x : ℝ) : ℂ) ^ (-(z + 1))‖ :=
        norm_nonneg (((x : ℝ) : ℂ) ^ (-(z + 1)))
      have htarget_nonneg :
          0 ≤ x ^ (-(δ + 1)) :=
        Real.rpow_nonneg (le_of_lt hx_pos) (-(δ + 1))
      have hmul :
          ‖((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) *
              (((x : ℝ) : ℂ) ^ (-(z + 1)))‖ =
            ‖((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ)‖ *
              ‖((x : ℝ) : ℂ) ^ (-(z + 1))‖ :=
        norm_mul
          ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ)
          (((x : ℝ) : ℂ) ^ (-(z + 1)))
      have hproduct :
          ‖((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ)‖ *
              ‖((x : ℝ) : ℂ) ^ (-(z + 1))‖ ≤
            1 * (x ^ (-(δ + 1))) :=
        mul_le_mul hB hcpow hcpow_nonneg htarget_nonneg
      exact Eq.subst
        (motive := fun t : ℝ => t ≤ x ^ (-(δ + 1)))
        hmul.symm
        (Eq.subst
          (motive := fun t : ℝ =>
            ‖((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ)‖ *
                ‖((x : ℝ) : ℂ) ^ (-(z + 1))‖ ≤ t)
          (one_mul (x ^ (-(δ + 1)))).symm
          hproduct))

/-- Locally uniform integrable majorant for the fixed-cutoff Bernoulli kernel
on compact parameter neighborhoods inside the punctured strip. -/
theorem eulerMaclaurinBernoulliKernel_local_integrable_majorant_on_puncturedStrip
    (N : ℕ)
    (hN : 0 < N)
    (z₀ : ℂ)
    (hz₀ : z₀ ∈ ({z : ℂ | 0 < z.re ∧ z.re < 2 ∧ z ≠ 1})) :
    ∃ r : ℝ, 0 < r ∧
      ∃ g : ℝ → ℝ, IntegrableOn g (Set.Ioi (((N : ℕ) : ℝ))) ∧
        ∀ z : ℂ, z ∈ Metric.ball z₀ r →
          ∀ᵐ x ∂volume.restrict (Set.Ioi (((N : ℕ) : ℝ))),
            ‖((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) *
              (((x : ℝ) : ℂ) ^ (-(z + 1)))‖ ≤ g x := by
  have hz₀_pos : 0 < z₀.re :=
    hz₀.1
  rcases eulerMaclaurin_ball_realPart_lowerBound_of_pos_re z₀ hz₀_pos with
    ⟨r, δ, hr_pos, hδ_pos, hre_lower⟩
  let g : ℝ → ℝ := fun x : ℝ => x ^ (-(δ + 1))
  have hg_integrable :
      IntegrableOn g (Set.Ioi (((N : ℕ) : ℝ))) :=
    eulerMaclaurin_integrableOn_Ioi_rpow_neg_delta_add_one
      N hN δ hδ_pos
  have hmajorant :
      ∀ z : ℂ, z ∈ Metric.ball z₀ r →
        ∀ᵐ x ∂volume.restrict (Set.Ioi (((N : ℕ) : ℝ))),
          ‖((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) *
            (((x : ℝ) : ℂ) ^ (-(z + 1)))‖ ≤ g x := by
    intro z hz
    exact
      eulerMaclaurinBernoulliKernel_ae_le_rpow_majorant_of_ball_re_lower
        N hN z₀ r δ hδ_pos hre_lower z hz
  exact ⟨r, hr_pos, g, hg_integrable, hmajorant⟩

/-- Parameter derivative of the fixed-cutoff Bernoulli kernel.

For fixed positive `x`, differentiating
`z ↦ B₁({x}) x^(-(z+1))` in the complex parameter contributes the scalar
factor `-Log x`.  This is the pointwise derivative kernel needed before
applying dominated differentiation to the fixed lower-limit improper integral. -/
noncomputable def eulerMaclaurinBernoulliKernel_parameterDerivative
    (x z : ℂ) : ℂ :=
  -Complex.log x *
    (((eulerMaclaurinFirstPeriodicBernoulli x.re : ℝ) : ℂ) *
      (x ^ (-(z + 1))))

/-- Real-tail form of the parameter derivative kernel. -/
noncomputable def eulerMaclaurinBernoulliKernel_realTailParameterDerivative
    (x : ℝ)
    (z : ℂ) : ℂ :=
  -Complex.log ((x : ℝ) : ℂ) *
    (((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) *
      ((((x : ℝ) : ℂ) ^ (-(z + 1)))))

/-- The fixed-parameter derivative kernel is a.e.-strongly measurable on a
positive cutoff tail. -/
theorem eulerMaclaurinBernoulliKernel_parameterDerivative_aestronglyMeasurable
    (N : ℕ)
    (hN : 0 < N)
    (z : ℂ) :
    AEStronglyMeasurable
      (fun x : ℝ =>
        eulerMaclaurinBernoulliKernel_realTailParameterDerivative x z)
      (volume.restrict (Set.Ioi (((N : ℕ) : ℝ)))) := by
  let K : ℝ → ℂ := fun x : ℝ =>
    ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) *
      (((x : ℝ) : ℂ) ^ (-(z + 1)))
  have hlog_real :
      AEStronglyMeasurable
        (fun x : ℝ => -((Real.log x : ℝ) : ℂ))
        (volume.restrict (Set.Ioi (((N : ℕ) : ℝ)))) := by
    have hcont :
        ContinuousOn
          (fun x : ℝ => -((Real.log x : ℝ) : ℂ))
          (Set.Ioi (((N : ℕ) : ℝ))) := by
      intro x hx
      have hx_pos : 0 < x :=
        lt_trans (Nat.cast_pos.mpr hN) hx
      exact
        ((Complex.continuous_ofReal.continuousAt.comp
            (Real.continuousAt_log (ne_of_gt hx_pos))).neg).continuousWithinAt
    exact hcont.aestronglyMeasurable measurableSet_Ioi
  have hkernel :
      AEStronglyMeasurable K
        (volume.restrict (Set.Ioi (((N : ℕ) : ℝ)))) := by
    simpa [K] using
      eulerMaclaurinBernoulliKernel_aestronglyMeasurable N hN z
  have hreal :
      AEStronglyMeasurable
        (fun x : ℝ => -((Real.log x : ℝ) : ℂ) * K x)
        (volume.restrict (Set.Ioi (((N : ℕ) : ℝ)))) :=
    hlog_real.mul hkernel
  have hae :
      (fun x : ℝ =>
        -((Real.log x : ℝ) : ℂ) * K x) =ᵐ[
          volume.restrict (Set.Ioi (((N : ℕ) : ℝ)))]
        (fun x : ℝ =>
          eulerMaclaurinBernoulliKernel_realTailParameterDerivative x z) := by
    exact ae_restrict_of_forall_mem measurableSet_Ioi
      (fun x hx_tail => by
        have hx_pos : 0 < x :=
          lt_trans (Nat.cast_pos.mpr hN) hx_tail
        have hlog :
            ((Real.log x : ℝ) : ℂ) =
              Complex.log ((x : ℝ) : ℂ) :=
          Complex.ofReal_log hx_pos.le
        unfold eulerMaclaurinBernoulliKernel_realTailParameterDerivative K
        exact congrArg
          (fun t : ℂ =>
            -t *
              (((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) *
                (((x : ℝ) : ℂ) ^ (-(z + 1)))))
          hlog)
  exact hreal.congr hae

/-- Pointwise complex derivative of the fixed-tail Bernoulli kernel in the
parameter.

This is the owner-level chain-rule input for dominated differentiation.  The
remaining work inside this theorem is only the explicit `cpow` derivative
calculation on the positive real ray; no global analytic assumption is hidden
in a wrapper. -/
theorem eulerMaclaurinBernoulliKernel_hasDerivAt_parameter
    (x : ℝ)
    (hx : 0 < x)
    (z : ℂ) :
    HasDerivAt
      (fun w : ℂ =>
        ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) *
          (((x : ℝ) : ℂ) ^ (-(w + 1))))
      (eulerMaclaurinBernoulliKernel_realTailParameterDerivative x z)
      z := by
  let B : ℂ := ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ)
  let a : ℂ := ((x : ℝ) : ℂ)
  have ha_ne : a ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (ne_of_gt hx)
  have hexp :
      HasDerivAt
        (fun w : ℂ => -(w + 1))
        (-(1 : ℂ))
        z := by
    exact ((hasDerivAt_id z).add_const (1 : ℂ)).neg
  have hpow :
      HasDerivAt
        (fun w : ℂ => a ^ (-(w + 1)))
        (a ^ (-(z + 1)) * Complex.log a * (-(1 : ℂ)))
        z :=
    hexp.const_cpow (Or.inl ha_ne)
  have hB :
      HasDerivAt
        (fun _ : ℂ => B)
        0
        z :=
    hasDerivAt_const z B
  have hmul :
      HasDerivAt
        (fun w : ℂ => B * (a ^ (-(w + 1))))
        (B * (a ^ (-(z + 1)) * Complex.log a * (-(1 : ℂ))) +
          (a ^ (-(z + 1))) * 0)
        z :=
    hB.mul hpow
  have hvalue :
      B * (a ^ (-(z + 1)) * Complex.log a * (-(1 : ℂ))) +
          (a ^ (-(z + 1))) * 0 =
        eulerMaclaurinBernoulliKernel_realTailParameterDerivative x z := by
    calc
      B * (a ^ (-(z + 1)) * Complex.log a * (-(1 : ℂ))) +
          (a ^ (-(z + 1))) * 0 =
          B * (a ^ (-(z + 1)) * Complex.log a * (-(1 : ℂ))) := by
        exact add_zero (B * (a ^ (-(z + 1)) * Complex.log a * (-(1 : ℂ))))
      _ = B * (-(Complex.log a) * a ^ (-(z + 1))) := by
        calc
          B * (a ^ (-(z + 1)) * Complex.log a * (-(1 : ℂ))) =
              B * ((a ^ (-(z + 1)) * Complex.log a) * (-(1 : ℂ))) := by
            exact rfl
          _ = B * (-(a ^ (-(z + 1)) * Complex.log a)) := by
            exact congrArg (fun t : ℂ => B * t)
              (mul_neg_one (a ^ (-(z + 1)) * Complex.log a))
          _ = B * (-(Complex.log a * a ^ (-(z + 1)))) := by
            exact congrArg (fun t : ℂ => B * (-t))
              (mul_comm (a ^ (-(z + 1))) (Complex.log a))
          _ = B * (-(Complex.log a) * a ^ (-(z + 1))) := by
            exact congrArg (fun t : ℂ => B * t)
              (neg_mul (Complex.log a) (a ^ (-(z + 1)))).symm
      _ = -(Complex.log a) * (B * a ^ (-(z + 1))) := by
        calc
          B * (-(Complex.log a) * a ^ (-(z + 1))) =
              (B * -(Complex.log a)) * a ^ (-(z + 1)) := by
            exact (mul_assoc B (-(Complex.log a)) (a ^ (-(z + 1)))).symm
          _ = (-(Complex.log a) * B) * a ^ (-(z + 1)) := by
            exact congrArg
              (fun t : ℂ => t * a ^ (-(z + 1)))
              (mul_comm B (-(Complex.log a)))
          _ = -(Complex.log a) * (B * a ^ (-(z + 1))) := by
            exact mul_assoc (-(Complex.log a)) B (a ^ (-(z + 1)))
      _ = eulerMaclaurinBernoulliKernel_realTailParameterDerivative x z := by
        unfold eulerMaclaurinBernoulliKernel_realTailParameterDerivative
        rfl
  exact (hmul.congr_deriv hvalue).congr_of_eventuallyEq
    (Filter.Eventually.of_forall
      (fun w : ℂ => by
        unfold B a
        rfl))

/-- Logarithmic power tail dominating the parameter derivative kernel on a
local parameter ball. -/
noncomputable def eulerMaclaurinBernoulliKernel_derivativeMajorant
    (δ : ℝ) : ℝ → ℝ :=
  fun x : ℝ => Real.log x * x ^ (-(δ + 1))

/-- Pointwise logarithmic-power domination on the positive ray.

This is the elementary comparison `log x ≤ x^η / η`, with `η = δ / 2`,
multiplied by the positive factor `x^-(δ+1)`. -/
theorem eulerMaclaurin_log_rpow_neg_delta_add_one_le_rpow_tail
    {x δ : ℝ}
    (hx : 0 < x)
    (hx_one : 1 ≤ x)
    (hδ : 0 < δ) :
    ‖Real.log x * x ^ (-(δ + 1))‖ ≤
      (2 / δ) * x ^ (-(δ / 2 + 1)) := by
  let η : ℝ := δ / 2
  have hη_pos : 0 < η := by
    exact div_pos hδ two_pos
  have hx_nonneg : 0 ≤ x := le_of_lt hx
  have hpow_nonneg : 0 ≤ x ^ (-(δ + 1)) :=
    Real.rpow_nonneg hx_nonneg (-(δ + 1))
  have hlog_le : Real.log x ≤ x ^ η / η :=
    Real.log_le_rpow_div hx_nonneg hη_pos
  have hmul_le :
      Real.log x * x ^ (-(δ + 1)) ≤
        (x ^ η / η) * x ^ (-(δ + 1)) :=
    mul_le_mul_of_nonneg_right hlog_le hpow_nonneg
  have htarget_eq :
      (x ^ η / η) * x ^ (-(δ + 1)) =
        (2 / δ) * x ^ (-(δ / 2 + 1)) := by
    have hη_ne : η ≠ 0 := ne_of_gt hη_pos
    have hpow :
        x ^ η * x ^ (-(δ + 1)) =
          x ^ (-(δ / 2 + 1)) := by
      calc
        x ^ η * x ^ (-(δ + 1)) =
            x ^ (η + (-(δ + 1))) := by
          exact (Real.rpow_add hx η (-(δ + 1))).symm
        _ = x ^ (-(δ / 2 + 1)) := by
          have hexp : η + (-(δ + 1)) = -(δ / 2 + 1) := by
            calc
              η + (-(δ + 1)) = δ / 2 + (-(δ + 1)) := by
                rfl
              _ = -(δ / 2 + 1) := by
                ring
          exact congrArg (fun e : ℝ => x ^ e) hexp
    calc
      (x ^ η / η) * x ^ (-(δ + 1)) =
          (η⁻¹) * (x ^ η * x ^ (-(δ + 1))) := by
        calc
          (x ^ η / η) * x ^ (-(δ + 1)) =
              (x ^ η * η⁻¹) * x ^ (-(δ + 1)) := by
            exact congrArg (fun t : ℝ => t * x ^ (-(δ + 1)))
              (div_eq_mul_inv (x ^ η) η)
          _ = η⁻¹ * (x ^ η * x ^ (-(δ + 1))) := by
            calc
              (x ^ η * η⁻¹) * x ^ (-(δ + 1)) =
                  η⁻¹ * x ^ η * x ^ (-(δ + 1)) := by
                exact congrArg (fun t : ℝ => t * x ^ (-(δ + 1)))
                  (mul_comm (x ^ η) η⁻¹)
              _ = η⁻¹ * (x ^ η * x ^ (-(δ + 1))) := by
                exact mul_assoc η⁻¹ (x ^ η) (x ^ (-(δ + 1)))
      _ = η⁻¹ * x ^ (-(δ / 2 + 1)) := by
        exact congrArg (fun t : ℝ => η⁻¹ * t) hpow
      _ = (2 / δ) * x ^ (-(δ / 2 + 1)) := by
        have hη_inv : η⁻¹ = 2 / δ := by
          unfold η
          field_simp [ne_of_gt hδ]
        exact congrArg (fun t : ℝ => t * x ^ (-(δ / 2 + 1))) hη_inv
  have hlog_nonneg : 0 ≤ Real.log x :=
    Real.log_nonneg hx_one
  have hleft_nonneg :
      0 ≤ Real.log x * x ^ (-(δ + 1)) :=
    mul_nonneg hlog_nonneg hpow_nonneg
  calc
    ‖Real.log x * x ^ (-(δ + 1))‖ =
        |Real.log x * x ^ (-(δ + 1))| := by
      exact Real.norm_eq_abs (Real.log x * x ^ (-(δ + 1)))
    _ = Real.log x * x ^ (-(δ + 1)) := by
      exact abs_of_nonneg hleft_nonneg
    _ ≤ (x ^ η / η) * x ^ (-(δ + 1)) :=
      hmul_le
    _ = (2 / δ) * x ^ (-(δ / 2 + 1)) :=
      htarget_eq

/-- The logarithmic power tail is integrable on every positive cutoff tail.

Classically this follows from the comparison
`log x ≤ x^(δ/2)` for large `x`, reducing the tail to
`x^(-(1+δ/2))`, plus local integrability on the compact initial segment. -/
theorem eulerMaclaurin_integrableOn_Ioi_log_rpow_neg_delta_add_one
    (N : ℕ)
    (hN : 0 < N)
    (δ : ℝ)
    (hδ : 0 < δ) :
    IntegrableOn
      (eulerMaclaurinBernoulliKernel_derivativeMajorant δ)
      (Set.Ioi (((N : ℕ) : ℝ))) := by
  have hN_pos_real : 0 < (((N : ℕ) : ℝ)) := by
    exact_mod_cast hN
  let b : ℝ → ℝ := fun x : ℝ => (2 / δ) * x ^ (-(δ / 2 + 1))
  have hb_integrable :
      IntegrableOn b (Set.Ioi (((N : ℕ) : ℝ))) := by
    have hexp_lt : -(δ / 2 + 1) < -(1 : ℝ) := by
      have hδ_half_pos : 0 < δ / 2 := div_pos hδ two_pos
      exact neg_lt_neg (lt_add_of_pos_left 1 hδ_half_pos)
    exact
      (integrableOn_Ioi_rpow_of_lt hexp_lt hN_pos_real).const_mul (2 / δ)
  have hmeas :
      AEStronglyMeasurable
        (eulerMaclaurinBernoulliKernel_derivativeMajorant δ)
        (volume.restrict (Set.Ioi (((N : ℕ) : ℝ)))) := by
    have hcont :
        ContinuousOn
          (eulerMaclaurinBernoulliKernel_derivativeMajorant δ)
          (Set.Ioi (((N : ℕ) : ℝ))) := by
      unfold eulerMaclaurinBernoulliKernel_derivativeMajorant
      have hlog :
          ContinuousOn Real.log (Set.Ioi (((N : ℕ) : ℝ))) := by
        intro x hx
        have hx_pos : 0 < x := lt_trans hN_pos_real hx
        exact (Real.continuousAt_log (ne_of_gt hx_pos)).continuousWithinAt
      have hrpow :
          ContinuousOn
            (fun x : ℝ => x ^ (-(δ + 1)))
            (Set.Ioi (((N : ℕ) : ℝ))) := by
        exact continuousOn_id.rpow_const
          (fun x hx => Or.inl (ne_of_gt (lt_trans hN_pos_real hx)))
      exact hlog.mul hrpow
    exact hcont.aestronglyMeasurable measurableSet_Ioi
  have hbound :
      ∀ᵐ x ∂volume.restrict (Set.Ioi (((N : ℕ) : ℝ))),
        ‖eulerMaclaurinBernoulliKernel_derivativeMajorant δ x‖ ≤ b x := by
    exact ae_restrict_of_forall_mem measurableSet_Ioi
      (fun x hx => by
        have hx_pos : 0 < x := lt_trans hN_pos_real hx
        have hx_one : 1 ≤ x :=
          eulerMaclaurin_one_le_of_mem_Ioi_nat_cast N hN hx
        unfold eulerMaclaurinBernoulliKernel_derivativeMajorant b
        exact eulerMaclaurin_log_rpow_neg_delta_add_one_le_rpow_tail
          hx_pos hx_one hδ)
  exact Integrable.mono' hb_integrable hmeas hbound

/-- On a parameter ball with `δ ≤ re z`, the fixed-cutoff Bernoulli parameter
derivative kernel is dominated on the tail by the logarithmic power majorant. -/
theorem eulerMaclaurinBernoulliKernel_parameterDerivative_ae_le_log_rpow_majorant_of_ball_re_lower
    (N : ℕ)
    (hN : 0 < N)
    (z₀ : ℂ)
    (r δ : ℝ)
    (hδ : 0 < δ)
    (hre_lower : ∀ z : ℂ, z ∈ Metric.ball z₀ r → δ ≤ z.re) :
    ∀ᵐ x ∂volume.restrict (Set.Ioi (((N : ℕ) : ℝ))),
      ∀ z : ℂ, z ∈ Metric.ball z₀ r →
        ‖eulerMaclaurinBernoulliKernel_realTailParameterDerivative x z‖ ≤
          eulerMaclaurinBernoulliKernel_derivativeMajorant δ x := by
  exact ae_restrict_of_forall_mem measurableSet_Ioi
    (fun x hx_tail z hz_ball => by
      have hx_one : 1 ≤ x :=
        eulerMaclaurin_one_le_of_mem_Ioi_nat_cast N hN hx_tail
      have hx_pos : 0 < x :=
        lt_of_lt_of_le zero_lt_one hx_one
      have hδz : δ ≤ z.re :=
        hre_lower z hz_ball
      have hB :
          ‖((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ)‖ ≤ 1 :=
        eulerMaclaurinFirstPeriodicBernoulli_norm_cast_le_one_local x
      have hcpow :
          ‖((x : ℝ) : ℂ) ^ (-(z + 1))‖ ≤ x ^ (-(δ + 1)) :=
        eulerMaclaurin_norm_real_cpow_le_rpow_of_re_lower
          hx_pos hx_one z hδz
      have hlog_norm :
          ‖-Complex.log ((x : ℝ) : ℂ)‖ = Real.log x := by
        have hlog_ofReal :
            Complex.log ((x : ℝ) : ℂ) = (Real.log x : ℂ) :=
          Complex.ofReal_log hx_pos.le
        calc
          ‖-Complex.log ((x : ℝ) : ℂ)‖ =
              ‖Complex.log ((x : ℝ) : ℂ)‖ := by
            exact norm_neg (Complex.log ((x : ℝ) : ℂ))
          _ = ‖(Real.log x : ℂ)‖ := by
            exact congrArg norm hlog_ofReal
          _ = |Real.log x| := by
            exact Complex.norm_ofReal (Real.log x)
          _ = Real.log x := by
            exact abs_of_nonneg (Real.log_nonneg hx_one)
      have hkernel_norm :
          ‖((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) *
              (((x : ℝ) : ℂ) ^ (-(z + 1)))‖ ≤
            x ^ (-(δ + 1)) := by
        have hcpow_nonneg :
            0 ≤ ‖((x : ℝ) : ℂ) ^ (-(z + 1))‖ :=
          norm_nonneg (((x : ℝ) : ℂ) ^ (-(z + 1)))
        have htarget_nonneg :
            0 ≤ x ^ (-(δ + 1)) :=
          Real.rpow_nonneg (le_of_lt hx_pos) (-(δ + 1))
        calc
          ‖((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) *
              (((x : ℝ) : ℂ) ^ (-(z + 1)))‖ =
              ‖((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ)‖ *
                ‖((x : ℝ) : ℂ) ^ (-(z + 1))‖ := by
            exact norm_mul
              ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ)
              (((x : ℝ) : ℂ) ^ (-(z + 1)))
          _ ≤ 1 * (x ^ (-(δ + 1))) :=
            mul_le_mul hB hcpow hcpow_nonneg htarget_nonneg
          _ = x ^ (-(δ + 1)) := by
            exact one_mul (x ^ (-(δ + 1)))
      have hlog_nonneg : 0 ≤ Real.log x :=
        Real.log_nonneg hx_one
      calc
        ‖eulerMaclaurinBernoulliKernel_realTailParameterDerivative x z‖ =
            ‖-Complex.log ((x : ℝ) : ℂ)‖ *
              ‖((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) *
                (((x : ℝ) : ℂ) ^ (-(z + 1)))‖ := by
          unfold eulerMaclaurinBernoulliKernel_realTailParameterDerivative
          exact norm_mul
            (-Complex.log ((x : ℝ) : ℂ))
            (((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) *
              (((x : ℝ) : ℂ) ^ (-(z + 1))))
        _ = Real.log x *
              ‖((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) *
                (((x : ℝ) : ℂ) ^ (-(z + 1)))‖ := by
          exact congrArg
            (fun t : ℝ =>
              t *
                ‖((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) *
                  (((x : ℝ) : ℂ) ^ (-(z + 1)))‖)
            hlog_norm
        _ ≤ Real.log x * x ^ (-(δ + 1)) :=
          mul_le_mul_of_nonneg_left hkernel_norm hlog_nonneg
        _ = eulerMaclaurinBernoulliKernel_derivativeMajorant δ x := by
          rfl)

/-- Local integrable majorant for the parameter derivative of the fixed-cutoff
Bernoulli kernel on compact parameter neighborhoods inside the punctured
strip. -/
theorem eulerMaclaurinBernoulliKernel_parameterDerivative_local_integrable_majorant_on_puncturedStrip
    (N : ℕ)
    (hN : 0 < N)
    (z₀ : ℂ)
    (hz₀ : z₀ ∈ ({z : ℂ | 0 < z.re ∧ z.re < 2 ∧ z ≠ 1})) :
    ∃ r : ℝ, 0 < r ∧
      ∃ g : ℝ → ℝ, IntegrableOn g (Set.Ioi (((N : ℕ) : ℝ))) ∧
        ∀ᵐ x ∂volume.restrict (Set.Ioi (((N : ℕ) : ℝ))),
          ∀ z : ℂ, z ∈ Metric.ball z₀ r →
            ‖eulerMaclaurinBernoulliKernel_realTailParameterDerivative x z‖ ≤
              g x := by
  have hz₀_pos : 0 < z₀.re :=
    hz₀.1
  rcases eulerMaclaurin_ball_realPart_lowerBound_of_pos_re z₀ hz₀_pos with
    ⟨r, δ, hr_pos, hδ_pos, hre_lower⟩
  let g : ℝ → ℝ := eulerMaclaurinBernoulliKernel_derivativeMajorant δ
  have hg_integrable :
      IntegrableOn g (Set.Ioi (((N : ℕ) : ℝ))) :=
    eulerMaclaurin_integrableOn_Ioi_log_rpow_neg_delta_add_one
      N hN δ hδ_pos
  have hmajorant :
      ∀ᵐ x ∂volume.restrict (Set.Ioi (((N : ℕ) : ℝ))),
        ∀ z : ℂ, z ∈ Metric.ball z₀ r →
          ‖eulerMaclaurinBernoulliKernel_realTailParameterDerivative x z‖ ≤
            g x :=
    eulerMaclaurinBernoulliKernel_parameterDerivative_ae_le_log_rpow_majorant_of_ball_re_lower
      N hN z₀ r δ hδ_pos hre_lower
  exact ⟨r, hr_pos, g, hg_integrable, hmajorant⟩

/-- Fixed lower-limit dominated differentiation for an improper parameter
integral over a positive tail.

This is the measure-theoretic owner API needed by the Euler-Maclaurin
Bernoulli kernel: the lower limit is fixed, the measure is
`volume.restrict (Ioi N)`, and the hypotheses are pointwise parameter
derivatives plus a local integrable majorant for those derivatives. -/
theorem hasDerivAt_integral_Ioi_of_local_integrable_derivative_majorant
    (N : ℕ)
    (F F' : ℂ → ℝ → ℂ)
    (z : ℂ)
    (r : ℝ)
    (hr : 0 < r)
    (g : ℝ → ℝ)
    (hF_meas :
      ∀ᶠ w in 𝓝 z,
        AEStronglyMeasurable
          (F w)
          (volume.restrict (Set.Ioi (((N : ℕ) : ℝ)))))
    (hF_int :
      Integrable
        (F z)
        (volume.restrict (Set.Ioi (((N : ℕ) : ℝ)))))
    (hF'_meas :
      AEStronglyMeasurable
        (F' z)
        (volume.restrict (Set.Ioi (((N : ℕ) : ℝ)))))
    (hg :
      IntegrableOn g (Set.Ioi (((N : ℕ) : ℝ)))
        volume)
    (hbound :
      ∀ᵐ x ∂volume.restrict (Set.Ioi (((N : ℕ) : ℝ))),
        ∀ w ∈ Metric.ball z r, ‖F' w x‖ ≤ g x)
    (hderiv :
      ∀ᵐ x ∂volume.restrict (Set.Ioi (((N : ℕ) : ℝ))),
        ∀ w ∈ Metric.ball z r,
          HasDerivAt (fun u : ℂ => F u x) (F' w x) w) :
    HasDerivAt
      (fun w : ℂ =>
        ∫ x in Set.Ioi (((N : ℕ) : ℝ)), F w x)
      (∫ x in Set.Ioi (((N : ℕ) : ℝ)), F' z x)
      z := by
  have hg_restrict :
      Integrable g (volume.restrict (Set.Ioi (((N : ℕ) : ℝ)))) :=
    hg
  have hparam :=
    hasDerivAt_integral_of_dominated_loc_of_deriv_le
      (μ := volume.restrict (Set.Ioi (((N : ℕ) : ℝ)))
      (F := F)
      (F' := F')
      (x₀ := z)
      (bound := g)
      hr
      hF_meas
      hF_int
      hF'_meas
      hbound
      hg_restrict
      hderiv
  exact hparam.2

/-- Dominated differentiation for the fixed-cutoff Bernoulli kernel, using
the local integrable majorant and the pointwise parameter differentiability
already owned above.

This is the reusable parameter-integral theorem for the Euler-Maclaurin
Bernoulli kernel with fixed lower limit.  It is deliberately separated from
the zeta defect so the remaining analytic work is the dominated-differentiation
API, not an endpoint-shaped holomorphicity assertion. -/
theorem eulerMaclaurinZetaBernoulliIntegralCoreWithCutoff_differentiable_under_integral_from_local_majorant
    (N : ℕ)
    (hN : 0 < N) :
    DifferentiableOn ℂ
      (eulerMaclaurinZetaBernoulliIntegralCoreWithCutoff N)
      ({z : ℂ | 0 < z.re ∧ z.re < 2 ∧ z ≠ 1}) := by
  intro z hz
  rcases
    eulerMaclaurinBernoulliKernel_parameterDerivative_local_integrable_majorant_on_puncturedStrip
      N hN z hz with
    ⟨r, hr_pos, g, hg_integrable, hmajorant⟩
  let F : ℂ → ℝ → ℂ := fun w x : ℝ =>
    ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) *
      (((x : ℝ) : ℂ) ^ (-(w + 1)))
  let F' : ℂ → ℝ → ℂ :=
    fun w x : ℝ =>
      eulerMaclaurinBernoulliKernel_realTailParameterDerivative x w
  have hderiv :
      ∀ᵐ x ∂volume.restrict (Set.Ioi (((N : ℕ) : ℝ))),
        ∀ w ∈ Metric.ball z r,
          HasDerivAt (fun u : ℂ => F u x) (F' w x) w := by
    exact ae_restrict_of_forall_mem measurableSet_Ioi
      (fun x hx_tail w hw => by
        have hx_pos : 0 < x := by
          exact lt_of_lt_of_le zero_lt_one
            (eulerMaclaurin_one_le_of_mem_Ioi_nat_cast N hN hx_tail)
        exact eulerMaclaurinBernoulliKernel_hasDerivAt_parameter x hx_pos w)
  have hbound :
      ∀ᵐ x ∂volume.restrict (Set.Ioi (((N : ℕ) : ℝ))),
        ∀ w ∈ Metric.ball z r, ‖F' w x‖ ≤ g x := by
    exact hmajorant.mono
      (fun x hx w hw => hx w hw)
  have hF_meas :
      ∀ᶠ w in 𝓝 z,
        AEStronglyMeasurable
          (F w)
          (volume.restrict (Set.Ioi (((N : ℕ) : ℝ)))) := by
    exact Filter.Eventually.of_forall
      (fun w : ℂ => by
        simpa [F] using
          eulerMaclaurinBernoulliKernel_aestronglyMeasurable N hN w)
  have hF_int :
      Integrable
        (F z)
        (volume.restrict (Set.Ioi (((N : ℕ) : ℝ)))) := by
    rcases
      eulerMaclaurinBernoulliKernel_local_integrable_majorant_on_puncturedStrip
        N hN z hz with
      ⟨r₀, hr₀_pos, g₀, hg₀_integrable, hmajorant₀⟩
    have hz_ball₀ : z ∈ Metric.ball z r₀ :=
      Metric.mem_ball_self hr₀_pos
    have hbound₀ :
        ∀ᵐ x ∂volume.restrict (Set.Ioi (((N : ℕ) : ℝ))),
          ‖F z x‖ ≤ g₀ x := by
      exact (hmajorant₀ z hz_ball₀).mono
        (fun x hx => by
          simpa [F] using hx)
    have hg₀ :
        Integrable g₀ (volume.restrict (Set.Ioi (((N : ℕ) : ℝ)))) :=
      hg₀_integrable
    have hmeas :
        AEStronglyMeasurable
          (F z)
          (volume.restrict (Set.Ioi (((N : ℕ) : ℝ)))) := by
      simpa [F] using
        eulerMaclaurinBernoulliKernel_aestronglyMeasurable N hN z
    exact Integrable.mono' hg₀ hmeas hbound₀
  have hF'_meas :
      AEStronglyMeasurable
        (F' z)
        (volume.restrict (Set.Ioi (((N : ℕ) : ℝ)))) := by
    simpa [F'] using
      eulerMaclaurinBernoulliKernel_parameterDerivative_aestronglyMeasurable
        N hN z
  have hhasDeriv :
      HasDerivAt
        (fun w : ℂ =>
          ∫ x in Set.Ioi (((N : ℕ) : ℝ)), F w x)
        (∫ x in Set.Ioi (((N : ℕ) : ℝ)), F' z x)
        z :=
    hasDerivAt_integral_Ioi_of_local_integrable_derivative_majorant
      N F F' z r hr_pos g hF_meas hF_int hF'_meas
      hg_integrable hbound hderiv
  have hsame :
      (fun w : ℂ =>
        ∫ x in Set.Ioi (((N : ℕ) : ℝ)), F w x) =
        eulerMaclaurinZetaBernoulliIntegralCoreWithCutoff N := by
    funext w
    rfl
  exact
    (Eq.subst
      (motive := fun H : ℂ → ℂ => DifferentiableAt ℂ H z)
      hsame
      hhasDeriv.differentiableAt).differentiableWithinAt

/-- Differentiation under the fixed lower-limit Bernoulli improper integral in
the complex parameter. -/
theorem eulerMaclaurinZetaBernoulliIntegralCoreWithCutoff_differentiable_under_integral
    (N : ℕ)
    (hN : 0 < N) :
    DifferentiableOn ℂ
      (eulerMaclaurinZetaBernoulliIntegralCoreWithCutoff N)
      ({z : ℂ | 0 < z.re ∧ z.re < 2 ∧ z ≠ 1}) := by
  exact
    eulerMaclaurinZetaBernoulliIntegralCoreWithCutoff_differentiable_under_integral_from_local_majorant
      N hN

/-- Fixed lower-limit Bernoulli integral core is holomorphic in the complex
parameter on the punctured strip.

This is the standard parameter-integral theorem: the lower limit is fixed, the
Bernoulli factor is bounded, and the complex-power kernel has locally uniform
integrable majorants on vertical compacta. -/
theorem eulerMaclaurinZetaBernoulliIntegralCoreWithCutoff_parameter_holomorphic_standard
    (N : ℕ)
    (hN : 0 < N) :
    DifferentiableOn ℂ
      (eulerMaclaurinZetaBernoulliIntegralCoreWithCutoff N)
      ({z : ℂ | 0 < z.re ∧ z.re < 2 ∧ z ≠ 1}) := by
  exact
    eulerMaclaurinZetaBernoulliIntegralCoreWithCutoff_differentiable_under_integral
      N hN

/-- Fixed lower-limit Bernoulli integral core is holomorphic in the complex
parameter on the punctured strip. -/
theorem eulerMaclaurinZetaBernoulliIntegralCoreWithCutoff_holomorphicOn_puncturedStrip
    (N : ℕ)
    (hN : 0 < N) :
    DifferentiableOn ℂ
      (eulerMaclaurinZetaBernoulliIntegralCoreWithCutoff N)
      ({z : ℂ | 0 < z.re ∧ z.re < 2 ∧ z ≠ 1}) := by
  exact
    eulerMaclaurinZetaBernoulliIntegralCoreWithCutoff_parameter_holomorphic_standard
      N hN

/-- Fixed-cutoff Bernoulli remainder is holomorphic on the punctured strip. -/
theorem eulerMaclaurinZetaBernoulliIntegralRemainderWithCutoff_holomorphicOn_puncturedStrip
    (N : ℕ)
    (hN : 0 < N) :
    DifferentiableOn ℂ
      (eulerMaclaurinZetaBernoulliIntegralRemainderWithCutoff N)
      ({z : ℂ | 0 < z.re ∧ z.re < 2 ∧ z ≠ 1}) := by
  unfold eulerMaclaurinZetaBernoulliIntegralRemainderWithCutoff
  have hid :
      DifferentiableOn ℂ
        (fun z : ℂ => z)
        ({z : ℂ | 0 < z.re ∧ z.re < 2 ∧ z ≠ 1}) :=
    differentiableOn_id
  have hneg_id :
      DifferentiableOn ℂ
        (fun z : ℂ => -z)
        ({z : ℂ | 0 < z.re ∧ z.re < 2 ∧ z ≠ 1}) :=
    hid.neg
  have hcore :
      DifferentiableOn ℂ
        (eulerMaclaurinZetaBernoulliIntegralCoreWithCutoff N)
        ({z : ℂ | 0 < z.re ∧ z.re < 2 ∧ z ≠ 1}) :=
    eulerMaclaurinZetaBernoulliIntegralCoreWithCutoff_holomorphicOn_puncturedStrip
      N hN
  exact hneg_id.mul hcore

/-- Fixed-cutoff defect is holomorphic on the punctured vertical strip. -/
theorem eulerMaclaurin_riemannZeta_fixedCutoffTailIdentityDefect_holomorphicOn_puncturedStrip_standard
    (N : ℕ)
    (hN : 0 < N) :
    DifferentiableOn ℂ
      (eulerMaclaurin_riemannZeta_fixedCutoffTailIdentityDefect N)
      ({z : ℂ | 0 < z.re ∧ z.re < 2 ∧ z ≠ 1}) := by
  unfold eulerMaclaurin_riemannZeta_fixedCutoffTailIdentityDefect
  have hzeta :
      DifferentiableOn ℂ
        riemannZeta
        ({z : ℂ | 0 < z.re ∧ z.re < 2 ∧ z ≠ 1}) :=
    eulerMaclaurin_riemannZeta_holomorphicOn_fixedCutoff_puncturedStrip
  have hfinite :
      DifferentiableOn ℂ
        (eulerMaclaurinZetaFinitePartWithCutoff N)
        ({z : ℂ | 0 < z.re ∧ z.re < 2 ∧ z ≠ 1}) :=
    eulerMaclaurinZetaFinitePartWithCutoff_holomorphicOn_puncturedStrip N
  have hmain :
      DifferentiableOn ℂ
        (eulerMaclaurinZetaMainTermWithCutoff N)
        ({z : ℂ | 0 < z.re ∧ z.re < 2 ∧ z ≠ 1}) :=
    eulerMaclaurinZetaMainTermWithCutoff_holomorphicOn_puncturedStrip N hN
  have hendpoint :
      DifferentiableOn ℂ
        (eulerMaclaurinZetaEndpointTermWithCutoff N)
        ({z : ℂ | 0 < z.re ∧ z.re < 2 ∧ z ≠ 1}) :=
    eulerMaclaurinZetaEndpointTermWithCutoff_holomorphicOn_puncturedStrip N hN
  have hremainder :
      DifferentiableOn ℂ
        (eulerMaclaurinZetaBernoulliIntegralRemainderWithCutoff N)
        ({z : ℂ | 0 < z.re ∧ z.re < 2 ∧ z ≠ 1}) :=
    eulerMaclaurinZetaBernoulliIntegralRemainderWithCutoff_holomorphicOn_puncturedStrip
      N hN
  exact (hzeta.sub hfinite).sub ((hmain.add hendpoint).add hremainder)

/-- The fixed punctured vertical strip used for the Euler-Maclaurin defect is open. -/
theorem eulerMaclaurin_fixedCutoff_puncturedStrip_isOpen :
    IsOpen ({z : ℂ | 0 < z.re ∧ z.re < 2 ∧ z ≠ 1}) := by
  have hleft : IsOpen {z : ℂ | 0 < z.re} :=
    isOpen_lt continuous_const Complex.continuous_re
  have hright : IsOpen {z : ℂ | z.re < 2} :=
    isOpen_lt Complex.continuous_re continuous_const
  have hpole : IsOpen {z : ℂ | z ≠ 1} :=
    isOpen_compl_singleton
  exact (hleft.inter hright).inter hpole

/-- The fixed-cutoff Euler-Maclaurin defect is analytic on a neighborhood of
the punctured strip. -/
theorem eulerMaclaurin_fixedCutoffTailIdentityDefect_analyticOnNhd_puncturedStrip
    (N : ℕ)
    (hN : 0 < N) :
    AnalyticOnNhd ℂ
      (eulerMaclaurin_riemannZeta_fixedCutoffTailIdentityDefect N)
      ({z : ℂ | 0 < z.re ∧ z.re < 2 ∧ z ≠ 1}) := by
  exact
    (eulerMaclaurin_riemannZeta_fixedCutoffTailIdentityDefect_holomorphicOn_puncturedStrip_standard
      N hN).analyticOnNhd
      eulerMaclaurin_fixedCutoff_puncturedStrip_isOpen

/-- Horizontal segments at nonzero imaginary height stay inside the punctured
strip once their endpoints lie in the strip.

This is the horizontal leg in the polygonal detour around the deleted point
`1`. -/
theorem eulerMaclaurin_puncturedVerticalStrip_horizontalSegment_mem
    {z w p : ℂ}
    (hz : z ∈ ({u : ℂ | 0 < u.re ∧ u.re < 2 ∧ u ≠ 1}))
    (hw : w ∈ ({u : ℂ | 0 < u.re ∧ u.re < 2 ∧ u ≠ 1}))
    (hp_re : p.re ∈ Set.Icc z.re w.re ∨ p.re ∈ Set.Icc w.re z.re)
    (hp_im : p.im = z.im)
    (hzw_im : z.im = w.im)
    (hz_im : z.im ≠ 0) :
    p ∈ ({u : ℂ | 0 < u.re ∧ u.re < 2 ∧ u ≠ 1}) := by
  constructor
  · cases hp_re with
    | inl hp_between =>
        exact lt_of_lt_of_le hz.1 hp_between.1
    | inr hp_between =>
        exact lt_of_lt_of_le hw.1 hp_between.1
  constructor
  · cases hp_re with
    | inl hp_between =>
        exact lt_of_le_of_lt hp_between.2 hw.2.1
    | inr hp_between =>
        exact lt_of_le_of_lt hp_between.2 hz.2.1
  · intro hbad
    have hp_one_im : p.im = (1 : ℂ).im :=
      congrArg Complex.im hbad
    have hz_zero : z.im = 0 := by
      calc
        z.im = p.im := hp_im.symm
        _ = (1 : ℂ).im := hp_one_im
        _ = 0 := rfl
    exact hz_im hz_zero

/-- Vertical segments at real part different from `1` stay inside the punctured
strip once their endpoints lie in the strip.

This is the vertical leg in the polygonal detour around the deleted point. -/
theorem eulerMaclaurin_puncturedVerticalStrip_verticalSegment_mem
    {z w p : ℂ}
    (hz : z ∈ ({u : ℂ | 0 < u.re ∧ u.re < 2 ∧ u ≠ 1}))
    (hw : w ∈ ({u : ℂ | 0 < u.re ∧ u.re < 2 ∧ u ≠ 1}))
    (hp_re : p.re = z.re)
    (hp_im : p.im ∈ Set.Icc z.im w.im ∨ p.im ∈ Set.Icc w.im z.im)
    (hzw_re : z.re = w.re)
    (hz_re : z.re ≠ 1) :
    p ∈ ({u : ℂ | 0 < u.re ∧ u.re < 2 ∧ u ≠ 1}) := by
  constructor
  · calc
      0 < z.re := hz.1
      _ = p.re := hp_re.symm
  constructor
  · calc
      p.re = z.re := hp_re
      _ < 2 := hz.2.1
  · intro hbad
    have hp_one_re : p.re = (1 : ℂ).re :=
      congrArg Complex.re hbad
    have hz_one : z.re = 1 := by
      calc
        z.re = p.re := hp_re.symm
        _ = (1 : ℂ).re := hp_one_re
        _ = 1 := rfl
    exact hz_re hz_one

/-- For any two points in the punctured strip, choose an endpoint detour height
away from the deleted point `1`.

This records only the endpoint normalization used by the corridor construction;
vertical path safety is handled by the corridor lemmas below. -/
theorem eulerMaclaurin_puncturedVerticalStrip_detourHeight_exists
    (z w : ℂ)
    (hz : z ∈ ({u : ℂ | 0 < u.re ∧ u.re < 2 ∧ u ≠ 1}))
    (hw : w ∈ ({u : ℂ | 0 < u.re ∧ u.re < 2 ∧ u ≠ 1})) :
    ∃ h : ℝ, h ≠ 0 ∧
      Complex.mk z.re h ∈ ({u : ℂ | 0 < u.re ∧ u.re < 2 ∧ u ≠ 1}) ∧
      Complex.mk w.re h ∈ ({u : ℂ | 0 < u.re ∧ u.re < 2 ∧ u ≠ 1}) := by
  refine ⟨1, one_ne_zero, ?_, ?_⟩
  · constructor
    · exact hz.1
    constructor
    · exact hz.2.1
    · intro hbad
      have him : (Complex.mk z.re (1 : ℝ)).im = (1 : ℂ).im :=
        congrArg Complex.im hbad
      change (1 : ℝ) = 0 at him
      exact one_ne_zero him
  · constructor
    · exact hw.1
    constructor
    · exact hw.2.1
    · intro hbad
      have him : (Complex.mk w.re (1 : ℝ)).im = (1 : ℂ).im :=
        congrArg Complex.im hbad
      change (1 : ℝ) = 0 at him
      exact one_ne_zero him

/-- Points in the left component `0 < Re z < 1` of the punctured strip are
joined inside the punctured strip. -/
theorem eulerMaclaurin_puncturedVerticalStrip_leftHalf_joined
    {z w : ℂ}
    (hz : z ∈ ({u : ℂ | 0 < u.re ∧ u.re < 2 ∧ u ≠ 1}))
    (hw : w ∈ ({u : ℂ | 0 < u.re ∧ u.re < 2 ∧ u ≠ 1}))
    (hz_left : z.re < 1)
    (hw_left : w.re < 1) :
    JoinedIn
      ({u : ℂ | 0 < u.re ∧ u.re < 2 ∧ u ≠ 1})
      z w := by
  exact
    puncturedVerticalStrip_leftHalf_joined
      (z := z) (w := w) hz hw hz_left hw_left

/-- Points in the right component `1 < Re z < 2` of the punctured strip are
joined inside the punctured strip. -/
theorem eulerMaclaurin_puncturedVerticalStrip_rightHalf_joined
    {z w : ℂ}
    (hz : z ∈ ({u : ℂ | 0 < u.re ∧ u.re < 2 ∧ u ≠ 1}))
    (hw : w ∈ ({u : ℂ | 0 < u.re ∧ u.re < 2 ∧ u ≠ 1}))
    (hz_right : 1 < z.re)
    (hw_right : 1 < w.re) :
    JoinedIn
      ({u : ℂ | 0 < u.re ∧ u.re < 2 ∧ u ≠ 1})
      z w := by
  exact
    puncturedVerticalStrip_rightHalf_joined
      (z := z) (w := w) hz hw hz_right hw_right

/-- Horizontal segments at nonzero height cross safely between any two real
parts in the open strip. -/
theorem eulerMaclaurin_puncturedVerticalStrip_nonzeroHeight_horizontalJoined
    {x₁ x₂ h : ℝ}
    (hx₁_left : 0 < x₁)
    (hx₁_right : x₁ < 2)
    (hx₂_left : 0 < x₂)
    (hx₂_right : x₂ < 2)
    (hh : h ≠ 0) :
    JoinedIn
      ({u : ℂ | 0 < u.re ∧ u.re < 2 ∧ u ≠ 1})
      (Complex.mk x₁ h)
      (Complex.mk x₂ h) := by
  exact
    puncturedVerticalStrip_nonzeroHeight_horizontalJoined
      hx₁_left hx₁_right hx₂_left hx₂_right hh

/-- The left safe corridor has positive real coordinate. -/
theorem real_zero_lt_one_half_for_puncturedVerticalStrip :
    (0 : ℝ) < 1 / 2 := by
  exact half_pos zero_lt_one

/-- The left safe corridor lies left of the deleted vertical line. -/
theorem real_one_half_lt_one_for_puncturedVerticalStrip :
    (1 / 2 : ℝ) < 1 := by
  exact half_lt_self zero_lt_one

/-- The left safe corridor lies inside the right strip boundary. -/
theorem real_one_half_lt_two_for_puncturedVerticalStrip :
    (1 / 2 : ℝ) < 2 := by
  exact
    lt_trans
      real_one_half_lt_one_for_puncturedVerticalStrip
      one_lt_two

/-- The right safe corridor has positive real coordinate. -/
theorem real_zero_lt_three_halves_for_puncturedVerticalStrip :
    (0 : ℝ) < 3 / 2 := by
  exact div_pos (show (0 : ℝ) < 3 by
    calc
      (0 : ℝ) < 1 := zero_lt_one
      _ < 3 := lt_trans one_lt_two (show (2 : ℝ) < 3 by
        exact lt_add_of_pos_right 2 zero_lt_one)) two_pos

/-- The right safe corridor lies right of the deleted vertical line. -/
theorem real_one_lt_three_halves_for_puncturedVerticalStrip :
    (1 : ℝ) < 3 / 2 := by
  exact
    (lt_div_iff₀ two_pos).2
      (show (1 : ℝ) * 2 < 3 by
        calc
          (1 : ℝ) * 2 = 2 := one_mul 2
          _ < 3 := lt_add_of_pos_right 2 zero_lt_one)

/-- The right safe corridor lies inside the right strip boundary. -/
theorem real_three_halves_lt_two_for_puncturedVerticalStrip :
    (3 / 2 : ℝ) < 2 := by
  exact
    (div_lt_iff₀ two_pos).2
      (show (3 : ℝ) < 2 * 2 by
        calc
          (3 : ℝ) < 4 := lt_add_of_pos_right 3 zero_lt_one
          _ = 2 * 2 := (show (4 : ℝ) = 2 * 2 by rfl))

/-- The left safe corridor real coordinate is not the deleted coordinate. -/
theorem real_one_half_ne_one_for_puncturedVerticalStrip :
    (1 / 2 : ℝ) ≠ 1 := by
  exact ne_of_lt real_one_half_lt_one_for_puncturedVerticalStrip

/-- The right safe corridor real coordinate is not the deleted coordinate. -/
theorem real_three_halves_ne_one_for_puncturedVerticalStrip :
    (3 / 2 : ℝ) ≠ 1 := by
  exact ne_of_gt real_one_lt_three_halves_for_puncturedVerticalStrip

/-- The left safe column lies in the punctured strip. -/
theorem eulerMaclaurin_puncturedVerticalStrip_leftColumn_mem
    {y : ℝ} :
    Complex.mk (1 / 2) y ∈
      ({u : ℂ | 0 < u.re ∧ u.re < 2 ∧ u ≠ 1}) := by
  constructor
  · exact real_zero_lt_one_half_for_puncturedVerticalStrip
  constructor
  · exact real_one_half_lt_two_for_puncturedVerticalStrip
  · intro hbad
    have hre : (Complex.mk (1 / 2 : ℝ) y).re = (1 : ℂ).re :=
      congrArg Complex.re hbad
    exact real_one_half_ne_one_for_puncturedVerticalStrip hre

/-- The right safe column lies in the punctured strip. -/
theorem eulerMaclaurin_puncturedVerticalStrip_rightColumn_mem
    {y : ℝ} :
    Complex.mk (3 / 2) y ∈
      ({u : ℂ | 0 < u.re ∧ u.re < 2 ∧ u ≠ 1}) := by
  constructor
  · exact real_zero_lt_three_halves_for_puncturedVerticalStrip
  constructor
  · exact real_three_halves_lt_two_for_puncturedVerticalStrip
  · intro hbad
    have hre : (Complex.mk (3 / 2 : ℝ) y).re = (1 : ℂ).re :=
      congrArg Complex.re hbad
    exact real_three_halves_ne_one_for_puncturedVerticalStrip hre

/-- The left half-column is a safe vertical corridor inside the punctured
strip. -/
theorem eulerMaclaurin_puncturedVerticalStrip_leftColumn_verticalJoined
    {y₁ y₂ : ℝ} :
    JoinedIn
      ({u : ℂ | 0 < u.re ∧ u.re < 2 ∧ u ≠ 1})
      (Complex.mk (1 / 2) y₁)
      (Complex.mk (1 / 2) y₂) := by
  exact
    eulerMaclaurin_puncturedVerticalStrip_leftHalf_joined
      eulerMaclaurin_puncturedVerticalStrip_leftColumn_mem
      eulerMaclaurin_puncturedVerticalStrip_leftColumn_mem
      real_one_half_lt_one_for_puncturedVerticalStrip
      real_one_half_lt_one_for_puncturedVerticalStrip

/-- The right half-column is a safe vertical corridor inside the punctured
strip. -/
theorem eulerMaclaurin_puncturedVerticalStrip_rightColumn_verticalJoined
    {y₁ y₂ : ℝ} :
    JoinedIn
      ({u : ℂ | 0 < u.re ∧ u.re < 2 ∧ u ≠ 1})
      (Complex.mk (3 / 2) y₁)
      (Complex.mk (3 / 2) y₂) := by
  exact
    eulerMaclaurin_puncturedVerticalStrip_rightHalf_joined
      eulerMaclaurin_puncturedVerticalStrip_rightColumn_mem
      eulerMaclaurin_puncturedVerticalStrip_rightColumn_mem
      real_one_lt_three_halves_for_puncturedVerticalStrip
      real_one_lt_three_halves_for_puncturedVerticalStrip

/-- Every point in the punctured strip is joined to one of the two safe
vertical corridors at its own imaginary height. -/
theorem eulerMaclaurin_puncturedVerticalStrip_joinedTo_safeCorridor
    {z : ℂ}
    (hz : z ∈ ({u : ℂ | 0 < u.re ∧ u.re < 2 ∧ u ≠ 1})) :
    JoinedIn
        ({u : ℂ | 0 < u.re ∧ u.re < 2 ∧ u ≠ 1})
        z
        (Complex.mk (1 / 2) z.im) ∨
      JoinedIn
        ({u : ℂ | 0 < u.re ∧ u.re < 2 ∧ u ≠ 1})
        z
        (Complex.mk (3 / 2) z.im) := by
  by_cases hz_left : z.re < 1
  · left
    exact
      eulerMaclaurin_puncturedVerticalStrip_leftHalf_joined
        hz
        eulerMaclaurin_puncturedVerticalStrip_leftColumn_mem
        hz_left
        real_one_half_lt_one_for_puncturedVerticalStrip
  · have hz_one_le : 1 ≤ z.re :=
      le_of_not_gt hz_left
    by_cases hz_re_eq_one : z.re = 1
    · have hz_im_ne_zero : z.im ≠ 0 := by
        intro hz_im_zero
        have hz_eq_one : z = (1 : ℂ) := by
          exact Complex.ext
            (by
              calc
                z.re = 1 := hz_re_eq_one
                _ = (1 : ℂ).re := rfl)
            (by
              calc
                z.im = 0 := hz_im_zero
                _ = (1 : ℂ).im := rfl)
        exact hz.2.2 hz_eq_one
      left
      have hjoined :
          JoinedIn
            ({u : ℂ | 0 < u.re ∧ u.re < 2 ∧ u ≠ 1})
            (Complex.mk z.re z.im)
            (Complex.mk (1 / 2) z.im) :=
        eulerMaclaurin_puncturedVerticalStrip_nonzeroHeight_horizontalJoined
          (by
            calc
              0 < z.re := hz.1)
          (by
            calc
              z.re < 2 := hz.2.1)
          real_zero_lt_one_half_for_puncturedVerticalStrip
          real_one_half_lt_two_for_puncturedVerticalStrip
          hz_im_ne_zero
      exact Eq.subst
        (motive := fun u : ℂ =>
          JoinedIn
            ({v : ℂ | 0 < v.re ∧ v.re < 2 ∧ v ≠ 1})
            u
            (Complex.mk (1 / 2) z.im))
        (Complex.eta z)
        hjoined
    · right
      have hz_right : 1 < z.re :=
        lt_of_le_of_ne hz_one_le (Ne.symm hz_re_eq_one)
      exact
        eulerMaclaurin_puncturedVerticalStrip_rightHalf_joined
          hz
          eulerMaclaurin_puncturedVerticalStrip_rightColumn_mem
          hz_right
          real_one_lt_three_halves_for_puncturedVerticalStrip

/-- The two safe vertical corridors are joined at any nonzero imaginary
height. -/
theorem eulerMaclaurin_puncturedVerticalStrip_leftCorridor_joined_rightCorridor
    {h : ℝ}
    (hh : h ≠ 0) :
    JoinedIn
      ({u : ℂ | 0 < u.re ∧ u.re < 2 ∧ u ≠ 1})
      (Complex.mk (1 / 2) h)
      (Complex.mk (3 / 2) h) := by
  exact
    eulerMaclaurin_puncturedVerticalStrip_nonzeroHeight_horizontalJoined
      real_zero_lt_one_half_for_puncturedVerticalStrip
      real_one_half_lt_two_for_puncturedVerticalStrip
      real_zero_lt_three_halves_for_puncturedVerticalStrip
      real_three_halves_lt_two_for_puncturedVerticalStrip
      hh

/-- Corridor polygonal-path construction in the punctured vertical strip.

The path first moves each endpoint horizontally to a safe column, moves
vertically in the safe columns, and crosses between the columns at nonzero
height. -/
theorem eulerMaclaurin_puncturedVerticalStrip_joinedIn_via_corridors
    {z w : ℂ}
    (hz : z ∈ ({u : ℂ | 0 < u.re ∧ u.re < 2 ∧ u ≠ 1}))
    (hw : w ∈ ({u : ℂ | 0 < u.re ∧ u.re < 2 ∧ u ≠ 1})) :
    JoinedIn ({u : ℂ | 0 < u.re ∧ u.re < 2 ∧ u ≠ 1}) z w := by
  have hz_corridor :
      JoinedIn
          ({u : ℂ | 0 < u.re ∧ u.re < 2 ∧ u ≠ 1})
          z
          (Complex.mk (1 / 2) z.im) ∨
        JoinedIn
          ({u : ℂ | 0 < u.re ∧ u.re < 2 ∧ u ≠ 1})
          z
          (Complex.mk (3 / 2) z.im) :=
    eulerMaclaurin_puncturedVerticalStrip_joinedTo_safeCorridor hz
  have hw_corridor :
      JoinedIn
          ({u : ℂ | 0 < u.re ∧ u.re < 2 ∧ u ≠ 1})
          w
          (Complex.mk (1 / 2) w.im) ∨
        JoinedIn
          ({u : ℂ | 0 < u.re ∧ u.re < 2 ∧ u ≠ 1})
          w
          (Complex.mk (3 / 2) w.im) :=
    eulerMaclaurin_puncturedVerticalStrip_joinedTo_safeCorridor hw
  cases hz_corridor with
  | inl hz_left =>
      cases hw_corridor with
      | inl hw_left =>
          exact
            hz_left.trans
              ((eulerMaclaurin_puncturedVerticalStrip_leftColumn_verticalJoined).trans
                hw_left.symm)
      | inr hw_right =>
          have hleft_to_right :
              JoinedIn
                ({u : ℂ | 0 < u.re ∧ u.re < 2 ∧ u ≠ 1})
                (Complex.mk (1 / 2) z.im)
                (Complex.mk (3 / 2) w.im) :=
            (eulerMaclaurin_puncturedVerticalStrip_leftColumn_verticalJoined
              (y₁ := z.im) (y₂ := 1)).trans
              ((eulerMaclaurin_puncturedVerticalStrip_leftCorridor_joined_rightCorridor
                (h := 1) one_ne_zero).trans
                (eulerMaclaurin_puncturedVerticalStrip_rightColumn_verticalJoined
                  (y₁ := 1) (y₂ := w.im)))
          exact hz_left.trans (hleft_to_right.trans hw_right.symm)
  | inr hz_right =>
      cases hw_corridor with
      | inl hw_left =>
          have hright_to_left :
              JoinedIn
                ({u : ℂ | 0 < u.re ∧ u.re < 2 ∧ u ≠ 1})
                (Complex.mk (3 / 2) z.im)
                (Complex.mk (1 / 2) w.im) :=
            (eulerMaclaurin_puncturedVerticalStrip_rightColumn_verticalJoined
              (y₁ := z.im) (y₂ := 1)).trans
              ((eulerMaclaurin_puncturedVerticalStrip_leftCorridor_joined_rightCorridor
                (h := 1) one_ne_zero).symm.trans
                (eulerMaclaurin_puncturedVerticalStrip_leftColumn_verticalJoined
                  (y₁ := 1) (y₂ := w.im)))
          exact hz_right.trans (hright_to_left.trans hw_left.symm)
      | inr hw_right =>
          exact
            hz_right.trans
              ((eulerMaclaurin_puncturedVerticalStrip_rightColumn_verticalJoined).trans
                hw_right.symm)

/-- Polygonal-path construction in the punctured vertical strip.

This is the public wrapper around the safe-corridor construction. -/
theorem eulerMaclaurin_puncturedVerticalStrip_joinedIn_via_polygon
    {z w : ℂ}
    (hz : z ∈ ({u : ℂ | 0 < u.re ∧ u.re < 2 ∧ u ≠ 1}))
    (hw : w ∈ ({u : ℂ | 0 < u.re ∧ u.re < 2 ∧ u ≠ 1})) :
    JoinedIn ({u : ℂ | 0 < u.re ∧ u.re < 2 ∧ u ≠ 1}) z w := by
  exact
    eulerMaclaurin_puncturedVerticalStrip_joinedIn_via_corridors
      hz hw

/-- The punctured vertical strip is nonempty. -/
theorem eulerMaclaurin_puncturedVerticalStrip_nonempty :
    ({z : ℂ | 0 < z.re ∧ z.re < 2 ∧ z ≠ 1}).Nonempty := by
  refine ⟨Complex.mk 1 1, ?_⟩
  constructor
  · exact zero_lt_one
  constructor
  · exact one_lt_two
  · intro hbad
    have him : (Complex.mk (1 : ℝ) 1).im = (1 : ℂ).im :=
      congrArg Complex.im hbad
    change (1 : ℝ) = 0 at him
    exact one_ne_zero him

/-- The punctured vertical strip `0 < Re z < 2`, `z ≠ 1`, is path-connected.

Geometrically this is an open vertical strip in the real plane with one point
removed; polygonal paths route around the removed point `1`. -/
theorem eulerMaclaurin_puncturedVerticalStrip_isPathConnected :
    IsPathConnected ({z : ℂ | 0 < z.re ∧ z.re < 2 ∧ z ≠ 1}) := by
  exact
    isPathConnected_iff.mpr
      ⟨eulerMaclaurin_puncturedVerticalStrip_nonempty,
        fun z hz w hw =>
          eulerMaclaurin_puncturedVerticalStrip_joinedIn_via_polygon
            hz hw⟩

/-- The punctured vertical strip `0 < Re z < 2`, `z ≠ 1`, is preconnected. -/
theorem eulerMaclaurin_puncturedVerticalStrip_isPreconnected :
    IsPreconnected ({z : ℂ | 0 < z.re ∧ z.re < 2 ∧ z ≠ 1}) := by
  exact
    (eulerMaclaurin_puncturedVerticalStrip_isPathConnected).isConnected.isPreconnected

/-- The fixed-cutoff defect vanishes on the open half-plane part of the
punctured strip. -/
theorem eulerMaclaurin_fixedCutoffTailIdentityDefect_zero_on_halfPlaneSubset
    (N : ℕ)
    (hN : 0 < N) :
    EqOn
      (eulerMaclaurin_riemannZeta_fixedCutoffTailIdentityDefect N)
      0
      ({z : ℂ | 1 < z.re ∧ z.re < 2}) := by
  intro z hz
  exact
    eulerMaclaurin_riemannZeta_fixedCutoffTailIdentityDefect_eq_zero_on_halfPlane_standard
      N hN z hz.1

/-- The open half-plane part `1 < Re z < 2` accumulates at the base point used
for the punctured-strip identity theorem. -/
theorem eulerMaclaurin_halfPlaneSubset_frequently_near_identityBase :
    ∃ᶠ z in 𝓝[≠] ((3 / 2 : ℝ) : ℂ),
      z ∈ ({z : ℂ | 1 < z.re ∧ z.re < 2}) := by
  have hopen : IsOpen ({z : ℂ | 1 < z.re ∧ z.re < 2}) := by
    have hleft : IsOpen {z : ℂ | 1 < z.re} :=
      isOpen_lt continuous_const Complex.continuous_re
    have hright : IsOpen {z : ℂ | z.re < 2} :=
      isOpen_lt Complex.continuous_re continuous_const
    exact hleft.inter hright
  have hbase : ((3 / 2 : ℝ) : ℂ) ∈ ({z : ℂ | 1 < z.re ∧ z.re < 2}) := by
    constructor
    · exact (lt_div_iff₀' zero_lt_two).mpr (by
        calc
          (1 : ℝ) * 2 = 2 := one_mul 2
          _ < 3 := by
            exact two_lt_three)
    · exact (div_lt_iff₀ zero_lt_two).mpr (by
        calc
          (3 : ℝ) < 3 + 1 := lt_add_of_pos_right 3 zero_lt_one
          _ = 2 * 2 := rfl)
  have heventually :
      ∀ᶠ z in 𝓝[≠] ((3 / 2 : ℝ) : ℂ),
        z ∈ ({z : ℂ | 1 < z.re ∧ z.re < 2}) :=
    mem_nhdsWithin_of_mem_nhds (hopen.mem_nhds hbase)
  exact heventually.frequently

/-- The chosen base point for the identity theorem lies in the punctured
vertical strip. -/
theorem eulerMaclaurin_identityBase_mem_puncturedVerticalStrip :
    ((3 / 2 : ℝ) : ℂ) ∈
      ({z : ℂ | 0 < z.re ∧ z.re < 2 ∧ z ≠ 1}) := by
  constructor
  · exact div_pos zero_lt_three zero_lt_two
  · constructor
    · exact (div_lt_iff₀ zero_lt_two).mpr (by
        calc
          (3 : ℝ) < 3 + 1 := lt_add_of_pos_right 3 zero_lt_one
          _ = 2 * 2 := rfl)
    · intro h
      have hre : (3 / 2 : ℝ) = 1 := by
        exact congrArg Complex.re h
      have hmul : (3 / 2 : ℝ) * 2 = 1 * 2 :=
        congrArg (fun x : ℝ => x * 2) hre
      have hleft : (3 / 2 : ℝ) * 2 = 3 :=
        div_mul_cancel₀ (3 : ℝ) (show (2 : ℝ) ≠ 0 by exact two_ne_zero)
      have hright : (1 : ℝ) * 2 = 2 :=
        one_mul 2
      have hthree_eq_two : (3 : ℝ) = 2 :=
        Eq.trans hleft.symm (Eq.trans hmul hright)
      have hthree_ne_two : (3 : ℝ) ≠ 2 := by
        exact ne_of_gt two_lt_three
      exact hthree_ne_two hthree_eq_two

/-- Identity theorem specialized to a fixed-cutoff defect on the punctured
vertical strip, using its vanishing on the half-plane substrip. -/
theorem eulerMaclaurin_fixedCutoffTailIdentityDefect_identityTheorem_from_analytic_zeroSet
    (N : ℕ)
    (hN : 0 < N) :
    EqOn
      (eulerMaclaurin_riemannZeta_fixedCutoffTailIdentityDefect N)
      0
      ({z : ℂ | 0 < z.re ∧ z.re < 2 ∧ z ≠ 1}) := by
  have han :
      AnalyticOnNhd ℂ
        (eulerMaclaurin_riemannZeta_fixedCutoffTailIdentityDefect N)
        ({z : ℂ | 0 < z.re ∧ z.re < 2 ∧ z ≠ 1}) :=
    eulerMaclaurin_fixedCutoffTailIdentityDefect_analyticOnNhd_puncturedStrip
      N hN
  have hpre :
      IsPreconnected ({z : ℂ | 0 < z.re ∧ z.re < 2 ∧ z ≠ 1}) :=
    eulerMaclaurin_puncturedVerticalStrip_isPreconnected
  have hbase_mem :
      ((3 / 2 : ℝ) : ℂ) ∈ ({z : ℂ | 0 < z.re ∧ z.re < 2 ∧ z ≠ 1}) := by
    exact eulerMaclaurin_identityBase_mem_puncturedVerticalStrip
  have hfreq :
      ∃ᶠ z in 𝓝[≠] ((3 / 2 : ℝ) : ℂ),
        eulerMaclaurin_riemannZeta_fixedCutoffTailIdentityDefect N z = 0 :=
    eulerMaclaurin_halfPlaneSubset_frequently_near_identityBase.mono
      (fun z hz =>
        eulerMaclaurin_fixedCutoffTailIdentityDefect_zero_on_halfPlaneSubset
          N hN hz)
  exact
    han.eqOn_zero_of_preconnected_of_frequently_eq_zero
      hpre hbase_mem hfreq

/-- Identity theorem for the fixed-cutoff Euler-Maclaurin defect on the
connected punctured strip.

This is the standard complex-analysis step: the fixed-cutoff defect is
holomorphic on the punctured strip and vanishes on the nonempty open subset
`1 < Re z < 2`, hence it vanishes throughout the connected component of the
punctured strip. -/
theorem eulerMaclaurin_fixedCutoffTailIdentityDefect_identityTheorem_from_halfPlaneZero_standard
    (N : ℕ)
    (hN : 0 < N)
    (z : ℂ)
    (hz_re_pos : 0 < z.re)
    (hz_re_lt_two : z.re < 2)
    (hz_ne_one : z ≠ 1) :
    eulerMaclaurin_riemannZeta_fixedCutoffTailIdentityDefect N z = 0 := by
  exact
    eulerMaclaurin_fixedCutoffTailIdentityDefect_identityTheorem_from_analytic_zeroSet
      N hN z ⟨hz_re_pos, hz_re_lt_two, hz_ne_one⟩

/-- Identity theorem for the fixed-cutoff Euler-Maclaurin defect on the
connected punctured strip. -/
theorem eulerMaclaurin_fixedCutoffTailIdentityDefect_analyticContinuation_zero_on_puncturedStrip_standard
    (N : ℕ)
    (hN : 0 < N)
    (z : ℂ)
    (hz_re_pos : 0 < z.re)
    (hz_re_lt_two : z.re < 2)
    (hz_ne_one : z ≠ 1) :
    eulerMaclaurin_riemannZeta_fixedCutoffTailIdentityDefect N z = 0 := by
  exact
    eulerMaclaurin_fixedCutoffTailIdentityDefect_identityTheorem_from_halfPlaneZero_standard
      N hN z hz_re_pos hz_re_lt_two hz_ne_one

/-- Identity theorem for the fixed-cutoff Euler-Maclaurin defect on the
connected punctured strip. -/
theorem eulerMaclaurin_fixedCutoffTailIdentityDefect_identityTheorem_on_puncturedStrip_standard
    (N : ℕ)
    (hN : 0 < N)
    (z : ℂ)
    (hz_re_pos : 0 < z.re)
    (hz_re_lt_two : z.re < 2)
    (hz_ne_one : z ≠ 1) :
    eulerMaclaurin_riemannZeta_fixedCutoffTailIdentityDefect N z = 0 := by
  exact
    eulerMaclaurin_fixedCutoffTailIdentityDefect_analyticContinuation_zero_on_puncturedStrip_standard
      N hN z hz_re_pos hz_re_lt_two hz_ne_one

/-- Fixed-cutoff defect vanishes on the convergent half-plane by the
Dirichlet-series split and the fixed-cutoff Euler-Maclaurin formula. -/
theorem eulerMaclaurin_riemannZeta_fixedCutoffTailIdentityDefect_eq_zero_on_halfPlane_standard
    (N : ℕ)
    (hN : 0 < N)
    (z : ℂ)
    (hhalf_plane : 1 < z.re) :
    eulerMaclaurin_riemannZeta_fixedCutoffTailIdentityDefect N z = 0 := by
  have hsplit :
      HasSum
        (fun n : ℕ =>
          if N < n then
            (1 : ℂ) / ((n : ℂ) ^ z)
          else
            0)
        (riemannZeta z - eulerMaclaurinZetaFinitePartWithCutoff N z) :=
    eulerMaclaurin_riemannZeta_fixedCutoff_halfPlane_finite_split_tail_hasSum
      N z hhalf_plane
  have htail :
      HasSum
        (fun n : ℕ =>
          if N < n then
            (1 : ℂ) / ((n : ℂ) ^ z)
          else
            0)
        (eulerMaclaurinZetaMainTermWithCutoff N z +
          eulerMaclaurinZetaEndpointTermWithCutoff N z +
          eulerMaclaurinZetaBernoulliIntegralRemainderWithCutoff N z) :=
    eulerMaclaurin_riemannZeta_fixedCutoff_postCutoffTail_ownerTerms_hasSum
      N hN z hhalf_plane
  have hidentity :
      riemannZeta z - eulerMaclaurinZetaFinitePartWithCutoff N z =
        eulerMaclaurinZetaMainTermWithCutoff N z +
          eulerMaclaurinZetaEndpointTermWithCutoff N z +
          eulerMaclaurinZetaBernoulliIntegralRemainderWithCutoff N z :=
    hsplit.unique htail
  unfold eulerMaclaurin_riemannZeta_fixedCutoffTailIdentityDefect
  exact sub_eq_zero.mpr hidentity

/-- Identity theorem for the fixed-cutoff Euler-Maclaurin defect on the
connected punctured strip. -/
theorem eulerMaclaurin_riemannZeta_fixedCutoffTailIdentityDefect_eq_zero_on_puncturedStrip_by_identityTheorem_standard
    (N : ℕ)
    (hN : 0 < N)
    (z : ℂ)
    (hz_re_pos : 0 < z.re)
    (hz_re_lt_two : z.re < 2)
    (hz_ne_one : z ≠ 1) :
    eulerMaclaurin_riemannZeta_fixedCutoffTailIdentityDefect N z = 0 := by
  exact
    eulerMaclaurin_fixedCutoffTailIdentityDefect_identityTheorem_on_puncturedStrip_standard
      N hN z hz_re_pos hz_re_lt_two hz_ne_one

/-- Boundary-line vanishing of the Euler-Maclaurin tail defect by analytic
continuation.

The defect is holomorphic on the punctured strip, vanishes on the connected
open subset `1 < Re z ≤ 2` by the half-plane Dirichlet-series calculation, and
therefore vanishes at the non-pole boundary points on `Re z = 1` by the
identity theorem/continuity of the owner continuation. -/
theorem eulerMaclaurin_riemannZeta_tailIdentityDefect_boundaryLine_eq_zero_by_identityTheorem_standard
    (z : ℂ)
    (hz_re : z.re = 1)
    (hz_ne_one : z ≠ 1) :
    eulerMaclaurin_riemannZeta_tailIdentityDefect z = 0 := by
  have hfixed :
      eulerMaclaurin_riemannZeta_fixedCutoffTailIdentityDefect
        (eulerMaclaurinPoleClearedZetaCutoff z) z = 0 :=
    eulerMaclaurin_riemannZeta_fixedCutoffTailIdentityDefect_eq_zero_on_puncturedStrip_by_identityTheorem_standard
      (eulerMaclaurinPoleClearedZetaCutoff z)
      (eulerMaclaurinPoleClearedZetaCutoff_pos z)
      z
      (Eq.subst (motive := fun x : ℝ => 0 < x) hz_re.symm zero_lt_one)
      (Eq.subst (motive := fun x : ℝ => x < 2) hz_re.symm one_lt_two)
      hz_ne_one
  exact
    Eq.trans
      (eulerMaclaurin_riemannZeta_tailIdentityDefect_eq_fixedCutoffDefect z)
      hfixed

/-- Boundary-line analytic-continuation uniqueness for the first-order
Euler-Maclaurin zeta tail.

The half-plane identity obtained from the Dirichlet series and
Euler-Maclaurin has a meromorphic continuation to the closed strip; after
removing the pole point `z = 1`, uniqueness of analytic continuation gives
the stated boundary-line equality at `Re z = 1`.  This is the exact owner
API needed for the boundary case, not a restatement of the public wrapper;
cf. Edwards, Ch. 1, and Titchmarsh, Ch. 2. -/
theorem eulerMaclaurin_riemannZeta_boundaryLine_tail_identity_by_analyticContinuation_standard
    (z : ℂ)
    (hz_re : z.re = 1)
    (hz_ne_one : z ≠ 1) :
    riemannZeta z - eulerMaclaurinZetaFinitePart z =
      eulerMaclaurinZetaMainTerm z +
        eulerMaclaurinZetaEndpointTerm z +
        eulerMaclaurinZetaBernoulliIntegralRemainder z := by
  exact
    eulerMaclaurin_riemannZeta_tailIdentity_of_defect_eq_zero
      (eulerMaclaurin_riemannZeta_tailIdentityDefect_boundaryLine_eq_zero_by_identityTheorem_standard
        z hz_re hz_ne_one)

/-- Boundary-line analytic continuation of the first-order Euler-Maclaurin
tail identity.

At `Re z = 1`, the ordinary Dirichlet tail is no longer absolutely summable;
the equality is the Abel/Euler-Maclaurin continuation of the half-plane tail
formula, away from the pole `z = 1`. -/
theorem eulerMaclaurin_riemannZeta_boundaryLine_tail_identity_with_bernoulliIntegralRemainder_standard
    (z : ℂ)
    (hz_re : z.re = 1)
    (hz_ne_one : z ≠ 1) :
    riemannZeta z - eulerMaclaurinZetaFinitePart z =
      eulerMaclaurinZetaMainTerm z +
        eulerMaclaurinZetaEndpointTerm z +
        eulerMaclaurinZetaBernoulliIntegralRemainder z := by
  exact
    eulerMaclaurin_riemannZeta_boundaryLine_tail_identity_by_analyticContinuation_standard
      z hz_re hz_ne_one

/-- First-order Euler-Maclaurin tail identity for the Riemann zeta function at
the owner cutoff `N = ⌊2 + ‖s‖⌋₊`.

This is the exact analytic theorem: the finite Dirichlet window is removed from
`ζ(s)`, and Euler-Maclaurin applied to the remaining tail of
`x ↦ x^{-s}` gives
`N^(1-s)/(s-1) + (1/2)N^{-s} - s ∫_N^∞ B₁({x})x^{-s-1} dx`.
It combines the Dirichlet-series split in `Re s > 1` with analytic
continuation across the closed strip away from `s = 1`; cf. Apostol, Analytic
Number Theory, Ch. 3, and Titchmarsh, Ch. 2. -/
theorem eulerMaclaurin_riemannZeta_tail_identity_with_bernoulliIntegralRemainder_standard
    (z : ℂ)
    (hz_one : 1 ≤ z.re)
    (hz_two : z.re ≤ 2)
    (hz_ne_one : z ≠ 1) :
    riemannZeta z - eulerMaclaurinZetaFinitePart z =
      eulerMaclaurinZetaMainTerm z +
        eulerMaclaurinZetaEndpointTerm z +
        eulerMaclaurinZetaBernoulliIntegralRemainder z := by
  by_cases hhalf_plane : 1 < z.re
  · have hsplit :
        HasSum
          (fun n : ℕ =>
            if eulerMaclaurinPoleClearedZetaCutoff z < n then
              (1 : ℂ) / ((n : ℂ) ^ z)
            else
              0)
          (riemannZeta z - eulerMaclaurinZetaFinitePart z) :=
      eulerMaclaurin_riemannZeta_halfPlane_finite_split_tail_hasSum z hhalf_plane
    have htail :
        HasSum
          (fun n : ℕ =>
            if eulerMaclaurinPoleClearedZetaCutoff z < n then
              (1 : ℂ) / ((n : ℂ) ^ z)
            else
              0)
          (eulerMaclaurinZetaMainTerm z +
            eulerMaclaurinZetaEndpointTerm z +
            eulerMaclaurinZetaBernoulliIntegralRemainder z) :=
      eulerMaclaurin_riemannZeta_postCutoffTail_eulerMaclaurin_hasSum_standard
        z hz_one hz_two hhalf_plane
    exact hsplit.unique htail
  · have hz_re_le_one : z.re ≤ 1 :=
      le_of_not_gt hhalf_plane
    have hz_re_eq_one : z.re = 1 :=
      le_antisymm hz_re_le_one hz_one
    exact
      eulerMaclaurin_riemannZeta_boundaryLine_tail_identity_with_bernoulliIntegralRemainder_standard
        z hz_re_eq_one hz_ne_one

/-- First-order Euler-Maclaurin formula for the raw Riemann zeta away from its
pole, with owner cutoff `N = ⌊2 + ‖s‖⌋₊`.

This is the canonical analytic input: split the Dirichlet series at `N`, apply
Euler-Maclaurin to the tail of `x ↦ x^{-s}`, and write the remainder as the
periodic Bernoulli integral `-s ∫_N^∞ B₁({x}) x^{-s-1} dx`; cf. Apostol,
Analytic Number Theory, Ch. 3, and Titchmarsh, Ch. 2. -/
theorem eulerMaclaurin_riemannZeta_formula_with_bernoulliIntegralRemainder_standard
    (z : ℂ)
    (hz_one : 1 ≤ z.re)
    (hz_two : z.re ≤ 2)
    (hz_ne_one : z ≠ 1) :
    riemannZeta z =
      eulerMaclaurinZetaFinitePart z +
        eulerMaclaurinZetaMainTerm z +
        eulerMaclaurinZetaEndpointTerm z +
        eulerMaclaurinZetaBernoulliIntegralRemainder z := by
  have htail :
      riemannZeta z - eulerMaclaurinZetaFinitePart z =
        eulerMaclaurinZetaMainTerm z +
          eulerMaclaurinZetaEndpointTerm z +
          eulerMaclaurinZetaBernoulliIntegralRemainder z :=
    eulerMaclaurin_riemannZeta_tail_identity_with_bernoulliIntegralRemainder_standard
      z hz_one hz_two hz_ne_one
  have hraw :
      riemannZeta z =
        eulerMaclaurinZetaFinitePart z +
          (eulerMaclaurinZetaMainTerm z +
            eulerMaclaurinZetaEndpointTerm z +
            eulerMaclaurinZetaBernoulliIntegralRemainder z) :=
    complex_eq_add_of_sub_eq htail
  calc
    riemannZeta z =
        eulerMaclaurinZetaFinitePart z +
          (eulerMaclaurinZetaMainTerm z +
            eulerMaclaurinZetaEndpointTerm z +
            eulerMaclaurinZetaBernoulliIntegralRemainder z) :=
      hraw
    _ = eulerMaclaurinZetaFinitePart z +
          eulerMaclaurinZetaMainTerm z +
          eulerMaclaurinZetaEndpointTerm z +
          eulerMaclaurinZetaBernoulliIntegralRemainder z := by
      calc
        eulerMaclaurinZetaFinitePart z +
            (eulerMaclaurinZetaMainTerm z +
              eulerMaclaurinZetaEndpointTerm z +
              eulerMaclaurinZetaBernoulliIntegralRemainder z) =
            (eulerMaclaurinZetaFinitePart z +
              (eulerMaclaurinZetaMainTerm z +
                eulerMaclaurinZetaEndpointTerm z)) +
              eulerMaclaurinZetaBernoulliIntegralRemainder z := by
          exact (add_assoc
            (eulerMaclaurinZetaFinitePart z)
            (eulerMaclaurinZetaMainTerm z + eulerMaclaurinZetaEndpointTerm z)
            (eulerMaclaurinZetaBernoulliIntegralRemainder z)).symm
        _ = eulerMaclaurinZetaFinitePart z +
              eulerMaclaurinZetaMainTerm z +
              eulerMaclaurinZetaEndpointTerm z +
              eulerMaclaurinZetaBernoulliIntegralRemainder z := by
          exact congrArg
            (fun w : ℂ => w + eulerMaclaurinZetaBernoulliIntegralRemainder z)
            ((add_assoc
              (eulerMaclaurinZetaFinitePart z)
              (eulerMaclaurinZetaMainTerm z)
              (eulerMaclaurinZetaEndpointTerm z)).symm)

/-- Multiplication by `s - 1` transports the raw non-pole
Euler-Maclaurin formula to the existing pole-cleared term definitions. -/
theorem eulerMaclaurin_poleCleared_formula_of_raw_formula
    {z : ℂ}
    (hz_ne_one : z ≠ 1)
    (hraw :
      riemannZeta z =
        eulerMaclaurinZetaFinitePart z +
          eulerMaclaurinZetaMainTerm z +
          eulerMaclaurinZetaEndpointTerm z +
          eulerMaclaurinZetaBernoulliIntegralRemainder z) :
    poleClearedRiemannZeta z =
      eulerMaclaurinPoleClearedZetaFinitePart z +
        eulerMaclaurinPoleClearedZetaMainTerm z +
        eulerMaclaurinPoleClearedZetaEndpointTerm z +
        eulerMaclaurinPoleClearedZetaBernoulliIntegralRemainder z := by
  let a : ℂ := z - 1
  let F : ℂ := eulerMaclaurinZetaFinitePart z
  let M : ℂ := eulerMaclaurinZetaMainTerm z
  let E : ℂ := eulerMaclaurinZetaEndpointTerm z
  let R : ℂ := eulerMaclaurinZetaBernoulliIntegralRemainder z
  have hpole :
      poleClearedRiemannZeta z = a * riemannZeta z := by
    exact poleClearedRiemannZeta_eq_of_ne_one hz_ne_one
  have hraw_local : riemannZeta z = F + M + E + R :=
    hraw
  have hmul_raw :
      a * riemannZeta z = a * (F + M + E + R) :=
    congrArg (fun w : ℂ => a * w) hraw_local
  have hdistribute :
      a * (F + M + E + R) =
        a * F + a * M + a * E + a * R := by
    calc
      a * (F + M + E + R) = a * ((F + M + E) + R) := rfl
      _ = a * (F + M + E) + a * R := by
        exact mul_add a (F + M + E) R
      _ = (a * (F + M) + a * E) + a * R := by
        exact congrArg (fun w : ℂ => w + a * R) (mul_add a (F + M) E)
      _ = ((a * F + a * M) + a * E) + a * R := by
        exact congrArg
          (fun w : ℂ => (w + a * E) + a * R)
          (mul_add a F M)
      _ = a * F + a * M + a * E + a * R := rfl
  have hF :
      a * F = eulerMaclaurinPoleClearedZetaFinitePart z :=
    (eulerMaclaurinPoleClearedZetaFinitePart_eq_mul_raw z).symm
  have hM :
      a * M = eulerMaclaurinPoleClearedZetaMainTerm z :=
    (eulerMaclaurinPoleClearedZetaMainTerm_eq_mul_raw hz_ne_one).symm
  have hE :
      a * E = eulerMaclaurinPoleClearedZetaEndpointTerm z :=
    (eulerMaclaurinPoleClearedZetaEndpointTerm_eq_mul_raw z).symm
  have hR :
      a * R = eulerMaclaurinPoleClearedZetaBernoulliIntegralRemainder z :=
    (eulerMaclaurinPoleClearedZetaBernoulliIntegralRemainder_eq_mul_raw z).symm
  have hterms :
      a * F + a * M + a * E + a * R =
        eulerMaclaurinPoleClearedZetaFinitePart z +
          eulerMaclaurinPoleClearedZetaMainTerm z +
          eulerMaclaurinPoleClearedZetaEndpointTerm z +
          eulerMaclaurinPoleClearedZetaBernoulliIntegralRemainder z := by
    calc
      a * F + a * M + a * E + a * R =
          eulerMaclaurinPoleClearedZetaFinitePart z + a * M + a * E + a * R := by
        exact congrArg
          (fun w : ℂ => w + a * M + a * E + a * R)
          hF
      _ = eulerMaclaurinPoleClearedZetaFinitePart z +
            eulerMaclaurinPoleClearedZetaMainTerm z + a * E + a * R := by
        exact congrArg
          (fun w : ℂ => eulerMaclaurinPoleClearedZetaFinitePart z + w + a * E + a * R)
          hM
      _ = eulerMaclaurinPoleClearedZetaFinitePart z +
            eulerMaclaurinPoleClearedZetaMainTerm z +
            eulerMaclaurinPoleClearedZetaEndpointTerm z + a * R := by
        exact congrArg
          (fun w : ℂ =>
            eulerMaclaurinPoleClearedZetaFinitePart z +
              eulerMaclaurinPoleClearedZetaMainTerm z + w + a * R)
          hE
      _ = eulerMaclaurinPoleClearedZetaFinitePart z +
            eulerMaclaurinPoleClearedZetaMainTerm z +
            eulerMaclaurinPoleClearedZetaEndpointTerm z +
            eulerMaclaurinPoleClearedZetaBernoulliIntegralRemainder z := by
        exact congrArg
          (fun w : ℂ =>
            eulerMaclaurinPoleClearedZetaFinitePart z +
              eulerMaclaurinPoleClearedZetaMainTerm z +
              eulerMaclaurinPoleClearedZetaEndpointTerm z + w)
          hR
  calc
    poleClearedRiemannZeta z = a * riemannZeta z :=
      hpole
    _ = a * (F + M + E + R) :=
      hmul_raw
    _ = a * F + a * M + a * E + a * R :=
      hdistribute
    _ = eulerMaclaurinPoleClearedZetaFinitePart z +
          eulerMaclaurinPoleClearedZetaMainTerm z +
          eulerMaclaurinPoleClearedZetaEndpointTerm z +
          eulerMaclaurinPoleClearedZetaBernoulliIntegralRemainder z :=
      hterms

/-- Subtracting a left summand from a two-term sum leaves the right summand. -/
theorem complex_add_sub_left_cancel
    (S R : ℂ) :
    (S + R) - S = R := by
  calc
    (S + R) - S = S + R + -S := by
      exact sub_eq_add_neg (S + R) S
    _ = S + (R + -S) := by
      exact add_assoc S R (-S)
    _ = S + (-S + R) := by
      exact congrArg (fun x : ℂ => S + x) (add_comm R (-S))
    _ = (S + -S) + R := by
      exact (add_assoc S (-S) R).symm
    _ = 0 + R := by
      exact congrArg (fun x : ℂ => x + R) (add_neg_cancel S)
    _ = R := by
      exact zero_add R

/-- Removable value of the pole-cleared first-order Euler-Maclaurin formula at
`s = 1`.

This is the endpoint cancellation of the raw formula after multiplying by
`s - 1`: the finite, endpoint, and Bernoulli terms vanish and the main term
has value `N^0 = 1`, matching the residue-normalized removable value
`poleClearedRiemannZeta 1 = 1`. -/
theorem eulerMaclaurin_poleCleared_formula_at_one_from_removable_value :
    poleClearedRiemannZeta (1 : ℂ) =
      eulerMaclaurinPoleClearedZetaFinitePart (1 : ℂ) +
        eulerMaclaurinPoleClearedZetaMainTerm (1 : ℂ) +
        eulerMaclaurinPoleClearedZetaEndpointTerm (1 : ℂ) +
        eulerMaclaurinPoleClearedZetaBernoulliIntegralRemainder (1 : ℂ) := by
  have hpole : poleClearedRiemannZeta (1 : ℂ) = 1 :=
    poleClearedRiemannZeta_one
  have hfinite :
      eulerMaclaurinPoleClearedZetaFinitePart (1 : ℂ) = 0 := by
    unfold eulerMaclaurinPoleClearedZetaFinitePart
    let S : ℂ :=
      ∑ n ∈ Finset.Icc 1 (eulerMaclaurinPoleClearedZetaCutoff (1 : ℂ)),
        1 / (((n : ℕ) : ℂ) ^ (1 : ℂ))
    calc
      ((1 : ℂ) - 1) * S = 0 * S := by
        exact congrArg (fun w : ℂ => w * S) (sub_self (1 : ℂ))
      _ = 0 := by
        exact zero_mul S
  have hmain :
      eulerMaclaurinPoleClearedZetaMainTerm (1 : ℂ) = 1 := by
    unfold eulerMaclaurinPoleClearedZetaMainTerm
    let N : ℂ := ((eulerMaclaurinPoleClearedZetaCutoff (1 : ℂ) : ℕ) : ℂ)
    calc
      N ^ ((1 : ℂ) - 1) = N ^ (0 : ℂ) := by
        exact congrArg (fun w : ℂ => N ^ w) (sub_self (1 : ℂ))
      _ = 1 := by
        exact Complex.cpow_zero N
  have hendpoint :
      eulerMaclaurinPoleClearedZetaEndpointTerm (1 : ℂ) = 0 := by
    unfold eulerMaclaurinPoleClearedZetaEndpointTerm
    let U : ℂ :=
      1 / (((eulerMaclaurinPoleClearedZetaCutoff (1 : ℂ) : ℕ) : ℂ) ^ (1 : ℂ))
    calc
      (((1 : ℂ) - 1) / 2) * U = (0 / 2 : ℂ) * U := by
        exact congrArg (fun w : ℂ => (w / 2) * U) (sub_self (1 : ℂ))
      _ = 0 * U := by
        exact congrArg (fun w : ℂ => w * U) (zero_div (2 : ℂ))
      _ = 0 := by
        exact zero_mul U
  have hremainder :
      eulerMaclaurinPoleClearedZetaBernoulliIntegralRemainder (1 : ℂ) = 0 := by
    unfold eulerMaclaurinPoleClearedZetaBernoulliIntegralRemainder
    let I : ℂ := eulerMaclaurinPoleClearedZetaBernoulliIntegralCore (1 : ℂ)
    calc
      -(((1 : ℂ) - 1) * 1) * I = -(0 * 1) * I := by
        exact congrArg (fun w : ℂ => -(w * 1) * I) (sub_self (1 : ℂ))
      _ = -0 * I := by
        exact congrArg (fun w : ℂ => -w * I) (zero_mul (1 : ℂ))
      _ = 0 * I := by
        exact congrArg (fun w : ℂ => w * I) (neg_zero : -(0 : ℂ) = 0)
      _ = 0 := by
        exact zero_mul I
  calc
    poleClearedRiemannZeta (1 : ℂ) = 1 :=
      hpole
    _ = 0 + 1 + 0 + 0 := by
      calc
        (1 : ℂ) = 0 + 1 := by
          exact (zero_add (1 : ℂ)).symm
        _ = 0 + 1 + 0 := by
          exact (add_zero (0 + (1 : ℂ))).symm
        _ = 0 + 1 + 0 + 0 := by
          exact (add_zero (0 + (1 : ℂ) + 0)).symm
    _ = eulerMaclaurinPoleClearedZetaFinitePart (1 : ℂ) +
          eulerMaclaurinPoleClearedZetaMainTerm (1 : ℂ) +
          eulerMaclaurinPoleClearedZetaEndpointTerm (1 : ℂ) +
          eulerMaclaurinPoleClearedZetaBernoulliIntegralRemainder (1 : ℂ) := by
      calc
        0 + 1 + 0 + 0 =
            eulerMaclaurinPoleClearedZetaFinitePart (1 : ℂ) + 1 + 0 + 0 := by
          exact congrArg (fun w : ℂ => w + 1 + 0 + 0) hfinite.symm
        _ = eulerMaclaurinPoleClearedZetaFinitePart (1 : ℂ) +
              eulerMaclaurinPoleClearedZetaMainTerm (1 : ℂ) + 0 + 0 := by
          exact congrArg
            (fun w : ℂ =>
              eulerMaclaurinPoleClearedZetaFinitePart (1 : ℂ) + w + 0 + 0)
            hmain.symm
        _ = eulerMaclaurinPoleClearedZetaFinitePart (1 : ℂ) +
              eulerMaclaurinPoleClearedZetaMainTerm (1 : ℂ) +
              eulerMaclaurinPoleClearedZetaEndpointTerm (1 : ℂ) + 0 := by
          exact congrArg
            (fun w : ℂ =>
              eulerMaclaurinPoleClearedZetaFinitePart (1 : ℂ) +
                eulerMaclaurinPoleClearedZetaMainTerm (1 : ℂ) + w + 0)
            hendpoint.symm
        _ = eulerMaclaurinPoleClearedZetaFinitePart (1 : ℂ) +
              eulerMaclaurinPoleClearedZetaMainTerm (1 : ℂ) +
              eulerMaclaurinPoleClearedZetaEndpointTerm (1 : ℂ) +
              eulerMaclaurinPoleClearedZetaBernoulliIntegralRemainder (1 : ℂ) := by
          exact congrArg
            (fun w : ℂ =>
              eulerMaclaurinPoleClearedZetaFinitePart (1 : ℂ) +
                eulerMaclaurinPoleClearedZetaMainTerm (1 : ℂ) +
                eulerMaclaurinPoleClearedZetaEndpointTerm (1 : ℂ) + w)
            hremainder.symm

/-- First-order Euler-Maclaurin formula for the pole-cleared zeta on
`1 ≤ Re s ≤ 2`, with cutoff `⌊2 + ‖s‖⌋₊` and explicit Bernoulli integral
remainder. -/
theorem eulerMaclaurin_poleClearedRiemannZeta_formula_with_bernoulliIntegralRemainder_standard
    (z : ℂ)
    (hz_one : 1 ≤ z.re)
    (hz_two : z.re ≤ 2) :
    poleClearedRiemannZeta z =
      eulerMaclaurinPoleClearedZetaFinitePart z +
        eulerMaclaurinPoleClearedZetaMainTerm z +
        eulerMaclaurinPoleClearedZetaEndpointTerm z +
        eulerMaclaurinPoleClearedZetaBernoulliIntegralRemainder z := by
  by_cases hz_ne_one : z ≠ 1
  · have hraw :
        riemannZeta z =
          eulerMaclaurinZetaFinitePart z +
            eulerMaclaurinZetaMainTerm z +
            eulerMaclaurinZetaEndpointTerm z +
            eulerMaclaurinZetaBernoulliIntegralRemainder z :=
      eulerMaclaurin_riemannZeta_formula_with_bernoulliIntegralRemainder_standard
        z hz_one hz_two hz_ne_one
    exact eulerMaclaurin_poleCleared_formula_of_raw_formula hz_ne_one hraw
  · have hz_eq_one : z = 1 :=
      of_not_not hz_ne_one
    exact Eq.subst
      (motive := fun w : ℂ =>
        poleClearedRiemannZeta w =
          eulerMaclaurinPoleClearedZetaFinitePart w +
            eulerMaclaurinPoleClearedZetaMainTerm w +
            eulerMaclaurinPoleClearedZetaEndpointTerm w +
            eulerMaclaurinPoleClearedZetaBernoulliIntegralRemainder w)
      hz_eq_one.symm
      eulerMaclaurin_poleCleared_formula_at_one_from_removable_value

/-- Euler-Maclaurin formula identifies the difference-defined pole-cleared
remainder with the explicit Bernoulli-periodic integral remainder. -/
theorem eulerMaclaurinPoleClearedZetaRemainderTerm_eq_bernoulliIntegralRemainder
    (z : ℂ)
    (hz_one : 1 ≤ z.re)
    (hz_two : z.re ≤ 2) :
    eulerMaclaurinPoleClearedZetaRemainderTerm z =
      eulerMaclaurinPoleClearedZetaBernoulliIntegralRemainder z := by
  unfold eulerMaclaurinPoleClearedZetaRemainderTerm
  let S : ℂ :=
    eulerMaclaurinPoleClearedZetaFinitePart z +
      eulerMaclaurinPoleClearedZetaMainTerm z +
      eulerMaclaurinPoleClearedZetaEndpointTerm z
  let R : ℂ := eulerMaclaurinPoleClearedZetaBernoulliIntegralRemainder z
  have hformula :
      poleClearedRiemannZeta z = S + R :=
    eulerMaclaurin_poleClearedRiemannZeta_formula_with_bernoulliIntegralRemainder_standard
      z hz_one hz_two
  have hsub :
      poleClearedRiemannZeta z - S = (S + R) - S :=
    congrArg (fun w : ℂ => w - S) hformula
  have hcancel : (S + R) - S = R :=
    complex_add_sub_left_cancel S R
  exact Eq.trans hsub hcancel

/-- The first periodic Bernoulli sawtooth is bounded by one in absolute value. -/
theorem eulerMaclaurinFirstPeriodicBernoulli_abs_le_one
    (x : ℝ) :
    |eulerMaclaurinFirstPeriodicBernoulli x| ≤ 1 := by
  unfold eulerMaclaurinFirstPeriodicBernoulli
  have hfract_nonneg : 0 ≤ Int.fract x :=
    Int.fract_nonneg x
  have hfract_le_one : Int.fract x ≤ 1 :=
    le_of_lt (Int.fract_lt_one x)
  have hlower : -(1 : ℝ) ≤ Int.fract x - 1 / 2 := by
    have hneg_half : -(1 : ℝ) ≤ -(1 / 2 : ℝ) := by
      exact neg_le_neg one_half_le_one
    have hshift : -(1 / 2 : ℝ) ≤ Int.fract x - 1 / 2 := by
      calc
        -(1 / 2 : ℝ) = 0 - 1 / 2 := by
          exact (zero_sub (1 / 2 : ℝ)).symm
        _ ≤ Int.fract x - 1 / 2 :=
          sub_le_sub_right hfract_nonneg (1 / 2 : ℝ)
    exact le_trans hneg_half hshift
  have hupper : Int.fract x - 1 / 2 ≤ 1 := by
    have hhalf_nonneg : 0 ≤ (1 / 2 : ℝ) :=
      one_half_nonneg
    calc
      Int.fract x - 1 / 2 ≤ Int.fract x :=
        sub_le_self (Int.fract x) hhalf_nonneg
      _ ≤ 1 :=
        hfract_le_one
  exact abs_le.mpr ⟨hlower, hupper⟩

/-- Positive-real complex powers in the Euler-Maclaurin tail are bounded by the
corresponding real power majorant. -/
theorem norm_real_cpow_neg_z_add_one_le_rpow
    {x : ℝ}
    (hx : 0 < x)
    (z : ℂ)
    (hz_one : 1 ≤ z.re) :
    ‖((x : ℝ) : ℂ) ^ (-(z + 1))‖ ≤ x ^ (-(z.re + 1)) := by
  have hnorm :
      ‖((x : ℝ) : ℂ) ^ (-(z + 1))‖ =
        x ^ (-(z + 1)).re := by
    calc
      ‖((x : ℝ) : ℂ) ^ (-(z + 1))‖ =
          Complex.abs (((x : ℝ) : ℂ) ^ (-(z + 1))) := by
        exact Complex.norm_eq_abs (((x : ℝ) : ℂ) ^ (-(z + 1)))
      _ = x ^ (-(z + 1)).re := by
        exact Complex.abs_cpow_eq_rpow_re_of_pos hx (-(z + 1))
  have hre : (-(z + 1)).re = -(z.re + 1) := by
    calc
      (-(z + 1)).re = -((z + 1).re) := by
        exact Complex.neg_re (z + 1)
      _ = -(z.re + (1 : ℂ).re) := by
        exact congrArg Neg.neg (Complex.add_re z 1)
      _ = -(z.re + 1) := by
        exact congrArg (fun t : ℝ => -(z.re + t)) Complex.one_re
  exact le_of_eq
    (Eq.trans hnorm (congrArg (fun e : ℝ => x ^ e) hre))

/-- Scalar tail integral bound for the real power majorant after a cutoff
`N ≥ 1` and exponent `σ ≥ 1`. -/
theorem integral_Ioi_rpow_neg_re_add_one_le_one_of_one_le_cutoff
    {N σ : ℝ}
    (hN : 1 ≤ N)
    (hσ : 1 ≤ σ) :
    ∫ x in Set.Ioi N, x ^ (-(σ + 1)) ≤ 1 := by
  have hN_pos : 0 < N :=
    lt_of_lt_of_le zero_lt_one hN
  have htwo_le : (2 : ℝ) ≤ σ + 1 := by
    calc
      (2 : ℝ) = 1 + 1 := by
        exact (one_add_one_eq_two : (1 : ℝ) + 1 = 2).symm
      _ ≤ σ + 1 :=
        add_le_add hσ le_rfl
  have hone_lt : (1 : ℝ) < σ + 1 :=
    lt_of_lt_of_le one_lt_two htwo_le
  have ha : -(σ + 1) < -(1 : ℝ) :=
    neg_lt_neg hone_lt
  have hintegral :
      ∫ x in Set.Ioi N, x ^ (-(σ + 1)) =
        -N ^ (-(σ + 1) + 1) / (-(σ + 1) + 1) :=
    integral_Ioi_rpow_of_lt ha hN_pos
  have hden : -(σ + 1) + 1 = -σ := by
    calc
      -(σ + 1) + 1 = (-σ + -1) + 1 := by
        exact congrArg (fun t : ℝ => t + 1) (neg_add σ 1)
      _ = -σ + (-1 + 1) := by
        exact add_assoc (-σ) (-1) 1
      _ = -σ + 0 := by
        exact congrArg (fun t : ℝ => -σ + t) (neg_add_cancel (1 : ℝ))
      _ = -σ := by
        exact add_zero (-σ)
  have hvalue :
      -N ^ (-(σ + 1) + 1) / (-(σ + 1) + 1) =
        N ^ (-σ) / σ := by
    have hnum :
        N ^ (-(σ + 1) + 1) = N ^ (-σ) :=
      congrArg (fun e : ℝ => N ^ e) hden
    calc
      -N ^ (-(σ + 1) + 1) / (-(σ + 1) + 1) =
          -N ^ (-σ) / (-(σ + 1) + 1) := by
        exact congrArg
          (fun t : ℝ => -t / (-(σ + 1) + 1))
          hnum
      _ = -N ^ (-σ) / (-σ) := by
        exact congrArg
          (fun t : ℝ => -N ^ (-σ) / t)
          hden
      _ = N ^ (-σ) / σ := by
        exact neg_div_neg_eq (N ^ (-σ)) σ
  have hsigma_nonneg : 0 ≤ σ :=
    le_trans zero_le_one hσ
  have hsigma_pos : 0 < σ :=
    lt_of_lt_of_le zero_lt_one hσ
  have hexponent_nonpos : -σ ≤ 0 :=
    neg_nonpos.mpr hsigma_nonneg
  have hpow_le : N ^ (-σ) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hN hexponent_nonpos
  have hquotient_le_one_div :
      N ^ (-σ) / σ ≤ 1 / σ :=
    div_le_div_of_nonneg_right hpow_le (le_of_lt hsigma_pos)
  have hone_div_le_one :
      1 / σ ≤ 1 :=
    le_trans
      (one_div_le_one_div_of_le zero_lt_one hσ)
      (le_of_eq (div_one (1 : ℝ)))
  have htail :
      -N ^ (-(σ + 1) + 1) / (-(σ + 1) + 1) ≤ 1 :=
    le_trans
      (Eq.subst
        (motive := fun t : ℝ => t ≤ 1 / σ)
        hvalue.symm
        hquotient_le_one_div)
      hone_div_le_one
  exact Eq.subst
    (motive := fun t : ℝ => t ≤ 1)
    hintegral.symm
    htail

/-- Bochner norm domination for the Bernoulli-periodic Euler-Maclaurin core by
the scalar real-power tail integral. -/
theorem eulerMaclaurin_firstPeriodicBernoulli_cpow_tail_norm_integral_domination
    (z : ℂ)
    (hz_one : 1 ≤ z.re)
    (hz_two : z.re ≤ 2) :
    ‖eulerMaclaurinPoleClearedZetaBernoulliIntegralCore z‖ ≤
      ∫ x in Set.Ioi (((eulerMaclaurinPoleClearedZetaCutoff z : ℕ) : ℝ)),
        x ^ (-(z.re + 1)) := by
  unfold eulerMaclaurinPoleClearedZetaBernoulliIntegralCore
  let N : ℝ := ((eulerMaclaurinPoleClearedZetaCutoff z : ℕ) : ℝ)
  let s : Set ℝ := Set.Ioi N
  let f : ℝ → ℂ :=
    fun x =>
      ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) *
        (((x : ℝ) : ℂ) ^ (-(z + 1)))
  let g : ℝ → ℝ :=
    fun x => x ^ (-(z.re + 1))
  have hN_one : (1 : ℝ) ≤ N :=
    one_le_eulerMaclaurinPoleClearedZetaCutoff_real z
  have hN_pos : 0 < N :=
    lt_of_lt_of_le zero_lt_one hN_one
  have htwo_le : (2 : ℝ) ≤ z.re + 1 := by
    calc
      (2 : ℝ) = 1 + 1 := by
        exact (one_add_one_eq_two : (1 : ℝ) + 1 = 2).symm
      _ ≤ z.re + 1 :=
        add_le_add hz_one le_rfl
  have hone_lt : (1 : ℝ) < z.re + 1 :=
    lt_of_lt_of_le one_lt_two htwo_le
  have ha : -(z.re + 1) < -(1 : ℝ) :=
    neg_lt_neg hone_lt
  have hg : Integrable g (volume.restrict s) :=
    integrableOn_Ioi_rpow_of_lt ha hN_pos
  have hbound : ∀ᵐ x ∂volume.restrict s, ‖f x‖ ≤ g x := by
    exact (ae_restrict_mem measurableSet_Ioi).mono
      (fun x hx =>
        by
          have hx_pos : 0 < x :=
            lt_trans hN_pos hx
          have hB_abs :
              |eulerMaclaurinFirstPeriodicBernoulli x| ≤ 1 :=
            eulerMaclaurinFirstPeriodicBernoulli_abs_le_one x
          have hB_norm :
              ‖((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ)‖ ≤ 1 := by
            calc
              ‖((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ)‖ =
                  |eulerMaclaurinFirstPeriodicBernoulli x| := by
                exact Complex.norm_ofReal (eulerMaclaurinFirstPeriodicBernoulli x)
              _ ≤ 1 :=
                hB_abs
          have hcpow :
              ‖((x : ℝ) : ℂ) ^ (-(z + 1))‖ ≤ g x :=
            norm_real_cpow_neg_z_add_one_le_rpow hx_pos z hz_one
          have hg_nonneg : 0 ≤ g x :=
            Real.rpow_nonneg (le_of_lt hx_pos) (-(z.re + 1))
          calc
            ‖f x‖ =
                ‖((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ)‖ *
                  ‖((x : ℝ) : ℂ) ^ (-(z + 1))‖ := by
              exact norm_mul
                ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ)
                (((x : ℝ) : ℂ) ^ (-(z + 1)))
            _ ≤ 1 * g x :=
              mul_le_mul hB_norm hcpow
                (norm_nonneg (((x : ℝ) : ℂ) ^ (-(z + 1))))
                zero_le_one
            _ = g x := by
              exact one_mul (g x)
      )
  exact norm_integral_le_of_norm_le hg hbound

/-- Scalar improper-integral tail estimate for the first periodic Bernoulli
Euler-Maclaurin kernel.

This is the real-variable analytic input behind the zeta remainder bound:
`|B₁({x})| ≤ 1`, positivity of the cutoff, the positive-real `cpow` norm
formula, and the tail estimate for `∫_N^∞ x^{-σ-1} dx` with `σ ≥ 1`. -/
theorem eulerMaclaurin_firstPeriodicBernoulli_cpow_tail_integral_norm_le_one_standard
    (z : ℂ)
    (hz_one : 1 ≤ z.re)
    (hz_two : z.re ≤ 2) :
    ‖eulerMaclaurinPoleClearedZetaBernoulliIntegralCore z‖ ≤ 1 := by
  have hdom :
      ‖eulerMaclaurinPoleClearedZetaBernoulliIntegralCore z‖ ≤
        ∫ x in Set.Ioi (((eulerMaclaurinPoleClearedZetaCutoff z : ℕ) : ℝ)),
          x ^ (-(z.re + 1)) :=
    eulerMaclaurin_firstPeriodicBernoulli_cpow_tail_norm_integral_domination
      z hz_one hz_two
  have hcutoff :
      (1 : ℝ) ≤ ((eulerMaclaurinPoleClearedZetaCutoff z : ℕ) : ℝ) :=
    one_le_eulerMaclaurinPoleClearedZetaCutoff_real z
  have htail :
      ∫ x in Set.Ioi (((eulerMaclaurinPoleClearedZetaCutoff z : ℕ) : ℝ)),
          x ^ (-(z.re + 1)) ≤ 1 :=
    integral_Ioi_rpow_neg_re_add_one_le_one_of_one_le_cutoff
      hcutoff hz_one
  exact le_trans hdom htail

/-- Standard Bernoulli-periodic tail majorant for the Euler-Maclaurin zeta
remainder core on the closed strip `1 ≤ Re z ≤ 2`. -/
theorem eulerMaclaurinPoleClearedZetaBernoulliIntegralCore_norm_le_one
    (z : ℂ)
    (hz_one : 1 ≤ z.re)
    (hz_two : z.re ≤ 2) :
    ‖eulerMaclaurinPoleClearedZetaBernoulliIntegralCore z‖ ≤ 1 := by
  exact
    eulerMaclaurin_firstPeriodicBernoulli_cpow_tail_integral_norm_le_one_standard
      z hz_one hz_two

/-- Polynomial bound for the explicit Bernoulli-periodic integral remainder.

The proof is the standard majorization:
`|B₁({x})| ≤ 1`, `‖x^{-z-1}‖ ≤ x^{-Re z-1}` for positive `x`, and
`∫_N^∞ x^{-Re z-1} dx ≤ 1` on `1 ≤ Re z`, followed by the elementary
polynomial bound for `(z - 1) z`. -/
theorem eulerMaclaurinPoleClearedZetaBernoulliIntegralRemainder_polynomial_bound :
    ∃ C : ℝ, ∃ m : ℕ,
      0 < C ∧
      ∀ z : ℂ,
        1 ≤ z.re →
        z.re ≤ 2 →
        ‖eulerMaclaurinPoleClearedZetaBernoulliIntegralRemainder z‖ ≤
          C * (1 + ‖z‖) ^ m := by
  refine ⟨1, 2, zero_lt_one, ?_⟩
  intro z hz_one hz_two
  unfold eulerMaclaurinPoleClearedZetaBernoulliIntegralRemainder
  let H : ℝ := 1 + ‖z‖
  have hH_nonneg : 0 ≤ H :=
    le_trans zero_le_one (le_add_of_nonneg_right (norm_nonneg z))
  have hz_norm : ‖z‖ ≤ H :=
    le_add_of_nonneg_left zero_le_one
  have hz_sub_norm : ‖z - 1‖ ≤ H :=
    eulerMaclaurinPoleClearedZetaFinitePart_poleFactor_norm_le_height z
  have hleft :
      ‖(z - 1) * z‖ ≤ H * H := by
    calc
      ‖(z - 1) * z‖ = ‖z - 1‖ * ‖z‖ := by
        exact norm_mul (z - 1) z
      _ ≤ H * H :=
        mul_le_mul hz_sub_norm hz_norm (norm_nonneg z) hH_nonneg
  have hcore :
      ‖eulerMaclaurinPoleClearedZetaBernoulliIntegralCore z‖ ≤ 1 :=
    eulerMaclaurinPoleClearedZetaBernoulliIntegralCore_norm_le_one z hz_one hz_two
  have hprod :
      ‖-((z - 1) * z) *
          eulerMaclaurinPoleClearedZetaBernoulliIntegralCore z‖ ≤
        (H * H) * 1 := by
    calc
      ‖-((z - 1) * z) *
          eulerMaclaurinPoleClearedZetaBernoulliIntegralCore z‖ =
          ‖-((z - 1) * z)‖ *
            ‖eulerMaclaurinPoleClearedZetaBernoulliIntegralCore z‖ := by
        exact norm_mul (-((z - 1) * z))
          (eulerMaclaurinPoleClearedZetaBernoulliIntegralCore z)
      _ = ‖(z - 1) * z‖ *
            ‖eulerMaclaurinPoleClearedZetaBernoulliIntegralCore z‖ := by
        exact congrArg
          (fun x : ℝ =>
            x * ‖eulerMaclaurinPoleClearedZetaBernoulliIntegralCore z‖)
          (norm_neg ((z - 1) * z))
      _ ≤ (H * H) * 1 :=
        mul_le_mul hleft hcore
          (norm_nonneg (eulerMaclaurinPoleClearedZetaBernoulliIntegralCore z))
          (mul_nonneg hH_nonneg hH_nonneg)
  have hcollapse : (H * H) * 1 = (1 : ℝ) * H ^ (2 : ℕ) := by
    calc
      (H * H) * 1 = H * H := by
        exact mul_one (H * H)
      _ = H ^ (2 : ℕ) := by
        exact (pow_two H).symm
      _ = (1 : ℝ) * H ^ (2 : ℕ) := by
        exact (one_mul (H ^ (2 : ℕ))).symm
  have htarget : (1 : ℝ) * H ^ (2 : ℕ) =
      (1 : ℝ) * (1 + ‖z‖) ^ (2 : ℕ) := rfl
  exact le_trans hprod (le_of_eq (hcollapse.trans htarget))

/-- Standard Euler-Maclaurin Bernoulli-periodic integral estimate for the
pole-cleared remainder on `1 ≤ Re s ≤ 2`.

This is the analytic owner input: after multiplying the usual
Euler-Maclaurin remainder
`s ∫_N^∞ B₁({x}) x^{-s-1} dx` by `s - 1`, the bounded Bernoulli function,
`‖x^{-s-1}‖ ≤ x^{-Re s - 1}`, and
`N = ⌊2 + ‖s‖⌋₊ ≥ 1` give a fixed polynomial envelope in `1 + ‖s‖`. -/
theorem eulerMaclaurinPoleClearedZetaRemainderTerm_bernoulliIntegral_polynomial_bound_standard :
    ∃ C : ℝ, ∃ m : ℕ,
      0 < C ∧
      ∀ z : ℂ,
        1 ≤ z.re →
        z.re ≤ 2 →
        ‖eulerMaclaurinPoleClearedZetaRemainderTerm z‖ ≤ C * (1 + ‖z‖) ^ m := by
  rcases eulerMaclaurinPoleClearedZetaBernoulliIntegralRemainder_polynomial_bound with
    ⟨C, m, hC, hbound⟩
  refine ⟨C, m, hC, ?_⟩
  intro z hz_one hz_two
  have hformula :
      eulerMaclaurinPoleClearedZetaRemainderTerm z =
        eulerMaclaurinPoleClearedZetaBernoulliIntegralRemainder z :=
    eulerMaclaurinPoleClearedZetaRemainderTerm_eq_bernoulliIntegralRemainder
      z hz_one hz_two
  exact Eq.subst
    (motive := fun w : ℂ => ‖w‖ ≤ C * (1 + ‖z‖) ^ m)
    hformula.symm
    (hbound z hz_one hz_two)

/-- Polynomial control for the pole-cleared Euler-Maclaurin remainder from the
standard Bernoulli-periodic integral majorant.

Analytically this is the estimate for
`(s - 1) · s ∫_N^∞ B₁({x}) x^{-s-1} dx` with
`N = ⌊2 + ‖s‖⌋₊`, using boundedness of `B₁`, `1 ≤ Re s ≤ 2`, and the
height-comparable cutoff. -/
theorem eulerMaclaurinPoleClearedZetaRemainderTerm_integral_majorant_polynomial_bound :
    ∃ C : ℝ, ∃ m : ℕ,
      0 < C ∧
      ∀ z : ℂ,
        1 ≤ z.re →
        z.re ≤ 2 →
        ‖eulerMaclaurinPoleClearedZetaRemainderTerm z‖ ≤ C * (1 + ‖z‖) ^ m := by
  exact eulerMaclaurinPoleClearedZetaRemainderTerm_bernoulliIntegral_polynomial_bound_standard

/-- The pole-cleared Euler-Maclaurin continuation formula in the `1 ≤ Re s ≤ 2`
strip, with the four canonical terms separated. -/

end
end LFunctions
end Boundary
