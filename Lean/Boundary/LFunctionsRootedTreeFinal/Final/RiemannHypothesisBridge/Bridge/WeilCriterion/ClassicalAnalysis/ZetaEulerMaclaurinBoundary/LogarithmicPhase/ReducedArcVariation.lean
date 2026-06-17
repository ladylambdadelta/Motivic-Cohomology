import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ClassicalAnalysis.ZetaEulerMaclaurinBoundary.LogarithmicPhase.RealPhaseBasics
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ClassicalAnalysis.ZetaEulerMaclaurinBoundary.LogarithmicPhase.ReducedArcSideDecomposition
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Angle
import Mathlib.Data.Complex.ExponentialBounds
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Real.Pi.Bounds

/-!
# Logarithmic phase estimates

This file owns the oscillatory phase `n^{-it}` input used by the
Euler-Maclaurin boundary argument.  The phase is logarithmic, not a
constant-ratio geometric progression.
-/

namespace Boundary
namespace LFunctions

noncomputable section
/-- The public three-piece constant dominates a single one-sided constant. -/
theorem Real.four_mul_inv_le_four_mul_three_mul_inv
    {lam : ℝ}
    (hlam_pos : 0 < lam) :
    4 * lam⁻¹ ≤ 4 * (3 * lam⁻¹) := by
  have hlam_inv_nonneg : 0 ≤ lam⁻¹ :=
    inv_nonneg.mpr hlam_pos.le
  have hthree_nonneg : 0 ≤ (3 : ℝ) :=
    zero_le_three
  have hone_le_three : (1 : ℝ) ≤ 3 :=
    have hraw :
        ((Nat.succ 0 : ℕ) : ℝ) ≤ ((Nat.succ 2 : ℕ) : ℝ) :=
      Nat.cast_le.mpr
        (Nat.succ_le_succ (Nat.zero_le 2))
    have hone_nat :
        (Nat.succ 0 : ℕ) = 1 :=
      rfl
    have hone_cast :
        ((Nat.succ 0 : ℕ) : ℝ) = (1 : ℝ) :=
      Eq.trans
        (congrArg (fun n : ℕ => (n : ℝ)) hone_nat)
        Nat.cast_one
    have hthree_nat :
        (Nat.succ 2 : ℕ) = 3 :=
      rfl
    have hthree_cast :
        ((Nat.succ 2 : ℕ) : ℝ) = (3 : ℝ) :=
      Eq.trans
        (congrArg (fun n : ℕ => (n : ℝ)) hthree_nat)
        Nat.cast_ofNat
    have hleft_normal :
        (1 : ℝ) ≤ ((Nat.succ 2 : ℕ) : ℝ) :=
      Eq.subst
        (motive := fun r : ℝ => r ≤ ((Nat.succ 2 : ℕ) : ℝ))
        hone_cast
        hraw
    Eq.subst
      (motive := fun r : ℝ => (1 : ℝ) ≤ r)
      hthree_cast
      hleft_normal
  have hinner :
      lam⁻¹ ≤ 3 * lam⁻¹ := by
    have hmul :
        1 * lam⁻¹ ≤ 3 * lam⁻¹ :=
      mul_le_mul_of_nonneg_right hone_le_three hlam_inv_nonneg
    exact Eq.subst
      (motive := fun r : ℝ => r ≤ 3 * lam⁻¹)
      (one_mul lam⁻¹)
      hmul
  exact mul_le_mul_of_nonneg_left hinner zero_le_four

/-- Three copies of the one-sided constant fold to the three-piece constant. -/
theorem Real.three_four_inv_eq_four_mul_three_mul_inv
    (lam : ℝ) :
    (4 * lam⁻¹ + 4 * lam⁻¹) + 4 * lam⁻¹ =
      4 * (3 * lam⁻¹) := by
  have htwo :
      4 * lam⁻¹ + 4 * lam⁻¹ = (4 + 4 : ℝ) * lam⁻¹ :=
    (add_mul (4 : ℝ) 4 lam⁻¹).symm
  have height :
      (4 + 4 : ℝ) = 8 :=
    have hnat : (4 + 4 : ℕ) = 8 :=
      rfl
    have hcast_sum :
        (((4 + 4 : ℕ) : ℝ) = (4 : ℝ) + 4) :=
      Nat.cast_add 4 4
    have hcast_value :
        (((4 + 4 : ℕ) : ℝ) = (8 : ℝ)) :=
      Eq.trans
        (congrArg (fun n : ℕ => (n : ℝ)) hnat)
        Nat.cast_ofNat
    Eq.trans hcast_sum.symm hcast_value
  have htwelve :
      (8 : ℝ) + 4 = 12 :=
    have hnat : (8 + 4 : ℕ) = 12 :=
      rfl
    have hcast_sum :
        (((8 + 4 : ℕ) : ℝ) = (8 : ℝ) + 4) :=
      Nat.cast_add 8 4
    have hcast_value :
        (((8 + 4 : ℕ) : ℝ) = (12 : ℝ)) :=
      Eq.trans
        (congrArg (fun n : ℕ => (n : ℝ)) hnat)
        Nat.cast_ofNat
    Eq.trans hcast_sum.symm hcast_value
  calc
    (4 * lam⁻¹ + 4 * lam⁻¹) + 4 * lam⁻¹ =
        ((4 + 4 : ℝ) * lam⁻¹) + 4 * lam⁻¹ :=
      congrArg (fun r : ℝ => r + 4 * lam⁻¹) htwo
    _ = (8 * lam⁻¹) + 4 * lam⁻¹ :=
      congrArg (fun r : ℝ => r * lam⁻¹ + 4 * lam⁻¹) height
    _ = ((8 : ℝ) + 4) * lam⁻¹ :=
      (add_mul (8 : ℝ) 4 lam⁻¹).symm
    _ = 12 * lam⁻¹ :=
      congrArg (fun r : ℝ => r * lam⁻¹) htwelve
    _ = (4 * 3) * lam⁻¹ :=
      congrArg (fun r : ℝ => r * lam⁻¹)
        (show (12 : ℝ) = 4 * 3 from
          have hnat : (4 * 3 : ℕ) = 12 :=
            rfl
          have hcast_mul :
              (((4 * 3 : ℕ) : ℝ) = (4 : ℝ) * 3) :=
            Nat.cast_mul 4 3
          have hcast_value :
              (((4 * 3 : ℕ) : ℝ) = (12 : ℝ)) :=
            Eq.trans
              (congrArg (fun n : ℕ => (n : ℝ)) hnat)
              Nat.cast_ofNat
          Eq.trans hcast_value.symm hcast_mul)
    _ = 4 * (3 * lam⁻¹) :=
      mul_assoc (4 : ℝ) 3 lam⁻¹

/-- The three-piece monotone sign-crossing bound: negative-side variation,
one crossing jump, and positive-side variation.

This is the discrete owner obligation behind the split theorem. -/
theorem Complex.reducedArc_inverseGeometricDenominator_three_piece_variation_bound
    (ψ : ℕ → ℝ)
    {a b m : ℕ}
    {lam : ℝ}
    (ham : a < m)
    (hm : m ∈ Finset.Icc a b)
    (hlam_pos : 0 < lam)
    (hψ_mem :
      ∀ n : ℕ,
        n ∈ Finset.Ico a b →
          ψ n ∈ Set.Ioc (-Real.pi) Real.pi)
    (hψ_mono :
      MonotoneOn (fun n : ℕ => ψ n) (Finset.Ico a b : Set ℕ) ∨
      AntitoneOn (fun n : ℕ => ψ n) (Finset.Ico a b : Set ℕ))
    (hψ_sep :
      ∀ n : ℕ,
        n ∈ Finset.Ico a b →
          lam ≤ ‖ψ n‖)
    (hψ_den :
      ∀ n : ℕ,
        n ∈ Finset.Ico a b →
          ‖Complex.reducedArc_inverseGeometricDenominator (ψ n)‖ ≤
            2 * lam⁻¹) :
    (∑ n ∈ Finset.Ioo a m,
      ‖Complex.reducedArc_inverseGeometricDenominator (ψ n) -
        Complex.reducedArc_inverseGeometricDenominator (ψ (n - 1))‖) ≤
        4 * (3 * lam⁻¹) := by
  let jump : ℕ → ℝ :=
    fun n : ℕ =>
      ‖Complex.reducedArc_inverseGeometricDenominator (ψ n) -
        Complex.reducedArc_inverseGeometricDenominator (ψ (n - 1))‖
  have hm_bounds : a ≤ m ∧ m ≤ b :=
    Finset.mem_Icc.mp hm
  have hm_self : m ∈ Finset.Icc a m :=
    Finset.mem_Icc.mpr ⟨hm_bounds.1, le_rfl⟩
  have htarget_one :
      4 * lam⁻¹ ≤ 4 * (3 * lam⁻¹) :=
    Real.four_mul_inv_le_four_mul_three_mul_inv hlam_pos
  have htarget_three :
      (4 * lam⁻¹ + 4 * lam⁻¹) + 4 * lam⁻¹ ≤
        4 * (3 * lam⁻¹) :=
    Eq.le (Real.three_four_inv_eq_four_mul_three_mul_inv lam)
  match hψ_mono with
  | Or.inl hmono =>
      have hmono_am :
          MonotoneOn ψ (Finset.Ico a m : Set ℕ) := by
        intro i hi j hj hij
        have hi_bounds : a ≤ i ∧ i < m :=
          Finset.mem_Ico.mp hi
        have hj_bounds : a ≤ j ∧ j < m :=
          Finset.mem_Ico.mp hj
        exact hmono
          (Finset.mem_Ico.mpr
            ⟨hi_bounds.1, lt_of_lt_of_le hi_bounds.2 hm_bounds.2⟩)
          (Finset.mem_Ico.mpr
            ⟨hj_bounds.1, lt_of_lt_of_le hj_bounds.2 hm_bounds.2⟩)
          hij
      have hsep_am :
          ∀ n : ℕ,
            n ∈ Finset.Ico a m →
              lam ≤ ‖ψ n‖ := by
        intro n hn
        have hn_bounds : a ≤ n ∧ n < m :=
          Finset.mem_Ico.mp hn
        exact hψ_sep n
          (Finset.mem_Ico.mpr
            ⟨hn_bounds.1, lt_of_lt_of_le hn_bounds.2 hm_bounds.2⟩)
      have hden_am :
          ∀ n : ℕ,
            n ∈ Finset.Ico a m →
              ‖Complex.reducedArc_inverseGeometricDenominator (ψ n)‖ ≤
                2 * lam⁻¹ := by
        intro n hn
        have hn_bounds : a ≤ n ∧ n < m :=
          Finset.mem_Ico.mp hn
        exact hψ_den n
          (Finset.mem_Ico.mpr
            ⟨hn_bounds.1, lt_of_lt_of_le hn_bounds.2 hm_bounds.2⟩)
      have hdecomp :=
        Real.monotoneOn_reducedArc_side_decomposition
          ψ hm hlam_pos hψ_mem hmono hψ_sep
      match hdecomp with
      | Or.inl hall_neg =>
          exact le_trans
            (Complex.reducedArc_inverseGeometricDenominator_oneSided_variation_bound
              ψ ham hm_self hlam_pos (Or.inr ⟨rfl, rfl⟩)
              hall_neg (Or.inl hmono_am) hsep_am hden_am)
            htarget_one
      | Or.inr hrest =>
          match hrest with
          | Or.inl hall_pos =>
              exact le_trans
                (Complex.reducedArc_inverseGeometricDenominator_oneSided_variation_bound
                  ψ ham hm_self hlam_pos (Or.inl ⟨rfl, rfl⟩)
                  hall_pos (Or.inl hmono_am) hsep_am hden_am)
                htarget_one
          | Or.inr hcross =>
              match hcross with
              | ⟨c, hac, hcm, hleft_side, hright_side⟩ =>
                  have hc_mem_original : c ∈ Finset.Ico a b :=
                    Finset.mem_Ico.mpr
                      ⟨le_of_lt hac, lt_of_lt_of_le hcm hm_bounds.2⟩
                  have hc_Icc_left : c ∈ Finset.Icc a c :=
                    Finset.mem_Icc.mpr ⟨le_of_lt hac, le_rfl⟩
                  have hm_Icc_right : m ∈ Finset.Icc c m :=
                    Finset.mem_Icc.mpr ⟨le_of_lt hcm, le_rfl⟩
                  have hmono_left :
                      MonotoneOn ψ (Finset.Ico a c : Set ℕ) := by
                    intro i hi j hj hij
                    have hi_bounds : a ≤ i ∧ i < c :=
                      Finset.mem_Ico.mp hi
                    have hj_bounds : a ≤ j ∧ j < c :=
                      Finset.mem_Ico.mp hj
                    exact hmono
                      (Finset.mem_Ico.mpr
                        ⟨hi_bounds.1,
                          lt_of_lt_of_le (lt_trans hi_bounds.2 hcm)
                            hm_bounds.2⟩)
                      (Finset.mem_Ico.mpr
                        ⟨hj_bounds.1,
                          lt_of_lt_of_le (lt_trans hj_bounds.2 hcm)
                            hm_bounds.2⟩)
                      hij
                  have hmono_right :
                      MonotoneOn ψ (Finset.Ico c m : Set ℕ) := by
                    intro i hi j hj hij
                    have hi_bounds : c ≤ i ∧ i < m :=
                      Finset.mem_Ico.mp hi
                    have hj_bounds : c ≤ j ∧ j < m :=
                      Finset.mem_Ico.mp hj
                    exact hmono
                      (Finset.mem_Ico.mpr
                        ⟨le_trans (le_of_lt hac) hi_bounds.1,
                          lt_of_lt_of_le hi_bounds.2 hm_bounds.2⟩)
                      (Finset.mem_Ico.mpr
                        ⟨le_trans (le_of_lt hac) hj_bounds.1,
                          lt_of_lt_of_le hj_bounds.2 hm_bounds.2⟩)
                      hij
                  have hsep_left :
                      ∀ n : ℕ,
                        n ∈ Finset.Ico a c →
                          lam ≤ ‖ψ n‖ := by
                    intro n hn
                    have hn_bounds : a ≤ n ∧ n < c :=
                      Finset.mem_Ico.mp hn
                    exact hψ_sep n
                      (Finset.mem_Ico.mpr
                        ⟨hn_bounds.1,
                          lt_of_lt_of_le (lt_trans hn_bounds.2 hcm)
                            hm_bounds.2⟩)
                  have hsep_right :
                      ∀ n : ℕ,
                        n ∈ Finset.Ico c m →
                          lam ≤ ‖ψ n‖ := by
                    intro n hn
                    have hn_bounds : c ≤ n ∧ n < m :=
                      Finset.mem_Ico.mp hn
                    exact hψ_sep n
                      (Finset.mem_Ico.mpr
                        ⟨le_trans (le_of_lt hac) hn_bounds.1,
                          lt_of_lt_of_le hn_bounds.2 hm_bounds.2⟩)
                  have hden_left :
                      ∀ n : ℕ,
                        n ∈ Finset.Ico a c →
                          ‖Complex.reducedArc_inverseGeometricDenominator
                            (ψ n)‖ ≤ 2 * lam⁻¹ := by
                    intro n hn
                    have hn_bounds : a ≤ n ∧ n < c :=
                      Finset.mem_Ico.mp hn
                    exact hψ_den n
                      (Finset.mem_Ico.mpr
                        ⟨hn_bounds.1,
                          lt_of_lt_of_le (lt_trans hn_bounds.2 hcm)
                            hm_bounds.2⟩)
                  have hden_right :
                      ∀ n : ℕ,
                        n ∈ Finset.Ico c m →
                          ‖Complex.reducedArc_inverseGeometricDenominator
                            (ψ n)‖ ≤ 2 * lam⁻¹ := by
                    intro n hn
                    have hn_bounds : c ≤ n ∧ n < m :=
                      Finset.mem_Ico.mp hn
                    exact hψ_den n
                      (Finset.mem_Ico.mpr
                        ⟨le_trans (le_of_lt hac) hn_bounds.1,
                          lt_of_lt_of_le hn_bounds.2 hm_bounds.2⟩)
                  have hleft :
                      (∑ n ∈ Finset.Ioo a c, jump n) ≤ 4 * lam⁻¹ :=
                    Complex.reducedArc_inverseGeometricDenominator_oneSided_variation_bound
                      ψ hac hc_Icc_left hlam_pos (Or.inr ⟨rfl, rfl⟩)
                      hleft_side (Or.inl hmono_left) hsep_left hden_left
                  have hright :
                      (∑ n ∈ Finset.Ioo c m, jump n) ≤ 4 * lam⁻¹ :=
                    Complex.reducedArc_inverseGeometricDenominator_oneSided_variation_bound
                      ψ hcm hm_Icc_right hlam_pos (Or.inl ⟨rfl, rfl⟩)
                      hright_side (Or.inl hmono_right) hsep_right hden_right
                  have hc_Ioo : c ∈ Finset.Ioo a m :=
                    Finset.mem_Ioo.mpr ⟨hac, hcm⟩
                  have hjump :
                      jump c ≤ 4 * lam⁻¹ :=
                    Complex.reducedArc_inverseGeometricDenominator_adjacent_norm_le_four_inv
                      ψ hc_Ioo hm hψ_den
                  have hsplit :
                      (∑ n ∈ Finset.Ioo a m, jump n) =
                        (∑ n ∈ Finset.Ioo a c, jump n) + jump c +
                          ∑ n ∈ Finset.Ioo c m, jump n :=
                    Finset.sum_Ioo_split_at jump hac hcm
                  have hparts :
                      (∑ n ∈ Finset.Ioo a c, jump n) + jump c +
                          ∑ n ∈ Finset.Ioo c m, jump n ≤
                        (4 * lam⁻¹ + 4 * lam⁻¹) + 4 * lam⁻¹ :=
                    add_le_add (add_le_add hleft hjump) hright
                  exact Eq.subst
                    (motive := fun r : ℝ =>
                      r ≤ 4 * (3 * lam⁻¹))
                    hsplit.symm
                    (le_trans hparts htarget_three)
  | Or.inr hanti =>
      have hanti_am :
          AntitoneOn ψ (Finset.Ico a m : Set ℕ) := by
        intro i hi j hj hij
        have hi_bounds : a ≤ i ∧ i < m :=
          Finset.mem_Ico.mp hi
        have hj_bounds : a ≤ j ∧ j < m :=
          Finset.mem_Ico.mp hj
        exact hanti
          (Finset.mem_Ico.mpr
            ⟨hi_bounds.1, lt_of_lt_of_le hi_bounds.2 hm_bounds.2⟩)
          (Finset.mem_Ico.mpr
            ⟨hj_bounds.1, lt_of_lt_of_le hj_bounds.2 hm_bounds.2⟩)
          hij
      have hsep_am :
          ∀ n : ℕ,
            n ∈ Finset.Ico a m →
              lam ≤ ‖ψ n‖ := by
        intro n hn
        have hn_bounds : a ≤ n ∧ n < m :=
          Finset.mem_Ico.mp hn
        exact hψ_sep n
          (Finset.mem_Ico.mpr
            ⟨hn_bounds.1, lt_of_lt_of_le hn_bounds.2 hm_bounds.2⟩)
      have hden_am :
          ∀ n : ℕ,
            n ∈ Finset.Ico a m →
              ‖Complex.reducedArc_inverseGeometricDenominator (ψ n)‖ ≤
                2 * lam⁻¹ := by
        intro n hn
        have hn_bounds : a ≤ n ∧ n < m :=
          Finset.mem_Ico.mp hn
        exact hψ_den n
          (Finset.mem_Ico.mpr
            ⟨hn_bounds.1, lt_of_lt_of_le hn_bounds.2 hm_bounds.2⟩)
      have hdecomp :=
        Real.antitoneOn_reducedArc_side_decomposition
          ψ hm hlam_pos hψ_mem hanti hψ_sep
      match hdecomp with
      | Or.inl hall_pos =>
          exact le_trans
            (Complex.reducedArc_inverseGeometricDenominator_oneSided_variation_bound
              ψ ham hm_self hlam_pos (Or.inl ⟨rfl, rfl⟩)
              hall_pos (Or.inr hanti_am) hsep_am hden_am)
            htarget_one
      | Or.inr hrest =>
          match hrest with
          | Or.inl hall_neg =>
              exact le_trans
                (Complex.reducedArc_inverseGeometricDenominator_oneSided_variation_bound
                  ψ ham hm_self hlam_pos (Or.inr ⟨rfl, rfl⟩)
                  hall_neg (Or.inr hanti_am) hsep_am hden_am)
                htarget_one
          | Or.inr hcross =>
              match hcross with
              | ⟨c, hac, hcm, hleft_side, hright_side⟩ =>
                  have hc_Icc_left : c ∈ Finset.Icc a c :=
                    Finset.mem_Icc.mpr ⟨le_of_lt hac, le_rfl⟩
                  have hm_Icc_right : m ∈ Finset.Icc c m :=
                    Finset.mem_Icc.mpr ⟨le_of_lt hcm, le_rfl⟩
                  have hanti_left :
                      AntitoneOn ψ (Finset.Ico a c : Set ℕ) := by
                    intro i hi j hj hij
                    have hi_bounds : a ≤ i ∧ i < c :=
                      Finset.mem_Ico.mp hi
                    have hj_bounds : a ≤ j ∧ j < c :=
                      Finset.mem_Ico.mp hj
                    exact hanti
                      (Finset.mem_Ico.mpr
                        ⟨hi_bounds.1,
                          lt_of_lt_of_le (lt_trans hi_bounds.2 hcm)
                            hm_bounds.2⟩)
                      (Finset.mem_Ico.mpr
                        ⟨hj_bounds.1,
                          lt_of_lt_of_le (lt_trans hj_bounds.2 hcm)
                            hm_bounds.2⟩)
                      hij
                  have hanti_right :
                      AntitoneOn ψ (Finset.Ico c m : Set ℕ) := by
                    intro i hi j hj hij
                    have hi_bounds : c ≤ i ∧ i < m :=
                      Finset.mem_Ico.mp hi
                    have hj_bounds : c ≤ j ∧ j < m :=
                      Finset.mem_Ico.mp hj
                    exact hanti
                      (Finset.mem_Ico.mpr
                        ⟨le_trans (le_of_lt hac) hi_bounds.1,
                          lt_of_lt_of_le hi_bounds.2 hm_bounds.2⟩)
                      (Finset.mem_Ico.mpr
                        ⟨le_trans (le_of_lt hac) hj_bounds.1,
                          lt_of_lt_of_le hj_bounds.2 hm_bounds.2⟩)
                      hij
                  have hsep_left :
                      ∀ n : ℕ,
                        n ∈ Finset.Ico a c →
                          lam ≤ ‖ψ n‖ := by
                    intro n hn
                    have hn_bounds : a ≤ n ∧ n < c :=
                      Finset.mem_Ico.mp hn
                    exact hψ_sep n
                      (Finset.mem_Ico.mpr
                        ⟨hn_bounds.1,
                          lt_of_lt_of_le (lt_trans hn_bounds.2 hcm)
                            hm_bounds.2⟩)
                  have hsep_right :
                      ∀ n : ℕ,
                        n ∈ Finset.Ico c m →
                          lam ≤ ‖ψ n‖ := by
                    intro n hn
                    have hn_bounds : c ≤ n ∧ n < m :=
                      Finset.mem_Ico.mp hn
                    exact hψ_sep n
                      (Finset.mem_Ico.mpr
                        ⟨le_trans (le_of_lt hac) hn_bounds.1,
                          lt_of_lt_of_le hn_bounds.2 hm_bounds.2⟩)
                  have hden_left :
                      ∀ n : ℕ,
                        n ∈ Finset.Ico a c →
                          ‖Complex.reducedArc_inverseGeometricDenominator
                            (ψ n)‖ ≤ 2 * lam⁻¹ := by
                    intro n hn
                    have hn_bounds : a ≤ n ∧ n < c :=
                      Finset.mem_Ico.mp hn
                    exact hψ_den n
                      (Finset.mem_Ico.mpr
                        ⟨hn_bounds.1,
                          lt_of_lt_of_le (lt_trans hn_bounds.2 hcm)
                            hm_bounds.2⟩)
                  have hden_right :
                      ∀ n : ℕ,
                        n ∈ Finset.Ico c m →
                          ‖Complex.reducedArc_inverseGeometricDenominator
                            (ψ n)‖ ≤ 2 * lam⁻¹ := by
                    intro n hn
                    have hn_bounds : c ≤ n ∧ n < m :=
                      Finset.mem_Ico.mp hn
                    exact hψ_den n
                      (Finset.mem_Ico.mpr
                        ⟨le_trans (le_of_lt hac) hn_bounds.1,
                          lt_of_lt_of_le hn_bounds.2 hm_bounds.2⟩)
                  have hleft :
                      (∑ n ∈ Finset.Ioo a c, jump n) ≤ 4 * lam⁻¹ :=
                    Complex.reducedArc_inverseGeometricDenominator_oneSided_variation_bound
                      ψ hac hc_Icc_left hlam_pos (Or.inl ⟨rfl, rfl⟩)
                      hleft_side (Or.inr hanti_left) hsep_left hden_left
                  have hright :
                      (∑ n ∈ Finset.Ioo c m, jump n) ≤ 4 * lam⁻¹ :=
                    Complex.reducedArc_inverseGeometricDenominator_oneSided_variation_bound
                      ψ hcm hm_Icc_right hlam_pos (Or.inr ⟨rfl, rfl⟩)
                      hright_side (Or.inr hanti_right) hsep_right hden_right
                  have hc_Ioo : c ∈ Finset.Ioo a m :=
                    Finset.mem_Ioo.mpr ⟨hac, hcm⟩
                  have hjump :
                      jump c ≤ 4 * lam⁻¹ :=
                    Complex.reducedArc_inverseGeometricDenominator_adjacent_norm_le_four_inv
                      ψ hc_Ioo hm hψ_den
                  have hsplit :
                      (∑ n ∈ Finset.Ioo a m, jump n) =
                        (∑ n ∈ Finset.Ioo a c, jump n) + jump c +
                          ∑ n ∈ Finset.Ioo c m, jump n :=
                    Finset.sum_Ioo_split_at jump hac hcm
                  have hparts :
                      (∑ n ∈ Finset.Ioo a c, jump n) + jump c +
                          ∑ n ∈ Finset.Ioo c m, jump n ≤
                        (4 * lam⁻¹ + 4 * lam⁻¹) + 4 * lam⁻¹ :=
                    add_le_add (add_le_add hleft hjump) hright
                  exact Eq.subst
                    (motive := fun r : ℝ =>
                      r ≤ 4 * (3 * lam⁻¹))
                    hsplit.symm
                    (le_trans hparts htarget_three)

/-- The three-piece variation constant is bounded by the public `π`-constant. -/
theorem Real.four_mul_three_mul_inv_le_four_mul_pi_mul_inv
    {lam : ℝ}
    (hlam_pos : 0 < lam) :
    4 * (3 * lam⁻¹) ≤ 4 * Real.pi * lam⁻¹ := by
  have hlam_inv_nonneg : 0 ≤ lam⁻¹ :=
    inv_nonneg.mpr hlam_pos.le
  have hthree_le_pi : (3 : ℝ) ≤ Real.pi :=
    le_of_lt Real.pi_gt_three
  have hinner :
      3 * lam⁻¹ ≤ Real.pi * lam⁻¹ :=
    mul_le_mul_of_nonneg_right hthree_le_pi hlam_inv_nonneg
  have houter :
      4 * (3 * lam⁻¹) ≤ 4 * (Real.pi * lam⁻¹) :=
    mul_le_mul_of_nonneg_left hinner zero_lt_four.le
  have htarget :
      4 * (Real.pi * lam⁻¹) = 4 * Real.pi * lam⁻¹ :=
    (mul_assoc (4 : ℝ) Real.pi lam⁻¹).symm
  exact Eq.subst
    (motive := fun r : ℝ => 4 * (3 * lam⁻¹) ≤ r)
    htarget
    houter

/-- A monotone reduced sequence separated from zero splits into at most a
negative-side block, one crossing jump, and a positive-side block. -/
theorem Complex.reducedArc_inverseGeometricDenominator_split_variation_bound
    (ψ : ℕ → ℝ)
    {a b m : ℕ}
    {lam : ℝ}
    (ham : a < m)
    (hm : m ∈ Finset.Icc a b)
    (hlam_pos : 0 < lam)
    (hψ_mem :
      ∀ n : ℕ,
        n ∈ Finset.Ico a b →
          ψ n ∈ Set.Ioc (-Real.pi) Real.pi)
    (hψ_mono :
      MonotoneOn (fun n : ℕ => ψ n) (Finset.Ico a b : Set ℕ) ∨
      AntitoneOn (fun n : ℕ => ψ n) (Finset.Ico a b : Set ℕ))
    (hψ_sep :
      ∀ n : ℕ,
        n ∈ Finset.Ico a b →
          lam ≤ ‖ψ n‖)
    (hψ_den :
      ∀ n : ℕ,
        n ∈ Finset.Ico a b →
          ‖Complex.reducedArc_inverseGeometricDenominator (ψ n)‖ ≤
            2 * lam⁻¹) :
    (∑ n ∈ Finset.Ioo a m,
      ‖Complex.reducedArc_inverseGeometricDenominator (ψ n) -
        Complex.reducedArc_inverseGeometricDenominator (ψ (n - 1))‖) ≤
        4 * Real.pi * lam⁻¹ := by
  exact le_trans
    (Complex.reducedArc_inverseGeometricDenominator_three_piece_variation_bound
      ψ ham hm hlam_pos hψ_mem hψ_mono hψ_sep hψ_den)
    (Real.four_mul_three_mul_inv_le_four_mul_pi_mul_inv hlam_pos)

/-- The analytic reduced-arc variation theorem for the inverse chord map.

This is the genuine no-winding core: a monotone finite sequence in the
fundamental interval, separated from `0`, has controlled total variation under
`ψ ↦ (1 - exp(iψ))⁻¹`. -/
theorem Complex.reducedArc_inverseGeometricDenominator_monotone_variation_bound
    (ψ : ℕ → ℝ)
    {a b m : ℕ}
    {lam : ℝ}
    (ham : a < m)
    (hm : m ∈ Finset.Icc a b)
    (hlam_pos : 0 < lam)
    (hψ_mem :
      ∀ n : ℕ,
        n ∈ Finset.Ico a b →
          ψ n ∈ Set.Ioc (-Real.pi) Real.pi)
    (hψ_mono :
      MonotoneOn (fun n : ℕ => ψ n) (Finset.Ico a b : Set ℕ) ∨
      AntitoneOn (fun n : ℕ => ψ n) (Finset.Ico a b : Set ℕ))
    (hψ_sep :
      ∀ n : ℕ,
        n ∈ Finset.Ico a b →
          lam ≤ ‖ψ n‖)
    (hψ_den :
      ∀ n : ℕ,
        n ∈ Finset.Ico a b →
          ‖Complex.reducedArc_inverseGeometricDenominator (ψ n)‖ ≤
            2 * lam⁻¹) :
    (∑ n ∈ Finset.Ioo a m,
      ‖Complex.reducedArc_inverseGeometricDenominator (ψ n) -
        Complex.reducedArc_inverseGeometricDenominator (ψ (n - 1))‖) ≤
        4 * Real.pi * lam⁻¹ := by
  exact
    Complex.reducedArc_inverseGeometricDenominator_split_variation_bound
      ψ ham hm hlam_pos hψ_mem hψ_mono hψ_sep hψ_den

/-- Exact reduced-arc variation lemma for the inverse geometric denominator.

This is the genuine no-winding analytic core: a monotone finite sequence in the
fundamental interval, separated from `0`, has controlled total variation under
`ψ ↦ (1 - exp(iψ))⁻¹`. -/
theorem Complex.reducedArc_inverseGeometricDenominator_variation_bound
    (ψ : ℕ → ℝ)
    {a b m : ℕ}
    {lam : ℝ}
    (ham : a < m)
    (hm : m ∈ Finset.Icc a b)
    (hlam_pos : 0 < lam)
    (hψ_mem :
      ∀ n : ℕ,
        n ∈ Finset.Ico a b →
          ψ n ∈ Set.Ioc (-Real.pi) Real.pi)
    (hψ_mono :
      MonotoneOn (fun n : ℕ => ψ n) (Finset.Ico a b : Set ℕ) ∨
      AntitoneOn (fun n : ℕ => ψ n) (Finset.Ico a b : Set ℕ))
    (hψ_sep :
      ∀ n : ℕ,
        n ∈ Finset.Ico a b →
          lam ≤ ‖ψ n‖)
    (hψ_den :
      ∀ n : ℕ,
        n ∈ Finset.Ico a b →
          ‖(1 - Complex.exp (Complex.I * (ψ n : ℂ)))⁻¹‖ ≤
            2 * lam⁻¹) :
    (∑ n ∈ Finset.Ioo a m,
      ‖(1 - Complex.exp (Complex.I * (ψ n : ℂ)))⁻¹ -
        (1 - Complex.exp (Complex.I * (ψ (n - 1) : ℂ)))⁻¹‖) ≤
        4 * Real.pi * lam⁻¹ := by
  have hψ_den_reduced :
      ∀ n : ℕ,
        n ∈ Finset.Ico a b →
          ‖Complex.reducedArc_inverseGeometricDenominator (ψ n)‖ ≤
            2 * lam⁻¹ := by
    intro n hn
    exact Eq.subst
      (motive := fun z : ℂ => ‖z‖ ≤ 2 * lam⁻¹)
      (Complex.reducedArc_inverseGeometricDenominator_eq (ψ n)).symm
      (hψ_den n hn)
  have hcore :
      (∑ n ∈ Finset.Ioo a m,
        ‖Complex.reducedArc_inverseGeometricDenominator (ψ n) -
          Complex.reducedArc_inverseGeometricDenominator (ψ (n - 1))‖) ≤
          4 * Real.pi * lam⁻¹ :=
    Complex.reducedArc_inverseGeometricDenominator_monotone_variation_bound
      ψ ham hm hlam_pos hψ_mem hψ_mono hψ_sep hψ_den_reduced
  have hsum :
      (∑ n ∈ Finset.Ioo a m,
        ‖Complex.reducedArc_inverseGeometricDenominator (ψ n) -
          Complex.reducedArc_inverseGeometricDenominator (ψ (n - 1))‖) =
        ∑ n ∈ Finset.Ioo a m,
          ‖(1 - Complex.exp (Complex.I * (ψ n : ℂ)))⁻¹ -
            (1 - Complex.exp (Complex.I * (ψ (n - 1) : ℂ)))⁻¹‖ := by
    exact Finset.sum_congr rfl
      (fun n hn =>
        have hn_eq :
            Complex.reducedArc_inverseGeometricDenominator (ψ n) =
              (1 - Complex.exp (Complex.I * (ψ n : ℂ)))⁻¹ :=
          Complex.reducedArc_inverseGeometricDenominator_eq (ψ n)
        have hpred_eq :
            Complex.reducedArc_inverseGeometricDenominator (ψ (n - 1)) =
              (1 - Complex.exp (Complex.I * (ψ (n - 1) : ℂ)))⁻¹ :=
          Complex.reducedArc_inverseGeometricDenominator_eq (ψ (n - 1))
        congrArg norm (congrArg₂ Sub.sub hn_eq hpred_eq))
  exact Eq.subst
    (motive := fun r : ℝ => r ≤ 4 * Real.pi * lam⁻¹)
    hsum
    hcore

/-- Reduced no-winding monotone separated increments control the total variation
of the inverse geometric denominators appearing in the finite Abel transform.

The reduced monotonicity hypothesis is essential: raw monotone increments can
wind through many periods and make this total variation grow with the number of
turns. -/
theorem Complex.realPhase_reducedMonotoneSeparated_inverseGeometricDenominator_variation_bound
    (φ : ℝ → ℝ)
    {a b m : ℕ}
    {lam : ℝ}
    (ham : a < m)
    (hm : m ∈ Finset.Icc a b)
    (hlam_pos : 0 < lam)
    (hred_mono : Complex.realPhase_reducedIntegerIncrementMonotoneOn φ a b)
    (hsep : Complex.realPhase_integerIncrementSeparatedOn φ a b lam)
    (hden :
      ∀ n : ℕ,
        n ∈ Finset.Ico a b →
          ‖Complex.realPhase_inverseGeometricDenominator φ n‖ ≤
            2 * lam⁻¹) :
    (∑ n ∈ Finset.Ioo a m,
      ‖Complex.realPhase_inverseGeometricDenominator φ n -
        Complex.realPhase_inverseGeometricDenominator φ (n - 1)‖) ≤
        4 * Real.pi * lam⁻¹ := by
  let ψ : ℕ → ℝ := Complex.realPhase_reducedIntegerIncrement φ
  have hψ_mem :
      ∀ n : ℕ,
        n ∈ Finset.Ico a b →
          ψ n ∈ Set.Ioc (-Real.pi) Real.pi := by
    intro n hn
    unfold ψ Complex.realPhase_reducedIntegerIncrement
    exact real_toIocMod_mem_Ioc_pi_for_logarithmicPhase
      (Complex.realPhase_integerIncrement φ n)
  have hψ_sep :
      ∀ n : ℕ,
        n ∈ Finset.Ico a b →
          lam ≤ ‖ψ n‖ := by
    intro n hn
    unfold ψ
    exact
      Complex.realPhase_reducedIntegerIncrement_norm_lower_bound
        φ hsep hn
  have hψ_den :
      ∀ n : ℕ,
        n ∈ Finset.Ico a b →
          ‖(1 - Complex.exp (Complex.I * (ψ n : ℂ)))⁻¹‖ ≤
            2 * lam⁻¹ := by
    intro n hn
    have htransport :
        Complex.realPhase_inverseGeometricDenominator φ n =
          (1 - Complex.exp (Complex.I * (ψ n : ℂ)))⁻¹ := by
      unfold ψ
      exact Complex.realPhase_inverseGeometricDenominator_eq_reduced φ n
    exact Eq.subst
      (motive := fun z : ℂ => ‖z‖ ≤ 2 * lam⁻¹)
      htransport
      (hden n hn)
  have hcore :
      (∑ n ∈ Finset.Ioo a m,
        ‖(1 - Complex.exp (Complex.I * (ψ n : ℂ)))⁻¹ -
          (1 - Complex.exp (Complex.I * (ψ (n - 1) : ℂ)))⁻¹‖) ≤
          4 * Real.pi * lam⁻¹ :=
    Complex.reducedArc_inverseGeometricDenominator_variation_bound
      ψ ham hm hlam_pos hψ_mem hred_mono hψ_sep hψ_den
  have hterms :
      (∑ n ∈ Finset.Ioo a m,
        ‖Complex.realPhase_inverseGeometricDenominator φ n -
          Complex.realPhase_inverseGeometricDenominator φ (n - 1)‖) =
        ∑ n ∈ Finset.Ioo a m,
          ‖(1 - Complex.exp (Complex.I * (ψ n : ℂ)))⁻¹ -
            (1 - Complex.exp (Complex.I * (ψ (n - 1) : ℂ)))⁻¹‖ := by
    exact Finset.sum_congr rfl
      (fun n hn =>
        have hn :
            Complex.realPhase_inverseGeometricDenominator φ n =
              (1 - Complex.exp (Complex.I * (ψ n : ℂ)))⁻¹ := by
          unfold ψ
          exact Complex.realPhase_inverseGeometricDenominator_eq_reduced φ n
        have hpred :
            Complex.realPhase_inverseGeometricDenominator φ (n - 1) =
              (1 - Complex.exp (Complex.I * (ψ (n - 1) : ℂ)))⁻¹ := by
          unfold ψ
          exact Complex.realPhase_inverseGeometricDenominator_eq_reduced φ (n - 1)
        congrArg norm (congrArg₂ Sub.sub hn hpred))
  exact Eq.subst
    (motive := fun r : ℝ => r ≤ 4 * Real.pi * lam⁻¹)
    hterms.symm
    hcore

/-- Variation estimate for the explicit finite Abel variation term. -/
theorem Complex.realPhase_prefixAbelVariation_norm_bound
    (φ : ℝ → ℝ)
    {a b m : ℕ}
    {lam : ℝ}
    (ham : a < m)
    (hm : m ∈ Finset.Icc a b)
    (hlam_pos : 0 < lam)
    (hinc_mono : Complex.realPhase_integerIncrementMonotoneOn φ a b)
    (hred_mono : Complex.realPhase_reducedIntegerIncrementMonotoneOn φ a b)
    (hsep : Complex.realPhase_integerIncrementSeparatedOn φ a b lam)
    (hden :
      ∀ n : ℕ,
        n ∈ Finset.Ico a b →
          ‖Complex.realPhase_inverseGeometricDenominator φ n‖ ≤
            2 * lam⁻¹) :
    ‖Complex.realPhase_prefixAbelVariation φ a m‖ ≤
      4 * Real.pi * lam⁻¹ := by
  have hsum_norm :
      ‖Complex.realPhase_prefixAbelVariation φ a m‖ ≤
        ∑ n ∈ Finset.Ioo a m,
          ‖(Complex.realPhase_inverseGeometricDenominator φ n -
              Complex.realPhase_inverseGeometricDenominator φ (n - 1)) *
            Complex.realPhase_integerUnit φ n‖ := by
    unfold Complex.realPhase_prefixAbelVariation
    exact norm_sum_le (Finset.Ioo a m)
      (fun n =>
        (Complex.realPhase_inverseGeometricDenominator φ n -
            Complex.realPhase_inverseGeometricDenominator φ (n - 1)) *
          Complex.realPhase_integerUnit φ n)
  have hunit :
      (∑ n ∈ Finset.Ioo a m,
          ‖(Complex.realPhase_inverseGeometricDenominator φ n -
              Complex.realPhase_inverseGeometricDenominator φ (n - 1)) *
            Complex.realPhase_integerUnit φ n‖) =
        ∑ n ∈ Finset.Ioo a m,
          ‖Complex.realPhase_inverseGeometricDenominator φ n -
            Complex.realPhase_inverseGeometricDenominator φ (n - 1)‖ := by
    exact Finset.sum_congr rfl
      (fun n hn =>
        have hunit_norm :
            ‖Complex.realPhase_integerUnit φ n‖ = 1 := by
          exact Complex.realPhase_exp_I_norm φ n
        calc
          ‖(Complex.realPhase_inverseGeometricDenominator φ n -
              Complex.realPhase_inverseGeometricDenominator φ (n - 1)) *
            Complex.realPhase_integerUnit φ n‖ =
              ‖Complex.realPhase_inverseGeometricDenominator φ n -
                Complex.realPhase_inverseGeometricDenominator φ (n - 1)‖ *
                ‖Complex.realPhase_integerUnit φ n‖ :=
            norm_mul
              (Complex.realPhase_inverseGeometricDenominator φ n -
                Complex.realPhase_inverseGeometricDenominator φ (n - 1))
              (Complex.realPhase_integerUnit φ n)
          _ =
              ‖Complex.realPhase_inverseGeometricDenominator φ n -
                Complex.realPhase_inverseGeometricDenominator φ (n - 1)‖ * 1 := by
            exact congrArg
              (fun r : ℝ =>
                ‖Complex.realPhase_inverseGeometricDenominator φ n -
                  Complex.realPhase_inverseGeometricDenominator φ (n - 1)‖ * r)
              hunit_norm
          _ =
              ‖Complex.realPhase_inverseGeometricDenominator φ n -
                Complex.realPhase_inverseGeometricDenominator φ (n - 1)‖ :=
            mul_one _)
  have hvariation :
      (∑ n ∈ Finset.Ioo a m,
        ‖Complex.realPhase_inverseGeometricDenominator φ n -
          Complex.realPhase_inverseGeometricDenominator φ (n - 1)‖) ≤
          4 * Real.pi * lam⁻¹ :=
    Complex.realPhase_reducedMonotoneSeparated_inverseGeometricDenominator_variation_bound
      φ ham hm hlam_pos hred_mono hsep hden
  exact le_trans hsum_norm
    (Eq.subst
      (motive := fun r : ℝ => r ≤ 4 * Real.pi * lam⁻¹)
      hunit.symm
      hvariation)
end

end LFunctions
end Boundary
