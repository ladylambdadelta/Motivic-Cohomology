import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ClassicalAnalysis.ZetaEulerMaclaurinBoundary.LogarithmicPhase.RealPhaseBasics
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ClassicalAnalysis.ZetaEulerMaclaurinBoundary.LogarithmicPhase.AbelCore
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
    (_hinc_mono : Complex.realPhase_integerIncrementMonotoneOn φ a b)
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

/-- Every real angle has an integer lattice translate in the principal
branch. -/
theorem Real.exists_int_sub_two_pi_mul_mem_principal
    (θ : ℝ) :
    ∃ k : ℤ,
      θ - (2 * Real.pi * (k : ℝ)) ∈
        Set.Ioc (-Real.pi) (-Real.pi + (2 * Real.pi)) := by
  match Complex.realPhase_twoPi_toIocMod_integerDistance θ with
  | ⟨k, hk⟩ =>
      have hmod :
          toIocMod Real.two_pi_pos (-Real.pi) θ ∈
            Set.Ioc (-Real.pi) (-Real.pi + (2 * Real.pi)) :=
        real_mem_Ioc_pi_to_periodic_upper_for_logarithmicPhase
          (real_toIocMod_mem_Ioc_pi_for_logarithmicPhase θ)
      exact Exists.intro k
        (Eq.subst
          (motive := fun value : ℝ =>
            value ∈ Set.Ioc (-Real.pi) (-Real.pi + (2 * Real.pi)))
          hk.symm
          hmod)

/-- A raw monotone sequence of integer increments admits a finite partition
into principal-branch packets for the `2πℤ` lattice.

This is the finite covering step in the all-integer Kusmin-Landau argument:
the packets are half-open integer intervals, and on each packet the raw
increment lies in one translate of the fundamental interval. -/
theorem Complex.realPhase_integerIncrementMonotone_principalBranchPacketCover_exists
    (φ : ℝ → ℝ)
    {c d : ℕ}
    (_hinc_mono : Complex.realPhase_integerIncrementMonotoneOn φ c d) :
    ∃ packets : Finset (ℕ × ℕ),
      Complex.realPhase_IcoFamilyUnion packets = Finset.Ico c d ∧
      (∀ p : ℕ × ℕ,
        p ∈ packets →
          c ≤ p.1 ∧ p.1 ≤ p.2 ∧ p.2 ≤ d) ∧
      (∀ p₁ : ℕ × ℕ,
        p₁ ∈ packets →
          ∀ p₂ : ℕ × ℕ,
            p₂ ∈ packets →
              p₁ ≠ p₂ →
                Disjoint (Finset.Ico p₁.1 p₁.2) (Finset.Ico p₂.1 p₂.2)) ∧
      (∀ p : ℕ × ℕ,
        p ∈ packets →
          ∃ k : ℤ,
            ∀ n : ℕ,
              n ∈ Finset.Ico p.1 p.2 →
                Complex.realPhase_integerIncrement φ n -
                    (2 * Real.pi * (k : ℝ)) ∈
                  Set.Ioc (-Real.pi) Real.pi) := by
  let packets : Finset (ℕ × ℕ) :=
    (Finset.Ico c d).image (fun n : ℕ => (n, n + 1))
  have hcover :
      Complex.realPhase_IcoFamilyUnion packets = Finset.Ico c d := by
    exact Finset.ext
      (fun x =>
        Iff.intro
          (fun hx =>
            have hx_union :
                ∃ p : ℕ × ℕ,
                  p ∈ packets ∧ x ∈ Finset.Ico p.1 p.2 :=
              Finset.mem_biUnion.mp hx
            match hx_union with
            | ⟨p, hp, hx_p⟩ =>
                have hp_image :
                    ∃ n : ℕ,
                      n ∈ Finset.Ico c d ∧ (n, n + 1) = p :=
                  Finset.mem_image.mp hp
                match hp_image with
                | ⟨n, hn, hnp⟩ =>
                    have hx_single :
                        x ∈ Finset.Ico n (n + 1) :=
                      Eq.subst
                        (motive := fun q : ℕ × ℕ =>
                          x ∈ Finset.Ico q.1 q.2)
                        hnp.symm
                        hx_p
                    have hIco_single :
                        Finset.Ico n (n + 1) = ({n} : Finset ℕ) :=
                      Nat.Ico_succ_singleton n
                    have hx_eq : x = n :=
                      Finset.mem_singleton.mp
                        (Eq.subst
                          (motive := fun S : Finset ℕ => x ∈ S)
                          hIco_single
                          hx_single)
                    Eq.subst
                      (motive := fun y : ℕ => y ∈ Finset.Ico c d)
                      hx_eq.symm
                      hn)
          (fun hx =>
            have hp : (x, x + 1) ∈ packets :=
              Finset.mem_image.mpr
                (Exists.intro x (And.intro hx rfl))
            have hx_self : x ∈ Finset.Ico x (x + 1) :=
              Finset.mem_Ico.mpr
                (And.intro le_rfl (Nat.lt_succ_self x))
            Finset.mem_biUnion.mpr
              (Exists.intro (x, x + 1)
                (And.intro hp hx_self))))
  have hbounded :
      ∀ p : ℕ × ℕ,
        p ∈ packets →
          c ≤ p.1 ∧ p.1 ≤ p.2 ∧ p.2 ≤ d := by
    intro p hp
    have hp_image :
        ∃ n : ℕ,
          n ∈ Finset.Ico c d ∧ (n, n + 1) = p :=
      Finset.mem_image.mp hp
    match hp_image with
    | ⟨n, hn, hnp⟩ =>
        have hn_bounds : c ≤ n ∧ n < d :=
          Finset.mem_Ico.mp hn
        have hsucc_le : n + 1 ≤ d :=
          Nat.succ_le_of_lt hn_bounds.2
        exact
          Eq.subst
            (motive := fun q : ℕ × ℕ =>
              c ≤ q.1 ∧ q.1 ≤ q.2 ∧ q.2 ≤ d)
            hnp
            (And.intro hn_bounds.1
              (And.intro (Nat.le_succ n) hsucc_le))
  have hdisjoint :
      ∀ p₁ : ℕ × ℕ,
        p₁ ∈ packets →
          ∀ p₂ : ℕ × ℕ,
            p₂ ∈ packets →
              p₁ ≠ p₂ →
                Disjoint (Finset.Ico p₁.1 p₁.2) (Finset.Ico p₂.1 p₂.2) := by
    intro p₁ hp₁ p₂ hp₂ hp_ne
    exact Finset.disjoint_left.mpr
      (fun x hx₁ hx₂ =>
        have hp₁_image :
            ∃ n₁ : ℕ,
              n₁ ∈ Finset.Ico c d ∧ (n₁, n₁ + 1) = p₁ :=
          Finset.mem_image.mp hp₁
        have hp₂_image :
            ∃ n₂ : ℕ,
              n₂ ∈ Finset.Ico c d ∧ (n₂, n₂ + 1) = p₂ :=
          Finset.mem_image.mp hp₂
        match hp₁_image with
        | ⟨n₁, _hn₁, hn₁p⟩ =>
            match hp₂_image with
            | ⟨n₂, _hn₂, hn₂p⟩ =>
                have hx₁_single :
                    x ∈ Finset.Ico n₁ (n₁ + 1) :=
                  Eq.subst
                    (motive := fun q : ℕ × ℕ =>
                      x ∈ Finset.Ico q.1 q.2)
                    hn₁p.symm
                    hx₁
                have hx₂_single :
                    x ∈ Finset.Ico n₂ (n₂ + 1) :=
                  Eq.subst
                    (motive := fun q : ℕ × ℕ =>
                      x ∈ Finset.Ico q.1 q.2)
                    hn₂p.symm
                    hx₂
                have hIco₁ :
                    Finset.Ico n₁ (n₁ + 1) = ({n₁} : Finset ℕ) :=
                  Nat.Ico_succ_singleton n₁
                have hIco₂ :
                    Finset.Ico n₂ (n₂ + 1) = ({n₂} : Finset ℕ) :=
                  Nat.Ico_succ_singleton n₂
                have hx_eq₁ : x = n₁ :=
                  Finset.mem_singleton.mp
                    (Eq.subst
                      (motive := fun S : Finset ℕ => x ∈ S)
                      hIco₁
                      hx₁_single)
                have hx_eq₂ : x = n₂ :=
                  Finset.mem_singleton.mp
                    (Eq.subst
                      (motive := fun S : Finset ℕ => x ∈ S)
                      hIco₂
                      hx₂_single)
                have hn_eq : n₁ = n₂ :=
                  Eq.trans hx_eq₁.symm hx_eq₂
                have hp_eq : p₁ = p₂ :=
                  Eq.trans hn₁p.symm
                    (Eq.trans
                      (congrArg (fun n : ℕ => (n, n + 1)) hn_eq)
                      hn₂p)
                hp_ne hp_eq)
  have hprincipal :
      ∀ p : ℕ × ℕ,
        p ∈ packets →
          ∃ k : ℤ,
            ∀ n : ℕ,
              n ∈ Finset.Ico p.1 p.2 →
                Complex.realPhase_integerIncrement φ n -
                    (2 * Real.pi * (k : ℝ)) ∈
                  Set.Ioc (-Real.pi) Real.pi := by
    intro p hp
    have hp_image :
        ∃ m : ℕ,
          m ∈ Finset.Ico c d ∧ (m, m + 1) = p :=
      Finset.mem_image.mp hp
    match hp_image with
    | ⟨m, _hm, hmp⟩ =>
        match
          Real.exists_int_sub_two_pi_mul_mem_principal
            (Complex.realPhase_integerIncrement φ m) with
        | ⟨k, hk⟩ =>
            exact Exists.intro k
              (fun n hn =>
                have hn_single :
                    n ∈ Finset.Ico m (m + 1) :=
                  Eq.subst
                    (motive := fun q : ℕ × ℕ =>
                      n ∈ Finset.Ico q.1 q.2)
                    hmp.symm
                    hn
                have hIco_single :
                    Finset.Ico m (m + 1) = ({m} : Finset ℕ) :=
                  Nat.Ico_succ_singleton m
                have hn_eq : n = m :=
                  Finset.mem_singleton.mp
                    (Eq.subst
                      (motive := fun S : Finset ℕ => n ∈ S)
                      hIco_single
                      hn_single)
                have hk_pi :
                    Complex.realPhase_integerIncrement φ m -
                        (2 * Real.pi * (k : ℝ)) ∈
                      Set.Ioc (-Real.pi) Real.pi := by
                  have hupper :
                      (-Real.pi + (2 * Real.pi)) = Real.pi :=
                    real_neg_pi_add_two_pi_eq_pi_for_logarithmicPhase
                  exact And.intro hk.1
                    (Eq.subst
                      (motive := fun right : ℝ =>
                        Complex.realPhase_integerIncrement φ m -
                          (2 * Real.pi * (k : ℝ)) ≤ right)
                      hupper
                      hk.2)
                Eq.subst
                  (motive := fun x : ℕ =>
                    Complex.realPhase_integerIncrement φ x -
                        (2 * Real.pi * (k : ℝ)) ∈
                      Set.Ioc (-Real.pi) Real.pi)
                  hn_eq.symm
                  hk_pi)
  exact Exists.intro packets
    (And.intro hcover
      (And.intro hbounded
        (And.intro hdisjoint hprincipal)))

/-- If a raw adjacent increment already lies in the principal `toIocMod`
interval, then reduction does not change it. -/
theorem Complex.realPhase_reducedIntegerIncrement_eq_raw_of_mem_principal
    (φ : ℝ → ℝ)
    {n : ℕ}
    (hprincipal :
      Complex.realPhase_integerIncrement φ n ∈
        Set.Ioc (-Real.pi) (-Real.pi + (2 * Real.pi))) :
    Complex.realPhase_reducedIntegerIncrement φ n =
      Complex.realPhase_integerIncrement φ n := by
  unfold Complex.realPhase_reducedIntegerIncrement
  exact
    (toIocMod_eq_self Real.two_pi_pos).mpr hprincipal

/-- Principal-interval control transfers raw monotonicity to reduced
monotonicity. -/
theorem Complex.realPhase_reducedIntegerIncrementMonotoneOn_of_raw_principal
    (φ : ℝ → ℝ)
    {a b : ℕ}
    (hinc_mono : Complex.realPhase_integerIncrementMonotoneOn φ a b)
    (hprincipal :
      ∀ n : ℕ,
        n ∈ Finset.Ico a b →
          Complex.realPhase_integerIncrement φ n ∈
            Set.Ioc (-Real.pi) (-Real.pi + (2 * Real.pi))) :
    Complex.realPhase_reducedIntegerIncrementMonotoneOn φ a b := by
  match hinc_mono with
  | Or.inl hmono =>
      exact Or.inl
        (fun m hm n hn hmn =>
          have hm_eq :
              Complex.realPhase_reducedIntegerIncrement φ m =
                Complex.realPhase_integerIncrement φ m :=
            Complex.realPhase_reducedIntegerIncrement_eq_raw_of_mem_principal
              φ (hprincipal m hm)
          have hn_eq :
              Complex.realPhase_reducedIntegerIncrement φ n =
                Complex.realPhase_integerIncrement φ n :=
            Complex.realPhase_reducedIntegerIncrement_eq_raw_of_mem_principal
              φ (hprincipal n hn)
          have hraw :
              Complex.realPhase_integerIncrement φ m ≤
                Complex.realPhase_integerIncrement φ n :=
            hmono hm hn hmn
          Eq.subst
            (motive := fun left : ℝ =>
              left ≤ Complex.realPhase_reducedIntegerIncrement φ n)
            hm_eq.symm
            (Eq.subst
              (motive := fun right : ℝ =>
                Complex.realPhase_integerIncrement φ m ≤ right)
              hn_eq.symm
              hraw))
  | Or.inr hanti =>
      exact Or.inr
        (fun m hm n hn hmn =>
          have hm_eq :
              Complex.realPhase_reducedIntegerIncrement φ m =
                Complex.realPhase_integerIncrement φ m :=
            Complex.realPhase_reducedIntegerIncrement_eq_raw_of_mem_principal
              φ (hprincipal m hm)
          have hn_eq :
              Complex.realPhase_reducedIntegerIncrement φ n =
                Complex.realPhase_integerIncrement φ n :=
            Complex.realPhase_reducedIntegerIncrement_eq_raw_of_mem_principal
              φ (hprincipal n hn)
          have hraw :
              Complex.realPhase_integerIncrement φ n ≤
                Complex.realPhase_integerIncrement φ m :=
            hanti hm hn hmn
          Eq.subst
            (motive := fun left : ℝ =>
              left ≤ Complex.realPhase_reducedIntegerIncrement φ m)
            hn_eq.symm
            (Eq.subst
              (motive := fun right : ℝ =>
                Complex.realPhase_integerIncrement φ n ≤ right)
              hm_eq.symm
              hraw))

/-- Integer lattice shifts preserve raw increment monotonicity on a block. -/
theorem Complex.realPhase_integerIncrementMonotoneOn_integerLatticeShift
    (φ : ℝ → ℝ)
    (k : ℤ)
    {c d : ℕ}
    (hinc_mono : Complex.realPhase_integerIncrementMonotoneOn φ c d) :
    Complex.realPhase_integerIncrementMonotoneOn
      (Complex.realPhase_integerLatticeShift φ k) c d := by
  match hinc_mono with
  | Or.inl hinc =>
      exact Or.inl
        (fun m hm n hn hmn =>
          have hm_eq :
              Complex.realPhase_integerIncrement
                  (Complex.realPhase_integerLatticeShift φ k) m =
                Complex.realPhase_integerIncrement φ m -
                  (2 * Real.pi * (k : ℝ)) :=
            Complex.realPhase_integerIncrement_integerLatticeShift_eq φ k m
          have hn_eq :
              Complex.realPhase_integerIncrement
                  (Complex.realPhase_integerLatticeShift φ k) n =
                Complex.realPhase_integerIncrement φ n -
                  (2 * Real.pi * (k : ℝ)) :=
            Complex.realPhase_integerIncrement_integerLatticeShift_eq φ k n
          have hraw :
              Complex.realPhase_integerIncrement φ m ≤
                Complex.realPhase_integerIncrement φ n :=
            hinc hm hn hmn
          have hshift :
              Complex.realPhase_integerIncrement φ m -
                  (2 * Real.pi * (k : ℝ)) ≤
                Complex.realPhase_integerIncrement φ n -
                  (2 * Real.pi * (k : ℝ)) :=
            sub_le_sub_right hraw (2 * Real.pi * (k : ℝ))
          Eq.subst
            (motive := fun left : ℝ =>
              left ≤
                Complex.realPhase_integerIncrement
                  (Complex.realPhase_integerLatticeShift φ k) n)
            hm_eq.symm
            (Eq.subst
              (motive := fun right : ℝ =>
                Complex.realPhase_integerIncrement φ m -
                    (2 * Real.pi * (k : ℝ)) ≤ right)
              hn_eq.symm
              hshift))
  | Or.inr hanti =>
      exact Or.inr
        (fun m hm n hn hmn =>
          have hm_eq :
              Complex.realPhase_integerIncrement
                  (Complex.realPhase_integerLatticeShift φ k) m =
                Complex.realPhase_integerIncrement φ m -
                  (2 * Real.pi * (k : ℝ)) :=
            Complex.realPhase_integerIncrement_integerLatticeShift_eq φ k m
          have hn_eq :
              Complex.realPhase_integerIncrement
                  (Complex.realPhase_integerLatticeShift φ k) n =
                Complex.realPhase_integerIncrement φ n -
                  (2 * Real.pi * (k : ℝ)) :=
            Complex.realPhase_integerIncrement_integerLatticeShift_eq φ k n
          have hraw :
              Complex.realPhase_integerIncrement φ n ≤
                Complex.realPhase_integerIncrement φ m :=
            hanti hm hn hmn
          have hshift :
              Complex.realPhase_integerIncrement φ n -
                  (2 * Real.pi * (k : ℝ)) ≤
                Complex.realPhase_integerIncrement φ m -
                  (2 * Real.pi * (k : ℝ)) :=
            sub_le_sub_right hraw (2 * Real.pi * (k : ℝ))
          Eq.subst
            (motive := fun left : ℝ =>
              left ≤
                Complex.realPhase_integerIncrement
                  (Complex.realPhase_integerLatticeShift φ k) m)
            hn_eq.symm
            (Eq.subst
              (motive := fun right : ℝ =>
                Complex.realPhase_integerIncrement φ n -
                    (2 * Real.pi * (k : ℝ)) ≤ right)
              hm_eq.symm
              hshift))

/-- On a principal-branch packet, raw monotonicity gives reduced monotonicity.

Subtracting the packet's integer lattice frequency does not change the sampled
exponentials and identifies the reduced increment with the monotone raw
increment in that packet. -/
theorem Complex.realPhase_reducedIntegerIncrementMonotoneOn_of_principalBranchPacket
    (φ : ℝ → ℝ)
    {c d : ℕ}
    {k : ℤ}
    (hinc_mono : Complex.realPhase_integerIncrementMonotoneOn φ c d)
    (hprincipal :
      ∀ n : ℕ,
        n ∈ Finset.Ico c d →
          Complex.realPhase_integerIncrement φ n -
              (2 * Real.pi * (k : ℝ)) ∈
            Set.Ioc (-Real.pi) Real.pi) :
    Complex.realPhase_reducedIntegerIncrementMonotoneOn
      (Complex.realPhase_integerLatticeShift φ k) c d := by
  have hmono_shift :
      Complex.realPhase_integerIncrementMonotoneOn
        (Complex.realPhase_integerLatticeShift φ k) c d :=
    Complex.realPhase_integerIncrementMonotoneOn_integerLatticeShift
      φ k hinc_mono
  have hprincipal_shift :
      ∀ n : ℕ,
        n ∈ Finset.Ico c d →
          Complex.realPhase_integerIncrement
              (Complex.realPhase_integerLatticeShift φ k) n ∈
            Set.Ioc (-Real.pi) (-Real.pi + (2 * Real.pi)) := by
    intro n hn
    have hraw :
        Complex.realPhase_integerIncrement φ n -
            (2 * Real.pi * (k : ℝ)) ∈
          Set.Ioc (-Real.pi) Real.pi :=
      hprincipal n hn
    have hupper :
        Real.pi = -Real.pi + (2 * Real.pi) := by
      calc
        Real.pi = 0 + Real.pi :=
          (zero_add Real.pi).symm
        _ = (-Real.pi + Real.pi) + Real.pi :=
          congrArg (fun r : ℝ => r + Real.pi) (neg_add_cancel Real.pi).symm
        _ = -Real.pi + (Real.pi + Real.pi) :=
          add_assoc (-Real.pi) Real.pi Real.pi
        _ = -Real.pi + (2 * Real.pi) :=
          congrArg (fun r : ℝ => -Real.pi + r) (two_mul Real.pi).symm
    have hraw_principal :
        Complex.realPhase_integerIncrement φ n -
            (2 * Real.pi * (k : ℝ)) ∈
          Set.Ioc (-Real.pi) (-Real.pi + (2 * Real.pi)) :=
      And.intro hraw.1
        (Eq.subst
          (motive := fun right : ℝ =>
            Complex.realPhase_integerIncrement φ n -
              (2 * Real.pi * (k : ℝ)) ≤ right)
          hupper
          hraw.2)
    have hincrement :
        Complex.realPhase_integerIncrement
            (Complex.realPhase_integerLatticeShift φ k) n =
          Complex.realPhase_integerIncrement φ n -
            (2 * Real.pi * (k : ℝ)) :=
      Complex.realPhase_integerIncrement_integerLatticeShift_eq φ k n
    exact
      Eq.subst
        (motive := fun r : ℝ =>
          r ∈ Set.Ioc (-Real.pi) (-Real.pi + (2 * Real.pi)))
        hincrement.symm
        hraw_principal
  exact
    Complex.realPhase_reducedIntegerIncrementMonotoneOn_of_raw_principal
      (Complex.realPhase_integerLatticeShift φ k)
      hmono_shift
      hprincipal_shift

/-- Integer lattice shifts preserve the sampled exponential sum on integer
blocks. -/
theorem Complex.realPhase_Ico_sum_integerLatticeShift_eq
    (φ : ℝ → ℝ)
    (k : ℤ)
    (c d : ℕ) :
    (∑ n ∈ Finset.Ico c d,
      Complex.exp
        (Complex.I *
          ((Complex.realPhase_integerLatticeShift φ k) n : ℂ))) =
      ∑ n ∈ Finset.Ico c d,
        Complex.exp (Complex.I * (φ n : ℂ)) := by
  exact Finset.sum_congr rfl
    (fun n _hn =>
      have hperiod :
          Complex.exp
              (((φ n - (2 * Real.pi * (k : ℝ)) * (n : ℝ) : ℝ) : ℂ) *
                Complex.I) =
            Complex.exp ((φ n : ℂ) * Complex.I) :=
        Complex.exp_mul_I_real_sub_int_two_pi_mul_nat_period_for_logarithmicPhase
          (φ n) k n
      have hleft_arg :
          Complex.I *
              (Complex.realPhase_integerLatticeShift φ k n : ℂ) =
            ((φ n - (2 * Real.pi * (k : ℝ)) * (n : ℝ) : ℝ) : ℂ) *
              Complex.I := by
        unfold Complex.realPhase_integerLatticeShift
        exact mul_comm Complex.I
          ((φ (n : ℝ) - (2 * Real.pi * (k : ℝ)) * (n : ℝ) : ℝ) : ℂ)
      have hright_arg :
          (φ n : ℂ) * Complex.I =
            Complex.I * (φ n : ℂ) :=
        mul_comm (φ n : ℂ) Complex.I
      Eq.trans
        (congrArg Complex.exp hleft_arg)
        (Eq.trans hperiod
          (congrArg Complex.exp hright_arg)))

/-- Integer lattice shifts preserve raw increment monotonicity on a block. -/
theorem Complex.realPhase_integerIncrementMonotoneOn_principalBranchShift
    (φ : ℝ → ℝ)
    (k : ℤ)
    {c d : ℕ}
    (hinc_mono : Complex.realPhase_integerIncrementMonotoneOn φ c d) :
    Complex.realPhase_integerIncrementMonotoneOn
      (Complex.realPhase_integerLatticeShift φ k) c d := by
  match hinc_mono with
  | Or.inl hinc =>
      exact Or.inl
        (fun m hm n hn hmn =>
          have hm_eq :
              Complex.realPhase_integerIncrement
                  (Complex.realPhase_integerLatticeShift φ k) m =
                Complex.realPhase_integerIncrement φ m -
                  (2 * Real.pi * (k : ℝ)) :=
            Complex.realPhase_integerIncrement_integerLatticeShift_eq φ k m
          have hn_eq :
              Complex.realPhase_integerIncrement
                  (Complex.realPhase_integerLatticeShift φ k) n =
                Complex.realPhase_integerIncrement φ n -
                  (2 * Real.pi * (k : ℝ)) :=
            Complex.realPhase_integerIncrement_integerLatticeShift_eq φ k n
          have hraw :
              Complex.realPhase_integerIncrement φ m ≤
                Complex.realPhase_integerIncrement φ n :=
            hinc hm hn hmn
          have hshift :
              Complex.realPhase_integerIncrement φ m -
                  (2 * Real.pi * (k : ℝ)) ≤
                Complex.realPhase_integerIncrement φ n -
                  (2 * Real.pi * (k : ℝ)) :=
            sub_le_sub_right hraw (2 * Real.pi * (k : ℝ))
          Eq.subst
            (motive := fun left : ℝ =>
              left ≤
                Complex.realPhase_integerIncrement
                  (Complex.realPhase_integerLatticeShift φ k) n)
            hm_eq.symm
            (Eq.subst
              (motive := fun right : ℝ =>
                Complex.realPhase_integerIncrement φ m -
                    (2 * Real.pi * (k : ℝ)) ≤ right)
              hn_eq.symm
              hshift))
  | Or.inr hdec =>
      exact Or.inr
        (fun m hm n hn hmn =>
          have hm_eq :
              Complex.realPhase_integerIncrement
                  (Complex.realPhase_integerLatticeShift φ k) m =
                Complex.realPhase_integerIncrement φ m -
                  (2 * Real.pi * (k : ℝ)) :=
            Complex.realPhase_integerIncrement_integerLatticeShift_eq φ k m
          have hn_eq :
              Complex.realPhase_integerIncrement
                  (Complex.realPhase_integerLatticeShift φ k) n =
                Complex.realPhase_integerIncrement φ n -
                  (2 * Real.pi * (k : ℝ)) :=
            Complex.realPhase_integerIncrement_integerLatticeShift_eq φ k n
          have hraw :
              Complex.realPhase_integerIncrement φ n ≤
                Complex.realPhase_integerIncrement φ m :=
            hdec hm hn hmn
          have hshift :
              Complex.realPhase_integerIncrement φ n -
                  (2 * Real.pi * (k : ℝ)) ≤
                Complex.realPhase_integerIncrement φ m -
                  (2 * Real.pi * (k : ℝ)) :=
            sub_le_sub_right hraw (2 * Real.pi * (k : ℝ))
          Eq.subst
            (motive := fun left : ℝ =>
              left ≤
                Complex.realPhase_integerIncrement
                  (Complex.realPhase_integerLatticeShift φ k) m)
            hn_eq.symm
            (Eq.subst
              (motive := fun right : ℝ =>
                Complex.realPhase_integerIncrement φ n -
                    (2 * Real.pi * (k : ℝ)) ≤ right)
              hm_eq.symm
              hshift))

/-- Integer lattice shifts preserve all-integer increment separation. -/
theorem Complex.realPhase_integerIncrementSeparatedOn_integerLatticeShift
    (φ : ℝ → ℝ)
    (k : ℤ)
    {c d : ℕ}
    {lam : ℝ}
    (hsep : Complex.realPhase_integerIncrementSeparatedOn φ c d lam) :
    Complex.realPhase_integerIncrementSeparatedOn
      (Complex.realPhase_integerLatticeShift φ k) c d lam := by
  intro n hn l
  have hbase :
      lam ≤
        ‖Complex.realPhase_integerIncrement φ n -
          (2 * Real.pi * ((k + l : ℤ) : ℝ))‖ :=
    hsep n hn (k + l)
  have hcenter :
      (2 * Real.pi * ((k + l : ℤ) : ℝ)) =
        (2 * Real.pi * (k : ℝ)) +
          (2 * Real.pi * (l : ℝ)) := by
    have hcast : ((k + l : ℤ) : ℝ) = (k : ℝ) + (l : ℝ) :=
      Int.cast_add k l
    calc
      (2 * Real.pi * ((k + l : ℤ) : ℝ)) =
          2 * Real.pi * ((k : ℝ) + (l : ℝ)) := by
        exact congrArg (fun r : ℝ => 2 * Real.pi * r) hcast
      _ =
          (2 * Real.pi * (k : ℝ)) +
            (2 * Real.pi * (l : ℝ)) := by
        exact mul_add (2 * Real.pi) (k : ℝ) (l : ℝ)
  have hincrement :
      Complex.realPhase_integerIncrement
          (Complex.realPhase_integerLatticeShift φ k) n =
        Complex.realPhase_integerIncrement φ n -
          (2 * Real.pi * (k : ℝ)) :=
    Complex.realPhase_integerIncrement_integerLatticeShift_eq φ k n
  have harg :
      Complex.realPhase_integerIncrement
            (Complex.realPhase_integerLatticeShift φ k) n -
          (2 * Real.pi * (l : ℝ)) =
        Complex.realPhase_integerIncrement φ n -
          (2 * Real.pi * ((k + l : ℤ) : ℝ)) := by
    calc
      Complex.realPhase_integerIncrement
            (Complex.realPhase_integerLatticeShift φ k) n -
          (2 * Real.pi * (l : ℝ)) =
        (Complex.realPhase_integerIncrement φ n -
            (2 * Real.pi * (k : ℝ))) -
          (2 * Real.pi * (l : ℝ)) := by
        exact congrArg
          (fun r : ℝ => r - (2 * Real.pi * (l : ℝ)))
          hincrement
      _ =
        Complex.realPhase_integerIncrement φ n -
          ((2 * Real.pi * (k : ℝ)) +
            (2 * Real.pi * (l : ℝ))) := by
        exact sub_sub
          (Complex.realPhase_integerIncrement φ n)
          (2 * Real.pi * (k : ℝ))
          (2 * Real.pi * (l : ℝ))
      _ =
        Complex.realPhase_integerIncrement φ n -
          (2 * Real.pi * ((k + l : ℤ) : ℝ)) := by
        exact congrArg
          (fun r : ℝ => Complex.realPhase_integerIncrement φ n - r)
          hcenter.symm
  exact
    Eq.subst
      (motive := fun r : ℝ => lam ≤ ‖r‖)
      harg.symm
      hbase

/-- A single principal-branch packet satisfies the already-proved reduced
Kusmin-Landau estimate after shifting its integer lattice frequency to zero. -/
theorem Complex.realPhase_Ico_sum_norm_le_principalBranchPacket
    (φ : ℝ → ℝ)
    {c d : ℕ}
    {lam : ℝ}
    {k : ℤ}
    (_hc : 1 ≤ c)
    (hlam_pos : 0 < lam)
    (hinc_mono : Complex.realPhase_integerIncrementMonotoneOn φ c d)
    (hsep : Complex.realPhase_integerIncrementSeparatedOn φ c d lam)
    (hprincipal :
      ∀ n : ℕ,
        n ∈ Finset.Ico c d →
          Complex.realPhase_integerIncrement φ n -
              (2 * Real.pi * (k : ℝ)) ∈
            Set.Ioc (-Real.pi) Real.pi) :
    ‖∑ n ∈ Finset.Ico c d,
      Complex.exp (Complex.I * (φ n : ℂ))‖ ≤
        4 * (lam⁻¹ + 1) + 4 * Real.pi * lam⁻¹ := by
  let ψ : ℝ → ℝ := Complex.realPhase_integerLatticeShift φ k
  have hinc_shift :
      Complex.realPhase_integerIncrementMonotoneOn ψ c d := by
    unfold ψ
    exact
      Complex.realPhase_integerIncrementMonotoneOn_principalBranchShift
        φ k hinc_mono
  have hred_shift :
      Complex.realPhase_reducedIntegerIncrementMonotoneOn ψ c d := by
    unfold ψ
    exact
      Complex.realPhase_reducedIntegerIncrementMonotoneOn_of_principalBranchPacket
        φ hinc_mono hprincipal
  have hsep_shift :
      Complex.realPhase_integerIncrementSeparatedOn ψ c d lam := by
    unfold ψ
    exact
      Complex.realPhase_integerIncrementSeparatedOn_integerLatticeShift
        φ k hsep
  have htarget_nonneg :
      0 ≤ 4 * (lam⁻¹ + 1) + 4 * Real.pi * lam⁻¹ := by
    have hlam_inv_nonneg : 0 ≤ lam⁻¹ :=
      inv_nonneg.mpr hlam_pos.le
    have hone_nonneg : 0 ≤ (1 : ℝ) :=
      zero_le_one
    have hsum_nonneg : 0 ≤ lam⁻¹ + 1 :=
      add_nonneg hlam_inv_nonneg hone_nonneg
    have hleft_nonneg : 0 ≤ 4 * (lam⁻¹ + 1) :=
      mul_nonneg zero_le_four hsum_nonneg
    have hfour_pi_nonneg : 0 ≤ 4 * Real.pi :=
      mul_nonneg zero_le_four (le_of_lt Real.pi_pos)
    have hright_nonneg : 0 ≤ 4 * Real.pi * lam⁻¹ :=
      mul_nonneg hfour_pi_nonneg hlam_inv_nonneg
    exact add_nonneg hleft_nonneg hright_nonneg
  match Classical.em (c < d) with
  | Or.inr hnot_lt =>
      have hIco_empty : Finset.Ico c d = (∅ : Finset ℕ) :=
        Finset.Ico_eq_empty hnot_lt
      have hsum_empty :
          (∑ n ∈ Finset.Ico c d,
            Complex.exp (Complex.I * (φ n : ℂ))) = 0 := by
        exact Eq.trans
          (congrArg
            (fun S : Finset ℕ =>
              ∑ n ∈ S, Complex.exp (Complex.I * (φ n : ℂ)))
            hIco_empty)
          Finset.sum_empty
      exact
        Eq.subst
          (motive := fun z : ℂ =>
            ‖z‖ ≤ 4 * (lam⁻¹ + 1) + 4 * Real.pi * lam⁻¹)
          hsum_empty.symm
          (Eq.subst
            (motive := fun r : ℝ =>
              r ≤ 4 * (lam⁻¹ + 1) + 4 * Real.pi * lam⁻¹)
            norm_zero.symm
            htarget_nonneg)
  | Or.inl hcd =>
      have hd_pos : 0 < d :=
        lt_of_le_of_lt (Nat.zero_le c) hcd
      have hm : d ∈ Finset.Icc c d :=
        Finset.mem_Icc.mpr ⟨le_of_lt hcd, le_rfl⟩
      have hshift_sum :
          (∑ n ∈ Finset.Ico c d,
            Complex.exp (Complex.I * (ψ n : ℂ))) =
            ∑ n ∈ Finset.Ico c d,
              Complex.exp (Complex.I * (φ n : ℂ)) := by
        unfold ψ
        exact Complex.realPhase_Ico_sum_integerLatticeShift_eq φ k c d
      have hden :
          ∀ n : ℕ,
            n ∈ Finset.Ico c d →
              ‖Complex.realPhase_inverseGeometricDenominator ψ n‖ ≤
                2 * lam⁻¹ := by
        intro n hn
        exact
          Complex.realPhase_geometricDenominator_inv_norm_bound
            hlam_pos
            (hsep_shift n hn)
      have htelescope :
          (∑ n ∈ Finset.Ico c d,
            Complex.realPhase_integerUnit ψ n) =
              Complex.realPhase_inverseGeometricDenominator ψ c *
                Complex.realPhase_integerUnit ψ c -
              Complex.realPhase_inverseGeometricDenominator ψ (d - 1) *
                Complex.realPhase_integerUnit ψ d +
              Complex.realPhase_prefixAbelVariation ψ c d :=
        Complex.realPhase_prefixAbel_Ico_telescope
          ψ hcd hm hlam_pos hsep_shift
      have hvariation :
          ‖Complex.realPhase_prefixAbelVariation ψ c d‖ ≤
            4 * Real.pi * lam⁻¹ :=
        Complex.realPhase_prefixAbelVariation_norm_bound
          ψ hcd hm hlam_pos hinc_shift hred_shift hsep_shift hden
      have hendpoint :
          ‖Complex.realPhase_inverseGeometricDenominator ψ c *
                Complex.realPhase_integerUnit ψ c -
              Complex.realPhase_inverseGeometricDenominator ψ (d - 1) *
                Complex.realPhase_integerUnit ψ d‖ ≤
            4 * (lam⁻¹ + 1) := by
        have hc_mem : c ∈ Finset.Ico c d :=
          Finset.mem_Ico.mpr ⟨le_rfl, hcd⟩
        have hpred_mem : d - 1 ∈ Finset.Ico c d := by
          have hc_pred : c ≤ d - 1 :=
            Nat.le_pred_of_lt hcd
          have hpred_lt : d - 1 < d :=
            Nat.pred_lt (Nat.ne_of_gt hd_pos)
          exact Finset.mem_Ico.mpr ⟨hc_pred, hpred_lt⟩
        have hc_den :
            ‖Complex.realPhase_inverseGeometricDenominator ψ c‖ ≤
              2 * lam⁻¹ :=
          hden c hc_mem
        have hpred_den :
            ‖Complex.realPhase_inverseGeometricDenominator ψ (d - 1)‖ ≤
              2 * lam⁻¹ :=
          hden (d - 1) hpred_mem
        have hc_unit :
            ‖Complex.realPhase_integerUnit ψ c‖ = 1 :=
          Complex.realPhase_exp_I_norm ψ c
        have hd_unit :
            ‖Complex.realPhase_integerUnit ψ d‖ = 1 :=
          Complex.realPhase_exp_I_norm ψ d
        have hfirst :
            ‖Complex.realPhase_inverseGeometricDenominator ψ c *
              Complex.realPhase_integerUnit ψ c‖ ≤ 2 * lam⁻¹ := by
          calc
            ‖Complex.realPhase_inverseGeometricDenominator ψ c *
              Complex.realPhase_integerUnit ψ c‖ =
                ‖Complex.realPhase_inverseGeometricDenominator ψ c‖ *
                  ‖Complex.realPhase_integerUnit ψ c‖ :=
              norm_mul
                (Complex.realPhase_inverseGeometricDenominator ψ c)
                (Complex.realPhase_integerUnit ψ c)
            _ = ‖Complex.realPhase_inverseGeometricDenominator ψ c‖ * 1 := by
              exact congrArg
                (fun r : ℝ =>
                  ‖Complex.realPhase_inverseGeometricDenominator ψ c‖ * r)
                hc_unit
            _ = ‖Complex.realPhase_inverseGeometricDenominator ψ c‖ :=
              mul_one _
            _ ≤ 2 * lam⁻¹ :=
              hc_den
        have hsecond :
            ‖Complex.realPhase_inverseGeometricDenominator ψ (d - 1) *
              Complex.realPhase_integerUnit ψ d‖ ≤ 2 * lam⁻¹ := by
          calc
            ‖Complex.realPhase_inverseGeometricDenominator ψ (d - 1) *
              Complex.realPhase_integerUnit ψ d‖ =
                ‖Complex.realPhase_inverseGeometricDenominator ψ (d - 1)‖ *
                  ‖Complex.realPhase_integerUnit ψ d‖ :=
              norm_mul
                (Complex.realPhase_inverseGeometricDenominator ψ (d - 1))
                (Complex.realPhase_integerUnit ψ d)
            _ = ‖Complex.realPhase_inverseGeometricDenominator ψ (d - 1)‖ * 1 := by
              exact congrArg
                (fun r : ℝ =>
                  ‖Complex.realPhase_inverseGeometricDenominator ψ (d - 1)‖ * r)
                hd_unit
            _ = ‖Complex.realPhase_inverseGeometricDenominator ψ (d - 1)‖ :=
              mul_one _
            _ ≤ 2 * lam⁻¹ :=
              hpred_den
        have htwo_endpoint :
            ‖Complex.realPhase_inverseGeometricDenominator ψ c *
                  Complex.realPhase_integerUnit ψ c -
                Complex.realPhase_inverseGeometricDenominator ψ (d - 1) *
                  Complex.realPhase_integerUnit ψ d‖ ≤
              2 * lam⁻¹ + 2 * lam⁻¹ := by
          exact le_trans
            (norm_sub_le
              (Complex.realPhase_inverseGeometricDenominator ψ c *
                Complex.realPhase_integerUnit ψ c)
              (Complex.realPhase_inverseGeometricDenominator ψ (d - 1) *
                Complex.realPhase_integerUnit ψ d))
            (add_le_add hfirst hsecond)
        have htwo_to_target :
            2 * lam⁻¹ + 2 * lam⁻¹ ≤ 4 * (lam⁻¹ + 1) := by
          have hlam_inv_nonneg : 0 ≤ lam⁻¹ :=
            inv_nonneg.mpr hlam_pos.le
          have htwo_sum :
              2 * lam⁻¹ + 2 * lam⁻¹ = (2 + 2 : ℝ) * lam⁻¹ :=
            (add_mul (2 : ℝ) 2 lam⁻¹).symm
          have hfour_nat :
              (2 + 2 : ℝ) = 4 := by
            have htwo_cast :
                ((2 : ℕ) : ℝ) = 2 :=
              Nat.cast_ofNat
            have hcast_add :
                (((2 + 2 : ℕ) : ℝ)) = (2 : ℝ) + (2 : ℝ) :=
              Eq.trans
                (Nat.cast_add 2 2)
                (congrArg₂ (fun x y : ℝ => x + y)
                  htwo_cast htwo_cast)
            have hnat :
                (((2 + 2 : ℕ) : ℝ)) = ((4 : ℕ) : ℝ) :=
              congrArg (fun n : ℕ => (n : ℝ))
                (show 2 + 2 = 4 from rfl)
            have hfour :
                ((4 : ℕ) : ℝ) = 4 :=
              Nat.cast_ofNat
            exact Eq.trans hcast_add.symm (Eq.trans hnat hfour)
          have hfour_inv_eq :
              2 * lam⁻¹ + 2 * lam⁻¹ = 4 * lam⁻¹ :=
            Eq.trans htwo_sum
              (congrArg (fun r : ℝ => r * lam⁻¹) hfour_nat)
          have hinner :
              lam⁻¹ ≤ lam⁻¹ + 1 :=
            le_add_of_nonneg_right zero_le_one
          have hmul :
              4 * lam⁻¹ ≤ 4 * (lam⁻¹ + 1) :=
            mul_le_mul_of_nonneg_left hinner zero_le_four
          exact Eq.subst
            (motive := fun left : ℝ => left ≤ 4 * (lam⁻¹ + 1))
            hfour_inv_eq.symm
            hmul
        exact le_trans htwo_endpoint htwo_to_target
      have hsum_shift_bound :
          ‖∑ n ∈ Finset.Ico c d,
            Complex.exp (Complex.I * (ψ n : ℂ))‖ ≤
            4 * (lam⁻¹ + 1) + 4 * Real.pi * lam⁻¹ := by
        have hunit_sum :
            (∑ n ∈ Finset.Ico c d,
              Complex.exp (Complex.I * (ψ n : ℂ))) =
              ∑ n ∈ Finset.Ico c d,
                Complex.realPhase_integerUnit ψ n := by
          rfl
        have hnorm_telescope :
            ‖∑ n ∈ Finset.Ico c d,
              Complex.realPhase_integerUnit ψ n‖ ≤
              ‖Complex.realPhase_inverseGeometricDenominator ψ c *
                    Complex.realPhase_integerUnit ψ c -
                  Complex.realPhase_inverseGeometricDenominator ψ (d - 1) *
                    Complex.realPhase_integerUnit ψ d‖ +
                ‖Complex.realPhase_prefixAbelVariation ψ c d‖ := by
          let endpoint : ℂ :=
            Complex.realPhase_inverseGeometricDenominator ψ c *
                Complex.realPhase_integerUnit ψ c -
              Complex.realPhase_inverseGeometricDenominator ψ (d - 1) *
                Complex.realPhase_integerUnit ψ d
          let variation : ℂ := Complex.realPhase_prefixAbelVariation ψ c d
          have htelescope_named :
              (∑ n ∈ Finset.Ico c d,
                Complex.realPhase_integerUnit ψ n) =
                  endpoint + variation := by
            unfold endpoint variation
            exact htelescope
          exact
            Eq.subst
              (motive := fun z : ℂ =>
                ‖z‖ ≤ ‖endpoint‖ + ‖variation‖)
              htelescope_named.symm
              (norm_add_le endpoint variation)
        exact
          Eq.subst
            (motive := fun z : ℂ =>
              ‖z‖ ≤ 4 * (lam⁻¹ + 1) + 4 * Real.pi * lam⁻¹)
            hunit_sum.symm
            (le_trans hnorm_telescope
              (add_le_add hendpoint hvariation))
      exact
        Eq.subst
          (motive := fun z : ℂ =>
            ‖z‖ ≤ 4 * (lam⁻¹ + 1) + 4 * Real.pi * lam⁻¹)
          hshift_sum
          hsum_shift_bound

/-- Half-open Abel telescope for unit complex samples and chord coefficients.

If `z n = q n * (z n - z (n + 1))` on `[a,b)`, then the half-open sum is
bounded by two endpoint coefficients and the total variation of `q` on the
same half-open block. -/
theorem Complex.Ico_sum_norm_le_chordAbel_endpoint_add_variation
    (z q : ℕ → ℂ)
    {a b : ℕ}
    (hz_unit : ∀ n : ℕ, n ∈ Finset.Icc a b → ‖z n‖ = 1)
    (hstep :
      ∀ n : ℕ,
        n ∈ Finset.Ico a b →
          z n = q n * (z n - z (n + 1))) :
    ‖∑ n ∈ Finset.Ico a b, z n‖ ≤
      ‖q a‖ + ‖q (b - 1)‖ +
        ∑ n ∈ Finset.Ico (a + 1) b, ‖q n - q (n - 1)‖ := by
  match Classical.em (a < b) with
  | Or.inr hnot_lt =>
      have hIco_empty : Finset.Ico a b = (∅ : Finset ℕ) :=
        Finset.Ico_eq_empty hnot_lt
      have hsum_empty :
          (∑ n ∈ Finset.Ico a b, z n) = 0 := by
        exact Eq.trans
          (congrArg (fun s : Finset ℕ => ∑ n ∈ s, z n) hIco_empty)
          Finset.sum_empty
      have hright_nonneg :
          0 ≤
            ‖q a‖ + ‖q (b - 1)‖ +
              ∑ n ∈ Finset.Ico (a + 1) b, ‖q n - q (n - 1)‖ := by
        have hleft : 0 ≤ ‖q a‖ + ‖q (b - 1)‖ :=
          add_nonneg (norm_nonneg (q a)) (norm_nonneg (q (b - 1)))
        have hsum :
            0 ≤ ∑ n ∈ Finset.Ico (a + 1) b, ‖q n - q (n - 1)‖ :=
          Finset.sum_nonneg
            (fun n _hn => norm_nonneg (q n - q (n - 1)))
        exact add_nonneg hleft hsum
      exact
        Eq.subst
          (motive := fun s : ℂ =>
            ‖s‖ ≤
              ‖q a‖ + ‖q (b - 1)‖ +
                ∑ n ∈ Finset.Ico (a + 1) b, ‖q n - q (n - 1)‖)
          hsum_empty.symm
          (Eq.subst
            (motive := fun r : ℝ =>
              r ≤
                ‖q a‖ + ‖q (b - 1)‖ +
                  ∑ n ∈ Finset.Ico (a + 1) b, ‖q n - q (n - 1)‖)
            norm_zero.symm
            hright_nonneg)
  | Or.inl hab =>
      have hterm :
          (∑ n ∈ Finset.Ico a b, z n) =
            ∑ n ∈ Finset.Ico a b, q n * (z n - z (n + 1)) := by
        exact Finset.sum_congr rfl
          (fun n hn => hstep n hn)
      have htelescope :
          (∑ n ∈ Finset.Ico a b, q n * (z n - z (n + 1))) =
            q a * z a - q (b - 1) * z b +
              ∑ n ∈ Finset.Ioo a b, (q n - q (n - 1)) * z n :=
        Complex.finiteAbel_Ico_mul_sub_telescope q z hab
      let endpoint : ℂ := q a * z a - q (b - 1) * z b
      let variation : ℂ :=
        ∑ n ∈ Finset.Ioo a b, (q n - q (n - 1)) * z n
      have hsum_telescope :
          (∑ n ∈ Finset.Ico a b, z n) = endpoint + variation := by
        unfold endpoint variation
        exact Eq.trans hterm htelescope
      have ha_mem : a ∈ Finset.Icc a b :=
        Finset.mem_Icc.mpr ⟨le_rfl, le_of_lt hab⟩
      have hb_mem : b ∈ Finset.Icc a b :=
        Finset.mem_Icc.mpr ⟨le_of_lt hab, le_rfl⟩
      have ha_unit : ‖z a‖ = 1 :=
        hz_unit a ha_mem
      have hb_unit : ‖z b‖ = 1 :=
        hz_unit b hb_mem
      have hendpoint :
          ‖endpoint‖ ≤ ‖q a‖ + ‖q (b - 1)‖ := by
        unfold endpoint
        have hfirst :
            ‖q a * z a‖ = ‖q a‖ := by
          calc
            ‖q a * z a‖ = ‖q a‖ * ‖z a‖ :=
              norm_mul (q a) (z a)
            _ = ‖q a‖ * 1 := by
              exact congrArg (fun r : ℝ => ‖q a‖ * r) ha_unit
            _ = ‖q a‖ :=
              mul_one ‖q a‖
        have hsecond :
            ‖q (b - 1) * z b‖ = ‖q (b - 1)‖ := by
          calc
            ‖q (b - 1) * z b‖ = ‖q (b - 1)‖ * ‖z b‖ :=
              norm_mul (q (b - 1)) (z b)
            _ = ‖q (b - 1)‖ * 1 := by
              exact congrArg (fun r : ℝ => ‖q (b - 1)‖ * r) hb_unit
            _ = ‖q (b - 1)‖ :=
              mul_one ‖q (b - 1)‖
        exact
          le_trans
            (norm_sub_le (q a * z a) (q (b - 1) * z b))
            (Eq.subst
              (motive := fun r : ℝ =>
                r ≤ ‖q a‖ + ‖q (b - 1)‖)
              (congrArg₂ (fun x y : ℝ => x + y) hfirst hsecond).symm
              (le_refl (‖q a‖ + ‖q (b - 1)‖)))
      have hvariation :
          ‖variation‖ ≤
            ∑ n ∈ Finset.Ico (a + 1) b, ‖q n - q (n - 1)‖ := by
        have hnorm_sum :
            ‖variation‖ ≤
              ∑ n ∈ Finset.Ioo a b, ‖(q n - q (n - 1)) * z n‖ := by
          unfold variation
          exact norm_sum_le (Finset.Ioo a b)
            (fun n => (q n - q (n - 1)) * z n)
        have hunit_sum :
            (∑ n ∈ Finset.Ioo a b, ‖(q n - q (n - 1)) * z n‖) =
              ∑ n ∈ Finset.Ioo a b, ‖q n - q (n - 1)‖ := by
          exact Finset.sum_congr rfl
            (fun n hn =>
              have hn_bounds : a < n ∧ n < b :=
                Finset.mem_Ioo.mp hn
              have hn_Icc : n ∈ Finset.Icc a b :=
                Finset.mem_Icc.mpr
                  ⟨le_of_lt hn_bounds.1, le_of_lt hn_bounds.2⟩
              have hn_unit : ‖z n‖ = 1 :=
                hz_unit n hn_Icc
              calc
                ‖(q n - q (n - 1)) * z n‖ =
                    ‖q n - q (n - 1)‖ * ‖z n‖ :=
                  norm_mul (q n - q (n - 1)) (z n)
                _ = ‖q n - q (n - 1)‖ * 1 := by
                  exact congrArg
                    (fun r : ℝ => ‖q n - q (n - 1)‖ * r)
                    hn_unit
                _ = ‖q n - q (n - 1)‖ :=
                  mul_one ‖q n - q (n - 1)‖)
        have hIoo :
            Finset.Ioo a b = Finset.Ico (a + 1) b :=
          Finset.nat_Ioo_eq_Ico_succ_left_for_logarithmicPhase a b
        exact
          le_trans hnorm_sum
            (Eq.subst
              (motive := fun r : ℝ =>
                r ≤
                  ∑ n ∈ Finset.Ico (a + 1) b, ‖q n - q (n - 1)‖)
              hunit_sum.symm
              (Eq.subst
                (motive := fun s : Finset ℕ =>
                  (∑ n ∈ s, ‖q n - q (n - 1)‖) ≤
                    ∑ n ∈ Finset.Ico (a + 1) b, ‖q n - q (n - 1)‖)
                hIoo.symm
                (le_refl
                  (∑ n ∈ Finset.Ico (a + 1) b,
                    ‖q n - q (n - 1)‖))))
      have hnorm :
          ‖∑ n ∈ Finset.Ico a b, z n‖ ≤ ‖endpoint‖ + ‖variation‖ := by
        exact
          Eq.subst
            (motive := fun s : ℂ => ‖s‖ ≤ ‖endpoint‖ + ‖variation‖)
            hsum_telescope.symm
            (norm_add_le endpoint variation)
      exact
        le_trans hnorm
          (add_le_add hendpoint hvariation)

/-- Endpoint budget for the two chord-Abel endpoint coefficients.

The degenerate half-open cases are included here so the public all-integer
Kusmin-Landau theorem remains a thin Abel-telescope wrapper. -/
theorem Complex.realPhase_allIntegerMonotoneSeparated_inverseGeometricDenominator_endpoint_bound
    (φ : ℝ → ℝ)
    {c d : ℕ}
    {lam : ℝ}
    (_hc : 1 ≤ c)
    (hcd : c < d)
    (hlam_pos : 0 < lam)
    (hsep : Complex.realPhase_integerIncrementSeparatedOn φ c d lam) :
    ‖Complex.realPhase_inverseGeometricDenominator φ c‖ +
      ‖Complex.realPhase_inverseGeometricDenominator φ (d - 1)‖ ≤
        4 * (lam⁻¹ + 1) := by
  have hd_pos : 0 < d :=
    lt_of_le_of_lt (Nat.zero_le c) hcd
  have hc_mem : c ∈ Finset.Ico c d :=
    Finset.mem_Ico.mpr ⟨le_rfl, hcd⟩
  have hpred_mem : d - 1 ∈ Finset.Ico c d := by
    have hc_pred : c ≤ d - 1 :=
      Nat.le_pred_of_lt hcd
    have hpred_lt : d - 1 < d :=
      Nat.pred_lt (Nat.ne_of_gt hd_pos)
    exact Finset.mem_Ico.mpr ⟨hc_pred, hpred_lt⟩
  have hc_bound :
      ‖Complex.realPhase_inverseGeometricDenominator φ c‖ ≤
        2 * lam⁻¹ := by
    unfold Complex.realPhase_inverseGeometricDenominator
    exact
      Complex.realPhase_geometricDenominator_inv_norm_bound
        hlam_pos
        (hsep c hc_mem)
  have hpred_bound :
      ‖Complex.realPhase_inverseGeometricDenominator φ (d - 1)‖ ≤
        2 * lam⁻¹ := by
    unfold Complex.realPhase_inverseGeometricDenominator
    exact
      Complex.realPhase_geometricDenominator_inv_norm_bound
        hlam_pos
        (hsep (d - 1) hpred_mem)
  have htwo_endpoint :
      ‖Complex.realPhase_inverseGeometricDenominator φ c‖ +
        ‖Complex.realPhase_inverseGeometricDenominator φ (d - 1)‖ ≤
          2 * lam⁻¹ + 2 * lam⁻¹ :=
    add_le_add hc_bound hpred_bound
  have htwo_to_four :
      2 * lam⁻¹ + 2 * lam⁻¹ ≤ 4 * (lam⁻¹ + 1) := by
    have hfour_eq :
        2 * lam⁻¹ + 2 * lam⁻¹ = 4 * lam⁻¹ :=
      real_two_mul_add_two_mul_eq_four_mul_for_logarithmicPhase lam⁻¹
    have hinner :
        lam⁻¹ ≤ lam⁻¹ + 1 :=
      le_add_of_nonneg_right zero_le_one
    have hmul :
        4 * lam⁻¹ ≤ 4 * (lam⁻¹ + 1) :=
      mul_le_mul_of_nonneg_left hinner zero_le_four
    exact Eq.subst
      (motive := fun r : ℝ => r ≤ 4 * (lam⁻¹ + 1))
      hfour_eq.symm
      hmul
  exact le_trans htwo_endpoint htwo_to_four

/-- Add the two all-integer Abel budgets into the public numerical target. -/
theorem realPhase_allIntegerMonotoneSeparated_abelBudget_le_target
    {endpoint variation lam : ℝ}
    (hendpoint : endpoint ≤ 4 * (lam⁻¹ + 1))
    (hvariation : variation ≤ 4 * Real.pi * lam⁻¹) :
    endpoint + variation ≤
      4 * (lam⁻¹ + 1) + 4 * Real.pi * lam⁻¹ :=
  add_le_add hendpoint hvariation

/-- Phase half-open Abel bound from explicit chord-coefficient budgets.

This wrapper intentionally does not assert that raw monotonicity and separation
control the coefficient variation.  It only combines the chord identity with
separately supplied endpoint and variation budgets. -/
theorem Complex.realPhase_Ico_sum_norm_le_allIntegerAbelVariation
    (φ : ℝ → ℝ)
    {c d : ℕ}
    {endpointBudget variationBudget : ℝ}
    {lam : ℝ}
    (hlam_pos : 0 < lam)
    (hsep : Complex.realPhase_integerIncrementSeparatedOn φ c d lam)
    (hendpoint :
      ‖Complex.realPhase_inverseGeometricDenominator φ c‖ +
        ‖Complex.realPhase_inverseGeometricDenominator φ (d - 1)‖ ≤
          endpointBudget)
    (hvariation :
      (∑ n ∈ Finset.Ico (c + 1) d,
        ‖Complex.realPhase_inverseGeometricDenominator φ n -
          Complex.realPhase_inverseGeometricDenominator φ (n - 1)‖) ≤
          variationBudget) :
    ‖∑ n ∈ Finset.Ico c d,
      Complex.exp (Complex.I * (φ n : ℂ))‖ ≤
        endpointBudget + variationBudget := by
  let z : ℕ → ℂ := fun n => Complex.realPhase_integerUnit φ n
  let q : ℕ → ℂ := fun n => Complex.realPhase_inverseGeometricDenominator φ n
  have hunit :
      ∀ n : ℕ, n ∈ Finset.Icc c d → ‖z n‖ = 1 := by
    intro n _hn
    unfold z
    exact Complex.realPhase_exp_I_norm φ n
  have hstep :
      ∀ n : ℕ,
        n ∈ Finset.Ico c d →
          z n = q n * (z n - z (n + 1)) := by
    intro n hn
    unfold z q Complex.realPhase_inverseGeometricDenominator
      Complex.realPhase_integerUnit
    exact
      (Complex.realPhase_geometricDenominator_inv_mul_step_difference
        φ hlam_pos hsep hn).symm
  have htelescope :
      ‖∑ n ∈ Finset.Ico c d, z n‖ ≤
        ‖q c‖ + ‖q (d - 1)‖ +
          ∑ n ∈ Finset.Ico (c + 1) d, ‖q n - q (n - 1)‖ :=
    Complex.Ico_sum_norm_le_chordAbel_endpoint_add_variation
      z q hunit hstep
  have hvariation :
      (∑ n ∈ Finset.Ico (c + 1) d,
        ‖q n - q (n - 1)‖) ≤
          variationBudget := by
    unfold q
    exact hvariation
  have hendpoint :
      ‖q c‖ + ‖q (d - 1)‖ ≤
        endpointBudget := by
    unfold q
    exact hendpoint
  have htarget :
      ‖q c‖ + ‖q (d - 1)‖ +
          ∑ n ∈ Finset.Ico (c + 1) d, ‖q n - q (n - 1)‖ ≤
        endpointBudget + variationBudget :=
    add_le_add hendpoint hvariation
  have hsum_eq :
      (∑ n ∈ Finset.Ico c d,
        Complex.exp (Complex.I * (φ n : ℂ))) =
        ∑ n ∈ Finset.Ico c d, z n := by
    unfold z Complex.realPhase_integerUnit
    rfl
  exact
    Eq.subst
      (motive := fun s : ℂ =>
        ‖s‖ ≤ endpointBudget + variationBudget)
      hsum_eq.symm
      (le_trans htelescope htarget)

end

end LFunctions
end Boundary
