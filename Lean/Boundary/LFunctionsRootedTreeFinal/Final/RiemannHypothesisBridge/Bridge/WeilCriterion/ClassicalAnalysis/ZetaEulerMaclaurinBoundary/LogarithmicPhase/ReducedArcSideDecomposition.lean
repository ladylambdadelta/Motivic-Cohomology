import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ClassicalAnalysis.ZetaEulerMaclaurinBoundary.LogarithmicPhase.RealPhaseBasics
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ClassicalAnalysis.ZetaEulerMaclaurinBoundary.LogarithmicPhase.InverseChordDerivatives
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Angle
import Mathlib.Data.Complex.ExponentialBounds
import Mathlib.Data.Rat.Cast.Order

/-!
# Logarithmic phase estimates

This file owns the oscillatory phase `n^{-it}` input used by the
Euler-Maclaurin boundary argument.  The phase is logarithmic, not a
constant-ratio geometric progression.
-/

namespace Boundary
namespace LFunctions

noncomputable section
/-- An open natural interval is the corresponding successor-left half-open
interval. -/
theorem Finset.nat_Ioo_eq_Ico_succ_left_for_logarithmicPhase
    (a b : ℕ) :
    Finset.Ioo a b = Finset.Ico (a + 1) b := by
  exact Finset.ext
    (fun n =>
      Iff.intro
        (fun hn =>
          have hbounds : a < n ∧ n < b :=
            Finset.mem_Ioo.mp hn
          Finset.mem_Ico.mpr
            (And.intro
              (Nat.succ_le_of_lt hbounds.1)
              hbounds.2))
        (fun hn =>
          have hbounds : a + 1 ≤ n ∧ n < b :=
            Finset.mem_Ico.mp hn
          Finset.mem_Ioo.mpr
            (And.intro
              (Nat.lt_of_succ_le hbounds.1)
              hbounds.2)))

theorem Nat.mem_Ico_of_mem_Ioo_right
    {a b m n : ℕ}
    (hn : n ∈ Finset.Ioo a m)
    (hm : m ∈ Finset.Icc a b) :
    n ∈ Finset.Ico a b := by
  have hn_bounds : a < n ∧ n < m :=
    Finset.mem_Ioo.mp hn
  have hm_bounds : a ≤ m ∧ m ≤ b :=
    Finset.mem_Icc.mp hm
  have han : a ≤ n :=
    le_of_lt hn_bounds.1
  have hnb : n < b :=
    lt_of_lt_of_le hn_bounds.2 hm_bounds.2
  exact Finset.mem_Ico.mpr ⟨han, hnb⟩

/-- The predecessor of an open summation index belongs to the monotonicity
block. -/
theorem Nat.pred_mem_Ico_of_mem_Ioo_right
    {a b m n : ℕ}
    (hn : n ∈ Finset.Ioo a m)
    (hm : m ∈ Finset.Icc a b) :
    n - 1 ∈ Finset.Ico a b := by
  have hn_bounds : a < n ∧ n < m :=
    Finset.mem_Ioo.mp hn
  have hm_bounds : a ≤ m ∧ m ≤ b :=
    Finset.mem_Icc.mp hm
  have ha_pred : a ≤ n - 1 :=
    Nat.le_pred_of_lt hn_bounds.1
  have hn_pos : 0 < n :=
    lt_of_le_of_lt (Nat.zero_le a) hn_bounds.1
  have hpred_lt_n : n - 1 < n :=
    Nat.pred_lt (Nat.ne_of_gt hn_pos)
  have hpred_lt_b : n - 1 < b :=
    lt_of_lt_of_le (lt_trans hpred_lt_n hn_bounds.2) hm_bounds.2
  exact Finset.mem_Ico.mpr ⟨ha_pred, hpred_lt_b⟩

/-- Monotone real sequences have nonnegative adjacent increments on the open
summation interval. -/
theorem Real.monotoneOn_nat_Ioo_adjacent_sub_nonneg
    (y : ℕ → ℝ)
    {a b m n : ℕ}
    (hn : n ∈ Finset.Ioo a m)
    (hm : m ∈ Finset.Icc a b)
    (hy : MonotoneOn y (Finset.Ico a b : Set ℕ)) :
    0 ≤ y n - y (n - 1) := by
  have hn_mem : n ∈ Finset.Ico a b :=
    Nat.mem_Ico_of_mem_Ioo_right hn hm
  have hpred_mem : n - 1 ∈ Finset.Ico a b :=
    Nat.pred_mem_Ico_of_mem_Ioo_right hn hm
  have hpred_le : n - 1 ≤ n :=
    Nat.sub_le n 1
  have hmono : y (n - 1) ≤ y n :=
    hy hpred_mem hn_mem hpred_le
  exact sub_nonneg.mpr hmono

/-- Antitone real sequences have nonpositive adjacent increments on the open
summation interval. -/
theorem Real.antitoneOn_nat_Ioo_adjacent_sub_nonpos
    (y : ℕ → ℝ)
    {a b m n : ℕ}
    (hn : n ∈ Finset.Ioo a m)
    (hm : m ∈ Finset.Icc a b)
    (hy : AntitoneOn y (Finset.Ico a b : Set ℕ)) :
    y n - y (n - 1) ≤ 0 := by
  have hn_mem : n ∈ Finset.Ico a b :=
    Nat.mem_Ico_of_mem_Ioo_right hn hm
  have hpred_mem : n - 1 ∈ Finset.Ico a b :=
    Nat.pred_mem_Ico_of_mem_Ioo_right hn hm
  have hpred_le : n - 1 ≤ n :=
    Nat.sub_le n 1
  have hanti : y n ≤ y (n - 1) :=
    hy hpred_mem hn_mem hpred_le
  exact sub_nonpos.mpr hanti

/-- Norm of an adjacent increment for a monotone real sequence. -/
theorem Real.monotoneOn_nat_Ioo_adjacent_norm_eq_sub
    (y : ℕ → ℝ)
    {a b m n : ℕ}
    (hn : n ∈ Finset.Ioo a m)
    (hm : m ∈ Finset.Icc a b)
    (hy : MonotoneOn y (Finset.Ico a b : Set ℕ)) :
    ‖y n - y (n - 1)‖ = y n - y (n - 1) := by
  have hnonneg : 0 ≤ y n - y (n - 1) :=
    Real.monotoneOn_nat_Ioo_adjacent_sub_nonneg y hn hm hy
  calc
    ‖y n - y (n - 1)‖ = |y n - y (n - 1)| :=
      Real.norm_eq_abs (y n - y (n - 1))
    _ = y n - y (n - 1) :=
      abs_of_nonneg hnonneg

/-- Norm of an adjacent increment for an antitone real sequence. -/
theorem Real.antitoneOn_nat_Ioo_adjacent_norm_eq_sub_rev
    (y : ℕ → ℝ)
    {a b m n : ℕ}
    (hn : n ∈ Finset.Ioo a m)
    (hm : m ∈ Finset.Icc a b)
    (hy : AntitoneOn y (Finset.Ico a b : Set ℕ)) :
    ‖y n - y (n - 1)‖ = y (n - 1) - y n := by
  have hnonpos : y n - y (n - 1) ≤ 0 :=
    Real.antitoneOn_nat_Ioo_adjacent_sub_nonpos y hn hm hy
  calc
    ‖y n - y (n - 1)‖ = |y n - y (n - 1)| :=
      Real.norm_eq_abs (y n - y (n - 1))
    _ = -(y n - y (n - 1)) :=
      abs_of_nonpos hnonpos
    _ = y (n - 1) - y n :=
      neg_sub (y n) (y (n - 1))

/-- Adjacent reduced inverse-denominator differences are controlled exactly by
the adjacent imaginary-coordinate difference. -/
theorem Complex.reducedArc_inverseGeometricDenominator_adjacent_norm_eq_imCoord
    (ψ : ℕ → ℝ)
    {n : ℕ}
    (hn_mem : ψ n ∈ Set.Ioc (-Real.pi) Real.pi)
    (hpred_mem : ψ (n - 1) ∈ Set.Ioc (-Real.pi) Real.pi)
    (hn_ne : ψ n ≠ 0)
    (hpred_ne : ψ (n - 1) ≠ 0) :
    ‖Complex.reducedArc_inverseGeometricDenominator (ψ n) -
      Complex.reducedArc_inverseGeometricDenominator (ψ (n - 1))‖ =
    ‖Complex.reducedArc_inverseGeometricDenominator_imCoord (ψ n) -
      Complex.reducedArc_inverseGeometricDenominator_imCoord (ψ (n - 1))‖ := by
  exact
    Complex.reducedArc_inverseGeometricDenominator_sub_norm_eq_imCoord
      hn_mem hpred_mem hn_ne hpred_ne

/-- A one-sided reduced-arc membership hypothesis implies membership in the
full reduced arc. -/
theorem Real.mem_reducedArc_of_mem_oneSided_reducedArc
    {ψ L U : ℝ}
    (hside : L = (0 : ℝ) ∧ U = Real.pi ∨
      L = -Real.pi ∧ U = (0 : ℝ))
    (hψ : ψ ∈ Set.Ioc L U) :
    ψ ∈ Set.Ioc (-Real.pi) Real.pi := by
  match hside with
  | Or.inl hpos =>
      have hψ_pos : ψ ∈ Set.Ioc (0 : ℝ) Real.pi :=
        Eq.subst
          (motive := fun l : ℝ => ψ ∈ Set.Ioc l Real.pi)
          hpos.1
          (Eq.subst
            (motive := fun u : ℝ => ψ ∈ Set.Ioc L u)
            hpos.2
            hψ)
      exact
        ⟨lt_trans (neg_lt_zero.mpr Real.pi_pos) hψ_pos.1, hψ_pos.2⟩
  | Or.inr hneg =>
      have hψ_neg : ψ ∈ Set.Ioc (-Real.pi) (0 : ℝ) :=
        Eq.subst
          (motive := fun l : ℝ => ψ ∈ Set.Ioc l (0 : ℝ))
          hneg.1
          (Eq.subst
            (motive := fun u : ℝ => ψ ∈ Set.Ioc L u)
            hneg.2
            hψ)
      have hψ_lt_pi : ψ < Real.pi :=
        lt_of_le_of_lt hψ_neg.2 Real.pi_pos
      exact
        ⟨hψ_neg.1, le_of_lt hψ_lt_pi⟩

/-- Positive lower bound for the norm excludes zero. -/
theorem Real.ne_zero_of_pos_le_norm
    {lam x : ℝ}
    (hlam_pos : 0 < lam)
    (hx : lam ≤ ‖x‖) :
    x ≠ 0 := by
  intro hx_zero
  have hnorm_zero_raw : ‖x‖ = ‖(0 : ℝ)‖ :=
    congrArg norm hx_zero
  have hnorm_zero_target : ‖(0 : ℝ)‖ = 0 :=
    norm_zero
  have hnorm_zero : ‖x‖ = 0 :=
    Eq.trans hnorm_zero_raw hnorm_zero_target
  have hlam_le_zero : lam ≤ 0 :=
    Eq.subst
      (motive := fun r : ℝ => lam ≤ r)
      hnorm_zero
      hx
  exact (not_le_of_gt hlam_pos) hlam_le_zero

/-- One-sided separated reduced-arc data gives nonzero membership in the full
reduced arc at an index. -/
theorem Real.oneSided_reducedArc_mem_and_ne_of_sep
    (ψ : ℕ → ℝ)
    {a b n : ℕ}
    {lam L U : ℝ}
    (hlam_pos : 0 < lam)
    (hside : L = (0 : ℝ) ∧ U = Real.pi ∨
      L = -Real.pi ∧ U = (0 : ℝ))
    (hn : n ∈ Finset.Ico a b)
    (hψ_mem :
      ∀ k : ℕ,
        k ∈ Finset.Ico a b →
          ψ k ∈ Set.Ioc L U)
    (hψ_sep :
      ∀ k : ℕ,
        k ∈ Finset.Ico a b →
          lam ≤ ‖ψ k‖) :
    ψ n ∈ Set.Ioc (-Real.pi) Real.pi ∧ ψ n ≠ 0 := by
  have hmem_side : ψ n ∈ Set.Ioc L U :=
    hψ_mem n hn
  have hmem : ψ n ∈ Set.Ioc (-Real.pi) Real.pi :=
    Real.mem_reducedArc_of_mem_oneSided_reducedArc hside hmem_side
  have hne : ψ n ≠ 0 :=
    Real.ne_zero_of_pos_le_norm hlam_pos (hψ_sep n hn)
  exact ⟨hmem, hne⟩

/-- Membership in the positive one-sided reduced arc after substituting the
recorded side endpoints. -/
theorem Real.mem_Ioc_zero_pi_of_mem_pos_side
    {ψ L U : ℝ}
    (hpos : L = (0 : ℝ) ∧ U = Real.pi)
    (hψ : ψ ∈ Set.Ioc L U) :
    ψ ∈ Set.Ioc (0 : ℝ) Real.pi :=
  Eq.subst
    (motive := fun l : ℝ => ψ ∈ Set.Ioc l Real.pi)
    hpos.1
    (Eq.subst
      (motive := fun u : ℝ => ψ ∈ Set.Ioc L u)
      hpos.2
      hψ)

/-- Membership in the negative one-sided reduced arc after substituting the
recorded side endpoints. -/
theorem Real.mem_Ioc_neg_pi_zero_of_mem_neg_side
    {ψ L U : ℝ}
    (hneg : L = -Real.pi ∧ U = (0 : ℝ))
    (hψ : ψ ∈ Set.Ioc L U) :
    ψ ∈ Set.Ioc (-Real.pi) (0 : ℝ) :=
  Eq.subst
    (motive := fun l : ℝ => ψ ∈ Set.Ioc l (0 : ℝ))
    hneg.1
    (Eq.subst
      (motive := fun u : ℝ => ψ ∈ Set.Ioc L u)
      hneg.2
      hψ)

/-- Negative-side membership plus separation from zero gives strict membership
in the open negative side. -/
theorem Real.mem_Ioo_neg_pi_zero_of_mem_neg_side_sep
    {ψ L U lam : ℝ}
    (hlam_pos : 0 < lam)
    (hneg : L = -Real.pi ∧ U = (0 : ℝ))
    (hψ : ψ ∈ Set.Ioc L U)
    (hsep : lam ≤ ‖ψ‖) :
    ψ ∈ Set.Ioo (-Real.pi) (0 : ℝ) := by
  have hψ_neg : ψ ∈ Set.Ioc (-Real.pi) (0 : ℝ) :=
    Real.mem_Ioc_neg_pi_zero_of_mem_neg_side hneg hψ
  have hne : ψ ≠ 0 :=
    Real.ne_zero_of_pos_le_norm hlam_pos hsep
  have hlt_zero : ψ < 0 :=
    lt_of_le_of_ne hψ_neg.2 hne
  exact ⟨hψ_neg.1, hlt_zero⟩

/-- A point in the reduced arc separated from zero lies on exactly one side of
the singularity. -/
theorem Real.mem_neg_side_or_pos_side_of_mem_reducedArc_sep
    {ψ lam : ℝ}
    (hlam_pos : 0 < lam)
    (hψ_mem : ψ ∈ Set.Ioc (-Real.pi) Real.pi)
    (hψ_sep : lam ≤ ‖ψ‖) :
    ψ ∈ Set.Ioo (-Real.pi) (0 : ℝ) ∨
      ψ ∈ Set.Ioc (0 : ℝ) Real.pi := by
  have hψ_ne : ψ ≠ 0 :=
    Real.ne_zero_of_pos_le_norm hlam_pos hψ_sep
  match lt_or_gt_of_ne hψ_ne with
  | Or.inl hψ_lt_zero =>
      exact Or.inl ⟨hψ_mem.1, hψ_lt_zero⟩
  | Or.inr hψ_pos =>
      exact Or.inr ⟨hψ_pos, hψ_mem.2⟩

/-- On a separated reduced arc, failure of negative-side membership forces
positive-side membership. -/
theorem Real.mem_pos_side_of_not_mem_neg_side_of_mem_reducedArc_sep
    {ψ lam : ℝ}
    (hlam_pos : 0 < lam)
    (hψ_mem : ψ ∈ Set.Ioc (-Real.pi) Real.pi)
    (hψ_sep : lam ≤ ‖ψ‖)
    (hψ_not_neg : ¬ ψ ∈ Set.Ioc (-Real.pi) (0 : ℝ)) :
    ψ ∈ Set.Ioc (0 : ℝ) Real.pi := by
  have hcases :
      ψ ∈ Set.Ioo (-Real.pi) (0 : ℝ) ∨
        ψ ∈ Set.Ioc (0 : ℝ) Real.pi :=
    Real.mem_neg_side_or_pos_side_of_mem_reducedArc_sep
      hlam_pos hψ_mem hψ_sep
  match hcases with
  | Or.inl hneg =>
      have hneg_ioc : ψ ∈ Set.Ioc (-Real.pi) (0 : ℝ) :=
        ⟨hneg.1, hneg.2.le⟩
      exact False.elim (hψ_not_neg hneg_ioc)
  | Or.inr hpos =>
      exact hpos

/-- On a separated reduced arc, failure of positive-side membership forces
negative-side membership. -/
theorem Real.mem_neg_side_of_not_mem_pos_side_of_mem_reducedArc_sep
    {ψ lam : ℝ}
    (hlam_pos : 0 < lam)
    (hψ_mem : ψ ∈ Set.Ioc (-Real.pi) Real.pi)
    (hψ_sep : lam ≤ ‖ψ‖)
    (hψ_not_pos : ¬ ψ ∈ Set.Ioc (0 : ℝ) Real.pi) :
    ψ ∈ Set.Ioc (-Real.pi) (0 : ℝ) := by
  have hcases :
      ψ ∈ Set.Ioo (-Real.pi) (0 : ℝ) ∨
        ψ ∈ Set.Ioc (0 : ℝ) Real.pi :=
    Real.mem_neg_side_or_pos_side_of_mem_reducedArc_sep
      hlam_pos hψ_mem hψ_sep
  match hcases with
  | Or.inl hneg =>
      exact ⟨hneg.1, hneg.2.le⟩
  | Or.inr hpos =>
      exact False.elim (hψ_not_pos hpos)

/-- Sign-side dichotomy for a separated reduced-arc sequence at an index. -/
theorem Real.sequence_mem_neg_side_or_pos_side_of_mem_reducedArc_sep
    (ψ : ℕ → ℝ)
    {a b n : ℕ}
    {lam : ℝ}
    (hlam_pos : 0 < lam)
    (hn : n ∈ Finset.Ico a b)
    (hψ_mem :
      ∀ k : ℕ,
        k ∈ Finset.Ico a b →
          ψ k ∈ Set.Ioc (-Real.pi) Real.pi)
    (hψ_sep :
      ∀ k : ℕ,
        k ∈ Finset.Ico a b →
          lam ≤ ‖ψ k‖) :
    ψ n ∈ Set.Ioo (-Real.pi) (0 : ℝ) ∨
      ψ n ∈ Set.Ioc (0 : ℝ) Real.pi :=
  Real.mem_neg_side_or_pos_side_of_mem_reducedArc_sep
    hlam_pos (hψ_mem n hn) (hψ_sep n hn)

/-- Adjacent separated reduced-arc samples are classified by their signs. -/
theorem Real.adjacent_mem_side_cases_of_mem_Ioo_sep
    (ψ : ℕ → ℝ)
    {a b m n : ℕ}
    {lam : ℝ}
    (hlam_pos : 0 < lam)
    (hn : n ∈ Finset.Ioo a m)
    (hm : m ∈ Finset.Icc a b)
    (hψ_mem :
      ∀ k : ℕ,
        k ∈ Finset.Ico a b →
          ψ k ∈ Set.Ioc (-Real.pi) Real.pi)
    (hψ_sep :
      ∀ k : ℕ,
        k ∈ Finset.Ico a b →
          lam ≤ ‖ψ k‖) :
    (ψ (n - 1) ∈ Set.Ioo (-Real.pi) (0 : ℝ) ∧
        ψ n ∈ Set.Ioo (-Real.pi) (0 : ℝ)) ∨
      (ψ (n - 1) ∈ Set.Ioc (0 : ℝ) Real.pi ∧
        ψ n ∈ Set.Ioc (0 : ℝ) Real.pi) ∨
      (ψ (n - 1) ∈ Set.Ioo (-Real.pi) (0 : ℝ) ∧
        ψ n ∈ Set.Ioc (0 : ℝ) Real.pi) ∨
      (ψ (n - 1) ∈ Set.Ioc (0 : ℝ) Real.pi ∧
        ψ n ∈ Set.Ioo (-Real.pi) (0 : ℝ)) := by
  have hn_mem : n ∈ Finset.Ico a b :=
    Nat.mem_Ico_of_mem_Ioo_right hn hm
  have hpred_mem : n - 1 ∈ Finset.Ico a b :=
    Nat.pred_mem_Ico_of_mem_Ioo_right hn hm
  have hn_side :
      ψ n ∈ Set.Ioo (-Real.pi) (0 : ℝ) ∨
        ψ n ∈ Set.Ioc (0 : ℝ) Real.pi :=
    Real.sequence_mem_neg_side_or_pos_side_of_mem_reducedArc_sep
      ψ hlam_pos hn_mem hψ_mem hψ_sep
  have hpred_side :
      ψ (n - 1) ∈ Set.Ioo (-Real.pi) (0 : ℝ) ∨
        ψ (n - 1) ∈ Set.Ioc (0 : ℝ) Real.pi :=
    Real.sequence_mem_neg_side_or_pos_side_of_mem_reducedArc_sep
      ψ hlam_pos hpred_mem hψ_mem hψ_sep
  match hpred_side with
  | Or.inl hpred_neg =>
      match hn_side with
      | Or.inl hn_neg =>
          exact Or.inl ⟨hpred_neg, hn_neg⟩
      | Or.inr hn_pos =>
          exact Or.inr (Or.inr (Or.inl ⟨hpred_neg, hn_pos⟩))
  | Or.inr hpred_pos =>
      match hn_side with
      | Or.inl hn_neg =>
          exact Or.inr (Or.inr (Or.inr ⟨hpred_pos, hn_neg⟩))
      | Or.inr hn_pos =>
          exact Or.inr (Or.inl ⟨hpred_pos, hn_pos⟩)

/-- A monotone sequence cannot move from the positive side to the negative side
across one adjacent step. -/
theorem Real.monotoneOn_forbids_adjacent_pos_to_neg
    (ψ : ℕ → ℝ)
    {a b m n : ℕ}
    (hn : n ∈ Finset.Ioo a m)
    (hm : m ∈ Finset.Icc a b)
    (hψ_mono : MonotoneOn ψ (Finset.Ico a b : Set ℕ))
    (hpred_pos : ψ (n - 1) ∈ Set.Ioc (0 : ℝ) Real.pi)
    (hn_neg : ψ n ∈ Set.Ioo (-Real.pi) (0 : ℝ)) :
    False := by
  have hn_mem : n ∈ Finset.Ico a b :=
    Nat.mem_Ico_of_mem_Ioo_right hn hm
  have hpred_mem : n - 1 ∈ Finset.Ico a b :=
    Nat.pred_mem_Ico_of_mem_Ioo_right hn hm
  have hpred_le_n : n - 1 ≤ n :=
    Nat.sub_le n 1
  have hmono_step : ψ (n - 1) ≤ ψ n :=
    hψ_mono hpred_mem hn_mem hpred_le_n
  have hzero_lt_n : 0 < ψ n :=
    lt_of_lt_of_le hpred_pos.1 hmono_step
  exact (not_lt_of_ge hn_neg.2.le) hzero_lt_n

/-- An antitone sequence cannot move from the negative side to the positive side
across one adjacent step. -/
theorem Real.antitoneOn_forbids_adjacent_neg_to_pos
    (ψ : ℕ → ℝ)
    {a b m n : ℕ}
    (hn : n ∈ Finset.Ioo a m)
    (hm : m ∈ Finset.Icc a b)
    (hψ_anti : AntitoneOn ψ (Finset.Ico a b : Set ℕ))
    (hpred_neg : ψ (n - 1) ∈ Set.Ioo (-Real.pi) (0 : ℝ))
    (hn_pos : ψ n ∈ Set.Ioc (0 : ℝ) Real.pi) :
    False := by
  have hn_mem : n ∈ Finset.Ico a b :=
    Nat.mem_Ico_of_mem_Ioo_right hn hm
  have hpred_mem : n - 1 ∈ Finset.Ico a b :=
    Nat.pred_mem_Ico_of_mem_Ioo_right hn hm
  have hpred_le_n : n - 1 ≤ n :=
    Nat.sub_le n 1
  have hanti_step : ψ n ≤ ψ (n - 1) :=
    hψ_anti hpred_mem hn_mem hpred_le_n
  have hzero_lt_pred : 0 < ψ (n - 1) :=
    lt_of_lt_of_le hn_pos.1 hanti_step
  exact (not_lt_of_ge hpred_neg.2.le) hzero_lt_pred

/-- Adjacent side classification for a monotone sequence: same-side or
negative-to-positive crossing. -/
theorem Real.monotoneOn_adjacent_side_cases_of_mem_Ioo_sep
    (ψ : ℕ → ℝ)
    {a b m n : ℕ}
    {lam : ℝ}
    (hlam_pos : 0 < lam)
    (hn : n ∈ Finset.Ioo a m)
    (hm : m ∈ Finset.Icc a b)
    (hψ_mem :
      ∀ k : ℕ,
        k ∈ Finset.Ico a b →
          ψ k ∈ Set.Ioc (-Real.pi) Real.pi)
    (hψ_mono : MonotoneOn ψ (Finset.Ico a b : Set ℕ))
    (hψ_sep :
      ∀ k : ℕ,
        k ∈ Finset.Ico a b →
          lam ≤ ‖ψ k‖) :
    (ψ (n - 1) ∈ Set.Ioo (-Real.pi) (0 : ℝ) ∧
        ψ n ∈ Set.Ioo (-Real.pi) (0 : ℝ)) ∨
      (ψ (n - 1) ∈ Set.Ioc (0 : ℝ) Real.pi ∧
        ψ n ∈ Set.Ioc (0 : ℝ) Real.pi) ∨
      (ψ (n - 1) ∈ Set.Ioo (-Real.pi) (0 : ℝ) ∧
        ψ n ∈ Set.Ioc (0 : ℝ) Real.pi) := by
  have hcases :=
    Real.adjacent_mem_side_cases_of_mem_Ioo_sep
      ψ hlam_pos hn hm hψ_mem hψ_sep
  match hcases with
  | Or.inl hneg_neg =>
      exact Or.inl hneg_neg
  | Or.inr hrest =>
      match hrest with
      | Or.inl hpos_pos =>
          exact Or.inr (Or.inl hpos_pos)
      | Or.inr hcross =>
          match hcross with
          | Or.inl hneg_pos =>
              exact Or.inr (Or.inr hneg_pos)
          | Or.inr hpos_neg =>
              exact False.elim
                (Real.monotoneOn_forbids_adjacent_pos_to_neg
                  ψ hn hm hψ_mono hpos_neg.1 hpos_neg.2)

/-- Adjacent side classification for an antitone sequence: same-side or
positive-to-negative crossing. -/
theorem Real.antitoneOn_adjacent_side_cases_of_mem_Ioo_sep
    (ψ : ℕ → ℝ)
    {a b m n : ℕ}
    {lam : ℝ}
    (hlam_pos : 0 < lam)
    (hn : n ∈ Finset.Ioo a m)
    (hm : m ∈ Finset.Icc a b)
    (hψ_mem :
      ∀ k : ℕ,
        k ∈ Finset.Ico a b →
          ψ k ∈ Set.Ioc (-Real.pi) Real.pi)
    (hψ_anti : AntitoneOn ψ (Finset.Ico a b : Set ℕ))
    (hψ_sep :
      ∀ k : ℕ,
        k ∈ Finset.Ico a b →
          lam ≤ ‖ψ k‖) :
    (ψ (n - 1) ∈ Set.Ioo (-Real.pi) (0 : ℝ) ∧
        ψ n ∈ Set.Ioo (-Real.pi) (0 : ℝ)) ∨
      (ψ (n - 1) ∈ Set.Ioc (0 : ℝ) Real.pi ∧
        ψ n ∈ Set.Ioc (0 : ℝ) Real.pi) ∨
      (ψ (n - 1) ∈ Set.Ioc (0 : ℝ) Real.pi ∧
        ψ n ∈ Set.Ioo (-Real.pi) (0 : ℝ)) := by
  have hcases :=
    Real.adjacent_mem_side_cases_of_mem_Ioo_sep
      ψ hlam_pos hn hm hψ_mem hψ_sep
  match hcases with
  | Or.inl hneg_neg =>
      exact Or.inl hneg_neg
  | Or.inr hrest =>
      match hrest with
      | Or.inl hpos_pos =>
          exact Or.inr (Or.inl hpos_pos)
      | Or.inr hcross =>
          match hcross with
          | Or.inl hneg_pos =>
              exact False.elim
                (Real.antitoneOn_forbids_adjacent_neg_to_pos
                  ψ hn hm hψ_anti hneg_pos.1 hneg_pos.2)
          | Or.inr hpos_neg =>
              exact Or.inr (Or.inr hpos_neg)

/-- A monotone separated sequence has at most one negative-to-positive adjacent
crossing. -/
theorem Real.monotoneOn_forbids_two_adjacent_neg_to_pos_crossings
    (ψ : ℕ → ℝ)
    {a b m i j : ℕ}
    (hi : i ∈ Finset.Ioo a m)
    (hj : j ∈ Finset.Ioo a m)
    (hm : m ∈ Finset.Icc a b)
    (hij : i < j)
    (hψ_mono : MonotoneOn ψ (Finset.Ico a b : Set ℕ))
    (hi_cross :
      ψ (i - 1) ∈ Set.Ioo (-Real.pi) (0 : ℝ) ∧
        ψ i ∈ Set.Ioc (0 : ℝ) Real.pi)
    (hj_cross :
      ψ (j - 1) ∈ Set.Ioo (-Real.pi) (0 : ℝ) ∧
        ψ j ∈ Set.Ioc (0 : ℝ) Real.pi) :
    False := by
  have hi_mem : i ∈ Finset.Ico a b :=
    Nat.mem_Ico_of_mem_Ioo_right hi hm
  have hj_pred_mem : j - 1 ∈ Finset.Ico a b :=
    Nat.pred_mem_Ico_of_mem_Ioo_right hj hm
  have hi_le_jpred : i ≤ j - 1 :=
    Nat.le_pred_of_lt hij
  have hmono_step : ψ i ≤ ψ (j - 1) :=
    hψ_mono hi_mem hj_pred_mem hi_le_jpred
  have hzero_lt_jpred : 0 < ψ (j - 1) :=
    lt_of_lt_of_le hi_cross.2.1 hmono_step
  exact (not_lt_of_ge hj_cross.1.2.le) hzero_lt_jpred

/-- An antitone separated sequence has at most one positive-to-negative adjacent
crossing. -/
theorem Real.antitoneOn_forbids_two_adjacent_pos_to_neg_crossings
    (ψ : ℕ → ℝ)
    {a b m i j : ℕ}
    (hi : i ∈ Finset.Ioo a m)
    (hj : j ∈ Finset.Ioo a m)
    (hm : m ∈ Finset.Icc a b)
    (hij : i < j)
    (hψ_anti : AntitoneOn ψ (Finset.Ico a b : Set ℕ))
    (hi_cross :
      ψ (i - 1) ∈ Set.Ioc (0 : ℝ) Real.pi ∧
        ψ i ∈ Set.Ioo (-Real.pi) (0 : ℝ))
    (hj_cross :
      ψ (j - 1) ∈ Set.Ioc (0 : ℝ) Real.pi ∧
        ψ j ∈ Set.Ioo (-Real.pi) (0 : ℝ)) :
    False := by
  have hi_mem : i ∈ Finset.Ico a b :=
    Nat.mem_Ico_of_mem_Ioo_right hi hm
  have hj_pred_mem : j - 1 ∈ Finset.Ico a b :=
    Nat.pred_mem_Ico_of_mem_Ioo_right hj hm
  have hi_le_jpred : i ≤ j - 1 :=
    Nat.le_pred_of_lt hij
  have hanti_step : ψ (j - 1) ≤ ψ i :=
    hψ_anti hi_mem hj_pred_mem hi_le_jpred
  have hzero_lt_i : 0 < ψ i :=
    lt_of_lt_of_le hj_cross.1.1 hanti_step
  exact (not_lt_of_ge hi_cross.2.2.le) hzero_lt_i

/-- Negative-to-positive adjacent crossing predicate. -/
def Real.adjacentNegToPosCrossing
    (ψ : ℕ → ℝ)
    (n : ℕ) : Prop :=
  ψ (n - 1) ∈ Set.Ioo (-Real.pi) (0 : ℝ) ∧
    ψ n ∈ Set.Ioc (0 : ℝ) Real.pi

/-- Positive-to-negative adjacent crossing predicate. -/
def Real.adjacentPosToNegCrossing
    (ψ : ℕ → ℝ)
    (n : ℕ) : Prop :=
  ψ (n - 1) ∈ Set.Ioc (0 : ℝ) Real.pi ∧
    ψ n ∈ Set.Ioo (-Real.pi) (0 : ℝ)

/-- The expanded form of `adjacentNegToPosCrossing`. -/
theorem Real.adjacentNegToPosCrossing_iff
    (ψ : ℕ → ℝ)
    (n : ℕ) :
    Real.adjacentNegToPosCrossing ψ n ↔
      ψ (n - 1) ∈ Set.Ioo (-Real.pi) (0 : ℝ) ∧
        ψ n ∈ Set.Ioc (0 : ℝ) Real.pi :=
  Iff.rfl

/-- The expanded form of `adjacentPosToNegCrossing`. -/
theorem Real.adjacentPosToNegCrossing_iff
    (ψ : ℕ → ℝ)
    (n : ℕ) :
    Real.adjacentPosToNegCrossing ψ n ↔
      ψ (n - 1) ∈ Set.Ioc (0 : ℝ) Real.pi ∧
        ψ n ∈ Set.Ioo (-Real.pi) (0 : ℝ) :=
  Iff.rfl

/-- Monotone negative-to-positive crossings are unique on the summation
interval. -/
theorem Real.monotoneOn_adjacentNegToPosCrossing_subsingleton
    (ψ : ℕ → ℝ)
    {a b m : ℕ}
    (hm : m ∈ Finset.Icc a b)
    (hψ_mono : MonotoneOn ψ (Finset.Ico a b : Set ℕ)) :
    Set.Subsingleton
      {n : ℕ |
        n ∈ (Finset.Ioo a m : Set ℕ) ∧
          Real.adjacentNegToPosCrossing ψ n} := by
  intro i hi j hj
  have hi_mem : i ∈ Finset.Ioo a m :=
    hi.1
  have hj_mem : j ∈ Finset.Ioo a m :=
    hj.1
  have hi_cross :
      ψ (i - 1) ∈ Set.Ioo (-Real.pi) (0 : ℝ) ∧
        ψ i ∈ Set.Ioc (0 : ℝ) Real.pi :=
    hi.2
  have hj_cross :
      ψ (j - 1) ∈ Set.Ioo (-Real.pi) (0 : ℝ) ∧
        ψ j ∈ Set.Ioc (0 : ℝ) Real.pi :=
    hj.2
  match lt_trichotomy i j with
  | Or.inl hij =>
      exact False.elim
        (Real.monotoneOn_forbids_two_adjacent_neg_to_pos_crossings
          ψ hi_mem hj_mem hm hij hψ_mono hi_cross hj_cross)
  | Or.inr hge =>
      match hge with
      | Or.inl hij =>
          exact hij
      | Or.inr hji =>
          exact Eq.symm
            (False.elim
              (Real.monotoneOn_forbids_two_adjacent_neg_to_pos_crossings
                ψ hj_mem hi_mem hm hji hψ_mono hj_cross hi_cross))

/-- Antitone positive-to-negative crossings are unique on the summation
interval. -/
theorem Real.antitoneOn_adjacentPosToNegCrossing_subsingleton
    (ψ : ℕ → ℝ)
    {a b m : ℕ}
    (hm : m ∈ Finset.Icc a b)
    (hψ_anti : AntitoneOn ψ (Finset.Ico a b : Set ℕ)) :
    Set.Subsingleton
      {n : ℕ |
        n ∈ (Finset.Ioo a m : Set ℕ) ∧
          Real.adjacentPosToNegCrossing ψ n} := by
  intro i hi j hj
  have hi_mem : i ∈ Finset.Ioo a m :=
    hi.1
  have hj_mem : j ∈ Finset.Ioo a m :=
    hj.1
  have hi_cross :
      ψ (i - 1) ∈ Set.Ioc (0 : ℝ) Real.pi ∧
        ψ i ∈ Set.Ioo (-Real.pi) (0 : ℝ) :=
    hi.2
  have hj_cross :
      ψ (j - 1) ∈ Set.Ioc (0 : ℝ) Real.pi ∧
        ψ j ∈ Set.Ioo (-Real.pi) (0 : ℝ) :=
    hj.2
  match lt_trichotomy i j with
  | Or.inl hij =>
      exact False.elim
        (Real.antitoneOn_forbids_two_adjacent_pos_to_neg_crossings
          ψ hi_mem hj_mem hm hij hψ_anti hi_cross hj_cross)
  | Or.inr hge =>
      match hge with
      | Or.inl hij =>
          exact hij
      | Or.inr hji =>
          exact Eq.symm
            (False.elim
              (Real.antitoneOn_forbids_two_adjacent_pos_to_neg_crossings
                ψ hj_mem hi_mem hm hji hψ_anti hj_cross hi_cross))

/-- A monotone separated reduced sequence is either entirely on one side on
`Ico a m`, or it has a first positive index giving a negative block followed by
a positive block. -/
theorem Real.monotoneOn_reducedArc_side_decomposition
    (ψ : ℕ → ℝ)
    {a b m : ℕ}
    {lam : ℝ}
    [∀ n : ℕ, Decidable (ψ n ∈ Set.Ioc (0 : ℝ) Real.pi)]
    (hm : m ∈ Finset.Icc a b)
    (hlam_pos : 0 < lam)
    (hψ_mem :
      ∀ n : ℕ,
        n ∈ Finset.Ico a b →
          ψ n ∈ Set.Ioc (-Real.pi) Real.pi)
    (hψ_mono : MonotoneOn ψ (Finset.Ico a b : Set ℕ))
    (hψ_sep :
      ∀ n : ℕ,
        n ∈ Finset.Ico a b →
          lam ≤ ‖ψ n‖) :
    (∀ n : ℕ,
        n ∈ Finset.Ico a m →
          ψ n ∈ Set.Ioc (-Real.pi) (0 : ℝ)) ∨
      (∀ n : ℕ,
        n ∈ Finset.Ico a m →
          ψ n ∈ Set.Ioc (0 : ℝ) Real.pi) ∨
      ∃ c : ℕ,
        a < c ∧ c < m ∧
          (∀ n : ℕ,
            n ∈ Finset.Ico a c →
              ψ n ∈ Set.Ioc (-Real.pi) (0 : ℝ)) ∧
          (∀ n : ℕ,
            n ∈ Finset.Ico c m →
              ψ n ∈ Set.Ioc (0 : ℝ) Real.pi) := by
  let positives : Finset ℕ :=
    (Finset.Ico a m).filter
      (fun n : ℕ => ψ n ∈ Set.Ioc (0 : ℝ) Real.pi)
  have hm_bounds : a ≤ m ∧ m ≤ b :=
    Finset.mem_Icc.mp hm
  by_cases hpos_nonempty : positives.Nonempty
  · let c : ℕ := positives.min' hpos_nonempty
    have hc_filter : c ∈ positives :=
      Finset.min'_mem positives hpos_nonempty
    have hc_data :
        c ∈ Finset.Ico a m ∧
          ψ c ∈ Set.Ioc (0 : ℝ) Real.pi :=
      Finset.mem_filter.mp hc_filter
    have hc_bounds : a ≤ c ∧ c < m :=
      Finset.mem_Ico.mp hc_data.1
    by_cases hca : c = a
    · exact Or.inr (Or.inl
        (fun n hn =>
          let hn_bounds : a ≤ n ∧ n < m := Finset.mem_Ico.mp hn
          let hn_mem_original : n ∈ Finset.Ico a b :=
            Finset.mem_Ico.mpr
              ⟨hn_bounds.1, lt_of_lt_of_le hn_bounds.2 hm_bounds.2⟩
          let hc_mem_original : c ∈ Finset.Ico a b :=
            Finset.mem_Ico.mpr
              ⟨hc_bounds.1, lt_of_lt_of_le hc_bounds.2 hm_bounds.2⟩
          let hc_le_n : c ≤ n :=
            Eq.subst
              (motive := fun r : ℕ => r ≤ n)
              hca.symm
              hn_bounds.1
          let hmono_step : ψ c ≤ ψ n :=
            hψ_mono hc_mem_original hn_mem_original hc_le_n
          ⟨lt_of_lt_of_le hc_data.2.1 hmono_step,
            (hψ_mem n hn_mem_original).2⟩))
    · have hac : a < c :=
        lt_of_le_of_ne hc_bounds.1 (Ne.symm hca)
      exact Or.inr (Or.inr
        ⟨c, hac, hc_bounds.2,
          (fun n hn =>
            let hn_bounds : a ≤ n ∧ n < c := Finset.mem_Ico.mp hn
            let hn_mem_am : n ∈ Finset.Ico a m :=
              Finset.mem_Ico.mpr
                ⟨hn_bounds.1, lt_trans hn_bounds.2 hc_bounds.2⟩
            let hn_mem_original : n ∈ Finset.Ico a b :=
              Finset.mem_Ico.mpr
                ⟨hn_bounds.1,
                  lt_of_lt_of_le (lt_trans hn_bounds.2 hc_bounds.2)
                    hm_bounds.2⟩
            let hnot_pos :
                ¬ ψ n ∈ Set.Ioc (0 : ℝ) Real.pi :=
              fun hn_pos =>
                let hn_filter : n ∈ positives :=
                  Finset.mem_filter.mpr ⟨hn_mem_am, hn_pos⟩
                let hc_le_n : c ≤ n :=
                  Finset.min'_le positives n hn_filter
                (not_lt_of_ge hc_le_n) hn_bounds.2
            Real.mem_neg_side_of_not_mem_pos_side_of_mem_reducedArc_sep
              hlam_pos (hψ_mem n hn_mem_original)
              (hψ_sep n hn_mem_original) hnot_pos),
          (fun n hn =>
            let hn_bounds : c ≤ n ∧ n < m := Finset.mem_Ico.mp hn
            let hn_mem_original : n ∈ Finset.Ico a b :=
              Finset.mem_Ico.mpr
                ⟨le_trans hc_bounds.1 hn_bounds.1,
                  lt_of_lt_of_le hn_bounds.2 hm_bounds.2⟩
            let hc_mem_original : c ∈ Finset.Ico a b :=
              Finset.mem_Ico.mpr
                ⟨hc_bounds.1, lt_of_lt_of_le hc_bounds.2 hm_bounds.2⟩
            let hmono_step : ψ c ≤ ψ n :=
              hψ_mono hc_mem_original hn_mem_original hn_bounds.1
            ⟨lt_of_lt_of_le hc_data.2.1 hmono_step,
              (hψ_mem n hn_mem_original).2⟩)⟩)
  · exact Or.inl
      (fun n hn =>
        let hn_bounds : a ≤ n ∧ n < m := Finset.mem_Ico.mp hn
        let hn_mem_original : n ∈ Finset.Ico a b :=
          Finset.mem_Ico.mpr
            ⟨hn_bounds.1, lt_of_lt_of_le hn_bounds.2 hm_bounds.2⟩
        let hnot_pos :
            ¬ ψ n ∈ Set.Ioc (0 : ℝ) Real.pi :=
          fun hn_pos =>
            hpos_nonempty ⟨n, Finset.mem_filter.mpr ⟨hn, hn_pos⟩⟩
        Real.mem_neg_side_of_not_mem_pos_side_of_mem_reducedArc_sep
          hlam_pos (hψ_mem n hn_mem_original)
          (hψ_sep n hn_mem_original) hnot_pos)

/-- An antitone separated reduced sequence is either entirely on one side on
`Ico a m`, or it has a first negative index giving a positive block followed by
a negative block. -/
theorem Real.antitoneOn_reducedArc_side_decomposition
    (ψ : ℕ → ℝ)
    {a b m : ℕ}
    {lam : ℝ}
    [∀ n : ℕ, Decidable (ψ n ∈ Set.Ioc (-Real.pi) (0 : ℝ))]
    (hm : m ∈ Finset.Icc a b)
    (hlam_pos : 0 < lam)
    (hψ_mem :
      ∀ n : ℕ,
        n ∈ Finset.Ico a b →
          ψ n ∈ Set.Ioc (-Real.pi) Real.pi)
    (hψ_anti : AntitoneOn ψ (Finset.Ico a b : Set ℕ))
    (hψ_sep :
      ∀ n : ℕ,
        n ∈ Finset.Ico a b →
          lam ≤ ‖ψ n‖) :
    (∀ n : ℕ,
        n ∈ Finset.Ico a m →
          ψ n ∈ Set.Ioc (0 : ℝ) Real.pi) ∨
      (∀ n : ℕ,
        n ∈ Finset.Ico a m →
          ψ n ∈ Set.Ioc (-Real.pi) (0 : ℝ)) ∨
      ∃ c : ℕ,
        a < c ∧ c < m ∧
          (∀ n : ℕ,
            n ∈ Finset.Ico a c →
              ψ n ∈ Set.Ioc (0 : ℝ) Real.pi) ∧
          (∀ n : ℕ,
            n ∈ Finset.Ico c m →
              ψ n ∈ Set.Ioc (-Real.pi) (0 : ℝ)) := by
  let negatives : Finset ℕ :=
    (Finset.Ico a m).filter
      (fun n : ℕ => ψ n ∈ Set.Ioc (-Real.pi) (0 : ℝ))
  have hm_bounds : a ≤ m ∧ m ≤ b :=
    Finset.mem_Icc.mp hm
  by_cases hneg_nonempty : negatives.Nonempty
  · let c : ℕ := negatives.min' hneg_nonempty
    have hc_filter : c ∈ negatives :=
      Finset.min'_mem negatives hneg_nonempty
    have hc_data :
        c ∈ Finset.Ico a m ∧
          ψ c ∈ Set.Ioc (-Real.pi) (0 : ℝ) :=
      Finset.mem_filter.mp hc_filter
    have hc_bounds : a ≤ c ∧ c < m :=
      Finset.mem_Ico.mp hc_data.1
    by_cases hca : c = a
    · exact Or.inr (Or.inl
        (fun n hn =>
          let hn_bounds : a ≤ n ∧ n < m := Finset.mem_Ico.mp hn
          let hn_mem_original : n ∈ Finset.Ico a b :=
            Finset.mem_Ico.mpr
              ⟨hn_bounds.1, lt_of_lt_of_le hn_bounds.2 hm_bounds.2⟩
          let hc_mem_original : c ∈ Finset.Ico a b :=
            Finset.mem_Ico.mpr
              ⟨hc_bounds.1, lt_of_lt_of_le hc_bounds.2 hm_bounds.2⟩
          let hc_le_n : c ≤ n :=
            Eq.subst
              (motive := fun r : ℕ => r ≤ n)
              hca.symm
              hn_bounds.1
          let hanti_step : ψ n ≤ ψ c :=
            hψ_anti hc_mem_original hn_mem_original hc_le_n
          ⟨(hψ_mem n hn_mem_original).1,
            le_trans hanti_step hc_data.2.2⟩))
    · have hac : a < c :=
        lt_of_le_of_ne hc_bounds.1 (Ne.symm hca)
      exact Or.inr (Or.inr
        ⟨c, hac, hc_bounds.2,
          (fun n hn =>
            let hn_bounds : a ≤ n ∧ n < c := Finset.mem_Ico.mp hn
            let hn_mem_am : n ∈ Finset.Ico a m :=
              Finset.mem_Ico.mpr
                ⟨hn_bounds.1, lt_trans hn_bounds.2 hc_bounds.2⟩
            let hn_mem_original : n ∈ Finset.Ico a b :=
              Finset.mem_Ico.mpr
                ⟨hn_bounds.1,
                  lt_of_lt_of_le (lt_trans hn_bounds.2 hc_bounds.2)
                    hm_bounds.2⟩
            let hnot_neg :
                ¬ ψ n ∈ Set.Ioc (-Real.pi) (0 : ℝ) :=
              fun hn_neg =>
                let hn_filter : n ∈ negatives :=
                  Finset.mem_filter.mpr ⟨hn_mem_am, hn_neg⟩
                let hc_le_n : c ≤ n :=
                  Finset.min'_le negatives n hn_filter
                (not_lt_of_ge hc_le_n) hn_bounds.2
            Real.mem_pos_side_of_not_mem_neg_side_of_mem_reducedArc_sep
              hlam_pos (hψ_mem n hn_mem_original)
              (hψ_sep n hn_mem_original) hnot_neg),
          (fun n hn =>
            let hn_bounds : c ≤ n ∧ n < m := Finset.mem_Ico.mp hn
            let hn_mem_original : n ∈ Finset.Ico a b :=
              Finset.mem_Ico.mpr
                ⟨le_trans hc_bounds.1 hn_bounds.1,
                  lt_of_lt_of_le hn_bounds.2 hm_bounds.2⟩
            let hc_mem_original : c ∈ Finset.Ico a b :=
              Finset.mem_Ico.mpr
                ⟨hc_bounds.1, lt_of_lt_of_le hc_bounds.2 hm_bounds.2⟩
            let hanti_step : ψ n ≤ ψ c :=
              hψ_anti hc_mem_original hn_mem_original hn_bounds.1
            ⟨(hψ_mem n hn_mem_original).1,
              le_trans hanti_step hc_data.2.2⟩)⟩)
  · exact Or.inl
      (fun n hn =>
        let hn_bounds : a ≤ n ∧ n < m := Finset.mem_Ico.mp hn
        let hn_mem_original : n ∈ Finset.Ico a b :=
          Finset.mem_Ico.mpr
            ⟨hn_bounds.1, lt_of_lt_of_le hn_bounds.2 hm_bounds.2⟩
        let hnot_neg :
            ¬ ψ n ∈ Set.Ioc (-Real.pi) (0 : ℝ) :=
          fun hn_neg =>
            hneg_nonempty ⟨n, Finset.mem_filter.mpr ⟨hn, hn_neg⟩⟩
        Real.mem_pos_side_of_not_mem_neg_side_of_mem_reducedArc_sep
          hlam_pos (hψ_mem n hn_mem_original)
          (hψ_sep n hn_mem_original) hnot_neg)

/-- The imaginary coordinate of a complex number is bounded by its norm. -/
theorem Complex.norm_im_le_norm
    (z : ℂ) :
    ‖z.im‖ ≤ ‖z‖ := by
  calc
    ‖z.im‖ = |z.im| :=
      Real.norm_eq_abs z.im
    _ ≤ Complex.abs z :=
      Complex.abs_im_le_abs z
    _ = ‖z‖ :=
      (Complex.norm_eq_abs z).symm

/-- The reduced inverse-denominator imaginary coordinate is bounded by the
complex norm. -/
theorem Complex.reducedArc_inverseGeometricDenominator_imCoord_norm_le_norm
    (ψ : ℝ) :
    ‖Complex.reducedArc_inverseGeometricDenominator_imCoord ψ‖ ≤
      ‖Complex.reducedArc_inverseGeometricDenominator ψ‖ := by
  exact Complex.norm_im_le_norm
    (Complex.reducedArc_inverseGeometricDenominator ψ)

/-- On a one-sided reduced arc, composing the inverse-chord imaginary coordinate
with a monotone-or-antitone sequence remains monotone-or-antitone. -/
theorem Complex.reducedArc_inverseGeometricDenominator_imCoord_mono_or_anti_on_oneSided
    (ψ : ℕ → ℝ)
    {a b : ℕ}
    {lam L U : ℝ}
    (hlam_pos : 0 < lam)
    (hside : L = (0 : ℝ) ∧ U = Real.pi ∨
      L = -Real.pi ∧ U = (0 : ℝ))
    (hψ_mem :
      ∀ n : ℕ,
        n ∈ Finset.Ico a b →
          ψ n ∈ Set.Ioc L U)
    (hψ_mono :
      MonotoneOn (fun n : ℕ => ψ n) (Finset.Ico a b : Set ℕ) ∨
      AntitoneOn (fun n : ℕ => ψ n) (Finset.Ico a b : Set ℕ))
    (hψ_sep :
      ∀ n : ℕ,
        n ∈ Finset.Ico a b →
          lam ≤ ‖ψ n‖) :
    MonotoneOn
        (fun n : ℕ =>
          Complex.reducedArc_inverseGeometricDenominator_imCoord (ψ n))
        (Finset.Ico a b : Set ℕ) ∨
      AntitoneOn
        (fun n : ℕ =>
          Complex.reducedArc_inverseGeometricDenominator_imCoord (ψ n))
        (Finset.Ico a b : Set ℕ) := by
  match hside with
  | Or.inl hpos =>
      have hmem_pos :
          ∀ n : ℕ,
            n ∈ Finset.Ico a b →
              ψ n ∈ Set.Ioc (0 : ℝ) Real.pi := by
        intro n hn
        exact Real.mem_Ioc_zero_pi_of_mem_pos_side hpos (hψ_mem n hn)
      match hψ_mono with
      | Or.inl hmono =>
          exact Or.inr
            (fun i hi j hj hij =>
              Complex.reducedArc_inverseGeometricDenominator_imCoord_antitoneOn_pos
                (hmem_pos i hi) (hmem_pos j hj) (hmono hi hj hij))
      | Or.inr hanti =>
          exact Or.inl
            (fun i hi j hj hij =>
              Complex.reducedArc_inverseGeometricDenominator_imCoord_antitoneOn_pos
                (hmem_pos j hj) (hmem_pos i hi) (hanti hi hj hij))
  | Or.inr hneg =>
      have hmem_neg :
          ∀ n : ℕ,
            n ∈ Finset.Ico a b →
              ψ n ∈ Set.Ioo (-Real.pi) (0 : ℝ) := by
        intro n hn
        exact Real.mem_Ioo_neg_pi_zero_of_mem_neg_side_sep
          hlam_pos hneg (hψ_mem n hn) (hψ_sep n hn)
      match hψ_mono with
      | Or.inl hmono =>
          exact Or.inr
            (fun i hi j hj hij =>
              Complex.reducedArc_inverseGeometricDenominator_imCoord_antitoneOn_neg
                (hmem_neg i hi) (hmem_neg j hj) (hmono hi hj hij))
      | Or.inr hanti =>
          exact Or.inl
            (fun i hi j hj hij =>
              Complex.reducedArc_inverseGeometricDenominator_imCoord_antitoneOn_neg
                (hmem_neg j hj) (hmem_neg i hi) (hanti hi hj hij))

/-- Scalar constant fold used by the one-sided variation endpoint estimate. -/
theorem Real.two_mul_add_two_mul_eq_four_mul
    (x : ℝ) :
    2 * x + 2 * x = 4 * x := by
  exact real_two_mul_add_two_mul_eq_four_mul_for_logarithmicPhase x

/-- Telescope for adjacent forward differences over a half-open natural
interval. -/
theorem Real.sum_Ico_adjacent_forward_sub_eq_endpoint_sub
    (g : ℕ → ℝ)
    {l u : ℕ}
    (hlu : l ≤ u) :
    (∑ n ∈ Finset.Ico l u, (g (n + 1) - g n)) =
      g u - g l := by
  have hIco_as_ranges :
      (∑ n ∈ Finset.Ico l u, (g (n + 1) - g n)) =
        (∑ n ∈ Finset.range u, (g (n + 1) - g n)) -
          ∑ n ∈ Finset.range l, (g (n + 1) - g n) :=
    Finset.sum_Ico_eq_sub (fun n : ℕ => g (n + 1) - g n) hlu
  have hu_range :
      (∑ n ∈ Finset.range u, (g (n + 1) - g n)) =
        g u - g 0 :=
    Finset.sum_range_sub g u
  have hl_range :
      (∑ n ∈ Finset.range l, (g (n + 1) - g n)) =
        g l - g 0 :=
    Finset.sum_range_sub g l
  have hrange_diff :
      (∑ n ∈ Finset.range u, (g (n + 1) - g n)) -
          ∑ n ∈ Finset.range l, (g (n + 1) - g n) =
        (g u - g 0) - (g l - g 0) :=
    congrArg₂ Sub.sub hu_range hl_range
  have hcancel :
      (g u - g 0) - (g l - g 0) =
        g u - g l :=
    sub_sub_sub_cancel_right (g u) (g l) (g 0)
  exact Eq.trans hIco_as_ranges (Eq.trans hrange_diff hcancel)

/-- Telescope for adjacent forward differences over an open natural interval. -/
theorem Real.sum_Ioo_adjacent_sub_eq_endpoint_sub
    (y : ℕ → ℝ)
    {a m : ℕ}
    (ham : a < m) :
    (∑ n ∈ Finset.Ioo a m, (y n - y (n - 1))) =
      y (m - 1) - y a := by
  have hIoo :
      Finset.Ioo a m = Finset.Ico (a + 1) m :=
    Finset.nat_Ioo_eq_Ico_succ_left_for_logarithmicPhase a m
  have hsucc_le : a + 1 ≤ m :=
    Nat.succ_le_of_lt ham
  have htel :
      (∑ n ∈ Finset.Ico (a + 1) m,
        ((fun k : ℕ => y (k - 1)) (n + 1) -
          (fun k : ℕ => y (k - 1)) n)) =
        (fun k : ℕ => y (k - 1)) m -
          (fun k : ℕ => y (k - 1)) (a + 1) :=
    Real.sum_Ico_adjacent_forward_sub_eq_endpoint_sub
      (fun k : ℕ => y (k - 1))
      hsucc_le
  have hleft :
      (∑ n ∈ Finset.Ico (a + 1) m,
        ((fun k : ℕ => y (k - 1)) (n + 1) -
          (fun k : ℕ => y (k - 1)) n)) =
        ∑ n ∈ Finset.Ico (a + 1) m, (y n - y (n - 1)) := by
    exact Finset.sum_congr rfl
      (fun n hn =>
        congrArg
          (fun r : ℝ => r - y (n - 1))
          (congrArg y
            (Eq.trans (Nat.add_succ_sub_one n 0) (add_zero n))))
  have hright :
      (fun k : ℕ => y (k - 1)) m -
          (fun k : ℕ => y (k - 1)) (a + 1) =
        y (m - 1) - y a := by
    exact congrArg
      (fun r : ℝ => y (m - 1) - r)
      (congrArg y
        (Eq.trans (Nat.add_succ_sub_one a 0) (add_zero a)))
  calc
    (∑ n ∈ Finset.Ioo a m, (y n - y (n - 1))) =
        ∑ n ∈ Finset.Ico (a + 1) m, (y n - y (n - 1)) := by
      exact congrArg
        (fun s : Finset ℕ =>
          ∑ n ∈ s, (y n - y (n - 1)))
        hIoo
    _ =
        (∑ n ∈ Finset.Ico (a + 1) m,
          ((fun k : ℕ => y (k - 1)) (n + 1) -
            (fun k : ℕ => y (k - 1)) n)) :=
      hleft.symm
    _ =
        (fun k : ℕ => y (k - 1)) m -
          (fun k : ℕ => y (k - 1)) (a + 1) :=
      htel
    _ = y (m - 1) - y a :=
      hright

/-- Telescope for adjacent backward differences over an open natural interval. -/
theorem Real.sum_Ioo_adjacent_sub_rev_eq_endpoint_sub
    (y : ℕ → ℝ)
    {a m : ℕ}
    (ham : a < m) :
    (∑ n ∈ Finset.Ioo a m, (y (n - 1) - y n)) =
      y a - y (m - 1) := by
  have hneg :
      (∑ n ∈ Finset.Ioo a m, (y (n - 1) - y n)) =
        -∑ n ∈ Finset.Ioo a m, (y n - y (n - 1)) := by
    calc
      (∑ n ∈ Finset.Ioo a m, (y (n - 1) - y n)) =
          ∑ n ∈ Finset.Ioo a m, -(y n - y (n - 1)) := by
        exact Finset.sum_congr rfl
          (fun n hn => (neg_sub (y n) (y (n - 1))).symm)
      _ = -∑ n ∈ Finset.Ioo a m, (y n - y (n - 1)) :=
        Finset.sum_neg_distrib
  have hforward :
      (∑ n ∈ Finset.Ioo a m, (y n - y (n - 1))) =
        y (m - 1) - y a :=
    Real.sum_Ioo_adjacent_sub_eq_endpoint_sub y ham
  calc
    (∑ n ∈ Finset.Ioo a m, (y (n - 1) - y n)) =
        -∑ n ∈ Finset.Ioo a m, (y n - y (n - 1)) :=
      hneg
    _ = -(y (m - 1) - y a) :=
      congrArg Neg.neg hforward
    _ = y a - y (m - 1) :=
      neg_sub (y (m - 1)) (y a)

/-- A real difference is bounded by the sum of endpoint norms. -/
theorem Real.sub_le_norm_add_norm
    (x y : ℝ) :
    x - y ≤ ‖x‖ + ‖y‖ := by
  have hx : x ≤ ‖x‖ :=
    Real.le_norm_self x
  have hy : -y ≤ ‖y‖ := by
    calc
      -y ≤ ‖-y‖ :=
        Real.le_norm_self (-y)
      _ = ‖y‖ :=
        norm_neg y
  have hsum : x + -y ≤ ‖x‖ + ‖y‖ :=
    add_le_add hx hy
  exact Eq.subst
    (motive := fun r : ℝ => r ≤ ‖x‖ + ‖y‖)
    (sub_eq_add_neg x y).symm
    hsum

/-- Monotone finite variation over an open natural interval telescopes to the
endpoint difference. -/
theorem Real.monotoneOn_nat_Ioo_totalVariation_eq_endpoint_sub
    (y : ℕ → ℝ)
    {a b m : ℕ}
    (ham : a < m)
    (hm : m ∈ Finset.Icc a b)
    (hy : MonotoneOn y (Finset.Ico a b : Set ℕ)) :
    (∑ n ∈ Finset.Ioo a m, ‖y n - y (n - 1)‖) =
      y (m - 1) - y a := by
  have hnorm :
      (∑ n ∈ Finset.Ioo a m, ‖y n - y (n - 1)‖) =
        ∑ n ∈ Finset.Ioo a m, (y n - y (n - 1)) := by
    exact Finset.sum_congr rfl
      (fun n hn =>
        Real.monotoneOn_nat_Ioo_adjacent_norm_eq_sub y hn hm hy)
  exact Eq.trans hnorm
    (Real.sum_Ioo_adjacent_sub_eq_endpoint_sub y ham)

/-- Antitone finite variation over an open natural interval telescopes to the
reverse endpoint difference. -/
theorem Real.antitoneOn_nat_Ioo_totalVariation_eq_endpoint_sub
    (y : ℕ → ℝ)
    {a b m : ℕ}
    (ham : a < m)
    (hm : m ∈ Finset.Icc a b)
    (hy : AntitoneOn y (Finset.Ico a b : Set ℕ)) :
    (∑ n ∈ Finset.Ioo a m, ‖y n - y (n - 1)‖) =
      y a - y (m - 1) := by
  have hnorm :
      (∑ n ∈ Finset.Ioo a m, ‖y n - y (n - 1)‖) =
        ∑ n ∈ Finset.Ioo a m, (y (n - 1) - y n) := by
    exact Finset.sum_congr rfl
      (fun n hn =>
        Real.antitoneOn_nat_Ioo_adjacent_norm_eq_sub_rev y hn hm hy)
  exact Eq.trans hnorm
    (Real.sum_Ioo_adjacent_sub_rev_eq_endpoint_sub y ham)

/-- Finite total variation of a monotone real sequence is controlled by endpoint
size. -/
theorem Real.monotoneOn_nat_Ioo_totalVariation_le_endpoint_norm
    (y : ℕ → ℝ)
    {a b m : ℕ}
    (ham : a < m)
    (hm : m ∈ Finset.Icc a b)
    (hy_mono :
      MonotoneOn y (Finset.Ico a b : Set ℕ) ∨
      AntitoneOn y (Finset.Ico a b : Set ℕ)) :
    (∑ n ∈ Finset.Ioo a m, ‖y n - y (n - 1)‖) ≤
      ‖y a‖ + ‖y (m - 1)‖ := by
  match hy_mono with
  | Or.inl hy =>
      have hsum :
          (∑ n ∈ Finset.Ioo a m, ‖y n - y (n - 1)‖) =
            y (m - 1) - y a :=
        Real.monotoneOn_nat_Ioo_totalVariation_eq_endpoint_sub y ham hm hy
      have hbound :
          y (m - 1) - y a ≤ ‖y (m - 1)‖ + ‖y a‖ :=
        Real.sub_le_norm_add_norm (y (m - 1)) (y a)
      have hcomm :
          ‖y (m - 1)‖ + ‖y a‖ = ‖y a‖ + ‖y (m - 1)‖ :=
        add_comm ‖y (m - 1)‖ ‖y a‖
      exact Eq.subst
        (motive := fun r : ℝ =>
          (∑ n ∈ Finset.Ioo a m, ‖y n - y (n - 1)‖) ≤ r)
        hcomm
        (Eq.subst
          (motive := fun r : ℝ =>
            r ≤ ‖y (m - 1)‖ + ‖y a‖)
          hsum.symm
          hbound)
  | Or.inr hy =>
      have hsum :
          (∑ n ∈ Finset.Ioo a m, ‖y n - y (n - 1)‖) =
            y a - y (m - 1) :=
        Real.antitoneOn_nat_Ioo_totalVariation_eq_endpoint_sub y ham hm hy
      have hbound :
          y a - y (m - 1) ≤ ‖y a‖ + ‖y (m - 1)‖ :=
        Real.sub_le_norm_add_norm (y a) (y (m - 1))
      exact Eq.subst
        (motive := fun r : ℝ =>
          r ≤ ‖y a‖ + ‖y (m - 1)‖)
        hsum.symm
        hbound

/-- One-sided inverse-chord variation after reducing to the vertical-line
imaginary coordinate. -/
theorem Complex.reducedArc_inverseGeometricDenominator_oneSided_variation_bound_from_imCoord
    (ψ : ℕ → ℝ)
    {a b m : ℕ}
    {lam : ℝ}
    {L U : ℝ}
    (ham : a < m)
    (hm : m ∈ Finset.Icc a b)
    (hlam_pos : 0 < lam)
    (hside : L = (0 : ℝ) ∧ U = Real.pi ∨
      L = -Real.pi ∧ U = (0 : ℝ))
    (hψ_mem :
      ∀ n : ℕ,
        n ∈ Finset.Ico a b →
          ψ n ∈ Set.Ioc L U)
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
        4 * lam⁻¹ := by
  let y : ℕ → ℝ :=
    fun n : ℕ =>
      Complex.reducedArc_inverseGeometricDenominator_imCoord (ψ n)
  have hymono :
      MonotoneOn y (Finset.Ico a b : Set ℕ) ∨
        AntitoneOn y (Finset.Ico a b : Set ℕ) :=
    Complex.reducedArc_inverseGeometricDenominator_imCoord_mono_or_anti_on_oneSided
      ψ hlam_pos hside hψ_mem hψ_mono hψ_sep
  have hcomplex_to_y :
      (∑ n ∈ Finset.Ioo a m,
        ‖Complex.reducedArc_inverseGeometricDenominator (ψ n) -
          Complex.reducedArc_inverseGeometricDenominator (ψ (n - 1))‖) =
        ∑ n ∈ Finset.Ioo a m, ‖y n - y (n - 1)‖ := by
    exact Finset.sum_congr rfl
      (fun n hn =>
        let hn_Ico : n ∈ Finset.Ico a b :=
          Nat.mem_Ico_of_mem_Ioo_right hn hm
        let hpred_Ico : n - 1 ∈ Finset.Ico a b :=
          Nat.pred_mem_Ico_of_mem_Ioo_right hn hm
        let hn_data :
            ψ n ∈ Set.Ioc (-Real.pi) Real.pi ∧ ψ n ≠ 0 :=
          Real.oneSided_reducedArc_mem_and_ne_of_sep
            ψ hlam_pos hside hn_Ico hψ_mem hψ_sep
        let hpred_data :
            ψ (n - 1) ∈ Set.Ioc (-Real.pi) Real.pi ∧
              ψ (n - 1) ≠ 0 :=
          Real.oneSided_reducedArc_mem_and_ne_of_sep
            ψ hlam_pos hside hpred_Ico hψ_mem hψ_sep
        Complex.reducedArc_inverseGeometricDenominator_adjacent_norm_eq_imCoord
          ψ hn_data.1 hpred_data.1 hn_data.2 hpred_data.2)
  have hreal_variation :
      (∑ n ∈ Finset.Ioo a m, ‖y n - y (n - 1)‖) ≤
        ‖y a‖ + ‖y (m - 1)‖ :=
    Real.monotoneOn_nat_Ioo_totalVariation_le_endpoint_norm
      y ham hm hymono
  have hm_bounds : a ≤ m ∧ m ≤ b :=
    Finset.mem_Icc.mp hm
  have ha_mem : a ∈ Finset.Ico a b :=
    Finset.mem_Ico.mpr
      ⟨le_rfl, lt_of_lt_of_le ham hm_bounds.2⟩
  have hm_pred_mem : m - 1 ∈ Finset.Ico a b := by
    have ha_pred : a ≤ m - 1 :=
      Nat.le_pred_of_lt ham
    have hm_pos : 0 < m :=
      lt_of_le_of_lt (Nat.zero_le a) ham
    have hpred_lt_m : m - 1 < m :=
      Nat.pred_lt (Nat.ne_of_gt hm_pos)
    have hpred_lt_b : m - 1 < b :=
      lt_of_lt_of_le hpred_lt_m hm_bounds.2
    exact Finset.mem_Ico.mpr ⟨ha_pred, hpred_lt_b⟩
  have ha_y :
      ‖y a‖ ≤ 2 * lam⁻¹ := by
    exact le_trans
      (Complex.reducedArc_inverseGeometricDenominator_imCoord_norm_le_norm
        (ψ a))
      (hψ_den a ha_mem)
  have hm_y :
      ‖y (m - 1)‖ ≤ 2 * lam⁻¹ := by
    exact le_trans
      (Complex.reducedArc_inverseGeometricDenominator_imCoord_norm_le_norm
        (ψ (m - 1)))
      (hψ_den (m - 1) hm_pred_mem)
  have hendpoint :
      ‖y a‖ + ‖y (m - 1)‖ ≤
        2 * lam⁻¹ + 2 * lam⁻¹ :=
    add_le_add ha_y hm_y
  have hendpoint_four :
      ‖y a‖ + ‖y (m - 1)‖ ≤ 4 * lam⁻¹ :=
    Eq.subst
      (motive := fun r : ℝ =>
        ‖y a‖ + ‖y (m - 1)‖ ≤ r)
      (Real.two_mul_add_two_mul_eq_four_mul lam⁻¹)
      hendpoint
  have hy_bound :
      (∑ n ∈ Finset.Ioo a m, ‖y n - y (n - 1)‖) ≤
        4 * lam⁻¹ :=
    le_trans hreal_variation hendpoint_four
  exact Eq.subst
    (motive := fun r : ℝ => r ≤ 4 * lam⁻¹)
    hcomplex_to_y.symm
    hy_bound

/-- Variation bound for the reduced inverse denominator on one side of the
singularity at zero. -/
theorem Complex.reducedArc_inverseGeometricDenominator_oneSided_variation_bound
    (ψ : ℕ → ℝ)
    {a b m : ℕ}
    {lam : ℝ}
    {L U : ℝ}
    (ham : a < m)
    (hm : m ∈ Finset.Icc a b)
    (hlam_pos : 0 < lam)
    (hside : L = (0 : ℝ) ∧ U = Real.pi ∨
      L = -Real.pi ∧ U = (0 : ℝ))
    (hψ_mem :
      ∀ n : ℕ,
        n ∈ Finset.Ico a b →
          ψ n ∈ Set.Ioc L U)
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
        4 * lam⁻¹ := by
  exact
    Complex.reducedArc_inverseGeometricDenominator_oneSided_variation_bound_from_imCoord
      ψ ham hm hlam_pos hside hψ_mem hψ_mono hψ_sep hψ_den

/-- A single adjacent inverse-denominator jump is bounded by the two endpoint
denominator bounds. -/
theorem Complex.reducedArc_inverseGeometricDenominator_adjacent_norm_le_four_inv
    (ψ : ℕ → ℝ)
    {a b m n : ℕ}
    {lam : ℝ}
    (hn : n ∈ Finset.Ioo a m)
    (hm : m ∈ Finset.Icc a b)
    (hψ_den :
      ∀ k : ℕ,
        k ∈ Finset.Ico a b →
          ‖Complex.reducedArc_inverseGeometricDenominator (ψ k)‖ ≤
            2 * lam⁻¹) :
    ‖Complex.reducedArc_inverseGeometricDenominator (ψ n) -
      Complex.reducedArc_inverseGeometricDenominator (ψ (n - 1))‖ ≤
        4 * lam⁻¹ := by
  have hn_mem : n ∈ Finset.Ico a b :=
    Nat.mem_Ico_of_mem_Ioo_right hn hm
  have hpred_mem : n - 1 ∈ Finset.Ico a b :=
    Nat.pred_mem_Ico_of_mem_Ioo_right hn hm
  have hn_bound :
      ‖Complex.reducedArc_inverseGeometricDenominator (ψ n)‖ ≤
        2 * lam⁻¹ :=
    hψ_den n hn_mem
  have hpred_bound :
      ‖Complex.reducedArc_inverseGeometricDenominator (ψ (n - 1))‖ ≤
        2 * lam⁻¹ :=
    hψ_den (n - 1) hpred_mem
  have hjump :
      ‖Complex.reducedArc_inverseGeometricDenominator (ψ n) -
        Complex.reducedArc_inverseGeometricDenominator (ψ (n - 1))‖ ≤
        ‖Complex.reducedArc_inverseGeometricDenominator (ψ n)‖ +
          ‖Complex.reducedArc_inverseGeometricDenominator (ψ (n - 1))‖ :=
    norm_sub_le
      (Complex.reducedArc_inverseGeometricDenominator (ψ n))
      (Complex.reducedArc_inverseGeometricDenominator (ψ (n - 1)))
  have hendpoint :
      ‖Complex.reducedArc_inverseGeometricDenominator (ψ n)‖ +
          ‖Complex.reducedArc_inverseGeometricDenominator (ψ (n - 1))‖ ≤
        2 * lam⁻¹ + 2 * lam⁻¹ :=
    add_le_add hn_bound hpred_bound
  have hfour :
      ‖Complex.reducedArc_inverseGeometricDenominator (ψ n)‖ +
          ‖Complex.reducedArc_inverseGeometricDenominator (ψ (n - 1))‖ ≤
        4 * lam⁻¹ :=
    Eq.subst
      (motive := fun r : ℝ =>
        ‖Complex.reducedArc_inverseGeometricDenominator (ψ n)‖ +
            ‖Complex.reducedArc_inverseGeometricDenominator (ψ (n - 1))‖ ≤ r)
      (Real.two_mul_add_two_mul_eq_four_mul lam⁻¹)
      hendpoint
  exact le_trans hjump hfour

/-- Splitting an open natural interval at an interior index separates the left
open interval, the crossing index, and the right open interval. -/
theorem Finset.sum_Ioo_split_at
    {α : Type*}
    [AddCommMonoid α]
    (f : ℕ → α)
    {a c m : ℕ}
    (hac : a < c)
    (hcm : c < m) :
    (∑ n ∈ Finset.Ioo a m, f n) =
      (∑ n ∈ Finset.Ioo a c, f n) + f c +
        ∑ n ∈ Finset.Ioo c m, f n := by
  have ha_succ_c : a + 1 ≤ c :=
    Nat.succ_le_of_lt hac
  have hc_le_m : c ≤ m :=
    le_of_lt hcm
  have hleft :
      Finset.Ioo a c = Finset.Ico (a + 1) c :=
    Finset.nat_Ioo_eq_Ico_succ_left_for_logarithmicPhase a c
  have hwhole :
      Finset.Ioo a m = Finset.Ico (a + 1) m :=
    Finset.nat_Ioo_eq_Ico_succ_left_for_logarithmicPhase a m
  have hright :
      Finset.Ioo c m = Finset.Ico (c + 1) m :=
    Finset.nat_Ioo_eq_Ico_succ_left_for_logarithmicPhase c m
  have hconsecutive :
      (∑ n ∈ Finset.Ico (a + 1) c, f n) +
          ∑ n ∈ Finset.Ico c m, f n =
        ∑ n ∈ Finset.Ico (a + 1) m, f n :=
    Finset.sum_Ico_consecutive f ha_succ_c hc_le_m
  have hpeel :
      (∑ n ∈ Finset.Ico c m, f n) =
        f c + ∑ n ∈ Finset.Ico (c + 1) m, f n :=
    Finset.sum_eq_sum_Ico_succ_bot hcm f
  calc
    (∑ n ∈ Finset.Ioo a m, f n) =
        ∑ n ∈ Finset.Ico (a + 1) m, f n :=
      congrArg (fun s : Finset ℕ => ∑ n ∈ s, f n) hwhole
    _ =
        (∑ n ∈ Finset.Ico (a + 1) c, f n) +
          ∑ n ∈ Finset.Ico c m, f n :=
      hconsecutive.symm
    _ =
        (∑ n ∈ Finset.Ico (a + 1) c, f n) +
          (f c + ∑ n ∈ Finset.Ico (c + 1) m, f n) :=
      congrArg
        (fun r : α =>
          (∑ n ∈ Finset.Ico (a + 1) c, f n) + r)
        hpeel
    _ =
        ((∑ n ∈ Finset.Ico (a + 1) c, f n) + f c) +
          ∑ n ∈ Finset.Ico (c + 1) m, f n :=
      (add_assoc
        (∑ n ∈ Finset.Ico (a + 1) c, f n)
        (f c)
        (∑ n ∈ Finset.Ico (c + 1) m, f n)).symm
    _ =
        (∑ n ∈ Finset.Ioo a c, f n) + f c +
          ∑ n ∈ Finset.Ioo c m, f n :=
      congrArg₂ Add.add
        (congrArg₂ Add.add
          (congrArg (fun s : Finset ℕ => ∑ n ∈ s, f n) hleft.symm)
          rfl)
        (congrArg (fun s : Finset ℕ => ∑ n ∈ s, f n) hright.symm)


end

end LFunctions
end Boundary
