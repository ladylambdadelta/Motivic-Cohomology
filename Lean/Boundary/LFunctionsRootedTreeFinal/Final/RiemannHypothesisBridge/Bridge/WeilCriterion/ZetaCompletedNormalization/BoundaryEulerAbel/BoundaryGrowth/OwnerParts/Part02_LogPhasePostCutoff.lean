import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalization.BoundaryEulerAbel.BoundaryGrowth.OwnerParts.Part01_CoreSetup

/-!
# Boundary growth owner part 2

This file is a mechanical forward-order split of `BoundaryGrowth.Owner`.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open scoped Filter Topology
local notation "π" => Real.pi

/-- Positive integer logarithmic step ratios decrease with the integer index. -/
theorem boundaryGrowth_logarithmicStepRatio_antitone_nat
    {m n : ℕ}
    (hm : 1 ≤ m)
    (hmn : m ≤ n) :
    (((n + 1 : ℕ) : ℝ) / (n : ℝ)) ≤
      (((m + 1 : ℕ) : ℝ) / (m : ℝ)) := by
  have hm_pos_nat : 0 < m :=
    Nat.lt_of_succ_le hm
  have hn_pos_nat : 0 < n :=
    lt_of_lt_of_le hm_pos_nat hmn
  have hm_pos : (0 : ℝ) < (m : ℝ) :=
    Nat.cast_pos.mpr hm_pos_nat
  have hn_pos : (0 : ℝ) < (n : ℝ) :=
    Nat.cast_pos.mpr hn_pos_nat
  have hmn_real : (m : ℝ) ≤ (n : ℝ) :=
    Nat.cast_le.mpr hmn
  have hreciprocal : (1 : ℝ) / (n : ℝ) ≤ (1 : ℝ) / (m : ℝ) :=
    one_div_le_one_div_of_le hm_pos hmn_real
  have hn_ratio :
      (((n + 1 : ℕ) : ℝ) / (n : ℝ)) =
        (1 : ℝ) + (1 : ℝ) / (n : ℝ) := by
    calc
      (((n + 1 : ℕ) : ℝ) / (n : ℝ)) =
          (((n : ℕ) : ℝ) + (1 : ℝ)) / (n : ℝ) := by
        exact congrArg (fun y : ℝ => y / (n : ℝ)) (Nat.cast_add n 1)
      _ = ((n : ℝ) / (n : ℝ)) + ((1 : ℝ) / (n : ℝ)) := by
        exact add_div (n : ℝ) (1 : ℝ) (n : ℝ)
      _ = (1 : ℝ) + ((1 : ℝ) / (n : ℝ)) := by
        exact congrArg (fun y : ℝ => y + ((1 : ℝ) / (n : ℝ)))
          (div_self (ne_of_gt hn_pos))
  have hm_ratio :
      (((m + 1 : ℕ) : ℝ) / (m : ℝ)) =
        (1 : ℝ) + (1 : ℝ) / (m : ℝ) := by
    calc
      (((m + 1 : ℕ) : ℝ) / (m : ℝ)) =
          (((m : ℕ) : ℝ) + (1 : ℝ)) / (m : ℝ) := by
        exact congrArg (fun y : ℝ => y / (m : ℝ)) (Nat.cast_add m 1)
      _ = ((m : ℝ) / (m : ℝ)) + ((1 : ℝ) / (m : ℝ)) := by
        exact add_div (m : ℝ) (1 : ℝ) (m : ℝ)
      _ = (1 : ℝ) + ((1 : ℝ) / (m : ℝ)) := by
        exact congrArg (fun y : ℝ => y + ((1 : ℝ) / (m : ℝ)))
          (div_self (ne_of_gt hm_pos))
  exact Eq.subst
    (motive := fun left : ℝ =>
      left ≤ (((m + 1 : ℕ) : ℝ) / (m : ℝ)))
    hn_ratio.symm
    (Eq.subst
      (motive := fun right : ℝ =>
        (1 : ℝ) + (1 : ℝ) / (n : ℝ) ≤ right)
      hm_ratio.symm
      (add_le_add_left hreciprocal 1))

/-- Logarithms of positive integer step ratios decrease with the integer index. -/
theorem boundaryGrowth_logarithmicStepLog_antitone_nat
    {m n : ℕ}
    (hm : 1 ≤ m)
    (hmn : m ≤ n) :
    Real.log (((n + 1 : ℕ) : ℝ) / (n : ℝ)) ≤
      Real.log (((m + 1 : ℕ) : ℝ) / (m : ℝ)) := by
  have hm_pos_nat : 0 < m :=
    Nat.lt_of_succ_le hm
  have hn_pos_nat : 0 < n :=
    lt_of_lt_of_le hm_pos_nat hmn
  have hn_pos : (0 : ℝ) < (n : ℝ) :=
    Nat.cast_pos.mpr hn_pos_nat
  have hn_succ_pos : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) :=
    Nat.cast_pos.mpr (Nat.succ_pos n)
  have hn_ratio_pos :
      (0 : ℝ) < (((n + 1 : ℕ) : ℝ) / (n : ℝ)) :=
    div_pos hn_succ_pos hn_pos
  exact
    Real.log_le_log
      hn_ratio_pos
      (boundaryGrowth_logarithmicStepRatio_antitone_nat hm hmn)

/-- Adjacent increments of the real logarithmic phase are the signed logarithmic
step ratios. -/
theorem boundaryGrowth_logarithmicPhase_integerIncrement_eq_neg_mul_logStep
    (t : ℝ)
    {n : ℕ}
    (hn : 1 ≤ n) :
    Complex.realPhase_integerIncrement
        (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t) n =
      -t * Real.log (((n + 1 : ℕ) : ℝ) / (n : ℝ)) := by
  have hn_pos_nat : 0 < n :=
    Nat.lt_of_succ_le hn
  have hn_pos : (0 : ℝ) < (n : ℝ) :=
    Nat.cast_pos.mpr hn_pos_nat
  have hn_ne : (n : ℝ) ≠ 0 :=
    ne_of_gt hn_pos
  have hsucc_ne : ((n + 1 : ℕ) : ℝ) ≠ 0 :=
    ne_of_gt (Nat.cast_pos.mpr (Nat.succ_pos n))
  have hlog_div :
      Real.log (((n + 1 : ℕ) : ℝ) / (n : ℝ)) =
        Real.log ((n + 1 : ℕ) : ℝ) - Real.log (n : ℝ) :=
    Real.log_div hsucc_ne hn_ne
  calc
    Complex.realPhase_integerIncrement
        (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t) n =
        (-t * Real.log ((n + 1 : ℕ) : ℝ)) -
          (-t * Real.log (n : ℝ)) := by
      rfl
    _ = -t * (Real.log ((n + 1 : ℕ) : ℝ) - Real.log (n : ℝ)) := by
      exact (mul_sub (-t) (Real.log ((n + 1 : ℕ) : ℝ)) (Real.log (n : ℝ))).symm
    _ = -t * Real.log (((n + 1 : ℕ) : ℝ) / (n : ℝ)) := by
      exact congrArg (fun y : ℝ => -t * y) hlog_div.symm

/-- Raw adjacent logarithmic increments are monotone on each positive integer
block.  This elementary fact is not enough for the reduced finite-difference
package: reduction modulo `2π` can wind, and exact resonances can occur. -/
theorem logarithmicPhase_integerIncrementMonotoneOn_of_logRatioMonotone_ownerGap
    (t : ℝ)
    {a b : ℕ}
    (ha : 1 ≤ a)
    (hab : a ≤ b) :
    Complex.realPhase_integerIncrementMonotoneOn
      (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t) a b := by
  have hcases : 0 ≤ t ∨ t ≤ 0 :=
    le_total 0 t
  match hcases with
  | Or.inl ht_nonneg =>
      exact Or.inr
        (fun m hm n hn hmn =>
          have hm_ge_a : a ≤ m :=
            (Finset.mem_Ico.mp hm).1
          have hm_pos : 1 ≤ m :=
            le_trans ha hm_ge_a
          have hlog :
              Real.log (((n + 1 : ℕ) : ℝ) / (n : ℝ)) ≤
                Real.log (((m + 1 : ℕ) : ℝ) / (m : ℝ)) :=
            boundaryGrowth_logarithmicStepLog_antitone_nat hm_pos hmn
          have hscaled :
              -t * Real.log (((m + 1 : ℕ) : ℝ) / (m : ℝ)) ≤
                -t * Real.log (((n + 1 : ℕ) : ℝ) / (n : ℝ)) :=
            mul_le_mul_of_nonpos_left hlog (neg_nonpos.mpr ht_nonneg)
          have hm_increment :
              Complex.realPhase_integerIncrement
                  (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t) m =
                -t * Real.log (((m + 1 : ℕ) : ℝ) / (m : ℝ)) :=
            boundaryGrowth_logarithmicPhase_integerIncrement_eq_neg_mul_logStep
              t hm_pos
          have hn_ge_a : a ≤ n :=
            le_trans hm_ge_a hmn
          have hn_pos : 1 ≤ n :=
            le_trans ha hn_ge_a
          have hn_increment :
              Complex.realPhase_integerIncrement
                  (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t) n =
                -t * Real.log (((n + 1 : ℕ) : ℝ) / (n : ℝ)) :=
            boundaryGrowth_logarithmicPhase_integerIncrement_eq_neg_mul_logStep
              t hn_pos
          Eq.subst
            (motive := fun left : ℝ =>
              left ≤
                Complex.realPhase_integerIncrement
                  (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t) n)
            hm_increment.symm
            (Eq.subst
              (motive := fun right : ℝ =>
                -t * Real.log (((m + 1 : ℕ) : ℝ) / (m : ℝ)) ≤ right)
              hn_increment.symm
              hscaled))
  | Or.inr ht_nonpos =>
      exact Or.inl
        (fun m hm n hn hmn =>
          have hm_ge_a : a ≤ m :=
            (Finset.mem_Ico.mp hm).1
          have hm_pos : 1 ≤ m :=
            le_trans ha hm_ge_a
          have hlog :
              Real.log (((n + 1 : ℕ) : ℝ) / (n : ℝ)) ≤
                Real.log (((m + 1 : ℕ) : ℝ) / (m : ℝ)) :=
            boundaryGrowth_logarithmicStepLog_antitone_nat hm_pos hmn
          have hscaled :
              -t * Real.log (((n + 1 : ℕ) : ℝ) / (n : ℝ)) ≤
                -t * Real.log (((m + 1 : ℕ) : ℝ) / (m : ℝ)) :=
            mul_le_mul_of_nonneg_left hlog (neg_nonneg.mpr ht_nonpos)
          have hm_increment :
              Complex.realPhase_integerIncrement
                  (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t) m =
                -t * Real.log (((m + 1 : ℕ) : ℝ) / (m : ℝ)) :=
            boundaryGrowth_logarithmicPhase_integerIncrement_eq_neg_mul_logStep
              t hm_pos
          have hn_ge_a : a ≤ n :=
            le_trans hm_ge_a hmn
          have hn_pos : 1 ≤ n :=
            le_trans ha hn_ge_a
          have hn_increment :
              Complex.realPhase_integerIncrement
                  (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t) n =
                -t * Real.log (((n + 1 : ℕ) : ℝ) / (n : ℝ)) :=
            boundaryGrowth_logarithmicPhase_integerIncrement_eq_neg_mul_logStep
              t hn_pos
          Eq.subst
            (motive := fun left : ℝ =>
              left ≤
                Complex.realPhase_integerIncrement
                  (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t) m)
            hn_increment.symm
            (Eq.subst
              (motive := fun right : ℝ =>
                -t * Real.log (((n + 1 : ℕ) : ℝ) / (n : ℝ)) ≤ right)
              hm_increment.symm
              hscaled))

/-- Endpoint-floor arithmetic for the public logarithmic-phase partial-sum
surface.

The VDC theorem supplies the factor
`40 * (((⌊x⌋₊ + 1) / |t| + sqrt (1 + |t|)) * log (2 + ⌊x⌋₊))`.
For `x ≥ ⌊2 + |t|⌋₊` and `1 ≤ |t|`, the endpoint shift is absorbed by
`1 / |t| ≤ sqrt (1 + |t|)`, while `log (2 + ⌊x⌋₊) ≤ log (2 + x)` follows
from `⌊x⌋₊ ≤ x`.  The only constant loss is therefore `40 -> 80`. -/
theorem boundaryLineOnePointRealParam_logarithmicPhase_vdcEndpoint_le_public80
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    {x : ℝ}
    (hx : (⌊2 + ‖t‖⌋₊ : ℝ) ≤ x) :
    40 *
        ((((⌊x⌋₊ + 1 : ℕ) : ℝ) / ‖t‖ +
            Real.sqrt (1 + ‖t‖)) *
          Real.log (2 + ⌊x⌋₊)) ≤
      80 * ((x / ‖t‖) + Real.sqrt (1 + ‖t‖)) * Real.log (2 + x) := by
  let T : ℝ := ‖t‖
  let S : ℝ := Real.sqrt (1 + T)
  let Lfloor : ℝ := Real.log (2 + ⌊x⌋₊)
  let Lx : ℝ := Real.log (2 + x)
  have hT_pos : 0 < T :=
    lt_of_lt_of_le zero_lt_one ht
  have hT_one : (1 : ℝ) ≤ T :=
    ht
  have hT_nonneg : 0 ≤ T :=
    le_of_lt hT_pos
  have hcutoff_nonneg : 0 ≤ ((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ) :=
    Nat.cast_nonneg ⌊2 + ‖t‖⌋₊
  have hx_nonneg : 0 ≤ x :=
    le_trans hcutoff_nonneg hx
  have hfloor_le_x : ((⌊x⌋₊ : ℕ) : ℝ) ≤ x :=
    Nat.floor_le hx_nonneg
  have hfloor_add_one_le :
      (((⌊x⌋₊ + 1 : ℕ) : ℝ) : ℝ) ≤ x + 1 := by
    calc
      (((⌊x⌋₊ + 1 : ℕ) : ℝ) : ℝ) =
          ((⌊x⌋₊ : ℕ) : ℝ) + 1 := by
        exact Nat.cast_add ⌊x⌋₊ 1
      _ ≤ x + 1 :=
        add_le_add_right hfloor_le_x 1
  have hone_div_le_one : (1 : ℝ) / T ≤ 1 := by
    calc
      (1 : ℝ) / T = 1 * T⁻¹ := by
        exact Eq.trans (one_div T) (one_mul T⁻¹).symm
      _ ≤ 1 * 1 :=
        mul_le_mul_of_nonneg_left
          (inv_le_one_of_one_le₀ hT_one)
          zero_le_one
      _ = 1 := by
        exact one_mul 1
  have hone_le_one_add_T : (1 : ℝ) ≤ 1 + T :=
    le_add_of_nonneg_right hT_nonneg
  have hone_le_S : (1 : ℝ) ≤ S := by
    exact Real.one_le_sqrt.mpr hone_le_one_add_T
  have hone_div_le_S : (1 : ℝ) / T ≤ S :=
    le_trans hone_div_le_one hone_le_S
  have hshift_div_le :
      (((⌊x⌋₊ + 1 : ℕ) : ℝ) / T) ≤ x / T + S := by
    calc
      (((⌊x⌋₊ + 1 : ℕ) : ℝ) / T) ≤ (x + 1) / T :=
        div_le_div_of_nonneg_right hfloor_add_one_le (le_of_lt hT_pos)
      _ = x / T + 1 / T := by
        exact add_div x 1 T
      _ ≤ x / T + S :=
        add_le_add_left hone_div_le_S (x / T)
  have hvdc_factor_le :
      (((⌊x⌋₊ + 1 : ℕ) : ℝ) / T + S) ≤
        2 * (x / T + S) := by
    calc
      (((⌊x⌋₊ + 1 : ℕ) : ℝ) / T + S) ≤
          (x / T + S) + S :=
        add_le_add_right hshift_div_le S
      _ ≤ (x / T + S) + (x / T + S) := by
        have hx_div_nonneg : 0 ≤ x / T :=
          div_nonneg hx_nonneg hT_nonneg
        have hS_le_sum : S ≤ x / T + S :=
          le_add_of_nonneg_left hx_div_nonneg
        exact add_le_add_left hS_le_sum (x / T + S)
      _ = 2 * (x / T + S) := by
        exact (two_mul (x / T + S)).symm
  have hlog_le : Lfloor ≤ Lx := by
    have hleft_pos : 0 < 2 + ((⌊x⌋₊ : ℕ) : ℝ) :=
      lt_of_lt_of_le zero_lt_two (le_add_of_nonneg_right (Nat.cast_nonneg ⌊x⌋₊))
    have harg_le : 2 + ((⌊x⌋₊ : ℕ) : ℝ) ≤ 2 + x :=
      add_le_add_left hfloor_le_x 2
    exact Real.log_le_log hleft_pos harg_le
  have hfactor_nonneg : 0 ≤ x / T + S := by
    exact add_nonneg (div_nonneg hx_nonneg hT_nonneg) (Real.sqrt_nonneg (1 + T))
  have hLfloor_nonneg : 0 ≤ Lfloor := by
    have hthree_le_arg : (3 : ℝ) ≤ 2 + ((⌊x⌋₊ : ℕ) : ℝ) := by
      have hfloor_one : (1 : ℝ) ≤ ((⌊x⌋₊ : ℕ) : ℝ) := by
        have hcutoff_one : (1 : ℝ) ≤ ((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ) :=
          Nat.cast_le.mpr (Nat.succ_le_of_lt (Nat.floor_pos.mpr (lt_of_lt_of_le zero_lt_two
            (le_add_of_nonneg_right (norm_nonneg t)))))
        have hx_one : (1 : ℝ) ≤ x :=
          le_trans hcutoff_one hx
        exact Nat.cast_le.mpr ((Nat.le_floor_iff hx_nonneg).mpr hx_one)
      calc
        (3 : ℝ) = 2 + 1 := by
          exact boundaryGrowth_real_two_add_one_eq_three.symm
        _ ≤ 2 + ((⌊x⌋₊ : ℕ) : ℝ) :=
          add_le_add_left hfloor_one 2
    have hone_le_arg : (1 : ℝ) ≤ 2 + ((⌊x⌋₊ : ℕ) : ℝ) :=
      le_trans (show (1 : ℝ) ≤ 3 from one_le_three) hthree_le_arg
    exact Real.log_nonneg hone_le_arg
  have hmul_factor_log :
      ((((⌊x⌋₊ + 1 : ℕ) : ℝ) / T + S) * Lfloor) ≤
        (2 * (x / T + S)) * Lx := by
    exact mul_le_mul hvdc_factor_le hlog_le hLfloor_nonneg
      (mul_nonneg zero_le_two hfactor_nonneg)
  have hscaled :
      40 *
          ((((⌊x⌋₊ + 1 : ℕ) : ℝ) / T + S) * Lfloor) ≤
        40 * ((2 * (x / T + S)) * Lx) :=
    mul_le_mul_of_nonneg_left hmul_factor_log
      (show (0 : ℝ) ≤ 40 from Nat.cast_nonneg 40)
  calc
    40 *
        ((((⌊x⌋₊ + 1 : ℕ) : ℝ) / ‖t‖ +
            Real.sqrt (1 + ‖t‖)) *
          Real.log (2 + ⌊x⌋₊)) =
        40 *
          ((((⌊x⌋₊ + 1 : ℕ) : ℝ) / T + S) * Lfloor) := rfl
    _ ≤ 40 * ((2 * (x / T + S)) * Lx) :=
      hscaled
    _ = 80 * ((x / T) + S) * Lx := by
      calc
        40 * ((2 * (x / T + S)) * Lx)
            = (40 * 2) * ((x / T + S) * Lx) := by
          exact Eq.trans
            (mul_assoc 40 (2 * (x / T + S)) Lx).symm
            (congrArg (fun y : ℝ => y * Lx)
              (mul_assoc 40 2 (x / T + S)))
        _ = 80 * ((x / T + S) * Lx) := by
          exact congrArg (fun y : ℝ => y * ((x / T + S) * Lx))
            boundaryGrowth_real_forty_mul_two_eq_eighty
        _ = 80 * (x / T + S) * Lx := by
          exact mul_assoc 80 (x / T + S) Lx
    _ = 80 * ((x / ‖t‖) + Real.sqrt (1 + ‖t‖)) * Real.log (2 + x) := rfl

/-- Endpoint-floor normalization from the proved VDC endpoint form to the
public first-derivative partial-sum bound. -/
theorem boundaryLineOnePointRealParam_logarithmicPhasePartialSumBound_of_vdc_endpoint
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    (hvdc :
      ∀ {x : ℝ},
        (⌊2 + ‖t‖⌋₊ : ℝ) ≤ x →
          ‖boundaryLineOnePointRealParam_logarithmicPhasePartialSum t ⌊x⌋₊‖ ≤
            40 *
              ((((⌊x⌋₊ + 1 : ℕ) : ℝ) / ‖t‖ +
                  Real.sqrt (1 + ‖t‖)) *
                Real.log (2 + ⌊x⌋₊))) :
    boundaryLineOnePointRealParam_logarithmicPhasePartialSumBound t := by
  intro x hx
  exact le_trans
    (hvdc hx)
    (boundaryLineOnePointRealParam_logarithmicPhase_vdcEndpoint_le_public80
      t ht hx)

/-- Conditional owner wrapper from the proved logarithmic-phase VDC estimate to
the public boundary-growth partial-sum hypothesis. -/
theorem boundaryLineOnePointRealParam_logarithmicPhasePartialSumBound_of_finiteDifference
    (hfiniteDifference : logarithmicPhaseFiniteDifferenceHypothesis)
    (t : ℝ)
    (ht : 1 ≤ ‖t‖) :
    boundaryLineOnePointRealParam_logarithmicPhasePartialSumBound t := by
  exact
    boundaryLineOnePointRealParam_logarithmicPhasePartialSumBound_of_vdc_endpoint
      t ht
      (fun hx =>
        boundaryLineOnePointRealParam_logarithmicPhasePartialSum_norm_le_vdc
          hfiniteDifference t ht hx)

/-- Exact antiderivative identity for the post-cutoff main integral.

This is the fundamental theorem of calculus step for
`x ↦ x^(-1-it)` on the positive interval
`[⌊2 + |t|⌋₊, M]`. -/
theorem boundaryLineOnePointRealParam_logarithmicPhase_postCutoff_mainIntegral_eq_intervalIntegral_ownerGap
    (t : ℝ)
    {M : ℕ}
    (hM : ⌊2 + ‖t‖⌋₊ ≤ M) :
    (∫ x in Set.Ioc (((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ)) (((M : ℕ) : ℝ)),
        (((x : ℝ) : ℂ) ^ (-boundaryLineOnePointRealParam t))) =
      ∫ x in (((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ))..(((M : ℕ) : ℝ)),
        (((x : ℝ) : ℂ) ^ (-boundaryLineOnePointRealParam t)) := by
  have hle :
      (((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ)) ≤ (((M : ℕ) : ℝ)) :=
    Nat.cast_le.mpr hM
  exact
    (intervalIntegral.integral_of_le
      (f := fun x : ℝ =>
        (((x : ℝ) : ℂ) ^ (-boundaryLineOnePointRealParam t)))
      hle).symm

/-- Exponent endpoint normalization for the post-cutoff main-integral
antiderivative. -/
theorem boundaryLineOnePointRealParam_logarithmicPhase_postCutoff_exponent_add_one
    (t : ℝ) :
    (-boundaryLineOnePointRealParam t) + (1 : ℂ) =
      -(t : ℂ) * Complex.I := by
  have htail :
      (-1 : ℂ) + (-(t : ℂ) * Complex.I) =
        -boundaryLineOnePointRealParam t :=
    boundaryLineOnePointRealParam_logarithmicPhase_tail_exponent_eq t
  calc
    (-boundaryLineOnePointRealParam t) + (1 : ℂ) =
        ((-1 : ℂ) + (-(t : ℂ) * Complex.I)) + (1 : ℂ) := by
      exact congrArg (fun z : ℂ => z + (1 : ℂ)) htail.symm
    _ = (-(t : ℂ) * Complex.I) + ((-1 : ℂ) + (1 : ℂ)) := by
      exact add_right_comm (-1 : ℂ) (-(t : ℂ) * Complex.I) (1 : ℂ)
    _ = (-(t : ℂ) * Complex.I) + (0 : ℂ) := by
      exact congrArg (fun z : ℂ => (-(t : ℂ) * Complex.I) + z) (neg_add_cancel (1 : ℂ))
    _ = -(t : ℂ) * Complex.I := by
      exact add_zero (-(t : ℂ) * Complex.I)

/-- The logarithmic-phase exponent is not the singular exponent `-1` on the
public range `1 ≤ ‖t‖`. -/
theorem boundaryLineOnePointRealParam_logarithmicPhase_postCutoff_exponent_ne_neg_one
    (t : ℝ)
    (ht : 1 ≤ ‖t‖) :
    -boundaryLineOnePointRealParam t ≠ (-1 : ℂ) := by
  intro h
  have hadd :
      (-boundaryLineOnePointRealParam t) + (1 : ℂ) =
        (-1 : ℂ) + (1 : ℂ) :=
    congrArg (fun z : ℂ => z + (1 : ℂ)) h
  have hleft :
      (-boundaryLineOnePointRealParam t) + (1 : ℂ) =
        -(t : ℂ) * Complex.I :=
    boundaryLineOnePointRealParam_logarithmicPhase_postCutoff_exponent_add_one t
  have hright :
      (-1 : ℂ) + (1 : ℂ) = (0 : ℂ) :=
    neg_add_cancel (1 : ℂ)
  have htI_zero :
      -(t : ℂ) * Complex.I = (0 : ℂ) :=
    Eq.trans hleft.symm (Eq.trans hadd hright)
  have hneg_t_zero : -t = 0 := by
    have him_eq :
        (-(t : ℂ) * Complex.I).im = ((0 : ℂ) : ℂ).im :=
      congrArg Complex.im htI_zero
    have hleft_im :
        (-(t : ℂ) * Complex.I).im = -t := by
      calc
        (-(t : ℂ) * Complex.I).im =
            (-(t : ℂ)).re := by
          exact Complex.mul_I_im (-(t : ℂ))
        _ = -((t : ℂ).re) := by
          exact Complex.neg_re (t : ℂ)
        _ = -t := by
          exact congrArg Neg.neg (Complex.ofReal_re t)
    have hright_im :
        ((0 : ℂ) : ℂ).im = (0 : ℝ) :=
      Complex.zero_im
    exact Eq.trans hleft_im.symm (Eq.trans him_eq hright_im)
  have ht_zero : t = 0 := by
    calc
      t = -(-t) := by
        exact (neg_neg t).symm
      _ = -(0 : ℝ) := by
        exact congrArg Neg.neg hneg_t_zero
      _ = 0 := by
        exact neg_zero
  have hnorm_zero : ‖t‖ = (0 : ℝ) :=
    congrArg norm ht_zero
  have hzero_lt_one : (0 : ℝ) < 1 :=
    zero_lt_one
  have hnot : ¬ ((1 : ℝ) ≤ 0) :=
    not_le.mpr hzero_lt_one
  exact hnot (Eq.subst (motive := fun r : ℝ => (1 : ℝ) ≤ r) hnorm_zero ht)

/-- The positive post-cutoff interval avoids the origin. -/
theorem boundaryLineOnePointRealParam_logarithmicPhase_postCutoff_zero_not_mem_uIcc
    (t : ℝ)
    {M : ℕ}
    (hM : ⌊2 + ‖t‖⌋₊ ≤ M) :
    (0 : ℝ) ∉
      [[(((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ)), (((M : ℕ) : ℝ))]] := by
  intro hzero_mem
  have hzero_pos :
      (0 : ℝ) < 0 :=
    boundaryLineOnePointRealParam_logarithmicPhase_postCutoff_mem_interval_pos
      t hM hzero_mem
  exact lt_irrefl (0 : ℝ) hzero_pos

/-- Direct `integral_cpow` evaluation before normalizing the endpoint exponent. -/
theorem boundaryLineOnePointRealParam_logarithmicPhase_postCutoff_intervalIntegral_eq_rawCpowAntiderivative
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    {M : ℕ}
    (hM : ⌊2 + ‖t‖⌋₊ ≤ M) :
    (∫ x in (((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ))..(((M : ℕ) : ℝ)),
        (((x : ℝ) : ℂ) ^ (-boundaryLineOnePointRealParam t))) =
      (((((M : ℕ) : ℝ) : ℂ) ^
            ((-boundaryLineOnePointRealParam t) + (1 : ℂ))) -
          (((((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ) : ℂ) ^
            ((-boundaryLineOnePointRealParam t) + (1 : ℂ)))) /
        ((-boundaryLineOnePointRealParam t) + (1 : ℂ)) := by
  exact
    integral_cpow
      (a := (((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ))
      (b := (((M : ℕ) : ℝ)))
      (r := -boundaryLineOnePointRealParam t)
      (Or.inr
        ⟨boundaryLineOnePointRealParam_logarithmicPhase_postCutoff_exponent_ne_neg_one
            t ht,
          boundaryLineOnePointRealParam_logarithmicPhase_postCutoff_zero_not_mem_uIcc
            t hM⟩)

theorem boundaryLineOnePointRealParam_logarithmicPhase_postCutoff_intervalIntegral_eq_antiderivativeDifference_ownerGap
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    {M : ℕ}
    (hM : ⌊2 + ‖t‖⌋₊ ≤ M) :
    (∫ x in (((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ))..(((M : ℕ) : ℝ)),
        (((x : ℝ) : ℂ) ^ (-boundaryLineOnePointRealParam t))) =
      (((((M : ℕ) : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I)) -
          (((((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ) : ℂ) ^
            (-(t : ℂ) * Complex.I)))) /
        (-(t : ℂ) * Complex.I) := by
  have hraw :
      (∫ x in (((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ))..(((M : ℕ) : ℝ)),
          (((x : ℝ) : ℂ) ^ (-boundaryLineOnePointRealParam t))) =
        (((((M : ℕ) : ℝ) : ℂ) ^
              ((-boundaryLineOnePointRealParam t) + (1 : ℂ))) -
            (((((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ) : ℂ) ^
              ((-boundaryLineOnePointRealParam t) + (1 : ℂ)))) /
          ((-boundaryLineOnePointRealParam t) + (1 : ℂ)) :=
    boundaryLineOnePointRealParam_logarithmicPhase_postCutoff_intervalIntegral_eq_rawCpowAntiderivative
      t ht hM
  have hexp :
      (-boundaryLineOnePointRealParam t) + (1 : ℂ) =
        -(t : ℂ) * Complex.I :=
    boundaryLineOnePointRealParam_logarithmicPhase_postCutoff_exponent_add_one t
  exact
    Eq.trans hraw
      (congrArg
        (fun z : ℂ =>
          let upper : ℂ := (((M : ℕ) : ℝ) : ℂ)
          let lower : ℂ := ((((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ) : ℂ))
          ((upper ^ z) - (lower ^ z)) / z)
        hexp)

theorem boundaryLineOnePointRealParam_logarithmicPhase_postCutoff_mainIntegral_eq_antiderivativeDifference_ownerGap
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    {M : ℕ}
    (hM : ⌊2 + ‖t‖⌋₊ ≤ M) :
    (∫ x in Set.Ioc (((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ)) (((M : ℕ) : ℝ)),
        (((x : ℝ) : ℂ) ^ (-boundaryLineOnePointRealParam t))) =
      (((((M : ℕ) : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I)) -
          (((((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ) : ℂ) ^
            (-(t : ℂ) * Complex.I)))) /
        (-(t : ℂ) * Complex.I) := by
  exact Eq.trans
    (boundaryLineOnePointRealParam_logarithmicPhase_postCutoff_mainIntegral_eq_intervalIntegral_ownerGap
      t hM)
    (boundaryLineOnePointRealParam_logarithmicPhase_postCutoff_intervalIntegral_eq_antiderivativeDifference_ownerGap
      t ht hM)

/-- Endpoint norm estimate for the antiderivative difference. -/
theorem boundaryLineOnePointRealParam_logarithmicPhase_postCutoff_antiderivativeDifference_norm_le_two_ownerGap
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    {M : ℕ}
    (hM : ⌊2 + ‖t‖⌋₊ ≤ M) :
    ‖(((((M : ℕ) : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I)) -
          (((((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ) : ℂ) ^
            (-(t : ℂ) * Complex.I)))) /
        (-(t : ℂ) * Complex.I)‖ ≤
      (2 : ℝ) := by
  let A : ℂ := (((M : ℕ) : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I)
  let B : ℂ :=
    ((((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I))
  let D : ℂ := -(t : ℂ) * Complex.I
  have hA : ‖A‖ ≤ (1 : ℝ) :=
    logarithmicPhase_nat_sample_norm_le_one t M
  have hB : ‖B‖ ≤ (1 : ℝ) :=
    logarithmicPhase_nat_sample_norm_le_one t ⌊2 + ‖t‖⌋₊
  have hnum_triangle : ‖A - B‖ ≤ ‖A‖ + ‖B‖ :=
    norm_sub_le A B
  have hnum_add_le_two : ‖A‖ + ‖B‖ ≤ (2 : ℝ) := by
    calc
      ‖A‖ + ‖B‖ ≤ (1 : ℝ) + 1 :=
        add_le_add hA hB
      _ = (2 : ℝ) := by
        exact one_add_one_eq_two
  have hnum_le_two : ‖A - B‖ ≤ (2 : ℝ) :=
    le_trans hnum_triangle hnum_add_le_two
  have hD_norm : ‖D‖ = ‖t‖ :=
    logarithmicPhaseFunction_derivative_numerator_norm t
  have hquot_norm : ‖(A - B) / D‖ = ‖A - B‖ / ‖D‖ :=
    norm_div (A - B) D
  have hquot_le_two_div_normD : ‖(A - B) / D‖ ≤ (2 : ℝ) / ‖D‖ := by
    exact Eq.subst
      (motive := fun r : ℝ => r ≤ (2 : ℝ) / ‖D‖)
      hquot_norm.symm
      (div_le_div_of_nonneg_right hnum_le_two (norm_nonneg D))
  have htwo_div_norm_t_le_two : (2 : ℝ) / ‖t‖ ≤ (2 : ℝ) := by
    have hinv_le_one : ‖t‖⁻¹ ≤ (1 : ℝ) :=
      inv_le_one_of_one_le₀ ht
    calc
      (2 : ℝ) / ‖t‖ = 2 * ‖t‖⁻¹ := by
        exact Eq.trans (div_eq_mul_inv 2 ‖t‖) rfl
      _ ≤ 2 * 1 := by
        exact mul_le_mul_of_nonneg_left hinv_le_one
          (show (0 : ℝ) ≤ 2 from zero_le_two)
      _ = (2 : ℝ) := by
        exact mul_one 2
  have hquot_le_two : ‖(A - B) / D‖ ≤ (2 : ℝ) := by
    exact le_trans hquot_le_two_div_normD
      (Eq.subst
        (motive := fun r : ℝ => (2 : ℝ) / r ≤ (2 : ℝ))
        hD_norm.symm
        htwo_div_norm_t_le_two)
  exact hquot_le_two

/-- Owner sink for the antiderivative estimate
`∫ x^(-1-it) dx = (M^(-it) - N^(-it))/(-it)`.

The sharp elementary bound supplied by this identity is `2 / |t|`, hence `≤ 2`
on the public range `1 ≤ |t|`.  A unit bound would require a stronger lower
bound on `|t|` or extra arithmetic information about the two integer endpoint
phases. -/
theorem boundaryLineOnePointRealParam_logarithmicPhase_postCutoff_mainIntegral_norm_le_two_ownerGap
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    {M : ℕ}
    (hM : ⌊2 + ‖t‖⌋₊ ≤ M) :
    ‖∫ x in Set.Ioc (((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ)) (((M : ℕ) : ℝ)),
        (((x : ℝ) : ℂ) ^ (-boundaryLineOnePointRealParam t))‖ ≤
      (2 : ℝ) := by
  have hidentity :
      (∫ x in Set.Ioc (((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ)) (((M : ℕ) : ℝ)),
          (((x : ℝ) : ℂ) ^ (-boundaryLineOnePointRealParam t))) =
        (((((M : ℕ) : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I)) -
            (((((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ) : ℂ) ^
              (-(t : ℂ) * Complex.I)))) /
          (-(t : ℂ) * Complex.I) :=
    boundaryLineOnePointRealParam_logarithmicPhase_postCutoff_mainIntegral_eq_antiderivativeDifference_ownerGap
      t ht hM
  have hbound :
      ‖(((((M : ℕ) : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I)) -
            (((((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ) : ℂ) ^
              (-(t : ℂ) * Complex.I)))) /
          (-(t : ℂ) * Complex.I)‖ ≤
        (2 : ℝ) :=
    boundaryLineOnePointRealParam_logarithmicPhase_postCutoff_antiderivativeDifference_norm_le_two_ownerGap
      t ht hM
  exact Eq.subst
    (motive := fun z : ℂ => ‖z‖ ≤ (2 : ℝ))
    hidentity.symm
    hbound

/-- Public main-integral component bound with the honest antiderivative
constant. -/
theorem boundaryLineOnePointRealParam_logarithmicPhase_postCutoff_mainIntegral_norm_le_two
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    {M : ℕ}
    (hM : ⌊2 + ‖t‖⌋₊ ≤ M) :
    ‖∫ x in Set.Ioc (((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ)) (((M : ℕ) : ℝ)),
        (((x : ℝ) : ℂ) ^ (-boundaryLineOnePointRealParam t))‖ ≤
      (2 : ℝ) := by
  exact
    boundaryLineOnePointRealParam_logarithmicPhase_postCutoff_mainIntegral_norm_le_two_ownerGap
      t ht hM

/-- Lower half-endpoint component in the post-cutoff Euler-Maclaurin tail. -/
theorem boundaryLineOnePointRealParam_logarithmicPhase_postCutoff_lowerHalfEndpoint_norm_le_one
    (t : ℝ) :
    ‖(-(1 / 2 : ℂ) *
        ((((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ) : ℂ) ^
          (-boundaryLineOnePointRealParam t)))‖ ≤
      (1 : ℝ) := by
  exact
    boundaryLineOnePointRealParam_logarithmicPhase_tail_halfEndpoint_norm_le_one
      t
      (boundaryLineOnePointRealParam_cutoff_pos t)
      (-(1 / 2 : ℂ))
      boundaryGrowth_complex_neg_one_div_two_norm_le_one

/-- Upper half-endpoint component in the post-cutoff Euler-Maclaurin tail. -/
theorem boundaryLineOnePointRealParam_logarithmicPhase_postCutoff_upperHalfEndpoint_norm_le_one
    (t : ℝ)
    {M : ℕ}
    (hM : ⌊2 + ‖t‖⌋₊ ≤ M) :
    ‖((1 / 2 : ℂ) *
        ((((M : ℕ) : ℝ) : ℂ) ^
          (-boundaryLineOnePointRealParam t)))‖ ≤
      (1 : ℝ) := by
  have hcutoff_pos : 0 < ⌊2 + ‖t‖⌋₊ :=
    boundaryLineOnePointRealParam_cutoff_pos t
  have hM_pos : 0 < M :=
    lt_of_lt_of_le hcutoff_pos hM
  exact
    boundaryLineOnePointRealParam_logarithmicPhase_tail_halfEndpoint_norm_le_one
      t
      hM_pos
      (1 / 2 : ℂ)
      boundaryGrowth_complex_one_div_two_norm_le_one

/-- Measure-to-interval transport for the real inverse-square majorant on the
post-cutoff interval. -/
theorem boundaryLineOnePointRealParam_logarithmicPhase_postCutoff_inverseSquareMajorant_eq_intervalIntegral
    (t : ℝ)
    {M : ℕ}
    (hM : ⌊2 + ‖t‖⌋₊ ≤ M) :
    (∫ x in Set.Ioc (((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ)) (((M : ℕ) : ℝ)),
        (1 + ‖t‖) / x ^ 2) =
      ∫ x in (((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ))..(((M : ℕ) : ℝ)),
        (1 + ‖t‖) / x ^ 2 := by
  have hle :
      (((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ)) ≤ (((M : ℕ) : ℝ)) :=
    Nat.cast_le.mpr hM
  exact
    (intervalIntegral.integral_of_le
      (f := fun x : ℝ => (1 + ‖t‖) / x ^ 2)
      hle).symm

/-- Pointwise derivative of the inverse-square majorant antiderivative on the
positive half-line. -/
theorem boundaryLineOnePointRealParam_logarithmicPhase_postCutoff_inverseSquareMajorant_antiderivative_hasDerivAt
    (t : ℝ)
    {x : ℝ}
    (hx : 0 < x) :
    HasDerivAt
      (fun y : ℝ => -((1 + ‖t‖) * y⁻¹))
      ((1 + ‖t‖) / x ^ 2)
      x := by
  have hx_ne : x ≠ 0 := ne_of_gt hx
  have hinv :
      HasDerivAt
        (fun y : ℝ => y⁻¹)
        (-(x ^ 2)⁻¹)
        x :=
    hasDerivAt_inv hx_ne
  have hmul :
      HasDerivAt
        (fun y : ℝ => (1 + ‖t‖) * y⁻¹)
        ((1 + ‖t‖) * (-(x ^ 2)⁻¹))
        x :=
    hinv.const_mul (1 + ‖t‖)
  have hneg :
      HasDerivAt
        (fun y : ℝ => -((1 + ‖t‖) * y⁻¹))
        (-((1 + ‖t‖) * (-(x ^ 2)⁻¹)))
        x :=
    hmul.neg
  have halg :
      (-((1 + ‖t‖) * (-(x ^ 2)⁻¹))) =
        (1 + ‖t‖) / x ^ 2 := by
    calc
      (-((1 + ‖t‖) * (-(x ^ 2)⁻¹))) =
          -(-((1 + ‖t‖) * (x ^ 2)⁻¹)) := by
        exact
          congrArg
            (fun y : ℝ => -y)
            (mul_neg (1 + ‖t‖) ((x ^ 2)⁻¹))
      _ =
          (1 + ‖t‖) * (x ^ 2)⁻¹ := by
        exact neg_neg ((1 + ‖t‖) * (x ^ 2)⁻¹)
      _ = (1 + ‖t‖) / x ^ 2 := by
        exact (div_eq_mul_inv (1 + ‖t‖) (x ^ 2)).symm
  exact halg ▸ hneg

/-- The post-cutoff interval stays in the positive half-line. -/
theorem boundaryLineOnePointRealParam_logarithmicPhase_postCutoff_mem_interval_pos
    (t : ℝ)
    {M : ℕ}
    (hM : ⌊2 + ‖t‖⌋₊ ≤ M)
    {x : ℝ}
    (hx :
      x ∈
        Set.uIcc
          (((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ))
          (((M : ℕ) : ℝ))) :
    0 < x := by
  have hle :
      (((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ)) ≤ (((M : ℕ) : ℝ)) :=
    Nat.cast_le.mpr hM
  have hinterval :
      x ∈
        Set.Icc
          (((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ))
          (((M : ℕ) : ℝ)) :=
    (Set.uIcc_of_le hle) ▸ hx
  have hleft_le_x :
      (((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ)) ≤ x :=
    hinterval.1
  have hcutoff_pos_nat : 0 < ⌊2 + ‖t‖⌋₊ :=
    boundaryLineOnePointRealParam_cutoff_pos t
  have hcutoff_pos_real :
      (0 : ℝ) < (((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ)) :=
    Nat.cast_pos.mpr hcutoff_pos_nat
  exact lt_of_lt_of_le hcutoff_pos_real hleft_le_x

/-- Interval integrability of the inverse-square majorant on the positive
post-cutoff interval. -/
theorem boundaryLineOnePointRealParam_logarithmicPhase_postCutoff_inverseSquareMajorant_intervalIntegrable
    (t : ℝ)
    {M : ℕ}
    (hM : ⌊2 + ‖t‖⌋₊ ≤ M) :
    IntervalIntegrable
      (fun x : ℝ => (1 + ‖t‖) / x ^ 2)
      volume
      (((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ))
      (((M : ℕ) : ℝ)) := by
  let a : ℝ := (((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ))
  let b : ℝ := (((M : ℕ) : ℝ))
  have hden_ne :
      ∀ x ∈ Set.uIcc a b, x ^ 2 ≠ 0 := by
    intro x hx
    have hx_pos :
        0 < x :=
      boundaryLineOnePointRealParam_logarithmicPhase_postCutoff_mem_interval_pos
        t
        hM
        hx
    have hx_ne : x ≠ 0 := ne_of_gt hx_pos
    exact pow_ne_zero 2 hx_ne
  have hnum_cont :
      ContinuousOn
        (fun _x : ℝ => (1 + ‖t‖))
        (Set.uIcc a b) :=
    continuous_const.continuousOn
  have hden_cont :
      ContinuousOn
        (fun x : ℝ => x ^ 2)
        (Set.uIcc a b) :=
    (continuous_id.pow 2).continuousOn
  have hquot_cont :
      ContinuousOn
        (fun x : ℝ => (1 + ‖t‖) / x ^ 2)
        (Set.uIcc a b) :=
    hnum_cont.div hden_cont hden_ne
  exact hquot_cont.intervalIntegrable

/-- Interval-integral FTC before endpoint algebra normalization. -/
theorem boundaryLineOnePointRealParam_logarithmicPhase_postCutoff_inverseSquareMajorant_intervalIntegral_eq_rawAntiderivative
    (t : ℝ)
    {M : ℕ}
    (hM : ⌊2 + ‖t‖⌋₊ ≤ M) :
    (∫ x in (((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ))..(((M : ℕ) : ℝ)),
        (1 + ‖t‖) / x ^ 2) =
      (-((1 + ‖t‖) * (((M : ℕ) : ℝ))⁻¹)) -
        (-((1 + ‖t‖) * (((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ))⁻¹)) := by
  exact
    intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun x hx =>
        boundaryLineOnePointRealParam_logarithmicPhase_postCutoff_inverseSquareMajorant_antiderivative_hasDerivAt
          t
          (boundaryLineOnePointRealParam_logarithmicPhase_postCutoff_mem_interval_pos
            t hM hx))
      (boundaryLineOnePointRealParam_logarithmicPhase_postCutoff_inverseSquareMajorant_intervalIntegrable
        t hM)

/-- Endpoint algebra for the inverse-square antiderivative. -/
theorem boundaryLineOnePointRealParam_logarithmicPhase_postCutoff_inverseSquareMajorant_rawAntiderivative_eq_endpointDifference
    (t : ℝ)
    {M : ℕ} :
    (-((1 + ‖t‖) * (((M : ℕ) : ℝ))⁻¹)) -
        (-((1 + ‖t‖) * (((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ))⁻¹)) =
      (1 + ‖t‖) *
        ((((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ))⁻¹ - (((M : ℕ) : ℝ))⁻¹) := by
  let c : ℝ := 1 + ‖t‖
  let a : ℝ := (((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ))⁻¹
  let b : ℝ := (((M : ℕ) : ℝ))⁻¹
  calc
    (-(c * b)) - (-(c * a)) = (-(c * b)) + (c * a) := by
      exact sub_neg_eq_add (-(c * b)) (c * a)
    _ = (c * a) + (-(c * b)) := by
      exact add_comm (-(c * b)) (c * a)
    _ = (c * a) - (c * b) := by
      exact (sub_eq_add_neg (c * a) (c * b)).symm
    _ = c * (a - b) := by
      exact (mul_sub c a b).symm

/-- Interval-integral FTC identity for the real inverse-square majorant. -/
theorem boundaryLineOnePointRealParam_logarithmicPhase_postCutoff_inverseSquareMajorant_intervalIntegral_eq_endpointDifference_ownerGap
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    {M : ℕ}
    (hM : ⌊2 + ‖t‖⌋₊ ≤ M) :
    (∫ x in (((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ))..(((M : ℕ) : ℝ)),
        (1 + ‖t‖) / x ^ 2) =
      (1 + ‖t‖) *
        ((((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ))⁻¹ - (((M : ℕ) : ℝ))⁻¹) := by
  exact Eq.trans
    (boundaryLineOnePointRealParam_logarithmicPhase_postCutoff_inverseSquareMajorant_intervalIntegral_eq_rawAntiderivative
      t hM)
    (boundaryLineOnePointRealParam_logarithmicPhase_postCutoff_inverseSquareMajorant_rawAntiderivative_eq_endpointDifference
      t)

/-- The boundary-line parameter has size at most the elementary scalar
`1 + |t|`. -/
theorem boundaryLineOnePointRealParam_norm_le_one_add_norm
    (t : ℝ) :
    ‖boundaryLineOnePointRealParam t‖ ≤ (1 : ℝ) + ‖t‖ := by
  have hparam :
      boundaryLineOnePointRealParam t = (1 : ℂ) + (t : ℂ) * Complex.I := by
    have hre :
        (boundaryLineOnePointRealParam t).re =
          ((1 : ℂ) + (t : ℂ) * Complex.I).re := by
      calc
        (boundaryLineOnePointRealParam t).re = (1 : ℝ) :=
          boundaryLineOnePointRealParam_re t
        _ = (1 : ℂ).re + (0 : ℝ) := by
          exact (add_zero (1 : ℝ)).symm
        _ = (1 : ℂ).re + (-(t : ℂ).im) := by
          exact congrArg (fun y : ℝ => (1 : ℂ).re + y)
            (Eq.trans neg_zero.symm
              (congrArg Neg.neg (Complex.ofReal_im t).symm))
        _ = (1 : ℂ).re + ((t : ℂ) * Complex.I).re := by
          exact congrArg (fun y : ℝ => (1 : ℂ).re + y)
            (Complex.mul_I_re (t : ℂ)).symm
        _ = ((1 : ℂ) + (t : ℂ) * Complex.I).re := by
          exact (Complex.add_re (1 : ℂ) ((t : ℂ) * Complex.I)).symm
    have him :
        (boundaryLineOnePointRealParam t).im =
          ((1 : ℂ) + (t : ℂ) * Complex.I).im := by
      calc
        (boundaryLineOnePointRealParam t).im = t :=
          boundaryLineOnePointRealParam_im t
        _ = (0 : ℝ) + t := by
          exact (zero_add t).symm
        _ = (1 : ℂ).im + (t : ℂ).re := by
          exact congrArg₂ (fun u v : ℝ => u + v)
            (Complex.ofReal_im 1).symm
            (Complex.ofReal_re t).symm
        _ = (1 : ℂ).im + ((t : ℂ) * Complex.I).im := by
          exact congrArg (fun y : ℝ => (1 : ℂ).im + y)
            (Complex.mul_I_im (t : ℂ)).symm
        _ = ((1 : ℂ) + (t : ℂ) * Complex.I).im := by
          exact (Complex.add_im (1 : ℂ) ((t : ℂ) * Complex.I)).symm
    exact Complex.ext hre him
  have htriangle :
      ‖(1 : ℂ) + (t : ℂ) * Complex.I‖ ≤
        ‖(1 : ℂ)‖ + ‖(t : ℂ) * Complex.I‖ :=
    norm_add_le (1 : ℂ) ((t : ℂ) * Complex.I)
  have hone : ‖(1 : ℂ)‖ = (1 : ℝ) :=
    norm_one
  have htI : ‖(t : ℂ) * Complex.I‖ = ‖t‖ := by
    have hmul :
        ‖(t : ℂ) * Complex.I‖ = ‖(t : ℂ)‖ * ‖Complex.I‖ :=
      norm_mul (t : ℂ) Complex.I
    have hI : ‖Complex.I‖ = (1 : ℝ) :=
      RCLike.norm_I_of_ne_zero (K := ℂ) Complex.I_ne_zero
    have ht : ‖(t : ℂ)‖ = ‖t‖ :=
      RCLike.norm_ofReal t
    calc
      ‖(t : ℂ) * Complex.I‖ = ‖(t : ℂ)‖ * ‖Complex.I‖ :=
        hmul
      _ = ‖(t : ℂ)‖ * (1 : ℝ) := by
        exact congrArg (fun y : ℝ => ‖(t : ℂ)‖ * y) hI
      _ = ‖(t : ℂ)‖ := by
        exact mul_one ‖(t : ℂ)‖
      _ = ‖t‖ :=
        ht
  have hright :
      ‖(1 : ℂ)‖ + ‖(t : ℂ) * Complex.I‖ = (1 : ℝ) + ‖t‖ := by
    exact congrArg₂ HAdd.hAdd hone htI
  exact Eq.subst
    (motive := fun z : ℂ => ‖z‖ ≤ (1 : ℝ) + ‖t‖)
    hparam.symm
    (Eq.subst
      (motive := fun r : ℝ => ‖(1 : ℂ) + (t : ℂ) * Complex.I‖ ≤ r)
      hright
      htriangle)

/-- The post-cutoff `Ioc` interval lies above `1`. -/
theorem boundaryLineOnePointRealParam_logarithmicPhase_postCutoff_one_le_of_mem_Ioc
    (t : ℝ)
    {M : ℕ}
    (hM : ⌊2 + ‖t‖⌋₊ ≤ M)
    {x : ℝ}
    (hx :
      x ∈
        Set.Ioc
          (((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ))
          (((M : ℕ) : ℝ))) :
    (1 : ℝ) ≤ x := by
  have hx_u :
      x ∈
        Set.uIcc
          (((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ))
          (((M : ℕ) : ℝ)) := by
    have hle :
        (((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ)) ≤ (((M : ℕ) : ℝ)) :=
      Nat.cast_le.mpr hM
    have hx_icc :
        x ∈
          Set.Icc
            (((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ))
            (((M : ℕ) : ℝ)) :=
      ⟨le_of_lt hx.1, hx.2⟩
    exact (Set.uIcc_of_le hle).symm ▸ hx_icc
  have hx_pos :
      0 < x :=
    boundaryLineOnePointRealParam_logarithmicPhase_postCutoff_mem_interval_pos
      t hM hx_u
  have hcutoff_le_x :
      (((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ)) ≤ x :=
    le_of_lt hx.1
  have hcutoff_ge_one :
      (1 : ℝ) ≤ (((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ)) := by
    have hcutoff_pos_nat : 0 < ⌊2 + ‖t‖⌋₊ :=
      boundaryLineOnePointRealParam_cutoff_pos t
    have hone_le_nat : 1 ≤ ⌊2 + ‖t‖⌋₊ :=
      Nat.succ_le_of_lt hcutoff_pos_nat
    exact Nat.cast_le.mpr hone_le_nat
  exact le_trans hcutoff_ge_one hcutoff_le_x

/-- Positive real powers with exponent `-2` are inverse squares. -/
theorem boundaryGrowth_real_rpow_neg_two_eq_inv_sq
    {x : ℝ}
    (hx : 0 < x) :
    x ^ (-(2 : ℝ)) = (x ^ 2)⁻¹ := by
  have hneg :
      x ^ (-(2 : ℝ)) = (x ^ (2 : ℝ))⁻¹ :=
    Real.rpow_neg (le_of_lt hx) 2
  have htwo :
      x ^ (2 : ℝ) = x ^ (2 : ℕ) :=
    Real.rpow_natCast x 2
  exact Eq.trans hneg (congrArg Inv.inv htwo)

/-- Pointwise norm of the Bernoulli derivative kernel before replacing
`x ^ (-2)` by the inverse-square scalar. -/
theorem boundaryLineOnePointRealParam_logarithmicPhase_postCutoff_bernoulliKernel_norm_le_one_add_norm_mul_rpow
    (t : ℝ)
    {M : ℕ}
    (hM : ⌊2 + ‖t‖⌋₊ ≤ M) :
    ∀ x ∈ Set.Ioc (((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ)) (((M : ℕ) : ℝ)),
      ‖((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) *
          (-boundaryLineOnePointRealParam t *
            (((x : ℝ) : ℂ) ^
              (-(boundaryLineOnePointRealParam t + 1))))‖ ≤
        (1 + ‖t‖) * x ^ (-(2 : ℝ)) := by
  intro x hx
  have hx_one :
      (1 : ℝ) ≤ x :=
    boundaryLineOnePointRealParam_logarithmicPhase_postCutoff_one_le_of_mem_Ioc
      t hM hx
  have hx_pos :
      0 < x :=
    lt_of_lt_of_le zero_lt_one hx_one
  have hB :
      ‖((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ)‖ ≤ 1 :=
    eulerMaclaurinFirstPeriodicBernoulli_norm_cast_le_one_finite x
  have hparam :
      ‖boundaryLineOnePointRealParam t‖ ≤ (1 : ℝ) + ‖t‖ :=
    boundaryLineOnePointRealParam_norm_le_one_add_norm t
  have hre :
      (1 : ℝ) ≤ (boundaryLineOnePointRealParam t).re := by
    exact le_of_eq (boundaryLineOnePointRealParam_re t).symm
  have hcpow :
      ‖((x : ℝ) : ℂ) ^
          (-(boundaryLineOnePointRealParam t + 1))‖ ≤
        x ^ (-(1 + 1 : ℝ)) :=
    eulerMaclaurin_norm_real_cpow_le_rpow_of_re_lower
      hx_pos hx_one (boundaryLineOnePointRealParam t) hre
  have hexponent :
      (-(1 + 1 : ℝ)) = (-(2 : ℝ)) := by
    exact congrArg Neg.neg (one_add_one_eq_two : (1 : ℝ) + 1 = 2)
  have hcpow_two :
      ‖((x : ℝ) : ℂ) ^
          (-(boundaryLineOnePointRealParam t + 1))‖ ≤
        x ^ (-(2 : ℝ)) :=
    Eq.subst
      (motive := fun e : ℝ =>
        ‖((x : ℝ) : ℂ) ^
          (-(boundaryLineOnePointRealParam t + 1))‖ ≤ x ^ e)
      hexponent
      hcpow
  have hpow_nonneg :
      0 ≤ x ^ (-(2 : ℝ)) :=
    Real.rpow_nonneg (le_of_lt hx_pos) (-(2 : ℝ))
  have hparam_nonneg :
      0 ≤ ‖boundaryLineOnePointRealParam t‖ :=
    norm_nonneg (boundaryLineOnePointRealParam t)
  have hinner_bound :
      ‖-boundaryLineOnePointRealParam t *
          (((x : ℝ) : ℂ) ^
            (-(boundaryLineOnePointRealParam t + 1)))‖ ≤
        ((1 : ℝ) + ‖t‖) * x ^ (-(2 : ℝ)) := by
    have hinner_norm :
        ‖-boundaryLineOnePointRealParam t *
            (((x : ℝ) : ℂ) ^
              (-(boundaryLineOnePointRealParam t + 1)))‖ =
          ‖boundaryLineOnePointRealParam t‖ *
            ‖((x : ℝ) : ℂ) ^
              (-(boundaryLineOnePointRealParam t + 1))‖ := by
      have hmul :
          ‖-boundaryLineOnePointRealParam t *
              (((x : ℝ) : ℂ) ^
                (-(boundaryLineOnePointRealParam t + 1)))‖ =
            ‖-boundaryLineOnePointRealParam t‖ *
              ‖((x : ℝ) : ℂ) ^
                (-(boundaryLineOnePointRealParam t + 1))‖ :=
        norm_mul
          (-boundaryLineOnePointRealParam t)
          (((x : ℝ) : ℂ) ^
            (-(boundaryLineOnePointRealParam t + 1)))
      have hneg :
          ‖-boundaryLineOnePointRealParam t‖ =
            ‖boundaryLineOnePointRealParam t‖ :=
        norm_neg (boundaryLineOnePointRealParam t)
      exact Eq.trans hmul
        (congrArg
          (fun r : ℝ =>
            r *
              ‖((x : ℝ) : ℂ) ^
                (-(boundaryLineOnePointRealParam t + 1))‖)
          hneg)
    have hproduct :
        ‖boundaryLineOnePointRealParam t‖ *
            ‖((x : ℝ) : ℂ) ^
              (-(boundaryLineOnePointRealParam t + 1))‖ ≤
          ((1 : ℝ) + ‖t‖) * x ^ (-(2 : ℝ)) :=
      mul_le_mul hparam hcpow_two
        (norm_nonneg
          (((x : ℝ) : ℂ) ^
            (-(boundaryLineOnePointRealParam t + 1))))
        hparam_nonneg
    exact Eq.subst
      (motive := fun r : ℝ =>
        r ≤ ((1 : ℝ) + ‖t‖) * x ^ (-(2 : ℝ)))
      hinner_norm.symm
      hproduct
  have houter_norm :
      ‖((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) *
          (-boundaryLineOnePointRealParam t *
            (((x : ℝ) : ℂ) ^
              (-(boundaryLineOnePointRealParam t + 1))))‖ =
        ‖((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ)‖ *
          ‖-boundaryLineOnePointRealParam t *
            (((x : ℝ) : ℂ) ^
              (-(boundaryLineOnePointRealParam t + 1)))‖ :=
    norm_mul
      ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ)
      (-boundaryLineOnePointRealParam t *
        (((x : ℝ) : ℂ) ^
          (-(boundaryLineOnePointRealParam t + 1))))
  have hproduct :
      ‖((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ)‖ *
          ‖-boundaryLineOnePointRealParam t *
            (((x : ℝ) : ℂ) ^
              (-(boundaryLineOnePointRealParam t + 1)))‖ ≤
        1 * (((1 : ℝ) + ‖t‖) * x ^ (-(2 : ℝ))) :=
    mul_le_mul hB hinner_bound
      (norm_nonneg
        (-boundaryLineOnePointRealParam t *
          (((x : ℝ) : ℂ) ^
            (-(boundaryLineOnePointRealParam t + 1)))))
      (zero_le_one : (0 : ℝ) ≤ 1)
  exact Eq.subst
    (motive := fun r : ℝ =>
      r ≤ ((1 : ℝ) + ‖t‖) * x ^ (-(2 : ℝ)))
    houter_norm.symm
    (Eq.subst
      (motive := fun r : ℝ =>
        ‖((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ)‖ *
            ‖-boundaryLineOnePointRealParam t *
              (((x : ℝ) : ℂ) ^
                (-(boundaryLineOnePointRealParam t + 1)))‖ ≤ r)
      (one_mul (((1 : ℝ) + ‖t‖) * x ^ (-(2 : ℝ))))
      hproduct)

/-- Scalar normalization for the pointwise Bernoulli derivative majorant on
the positive post-cutoff interval. -/
theorem boundaryLineOnePointRealParam_logarithmicPhase_postCutoff_one_add_norm_mul_rpow_le_realMajorant
    (t : ℝ)
    {M : ℕ}
    (hM : ⌊2 + ‖t‖⌋₊ ≤ M) :
    ∀ x ∈ Set.Ioc (((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ)) (((M : ℕ) : ℝ)),
      (1 + ‖t‖) * x ^ (-(2 : ℝ)) ≤
        (1 + ‖t‖) / x ^ 2 := by
  intro x hx
  have hx_u :
      x ∈
        Set.uIcc
          (((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ))
          (((M : ℕ) : ℝ)) := by
    have hle :
        (((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ)) ≤ (((M : ℕ) : ℝ)) :=
      Nat.cast_le.mpr hM
    have hx_icc :
        x ∈
          Set.Icc
            (((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ))
            (((M : ℕ) : ℝ)) :=
      ⟨le_of_lt hx.1, hx.2⟩
    exact (Set.uIcc_of_le hle).symm ▸ hx_icc
  have hx_pos :
      0 < x :=
    boundaryLineOnePointRealParam_logarithmicPhase_postCutoff_mem_interval_pos
      t hM hx_u
  have hrpow :
      x ^ (-(2 : ℝ)) = (x ^ 2)⁻¹ :=
    boundaryGrowth_real_rpow_neg_two_eq_inv_sq hx_pos
  have hdiv :
      (1 + ‖t‖) / x ^ 2 = (1 + ‖t‖) * (x ^ 2)⁻¹ :=
    div_eq_mul_inv (1 + ‖t‖) (x ^ 2)
  exact le_of_eq
    (Eq.trans
      (congrArg (fun y : ℝ => (1 + ‖t‖) * y) hrpow)
      hdiv.symm)

/-- Norm domination for the periodic-Bernoulli remainder by the elementary
real derivative majorant. -/
theorem boundaryLineOnePointRealParam_logarithmicPhase_postCutoff_bernoulliRemainder_pointwise_norm_le_realMajorant_ownerGap
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    {M : ℕ}
    (hM : ⌊2 + ‖t‖⌋₊ ≤ M) :
    ∀ x ∈ Set.Ioc (((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ)) (((M : ℕ) : ℝ)),
      ‖((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) *
          (-boundaryLineOnePointRealParam t *
            (((x : ℝ) : ℂ) ^
              (-(boundaryLineOnePointRealParam t + 1))))‖ ≤
        (1 + ‖t‖) / x ^ 2 := by
  intro x hx
  exact le_trans
    (boundaryLineOnePointRealParam_logarithmicPhase_postCutoff_bernoulliKernel_norm_le_one_add_norm_mul_rpow
      t hM x hx)
    (boundaryLineOnePointRealParam_logarithmicPhase_postCutoff_one_add_norm_mul_rpow_le_realMajorant
      t hM x hx)

/-- Integrability of the scalar inverse-square majorant on the post-cutoff
`Ioc` interval, in the form required by Bochner norm domination. -/
theorem boundaryLineOnePointRealParam_logarithmicPhase_postCutoff_inverseSquareMajorant_integrable_restrict_Ioc
    (t : ℝ)
    {M : ℕ}
    (hM : ⌊2 + ‖t‖⌋₊ ≤ M) :
    Integrable
      (fun x : ℝ => (1 + ‖t‖) / x ^ 2)
      (volume.restrict
        (Set.Ioc
          (((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ))
          (((M : ℕ) : ℝ)))) := by
  have hle :
      (((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ)) ≤ (((M : ℕ) : ℝ)) :=
    Nat.cast_le.mpr hM
  exact
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hle).mp
      (boundaryLineOnePointRealParam_logarithmicPhase_postCutoff_inverseSquareMajorant_intervalIntegrable
        t hM)

/-- Bochner norm domination for the post-cutoff Bernoulli remainder over the
finite interval. -/
theorem boundaryLineOnePointRealParam_logarithmicPhase_postCutoff_bernoulliRemainder_integral_norm_le_of_pointwise_realMajorant_core
    (t : ℝ)
    {M : ℕ}
    (hM : ⌊2 + ‖t‖⌋₊ ≤ M)
    (hpoint :
      ∀ x ∈ Set.Ioc (((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ)) (((M : ℕ) : ℝ)),
        ‖((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) *
            (-boundaryLineOnePointRealParam t *
              (((x : ℝ) : ℂ) ^
                (-(boundaryLineOnePointRealParam t + 1))))‖ ≤
          (1 + ‖t‖) / x ^ 2) :
    ‖∫ x in Set.Ioc (((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ)) (((M : ℕ) : ℝ)),
        ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) *
          (-boundaryLineOnePointRealParam t *
            (((x : ℝ) : ℂ) ^
              (-(boundaryLineOnePointRealParam t + 1))))‖ ≤
      ∫ x in Set.Ioc (((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ)) (((M : ℕ) : ℝ)),
        (1 + ‖t‖) / x ^ 2 := by
  let s : Set ℝ :=
    Set.Ioc
      (((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ))
      (((M : ℕ) : ℝ))
  let f : ℝ → ℂ := fun x =>
    ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) *
      (-boundaryLineOnePointRealParam t *
        (((x : ℝ) : ℂ) ^
          (-(boundaryLineOnePointRealParam t + 1))))
  let g : ℝ → ℝ := fun x => (1 + ‖t‖) / x ^ 2
  have hg :
      Integrable g (volume.restrict s) :=
    boundaryLineOnePointRealParam_logarithmicPhase_postCutoff_inverseSquareMajorant_integrable_restrict_Ioc
      t hM
  have hbound :
      ∀ᵐ x ∂volume.restrict s, ‖f x‖ ≤ g x :=
    (ae_restrict_mem measurableSet_Ioc).mono
      (fun x hx => hpoint x hx)
  exact norm_integral_le_of_norm_le hg hbound

theorem boundaryLineOnePointRealParam_logarithmicPhase_postCutoff_bernoulliRemainder_integral_norm_le_of_pointwise_realMajorant_ownerGap
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    {M : ℕ}
    (hM : ⌊2 + ‖t‖⌋₊ ≤ M)
    (hpoint :
      ∀ x ∈ Set.Ioc (((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ)) (((M : ℕ) : ℝ)),
        ‖((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) *
            (-boundaryLineOnePointRealParam t *
              (((x : ℝ) : ℂ) ^
                (-(boundaryLineOnePointRealParam t + 1))))‖ ≤
          (1 + ‖t‖) / x ^ 2) :
    ‖∫ x in Set.Ioc (((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ)) (((M : ℕ) : ℝ)),
        ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) *
          (-boundaryLineOnePointRealParam t *
            (((x : ℝ) : ℂ) ^
              (-(boundaryLineOnePointRealParam t + 1))))‖ ≤
      ∫ x in Set.Ioc (((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ)) (((M : ℕ) : ℝ)),
        (1 + ‖t‖) / x ^ 2 := by
  exact
    boundaryLineOnePointRealParam_logarithmicPhase_postCutoff_bernoulliRemainder_integral_norm_le_of_pointwise_realMajorant_core
      t hM hpoint

theorem boundaryLineOnePointRealParam_logarithmicPhase_postCutoff_bernoulliRemainder_norm_le_realMajorant_ownerGap
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    {M : ℕ}
    (hM : ⌊2 + ‖t‖⌋₊ ≤ M) :
    ‖∫ x in Set.Ioc (((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ)) (((M : ℕ) : ℝ)),
        ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) *
          (-boundaryLineOnePointRealParam t *
            (((x : ℝ) : ℂ) ^
              (-(boundaryLineOnePointRealParam t + 1))))‖ ≤
      ∫ x in Set.Ioc (((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ)) (((M : ℕ) : ℝ)),
        (1 + ‖t‖) / x ^ 2 := by
  exact
    boundaryLineOnePointRealParam_logarithmicPhase_postCutoff_bernoulliRemainder_integral_norm_le_of_pointwise_realMajorant_ownerGap
      t ht hM
      (boundaryLineOnePointRealParam_logarithmicPhase_postCutoff_bernoulliRemainder_pointwise_norm_le_realMajorant_ownerGap
        t ht hM)

/-- The canonical Abel cutoff is at least `1 + |t|` after coercion to `ℝ`. -/
theorem boundaryLineOnePointRealParam_postCutoff_one_add_norm_le_cutoff
    (t : ℝ) :
    (1 : ℝ) + ‖t‖ ≤ ((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ) := by
  have hsub_lt :
      (2 + ‖t‖ : ℝ) - 1 < ((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ) :=
    Nat.sub_one_lt_floor (2 + ‖t‖)
  have hone_add_eq :
      (1 : ℝ) + ‖t‖ = (2 + ‖t‖ : ℝ) - 1 := by
    calc
      (1 : ℝ) + ‖t‖ = (2 - 1) + ‖t‖ := by
        exact congrArg (fun y : ℝ => y + ‖t‖)
          (show (1 : ℝ) = 2 - 1 by
            exact eq_sub_iff_add_eq.mpr
              (one_add_one_eq_two : (1 : ℝ) + 1 = 2))
      _ = (2 + ‖t‖) - 1 := by
        exact (sub_add_eq_add_sub 2 1 ‖t‖).symm
  exact (le_of_eq hone_add_eq).trans hsub_lt.le

/-- Sharp real-variable cutoff estimate for the Bernoulli-remainder derivative
majorant.

This is the scalar calculus core: since
`⌊2 + |t|⌋₊ ≥ 1 + |t|`, the finite tail of `(1 + |t|) / x^2` from the
canonical cutoff is bounded by one. -/
theorem boundaryLineOnePointRealParam_logarithmicPhase_postCutoff_inverseSquareMajorant_eq_endpointDifference_ownerGap
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    {M : ℕ}
    (hM : ⌊2 + ‖t‖⌋₊ ≤ M) :
    (∫ x in Set.Ioc (((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ)) (((M : ℕ) : ℝ)),
        (1 + ‖t‖) / x ^ 2) =
      (1 + ‖t‖) *
        ((((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ))⁻¹ - (((M : ℕ) : ℝ))⁻¹) := by
  have htransport :
      (∫ x in Set.Ioc (((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ)) (((M : ℕ) : ℝ)),
          (1 + ‖t‖) / x ^ 2) =
        ∫ x in (((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ))..(((M : ℕ) : ℝ)),
          (1 + ‖t‖) / x ^ 2 :=
    boundaryLineOnePointRealParam_logarithmicPhase_postCutoff_inverseSquareMajorant_eq_intervalIntegral
      t hM
  exact Eq.trans
    htransport
    (boundaryLineOnePointRealParam_logarithmicPhase_postCutoff_inverseSquareMajorant_intervalIntegral_eq_endpointDifference_ownerGap
      t ht hM)

theorem boundaryLineOnePointRealParam_logarithmicPhase_postCutoff_inverseSquareEndpointDifference_le_cutoffRatio_ownerGap
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    {M : ℕ}
    (hM : ⌊2 + ‖t‖⌋₊ ≤ M) :
    (1 + ‖t‖) *
        ((((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ))⁻¹ - (((M : ℕ) : ℝ))⁻¹) ≤
      (1 + ‖t‖) * ((((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ))⁻¹) := by
  have hM_nonneg : 0 ≤ (((M : ℕ) : ℝ) : ℝ) :=
    Nat.cast_nonneg M
  have hM_inv_nonneg : 0 ≤ ((((M : ℕ) : ℝ) : ℝ))⁻¹ :=
    inv_nonneg.mpr hM_nonneg
  have hdrop_upper_endpoint :
      ((((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ))⁻¹ - (((M : ℕ) : ℝ))⁻¹) ≤
        ((((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ))⁻¹) :=
    sub_le_self
      ((((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ))⁻¹)
      hM_inv_nonneg
  have hcoefficient_nonneg : 0 ≤ (1 : ℝ) + ‖t‖ :=
    add_nonneg zero_le_one (norm_nonneg t)
  exact
    mul_le_mul_of_nonneg_left
      hdrop_upper_endpoint
      hcoefficient_nonneg

theorem boundaryLineOnePointRealParam_logarithmicPhase_postCutoff_cutoffRatio_le_one_ownerGap
    (t : ℝ)
    (ht : 1 ≤ ‖t‖) :
    (1 + ‖t‖) * ((((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ))⁻¹) ≤
      1 := by
  have hcutoff_ge :
      (1 : ℝ) + ‖t‖ ≤ ((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ) :=
    boundaryLineOnePointRealParam_postCutoff_one_add_norm_le_cutoff t
  have hone_add_norm_pos : 0 < (1 : ℝ) + ‖t‖ := by
    exact lt_of_lt_of_le
      zero_lt_one
      (le_add_of_nonneg_right (norm_nonneg t))
  have hcutoff_pos : 0 < ((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ) :=
    lt_of_lt_of_le hone_add_norm_pos hcutoff_ge
  have hratio_le_one :
      ((1 : ℝ) + ‖t‖) / ((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ) ≤ 1 :=
    (div_le_one₀ hcutoff_pos).mpr hcutoff_ge
  exact Eq.subst
    (motive := fun r : ℝ => r ≤ 1)
    (div_eq_mul_inv ((1 : ℝ) + ‖t‖) ((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ))
    hratio_le_one

/-- The post-cutoff reciprocal endpoint absorbs the logarithmic frequency.

This is the scalar endpoint estimate used by the reciprocal-drift component of
the finite normalized-kernel block decomposition. -/
theorem boundaryLineOnePointRealParam_logarithmicPhase_postCutoff_norm_mul_cutoff_inv_le_one
    (t : ℝ)
    (ht : 1 ≤ ‖t‖) :
    ‖t‖ * ((((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ))⁻¹) ≤
      1 := by
  have hnorm_le_one_add : ‖t‖ ≤ (1 : ℝ) + ‖t‖ :=
    le_add_of_nonneg_left zero_le_one
  have hcutoff_nonneg :
      0 ≤ ((((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ))⁻¹) :=
    inv_nonneg.mpr (Nat.cast_nonneg ⌊2 + ‖t‖⌋₊)
  have hmul :
      ‖t‖ * ((((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ))⁻¹) ≤
        (1 + ‖t‖) * ((((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ))⁻¹) :=
    mul_le_mul_of_nonneg_right hnorm_le_one_add hcutoff_nonneg
  exact le_trans hmul
    (boundaryLineOnePointRealParam_logarithmicPhase_postCutoff_cutoffRatio_le_one_ownerGap
      t ht)

/-- The reciprocal-drift endpoint bound is dominated by the canonical
`2 sqrt(1 + |t|) log(2 + M)` post-cutoff scale. -/
theorem boundaryLineOnePointRealParam_logarithmicPhase_postCutoff_norm_mul_cutoff_inv_le_two_sqrt_log
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    {M : ℕ}
    (hM : ⌊2 + ‖t‖⌋₊ ≤ M) :
    ‖t‖ * ((((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ))⁻¹) ≤
      2 * Real.sqrt (1 + ‖t‖) * Real.log (2 + M) := by
  have hsqrt_ge_one : (1 : ℝ) ≤ Real.sqrt (1 + ‖t‖) := by
    have hone_le_one_add_norm : (1 : ℝ) ≤ 1 + ‖t‖ :=
      le_add_of_nonneg_right (norm_nonneg t)
    exact Real.one_le_sqrt.mpr hone_le_one_add_norm
  have hM_ge_one_add_norm :
      (1 : ℝ) + ‖t‖ ≤ (M : ℝ) :=
    le_trans
      (boundaryLineOnePointRealParam_postCutoff_one_add_norm_le_cutoff t)
      (Nat.cast_le.mpr hM)
  have harg_le :
      2 + ‖t‖ ≤ (2 : ℝ) + M := by
    have hone_add_one :
        (1 : ℝ) + 1 = 2 :=
      one_add_one_eq_two
    have htwo_add_norm :
        2 + ‖t‖ = 1 + (1 + ‖t‖) := by
      calc
        2 + ‖t‖ = ((1 : ℝ) + 1) + ‖t‖ := by
          exact congrArg (fun x : ℝ => x + ‖t‖) hone_add_one.symm
        _ = 1 + (1 + ‖t‖) := by
          exact add_assoc (1 : ℝ) 1 ‖t‖
    calc
      2 + ‖t‖ = 1 + (1 + ‖t‖) :=
        htwo_add_norm
      _ ≤ 1 + (M : ℝ) :=
        add_le_add_left hM_ge_one_add_norm 1
      _ ≤ 2 + (M : ℝ) :=
        add_le_add_right (show (1 : ℝ) ≤ 2 from one_le_two) (M : ℝ)
  have hlog_lower_norm : (1 : ℝ) ≤ Real.log (2 + ‖t‖) :=
    one_le_log_two_add_norm_of_one_le_norm ht
  have hlog_lower_M : (1 : ℝ) ≤ Real.log (2 + M) := by
    have harg_pos : 0 < 2 + ‖t‖ :=
      lt_of_lt_of_le zero_lt_two
        (le_add_of_nonneg_right (norm_nonneg t))
    have hlog_le :
        Real.log (2 + ‖t‖) ≤ Real.log (2 + M) :=
      Real.log_le_log harg_pos harg_le
    exact le_trans hlog_lower_norm hlog_le
  have hfactor_ge_one :
      (1 : ℝ) ≤ Real.sqrt (1 + ‖t‖) * Real.log (2 + M) :=
    one_le_mul hsqrt_ge_one hlog_lower_M
  have hscale_ge_one :
      (1 : ℝ) ≤ 2 * Real.sqrt (1 + ‖t‖) * Real.log (2 + M) := by
    calc
      (1 : ℝ) ≤ 2 * (Real.sqrt (1 + ‖t‖) * Real.log (2 + M)) :=
        le_trans hfactor_ge_one
          (mul_le_mul_of_nonneg_right
            (show (1 : ℝ) ≤ 2 from one_le_two)
            (mul_nonneg
              (Real.sqrt_nonneg (1 + ‖t‖))
              (le_trans (show (0 : ℝ) ≤ 1 from zero_le_one) hlog_lower_M)))
      _ = 2 * Real.sqrt (1 + ‖t‖) * Real.log (2 + M) :=
        (mul_assoc 2 (Real.sqrt (1 + ‖t‖)) (Real.log (2 + M))).symm
  exact le_trans
    (boundaryLineOnePointRealParam_logarithmicPhase_postCutoff_norm_mul_cutoff_inv_le_one
      t ht)
    hscale_ge_one


end LFunctions
end Boundary
