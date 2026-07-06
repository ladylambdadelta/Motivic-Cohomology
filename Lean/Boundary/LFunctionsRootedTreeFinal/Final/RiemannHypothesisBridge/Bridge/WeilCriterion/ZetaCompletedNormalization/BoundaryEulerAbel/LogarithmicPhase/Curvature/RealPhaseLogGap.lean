import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalization.BoundaryEulerAbel.LogarithmicPhase.Curvature.RealPhaseShiftedDifference

/-!
# Fixed-width logarithmic gap arithmetic

This file owns the arithmetic core behind the final shifted-increment
monotonicity proof for the logarithmic real phase.
-/

namespace Boundary
namespace LFunctions

noncomputable section

/-- Numerator arithmetic for a fixed-width adjacent-logarithm gap. -/
theorem Nat.logarithmicPhase_fixedWidthGapNumerator_eq
    (h n : ℕ) :
    (n + 1) * (n + h) = n * (n + h + 1) + h := by
  calc
    (n + 1) * (n + h) =
        n * (n + h) + 1 * (n + h) :=
      Nat.add_mul n 1 (n + h)
    _ = n * (n + h) + (n + h) :=
      congrArg
        (fun r : ℕ => n * (n + h) + r)
        (Nat.one_mul (n + h))
    _ = n * (n + h) + n + h :=
      (Nat.add_assoc (n * (n + h)) n h).symm
    _ = n * (n + h) + n * 1 + h :=
      congrArg
        (fun r : ℕ => n * (n + h) + r + h)
        (Nat.mul_one n).symm
    _ = n * ((n + h) + 1) + h :=
      congrArg
        (fun r : ℕ => r + h)
        (Nat.mul_add n (n + h) 1).symm
    _ = n * (n + h + 1) + h :=
      rfl

/-- Real-cast numerator arithmetic for a fixed-width adjacent-logarithm gap. -/
theorem Real.logarithmicPhase_fixedWidthGapNumerator_eq
    (h n : ℕ) :
    (((n + 1) * (n + h) : ℕ) : ℝ) =
      ((n * (n + h + 1) : ℕ) : ℝ) + (h : ℝ) := by
  have hnat :
      (n + 1) * (n + h) = n * (n + h + 1) + h :=
    Nat.logarithmicPhase_fixedWidthGapNumerator_eq h n
  have hcast :
      (((n * (n + h + 1) + h : ℕ) : ℝ)) =
        ((n * (n + h + 1) : ℕ) : ℝ) + (h : ℝ) :=
    Nat.cast_add (n * (n + h + 1)) h
  exact Eq.trans (congrArg (fun k : ℕ => (k : ℝ)) hnat) hcast

/-- The fixed-width logarithmic-gap denominator is monotone in the left
endpoint. -/
theorem Nat.logarithmicPhase_fixedWidthGapDenominator_mono
    {h m n : ℕ}
    (hmn : m ≤ n) :
    m * (m + h + 1) ≤ n * (n + h + 1) := by
  have hright : m + h + 1 ≤ n + h + 1 := by
    exact Nat.succ_le_succ (Nat.add_le_add_right hmn h)
  exact Nat.mul_le_mul hmn hright

/-- Real-cast form of fixed-width denominator monotonicity. -/
theorem Real.logarithmicPhase_fixedWidthGapDenominator_mono
    {h m n : ℕ}
    (hmn : m ≤ n) :
    ((m * (m + h + 1) : ℕ) : ℝ) ≤
      ((n * (n + h + 1) : ℕ) : ℝ) :=
  Nat.cast_le.mpr
    (Nat.logarithmicPhase_fixedWidthGapDenominator_mono hmn)

/-- The fixed-width logarithmic-gap denominator is positive on positive
integer endpoints. -/
theorem Real.logarithmicPhase_fixedWidthGapDenominator_pos
    {h n : ℕ}
    (hn : 1 ≤ n) :
    0 < ((n * (n + h + 1) : ℕ) : ℝ) := by
  have hn_pos : 0 < n :=
    Nat.lt_of_succ_le hn
  have hright_pos : 0 < n + h + 1 :=
    Nat.succ_pos (n + h)
  have hprod_pos : 0 < n * (n + h + 1) :=
    Nat.mul_pos hn_pos hright_pos
  exact Nat.cast_pos.mpr hprod_pos

/-- The reciprocal rational factor `h / (n * (n+h+1))` is antitone in the
left endpoint. -/
theorem Real.logarithmicPhase_fixedWidthGapReciprocal_antitone
    {h m n : ℕ}
    (hm : 1 ≤ m)
    (hmn : m ≤ n) :
    ((h : ℝ) / ((n * (n + h + 1) : ℕ) : ℝ)) ≤
      ((h : ℝ) / ((m * (m + h + 1) : ℕ) : ℝ)) := by
  have hn : 1 ≤ n :=
    le_trans hm hmn
  have hden_m_pos :
      0 < ((m * (m + h + 1) : ℕ) : ℝ) :=
    Real.logarithmicPhase_fixedWidthGapDenominator_pos hm
  have hden_le :
      ((m * (m + h + 1) : ℕ) : ℝ) ≤
        ((n * (n + h + 1) : ℕ) : ℝ) :=
    Real.logarithmicPhase_fixedWidthGapDenominator_mono hmn
  have hnum_nonneg : 0 ≤ (h : ℝ) :=
    Nat.cast_nonneg h
  exact div_le_div_of_nonneg_left hnum_nonneg hden_m_pos hden_le

/-- The normalized fixed-width rational gap factor is antitone in the left
endpoint. -/
theorem Real.logarithmicPhase_fixedWidthGapFactor_antitone
    {h m n : ℕ}
    (hm : 1 ≤ m)
    (hmn : m ≤ n) :
    (1 : ℝ) + (h : ℝ) / ((n * (n + h + 1) : ℕ) : ℝ) ≤
      (1 : ℝ) + (h : ℝ) / ((m * (m + h + 1) : ℕ) : ℝ) :=
  add_le_add_left
    (Real.logarithmicPhase_fixedWidthGapReciprocal_antitone hm hmn)
    1

/-- Logarithms of the normalized fixed-width rational gap factors are antitone
in the left endpoint. -/
theorem Real.logarithmicPhase_fixedWidthLogGapFactor_antitone
    {h m n : ℕ}
    (hm : 1 ≤ m)
    (hmn : m ≤ n) :
    Real.log
        ((1 : ℝ) + (h : ℝ) / ((n * (n + h + 1) : ℕ) : ℝ)) ≤
      Real.log
        ((1 : ℝ) + (h : ℝ) / ((m * (m + h + 1) : ℕ) : ℝ)) := by
  have hfactor_n_pos :
      0 <
        (1 : ℝ) + (h : ℝ) / ((n * (n + h + 1) : ℕ) : ℝ) := by
    have hden_n_pos :
        0 < ((n * (n + h + 1) : ℕ) : ℝ) :=
      Real.logarithmicPhase_fixedWidthGapDenominator_pos
        (le_trans hm hmn)
    have hquot_nonneg :
        0 ≤ (h : ℝ) / ((n * (n + h + 1) : ℕ) : ℝ) :=
      div_nonneg (Nat.cast_nonneg h) (le_of_lt hden_n_pos)
    exact lt_of_lt_of_le zero_lt_one (le_add_of_nonneg_right hquot_nonneg)
  exact
    Real.log_le_log
      hfactor_n_pos
      (Real.logarithmicPhase_fixedWidthGapFactor_antitone hm hmn)

/-- Cast-normalized quotient of adjacent logarithmic ratios. -/
theorem Real.logarithmicPhase_fixedWidthRatio_eq_natQuotient
    {h n : ℕ}
    (_hn : 1 ≤ n) :
    ((((n + 1 : ℕ) : ℝ) / ((n : ℕ) : ℝ)) /
        (((n + h + 1 : ℕ) : ℝ) / ((n + h : ℕ) : ℝ))) =
      (((n + 1) * (n + h) : ℕ) : ℝ) /
        ((n * (n + h + 1) : ℕ) : ℝ) := by
  have hratio_div :
      ((((n + 1 : ℕ) : ℝ) / ((n : ℕ) : ℝ)) /
          (((n + h + 1 : ℕ) : ℝ) / ((n + h : ℕ) : ℝ))) =
        (((n + 1 : ℕ) : ℝ) * ((n + h : ℕ) : ℝ)) /
          (((n : ℕ) : ℝ) * ((n + h + 1 : ℕ) : ℝ)) :=
    div_div_div_eq
      (((n + 1 : ℕ) : ℝ))
      (((n : ℕ) : ℝ))
      (((n + h + 1 : ℕ) : ℝ))
      (((n + h : ℕ) : ℝ))
  have hnum_cast :
      (((n + 1 : ℕ) : ℝ) * ((n + h : ℕ) : ℝ)) =
        (((n + 1) * (n + h) : ℕ) : ℝ) :=
    (Nat.cast_mul (n + 1) (n + h)).symm
  have hden_cast :
      (((n : ℕ) : ℝ) * ((n + h + 1 : ℕ) : ℝ)) =
        ((n * (n + h + 1) : ℕ) : ℝ) :=
    (Nat.cast_mul n (n + h + 1)).symm
  have hratio_cast :
      (((n + 1 : ℕ) : ℝ) * ((n + h : ℕ) : ℝ)) /
          (((n : ℕ) : ℝ) * ((n + h + 1 : ℕ) : ℝ)) =
        (((n + 1) * (n + h) : ℕ) : ℝ) /
          ((n * (n + h + 1) : ℕ) : ℝ) :=
    calc
      (((n + 1 : ℕ) : ℝ) * ((n + h : ℕ) : ℝ)) /
          (((n : ℕ) : ℝ) * ((n + h + 1 : ℕ) : ℝ)) =
          (((n + 1) * (n + h) : ℕ) : ℝ) /
            (((n : ℕ) : ℝ) * ((n + h + 1 : ℕ) : ℝ)) := by
        exact
          congrArg
            (fun num : ℝ =>
              num / (((n : ℕ) : ℝ) * ((n + h + 1 : ℕ) : ℝ)))
            hnum_cast
      _ =
          (((n + 1) * (n + h) : ℕ) : ℝ) /
            ((n * (n + h + 1) : ℕ) : ℝ) := by
        exact
          congrArg
            (fun den : ℝ =>
              (((n + 1) * (n + h) : ℕ) : ℝ) / den)
            hden_cast
  exact Eq.trans hratio_div hratio_cast

/-- The cast-normalized fixed-width quotient is the rational gap factor. -/
theorem Real.logarithmicPhase_fixedWidthNatQuotient_eq_gapFactor
    {h n : ℕ}
    (hn : 1 ≤ n) :
    (((n + 1) * (n + h) : ℕ) : ℝ) /
        ((n * (n + h + 1) : ℕ) : ℝ) =
      (1 : ℝ) + (h : ℝ) / ((n * (n + h + 1) : ℕ) : ℝ) := by
  have hden_pos :
      0 < ((n * (n + h + 1) : ℕ) : ℝ) :=
    Real.logarithmicPhase_fixedWidthGapDenominator_pos hn
  have hden_ne :
      ((n * (n + h + 1) : ℕ) : ℝ) ≠ 0 :=
    ne_of_gt hden_pos
  have hnum_eq :
      (((n + 1) * (n + h) : ℕ) : ℝ) =
        ((n * (n + h + 1) : ℕ) : ℝ) + (h : ℝ) :=
    Real.logarithmicPhase_fixedWidthGapNumerator_eq h n
  have hdiv_num :
      (((n + 1) * (n + h) : ℕ) : ℝ) /
          ((n * (n + h + 1) : ℕ) : ℝ) =
        (((n * (n + h + 1) : ℕ) : ℝ) + (h : ℝ)) /
          ((n * (n + h + 1) : ℕ) : ℝ) :=
    congrArg
      (fun num : ℝ => num / ((n * (n + h + 1) : ℕ) : ℝ))
      hnum_eq
  have hfactor_symm :
      (((n * (n + h + 1) : ℕ) : ℝ) + (h : ℝ)) /
          ((n * (n + h + 1) : ℕ) : ℝ) =
        (1 : ℝ) + (h : ℝ) / ((n * (n + h + 1) : ℕ) : ℝ) :=
    (one_add_div hden_ne).symm
  exact Eq.trans hdiv_num hfactor_symm

/-- The quotient of adjacent logarithmic ratios has the fixed-width rational
gap form. -/
theorem Real.logarithmicPhase_fixedWidthRatio_eq_gapFactor
    {h n : ℕ}
    (hn : 1 ≤ n) :
    ((((n + 1 : ℕ) : ℝ) / ((n : ℕ) : ℝ)) /
        (((n + h + 1 : ℕ) : ℝ) / ((n + h : ℕ) : ℝ))) =
      (1 : ℝ) + (h : ℝ) / ((n * (n + h + 1) : ℕ) : ℝ) := by
  have hratio_nat :
      ((((n + 1 : ℕ) : ℝ) / ((n : ℕ) : ℝ)) /
          (((n + h + 1 : ℕ) : ℝ) / ((n + h : ℕ) : ℝ))) =
        (((n + 1) * (n + h) : ℕ) : ℝ) /
          ((n * (n + h + 1) : ℕ) : ℝ) :=
    Real.logarithmicPhase_fixedWidthRatio_eq_natQuotient hn
  have hnat_factor :
      (((n + 1) * (n + h) : ℕ) : ℝ) /
          ((n * (n + h + 1) : ℕ) : ℝ) =
        (1 : ℝ) + (h : ℝ) / ((n * (n + h + 1) : ℕ) : ℝ) :=
    Real.logarithmicPhase_fixedWidthNatQuotient_eq_gapFactor hn
  exact
    Eq.trans hratio_nat hnat_factor

/-- Sign transport for fixed-width increment gaps in the nonnegative branch. -/
theorem Real.neg_mul_sub_neg_mul_swap
    (t A B : ℝ) :
    (-t * B) - (-t * A) = t * (A - B) := by
  have hleft : (-t * B) = -(t * B) :=
    (neg_mul_eq_neg_mul t B).symm
  have hright : (-t * A) = -(t * A) :=
    (neg_mul_eq_neg_mul t A).symm
  calc
    (-t * B) - (-t * A) = -(t * B) - (-t * A) := by
      exact congrArg (fun left : ℝ => left - (-t * A)) hleft
    _ = -(t * B) - (-(t * A)) := by
      exact congrArg (fun right : ℝ => -(t * B) - right) hright
    _ = -(t * B) + t * A :=
      sub_neg_eq_add (-(t * B)) (t * A)
    _ = t * A + -(t * B) :=
      add_comm (-(t * B)) (t * A)
    _ = t * A - t * B :=
      (sub_eq_add_neg (t * A) (t * B)).symm
    _ = t * (A - B) :=
      (mul_sub t A B).symm

/-- Difference of adjacent logarithmic ratios across a fixed width. -/
theorem Real.logarithmicPhase_fixedWidthLogGap_eq
    {h n : ℕ}
    (hn : 1 ≤ n) :
    Real.log ((((n + 1 : ℕ) : ℝ) / ((n : ℕ) : ℝ))) -
        Real.log ((((n + h + 1 : ℕ) : ℝ) / ((n + h : ℕ) : ℝ))) =
      Real.log
        ((1 : ℝ) + (h : ℝ) / ((n * (n + h + 1) : ℕ) : ℝ)) := by
  have hn_pos_nat : 0 < n :=
    Nat.lt_of_succ_le hn
  have hn_h_pos_nat : 0 < n + h :=
    lt_of_lt_of_le hn_pos_nat (Nat.le_add_right n h)
  have hn_real_pos : 0 < ((n : ℕ) : ℝ) :=
    Nat.cast_pos.mpr hn_pos_nat
  have hn_h_real_pos : 0 < ((n + h : ℕ) : ℝ) :=
    Nat.cast_pos.mpr hn_h_pos_nat
  have hn_succ_real_pos : 0 < ((n + 1 : ℕ) : ℝ) :=
    Nat.cast_pos.mpr (Nat.succ_pos n)
  have hn_h_succ_real_pos : 0 < ((n + h + 1 : ℕ) : ℝ) :=
    Nat.cast_pos.mpr (Nat.succ_pos (n + h))
  have hleft_ne :
      (((n + 1 : ℕ) : ℝ) / ((n : ℕ) : ℝ)) ≠ 0 :=
    ne_of_gt (div_pos hn_succ_real_pos hn_real_pos)
  have hright_ne :
      (((n + h + 1 : ℕ) : ℝ) / ((n + h : ℕ) : ℝ)) ≠ 0 :=
    ne_of_gt (div_pos hn_h_succ_real_pos hn_h_real_pos)
  have hlog_div :
      Real.log
          ((((n + 1 : ℕ) : ℝ) / ((n : ℕ) : ℝ)) /
            (((n + h + 1 : ℕ) : ℝ) / ((n + h : ℕ) : ℝ))) =
        Real.log ((((n + 1 : ℕ) : ℝ) / ((n : ℕ) : ℝ))) -
          Real.log ((((n + h + 1 : ℕ) : ℝ) / ((n + h : ℕ) : ℝ))) :=
    Real.log_div hleft_ne hright_ne
  have hratio :
      ((((n + 1 : ℕ) : ℝ) / ((n : ℕ) : ℝ)) /
          (((n + h + 1 : ℕ) : ℝ) / ((n + h : ℕ) : ℝ))) =
        (1 : ℝ) + (h : ℝ) / ((n * (n + h + 1) : ℕ) : ℝ) :=
    Real.logarithmicPhase_fixedWidthRatio_eq_gapFactor hn
  exact
    Eq.trans hlog_div.symm
      (congrArg Real.log hratio)

/-- The fixed-width logarithmic gap is antitone in the left endpoint. -/
theorem Real.logarithmicPhase_fixedWidthLogGap_antitone
    {h m n : ℕ}
    (hm : 1 ≤ m)
    (hmn : m ≤ n) :
    Real.log ((((n + 1 : ℕ) : ℝ) / ((n : ℕ) : ℝ))) -
        Real.log ((((n + h + 1 : ℕ) : ℝ) / ((n + h : ℕ) : ℝ))) ≤
      Real.log ((((m + 1 : ℕ) : ℝ) / ((m : ℕ) : ℝ))) -
        Real.log ((((m + h + 1 : ℕ) : ℝ) / ((m + h : ℕ) : ℝ))) := by
  have hn : 1 ≤ n :=
    le_trans hm hmn
  have hn_eq :
      Real.log ((((n + 1 : ℕ) : ℝ) / ((n : ℕ) : ℝ))) -
          Real.log ((((n + h + 1 : ℕ) : ℝ) / ((n + h : ℕ) : ℝ))) =
        Real.log
          ((1 : ℝ) + (h : ℝ) / ((n * (n + h + 1) : ℕ) : ℝ)) :=
    Real.logarithmicPhase_fixedWidthLogGap_eq hn
  have hm_eq :
      Real.log ((((m + 1 : ℕ) : ℝ) / ((m : ℕ) : ℝ))) -
          Real.log ((((m + h + 1 : ℕ) : ℝ) / ((m + h : ℕ) : ℝ))) =
        Real.log
          ((1 : ℝ) + (h : ℝ) / ((m * (m + h + 1) : ℕ) : ℝ)) :=
    Real.logarithmicPhase_fixedWidthLogGap_eq hm
  have hfactor :
      Real.log
          ((1 : ℝ) + (h : ℝ) / ((n * (n + h + 1) : ℕ) : ℝ)) ≤
        Real.log
          ((1 : ℝ) + (h : ℝ) / ((m * (m + h + 1) : ℕ) : ℝ)) :=
    Real.logarithmicPhase_fixedWidthLogGapFactor_antitone hm hmn
  exact
    Eq.subst
      (motive := fun left : ℝ =>
        left ≤
          Real.log ((((m + 1 : ℕ) : ℝ) / ((m : ℕ) : ℝ))) -
            Real.log ((((m + h + 1 : ℕ) : ℝ) / ((m + h : ℕ) : ℝ))))
      hn_eq.symm
      (Eq.subst
        (motive := fun right : ℝ =>
          Real.log
              ((1 : ℝ) + (h : ℝ) / ((n * (n + h + 1) : ℕ) : ℝ)) ≤
            right)
        hm_eq.symm
        hfactor)

/-- Parent adjacent-increment fixed-width gaps are the nonnegative frequency
times the fixed-width logarithmic gap. -/
theorem Complex.logarithmicPhaseRealPhase_parentFixedWidthGap_eq_mul_logGap
    (t : ℝ)
    {h n : ℕ}
    (hn : 1 ≤ n) :
    Complex.realPhase_integerIncrement
        (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
        (n + h) -
      Complex.realPhase_integerIncrement
        (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
        n =
      t *
        (Real.log ((((n + 1 : ℕ) : ℝ) / ((n : ℕ) : ℝ))) -
          Real.log ((((n + h + 1 : ℕ) : ℝ) / ((n + h : ℕ) : ℝ)))) := by
  have hn_pos : 0 < n :=
    Nat.lt_of_succ_le hn
  have hn_h_pos : 0 < n + h :=
    lt_of_lt_of_le hn_pos (Nat.le_add_right n h)
  have hn_eq :
      Complex.realPhase_integerIncrement
          (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
          n =
        -t * Real.log ((((n + 1 : ℕ) : ℝ) / ((n : ℕ) : ℝ))) :=
    Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase_integerIncrement_eq_neg_mul_log_ratio
      t hn_pos
  have hnh_eq :
      Complex.realPhase_integerIncrement
          (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
          (n + h) =
        -t *
          Real.log ((((n + h + 1 : ℕ) : ℝ) / ((n + h : ℕ) : ℝ))) :=
    Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase_integerIncrement_eq_neg_mul_log_ratio
      t hn_h_pos
  calc
    Complex.realPhase_integerIncrement
        (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
        (n + h) -
      Complex.realPhase_integerIncrement
        (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
        n =
        (-t *
          Real.log ((((n + h + 1 : ℕ) : ℝ) / ((n + h : ℕ) : ℝ)))) -
          (-t * Real.log ((((n + 1 : ℕ) : ℝ) / ((n : ℕ) : ℝ)))) := by
      exact
        calc
          Complex.realPhase_integerIncrement
              (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
              (n + h) -
            Complex.realPhase_integerIncrement
              (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
              n =
              (-t *
                Real.log
                  ((((n + h + 1 : ℕ) : ℝ) / ((n + h : ℕ) : ℝ)))) -
                Complex.realPhase_integerIncrement
                  (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
                  n := by
            exact
              congrArg
                (fun left : ℝ =>
                  left -
                    Complex.realPhase_integerIncrement
                      (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
                      n)
                hnh_eq
          _ =
              (-t *
                Real.log
                  ((((n + h + 1 : ℕ) : ℝ) / ((n + h : ℕ) : ℝ)))) -
                (-t *
                  Real.log ((((n + 1 : ℕ) : ℝ) / ((n : ℕ) : ℝ)))) := by
            exact
              congrArg
                (fun right : ℝ =>
                  (-t *
                    Real.log
                      ((((n + h + 1 : ℕ) : ℝ) / ((n + h : ℕ) : ℝ)))) -
                    right)
                hn_eq
    _ =
        t *
          (Real.log ((((n + 1 : ℕ) : ℝ) / ((n : ℕ) : ℝ))) -
            Real.log ((((n + h + 1 : ℕ) : ℝ) / ((n + h : ℕ) : ℝ)))) := by
      exact
        Real.neg_mul_sub_neg_mul_swap
          t
          (Real.log ((((n + 1 : ℕ) : ℝ) / ((n : ℕ) : ℝ))))
          (Real.log ((((n + h + 1 : ℕ) : ℝ) / ((n + h : ℕ) : ℝ))))

/-- The fixed-width logarithmic gap is nonnegative. -/
theorem Real.logarithmicPhase_fixedWidthLogGap_nonneg
    {h n : ℕ}
    (hn : 1 ≤ n) :
    0 ≤
      Real.log ((((n + 1 : ℕ) : ℝ) / ((n : ℕ) : ℝ))) -
        Real.log ((((n + h + 1 : ℕ) : ℝ) / ((n + h : ℕ) : ℝ))) := by
  have hgap_eq :
      Real.log ((((n + 1 : ℕ) : ℝ) / ((n : ℕ) : ℝ))) -
          Real.log ((((n + h + 1 : ℕ) : ℝ) / ((n + h : ℕ) : ℝ))) =
        Real.log
          ((1 : ℝ) + (h : ℝ) / ((n * (n + h + 1) : ℕ) : ℝ)) :=
    Real.logarithmicPhase_fixedWidthLogGap_eq hn
  have hden_pos :
      0 < ((n * (n + h + 1) : ℕ) : ℝ) :=
    Real.logarithmicPhase_fixedWidthGapDenominator_pos hn
  have hquot_nonneg :
      0 ≤ (h : ℝ) / ((n * (n + h + 1) : ℕ) : ℝ) :=
    div_nonneg (Nat.cast_nonneg h) (le_of_lt hden_pos)
  have hfactor_one :
      (1 : ℝ) ≤
        (1 : ℝ) + (h : ℝ) / ((n * (n + h + 1) : ℕ) : ℝ) :=
    le_add_of_nonneg_right hquot_nonneg
  have hlog_nonneg :
      0 ≤
        Real.log
          ((1 : ℝ) + (h : ℝ) / ((n * (n + h + 1) : ℕ) : ℝ)) :=
    Real.log_nonneg hfactor_one
  exact
    Eq.subst
      (motive := fun r : ℝ => 0 ≤ r)
      hgap_eq.symm
      hlog_nonneg

/-- Positive-frequency shifted logarithmic increments are nonnegative. -/
theorem Complex.logarithmicPhaseRealPhase_shiftedDifference_integerIncrement_nonneg
    (t : ℝ)
    (ht_nonneg : 0 ≤ t)
    {h n : ℕ}
    (hn : 1 ≤ n) :
    0 ≤
      Complex.realPhase_integerIncrement
        (Complex.logarithmicPhaseRealPhase_shiftedDifference t h) n := by
  have hshift :
      Complex.realPhase_integerIncrement
          (Complex.logarithmicPhaseRealPhase_shiftedDifference t h) n =
        Complex.realPhase_integerIncrement
            (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
            (n + h) -
          Complex.realPhase_integerIncrement
            (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
            n :=
    Complex.logarithmicPhaseRealPhase_shiftedDifference_integerIncrement_eq t h n
  have hparent :
      Complex.realPhase_integerIncrement
          (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
          (n + h) -
        Complex.realPhase_integerIncrement
          (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
          n =
        t *
          (Real.log ((((n + 1 : ℕ) : ℝ) / ((n : ℕ) : ℝ))) -
            Real.log ((((n + h + 1 : ℕ) : ℝ) / ((n + h : ℕ) : ℝ)))) :=
    Complex.logarithmicPhaseRealPhase_parentFixedWidthGap_eq_mul_logGap
      t hn
  have hgap_nonneg :
      0 ≤
        Real.log ((((n + 1 : ℕ) : ℝ) / ((n : ℕ) : ℝ))) -
          Real.log ((((n + h + 1 : ℕ) : ℝ) / ((n + h : ℕ) : ℝ))) :=
    Real.logarithmicPhase_fixedWidthLogGap_nonneg hn
  have hmul_nonneg :
      0 ≤
        t *
          (Real.log ((((n + 1 : ℕ) : ℝ) / ((n : ℕ) : ℝ))) -
            Real.log ((((n + h + 1 : ℕ) : ℝ) / ((n + h : ℕ) : ℝ)))) :=
    mul_nonneg ht_nonneg hgap_nonneg
  exact
    Eq.subst
      (motive := fun left : ℝ => 0 ≤ left)
      hshift.symm
      (Eq.subst
        (motive := fun right : ℝ => 0 ≤ right)
        hparent.symm
        hmul_nonneg)

/-- In the nonnegative branch, fixed-width parent increment gaps are
antitone on integer subblocks. -/
theorem Complex.logarithmicPhaseRealPhase_parentFixedWidthGap_antitoneOn
    (t : ℝ)
    (ht_nonneg : 0 ≤ t)
    {a b h : ℕ}
    (ha : 1 ≤ a) :
    AntitoneOn
      (fun n : ℕ =>
        Complex.realPhase_integerIncrement
            (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
            (n + h) -
          Complex.realPhase_integerIncrement
            (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
            n)
      (Finset.Ico a (b - h) : Set ℕ) := by
  intro m hm n _hn hmn
  have hm_bounds : a ≤ m ∧ m < b - h :=
    Finset.mem_Ico.mp hm
  have hm_one : 1 ≤ m :=
    le_trans ha hm_bounds.1
  have hn_one : 1 ≤ n :=
    le_trans hm_one hmn
  have hlog :
      Real.log ((((n + 1 : ℕ) : ℝ) / ((n : ℕ) : ℝ))) -
          Real.log ((((n + h + 1 : ℕ) : ℝ) / ((n + h : ℕ) : ℝ))) ≤
        Real.log ((((m + 1 : ℕ) : ℝ) / ((m : ℕ) : ℝ))) -
          Real.log ((((m + h + 1 : ℕ) : ℝ) / ((m + h : ℕ) : ℝ))) :=
    Real.logarithmicPhase_fixedWidthLogGap_antitone hm_one hmn
  have hscaled :
      t *
          (Real.log ((((n + 1 : ℕ) : ℝ) / ((n : ℕ) : ℝ))) -
            Real.log ((((n + h + 1 : ℕ) : ℝ) / ((n + h : ℕ) : ℝ)))) ≤
        t *
          (Real.log ((((m + 1 : ℕ) : ℝ) / ((m : ℕ) : ℝ))) -
            Real.log ((((m + h + 1 : ℕ) : ℝ) / ((m + h : ℕ) : ℝ)))) :=
    mul_le_mul_of_nonneg_left hlog ht_nonneg
  have hn_eq :
      Complex.realPhase_integerIncrement
          (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
          (n + h) -
        Complex.realPhase_integerIncrement
          (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
          n =
        t *
          (Real.log ((((n + 1 : ℕ) : ℝ) / ((n : ℕ) : ℝ))) -
            Real.log ((((n + h + 1 : ℕ) : ℝ) / ((n + h : ℕ) : ℝ)))) :=
    Complex.logarithmicPhaseRealPhase_parentFixedWidthGap_eq_mul_logGap
      t hn_one
  have hm_eq :
      Complex.realPhase_integerIncrement
          (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
          (m + h) -
        Complex.realPhase_integerIncrement
          (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
          m =
        t *
          (Real.log ((((m + 1 : ℕ) : ℝ) / ((m : ℕ) : ℝ))) -
            Real.log ((((m + h + 1 : ℕ) : ℝ) / ((m + h : ℕ) : ℝ)))) :=
    Complex.logarithmicPhaseRealPhase_parentFixedWidthGap_eq_mul_logGap
      t hm_one
  exact
    Eq.subst
      (motive := fun left : ℝ =>
        left ≤
          Complex.realPhase_integerIncrement
              (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
              (m + h) -
            Complex.realPhase_integerIncrement
              (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
              m)
      hn_eq.symm
      (Eq.subst
        (motive := fun right : ℝ =>
          t *
              (Real.log ((((n + 1 : ℕ) : ℝ) / ((n : ℕ) : ℝ))) -
                Real.log ((((n + h + 1 : ℕ) : ℝ) / ((n + h : ℕ) : ℝ)))) ≤
            right)
        hm_eq.symm
        hscaled)

/-- Raw shifted-increment monotonicity for the positive-frequency logarithmic
shift. -/
theorem Complex.logarithmicPhaseRealPhase_shiftedDifference_integerIncrementMonotoneOn_of_nonneg
    (t : ℝ)
    (ht_nonneg : 0 ≤ t)
    {a b h : ℕ}
    (ha : 1 ≤ a) :
    Complex.realPhase_integerIncrementMonotoneOn
      (Complex.logarithmicPhaseRealPhase_shiftedDifference t h) a (b - h) := by
  exact
    Complex.logarithmicPhaseRealPhase_shiftedDifference_integerIncrementMonotoneOn_of_parentGap_antitone
      t
      (Complex.logarithmicPhaseRealPhase_parentFixedWidthGap_antitoneOn
        t ht_nonneg ha)

end

end LFunctions
end Boundary
