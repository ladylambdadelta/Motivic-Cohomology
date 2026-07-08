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

/-- If the right endpoint is strictly to the right, its fixed-width
denominator dominates the left denominator plus the span times the left
endpoint. -/
theorem Nat.logarithmicPhase_fixedWidthGapDenominator_gap_lower
    {h m n : ℕ}
    (hmn : m < n) :
    (m + 1) * (m + h) + (n - m) * m ≤
      n * (n + h + 1) := by
  have hspan_pos : 1 ≤ n - m :=
    Nat.succ_le_iff.mpr (Nat.zero_lt_sub_of_lt hmn)
  have hm_le_n : m ≤ n :=
    le_of_lt hmn
  have hright_le :
      m + h + 1 ≤ n + h + 1 :=
    Nat.succ_le_succ (Nat.add_le_add_right hm_le_n h)
  have hbase :
      n * (m + h + 1) ≤ n * (n + h + 1) :=
    Nat.mul_le_mul_left n hright_le
  have hn_eq : n = m + (n - m) :=
    (Nat.add_sub_of_le hm_le_n).symm
  have hsplit :
      n * (m + h + 1) =
        m * (m + h + 1) + (n - m) * (m + h + 1) := by
    calc
      n * (m + h + 1) =
          (m + (n - m)) * (m + h + 1) := by
        exact congrArg (fun r : ℕ => r * (m + h + 1)) hn_eq
      _ =
          m * (m + h + 1) + (n - m) * (m + h + 1) :=
        Nat.add_mul m (n - m) (m + h + 1)
  have hleft_expand :
      (m + 1) * (m + h) =
        m * (m + h) + (m + h) := by
    calc
      (m + 1) * (m + h) =
          m * (m + h) + 1 * (m + h) :=
        Nat.add_mul m 1 (m + h)
      _ = m * (m + h) + (m + h) := by
        exact congrArg
          (fun r : ℕ => m * (m + h) + r)
          (Nat.one_mul (m + h))
  have hbase_expand :
      m * (m + h + 1) =
        m * (m + h) + m := by
    calc
      m * (m + h + 1) =
          m * ((m + h) + 1) := by
        rfl
      _ = m * (m + h) + m * 1 :=
        Nat.mul_add m (m + h) 1
      _ = m * (m + h) + m := by
        exact congrArg
          (fun r : ℕ => m * (m + h) + r)
          (Nat.mul_one m)
  have hspan_factor_lower :
      (n - m) * m + h ≤ (n - m) * (m + h + 1) := by
    have hh_succ_le :
        h + 1 ≤ (n - m) * (h + 1) :=
      Nat.le_mul_of_pos_left (h + 1) hspan_pos
    have hh_le :
        h ≤ (n - m) * (h + 1) :=
      le_trans (Nat.le_succ h) hh_succ_le
    have hsplit_span :
        (n - m) * (m + h + 1) =
          (n - m) * m + (n - m) * (h + 1) := by
      calc
        (n - m) * (m + h + 1) =
            (n - m) * (m + (h + 1)) := by
          exact
            congrArg
              (fun r : ℕ => (n - m) * r)
              (Nat.add_assoc m h 1)
        _ =
            (n - m) * m + (n - m) * (h + 1) :=
          Nat.mul_add (n - m) m (h + 1)
    have hsum_le :
        (n - m) * m + h ≤
          (n - m) * m + (n - m) * (h + 1) :=
      Nat.add_le_add_left hh_le ((n - m) * m)
    exact
      Eq.subst
        (motive := fun right : ℕ =>
          (n - m) * m + h ≤ right)
        hsplit_span.symm
        hsum_le
  have hspan_factor_with_base :
      (m + h) + (n - m) * m ≤
        m + (n - m) * (m + h + 1) := by
    have hmul_succ :
        (m + h) + (n - m) * m =
          m + ((n - m) * m + h) := by
      calc
        (m + h) + (n - m) * m =
            m + (h + (n - m) * m) := by
          exact add_assoc m h ((n - m) * m)
        _ = m + ((n - m) * m + h) := by
          exact congrArg (fun r : ℕ => m + r)
            (Nat.add_comm h ((n - m) * m))
    exact
      Eq.subst
        (motive := fun left : ℕ =>
          left ≤ m + (n - m) * (m + h + 1))
        hmul_succ.symm
        (Nat.add_le_add_left hspan_factor_lower m)
  have hcore :
      (m + 1) * (m + h) + (n - m) * m ≤
        n * (m + h + 1) := by
    have hmove :
        (m + h) + (n - m) * m ≤
          m + (n - m) * (m + h + 1) := by
      exact hspan_factor_with_base
    calc
      (m + 1) * (m + h) + (n - m) * m =
          (m * (m + h) + (m + h)) + (n - m) * m := by
        exact congrArg
          (fun r : ℕ => r + (n - m) * m)
          hleft_expand
      _ =
          m * (m + h) + ((m + h) + (n - m) * m) := by
        exact Nat.add_assoc (m * (m + h)) (m + h) ((n - m) * m)
      _ ≤
          m * (m + h) + (m + (n - m) * (m + h + 1)) :=
        Nat.add_le_add_left hmove (m * (m + h))
      _ =
          (m * (m + h) + m) + (n - m) * (m + h + 1) := by
        exact (Nat.add_assoc (m * (m + h)) m
          ((n - m) * (m + h + 1))).symm
      _ =
          m * (m + h + 1) + (n - m) * (m + h + 1) := by
        exact congrArg
          (fun r : ℕ => r + (n - m) * (m + h + 1))
          hbase_expand.symm
      _ = n * (m + h + 1) :=
        hsplit.symm
  exact le_trans hcore hbase

/-- A real reciprocal gap is bounded below by a numerator gap divided by a
common square denominator bound.  This is the denominator-comparison core used
for fixed-width logarithmic rational endpoint spreads. -/
theorem Real.reciprocal_gap_lower_of_denominator_gap_and_upper_bound
    {H A D B L : ℝ}
    (hH_nonneg : 0 ≤ H)
    (hA_pos : 0 < A)
    (hD_pos : 0 < D)
    (hAD_order : A ≤ D)
    (hgap : L ≤ D - A)
    (hA_le_B : A ≤ B)
    (hD_le_B : D ≤ B)
    (hL_nonneg : 0 ≤ L) :
    H * L / (B * B) ≤ H / A - H / D := by
  have hB_pos : 0 < B :=
    lt_of_lt_of_le hD_pos hD_le_B
  have hBB_pos : 0 < B * B :=
    mul_pos hB_pos hB_pos
  have hAD_pos : 0 < A * D :=
    mul_pos hA_pos hD_pos
  have hAD_le_BB : A * D ≤ B * B :=
    mul_le_mul hA_le_B hD_le_B (le_of_lt hD_pos) (le_of_lt hB_pos)
  have hHL_nonneg : 0 ≤ H * L :=
    mul_nonneg hH_nonneg hL_nonneg
  have hHgap_nonneg : 0 ≤ H * (D - A) :=
    mul_nonneg hH_nonneg (sub_nonneg.mpr hAD_order)
  have hnum_le :
      H * L ≤ H * (D - A) :=
    mul_le_mul_of_nonneg_left hgap hH_nonneg
  have hleft_den :
      H * L / (B * B) ≤ H * L / (A * D) :=
    div_le_div_of_nonneg_left hHL_nonneg hAD_pos hAD_le_BB
  have hnum_den :
      H * L / (A * D) ≤ H * (D - A) / (A * D) :=
    div_le_div_of_nonneg_right hnum_le (le_of_lt hAD_pos)
  have hspread_eq :
      H / A - H / D = H * (D - A) / (A * D) := by
    have hA_ne : A ≠ 0 :=
      ne_of_gt hA_pos
    have hD_ne : D ≠ 0 :=
      ne_of_gt hD_pos
    have hdiv :
        H / A - H / D = (H * D - A * H) / (A * D) :=
      div_sub_div H H hA_ne hD_ne
    have hnum :
        H * D - A * H = H * (D - A) := by
      calc
        H * D - A * H = H * D - H * A := by
          exact congrArg (fun r : ℝ => H * D - r) (mul_comm A H)
        _ = H * (D - A) := by
          exact (mul_sub H D A).symm
    exact
      Eq.trans hdiv
        (congrArg (fun r : ℝ => r / (A * D)) hnum)
  exact
    le_trans hleft_den
      (le_trans hnum_den
        (le_of_eq hspread_eq.symm))

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

/-- Parent adjacent-increment fixed-width gaps are the nonnegative frequency
times the normalized rational logarithmic gap. -/
theorem Complex.logarithmicPhaseRealPhase_parentFixedWidthGap_eq_mul_logFactor
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
        Real.log
          ((1 : ℝ) + (h : ℝ) / ((n * (n + h + 1) : ℕ) : ℝ)) := by
  have hparent_logGap :
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
  have hlogGap_eq :
      Real.log ((((n + 1 : ℕ) : ℝ) / ((n : ℕ) : ℝ))) -
          Real.log ((((n + h + 1 : ℕ) : ℝ) / ((n + h : ℕ) : ℝ))) =
        Real.log
          ((1 : ℝ) + (h : ℝ) / ((n * (n + h + 1) : ℕ) : ℝ)) :=
    Real.logarithmicPhase_fixedWidthLogGap_eq hn
  have hmul_logGap :
      t *
          (Real.log ((((n + 1 : ℕ) : ℝ) / ((n : ℕ) : ℝ))) -
            Real.log ((((n + h + 1 : ℕ) : ℝ) / ((n + h : ℕ) : ℝ)))) =
        t *
          Real.log
            ((1 : ℝ) + (h : ℝ) / ((n * (n + h + 1) : ℕ) : ℝ)) :=
    congrArg
      (fun gap : ℝ => t * gap)
      hlogGap_eq
  exact
    Eq.trans hparent_logGap hmul_logGap

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

/-- The fixed-width logarithmic gap is bounded by its rational gap factor. -/
theorem Real.logarithmicPhase_fixedWidthLogGap_le_reciprocal
    {h n : ℕ}
    (hn : 1 ≤ n) :
    Real.log ((((n + 1 : ℕ) : ℝ) / ((n : ℕ) : ℝ))) -
        Real.log ((((n + h + 1 : ℕ) : ℝ) / ((n + h : ℕ) : ℝ))) ≤
      (h : ℝ) / ((n * (n + h + 1) : ℕ) : ℝ) := by
  let q : ℝ := (h : ℝ) / ((n * (n + h + 1) : ℕ) : ℝ)
  have hgap_eq :
      Real.log ((((n + 1 : ℕ) : ℝ) / ((n : ℕ) : ℝ))) -
          Real.log ((((n + h + 1 : ℕ) : ℝ) / ((n + h : ℕ) : ℝ))) =
        Real.log ((1 : ℝ) + q) :=
    Real.logarithmicPhase_fixedWidthLogGap_eq hn
  have hden_pos :
      0 < ((n * (n + h + 1) : ℕ) : ℝ) :=
    Real.logarithmicPhase_fixedWidthGapDenominator_pos hn
  have hq_nonneg : 0 ≤ q :=
    div_nonneg (Nat.cast_nonneg h) (le_of_lt hden_pos)
  have hfactor_pos : 0 < (1 : ℝ) + q :=
    lt_of_lt_of_le zero_lt_one (le_add_of_nonneg_right hq_nonneg)
  have hlog_le_sub :
      Real.log ((1 : ℝ) + q) ≤ ((1 : ℝ) + q) - 1 :=
    Real.log_le_sub_one_of_pos hfactor_pos
  have hsub_eq : ((1 : ℝ) + q) - 1 = q := by
    calc
      ((1 : ℝ) + q) - 1 = (q + 1) - 1 :=
        congrArg (fun r : ℝ => r - 1) (add_comm (1 : ℝ) q)
      _ = q :=
        add_sub_cancel_right q 1
  have hlog_le_q : Real.log ((1 : ℝ) + q) ≤ q :=
    Eq.subst
      (motive := fun r : ℝ => Real.log ((1 : ℝ) + q) ≤ r)
      hsub_eq
      hlog_le_sub
  exact
    Eq.subst
      (motive := fun left : ℝ => left ≤ q)
      hgap_eq.symm
      hlog_le_q

/-- The fixed-width logarithmic gap is bounded below by the reciprocal of the
right normalized numerator. -/
theorem Real.reciprocal_succ_mul_shift_le_logarithmicPhase_fixedWidthLogGap
    {h n : ℕ}
    (hn : 1 ≤ n) :
    (h : ℝ) / (((n + 1) * (n + h) : ℕ) : ℝ) ≤
      Real.log ((((n + 1 : ℕ) : ℝ) / ((n : ℕ) : ℝ))) -
        Real.log ((((n + h + 1 : ℕ) : ℝ) / ((n + h : ℕ) : ℝ))) := by
  let D : ℝ := ((n * (n + h + 1) : ℕ) : ℝ)
  let H : ℝ := (h : ℝ)
  let P : ℝ := (((n + 1) * (n + h) : ℕ) : ℝ)
  let q : ℝ := H / D
  have hgap_eq :
      Real.log ((((n + 1 : ℕ) : ℝ) / ((n : ℕ) : ℝ))) -
          Real.log ((((n + h + 1 : ℕ) : ℝ) / ((n + h : ℕ) : ℝ))) =
        Real.log ((1 : ℝ) + q) :=
    Real.logarithmicPhase_fixedWidthLogGap_eq hn
  have hD_pos : 0 < D :=
    Real.logarithmicPhase_fixedWidthGapDenominator_pos hn
  have hD_ne : D ≠ 0 :=
    ne_of_gt hD_pos
  have hq_nonneg : 0 ≤ q :=
    div_nonneg (Nat.cast_nonneg h) (le_of_lt hD_pos)
  have hfactor_pos : 0 < (1 : ℝ) + q :=
    lt_of_lt_of_le zero_lt_one (le_add_of_nonneg_right hq_nonneg)
  have hlog_lower :
      (1 : ℝ) - (((1 : ℝ) + q)⁻¹) ≤ Real.log ((1 : ℝ) + q) :=
    Real.one_sub_inv_le_log_of_pos hfactor_pos
  have hP_eq : P = D + H :=
    Real.logarithmicPhase_fixedWidthGapNumerator_eq h n
  have hP_pos : 0 < P := by
    have hD_add_H_pos : 0 < D + H :=
      lt_of_lt_of_le hD_pos (le_add_of_nonneg_right (Nat.cast_nonneg h))
    exact
      Eq.subst
        (motive := fun r : ℝ => 0 < r)
        hP_eq.symm
        hD_add_H_pos
  have hP_ne : P ≠ 0 :=
    ne_of_gt hP_pos
  have hfactor_eq : (1 : ℝ) + q = P / D := by
    have hone_add :
        (1 : ℝ) + H / D = (D + H) / D :=
      one_add_div hD_ne
    exact
      Eq.trans hone_add
        (congrArg (fun r : ℝ => r / D) hP_eq.symm)
  have hinv_factor : (((1 : ℝ) + q)⁻¹) = D / P := by
    have hdiv_inv : (P / D)⁻¹ = D / P :=
      inv_div P D
    exact
      Eq.trans (congrArg Inv.inv hfactor_eq) hdiv_inv
  have hone_as_div : (1 : ℝ) = P / P :=
    (div_self hP_ne).symm
  have hsub_div :
      (1 : ℝ) - (((1 : ℝ) + q)⁻¹) = H / P := by
    calc
      (1 : ℝ) - (((1 : ℝ) + q)⁻¹) =
          P / P - (((1 : ℝ) + q)⁻¹) := by
        exact congrArg (fun r : ℝ => r - (((1 : ℝ) + q)⁻¹)) hone_as_div
      _ = P / P - D / P := by
        exact congrArg (fun r : ℝ => P / P - r) hinv_factor
      _ = (P - D) / P := by
        exact (sub_div P D P).symm
      _ = ((D + H) - D) / P := by
        exact
          congrArg
            (fun r : ℝ => (r - D) / P)
            hP_eq
      _ = H / P := by
        exact congrArg (fun r : ℝ => r / P) (add_sub_cancel_left D H)
  have hlower_to_gap :
      H / P ≤
        Real.log ((((n + 1 : ℕ) : ℝ) / ((n : ℕ) : ℝ))) -
          Real.log ((((n + h + 1 : ℕ) : ℝ) / ((n + h : ℕ) : ℝ))) :=
    Eq.subst
      (motive := fun left : ℝ =>
        left ≤
          Real.log ((((n + 1 : ℕ) : ℝ) / ((n : ℕ) : ℝ))) -
            Real.log ((((n + h + 1 : ℕ) : ℝ) / ((n + h : ℕ) : ℝ))))
      hsub_div
      (Eq.subst
        (motive := fun right : ℝ =>
          (1 : ℝ) - (((1 : ℝ) + q)⁻¹) ≤ right)
        hgap_eq.symm
        hlog_lower)
  exact hlower_to_gap

/-- Positive-frequency shifted logarithmic increments are bounded by the
scaled rational fixed-width gap factor. -/
theorem Complex.logarithmicPhaseRealPhase_shiftedDifference_integerIncrement_le_scaled_reciprocal
    (t : ℝ)
    (ht_nonneg : 0 ≤ t)
    {h n : ℕ}
    (hn : 1 ≤ n) :
    Complex.realPhase_integerIncrement
        (Complex.logarithmicPhaseRealPhase_shiftedDifference t h) n ≤
      t * ((h : ℝ) / ((n * (n + h + 1) : ℕ) : ℝ)) := by
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
  have hgap_le :
      Real.log ((((n + 1 : ℕ) : ℝ) / ((n : ℕ) : ℝ))) -
          Real.log ((((n + h + 1 : ℕ) : ℝ) / ((n + h : ℕ) : ℝ))) ≤
        (h : ℝ) / ((n * (n + h + 1) : ℕ) : ℝ) :=
    Real.logarithmicPhase_fixedWidthLogGap_le_reciprocal hn
  have hscaled :
      t *
          (Real.log ((((n + 1 : ℕ) : ℝ) / ((n : ℕ) : ℝ))) -
            Real.log ((((n + h + 1 : ℕ) : ℝ) / ((n + h : ℕ) : ℝ)))) ≤
        t * ((h : ℝ) / ((n * (n + h + 1) : ℕ) : ℝ)) :=
    mul_le_mul_of_nonneg_left hgap_le ht_nonneg
  exact
    Eq.subst
      (motive := fun left : ℝ =>
        left ≤ t * ((h : ℝ) / ((n * (n + h + 1) : ℕ) : ℝ)))
      hshift.symm
      (Eq.subst
        (motive := fun right : ℝ =>
          right ≤ t * ((h : ℝ) / ((n * (n + h + 1) : ℕ) : ℝ)))
        hparent.symm
        hscaled)

/-- Positive-frequency shifted logarithmic increments are bounded below by
the right normalized reciprocal fixed-width gap factor. -/
theorem Complex.logarithmicPhaseRealPhase_shiftedDifference_scaled_reciprocal_succ_mul_shift_le_integerIncrement
    (t : ℝ)
    (ht_nonneg : 0 ≤ t)
    {h n : ℕ}
    (hn : 1 ≤ n) :
    t * ((h : ℝ) / (((n + 1) * (n + h) : ℕ) : ℝ)) ≤
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
  have hgap_lower :
      (h : ℝ) / (((n + 1) * (n + h) : ℕ) : ℝ) ≤
        Real.log ((((n + 1 : ℕ) : ℝ) / ((n : ℕ) : ℝ))) -
          Real.log ((((n + h + 1 : ℕ) : ℝ) / ((n + h : ℕ) : ℝ))) :=
    Real.reciprocal_succ_mul_shift_le_logarithmicPhase_fixedWidthLogGap hn
  have hscaled :
      t * ((h : ℝ) / (((n + 1) * (n + h) : ℕ) : ℝ)) ≤
        t *
          (Real.log ((((n + 1 : ℕ) : ℝ) / ((n : ℕ) : ℝ))) -
            Real.log ((((n + h + 1 : ℕ) : ℝ) / ((n + h : ℕ) : ℝ)))) :=
    mul_le_mul_of_nonneg_left hgap_lower ht_nonneg
  exact
    Eq.subst
      (motive := fun right : ℝ =>
        t * ((h : ℝ) / (((n + 1) * (n + h) : ℕ) : ℝ)) ≤ right)
      hshift.symm
      (Eq.subst
        (motive := fun right : ℝ =>
          t * ((h : ℝ) / (((n + 1) * (n + h) : ℕ) : ℝ)) ≤ right)
        hparent.symm
        hscaled)

/-- The endpoint spread of positive-frequency shifted logarithmic adjacent
increments is bounded below by the difference of the rational lower/upper
fixed-width gap factors. -/
theorem Complex.logarithmicPhaseRealPhase_shiftedDifference_rational_endpoint_spread_le_integerIncrement_spread
    (t : ℝ)
    (ht_nonneg : 0 ≤ t)
    {h m n : ℕ}
    (hm : 1 ≤ m)
    (hmn : m ≤ n) :
    t *
        (((h : ℝ) / (((m + 1) * (m + h) : ℕ) : ℝ)) -
          ((h : ℝ) / ((n * (n + h + 1) : ℕ) : ℝ))) ≤
      Complex.realPhase_integerIncrement
          (Complex.logarithmicPhaseRealPhase_shiftedDifference t h) m -
        Complex.realPhase_integerIncrement
          (Complex.logarithmicPhaseRealPhase_shiftedDifference t h) n := by
  have hn : 1 ≤ n :=
    le_trans hm hmn
  have hleft_lower :
      t * ((h : ℝ) / (((m + 1) * (m + h) : ℕ) : ℝ)) ≤
        Complex.realPhase_integerIncrement
          (Complex.logarithmicPhaseRealPhase_shiftedDifference t h) m :=
    Complex.logarithmicPhaseRealPhase_shiftedDifference_scaled_reciprocal_succ_mul_shift_le_integerIncrement
      t ht_nonneg hm
  have hright_upper :
      Complex.realPhase_integerIncrement
          (Complex.logarithmicPhaseRealPhase_shiftedDifference t h) n ≤
        t * ((h : ℝ) / ((n * (n + h + 1) : ℕ) : ℝ)) :=
    Complex.logarithmicPhaseRealPhase_shiftedDifference_integerIncrement_le_scaled_reciprocal
      t ht_nonneg hn
  have hneg_right :
      -(t * ((h : ℝ) / ((n * (n + h + 1) : ℕ) : ℝ))) ≤
        -Complex.realPhase_integerIncrement
          (Complex.logarithmicPhaseRealPhase_shiftedDifference t h) n :=
    neg_le_neg hright_upper
  have hsum :
      t * ((h : ℝ) / (((m + 1) * (m + h) : ℕ) : ℝ)) +
          -(t * ((h : ℝ) / ((n * (n + h + 1) : ℕ) : ℝ))) ≤
        Complex.realPhase_integerIncrement
            (Complex.logarithmicPhaseRealPhase_shiftedDifference t h) m +
          -Complex.realPhase_integerIncrement
            (Complex.logarithmicPhaseRealPhase_shiftedDifference t h) n :=
    add_le_add hleft_lower hneg_right
  have hleft_eq :
      t *
          (((h : ℝ) / (((m + 1) * (m + h) : ℕ) : ℝ)) -
            ((h : ℝ) / ((n * (n + h + 1) : ℕ) : ℝ))) =
        t * ((h : ℝ) / (((m + 1) * (m + h) : ℕ) : ℝ)) +
          -(t * ((h : ℝ) / ((n * (n + h + 1) : ℕ) : ℝ))) := by
    calc
      t *
          (((h : ℝ) / (((m + 1) * (m + h) : ℕ) : ℝ)) -
            ((h : ℝ) / ((n * (n + h + 1) : ℕ) : ℝ))) =
        t * ((h : ℝ) / (((m + 1) * (m + h) : ℕ) : ℝ)) -
          t * ((h : ℝ) / ((n * (n + h + 1) : ℕ) : ℝ)) := by
        exact mul_sub t
          ((h : ℝ) / (((m + 1) * (m + h) : ℕ) : ℝ))
          ((h : ℝ) / ((n * (n + h + 1) : ℕ) : ℝ))
      _ =
        t * ((h : ℝ) / (((m + 1) * (m + h) : ℕ) : ℝ)) +
          -(t * ((h : ℝ) / ((n * (n + h + 1) : ℕ) : ℝ))) := by
        exact sub_eq_add_neg
          (t * ((h : ℝ) / (((m + 1) * (m + h) : ℕ) : ℝ)))
          (t * ((h : ℝ) / ((n * (n + h + 1) : ℕ) : ℝ)))
  have hright_eq :
      Complex.realPhase_integerIncrement
          (Complex.logarithmicPhaseRealPhase_shiftedDifference t h) m -
        Complex.realPhase_integerIncrement
          (Complex.logarithmicPhaseRealPhase_shiftedDifference t h) n =
        Complex.realPhase_integerIncrement
            (Complex.logarithmicPhaseRealPhase_shiftedDifference t h) m +
          -Complex.realPhase_integerIncrement
            (Complex.logarithmicPhaseRealPhase_shiftedDifference t h) n :=
    sub_eq_add_neg
      (Complex.realPhase_integerIncrement
        (Complex.logarithmicPhaseRealPhase_shiftedDifference t h) m)
      (Complex.realPhase_integerIncrement
        (Complex.logarithmicPhaseRealPhase_shiftedDifference t h) n)
  exact
    Eq.subst
      (motive := fun left : ℝ =>
        left ≤
          Complex.realPhase_integerIncrement
              (Complex.logarithmicPhaseRealPhase_shiftedDifference t h) m -
            Complex.realPhase_integerIncrement
              (Complex.logarithmicPhaseRealPhase_shiftedDifference t h) n)
      hleft_eq.symm
      (Eq.subst
        (motive := fun right : ℝ =>
          t * ((h : ℝ) / (((m + 1) * (m + h) : ℕ) : ℝ)) +
              -(t * ((h : ℝ) / ((n * (n + h + 1) : ℕ) : ℝ))) ≤ right)
        hright_eq.symm
        hsum)

/-- Normed nonnegative-frequency form of the rational endpoint-spread lower
bound for shifted logarithmic adjacent increments. -/
theorem Complex.logarithmicPhaseRealPhase_shiftedDifference_norm_rational_endpoint_spread_le_integerIncrement_spread
    (t : ℝ)
    (ht_nonneg : 0 ≤ t)
    {h m n : ℕ}
    (hm : 1 ≤ m)
    (hmn : m ≤ n) :
    ‖t‖ *
        (((h : ℝ) / (((m + 1) * (m + h) : ℕ) : ℝ)) -
          ((h : ℝ) / ((n * (n + h + 1) : ℕ) : ℝ))) ≤
      Complex.realPhase_integerIncrement
          (Complex.logarithmicPhaseRealPhase_shiftedDifference t h) m -
        Complex.realPhase_integerIncrement
          (Complex.logarithmicPhaseRealPhase_shiftedDifference t h) n := by
  have hnorm : ‖t‖ = t :=
    Real.norm_of_nonneg ht_nonneg
  have hsigned :
      t *
          (((h : ℝ) / (((m + 1) * (m + h) : ℕ) : ℝ)) -
            ((h : ℝ) / ((n * (n + h + 1) : ℕ) : ℝ))) ≤
        Complex.realPhase_integerIncrement
            (Complex.logarithmicPhaseRealPhase_shiftedDifference t h) m -
          Complex.realPhase_integerIncrement
            (Complex.logarithmicPhaseRealPhase_shiftedDifference t h) n :=
    Complex.logarithmicPhaseRealPhase_shiftedDifference_rational_endpoint_spread_le_integerIncrement_spread
      t ht_nonneg hm hmn
  exact
    Eq.subst
      (motive := fun left : ℝ =>
        left *
            (((h : ℝ) / (((m + 1) * (m + h) : ℕ) : ℝ)) -
              ((h : ℝ) / ((n * (n + h + 1) : ℕ) : ℝ))) ≤
          Complex.realPhase_integerIncrement
              (Complex.logarithmicPhaseRealPhase_shiftedDifference t h) m -
            Complex.realPhase_integerIncrement
              (Complex.logarithmicPhaseRealPhase_shiftedDifference t h) n)
      hnorm.symm
      hsigned

/-- If the endpoint square dominates the fixed-width denominator, then the
standard shifted lower parameter is below the adjacent increment. -/
theorem Complex.logarithmicPhaseRealPhase_shiftedDifference_lowerParameter_le_integerIncrement_of_denominator_le
    (t : ℝ)
    (ht_nonneg : 0 ≤ t)
    {b h n : ℕ}
    (hn : 1 ≤ n)
    (hden :
      ((n + 1) * (n + h) : ℕ) ≤ (b + 1) * (b + 1)) :
    t *
        ((((b + 1 : ℕ) : ℝ) *
          (((b + 1 : ℕ) : ℝ)))⁻¹) *
        (h : ℝ) ≤
      Complex.realPhase_integerIncrement
        (Complex.logarithmicPhaseRealPhase_shiftedDifference t h) n := by
  let P : ℝ := (((n + 1) * (n + h) : ℕ) : ℝ)
  let Bsq : ℝ :=
    (((b + 1 : ℕ) : ℝ) * (((b + 1 : ℕ) : ℝ)))
  have hP_pos : 0 < P := by
    have hn_pos : 0 < n :=
      Nat.lt_of_succ_le hn
    have hn_succ_pos : 0 < n + 1 :=
      Nat.succ_pos n
    have hn_h_pos : 0 < n + h :=
      lt_of_lt_of_le hn_pos (Nat.le_add_right n h)
    have hprod_pos : 0 < (n + 1) * (n + h) :=
      Nat.mul_pos hn_succ_pos hn_h_pos
    exact Nat.cast_pos.mpr hprod_pos
  have hB_pos : 0 < (((b + 1 : ℕ) : ℝ)) :=
    Nat.cast_pos.mpr (Nat.succ_pos b)
  have hBsq_pos : 0 < Bsq :=
    mul_pos hB_pos hB_pos
  have hP_le_Bsq : P ≤ Bsq := by
    have hcast :
        (((n + 1) * (n + h) : ℕ) : ℝ) ≤
          (((b + 1) * (b + 1) : ℕ) : ℝ) :=
      Nat.cast_le.mpr hden
    have hBsq_cast :
        (((b + 1) * (b + 1) : ℕ) : ℝ) = Bsq :=
      Nat.cast_mul (b + 1) (b + 1)
    exact
      Eq.subst
        (motive := fun right : ℝ => P ≤ right)
        hBsq_cast
        hcast
  have hnum_nonneg : 0 ≤ (h : ℝ) :=
    Nat.cast_nonneg h
  have hreciprocal :
      (h : ℝ) / Bsq ≤ (h : ℝ) / P :=
    div_le_div_of_nonneg_left hnum_nonneg hP_pos hP_le_Bsq
  have hleft_eq :
      t *
          ((((b + 1 : ℕ) : ℝ) *
            (((b + 1 : ℕ) : ℝ)))⁻¹) *
          (h : ℝ) =
        t * ((h : ℝ) / Bsq) := by
    calc
      t *
          ((((b + 1 : ℕ) : ℝ) *
            (((b + 1 : ℕ) : ℝ)))⁻¹) *
          (h : ℝ) =
          (t * Bsq⁻¹) * (h : ℝ) := by
        rfl
      _ = t * (Bsq⁻¹ * (h : ℝ)) := by
        exact mul_assoc t Bsq⁻¹ (h : ℝ)
      _ = t * ((h : ℝ) * Bsq⁻¹) := by
        exact congrArg (fun r : ℝ => t * r) (mul_comm Bsq⁻¹ (h : ℝ))
      _ = t * ((h : ℝ) / Bsq) := by
        exact congrArg (fun r : ℝ => t * r) (div_eq_mul_inv (h : ℝ) Bsq).symm
  have hscaled :
      t * ((h : ℝ) / Bsq) ≤ t * ((h : ℝ) / P) :=
    mul_le_mul_of_nonneg_left hreciprocal ht_nonneg
  have hincrement_lower :
      t * ((h : ℝ) / P) ≤
        Complex.realPhase_integerIncrement
          (Complex.logarithmicPhaseRealPhase_shiftedDifference t h) n :=
    Complex.logarithmicPhaseRealPhase_shiftedDifference_scaled_reciprocal_succ_mul_shift_le_integerIncrement
      t ht_nonneg hn
  exact
    Eq.subst
      (motive := fun left : ℝ =>
        left ≤
          Complex.realPhase_integerIncrement
            (Complex.logarithmicPhaseRealPhase_shiftedDifference t h) n)
      hleft_eq.symm
      (le_trans hscaled hincrement_lower)

/-- A scaled rational fixed-width gap bound implies the pointwise `π` bound
needed for no-winding of shifted logarithmic increments. -/
theorem Complex.logarithmicPhaseRealPhase_shiftedDifference_integerIncrement_le_pi_of_scaled_reciprocal
    (t : ℝ)
    (ht_nonneg : 0 ≤ t)
    {h n : ℕ}
    (hn : 1 ≤ n)
    (hscaled_pi :
      t * ((h : ℝ) / ((n * (n + h + 1) : ℕ) : ℝ)) ≤ Real.pi) :
    Complex.realPhase_integerIncrement
        (Complex.logarithmicPhaseRealPhase_shiftedDifference t h) n ≤
      Real.pi :=
  le_trans
    (Complex.logarithmicPhaseRealPhase_shiftedDifference_integerIncrement_le_scaled_reciprocal
      t ht_nonneg hn)
    hscaled_pi

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
