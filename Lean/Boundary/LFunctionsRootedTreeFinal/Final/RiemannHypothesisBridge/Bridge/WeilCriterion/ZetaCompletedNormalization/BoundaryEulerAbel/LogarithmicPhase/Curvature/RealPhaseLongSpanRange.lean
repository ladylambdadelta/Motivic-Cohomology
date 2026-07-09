import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalization.BoundaryEulerAbel.LogarithmicPhase.Curvature.RealPhaseLogGap
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalization.BoundaryEulerAbel.LogarithmicPhase.Curvature.RealPhaseResonancePartition

/-!
# Span-local long shifted-increment ranges

This file owns the local endpoint range used by the all-integer monotone
curvature decomposition.  The point is to count resonances from the actual
increment span on a half-open block, not from the absolute left endpoint height
on the whole long block.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open scoped Topology

/-- Upper rational endpoint for shifted logarithmic increments on a half-open
block beginning at `c`. -/
abbrev Real.logarithmicPhaseRealPhase_spanIncrementHi
    (t : ℝ)
    (c h : ℕ) : ℝ :=
  t * ((h : ℝ) / ((c * (c + h + 1) : ℕ) : ℝ))

/-- Lower rational endpoint for shifted logarithmic increments on a nonempty
half-open block ending at `d`.  For `n = d - 1`, the lower fixed-width gap
denominator is `(n + 1) * (n + h)`. -/
abbrev Real.logarithmicPhaseRealPhase_spanIncrementLo
    (t : ℝ)
    (d h : ℕ) : ℝ :=
  t * ((h : ℝ) / ((d * (d - 1 + h) : ℕ) : ℝ))

/-- Width of the local rational endpoint span for shifted logarithmic
increments on `Ico c d`. -/
abbrev Real.logarithmicPhaseRealPhase_spanIncrementWidth
    (t : ℝ)
    (c d h : ℕ) : ℝ :=
  Real.logarithmicPhaseRealPhase_spanIncrementHi t c h -
    Real.logarithmicPhaseRealPhase_spanIncrementLo t d h

/-- The lower span endpoint is below every shifted logarithmic increment in
the half-open block. -/
theorem Complex.logarithmicPhaseRealPhase_shiftedDifference_spanIncrementLo_le_integerIncrement
    (t : ℝ)
    (ht_nonneg : 0 ≤ t)
    {c d h n : ℕ}
    (hc : 1 ≤ c)
    (hn : n ∈ Finset.Ico c d) :
    Real.logarithmicPhaseRealPhase_spanIncrementLo t d h ≤
      Complex.realPhase_integerIncrement
        (Complex.realPhase_secondDerivative_vdc_shiftedDifference
          (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
          h)
        n := by
  have hn_bounds : c ≤ n ∧ n < d :=
    Finset.mem_Ico.mp hn
  have hn_one : 1 ≤ n :=
    le_trans hc hn_bounds.1
  have hn_succ_le : n + 1 ≤ d :=
    Nat.succ_le_of_lt hn_bounds.2
  have hn_le_pred : n ≤ d - 1 :=
    Nat.le_pred_of_lt hn_bounds.2
  have hn_shift_le : n + h ≤ d - 1 + h :=
    Nat.add_le_add_right hn_le_pred h
  have hden :
      ((n + 1) * (n + h) : ℕ) ≤ d * (d - 1 + h) :=
    Nat.mul_le_mul hn_succ_le hn_shift_le
  let P : ℝ := (((n + 1) * (n + h) : ℕ) : ℝ)
  let D : ℝ := ((d * (d - 1 + h) : ℕ) : ℝ)
  have hP_pos : 0 < P := by
    have hn_pos : 0 < n :=
      Nat.lt_of_succ_le hn_one
    have hn_succ_pos : 0 < n + 1 :=
      Nat.succ_pos n
    have hn_h_pos : 0 < n + h :=
      lt_of_lt_of_le hn_pos (Nat.le_add_right n h)
    have hprod_pos : 0 < (n + 1) * (n + h) :=
      Nat.mul_pos hn_succ_pos hn_h_pos
    exact Nat.cast_pos.mpr hprod_pos
  have hP_le_D : P ≤ D :=
    Nat.cast_le.mpr hden
  have hnum_nonneg : 0 ≤ (h : ℝ) :=
    Nat.cast_nonneg h
  have hrec :
      (h : ℝ) / D ≤ (h : ℝ) / P :=
    div_le_div_of_nonneg_left hnum_nonneg hP_pos hP_le_D
  have hscaled :
      t * ((h : ℝ) / D) ≤ t * ((h : ℝ) / P) :=
    mul_le_mul_of_nonneg_left hrec ht_nonneg
  have hpoint :
      t * ((h : ℝ) / P) ≤
        Complex.realPhase_integerIncrement
          (Complex.logarithmicPhaseRealPhase_shiftedDifference t h)
          n :=
    Complex.logarithmicPhaseRealPhase_shiftedDifference_scaled_reciprocal_succ_mul_shift_le_integerIncrement
      t ht_nonneg hn_one
  exact le_trans hscaled hpoint

/-- The upper span endpoint is above every shifted logarithmic increment in
the half-open block. -/
theorem Complex.logarithmicPhaseRealPhase_shiftedDifference_integerIncrement_le_spanIncrementHi
    (t : ℝ)
    (ht_nonneg : 0 ≤ t)
    {c d h n : ℕ}
    (hc : 1 ≤ c)
    (hn : n ∈ Finset.Ico c d) :
    Complex.realPhase_integerIncrement
        (Complex.realPhase_secondDerivative_vdc_shiftedDifference
          (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
          h)
        n ≤
      Real.logarithmicPhaseRealPhase_spanIncrementHi t c h := by
  have hn_bounds : c ≤ n ∧ n < d :=
    Finset.mem_Ico.mp hn
  have hn_one : 1 ≤ n :=
    le_trans hc hn_bounds.1
  have hpoint :
      Complex.realPhase_integerIncrement
          (Complex.logarithmicPhaseRealPhase_shiftedDifference t h)
          n ≤
        t * ((h : ℝ) / ((n * (n + h + 1) : ℕ) : ℝ)) :=
    Complex.logarithmicPhaseRealPhase_shiftedDifference_integerIncrement_le_scaled_reciprocal
      t ht_nonneg hn_one
  have hrec :
      ((h : ℝ) / ((n * (n + h + 1) : ℕ) : ℝ)) ≤
        ((h : ℝ) / ((c * (c + h + 1) : ℕ) : ℝ)) :=
    Real.logarithmicPhase_fixedWidthGapReciprocal_antitone
      hc hn_bounds.1
  have hscaled :
      t * ((h : ℝ) / ((n * (n + h + 1) : ℕ) : ℝ)) ≤
        t * ((h : ℝ) / ((c * (c + h + 1) : ℕ) : ℝ)) :=
    mul_le_mul_of_nonneg_left hrec ht_nonneg
  exact le_trans hpoint hscaled

/-- Shifted logarithmic increments on a half-open block lie in the local
endpoint span determined by that same block. -/
theorem Complex.logarithmicPhaseRealPhase_shiftedDifference_integerIncrement_mem_span_range
    (t : ℝ)
    (ht_nonneg : 0 ≤ t)
    {c d h n : ℕ}
    (hc : 1 ≤ c)
    (hn : n ∈ Finset.Ico c d) :
    Real.logarithmicPhaseRealPhase_spanIncrementLo t d h ≤
          Complex.realPhase_integerIncrement
            (Complex.realPhase_secondDerivative_vdc_shiftedDifference
              (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
              h)
            n ∧
        Complex.realPhase_integerIncrement
            (Complex.realPhase_secondDerivative_vdc_shiftedDifference
              (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
              h)
            n ≤
          Real.logarithmicPhaseRealPhase_spanIncrementHi t c h :=
  And.intro
    (Complex.logarithmicPhaseRealPhase_shiftedDifference_spanIncrementLo_le_integerIncrement
      t ht_nonneg hc hn)
    (Complex.logarithmicPhaseRealPhase_shiftedDifference_integerIncrement_le_spanIncrementHi
      t ht_nonneg hc hn)

/-- On a nonempty positive half-open block, the span lower endpoint is below
the span upper endpoint. -/
theorem Real.logarithmicPhaseRealPhase_spanIncrementLo_le_spanIncrementHi
    (t : ℝ)
    (ht_nonneg : 0 ≤ t)
    {c d h : ℕ}
    (hc : 1 ≤ c)
    (hcd : c < d) :
    Real.logarithmicPhaseRealPhase_spanIncrementLo t d h ≤
      Real.logarithmicPhaseRealPhase_spanIncrementHi t c h := by
  have hn : d - 1 ∈ Finset.Ico c d := by
    have hc_le_pred : c ≤ d - 1 :=
      Nat.le_pred_of_lt hcd
    have hd_pos : 0 < d :=
      lt_of_lt_of_le (Nat.zero_lt_one) (le_trans hc (le_of_lt hcd))
    have hpred_lt : d - 1 < d :=
      Nat.sub_lt hd_pos (Nat.zero_lt_one)
    exact Finset.mem_Ico.mpr (And.intro hc_le_pred hpred_lt)
  have hrange :
      Real.logarithmicPhaseRealPhase_spanIncrementLo t d h ≤
            Complex.realPhase_integerIncrement
              (Complex.realPhase_secondDerivative_vdc_shiftedDifference
                (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
                h)
              (d - 1) ∧
          Complex.realPhase_integerIncrement
              (Complex.realPhase_secondDerivative_vdc_shiftedDifference
                (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
                h)
              (d - 1) ≤
            Real.logarithmicPhaseRealPhase_spanIncrementHi t c h :=
    Complex.logarithmicPhaseRealPhase_shiftedDifference_integerIncrement_mem_span_range
      t ht_nonneg hc hn
  exact le_trans hrange.1 hrange.2

/-- Span-local active-center cardinality bound. -/
theorem Complex.realPhase_integerIncrementRangeActiveCenters_span_card_real_le_width_add_five
    (t : ℝ)
    (ht_nonneg : 0 ≤ t)
    {c d h : ℕ}
    (hc : 1 ≤ c)
    (hcd : c < d)
    {eta : ℝ}
    (heta_nonneg : 0 ≤ eta) :
    ((Complex.realPhase_integerIncrementRangeActiveCenters
        (Real.logarithmicPhaseRealPhase_spanIncrementLo t d h)
        (Real.logarithmicPhaseRealPhase_spanIncrementHi t c h)
        eta).card : ℝ) ≤
      (((Real.logarithmicPhaseRealPhase_spanIncrementHi t c h + eta) /
          (2 * Real.pi)) -
        ((Real.logarithmicPhaseRealPhase_spanIncrementLo t d h - eta) /
          (2 * Real.pi)) + 5) :=
  Complex.realPhase_integerIncrementRangeActiveCenters_card_real_le_width_add_five
    (Real.logarithmicPhaseRealPhase_spanIncrementLo_le_spanIncrementHi
      t ht_nonneg hc hcd)
    heta_nonneg

end

end LFunctions
end Boundary
