import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalization.BoundaryEulerAbel.LogarithmicPhase.Curvature.RealPhaseResonancePartition

/-!
# Empty zero-centered resonance windows

This file owns the bridge from pointwise lower bounds for shifted logarithmic
increments to emptiness of the strict zero-centered resonance window.
-/

namespace Boundary
namespace LFunctions

noncomputable section

/-- On a shifted half-open block, the fixed-width denominator is dominated by
the square of the right endpoint. -/
theorem Nat.logarithmicPhase_fixedWidthDenominator_le_endpointSquare_of_mem_Ico
    {a b h n : ℕ}
    (hn : n ∈ Finset.Ico a (b - h)) :
    (n + 1) * (n + h) ≤ (b + 1) * (b + 1) := by
  have hn_bounds : a ≤ n ∧ n < b - h :=
    Finset.mem_Ico.mp hn
  have hsub_le_b : b - h ≤ b :=
    Nat.sub_le b h
  have hn_lt_b : n < b :=
    lt_of_lt_of_le hn_bounds.2 hsub_le_b
  have hn_succ_le_b : n + 1 ≤ b :=
    Nat.succ_le_iff.mpr hn_lt_b
  have hn_succ_le_endpoint : n + 1 ≤ b + 1 :=
    le_trans hn_succ_le_b (Nat.le_succ b)
  have hn_add_h_lt_b : n + h < b :=
    Nat.lt_sub_iff_add_lt.mp hn_bounds.2
  have hn_add_h_le_b : n + h ≤ b :=
    Nat.le_of_lt hn_add_h_lt_b
  have hn_add_h_le_endpoint : n + h ≤ b + 1 :=
    le_trans hn_add_h_le_b (Nat.le_succ b)
  exact Nat.mul_le_mul hn_succ_le_endpoint hn_add_h_le_endpoint

/-- A strict zero-centered integer-increment resonance window is empty when
every point of the ambient block is at least the window radius from zero. -/
theorem Complex.realPhase_integerIncrement_zero_resonanceWindow_eq_empty_of_lower_bound
    (φ : ℝ → ℝ)
    {a b : ℕ}
    {lam : ℝ}
    (hlower :
      ∀ n : ℕ,
        n ∈ Finset.Ico a b →
          lam ≤ Complex.realPhase_integerIncrement φ n) :
    Complex.realPhase_integerIncrementResonanceWindow
        φ a b (2 * Real.pi * (0 : ℝ)) lam =
      ∅ := by
  have hzero : 2 * Real.pi * (0 : ℝ) = 0 :=
    mul_zero (2 * Real.pi)
  exact
    Finset.ext
      (fun n =>
        Iff.intro
          (fun hn =>
            have hdata :
                n ∈ Finset.Ico a b ∧
                  ‖Complex.realPhase_integerIncrement φ n -
                    (2 * Real.pi * (0 : ℝ))‖ < lam :=
              (Complex.mem_realPhase_integerIncrementResonanceWindow_iff
                (φ := φ)
                (a := a)
                (b := b)
                (n := n)
                (resonance := 2 * Real.pi * (0 : ℝ))
                (lam := lam)).mp hn
            have hlower_n :
                lam ≤ Complex.realPhase_integerIncrement φ n :=
              hlower n hdata.1
            have hinc_le_abs :
                Complex.realPhase_integerIncrement φ n ≤
                  ‖Complex.realPhase_integerIncrement φ n -
                    (2 * Real.pi * (0 : ℝ))‖ := by
              have hinc_le_abs_zero :
                  Complex.realPhase_integerIncrement φ n ≤
                    ‖Complex.realPhase_integerIncrement φ n - 0‖ := by
                exact le_abs_self (Complex.realPhase_integerIncrement φ n)
              exact
                Eq.subst
                  (motive := fun r : ℝ =>
                    Complex.realPhase_integerIncrement φ n ≤
                      ‖Complex.realPhase_integerIncrement φ n - r‖)
                  hzero.symm
                  hinc_le_abs_zero
            have hnot_lt :
                ¬ ‖Complex.realPhase_integerIncrement φ n -
                    (2 * Real.pi * (0 : ℝ))‖ < lam :=
              not_lt_of_ge (le_trans hlower_n hinc_le_abs)
            False.elim (hnot_lt hdata.2))
          (fun hn_empty => False.elim (Finset.not_mem_empty n hn_empty)))

/-- Shifted-logarithmic specialization of zero-window emptiness. -/
theorem Complex.logarithmicPhaseRealPhase_shiftedDifference_zero_resonanceWindow_eq_empty_of_lower_bound
    (t : ℝ)
    {a b h : ℕ}
    {lam : ℝ}
    (hlower :
      ∀ n : ℕ,
        n ∈ Finset.Ico a (b - h) →
          lam ≤
            Complex.realPhase_integerIncrement
              (Complex.realPhase_secondDerivative_vdc_shiftedDifference
                (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
                h)
              n) :
    Complex.realPhase_integerIncrementResonanceWindow
        (Complex.realPhase_secondDerivative_vdc_shiftedDifference
          (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
          h)
        a (b - h) (2 * Real.pi * (0 : ℝ)) lam =
      ∅ := by
  exact
    Complex.realPhase_integerIncrement_zero_resonanceWindow_eq_empty_of_lower_bound
      (Complex.realPhase_secondDerivative_vdc_shiftedDifference
        (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
        h)
      hlower

/-- The zero-centered shifted-logarithmic resonance window is empty when the
endpoint square dominates the fixed-width denominator throughout the block. -/
theorem Complex.logarithmicPhaseRealPhase_shiftedDifference_zero_resonanceWindow_eq_empty_of_denominator_le
    (t : ℝ)
    (ht_nonneg : 0 ≤ t)
    {a b h : ℕ}
    (ha : 1 ≤ a)
    (hden :
      ∀ n : ℕ,
        n ∈ Finset.Ico a (b - h) →
          ((n + 1) * (n + h) : ℕ) ≤ (b + 1) * (b + 1)) :
    Complex.realPhase_integerIncrementResonanceWindow
        (Complex.realPhase_secondDerivative_vdc_shiftedDifference
          (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
          h)
        a (b - h) (2 * Real.pi * (0 : ℝ))
        (t *
          ((((b + 1 : ℕ) : ℝ) *
            (((b + 1 : ℕ) : ℝ)))⁻¹) *
          (h : ℝ)) =
      ∅ := by
  have hlower :
      ∀ n : ℕ,
        n ∈ Finset.Ico a (b - h) →
          t *
              ((((b + 1 : ℕ) : ℝ) *
                (((b + 1 : ℕ) : ℝ)))⁻¹) *
              (h : ℝ) ≤
            Complex.realPhase_integerIncrement
              (Complex.realPhase_secondDerivative_vdc_shiftedDifference
                (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
                h)
              n := by
    intro n hn
    have hn_bounds : a ≤ n ∧ n < b - h :=
      Finset.mem_Ico.mp hn
    have hn_one : 1 ≤ n :=
      le_trans ha hn_bounds.1
    exact
      Complex.logarithmicPhaseRealPhase_shiftedDifference_lowerParameter_le_integerIncrement_of_denominator_le
        t ht_nonneg hn_one (hden n hn)
  exact
    Complex.logarithmicPhaseRealPhase_shiftedDifference_zero_resonanceWindow_eq_empty_of_lower_bound
      t hlower

/-- In the positive-frequency branch, the canonical zero-centered shifted
logarithmic resonance window is empty on every shifted half-open block. -/
theorem Complex.logarithmicPhaseRealPhase_shiftedDifference_zero_resonanceWindow_eq_empty_of_nonneg
    (t : ℝ)
    (ht_nonneg : 0 ≤ t)
    {a b h : ℕ}
    (ha : 1 ≤ a) :
    Complex.realPhase_integerIncrementResonanceWindow
        (Complex.realPhase_secondDerivative_vdc_shiftedDifference
          (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
          h)
        a (b - h) (2 * Real.pi * (0 : ℝ))
        (‖t‖ *
          ((((b + 1 : ℕ) : ℝ) *
            (((b + 1 : ℕ) : ℝ)))⁻¹) *
          (h : ℝ)) =
      ∅ := by
  have hempty_t :
      Complex.realPhase_integerIncrementResonanceWindow
          (Complex.realPhase_secondDerivative_vdc_shiftedDifference
            (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
            h)
          a (b - h) (2 * Real.pi * (0 : ℝ))
          (t *
            ((((b + 1 : ℕ) : ℝ) *
              (((b + 1 : ℕ) : ℝ)))⁻¹) *
            (h : ℝ)) =
        ∅ :=
    Complex.logarithmicPhaseRealPhase_shiftedDifference_zero_resonanceWindow_eq_empty_of_denominator_le
      t ht_nonneg ha
      (fun n hn =>
        Nat.logarithmicPhase_fixedWidthDenominator_le_endpointSquare_of_mem_Ico
          hn)
  have hnorm_eq : ‖t‖ = t :=
    Real.norm_of_nonneg ht_nonneg
  have hradius_eq :
      ‖t‖ *
          ((((b + 1 : ℕ) : ℝ) *
            (((b + 1 : ℕ) : ℝ)))⁻¹) *
          (h : ℝ) =
        t *
          ((((b + 1 : ℕ) : ℝ) *
            (((b + 1 : ℕ) : ℝ)))⁻¹) *
          (h : ℝ) :=
    congrArg
      (fun r : ℝ =>
        r *
          ((((b + 1 : ℕ) : ℝ) *
            (((b + 1 : ℕ) : ℝ)))⁻¹) *
          (h : ℝ))
      hnorm_eq
  exact
    Eq.subst
      (motive := fun radius : ℝ =>
        Complex.realPhase_integerIncrementResonanceWindow
            (Complex.realPhase_secondDerivative_vdc_shiftedDifference
              (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
              h)
            a (b - h) (2 * Real.pi * (0 : ℝ)) radius =
          ∅)
      hradius_eq.symm
      hempty_t

/-- Any half-open interval representing the canonical zero-centered shifted
logarithmic resonance window in the positive branch has zero length. -/
theorem Complex.logarithmicPhaseRealPhase_shiftedDifference_zero_resonanceWindow_Ico_length_le_zero_of_nonneg
    (t : ℝ)
    (ht_nonneg : 0 ≤ t)
    {a b h c d : ℕ}
    (ha : 1 ≤ a)
    (hwindow :
      Complex.realPhase_integerIncrementResonanceWindow
          (Complex.realPhase_secondDerivative_vdc_shiftedDifference
            (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
            h)
          a (b - h) (2 * Real.pi * (0 : ℝ))
          (‖t‖ *
            ((((b + 1 : ℕ) : ℝ) *
              (((b + 1 : ℕ) : ℝ)))⁻¹) *
            (h : ℝ)) =
        Finset.Ico c d) :
    ((d - c : ℕ) : ℝ) ≤ 0 := by
  have hempty :
      Complex.realPhase_integerIncrementResonanceWindow
          (Complex.realPhase_secondDerivative_vdc_shiftedDifference
            (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
            h)
          a (b - h) (2 * Real.pi * (0 : ℝ))
          (‖t‖ *
            ((((b + 1 : ℕ) : ℝ) *
              (((b + 1 : ℕ) : ℝ)))⁻¹) *
            (h : ℝ)) =
        ∅ :=
    Complex.logarithmicPhaseRealPhase_shiftedDifference_zero_resonanceWindow_eq_empty_of_nonneg
      t ht_nonneg ha
  have hcard_len :
      (Complex.realPhase_integerIncrementResonanceWindow
          (Complex.realPhase_secondDerivative_vdc_shiftedDifference
            (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
            h)
          a (b - h) (2 * Real.pi * (0 : ℝ))
          (‖t‖ *
            ((((b + 1 : ℕ) : ℝ) *
              (((b + 1 : ℕ) : ℝ)))⁻¹) *
            (h : ℝ))).card =
        d - c :=
    Complex.realPhase_integerIncrementResonanceWindow_card_eq_of_eq_Ico
      (Complex.realPhase_secondDerivative_vdc_shiftedDifference
        (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
        h)
      hwindow
  have hcard_zero :
      (Complex.realPhase_integerIncrementResonanceWindow
          (Complex.realPhase_secondDerivative_vdc_shiftedDifference
            (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
            h)
          a (b - h) (2 * Real.pi * (0 : ℝ))
          (‖t‖ *
            ((((b + 1 : ℕ) : ℝ) *
              (((b + 1 : ℕ) : ℝ)))⁻¹) *
            (h : ℝ))).card =
        0 :=
    Eq.trans (congrArg Finset.card hempty) Finset.card_empty
  have hlen_zero : d - c = 0 :=
    Eq.trans hcard_len.symm hcard_zero
  have hcast_zero : ((d - c : ℕ) : ℝ) = 0 :=
    Eq.trans (congrArg (fun m : ℕ => (m : ℝ)) hlen_zero) Nat.cast_zero
  exact le_of_eq hcast_zero

end

end LFunctions
end Boundary
