import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalization.BoundaryEulerAbel.LogarithmicPhase.Curvature.RealPhaseEndpointFirstDerivative
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalization.BoundaryEulerAbel.LogarithmicPhase.Curvature.RealPhaseResonancePartition

/-!
# Span-local original adjacent-increment ranges

This file owns the range bridge for the original logarithmic real phase.  The
shifted-difference span lemmas do not apply here: these are the adjacent
increments of the original phase itself.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open scoped Topology

/-- Lower endpoint for original logarithmic adjacent increments on a positive
half-open block beginning at `c`. -/
abbrev Real.logarithmicPhaseRealPhase_originalSpanIncrementLo
    (t : ℝ)
    (c : ℕ) : ℝ :=
  -(‖t‖ / (c : ℝ))

/-- Upper endpoint for original logarithmic adjacent increments on a nonempty
positive half-open block ending at `d`. -/
abbrev Real.logarithmicPhaseRealPhase_originalSpanIncrementHi
    (t : ℝ)
    (d : ℕ) : ℝ :=
  -(‖t‖ / (d : ℝ))

/-- The original adjacent-increment span endpoints are ordered on positive
half-open blocks. -/
theorem Real.logarithmicPhaseRealPhase_originalSpanIncrementLo_le_hi
    (t : ℝ)
    {c d : ℕ}
    (hc : 1 ≤ c)
    (hcd : c ≤ d) :
    Real.logarithmicPhaseRealPhase_originalSpanIncrementLo t c ≤
      Real.logarithmicPhaseRealPhase_originalSpanIncrementHi t d := by
  have hc_pos : 0 < (c : ℝ) :=
    Nat.cast_pos.mpr (Nat.lt_of_succ_le hc)
  have hd_pos_nat : 0 < d :=
    lt_of_lt_of_le (Nat.lt_of_succ_le hc) hcd
  have hd_pos : 0 < (d : ℝ) :=
    Nat.cast_pos.mpr hd_pos_nat
  have hcd_real : (c : ℝ) ≤ (d : ℝ) :=
    Nat.cast_le.mpr hcd
  have hrecip :
      (d : ℝ)⁻¹ ≤ (c : ℝ)⁻¹ :=
    inv_anti₀ hc_pos hcd_real
  have hscale :
      ‖t‖ / (d : ℝ) ≤ ‖t‖ / (c : ℝ) := by
    have hmul :
        ‖t‖ * (d : ℝ)⁻¹ ≤ ‖t‖ * (c : ℝ)⁻¹ :=
      mul_le_mul_of_nonneg_left hrecip (norm_nonneg t)
    exact
      Eq.subst
        (motive := fun left : ℝ => left ≤ ‖t‖ / (c : ℝ))
        (div_eq_mul_inv ‖t‖ (d : ℝ)).symm
        (Eq.subst
          (motive := fun right : ℝ => ‖t‖ * (d : ℝ)⁻¹ ≤ right)
          (div_eq_mul_inv ‖t‖ (c : ℝ)).symm
          hmul)
  exact neg_le_neg hscale

/-- Original logarithmic adjacent increments lie above the span-local lower
endpoint. -/
theorem Complex.logarithmicPhaseRealPhase_originalSpanIncrementLo_le_integerIncrement
    (t : ℝ)
    {c d n : ℕ}
    (hc : 1 ≤ c)
    (hn : n ∈ Finset.Ico c d) :
    Real.logarithmicPhaseRealPhase_originalSpanIncrementLo t c ≤
      Complex.realPhase_integerIncrement
        (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
        n := by
  let φ : ℝ → ℝ :=
    Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t
  have hn_bounds : c ≤ n ∧ n < d :=
    Finset.mem_Ico.mp hn
  have hn_one : 1 ≤ n :=
    le_trans hc hn_bounds.1
  have hn_pos : 0 < n :=
    Nat.lt_of_succ_le hn_one
  have hc_pos_real : 0 < (c : ℝ) :=
    Nat.cast_pos.mpr (Nat.lt_of_succ_le hc)
  have hn_pos_real : 0 < (n : ℝ) :=
    Nat.cast_pos.mpr hn_pos
  have hcn_real : (c : ℝ) ≤ (n : ℝ) :=
    Nat.cast_le.mpr hn_bounds.1
  have hrecip :
      (n : ℝ)⁻¹ ≤ (c : ℝ)⁻¹ :=
    inv_anti₀ hc_pos_real hcn_real
  have hscale :
      ‖t‖ / (n : ℝ) ≤ ‖t‖ / (c : ℝ) := by
    have hmul :
        ‖t‖ * (n : ℝ)⁻¹ ≤ ‖t‖ * (c : ℝ)⁻¹ :=
      mul_le_mul_of_nonneg_left hrecip (norm_nonneg t)
    exact
      Eq.subst
        (motive := fun left : ℝ => left ≤ ‖t‖ / (c : ℝ))
        (div_eq_mul_inv ‖t‖ (n : ℝ)).symm
        (Eq.subst
          (motive := fun right : ℝ => ‖t‖ * (n : ℝ)⁻¹ ≤ right)
          (div_eq_mul_inv ‖t‖ (c : ℝ)).symm
          hmul)
  have hnorm :
      ‖Complex.realPhase_integerIncrement φ n‖ ≤ ‖t‖ / (n : ℝ) :=
    Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase_integerIncrement_norm_le_localScale
      t hn_pos
  have habs :
      |Complex.realPhase_integerIncrement φ n| ≤ ‖t‖ / (c : ℝ) :=
    Eq.subst
      (motive := fun left : ℝ => left ≤ ‖t‖ / (c : ℝ))
      (Real.norm_eq_abs (Complex.realPhase_integerIncrement φ n))
      (le_trans hnorm hscale)
  exact neg_le_of_abs_le habs

/-- Original logarithmic adjacent increments are nonpositive in the
nonnegative-parameter branch. -/
theorem Complex.logarithmicPhaseRealPhase_original_integerIncrement_le_spanIncrementHi
    (t : ℝ)
    (ht_nonneg : 0 ≤ t)
    {c d n : ℕ}
    (hc : 1 ≤ c)
    (hn : n ∈ Finset.Ico c d) :
    Complex.realPhase_integerIncrement
        (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
        n ≤
      Real.logarithmicPhaseRealPhase_originalSpanIncrementHi t d := by
  let φ : ℝ → ℝ :=
    Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t
  have hn_bounds : c ≤ n ∧ n < d :=
    Finset.mem_Ico.mp hn
  have hn_one : 1 ≤ n :=
    le_trans hc hn_bounds.1
  have hn_pos : 0 < n :=
    Nat.lt_of_succ_le hn_one
  have hn_succ_le_d : n + 1 ≤ d :=
    Nat.succ_le_of_lt hn_bounds.2
  have hd_pos : 0 < d :=
    lt_of_lt_of_le (Nat.zero_lt_succ n) hn_succ_le_d
  have hn_succ_pos_real : 0 < ((n + 1 : ℕ) : ℝ) :=
    Nat.cast_pos.mpr (Nat.succ_pos n)
  have hd_pos_real : 0 < (d : ℝ) :=
    Nat.cast_pos.mpr hd_pos
  have hn_succ_le_d_real : ((n + 1 : ℕ) : ℝ) ≤ (d : ℝ) :=
    Nat.cast_le.mpr hn_succ_le_d
  let L : ℝ :=
    Real.log ((((n + 1 : ℕ) : ℝ)) / (((n : ℕ) : ℝ)))
  have hL_lower :
      ((n + 1 : ℕ) : ℝ)⁻¹ ≤ L :=
    Complex.logarithmicPhase_successive_log_ratio_lower_bound hn_pos
  have ht_norm : ‖t‖ = t :=
    Real.norm_of_nonneg ht_nonneg
  have ht_nonneg_norm : 0 ≤ ‖t‖ :=
    norm_nonneg t
  have hneg_t_nonpos : -‖t‖ ≤ 0 :=
    neg_nonpos.mpr ht_nonneg_norm
  have hscaled :
      -‖t‖ * L ≤ -‖t‖ * (((n + 1 : ℕ) : ℝ)⁻¹) :=
    mul_le_mul_of_nonpos_left hL_lower hneg_t_nonpos
  have hincrement_eq :
      Complex.realPhase_integerIncrement φ n =
        -‖t‖ * L := by
    have hraw :
        Complex.realPhase_integerIncrement φ n =
          -t * L :=
      Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase_integerIncrement_eq_neg_mul_log_ratio
        t hn_pos
    have hcoef : -t = -‖t‖ :=
      congrArg Neg.neg ht_norm.symm
    exact
      Eq.trans hraw
        (congrArg (fun r : ℝ => r * L) hcoef)
  have hrecip :
      (d : ℝ)⁻¹ ≤ ((n + 1 : ℕ) : ℝ)⁻¹ :=
    inv_anti₀ hn_succ_pos_real hn_succ_le_d_real
  have hscale_right :
      -‖t‖ * (((n + 1 : ℕ) : ℝ)⁻¹) ≤ -‖t‖ * (d : ℝ)⁻¹ :=
    mul_le_mul_of_nonpos_left hrecip hneg_t_nonpos
  have hdiv_right :
      -‖t‖ * (d : ℝ)⁻¹ = -(‖t‖ / (d : ℝ)) := by
    calc
      -‖t‖ * (d : ℝ)⁻¹ = -(‖t‖ * (d : ℝ)⁻¹) :=
        neg_mul ‖t‖ ((d : ℝ)⁻¹)
      _ = -(‖t‖ / (d : ℝ)) :=
        congrArg Neg.neg (div_eq_mul_inv ‖t‖ (d : ℝ)).symm
  exact
    Eq.subst
      (motive := fun left : ℝ =>
        left ≤ Real.logarithmicPhaseRealPhase_originalSpanIncrementHi t d)
      hincrement_eq.symm
      (Eq.subst
        (motive := fun right : ℝ =>
          -‖t‖ * L ≤ right)
        hdiv_right
        (le_trans hscaled hscale_right))

/-- Original logarithmic adjacent increments on a positive half-open block lie
in the local range determined by the left endpoint. -/
theorem Complex.logarithmicPhaseRealPhase_original_integerIncrement_mem_span_range
    (t : ℝ)
    (ht_nonneg : 0 ≤ t)
    {c d n : ℕ}
    (hc : 1 ≤ c)
    (hn : n ∈ Finset.Ico c d) :
    Real.logarithmicPhaseRealPhase_originalSpanIncrementLo t c ≤
          Complex.realPhase_integerIncrement
            (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
            n ∧
        Complex.realPhase_integerIncrement
            (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
            n ≤
          Real.logarithmicPhaseRealPhase_originalSpanIncrementHi t d :=
  And.intro
    (Complex.logarithmicPhaseRealPhase_originalSpanIncrementLo_le_integerIncrement
      t hc hn)
    (Complex.logarithmicPhaseRealPhase_original_integerIncrement_le_spanIncrementHi
      t ht_nonneg hc hn)

/-- Active original-phase integer centers are bounded by the span-local range
of original adjacent increments. -/
theorem Complex.logarithmicPhaseRealPhase_original_activeCenters_card_real_le_rangeActiveCenters_card
    (t : ℝ)
    (ht_nonneg : 0 ≤ t)
    {c d : ℕ}
    {lam : ℝ}
    (hc : 1 ≤ c) :
    ((Complex.realPhase_integerIncrementActiveCenters
        (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
        c d lam).card : ℝ) ≤
      ((Complex.realPhase_integerIncrementRangeActiveCenters
        (Real.logarithmicPhaseRealPhase_originalSpanIncrementLo t c)
        (Real.logarithmicPhaseRealPhase_originalSpanIncrementHi t d)
        lam).card : ℝ) := by
  exact
    Complex.realPhase_integerIncrementActiveCenters_card_real_le_rangeActiveCenters_card
      (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
      (Complex.logarithmicPhaseRealPhase_original_integerIncrement_mem_span_range
        t ht_nonneg hc)

end

end LFunctions
end Boundary
