import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalization.BoundaryEulerAbel.LogarithmicPhase.Curvature.RealPhaseLongBranch
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalization.BoundaryEulerAbel.LogarithmicPhase.Curvature.RealPhaseLongAdditiveResonance
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalization.BoundaryEulerAbel.LogarithmicPhase.Curvature.RealPhaseLongChordAbel
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalization.BoundaryEulerAbel.LogarithmicPhase.Curvature.RealPhaseLongWeightedMassBudget

/-!
# Positive long-branch monotone-curvature closure

This file owns the final nonnegative long-branch estimate from the actual
all-integer monotone-curvature resonance decomposition.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open scoped Topology

/-- In the long square-root branch, every canonical Weyl shift leaves a
nonempty shifted endpoint block. -/
theorem Complex.logarithmicPhaseRealPhase_shiftRange_habh_of_sqrt_long
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    {a b : ℕ}
    (hab : a ≤ b)
    (hlong_sqrt :
      Real.sqrt (1 + ‖t‖) < (((b + 1 : ℕ) : ℝ) - (a : ℝ))) :
    ∀ h : ℕ,
      h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange
          (Real.secondDerivativeVdc_weylShiftLength ‖t‖) →
        a ≤ b - h := by
  have hgap :
      Real.secondDerivativeVdc_weylShiftLength ‖t‖ ≤ b - a :=
    Nat.secondDerivativeVdc_weylShiftLength_le_block_gap_of_sqrt_long
      ht hlong_sqrt
  intro h hh
  have hh_gap : h ≤ b - a :=
    le_trans
      (Complex.realPhase_secondDerivative_vdc_shiftRange_le hh)
      hgap
  have hha_le_b :
      h + a ≤ b := by
    have hstep :
        h + a ≤ (b - a) + a :=
      Nat.add_le_add_right hh_gap a
    have hcancel :
        (b - a) + a = b :=
      Nat.sub_add_cancel hab
    exact
      Eq.subst
        (motive := fun right : ℕ => h + a ≤ right)
        hcancel
        hstep
  have hah_le_b :
      a + h ≤ b :=
    Eq.subst
      (motive := fun left : ℕ => left ≤ b)
      (Nat.add_comm h a)
      hha_le_b
  exact Nat.le_sub_of_add_le hah_le_b

/-- Span-local shifted increments lie in the canonical long-shift range on
every Weyl shift. -/
theorem Complex.logarithmicPhaseRealPhase_shiftRange_mem_longShiftSpan
    (t : ℝ)
    (ht_nonneg : 0 ≤ t)
    {a b : ℕ}
    (ha : 1 ≤ a) :
    ∀ h : ℕ,
      h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange
          (Real.secondDerivativeVdc_weylShiftLength ‖t‖) →
        ∀ n : ℕ,
          n ∈ Finset.Ico a (b - h) →
            Real.logarithmicPhaseRealPhase_longShiftSpanLo t a b h ≤
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
                Real.logarithmicPhaseRealPhase_longShiftSpanHi t a h := by
  intro h _hh n hn
  have hspan :
      Real.logarithmicPhaseRealPhase_spanIncrementLo t (b - h) h ≤
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
            Real.logarithmicPhaseRealPhase_spanIncrementHi t a h :=
    Complex.logarithmicPhaseRealPhase_shiftedDifference_integerIncrement_mem_span_range
      t ht_nonneg ha hn
  exact And.intro
    (le_trans
      (min_le_left
        (Real.logarithmicPhaseRealPhase_spanIncrementLo t (b - h) h)
        (Real.logarithmicPhaseRealPhase_spanIncrementHi t a h))
      hspan.1)
    hspan.2

/-- The positive long-branch estimate with canonical all-integer
monotone-curvature resonance parameters, reduced to the finite radicand
arithmetic for those parameters. -/
theorem Complex.logarithmicPhaseRealPhase_long_nonneg_monotoneCurvature_resonanceDecomposition_of_radicand
    (t : ℝ)
    (ht_nonneg : 0 ≤ t)
    (ht : 1 ≤ ‖t‖)
    {a b : ℕ}
    (ha : 1 ≤ a)
    (hab : a ≤ b)
    (hab_strict : a < b)
    (hlong_sqrt :
      Real.sqrt (1 + ‖t‖) < (((b + 1 : ℕ) : ℝ) - (a : ℝ)))
    (hlong_endpoint :
      (((b + 1 : ℕ) : ℝ) / ‖t‖) <
        (((b + 1 : ℕ) : ℝ) - (a : ℝ)))
    (hrad :
      ((Real.secondDerivativeVdc_blockLength a b) +
          (Real.secondDerivativeVdc_weylShiftLength ‖t‖ : ℝ)) *
          (((Real.secondDerivativeVdc_blockLength a b) +
              2 *
                (∑ h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange
                  (Real.secondDerivativeVdc_weylShiftLength ‖t‖),
                  ((((((Complex.realPhase_integerIncrementRangeActiveCenters
                      (Real.logarithmicPhaseRealPhase_longShiftSpanLo t a b h)
                      (Real.logarithmicPhaseRealPhase_longShiftSpanHi t a h)
                      (Real.logarithmicPhaseRealPhase_longEta ‖t‖ b h)).card :
                        ℕ) : ℝ) *
                    Real.logarithmicPhaseRealPhase_longWindowBudget ‖t‖ b h +
                    ((((((Complex.realPhase_integerIncrementRangeActiveCenters
                        (Real.logarithmicPhaseRealPhase_longShiftSpanLo t a b h)
                        (Real.logarithmicPhaseRealPhase_longShiftSpanHi t a h)
                        (Real.logarithmicPhaseRealPhase_longEta ‖t‖ b h)).card +
                        (Complex.realPhase_integerIncrementRangeActiveCenters
                          (Real.logarithmicPhaseRealPhase_longShiftSpanLo t a b h)
                          (Real.logarithmicPhaseRealPhase_longShiftSpanHi t a h)
                          Real.pi).card : ℕ) + 1 : ℕ) : ℝ) *
                      (4 *
                          ((Real.logarithmicPhaseRealPhase_longEta ‖t‖ b h)⁻¹ +
                            1) +
                        4 * Real.pi *
                          (Real.logarithmicPhaseRealPhase_longEta ‖t‖ b h)⁻¹))) +
                    1))) *
            (((Real.secondDerivativeVdc_weylShiftLength ‖t‖ : ℕ) : ℝ)⁻¹)) ≤
        (80 * ((((b + 1 : ℕ) : ℝ) / ‖t‖ +
          Real.sqrt (1 + ‖t‖)))) ^ 2) :
    ‖∑ n ∈ Finset.Icc a b,
      Complex.exp
        (Complex.I *
          (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase
            t n : ℂ))‖ ≤
      80 * ((((b + 1 : ℕ) : ℝ) / ‖t‖ +
        Real.sqrt (1 + ‖t‖))) := by
  exact
    Complex.logarithmicPhaseRealPhase_long_nonneg_bProcess_budget_of_rangeCounted_activeCenter_endpoint_spread_additiveResonance_radicand
      (t := t)
      (ht_nonneg := ht_nonneg)
      (ht := ht)
      (a := a)
      (b := b)
      (ha := ha)
      (hab := hab)
      (_hab_strict := hab_strict)
      (hlong_sqrt := hlong_sqrt)
      (_hlong_endpoint := hlong_endpoint)
      (eta := fun h => Real.logarithmicPhaseRealPhase_longEta ‖t‖ b h)
      (rho := fun h => Real.logarithmicPhaseRealPhase_longRho ‖t‖ b h)
      (W := fun h => Real.logarithmicPhaseRealPhase_longWindowBudget ‖t‖ b h)
      (lo := fun h => Real.logarithmicPhaseRealPhase_longShiftSpanLo t a b h)
      (hi := fun h => Real.logarithmicPhaseRealPhase_longShiftSpanHi t a h)
      (Complex.logarithmicPhaseRealPhase_shiftRange_habh_of_sqrt_long
        t ht hab hlong_sqrt)
      (Complex.logarithmicPhaseRealPhase_shiftRange_longEta_pos
        t ht (b := b))
      (Complex.logarithmicPhaseRealPhase_shiftRange_longEta_le_pi_of_sqrt_long
        t ht hab hlong_sqrt)
      (Complex.logarithmicPhaseRealPhase_shiftRange_longRho_pos
        t ht (b := b))
      (Complex.logarithmicPhaseRealPhase_shiftRange_longWindowBudget_majorizes
        ‖t‖ (b := b))
      (Complex.logarithmicPhaseRealPhase_shiftRange_mem_longShiftSpan
        t ht_nonneg ha)
      (Complex.logarithmicPhaseRealPhase_shiftRange_longRho_rational_endpoint_spread
        t ht_nonneg (a := a) (b := b))
      (Complex.logarithmicPhaseRealPhase_shiftRange_longWindowBudget_nonneg
        t ht (b := b))
      (Complex.logarithmicPhaseRealPhase_shiftedDifference_integerIncrementMonotoneOn
        t ht_nonneg ha)
      hrad

/-- The positive long-branch estimate with canonical all-integer
monotone-curvature resonance parameters, with the resonance majorant capped by
the trivial shifted-block cardinality before entering the Weyl radicand. -/
theorem Complex.logarithmicPhaseRealPhase_long_nonneg_monotoneCurvature_resonanceDecomposition_of_capped_radicand
    (t : ℝ)
    (ht_nonneg : 0 ≤ t)
    (ht : 1 ≤ ‖t‖)
    {a b : ℕ}
    (ha : 1 ≤ a)
    (hab : a ≤ b)
    (hab_strict : a < b)
    (hlong_sqrt :
      Real.sqrt (1 + ‖t‖) < (((b + 1 : ℕ) : ℝ) - (a : ℝ)))
    (hlong_endpoint :
      (((b + 1 : ℕ) : ℝ) / ‖t‖) <
        (((b + 1 : ℕ) : ℝ) - (a : ℝ)))
    (hrad :
      Real.logarithmicPhaseRealPhase_longCappedRadicand t a b ≤
        (80 * ((((b + 1 : ℕ) : ℝ) / ‖t‖ +
          Real.sqrt (1 + ‖t‖)))) ^ 2) :
    ‖∑ n ∈ Finset.Icc a b,
      Complex.exp
        (Complex.I *
          (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase
            t n : ℂ))‖ ≤
      80 * ((((b + 1 : ℕ) : ℝ) / ‖t‖ +
        Real.sqrt (1 + ‖t‖))) := by
  have henvelope :
      Complex.realPhase_secondDerivative_vdc_shiftedCorrelationEnvelope
          (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
          a b (Real.secondDerivativeVdc_weylShiftLength ‖t‖) ≤
        Real.logarithmicPhaseRealPhase_longCappedEnvelope t a b := by
    have habh :
        ∀ h : ℕ,
          h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange
              (Real.secondDerivativeVdc_weylShiftLength ‖t‖) →
            a ≤ b - h :=
      Complex.logarithmicPhaseRealPhase_shiftRange_habh_of_sqrt_long
        t ht hab hlong_sqrt
    have heta_pos :
        ∀ h : ℕ,
          h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange
              (Real.secondDerivativeVdc_weylShiftLength ‖t‖) →
            0 < Real.logarithmicPhaseRealPhase_longEta ‖t‖ b h :=
      Complex.logarithmicPhaseRealPhase_shiftRange_longEta_pos
        t ht (b := b)
    have heta_pi :
        ∀ h : ℕ,
          h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange
              (Real.secondDerivativeVdc_weylShiftLength ‖t‖) →
            Real.logarithmicPhaseRealPhase_longEta ‖t‖ b h ≤ Real.pi :=
      Complex.logarithmicPhaseRealPhase_shiftRange_longEta_le_pi_of_sqrt_long
        t ht hab hlong_sqrt
    have hrho_pos :
        ∀ h : ℕ,
          h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange
              (Real.secondDerivativeVdc_weylShiftLength ‖t‖) →
            0 < Real.logarithmicPhaseRealPhase_longRho ‖t‖ b h :=
      Complex.logarithmicPhaseRealPhase_shiftRange_longRho_pos
        t ht (b := b)
    have hW :
        ∀ h : ℕ,
          h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange
              (Real.secondDerivativeVdc_weylShiftLength ‖t‖) →
            (2 * Real.logarithmicPhaseRealPhase_longEta ‖t‖ b h) /
                Real.logarithmicPhaseRealPhase_longRho ‖t‖ b h + 1 ≤
              Real.logarithmicPhaseRealPhase_longWindowBudget ‖t‖ b h :=
      Complex.logarithmicPhaseRealPhase_shiftRange_longWindowBudget_majorizes
        ‖t‖ (b := b)
    have hrange :
        ∀ h : ℕ,
          h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange
              (Real.secondDerivativeVdc_weylShiftLength ‖t‖) →
            ∀ n : ℕ,
              n ∈ Finset.Ico a (b - h) →
                Real.logarithmicPhaseRealPhase_longShiftSpanLo t a b h ≤
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
                    Real.logarithmicPhaseRealPhase_longShiftSpanHi t a h :=
      Complex.logarithmicPhaseRealPhase_shiftRange_mem_longShiftSpan
        t ht_nonneg ha
    have hrational :
        ∀ h : ℕ,
          h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange
              (Real.secondDerivativeVdc_weylShiftLength ‖t‖) →
            ∀ k : ℤ,
              ∀ c d : ℕ,
                Complex.realPhase_integerIncrementResonanceWindow
                    (Complex.realPhase_secondDerivative_vdc_shiftedDifference
                      (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
                      h)
                    a (b - h) (2 * Real.pi * (k : ℝ))
                    (Real.logarithmicPhaseRealPhase_longEta ‖t‖ b h) =
                  Finset.Ico c d →
                c < d - 1 →
                  Real.logarithmicPhaseRealPhase_longRho ‖t‖ b h *
                      (((d - 1) - c : ℕ) : ℝ) ≤
                    ‖t‖ *
                      (((h : ℝ) / (((c + 1) * (c + h) : ℕ) : ℝ)) -
                        ((h : ℝ) /
                          (((d - 1) * ((d - 1) + h + 1) : ℕ) : ℝ))) :=
      Complex.logarithmicPhaseRealPhase_shiftRange_longRho_rational_endpoint_spread
        t ht_nonneg (a := a) (b := b)
    have hW_nonneg :
        ∀ h : ℕ,
          h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange
              (Real.secondDerivativeVdc_weylShiftLength ‖t‖) →
            0 ≤ Real.logarithmicPhaseRealPhase_longWindowBudget ‖t‖ b h :=
      Complex.logarithmicPhaseRealPhase_shiftRange_longWindowBudget_nonneg
        t ht (b := b)
    have hinc_mono :
        ∀ h : ℕ,
          h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange
              (Real.secondDerivativeVdc_weylShiftLength ‖t‖) →
            Complex.realPhase_integerIncrementMonotoneOn
              (Complex.realPhase_secondDerivative_vdc_shiftedDifference
                (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
                h)
              a (b - h) :=
      Complex.logarithmicPhaseRealPhase_shiftedDifference_integerIncrementMonotoneOn
        t ht_nonneg ha
    have hwindow :
        ∀ h : ℕ,
          h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange
              (Real.secondDerivativeVdc_weylShiftLength ‖t‖) →
            ∀ k : ℤ,
              k ∈
                Complex.logarithmicPhaseRealPhase_shiftedDifference_activeCenters
                  t a b h (Real.logarithmicPhaseRealPhase_longEta ‖t‖ b h) →
                ((Complex.realPhase_integerIncrementResonanceWindow
                  (Complex.realPhase_secondDerivative_vdc_shiftedDifference
                    (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
                    h)
                  a (b - h) (2 * Real.pi * (k : ℝ))
                  (Real.logarithmicPhaseRealPhase_longEta ‖t‖ b h)).card :
                    ℝ) ≤
                  Real.logarithmicPhaseRealPhase_longWindowBudget ‖t‖ b h :=
      Complex.logarithmicPhaseRealPhase_shiftRange_activeCenter_window_card_le_of_rational_endpoint_spread
        t ht_nonneg ha habh hinc_mono
        (fun h hh => le_of_lt (heta_pos h hh))
        hrho_pos hW hrational
    show
      (∑ h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange
          (Real.secondDerivativeVdc_weylShiftLength ‖t‖),
        ‖Complex.logarithmicPhaseRealPhase_shiftedCorrelation t h a b‖) ≤
        ∑ h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange
          (Real.secondDerivativeVdc_weylShiftLength ‖t‖),
          Real.logarithmicPhaseRealPhase_longCappedEnvelopeTerm t a b h
    exact Finset.sum_le_sum
      (fun h hh =>
        have hadd_active :
            ‖Complex.logarithmicPhaseRealPhase_shiftedCorrelation t h a b‖ ≤
              ((((Complex.logarithmicPhaseRealPhase_shiftedDifference_activeCenters
                t a b h (Real.logarithmicPhaseRealPhase_longEta ‖t‖ b h)).card :
                  ℝ) *
                  Real.logarithmicPhaseRealPhase_longWindowBudget ‖t‖ b h) +
                (((((Complex.logarithmicPhaseRealPhase_shiftedDifference_activeCenters
                    t a b h (Real.logarithmicPhaseRealPhase_longEta ‖t‖ b h)).card +
                    (Complex.realPhase_integerIncrementRangeActiveCenters
                      (Real.logarithmicPhaseRealPhase_longShiftSpanLo t a b h)
                      (Real.logarithmicPhaseRealPhase_longShiftSpanHi t a h)
                      Real.pi).card : ℕ) + 1 : ℕ) : ℝ) *
                  (4 *
                      ((Real.logarithmicPhaseRealPhase_longEta ‖t‖ b h)⁻¹ +
                        1) +
                    4 * Real.pi *
                      (Real.logarithmicPhaseRealPhase_longEta ‖t‖ b h)⁻¹))) +
                1 :=
          Complex.logarithmicPhaseRealPhase_shiftedCorrelation_norm_le_activeCenterCount_window_add_additivePrincipalFirstDerivativeGapMajorants_add_one
            t ha (habh h hh) (heta_pos h hh) (heta_pi h hh)
            (hrange h hh) (hwindow h hh) (hinc_mono h hh)
        have hcard :
            (Complex.logarithmicPhaseRealPhase_shiftedDifference_activeCenters
              t a b h (Real.logarithmicPhaseRealPhase_longEta ‖t‖ b h)).card ≤
              (Complex.realPhase_integerIncrementRangeActiveCenters
                (Real.logarithmicPhaseRealPhase_longShiftSpanLo t a b h)
                (Real.logarithmicPhaseRealPhase_longShiftSpanHi t a h)
                (Real.logarithmicPhaseRealPhase_longEta ‖t‖ b h)).card :=
          Complex.logarithmicPhaseRealPhase_shiftedDifference_activeCenters_card_le_rangeActiveCenters_card
            t (hrange h hh)
        have hgap_nonneg :
            0 ≤
              4 * ((Real.logarithmicPhaseRealPhase_longEta ‖t‖ b h)⁻¹ + 1) +
                4 * Real.pi *
                  (Real.logarithmicPhaseRealPhase_longEta ‖t‖ b h)⁻¹ :=
          Real.logarithmicPhaseRealPhase_longAdditiveGapMajorant_nonneg
            t ht hh
        have hadd_range :
            ‖Complex.logarithmicPhaseRealPhase_shiftedCorrelation t h a b‖ ≤
              Real.logarithmicPhaseRealPhase_longAdditiveEnvelopeTerm t a b h :=
          le_trans hadd_active
            (Real.logarithmicPhaseRealPhase_additiveResonanceShiftBudget_mono
              hcard (hW_nonneg h hh) hgap_nonneg)
        have hcard_bound :
            ‖Complex.logarithmicPhaseRealPhase_shiftedCorrelation t h a b‖ ≤
              (((Finset.Icc a (b - h)).card : ℝ)) :=
          Complex.logarithmicPhaseRealPhase_shiftedCorrelation_norm_le_card
            t h a b
        le_min hadd_range hcard_bound)
  exact
    Complex.logarithmicPhaseRealPhase_long_bound_of_weylEnvelope_radicand_target_of_shiftedCorrelationEnvelope_bound
      t ht hab hlong_sqrt henvelope hrad

/-- The canonical chord-Abel estimate for every Weyl shift after the
all-integer reduced-arc denominator data have been supplied. -/
theorem Complex.logarithmicPhaseRealPhase_shiftedCorrelationEnvelope_le_longChordAbelBudget
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    {a b : ℕ}
    (ha : 1 ≤ a)
    (hab : a ≤ b)
    (hlong_sqrt :
      Real.sqrt (1 + ‖t‖) < (((b + 1 : ℕ) : ℝ) - (a : ℝ)))
    (hred :
      ∀ h : ℕ,
        h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange
            (Real.secondDerivativeVdc_weylShiftLength ‖t‖) →
          Complex.realPhase_reducedIntegerIncrementMonotoneOn
            (Complex.logarithmicPhaseRealPhase_shiftedDifferencePhase t h)
            a (b - h))
    (hsep :
      ∀ h : ℕ,
        h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange
            (Real.secondDerivativeVdc_weylShiftLength ‖t‖) →
          Complex.realPhase_integerIncrementSeparatedOn
            (Complex.logarithmicPhaseRealPhase_shiftedDifferencePhase t h)
            a (b - h)
            (Real.logarithmicPhaseRealPhase_longEta ‖t‖ b h)) :
    Complex.realPhase_secondDerivative_vdc_shiftedCorrelationEnvelope
        (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
        a b (Real.secondDerivativeVdc_weylShiftLength ‖t‖) ≤
      ∑ h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange
          (Real.secondDerivativeVdc_weylShiftLength ‖t‖),
        Complex.logarithmicPhaseRealPhase_longChordEndpointBudget t b h +
          Complex.logarithmicPhaseRealPhase_longChordVariationBudget t b h + 1 := by
  show
    (∑ h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange
        (Real.secondDerivativeVdc_weylShiftLength ‖t‖),
      ‖Complex.logarithmicPhaseRealPhase_shiftedCorrelation t h a b‖) ≤
      ∑ h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange
          (Real.secondDerivativeVdc_weylShiftLength ‖t‖),
        Complex.logarithmicPhaseRealPhase_longChordEndpointBudget t b h +
          Complex.logarithmicPhaseRealPhase_longChordVariationBudget t b h + 1
  exact Finset.sum_le_sum
    (fun h hh =>
      have habh :
          a ≤ b - h :=
        Complex.logarithmicPhaseRealPhase_shiftRange_habh_of_sqrt_long
          t ht hab hlong_sqrt h hh
      Complex.logarithmicPhaseRealPhase_shiftedCorrelation_norm_le_longChordAbelBudget_of_le
        t ha habh
        (Complex.logarithmicPhaseRealPhase_shiftRange_longEta_pos
          t ht (b := b) h hh)
        (hred h hh)
        (hsep h hh))

/-- The canonical chord-Abel estimate for every Weyl shift from explicit
all-integer separation, endpoint, and chord-variation budgets. -/
theorem Complex.logarithmicPhaseRealPhase_shiftedCorrelationEnvelope_le_longChordAbelBudget_of_direct
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    {a b : ℕ}
    (hab : a ≤ b)
    (hlong_sqrt :
      Real.sqrt (1 + ‖t‖) < (((b + 1 : ℕ) : ℝ) - (a : ℝ)))
    (hsep :
      ∀ h : ℕ,
        h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange
            (Real.secondDerivativeVdc_weylShiftLength ‖t‖) →
          Complex.realPhase_integerIncrementSeparatedOn
            (Complex.logarithmicPhaseRealPhase_shiftedDifferencePhase t h)
            a (b - h)
            (Real.logarithmicPhaseRealPhase_longEta ‖t‖ b h))
    (hendpoint :
      ∀ h : ℕ,
        h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange
            (Real.secondDerivativeVdc_weylShiftLength ‖t‖) →
          ‖Complex.realPhase_inverseGeometricDenominator
              (Complex.logarithmicPhaseRealPhase_shiftedDifferencePhase t h)
              a‖ +
            ‖Complex.realPhase_inverseGeometricDenominator
              (Complex.logarithmicPhaseRealPhase_shiftedDifferencePhase t h)
              ((b - h) - 1)‖ ≤
              Complex.logarithmicPhaseRealPhase_longChordEndpointBudget t b h)
    (hvariation :
      ∀ h : ℕ,
        h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange
            (Real.secondDerivativeVdc_weylShiftLength ‖t‖) →
          (∑ n ∈ Finset.Ico (a + 1) (b - h),
            ‖Complex.realPhase_inverseGeometricDenominator
                (Complex.logarithmicPhaseRealPhase_shiftedDifferencePhase t h)
                n -
              Complex.realPhase_inverseGeometricDenominator
                (Complex.logarithmicPhaseRealPhase_shiftedDifferencePhase t h)
                (n - 1)‖) ≤
              Complex.logarithmicPhaseRealPhase_longChordVariationBudget t b h) :
    Complex.realPhase_secondDerivative_vdc_shiftedCorrelationEnvelope
        (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
        a b (Real.secondDerivativeVdc_weylShiftLength ‖t‖) ≤
      ∑ h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange
          (Real.secondDerivativeVdc_weylShiftLength ‖t‖),
        Complex.logarithmicPhaseRealPhase_longChordEndpointBudget t b h +
          Complex.logarithmicPhaseRealPhase_longChordVariationBudget t b h + 1 := by
  show
    (∑ h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange
        (Real.secondDerivativeVdc_weylShiftLength ‖t‖),
      ‖Complex.logarithmicPhaseRealPhase_shiftedCorrelation t h a b‖) ≤
      ∑ h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange
          (Real.secondDerivativeVdc_weylShiftLength ‖t‖),
        Complex.logarithmicPhaseRealPhase_longChordEndpointBudget t b h +
          Complex.logarithmicPhaseRealPhase_longChordVariationBudget t b h + 1
  exact Finset.sum_le_sum
    (fun h hh =>
      have habh :
          a ≤ b - h :=
        Complex.logarithmicPhaseRealPhase_shiftRange_habh_of_sqrt_long
          t ht hab hlong_sqrt h hh
      let φ : ℝ → ℝ :=
        Complex.logarithmicPhaseRealPhase_shiftedDifferencePhase t h
      have hico :
          ‖∑ n ∈ Finset.Ico a (b - h),
            Complex.exp (Complex.I * (φ n : ℂ))‖ ≤
              Complex.logarithmicPhaseRealPhase_longChordEndpointBudget t b h +
                Complex.logarithmicPhaseRealPhase_longChordVariationBudget t b h :=
        Complex.realPhase_Ico_sum_norm_le_allIntegerAbelVariation
          φ
          (Complex.logarithmicPhaseRealPhase_shiftRange_longEta_pos
            t ht (b := b) h hh)
          (hsep h hh)
          (hendpoint h hh)
          (hvariation h hh)
      have hterminal :
          ‖Complex.logarithmicPhaseRealPhase_shiftedCorrelation t h a b‖ ≤
            ‖∑ n ∈ Finset.Ico a (b - h),
              Complex.exp (Complex.I * (φ n : ℂ))‖ + 1 :=
        Complex.logarithmicPhaseRealPhase_shiftedCorrelation_norm_le_Ico_sum_norm_add_one
          t habh
      le_trans hterminal (add_le_add_right hico 1))

/-- Long-branch closure from direct all-integer chord-Abel denominator
budgets and the corresponding finite square-budget arithmetic. -/
theorem Complex.logarithmicPhaseRealPhase_long_nonneg_monotoneCurvature_resonanceDecomposition_of_direct_chordAbel
    (t : ℝ)
    (ht_nonneg : 0 ≤ t)
    (ht : 1 ≤ ‖t‖)
    {a b : ℕ}
    (ha : 1 ≤ a)
    (hab : a ≤ b)
    (hab_strict : a < b)
    (hlong_sqrt :
      Real.sqrt (1 + ‖t‖) < (((b + 1 : ℕ) : ℝ) - (a : ℝ)))
    (hlong_endpoint :
      (((b + 1 : ℕ) : ℝ) / ‖t‖) <
        (((b + 1 : ℕ) : ℝ) - (a : ℝ)))
    (hsep :
      ∀ h : ℕ,
        h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange
            (Real.secondDerivativeVdc_weylShiftLength ‖t‖) →
          Complex.realPhase_integerIncrementSeparatedOn
            (Complex.logarithmicPhaseRealPhase_shiftedDifferencePhase t h)
            a (b - h)
            (Real.logarithmicPhaseRealPhase_longEta ‖t‖ b h))
    (hendpoint :
      ∀ h : ℕ,
        h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange
            (Real.secondDerivativeVdc_weylShiftLength ‖t‖) →
          ‖Complex.realPhase_inverseGeometricDenominator
              (Complex.logarithmicPhaseRealPhase_shiftedDifferencePhase t h)
              a‖ +
            ‖Complex.realPhase_inverseGeometricDenominator
              (Complex.logarithmicPhaseRealPhase_shiftedDifferencePhase t h)
              ((b - h) - 1)‖ ≤
              Complex.logarithmicPhaseRealPhase_longChordEndpointBudget t b h)
    (hvariation :
      ∀ h : ℕ,
        h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange
            (Real.secondDerivativeVdc_weylShiftLength ‖t‖) →
          (∑ n ∈ Finset.Ico (a + 1) (b - h),
            ‖Complex.realPhase_inverseGeometricDenominator
                (Complex.logarithmicPhaseRealPhase_shiftedDifferencePhase t h)
                n -
              Complex.realPhase_inverseGeometricDenominator
                (Complex.logarithmicPhaseRealPhase_shiftedDifferencePhase t h)
                (n - 1)‖) ≤
              Complex.logarithmicPhaseRealPhase_longChordVariationBudget t b h)
    (hrad :
      ((Real.secondDerivativeVdc_blockLength a b) +
          (Real.secondDerivativeVdc_weylShiftLength ‖t‖ : ℝ)) *
          (((Real.secondDerivativeVdc_blockLength a b) +
              2 *
                (∑ h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange
                    (Real.secondDerivativeVdc_weylShiftLength ‖t‖),
                  Complex.logarithmicPhaseRealPhase_longChordEndpointBudget t b h +
                    Complex.logarithmicPhaseRealPhase_longChordVariationBudget t b h + 1)) *
            (((Real.secondDerivativeVdc_weylShiftLength ‖t‖ : ℕ) : ℝ)⁻¹)) ≤
        (80 * ((((b + 1 : ℕ) : ℝ) / ‖t‖ +
          Real.sqrt (1 + ‖t‖)))) ^ 2) :
    ‖∑ n ∈ Finset.Icc a b,
      Complex.exp
        (Complex.I *
          (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase
            t n : ℂ))‖ ≤
      80 * ((((b + 1 : ℕ) : ℝ) / ‖t‖ +
        Real.sqrt (1 + ‖t‖))) := by
  have henvelope :
      Complex.realPhase_secondDerivative_vdc_shiftedCorrelationEnvelope
          (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
          a b (Real.secondDerivativeVdc_weylShiftLength ‖t‖) ≤
        ∑ h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange
            (Real.secondDerivativeVdc_weylShiftLength ‖t‖),
          Complex.logarithmicPhaseRealPhase_longChordEndpointBudget t b h +
            Complex.logarithmicPhaseRealPhase_longChordVariationBudget t b h + 1 :=
    Complex.logarithmicPhaseRealPhase_shiftedCorrelationEnvelope_le_longChordAbelBudget_of_direct
      t ht hab hlong_sqrt hsep hendpoint hvariation
  exact
    Complex.logarithmicPhaseRealPhase_long_bound_of_weylEnvelope_radicand_target_of_shiftedCorrelationEnvelope_bound
      t ht hab hlong_sqrt henvelope hrad

/-- Long-branch closure from canonical all-integer chord-Abel denominator data
and the corresponding finite square-budget arithmetic. -/
theorem Complex.logarithmicPhaseRealPhase_long_nonneg_monotoneCurvature_resonanceDecomposition_of_chordAbel
    (t : ℝ)
    (ht_nonneg : 0 ≤ t)
    (ht : 1 ≤ ‖t‖)
    {a b : ℕ}
    (ha : 1 ≤ a)
    (hab : a ≤ b)
    (hab_strict : a < b)
    (hlong_sqrt :
      Real.sqrt (1 + ‖t‖) < (((b + 1 : ℕ) : ℝ) - (a : ℝ)))
    (hlong_endpoint :
      (((b + 1 : ℕ) : ℝ) / ‖t‖) <
        (((b + 1 : ℕ) : ℝ) - (a : ℝ)))
    (hred :
      ∀ h : ℕ,
        h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange
            (Real.secondDerivativeVdc_weylShiftLength ‖t‖) →
          Complex.realPhase_reducedIntegerIncrementMonotoneOn
            (Complex.logarithmicPhaseRealPhase_shiftedDifferencePhase t h)
            a (b - h))
    (hsep :
      ∀ h : ℕ,
        h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange
            (Real.secondDerivativeVdc_weylShiftLength ‖t‖) →
          Complex.realPhase_integerIncrementSeparatedOn
            (Complex.logarithmicPhaseRealPhase_shiftedDifferencePhase t h)
            a (b - h)
            (Real.logarithmicPhaseRealPhase_longEta ‖t‖ b h))
    (hrad :
      ((Real.secondDerivativeVdc_blockLength a b) +
          (Real.secondDerivativeVdc_weylShiftLength ‖t‖ : ℝ)) *
          (((Real.secondDerivativeVdc_blockLength a b) +
              2 *
                (∑ h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange
                    (Real.secondDerivativeVdc_weylShiftLength ‖t‖),
                  Complex.logarithmicPhaseRealPhase_longChordEndpointBudget t b h +
                    Complex.logarithmicPhaseRealPhase_longChordVariationBudget t b h + 1)) *
            (((Real.secondDerivativeVdc_weylShiftLength ‖t‖ : ℕ) : ℝ)⁻¹)) ≤
        (80 * ((((b + 1 : ℕ) : ℝ) / ‖t‖ +
          Real.sqrt (1 + ‖t‖)))) ^ 2) :
    ‖∑ n ∈ Finset.Icc a b,
      Complex.exp
        (Complex.I *
          (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase
            t n : ℂ))‖ ≤
      80 * ((((b + 1 : ℕ) : ℝ) / ‖t‖ +
        Real.sqrt (1 + ‖t‖))) := by
  have henvelope :
      Complex.realPhase_secondDerivative_vdc_shiftedCorrelationEnvelope
          (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
          a b (Real.secondDerivativeVdc_weylShiftLength ‖t‖) ≤
        ∑ h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange
            (Real.secondDerivativeVdc_weylShiftLength ‖t‖),
          Complex.logarithmicPhaseRealPhase_longChordEndpointBudget t b h +
            Complex.logarithmicPhaseRealPhase_longChordVariationBudget t b h + 1 :=
    Complex.logarithmicPhaseRealPhase_shiftedCorrelationEnvelope_le_longChordAbelBudget
      t ht ha hab hlong_sqrt hred hsep
  exact
    Complex.logarithmicPhaseRealPhase_long_bound_of_weylEnvelope_radicand_target_of_shiftedCorrelationEnvelope_bound
      t ht hab hlong_sqrt henvelope hrad

/-- Positive long-branch estimate from the weighted all-integer
monotone-curvature resonance decomposition.  This is the honest
second-derivative Weyl route: each shifted correlation is bounded by the
all-integer resonance decomposition, and the exact Weyl inequality uses the
weighted shifted-correlation mass. -/
theorem Complex.logarithmicPhaseRealPhase_long_nonneg_monotoneCurvature_resonanceDecomposition_of_weighted_radicand
    (t : ℝ)
    (ht_nonneg : 0 ≤ t)
    (ht : 1 ≤ ‖t‖)
    {a b : ℕ}
    (ha : 1 ≤ a)
    (hab : a ≤ b)
    (hab_strict : a < b)
    (hlong_sqrt :
      Real.sqrt (1 + ‖t‖) < (((b + 1 : ℕ) : ℝ) - (a : ℝ)))
    (hlong_endpoint :
      (((b + 1 : ℕ) : ℝ) / ‖t‖) <
        (((b + 1 : ℕ) : ℝ) - (a : ℝ)))
    (hrad :
      Real.logarithmicPhaseRealPhase_longWeightedAdditiveRadicand t a b ≤
        (80 * ((((b + 1 : ℕ) : ℝ) / ‖t‖ +
          Real.sqrt (1 + ‖t‖)))) ^ 2) :
    ‖∑ n ∈ Finset.Icc a b,
      Complex.exp
        (Complex.I *
          (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase
            t n : ℂ))‖ ≤
      80 * ((((b + 1 : ℕ) : ℝ) / ‖t‖ +
        Real.sqrt (1 + ‖t‖))) := by
  let H : ℕ := Real.secondDerivativeVdc_weylShiftLength ‖t‖
  let φ : ℝ → ℝ :=
    Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t
  have hH : 1 ≤ H :=
    Real.one_le_secondDerivativeVdc_weylShiftLength ht
  have hH_block : H ≤ (Finset.Icc a b).card :=
    Nat.secondDerivativeVdc_weylShiftLength_le_block_card_of_sqrt_long
      ht hab hlong_sqrt
  have habh :
      ∀ h : ℕ,
        h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange H →
          a ≤ b - h :=
    Complex.logarithmicPhaseRealPhase_shiftRange_habh_of_sqrt_long
      t ht hab hlong_sqrt
  have heta_pos :
      ∀ h : ℕ,
        h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange H →
          0 < Real.logarithmicPhaseRealPhase_longEta ‖t‖ b h :=
    Complex.logarithmicPhaseRealPhase_shiftRange_longEta_pos
      t ht (b := b)
  have heta_pi :
      ∀ h : ℕ,
        h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange H →
          Real.logarithmicPhaseRealPhase_longEta ‖t‖ b h ≤ Real.pi :=
    Complex.logarithmicPhaseRealPhase_shiftRange_longEta_le_pi_of_sqrt_long
      t ht hab hlong_sqrt
  have hrho_pos :
      ∀ h : ℕ,
        h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange H →
          0 < Real.logarithmicPhaseRealPhase_longRho ‖t‖ b h :=
    Complex.logarithmicPhaseRealPhase_shiftRange_longRho_pos
      t ht (b := b)
  have hW :
      ∀ h : ℕ,
        h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange H →
          (2 * Real.logarithmicPhaseRealPhase_longEta ‖t‖ b h) /
              Real.logarithmicPhaseRealPhase_longRho ‖t‖ b h + 1 ≤
            Real.logarithmicPhaseRealPhase_longWindowBudget ‖t‖ b h :=
    Complex.logarithmicPhaseRealPhase_shiftRange_longWindowBudget_majorizes
      ‖t‖ (b := b)
  have hrange :
      ∀ h : ℕ,
        h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange H →
          ∀ n : ℕ,
            n ∈ Finset.Ico a (b - h) →
              Real.logarithmicPhaseRealPhase_longShiftSpanLo t a b h ≤
                  Complex.realPhase_integerIncrement
                    (Complex.realPhase_secondDerivative_vdc_shiftedDifference
                      φ h)
                    n ∧
                Complex.realPhase_integerIncrement
                    (Complex.realPhase_secondDerivative_vdc_shiftedDifference
                      φ h)
                    n ≤
                  Real.logarithmicPhaseRealPhase_longShiftSpanHi t a h :=
    Complex.logarithmicPhaseRealPhase_shiftRange_mem_longShiftSpan
      t ht_nonneg ha
  have hrational :
      ∀ h : ℕ,
        h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange H →
          ∀ k : ℤ,
            ∀ c d : ℕ,
              Complex.realPhase_integerIncrementResonanceWindow
                  (Complex.realPhase_secondDerivative_vdc_shiftedDifference
                    φ h)
                  a (b - h) (2 * Real.pi * (k : ℝ))
                  (Real.logarithmicPhaseRealPhase_longEta ‖t‖ b h) =
                Finset.Ico c d →
              c < d - 1 →
                Real.logarithmicPhaseRealPhase_longRho ‖t‖ b h *
                    (((d - 1) - c : ℕ) : ℝ) ≤
                  ‖t‖ *
                    (((h : ℝ) / (((c + 1) * (c + h) : ℕ) : ℝ)) -
                      ((h : ℝ) /
                        (((d - 1) * ((d - 1) + h + 1) : ℕ) : ℝ))) :=
    Complex.logarithmicPhaseRealPhase_shiftRange_longRho_rational_endpoint_spread
      t ht_nonneg (a := a) (b := b)
  have hW_nonneg :
      ∀ h : ℕ,
        h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange H →
          0 ≤ Real.logarithmicPhaseRealPhase_longWindowBudget ‖t‖ b h :=
    Complex.logarithmicPhaseRealPhase_shiftRange_longWindowBudget_nonneg
      t ht (b := b)
  have hinc_mono :
      ∀ h : ℕ,
        h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange H →
          Complex.realPhase_integerIncrementMonotoneOn
            (Complex.realPhase_secondDerivative_vdc_shiftedDifference φ h)
            a (b - h) :=
    Complex.logarithmicPhaseRealPhase_shiftedDifference_integerIncrementMonotoneOn
      t ht_nonneg ha
  have hwindow :
      ∀ h : ℕ,
        h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange H →
          ∀ k : ℤ,
            k ∈
              Complex.logarithmicPhaseRealPhase_shiftedDifference_activeCenters
                t a b h (Real.logarithmicPhaseRealPhase_longEta ‖t‖ b h) →
              ((Complex.realPhase_integerIncrementResonanceWindow
                (Complex.realPhase_secondDerivative_vdc_shiftedDifference
                  φ h)
                a (b - h) (2 * Real.pi * (k : ℝ))
                (Real.logarithmicPhaseRealPhase_longEta ‖t‖ b h)).card :
                  ℝ) ≤
                Real.logarithmicPhaseRealPhase_longWindowBudget ‖t‖ b h :=
    Complex.logarithmicPhaseRealPhase_shiftRange_activeCenter_window_card_le_of_rational_endpoint_spread
      t ht_nonneg ha habh hinc_mono
      (fun h hh => le_of_lt (heta_pos h hh))
      hrho_pos hW hrational
  have hpoint :
      ∀ h : ℕ,
        h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange H →
          ‖Complex.realPhase_secondDerivative_vdc_shiftedCorrelation
              φ h a b‖ ≤
            Real.logarithmicPhaseRealPhase_longAdditiveEnvelopeTerm t a b h := by
    intro h hh
    have hadd_active :
        ‖Complex.logarithmicPhaseRealPhase_shiftedCorrelation t h a b‖ ≤
          ((((Complex.logarithmicPhaseRealPhase_shiftedDifference_activeCenters
            t a b h (Real.logarithmicPhaseRealPhase_longEta ‖t‖ b h)).card :
              ℝ) *
              Real.logarithmicPhaseRealPhase_longWindowBudget ‖t‖ b h) +
            (((((Complex.logarithmicPhaseRealPhase_shiftedDifference_activeCenters
                t a b h (Real.logarithmicPhaseRealPhase_longEta ‖t‖ b h)).card +
                (Complex.realPhase_integerIncrementRangeActiveCenters
                  (Real.logarithmicPhaseRealPhase_longShiftSpanLo t a b h)
                  (Real.logarithmicPhaseRealPhase_longShiftSpanHi t a h)
                  Real.pi).card : ℕ) + 1 : ℕ) : ℝ) *
              (4 *
                  ((Real.logarithmicPhaseRealPhase_longEta ‖t‖ b h)⁻¹ +
                    1) +
                4 * Real.pi *
                  (Real.logarithmicPhaseRealPhase_longEta ‖t‖ b h)⁻¹))) +
            1 :=
      Complex.logarithmicPhaseRealPhase_shiftedCorrelation_norm_le_activeCenterCount_window_add_additivePrincipalFirstDerivativeGapMajorants_add_one
        t ha (habh h hh) (heta_pos h hh) (heta_pi h hh)
        (hrange h hh) (hwindow h hh) (hinc_mono h hh)
    have hcard :
        (Complex.logarithmicPhaseRealPhase_shiftedDifference_activeCenters
          t a b h (Real.logarithmicPhaseRealPhase_longEta ‖t‖ b h)).card ≤
          (Complex.realPhase_integerIncrementRangeActiveCenters
            (Real.logarithmicPhaseRealPhase_longShiftSpanLo t a b h)
            (Real.logarithmicPhaseRealPhase_longShiftSpanHi t a h)
            (Real.logarithmicPhaseRealPhase_longEta ‖t‖ b h)).card :=
      Complex.logarithmicPhaseRealPhase_shiftedDifference_activeCenters_card_le_rangeActiveCenters_card
        t (hrange h hh)
    have hgap_nonneg :
        0 ≤
          4 * ((Real.logarithmicPhaseRealPhase_longEta ‖t‖ b h)⁻¹ + 1) +
            4 * Real.pi *
              (Real.logarithmicPhaseRealPhase_longEta ‖t‖ b h)⁻¹ :=
      Real.logarithmicPhaseRealPhase_longAdditiveGapMajorant_nonneg
        t ht hh
    have hadd_range :
        ‖Complex.logarithmicPhaseRealPhase_shiftedCorrelation t h a b‖ ≤
          Real.logarithmicPhaseRealPhase_longAdditiveEnvelopeTerm t a b h :=
      le_trans hadd_active
        (Real.logarithmicPhaseRealPhase_additiveResonanceShiftBudget_mono
          hcard (hW_nonneg h hh) hgap_nonneg)
    exact hadd_range
  have hweyl :
      ‖∑ n ∈ Finset.Icc a b,
        Complex.exp (Complex.I * (φ n : ℂ))‖ ≤
        Real.secondDerivativeVdc_weightedWeylEnvelopeMajorant a b H
          (Complex.realPhase_secondDerivative_vdc_weylTranslatePositiveDifferenceMass
            φ a b H) :=
    @Complex.realPhase_secondDerivative_vdc_original_sum_norm_le_weightedWeylEnvelope
      φ a b H hH hH_block
  have hmass :
      Complex.realPhase_secondDerivative_vdc_weylTranslatePositiveDifferenceMass
          φ a b H ≤
        Real.logarithmicPhaseRealPhase_longWeightedAdditiveMass t a b :=
    Complex.realPhase_secondDerivative_vdc_weylTranslatePositiveDifferenceMass_le_weightedMajorants
      φ a b H
      (fun h => Real.logarithmicPhaseRealPhase_longAdditiveEnvelopeTerm t a b h)
      hpoint
  have hmajorant :
      Real.secondDerivativeVdc_weightedWeylEnvelopeMajorant a b H
          (Complex.realPhase_secondDerivative_vdc_weylTranslatePositiveDifferenceMass
            φ a b H) ≤
        Real.secondDerivativeVdc_weightedWeylEnvelopeMajorant a b H
          (Real.logarithmicPhaseRealPhase_longWeightedAdditiveMass t a b) :=
    Real.secondDerivativeVdc_weightedWeylEnvelopeMajorant_mono hH hmass
  have htarget_nonneg :
      0 ≤
        80 * ((((b + 1 : ℕ) : ℝ) / ‖t‖ +
          Real.sqrt (1 + ‖t‖))) :=
    mul_nonneg
      (Nat.cast_nonneg 80)
      (le_of_lt (Real.secondDerivativeVdc_target_pos (b := b) ht))
  have htarget :
      Real.secondDerivativeVdc_weightedWeylEnvelopeMajorant a b H
          (Real.logarithmicPhaseRealPhase_longWeightedAdditiveMass t a b) ≤
        80 * ((((b + 1 : ℕ) : ℝ) / ‖t‖ +
          Real.sqrt (1 + ‖t‖))) :=
    Real.secondDerivativeVdc_weightedWeylEnvelopeMajorant_le_of_radicand_le_sq
      htarget_nonneg hrad
  exact le_trans (le_trans hweyl hmajorant) htarget

/-- Positive long-branch estimate from the actual all-integer
monotone-curvature resonance decomposition. -/
theorem Complex.logarithmicPhaseRealPhase_long_nonneg_monotoneCurvature_resonanceDecomposition
    (t : ℝ)
    (ht_nonneg : 0 ≤ t)
    (ht : 1 ≤ ‖t‖)
    {a b : ℕ}
    (ha : 1 ≤ a)
    (hab : a ≤ b)
    (hab_strict : a < b)
    (hlong_sqrt :
      Real.sqrt (1 + ‖t‖) < (((b + 1 : ℕ) : ℝ) - (a : ℝ)))
    (hlong_endpoint :
      (((b + 1 : ℕ) : ℝ) / ‖t‖) <
        (((b + 1 : ℕ) : ℝ) - (a : ℝ))) :
    ‖∑ n ∈ Finset.Icc a b,
      Complex.exp
        (Complex.I *
          (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase
            t n : ℂ))‖ ≤
      80 * ((((b + 1 : ℕ) : ℝ) / ‖t‖ +
        Real.sqrt (1 + ‖t‖))) := by
  exact
    Complex.logarithmicPhaseRealPhase_long_nonneg_monotoneCurvature_resonanceDecomposition_of_weighted_radicand
      (t := t)
      (ht_nonneg := ht_nonneg)
      (ht := ht)
      (a := a)
      (b := b)
      (ha := ha)
      (hab := hab)
      (hab_strict := hab_strict)
      (hlong_sqrt := hlong_sqrt)
      (hlong_endpoint := hlong_endpoint)
      (Real.logarithmicPhaseRealPhase_longWeightedAdditiveRadicand_le_final_square
        t ht_nonneg ht ha hab hab_strict hlong_sqrt hlong_endpoint)

end

end LFunctions
end Boundary
