import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalization.BoundaryEulerAbel.LogarithmicPhase.Curvature.RealPhaseLongAdditiveCover

/-!
# Additive all-integer resonance Weyl target

This file lifts the one-shift additive resonance decomposition through the
second-derivative Weyl envelope.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open scoped Topology

/-- The shifted-correlation envelope is controlled by the additive
all-integer monotone-curvature resonance decomposition on each Weyl shift. -/
theorem Complex.logarithmicPhaseRealPhase_shiftedCorrelationEnvelope_le_activeCenterCount_window_add_additivePrincipalFirstDerivativeGapMajorants_add_one
    (t : ℝ)
    {a b H : ℕ}
    {eta W lo hi : ℕ → ℝ}
    (ha : 1 ≤ a)
    (habh :
      ∀ h : ℕ,
        h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange H →
          a ≤ b - h)
    (heta_pos :
      ∀ h : ℕ,
        h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange H →
          0 < eta h)
    (heta_pi :
      ∀ h : ℕ,
        h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange H →
          eta h ≤ Real.pi)
    (hrange :
      ∀ h : ℕ,
        h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange H →
          ∀ n : ℕ,
            n ∈ Finset.Ico a (b - h) →
              lo h ≤
                  Complex.realPhase_integerIncrement
                    (Complex.realPhase_secondDerivative_vdc_shiftedDifference
                      (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
                      h)
                    n ∧
                Complex.realPhase_integerIncrement
                    (Complex.realPhase_secondDerivative_vdc_shiftedDifference
                      (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
                      h)
                    n ≤ hi h)
    (hwindow :
      ∀ h : ℕ,
        h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange H →
          ∀ k : ℤ,
            k ∈
              Complex.logarithmicPhaseRealPhase_shiftedDifference_activeCenters
                t a b h (eta h) →
              ((Complex.realPhase_integerIncrementResonanceWindow
                (Complex.realPhase_secondDerivative_vdc_shiftedDifference
                  (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
                  h)
                a (b - h) (2 * Real.pi * (k : ℝ)) (eta h)).card :
                  ℝ) ≤ W h)
    (hinc_mono :
      ∀ h : ℕ,
        h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange H →
          Complex.realPhase_integerIncrementMonotoneOn
            (Complex.realPhase_secondDerivative_vdc_shiftedDifference
              (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
              h)
            a (b - h)) :
    Complex.realPhase_secondDerivative_vdc_shiftedCorrelationEnvelope
        (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
        a b H ≤
      ∑ h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange H,
        (((((Complex.logarithmicPhaseRealPhase_shiftedDifference_activeCenters
          t a b h (eta h)).card : ℝ) * W h) +
          ((((((Complex.logarithmicPhaseRealPhase_shiftedDifference_activeCenters
            t a b h (eta h)).card +
            (Complex.realPhase_integerIncrementRangeActiveCenters
              (lo h) (hi h) Real.pi).card : ℕ) + 1 : ℕ) : ℝ) *
            (4 * ((eta h)⁻¹ + 1) + 4 * Real.pi * (eta h)⁻¹))) +
          1) := by
  show
    (∑ h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange H,
      ‖Complex.logarithmicPhaseRealPhase_shiftedCorrelation t h a b‖) ≤
      ∑ h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange H,
        (((((Complex.logarithmicPhaseRealPhase_shiftedDifference_activeCenters
          t a b h (eta h)).card : ℝ) * W h) +
          ((((((Complex.logarithmicPhaseRealPhase_shiftedDifference_activeCenters
            t a b h (eta h)).card +
            (Complex.realPhase_integerIncrementRangeActiveCenters
              (lo h) (hi h) Real.pi).card : ℕ) + 1 : ℕ) : ℝ) *
            (4 * ((eta h)⁻¹ + 1) + 4 * Real.pi * (eta h)⁻¹))) +
          1)
  exact Finset.sum_le_sum
    (fun h hh =>
      Complex.logarithmicPhaseRealPhase_shiftedCorrelation_norm_le_activeCenterCount_window_add_additivePrincipalFirstDerivativeGapMajorants_add_one
        t ha (habh h hh) (heta_pos h hh) (heta_pi h hh)
        (hrange h hh) (hwindow h hh) (hinc_mono h hh))

/-- Monotonicity of one additive-resonance shift budget in the active-center
count. -/
theorem Real.logarithmicPhaseRealPhase_additiveResonanceShiftBudget_mono
    {A C P : ℕ}
    {W G : ℝ}
    (hAC : A ≤ C)
    (hW_nonneg : 0 ≤ W)
    (hG_nonneg : 0 ≤ G) :
    ((((A : ℝ) * W) + (((((A + P : ℕ) + 1 : ℕ) : ℝ) * G))) + 1) ≤
      ((((C : ℝ) * W) + (((((C + P : ℕ) + 1 : ℕ) : ℝ) * G))) + 1) := by
  have hA_real : (A : ℝ) ≤ (C : ℝ) :=
    Nat.cast_le.mpr hAC
  have hleft :
      (A : ℝ) * W ≤ (C : ℝ) * W :=
    mul_le_mul_of_nonneg_right hA_real hW_nonneg
  have hAPC_nat : (A + P : ℕ) + 1 ≤ (C + P : ℕ) + 1 :=
    Nat.succ_le_succ (Nat.add_le_add_right hAC P)
  have hAPC_real :
      (((A + P : ℕ) + 1 : ℕ) : ℝ) ≤
        (((C + P : ℕ) + 1 : ℕ) : ℝ) :=
    Nat.cast_le.mpr hAPC_nat
  have hright :
      ((((A + P : ℕ) + 1 : ℕ) : ℝ) * G) ≤
        ((((C + P : ℕ) + 1 : ℕ) : ℝ) * G) :=
    mul_le_mul_of_nonneg_right hAPC_real hG_nonneg
  exact add_le_add_right (add_le_add hleft hright) 1

/-- Explicit increment ranges replace the actual active-center counts in the
additive all-integer shifted-correlation envelope. -/
theorem Complex.logarithmicPhaseRealPhase_shiftedCorrelationEnvelope_le_rangeCounted_activeCenter_window_add_additivePrincipalFirstDerivativeGapMajorants_add_one
    (t : ℝ)
    {a b H : ℕ}
    {eta W lo hi : ℕ → ℝ}
    (ha : 1 ≤ a)
    (habh :
      ∀ h : ℕ,
        h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange H →
          a ≤ b - h)
    (heta_pos :
      ∀ h : ℕ,
        h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange H →
          0 < eta h)
    (heta_pi :
      ∀ h : ℕ,
        h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange H →
          eta h ≤ Real.pi)
    (hrange :
      ∀ h : ℕ,
        h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange H →
          ∀ n : ℕ,
            n ∈ Finset.Ico a (b - h) →
              lo h ≤
                  Complex.realPhase_integerIncrement
                    (Complex.realPhase_secondDerivative_vdc_shiftedDifference
                      (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
                      h)
                    n ∧
                Complex.realPhase_integerIncrement
                    (Complex.realPhase_secondDerivative_vdc_shiftedDifference
                      (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
                      h)
                    n ≤ hi h)
    (hwindow :
      ∀ h : ℕ,
        h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange H →
          ∀ k : ℤ,
            k ∈
              Complex.logarithmicPhaseRealPhase_shiftedDifference_activeCenters
                t a b h (eta h) →
              ((Complex.realPhase_integerIncrementResonanceWindow
                (Complex.realPhase_secondDerivative_vdc_shiftedDifference
                  (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
                  h)
                a (b - h) (2 * Real.pi * (k : ℝ)) (eta h)).card :
                  ℝ) ≤ W h)
    (hW_nonneg :
      ∀ h : ℕ,
        h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange H →
          0 ≤ W h)
    (hinc_mono :
      ∀ h : ℕ,
        h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange H →
          Complex.realPhase_integerIncrementMonotoneOn
            (Complex.realPhase_secondDerivative_vdc_shiftedDifference
              (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
              h)
            a (b - h)) :
    Complex.realPhase_secondDerivative_vdc_shiftedCorrelationEnvelope
        (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
        a b H ≤
      ∑ h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange H,
        ((((((Complex.realPhase_integerIncrementRangeActiveCenters
            (lo h) (hi h) (eta h)).card : ℕ) : ℝ) * W h +
          ((((((Complex.realPhase_integerIncrementRangeActiveCenters
              (lo h) (hi h) (eta h)).card +
              (Complex.realPhase_integerIncrementRangeActiveCenters
                (lo h) (hi h) Real.pi).card : ℕ) + 1 : ℕ) : ℝ) *
            (4 * ((eta h)⁻¹ + 1) + 4 * Real.pi * (eta h)⁻¹))) +
          1) := by
  have hactive :
      Complex.realPhase_secondDerivative_vdc_shiftedCorrelationEnvelope
          (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
          a b H ≤
        ∑ h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange H,
          (((((Complex.logarithmicPhaseRealPhase_shiftedDifference_activeCenters
            t a b h (eta h)).card : ℝ) * W h) +
            ((((((Complex.logarithmicPhaseRealPhase_shiftedDifference_activeCenters
              t a b h (eta h)).card +
              (Complex.realPhase_integerIncrementRangeActiveCenters
                (lo h) (hi h) Real.pi).card : ℕ) + 1 : ℕ) : ℝ) *
              (4 * ((eta h)⁻¹ + 1) + 4 * Real.pi * (eta h)⁻¹))) +
            1) :=
    Complex.logarithmicPhaseRealPhase_shiftedCorrelationEnvelope_le_activeCenterCount_window_add_additivePrincipalFirstDerivativeGapMajorants_add_one
      t ha habh heta_pos heta_pi hrange hwindow hinc_mono
  have hbudget_mono :
      (∑ h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange H,
          (((((Complex.logarithmicPhaseRealPhase_shiftedDifference_activeCenters
            t a b h (eta h)).card : ℝ) * W h) +
            ((((((Complex.logarithmicPhaseRealPhase_shiftedDifference_activeCenters
              t a b h (eta h)).card +
              (Complex.realPhase_integerIncrementRangeActiveCenters
                (lo h) (hi h) Real.pi).card : ℕ) + 1 : ℕ) : ℝ) *
              (4 * ((eta h)⁻¹ + 1) + 4 * Real.pi * (eta h)⁻¹))) +
            1)) ≤
        ∑ h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange H,
          ((((((Complex.realPhase_integerIncrementRangeActiveCenters
              (lo h) (hi h) (eta h)).card : ℕ) : ℝ) * W h +
            ((((((Complex.realPhase_integerIncrementRangeActiveCenters
                (lo h) (hi h) (eta h)).card +
                (Complex.realPhase_integerIncrementRangeActiveCenters
                  (lo h) (hi h) Real.pi).card : ℕ) + 1 : ℕ) : ℝ) *
              (4 * ((eta h)⁻¹ + 1) + 4 * Real.pi * (eta h)⁻¹))) +
            1) :=
    Finset.sum_le_sum
      (fun h hh =>
        have hcard :
            (Complex.logarithmicPhaseRealPhase_shiftedDifference_activeCenters
              t a b h (eta h)).card ≤
              (Complex.realPhase_integerIncrementRangeActiveCenters
                (lo h) (hi h) (eta h)).card :=
          Complex.logarithmicPhaseRealPhase_shiftedDifference_activeCenters_card_le_rangeActiveCenters_card
            t (hrange h hh)
        have hG_nonneg :
            0 ≤ 4 * ((eta h)⁻¹ + 1) + 4 * Real.pi * (eta h)⁻¹ := by
          have heta_inv_nonneg : 0 ≤ (eta h)⁻¹ :=
            inv_nonneg.mpr (le_of_lt (heta_pos h hh))
          have hinner_nonneg : 0 ≤ (eta h)⁻¹ + 1 :=
            add_nonneg heta_inv_nonneg zero_le_one
          have hleft_nonneg : 0 ≤ 4 * ((eta h)⁻¹ + 1) :=
            mul_nonneg zero_le_four hinner_nonneg
          have hfour_pi_nonneg : 0 ≤ 4 * Real.pi :=
            mul_nonneg zero_le_four Real.pi_nonneg
          have hright_nonneg : 0 ≤ 4 * Real.pi * (eta h)⁻¹ :=
            mul_nonneg hfour_pi_nonneg heta_inv_nonneg
          exact add_nonneg hleft_nonneg hright_nonneg
        Real.logarithmicPhaseRealPhase_additiveResonanceShiftBudget_mono
          hcard (hW_nonneg h hh) hG_nonneg)
  exact le_trans hactive hbudget_mono

/-- Range-counted additive all-integer active resonance control supplies the
positive long Weyl target once the corresponding explicit radicand is below the
target square. -/
theorem Complex.logarithmicPhaseRealPhase_long_bound_of_rangeCounted_activeCenter_window_additiveResonance_radicand
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    {a b : ℕ}
    (ha : 1 ≤ a)
    (hab : a ≤ b)
    (hlong_sqrt :
      Real.sqrt (1 + ‖t‖) < (((b + 1 : ℕ) : ℝ) - (a : ℝ)))
    {eta W lo hi : ℕ → ℝ}
    (habh :
      ∀ h : ℕ,
        h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange
            (Real.secondDerivativeVdc_weylShiftLength ‖t‖) →
          a ≤ b - h)
    (heta_pos :
      ∀ h : ℕ,
        h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange
            (Real.secondDerivativeVdc_weylShiftLength ‖t‖) →
          0 < eta h)
    (heta_pi :
      ∀ h : ℕ,
        h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange
            (Real.secondDerivativeVdc_weylShiftLength ‖t‖) →
          eta h ≤ Real.pi)
    (hrange :
      ∀ h : ℕ,
        h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange
            (Real.secondDerivativeVdc_weylShiftLength ‖t‖) →
          ∀ n : ℕ,
            n ∈ Finset.Ico a (b - h) →
              lo h ≤
                  Complex.realPhase_integerIncrement
                    (Complex.realPhase_secondDerivative_vdc_shiftedDifference
                      (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
                      h)
                    n ∧
                Complex.realPhase_integerIncrement
                    (Complex.realPhase_secondDerivative_vdc_shiftedDifference
                      (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
                      h)
                    n ≤ hi h)
    (hwindow :
      ∀ h : ℕ,
        h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange
            (Real.secondDerivativeVdc_weylShiftLength ‖t‖) →
          ∀ k : ℤ,
            k ∈
              Complex.logarithmicPhaseRealPhase_shiftedDifference_activeCenters
                t a b h (eta h) →
              ((Complex.realPhase_integerIncrementResonanceWindow
                (Complex.realPhase_secondDerivative_vdc_shiftedDifference
                  (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
                  h)
                a (b - h) (2 * Real.pi * (k : ℝ)) (eta h)).card :
                  ℝ) ≤ W h)
    (hW_nonneg :
      ∀ h : ℕ,
        h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange
            (Real.secondDerivativeVdc_weylShiftLength ‖t‖) →
          0 ≤ W h)
    (hinc_mono :
      ∀ h : ℕ,
        h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange
            (Real.secondDerivativeVdc_weylShiftLength ‖t‖) →
          Complex.realPhase_integerIncrementMonotoneOn
            (Complex.realPhase_secondDerivative_vdc_shiftedDifference
              (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
              h)
            a (b - h))
    (hrad :
      ((Real.secondDerivativeVdc_blockLength a b) +
          (Real.secondDerivativeVdc_weylShiftLength ‖t‖ : ℝ)) *
          (((Real.secondDerivativeVdc_blockLength a b) +
              2 *
                (∑ h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange
                  (Real.secondDerivativeVdc_weylShiftLength ‖t‖),
                  ((((((Complex.realPhase_integerIncrementRangeActiveCenters
                      (lo h) (hi h) (eta h)).card : ℕ) : ℝ) * W h +
                    ((((((Complex.realPhase_integerIncrementRangeActiveCenters
                        (lo h) (hi h) (eta h)).card +
                        (Complex.realPhase_integerIncrementRangeActiveCenters
                          (lo h) (hi h) Real.pi).card : ℕ) + 1 : ℕ) : ℝ) *
                      (4 * ((eta h)⁻¹ + 1) +
                        4 * Real.pi * (eta h)⁻¹))) +
                    1))) *
            (((Real.secondDerivativeVdc_weylShiftLength ‖t‖ : ℕ) : ℝ)⁻¹)) ≤
        (80 * ((((b + 1 : ℕ) : ℝ) / ‖t‖ +
          Real.sqrt (1 + ‖t‖)))) ^ 2) :
    ‖∑ n ∈ Finset.Icc a b,
      Complex.exp
        (Complex.I *
          (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t n : ℂ))‖ ≤
      80 * ((((b + 1 : ℕ) : ℝ) / ‖t‖ +
        Real.sqrt (1 + ‖t‖))) := by
  have henvelope :
      Complex.realPhase_secondDerivative_vdc_shiftedCorrelationEnvelope
          (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
          a b (Real.secondDerivativeVdc_weylShiftLength ‖t‖) ≤
        ∑ h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange
          (Real.secondDerivativeVdc_weylShiftLength ‖t‖),
          ((((((Complex.realPhase_integerIncrementRangeActiveCenters
              (lo h) (hi h) (eta h)).card : ℕ) : ℝ) * W h +
            ((((((Complex.realPhase_integerIncrementRangeActiveCenters
                (lo h) (hi h) (eta h)).card +
                (Complex.realPhase_integerIncrementRangeActiveCenters
                  (lo h) (hi h) Real.pi).card : ℕ) + 1 : ℕ) : ℝ) *
              (4 * ((eta h)⁻¹ + 1) +
                4 * Real.pi * (eta h)⁻¹))) +
            1) :=
    Complex.logarithmicPhaseRealPhase_shiftedCorrelationEnvelope_le_rangeCounted_activeCenter_window_add_additivePrincipalFirstDerivativeGapMajorants_add_one
      t ha habh heta_pos heta_pi hrange hwindow hW_nonneg hinc_mono
  exact
    Complex.logarithmicPhaseRealPhase_long_bound_of_weylEnvelope_radicand_target_of_shiftedCorrelationEnvelope_bound
      t ht hab hlong_sqrt henvelope hrad

end

end LFunctions
end Boundary
