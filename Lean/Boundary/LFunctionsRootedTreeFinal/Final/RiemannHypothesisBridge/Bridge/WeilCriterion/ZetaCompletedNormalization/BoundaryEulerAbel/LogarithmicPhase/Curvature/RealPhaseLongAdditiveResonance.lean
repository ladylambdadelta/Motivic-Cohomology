import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalization.BoundaryEulerAbel.LogarithmicPhase.Curvature.RealPhaseLongAdditiveWeylTarget

/-!
# Additive all-integer resonance endpoint spread

This file consumes the additive all-integer Weyl target and discharges the
window-length hypotheses from monotone endpoint spread.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open scoped Topology

/-- Positive long-branch estimate from the standard additive all-integer
monotone-curvature resonance decomposition.

This is the analytic owner sink: resonant windows are controlled by monotone
endpoint spread, and the complement is covered by the resonance-family gaps
plus the principal-strip crossings additively. -/
theorem Complex.logarithmicPhaseRealPhase_long_nonneg_bProcess_budget_of_rangeCounted_activeCenter_endpoint_spread_additiveResonance_radicand
    (t : ℝ)
    (ht_nonneg : 0 ≤ t)
    (ht : 1 ≤ ‖t‖)
    {a b : ℕ}
    (ha : 1 ≤ a)
    (hab : a ≤ b)
    (_hab_strict : a < b)
    (hlong_sqrt :
      Real.sqrt (1 + ‖t‖) < (((b + 1 : ℕ) : ℝ) - (a : ℝ)))
    (_hlong_endpoint :
      (((b + 1 : ℕ) : ℝ) / ‖t‖) <
        (((b + 1 : ℕ) : ℝ) - (a : ℝ)))
    {eta rho W lo hi : ℕ → ℝ}
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
    (hrho_pos :
      ∀ h : ℕ,
        h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange
            (Real.secondDerivativeVdc_weylShiftLength ‖t‖) →
          0 < rho h)
    (hW :
      ∀ h : ℕ,
        h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange
            (Real.secondDerivativeVdc_weylShiftLength ‖t‖) →
          (2 * eta h) / rho h + 1 ≤ W h)
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
    (hrational :
      ∀ h : ℕ,
        h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange
            (Real.secondDerivativeVdc_weylShiftLength ‖t‖) →
          ∀ k : ℤ,
            ∀ c d : ℕ,
              Complex.realPhase_integerIncrementResonanceWindow
                  (Complex.realPhase_secondDerivative_vdc_shiftedDifference
                    (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
                    h)
                  a (b - h) (2 * Real.pi * (k : ℝ)) (eta h) =
                Finset.Ico c d →
              c < d - 1 →
                rho h * (((d - 1) - c : ℕ) : ℝ) ≤
                  ‖t‖ *
                    (((h : ℝ) / (((c + 1) * (c + h) : ℕ) : ℝ)) -
                      ((h : ℝ) /
                        (((d - 1) * ((d - 1) + h + 1) : ℕ) : ℝ))))
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
  have heta_nonneg :
      ∀ h : ℕ,
        h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange
            (Real.secondDerivativeVdc_weylShiftLength ‖t‖) →
          0 ≤ eta h :=
    fun h hh => le_of_lt (heta_pos h hh)
  have hwindow :
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
                  ℝ) ≤ W h :=
    Complex.logarithmicPhaseRealPhase_shiftRange_activeCenter_window_card_le_of_rational_endpoint_spread
      t ht_nonneg ha habh hinc_mono heta_nonneg hrho_pos hW hrational
  exact
    Complex.logarithmicPhaseRealPhase_long_bound_of_rangeCounted_activeCenter_window_additiveResonance_radicand
      t ht ha hab hlong_sqrt habh heta_pos heta_pi hrange hwindow
      hW_nonneg hinc_mono hrad

end

end LFunctions
end Boundary
