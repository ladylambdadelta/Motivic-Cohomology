import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalization.BoundaryEulerAbel.LogarithmicPhase.Curvature.RealPhaseResonancePartition

/-!
# Active integer-resonance window lengths

This file owns the short bridge from the logarithmic endpoint-spread lemma to
the window-cardinality hypothesis used by the active-center Weyl envelope.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open scoped Topology

/-- A shifted logarithmic integer-centered resonance window has the standard
endpoint-spread length bound.  The center is arbitrary; the endpoint spread is
the same for every linear integer-frequency shift. -/
theorem Complex.logarithmicPhaseRealPhase_shiftedDifference_integerResonanceWindow_card_le_of_rational_endpoint_spread
    (t : ℝ)
    (ht_nonneg : 0 ≤ t)
    {a b h : ℕ}
    {lam rho : ℝ}
    (ha : 1 ≤ a)
    (habh : a ≤ b - h)
    (hmono :
      Complex.realPhase_integerIncrementMonotoneOn
        (Complex.realPhase_secondDerivative_vdc_shiftedDifference
          (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
          h)
        a (b - h))
    (hlam_nonneg : 0 ≤ lam)
    (hrho_pos : 0 < rho)
    (k : ℤ)
    (hrational :
      ∀ c d : ℕ,
        Complex.realPhase_integerIncrementResonanceWindow
            (Complex.realPhase_secondDerivative_vdc_shiftedDifference
              (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
              h)
            a (b - h) (2 * Real.pi * (k : ℝ)) lam =
          Finset.Ico c d →
        c < d - 1 →
          rho * (((d - 1) - c : ℕ) : ℝ) ≤
            ‖t‖ *
              (((h : ℝ) / (((c + 1) * (c + h) : ℕ) : ℝ)) -
                ((h : ℝ) /
                  (((d - 1) * ((d - 1) + h + 1) : ℕ) : ℝ)))) :
    ((Complex.realPhase_integerIncrementResonanceWindow
        (Complex.realPhase_secondDerivative_vdc_shiftedDifference
          (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
          h)
        a (b - h) (2 * Real.pi * (k : ℝ)) lam).card : ℝ) ≤
      (2 * lam) / rho + 1 := by
  exact
    Complex.logarithmicPhaseRealPhase_shiftedDifference_resonanceWindow_card_real_le_one_add_two_mul_div_of_rational_endpoint_spread
      t ht_nonneg ha habh hmono hlam_nonneg hrho_pos hrational

/-- Shift-range form of the active integer-resonance window cardinality
estimate, packaged in the exact hypothesis shape required by the range-counted
active-center Weyl theorem. -/
theorem Complex.logarithmicPhaseRealPhase_shiftRange_activeCenter_window_card_le_of_rational_endpoint_spread
    (t : ℝ)
    (ht_nonneg : 0 ≤ t)
    {a b : ℕ}
    {lam rho W : ℕ → ℝ}
    (ha : 1 ≤ a)
    (habh :
      ∀ h : ℕ,
        h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange
            (Real.secondDerivativeVdc_weylShiftLength ‖t‖) →
          a ≤ b - h)
    (hmono :
      ∀ h : ℕ,
        h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange
            (Real.secondDerivativeVdc_weylShiftLength ‖t‖) →
          Complex.realPhase_integerIncrementMonotoneOn
            (Complex.realPhase_secondDerivative_vdc_shiftedDifference
              (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
              h)
            a (b - h))
    (hlam_nonneg :
      ∀ h : ℕ,
        h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange
            (Real.secondDerivativeVdc_weylShiftLength ‖t‖) →
          0 ≤ lam h)
    (hrho_pos :
      ∀ h : ℕ,
        h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange
            (Real.secondDerivativeVdc_weylShiftLength ‖t‖) →
          0 < rho h)
    (hW :
      ∀ h : ℕ,
        h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange
            (Real.secondDerivativeVdc_weylShiftLength ‖t‖) →
          (2 * lam h) / rho h + 1 ≤ W h)
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
                  a (b - h) (2 * Real.pi * (k : ℝ)) (lam h) =
                Finset.Ico c d →
              c < d - 1 →
                rho h * (((d - 1) - c : ℕ) : ℝ) ≤
                  ‖t‖ *
                    (((h : ℝ) / (((c + 1) * (c + h) : ℕ) : ℝ)) -
                      ((h : ℝ) /
                        (((d - 1) * ((d - 1) + h + 1) : ℕ) : ℝ)))) :
    ∀ h : ℕ,
      h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange
          (Real.secondDerivativeVdc_weylShiftLength ‖t‖) →
        ∀ k : ℤ,
          k ∈
            Complex.logarithmicPhaseRealPhase_shiftedDifference_activeCenters
              t a b h (lam h) →
            ((Complex.realPhase_integerIncrementResonanceWindow
              (Complex.realPhase_secondDerivative_vdc_shiftedDifference
                (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
                h)
              a (b - h) (2 * Real.pi * (k : ℝ)) (lam h)).card :
                ℝ) ≤ W h := by
  intro h hh k _hk
  have hcard :
      ((Complex.realPhase_integerIncrementResonanceWindow
        (Complex.realPhase_secondDerivative_vdc_shiftedDifference
          (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
          h)
        a (b - h) (2 * Real.pi * (k : ℝ)) (lam h)).card : ℝ) ≤
        (2 * lam h) / rho h + 1 :=
    Complex.logarithmicPhaseRealPhase_shiftedDifference_integerResonanceWindow_card_le_of_rational_endpoint_spread
      t ht_nonneg ha (habh h hh) (hmono h hh) (hlam_nonneg h hh)
      (hrho_pos h hh) k (hrational h hh k)
  exact le_trans hcard (hW h hh)

end

end LFunctions
end Boundary
