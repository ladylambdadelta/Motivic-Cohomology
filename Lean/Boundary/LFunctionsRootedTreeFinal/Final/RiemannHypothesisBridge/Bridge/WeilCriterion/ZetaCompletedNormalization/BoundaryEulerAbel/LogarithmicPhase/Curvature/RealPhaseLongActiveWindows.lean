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

end

end LFunctions
end Boundary
