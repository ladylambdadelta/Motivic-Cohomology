import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalization.BoundaryEulerAbel.LogarithmicPhase.Curvature.RealPhaseCore

/-!
# Real-phase derivative packet-index monotonicity

This file owns the monotonicity of the logarithmic derivative packet index on
positive integer blocks.
-/

namespace Boundary
namespace LFunctions

noncomputable section

/-- The logarithmic derivative-packet index is monotone in the sample variable
on the positive branch `t ≥ 0`. -/
theorem Complex.logarithmicPhaseRealPhase_derivPacketIndex_mono
    (t : ℝ)
    (ht_nonneg : 0 ≤ t)
    {a b k n : ℕ}
    (ha : 1 ≤ a)
    (hk_block : k ∈ Finset.Icc a b)
    (hn_block : n ∈ Finset.Icc a b)
    (hkn : k ≤ n) :
    Complex.realPhase_secondDerivative_vdc_derivPacketIndex
        (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t) k ≤
      Complex.realPhase_secondDerivative_vdc_derivPacketIndex
        (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t) n := by
  let φ : ℝ → ℝ :=
    Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t
  have hk_one : 1 ≤ k :=
    le_trans ha (Finset.mem_Icc.mp hk_block).1
  have hn_one : 1 ≤ n :=
    le_trans ha (Finset.mem_Icc.mp hn_block).1
  have hk_pos_nat : 0 < k :=
    Nat.lt_of_succ_le hk_one
  have hn_pos_nat : 0 < n :=
    Nat.lt_of_succ_le hn_one
  have hk_pos : 0 < (k : ℝ) :=
    Nat.cast_pos.mpr hk_pos_nat
  have hn_pos : 0 < (n : ℝ) :=
    Nat.cast_pos.mpr hn_pos_nat
  have hT_nonneg : 0 ≤ ‖t‖ :=
    norm_nonneg t
  have hrecip :
      (n : ℝ)⁻¹ ≤ (k : ℝ)⁻¹ :=
    inv_anti₀ hk_pos (Nat.cast_le.mpr hkn)
  have hscale :
      ‖t‖ / (n : ℝ) ≤ ‖t‖ / (k : ℝ) := by
    have hmul :
        ‖t‖ * (n : ℝ)⁻¹ ≤ ‖t‖ * (k : ℝ)⁻¹ :=
      mul_le_mul_of_nonneg_left hrecip hT_nonneg
    exact
      Eq.subst
        (motive := fun left : ℝ => left ≤ ‖t‖ / (k : ℝ))
        (div_eq_mul_inv ‖t‖ (n : ℝ)).symm
        (Eq.subst
          (motive := fun right : ℝ => ‖t‖ * (n : ℝ)⁻¹ ≤ right)
          (div_eq_mul_inv ‖t‖ (k : ℝ)).symm
          hmul)
  have hderiv_k :
      deriv φ k = -(‖t‖ / (k : ℝ)) :=
    Complex.logarithmicPhaseRealPhase_deriv_eq_neg_norm_div_parenthesized
      t ht_nonneg hk_pos
  have hderiv_n :
      deriv φ n = -(‖t‖ / (n : ℝ)) :=
    Complex.logarithmicPhaseRealPhase_deriv_eq_neg_norm_div_parenthesized
      t ht_nonneg hn_pos
  have hderiv_le :
      deriv φ k ≤ deriv φ n := by
    have hneg :
        -(‖t‖ / (k : ℝ)) ≤ -(‖t‖ / (n : ℝ)) :=
      neg_le_neg hscale
    exact
      Eq.subst
        (motive := fun left : ℝ => left ≤ deriv φ n)
        hderiv_k.symm
        (Eq.subst
          (motive := fun right : ℝ => -(‖t‖ / (k : ℝ)) ≤ right)
          hderiv_n.symm
          hneg)
  have hfloor_arg :
      deriv φ k + (1 / 2 : ℝ) ≤ deriv φ n + (1 / 2 : ℝ) :=
    add_le_add_right hderiv_le (1 / 2 : ℝ)
  exact Int.floor_mono hfloor_arg

end

end LFunctions
end Boundary
