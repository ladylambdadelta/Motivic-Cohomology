import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalization.BoundaryEulerAbel.LogarithmicPhase.Curvature.RealPhaseCore

/-!
# Real-phase active derivative-packet bounds

This file owns the elementary witness and endpoint index bounds for active
second-derivative packets of the real logarithmic phase.
-/

namespace Boundary
namespace LFunctions

noncomputable section

/-- Active derivative-frequency membership is witnessed by an actual integer
sample in the original block. -/
theorem Complex.logarithmicPhaseRealPhase_activeDerivPacket_witness
    (t : ℝ)
    {a b : ℕ}
    {m : ℤ}
    (hm :
      m ∈
        Complex.realPhase_secondDerivative_vdc_activeDerivPackets
          (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
          a b) :
    ∃ n : ℕ,
      n ∈ Finset.Icc a b ∧
        Complex.realPhase_secondDerivative_vdc_derivPacketIndex
          (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
          n = m := by
  exact Finset.mem_image.mp hm

/-- The witnessing sample for an active logarithmic derivative packet lies in
the parent real interval. -/
theorem Complex.logarithmicPhaseRealPhase_activeDerivPacket_witness_mem_Icc
    {a b n : ℕ}
    (hn : n ∈ Finset.Icc a b) :
    (n : ℝ) ∈ Set.Icc (a : ℝ) ((b + 1 : ℕ) : ℝ) := by
  have hn_bounds : a ≤ n ∧ n ≤ b :=
    Finset.mem_Icc.mp hn
  exact And.intro
    (Nat.cast_le.mpr hn_bounds.1)
    (Nat.cast_le.mpr
      (Nat.le_trans hn_bounds.2 (Nat.le_succ b)))

/-- The floor packet index is below the derivative value plus half a unit. -/
theorem Complex.realPhase_secondDerivative_vdc_derivPacketIndex_cast_le
    (φ : ℝ → ℝ)
    (n : ℕ) :
    ((Complex.realPhase_secondDerivative_vdc_derivPacketIndex φ n : ℤ) : ℝ) ≤
      deriv φ n + (1 / 2 : ℝ) := by
  exact Int.floor_le (deriv φ n + (1 / 2 : ℝ))

/-- The derivative value minus half a unit is below the floor packet index. -/
theorem Complex.realPhase_secondDerivative_vdc_deriv_sub_half_le_index_cast
    (φ : ℝ → ℝ)
    (n : ℕ) :
    deriv φ n - (1 / 2 : ℝ) ≤
      ((Complex.realPhase_secondDerivative_vdc_derivPacketIndex φ n : ℤ) : ℝ) := by
  have hfloor :
      deriv φ n + (1 / 2 : ℝ) <
        ((Complex.realPhase_secondDerivative_vdc_derivPacketIndex φ n : ℤ) : ℝ) + 1 :=
    Int.lt_floor_add_one (deriv φ n + (1 / 2 : ℝ))
  have hsub_lt :
      deriv φ n + (1 / 2 : ℝ) - 1 <
        ((Complex.realPhase_secondDerivative_vdc_derivPacketIndex φ n : ℤ) : ℝ) :=
    (sub_lt_iff_lt_add).mpr hfloor
  have hleft :
      deriv φ n + (1 / 2 : ℝ) - 1 =
        deriv φ n - (1 / 2 : ℝ) := by
    have hhalf_sub_one :
        (1 / 2 : ℝ) - 1 = -(1 / 2 : ℝ) :=
      half_sub (1 : ℝ)
    calc
      deriv φ n + (1 / 2 : ℝ) - 1 =
          deriv φ n + ((1 / 2 : ℝ) - 1) :=
        add_sub_assoc (deriv φ n) (1 / 2 : ℝ) 1
      _ = deriv φ n + (-(1 / 2 : ℝ)) := by
        exact congrArg (fun r : ℝ => deriv φ n + r) hhalf_sub_one
      _ = deriv φ n - (1 / 2 : ℝ) :=
        (sub_eq_add_neg (deriv φ n) (1 / 2 : ℝ)).symm
  exact le_of_lt
    (Eq.subst
      (motive := fun r : ℝ =>
        r <
          ((Complex.realPhase_secondDerivative_vdc_derivPacketIndex φ n : ℤ) : ℝ))
      hleft
      hsub_lt)

/-- Active logarithmic packet indices are bounded above by the right endpoint
derivative, with the unavoidable half-window slack. -/
theorem Complex.logarithmicPhaseRealPhase_activeDerivPacket_index_upper
    (t : ℝ)
    (ht_nonneg : 0 ≤ t)
    {a b : ℕ}
    (ha : 1 ≤ a)
    {m : ℤ}
    (hm :
      m ∈
        Complex.realPhase_secondDerivative_vdc_activeDerivPackets
          (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
          a b) :
    (m : ℝ) ≤
      -(‖t‖ / (((b + 1 : ℕ) : ℝ))) + (1 / 2 : ℝ) := by
  let φ : ℝ → ℝ :=
    Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t
  match
    Complex.logarithmicPhaseRealPhase_activeDerivPacket_witness t hm with
  | ⟨n, hn_block, hn_index⟩ =>
      have hn_Icc :
          (n : ℝ) ∈ Set.Icc (a : ℝ) ((b + 1 : ℕ) : ℝ) :=
        Complex.logarithmicPhaseRealPhase_activeDerivPacket_witness_mem_Icc
          hn_block
      have hneg_lower :
          ‖t‖ / (((b + 1 : ℕ) : ℝ)) ≤ -deriv φ n :=
        Complex.logarithmicPhaseRealPhase_neg_deriv_lower_on_integer_block
          t ht_nonneg ha hn_Icc
      have hderiv_upper :
          deriv φ n ≤ -(‖t‖ / (((b + 1 : ℕ) : ℝ))) := by
        have hneg :
            -(-deriv φ n) ≤ -(‖t‖ / (((b + 1 : ℕ) : ℝ))) :=
          neg_le_neg hneg_lower
        exact
          Eq.subst
            (motive := fun left : ℝ =>
              left ≤ -(‖t‖ / (((b + 1 : ℕ) : ℝ))))
            (neg_neg (deriv φ n))
            hneg
      have hindex_le :
          ((Complex.realPhase_secondDerivative_vdc_derivPacketIndex φ n : ℤ) : ℝ) ≤
            deriv φ n + (1 / 2 : ℝ) :=
        Complex.realPhase_secondDerivative_vdc_derivPacketIndex_cast_le φ n
      have hderiv_half :
          deriv φ n + (1 / 2 : ℝ) ≤
            -(‖t‖ / (((b + 1 : ℕ) : ℝ))) + (1 / 2 : ℝ) :=
        add_le_add_right hderiv_upper (1 / 2 : ℝ)
      exact
        Eq.subst
          (motive := fun k : ℤ =>
            (k : ℝ) ≤
              -(‖t‖ / (((b + 1 : ℕ) : ℝ))) + (1 / 2 : ℝ))
          hn_index
          (le_trans hindex_le hderiv_half)

/-- Active logarithmic packet indices are bounded below by the left endpoint
derivative, with the unavoidable half-window slack. -/
theorem Complex.logarithmicPhaseRealPhase_activeDerivPacket_index_lower
    (t : ℝ)
    (ht_nonneg : 0 ≤ t)
    {a b : ℕ}
    (ha : 1 ≤ a)
    {m : ℤ}
    (hm :
      m ∈
        Complex.realPhase_secondDerivative_vdc_activeDerivPackets
          (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
          a b) :
    -(‖t‖ / (a : ℝ)) - (1 / 2 : ℝ) ≤ (m : ℝ) := by
  let φ : ℝ → ℝ :=
    Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t
  match
    Complex.logarithmicPhaseRealPhase_activeDerivPacket_witness t hm with
  | ⟨n, hn_block, hn_index⟩ =>
      have hn_Icc :
          (n : ℝ) ∈ Set.Icc (a : ℝ) ((b + 1 : ℕ) : ℝ) :=
        Complex.logarithmicPhaseRealPhase_activeDerivPacket_witness_mem_Icc
          hn_block
      have hneg_deriv_upper :
          -deriv φ n ≤ ‖t‖ / (a : ℝ) :=
        Complex.logarithmicPhaseRealPhase_neg_deriv_upper_on_integer_block
          t ht_nonneg ha hn_Icc
      have hderiv_lower :
          -(‖t‖ / (a : ℝ)) ≤ deriv φ n := by
        have hneg :
            -(‖t‖ / (a : ℝ)) ≤ -(-deriv φ n) :=
          neg_le_neg hneg_deriv_upper
        exact
          Eq.subst
            (motive := fun right : ℝ =>
              -(‖t‖ / (a : ℝ)) ≤ right)
            (neg_neg (deriv φ n))
            hneg
      have hderiv_half :
          -(‖t‖ / (a : ℝ)) - (1 / 2 : ℝ) ≤
            deriv φ n - (1 / 2 : ℝ) :=
        sub_le_sub_right hderiv_lower (1 / 2 : ℝ)
      have hindex_lower :
          deriv φ n - (1 / 2 : ℝ) ≤
            ((Complex.realPhase_secondDerivative_vdc_derivPacketIndex φ n : ℤ) : ℝ) :=
        Complex.realPhase_secondDerivative_vdc_deriv_sub_half_le_index_cast φ n
      exact
        Eq.subst
          (motive := fun k : ℤ =>
            -(‖t‖ / (a : ℝ)) - (1 / 2 : ℝ) ≤ (k : ℝ))
          hn_index
          (le_trans hderiv_half hindex_lower)

end

end LFunctions
end Boundary
