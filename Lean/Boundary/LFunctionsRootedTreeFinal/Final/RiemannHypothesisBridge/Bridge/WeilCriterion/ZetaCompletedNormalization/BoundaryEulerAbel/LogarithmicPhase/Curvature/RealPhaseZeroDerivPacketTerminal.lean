import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalization.BoundaryEulerAbel.LogarithmicPhase.Curvature.RealPhaseEndpointRightZero

/-!
# Real-phase zero derivative packet terminal interval

This file owns the order-theoretic reconstruction of the zero derivative
frequency packet as a terminal interval.
-/

namespace Boundary
namespace LFunctions

noncomputable section

/-- Upward closure of the zero derivative-frequency packet inside the block. -/
theorem Complex.logarithmicPhaseRealPhase_zeroDerivPacket_upwardClosed
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    (ht_nonneg : 0 ≤ t)
    {a b n k : ℕ}
    (ha : 1 ≤ a)
    (hn :
      n ∈ Complex.realPhase_secondDerivative_vdc_derivPacket
        (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
        a b 0)
    (hk_block : k ∈ Finset.Icc a b)
    (hnk : n ≤ k) :
    k ∈ Complex.realPhase_secondDerivative_vdc_derivPacket
      (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
      a b 0 := by
  let φ : ℝ → ℝ :=
    Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t
  have hn_block : n ∈ Finset.Icc a b :=
    Complex.realPhase_secondDerivative_vdc_derivPacket_mem_block φ hn
  have hn_one : 1 ≤ n :=
    le_trans ha (Finset.mem_Icc.mp hn_block).1
  have hk_one : 1 ≤ k :=
    le_trans ha (Finset.mem_Icc.mp hk_block).1
  have hn_pos_nat : 0 < n :=
    Nat.lt_of_succ_le hn_one
  have hk_pos_nat : 0 < k :=
    Nat.lt_of_succ_le hk_one
  have hn_pos : 0 < (n : ℝ) :=
    Nat.cast_pos.mpr hn_pos_nat
  have hk_pos : 0 < (k : ℝ) :=
    Nat.cast_pos.mpr hk_pos_nat
  have hT_nonneg : 0 ≤ ‖t‖ :=
    le_trans zero_le_one ht
  have hwindow_lower_n :
      ((0 : ℤ) : ℝ) - (1 / 2 : ℝ) ≤ deriv φ n :=
    Complex.realPhase_secondDerivative_vdc_derivPacket_lower φ hn
  have hzero_left :
      ((0 : ℤ) : ℝ) - (1 / 2 : ℝ) = -(1 / 2 : ℝ) := by
    calc
      ((0 : ℤ) : ℝ) - (1 / 2 : ℝ) =
          (0 : ℝ) - (1 / 2 : ℝ) := by
        exact congrArg (fun r : ℝ => r - (1 / 2 : ℝ)) Int.cast_zero
      _ = -(1 / 2 : ℝ) :=
        zero_sub (1 / 2 : ℝ)
  have hderiv_n :
      deriv φ n = -(‖t‖ / (n : ℝ)) :=
    Complex.logarithmicPhaseRealPhase_deriv_eq_neg_norm_div_parenthesized
      t ht_nonneg hn_pos
  have hneg_bound_n :
      -(1 / 2 : ℝ) ≤ -(‖t‖ / (n : ℝ)) :=
    Eq.subst
      (motive := fun right : ℝ => -(1 / 2 : ℝ) ≤ right)
      hderiv_n
      (Eq.subst
        (motive := fun left : ℝ => left ≤ deriv φ n)
        hzero_left
        hwindow_lower_n)
  have hscale_n :
      ‖t‖ / (n : ℝ) ≤ (1 / 2 : ℝ) := by
    have hflip :
        - (-(‖t‖ / (n : ℝ))) ≤ - (-(1 / 2 : ℝ)) :=
      neg_le_neg hneg_bound_n
    exact
      Eq.subst
        (motive := fun left : ℝ => left ≤ (1 / 2 : ℝ))
        (neg_neg (‖t‖ / (n : ℝ)))
        (Eq.subst
          (motive := fun right : ℝ =>
            - (-(‖t‖ / (n : ℝ))) ≤ right)
          (neg_neg (1 / 2 : ℝ))
          hflip)
  have hrecip_kn : (k : ℝ)⁻¹ ≤ (n : ℝ)⁻¹ :=
    inv_anti₀ hn_pos (Nat.cast_le.mpr hnk)
  have hscale_kn :
      ‖t‖ / (k : ℝ) ≤ ‖t‖ / (n : ℝ) := by
    have hmul :
        ‖t‖ * (k : ℝ)⁻¹ ≤ ‖t‖ * (n : ℝ)⁻¹ :=
      mul_le_mul_of_nonneg_left hrecip_kn hT_nonneg
    exact
      Eq.subst
        (motive := fun left : ℝ => left ≤ ‖t‖ / (n : ℝ))
        (div_eq_mul_inv ‖t‖ (k : ℝ)).symm
        (Eq.subst
          (motive := fun right : ℝ => ‖t‖ * (k : ℝ)⁻¹ ≤ right)
          (div_eq_mul_inv ‖t‖ (n : ℝ)).symm
          hmul)
  have hscale_k :
      ‖t‖ / (k : ℝ) ≤ (1 / 2 : ℝ) :=
    le_trans hscale_kn hscale_n
  have hderiv_k :
      deriv φ k = -(‖t‖ / (k : ℝ)) :=
    Complex.logarithmicPhaseRealPhase_deriv_eq_neg_norm_div_parenthesized
      t ht_nonneg hk_pos
  have hlower_k_raw :
      -(1 / 2 : ℝ) ≤ -(‖t‖ / (k : ℝ)) :=
    neg_le_neg hscale_k
  have hlower_k :
      ((0 : ℤ) : ℝ) - (1 / 2 : ℝ) ≤ deriv φ k :=
    Eq.subst
      (motive := fun right : ℝ =>
        ((0 : ℤ) : ℝ) - (1 / 2 : ℝ) ≤ right)
      hderiv_k.symm
      (Eq.subst
        (motive := fun left : ℝ => left ≤ -(‖t‖ / (k : ℝ)))
        hzero_left.symm
        hlower_k_raw)
  have hscale_k_nonneg :
      0 ≤ ‖t‖ / (k : ℝ) :=
    div_nonneg hT_nonneg (le_of_lt hk_pos)
  have hderiv_k_nonpos :
      deriv φ k ≤ 0 :=
    Eq.subst
      (motive := fun left : ℝ => left ≤ 0)
      hderiv_k.symm
      (neg_nonpos.mpr hscale_k_nonneg)
  have hhalf_pos : (0 : ℝ) < (1 / 2 : ℝ) :=
    half_pos zero_lt_one
  have hzero_lt_upper :
      (0 : ℝ) < ((0 : ℤ) : ℝ) + (1 / 2 : ℝ) := by
    have hupper_eq :
        ((0 : ℤ) : ℝ) + (1 / 2 : ℝ) = (1 / 2 : ℝ) := by
      calc
        ((0 : ℤ) : ℝ) + (1 / 2 : ℝ) =
            (0 : ℝ) + (1 / 2 : ℝ) := by
          exact congrArg (fun r : ℝ => r + (1 / 2 : ℝ)) Int.cast_zero
        _ = (1 / 2 : ℝ) :=
          zero_add (1 / 2 : ℝ)
    exact
      Eq.subst
        (motive := fun right : ℝ => (0 : ℝ) < right)
        hupper_eq.symm
        hhalf_pos
  have hupper_k :
      deriv φ k < ((0 : ℤ) : ℝ) + (1 / 2 : ℝ) :=
    lt_of_le_of_lt hderiv_k_nonpos hzero_lt_upper
  exact
    (Complex.mem_realPhase_secondDerivative_vdc_derivPacket_iff φ).mpr
      (And.intro hk_block (And.intro hlower_k hupper_k))

/-- A nonempty zero derivative-frequency packet reaches the right endpoint of
the ambient block. -/
theorem Complex.logarithmicPhaseRealPhase_zeroDerivPacket_nonempty_rightEndpoint
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    (ht_nonneg : 0 ≤ t)
    {a b : ℕ}
    (ha : 1 ≤ a)
    (hp :
      (Complex.realPhase_secondDerivative_vdc_derivPacket
        (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
        a b 0).Nonempty) :
    b ∈ Complex.realPhase_secondDerivative_vdc_derivPacket
      (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
      a b 0 := by
  match hp with
  | ⟨n, hn⟩ =>
      have hn_block : n ∈ Finset.Icc a b :=
        Complex.realPhase_secondDerivative_vdc_derivPacket_mem_block
          (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
          hn
      have hn_bounds : a ≤ n ∧ n ≤ b :=
        Finset.mem_Icc.mp hn_block
      have hb_block : b ∈ Finset.Icc a b :=
        Finset.mem_Icc.mpr (And.intro (le_trans hn_bounds.1 hn_bounds.2) le_rfl)
      exact
        Complex.logarithmicPhaseRealPhase_zeroDerivPacket_upwardClosed
          t ht ht_nonneg ha hn hb_block hn_bounds.2

/-- A nonempty upward-closed zero packet is exactly the interval from its least
sample to the right endpoint. -/
theorem Complex.logarithmicPhaseRealPhase_zeroDerivPacket_nonempty_eq_min_Icc
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    (ht_nonneg : 0 ≤ t)
    {a b : ℕ}
    (ha : 1 ≤ a)
    (hp :
      (Complex.realPhase_secondDerivative_vdc_derivPacket
        (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
        a b 0).Nonempty) :
    Complex.realPhase_secondDerivative_vdc_derivPacket
        (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
        a b 0 =
      Finset.Icc
        ((Complex.realPhase_secondDerivative_vdc_derivPacket
          (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
          a b 0).min' hp)
        b := by
  let φ : ℝ → ℝ :=
    Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t
  let packet : Finset ℕ :=
    Complex.realPhase_secondDerivative_vdc_derivPacket φ a b 0
  let c : ℕ := packet.min' hp
  have hc_mem : c ∈ packet :=
    Finset.min'_mem packet hp
  have hc_block : c ∈ Finset.Icc a b :=
    Complex.realPhase_secondDerivative_vdc_derivPacket_mem_block φ hc_mem
  have hc_bounds : a ≤ c ∧ c ≤ b :=
    Finset.mem_Icc.mp hc_block
  exact Finset.ext
    (fun n =>
      Iff.intro
        (fun hn =>
          have hn_min : c ≤ n :=
            Finset.min'_le packet n hn
          have hn_block : n ∈ Finset.Icc a b :=
            Complex.realPhase_secondDerivative_vdc_derivPacket_mem_block φ hn
          have hn_bounds : a ≤ n ∧ n ≤ b :=
            Finset.mem_Icc.mp hn_block
          Finset.mem_Icc.mpr (And.intro hn_min hn_bounds.2))
        (fun hn_interval =>
          have hn_bounds : c ≤ n ∧ n ≤ b :=
            Finset.mem_Icc.mp hn_interval
          have hn_block : n ∈ Finset.Icc a b :=
            Finset.mem_Icc.mpr
              (And.intro (le_trans hc_bounds.1 hn_bounds.1) hn_bounds.2)
          Complex.logarithmicPhaseRealPhase_zeroDerivPacket_upwardClosed
            t ht ht_nonneg ha hc_mem hn_block hn_bounds.1))

/-- The zero derivative-frequency packet is a genuine terminal endpoint
interval. -/
theorem Complex.logarithmicPhaseRealPhase_zeroDerivPacket_eq_terminalInterval
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    (ht_nonneg : 0 ≤ t)
    {a b : ℕ}
    (ha : 1 ≤ a)
    (hab : a ≤ b) :
    ∃ c : ℕ,
      a ≤ c ∧ c ≤ b + 1 ∧
      Complex.realPhase_secondDerivative_vdc_derivPacket
          (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
          a b 0 =
        Finset.Icc c b := by
  let packet : Finset ℕ :=
    Complex.realPhase_secondDerivative_vdc_derivPacket
      (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
      a b 0
  match packet.eq_empty_or_nonempty with
  | Or.inl hempty =>
      have hinterval_empty : Finset.Icc (b + 1) b = (∅ : Finset ℕ) :=
        Finset.eq_empty_iff_forall_not_mem.mpr
          (fun n hn =>
            have hn_bounds : b + 1 ≤ n ∧ n ≤ b :=
              Finset.mem_Icc.mp hn
            have hb_lt_n : b < n :=
              Nat.lt_of_succ_le hn_bounds.1
            have hnot : ¬ n ≤ b :=
              not_le_of_gt hb_lt_n
            hnot hn_bounds.2)
      have hpacket_empty :
          Complex.realPhase_secondDerivative_vdc_derivPacket
              (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
              a b 0 =
            ∅ :=
        hempty
      exact Exists.intro (b + 1)
        (And.intro
          (Nat.le_trans hab (Nat.le_succ b))
          (And.intro le_rfl
            (Eq.trans hpacket_empty hinterval_empty.symm)))
  | Or.inr hp =>
      let c : ℕ := packet.min' hp
      have hc_mem :
          c ∈ Complex.realPhase_secondDerivative_vdc_derivPacket
            (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
            a b 0 :=
        Finset.min'_mem packet hp
      have hc_block : c ∈ Finset.Icc a b :=
        Complex.realPhase_secondDerivative_vdc_derivPacket_mem_block
          (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
          hc_mem
      have hc_bounds : a ≤ c ∧ c ≤ b :=
        Finset.mem_Icc.mp hc_block
      have hpacket :
          Complex.realPhase_secondDerivative_vdc_derivPacket
              (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
              a b 0 =
            Finset.Icc c b :=
        Complex.logarithmicPhaseRealPhase_zeroDerivPacket_nonempty_eq_min_Icc
          t ht ht_nonneg ha hp
      exact Exists.intro c
        (And.intro hc_bounds.1
          (And.intro (Nat.le_trans hc_bounds.2 (Nat.le_succ b)) hpacket))

end

end LFunctions
end Boundary
