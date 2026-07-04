import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalization.BoundaryEulerAbel.LogarithmicPhase.Curvature.RealPhaseZeroDerivPacketTerminal

/-!
# Real-phase zero terminal increment bounds

This file owns the elementary adjacent-increment bounds on the nonempty
zero-derivative terminal packet.
-/

namespace Boundary
namespace LFunctions

noncomputable section

/-- Successive integer logarithmic ratios have the canonical reciprocal upper
bound. -/
theorem Complex.logarithmicPhase_successive_log_ratio_upper_bound
    {n : ℕ}
    (hn : 0 < n) :
    Real.log ((((n + 1 : ℕ) : ℝ)) / (((n : ℕ) : ℝ))) ≤
      (((n : ℕ) : ℝ))⁻¹ := by
  have hn_real_pos : (0 : ℝ) < (((n : ℕ) : ℝ)) :=
    Nat.cast_pos.mpr hn
  have hn_real_ne : (((n : ℕ) : ℝ)) ≠ 0 :=
    ne_of_gt hn_real_pos
  have hsucc_pos_nat : 0 < n + 1 :=
    Nat.succ_pos n
  have hsucc_real_pos : (0 : ℝ) < (((n + 1 : ℕ) : ℝ)) :=
    Nat.cast_pos.mpr hsucc_pos_nat
  have hratio_pos :
      0 < (((n + 1 : ℕ) : ℝ)) / (((n : ℕ) : ℝ)) :=
    div_pos hsucc_real_pos hn_real_pos
  have hlog_le :
      Real.log ((((n + 1 : ℕ) : ℝ)) / (((n : ℕ) : ℝ))) ≤
        (((n + 1 : ℕ) : ℝ)) / (((n : ℕ) : ℝ)) - 1 :=
    Real.log_le_sub_one_of_pos hratio_pos
  have hone_as_ratio :
      (1 : ℝ) =
        (((n : ℕ) : ℝ)) / (((n : ℕ) : ℝ)) :=
    (div_self hn_real_ne).symm
  have hsucc_sub :
      (((n + 1 : ℕ) : ℝ)) - (((n : ℕ) : ℝ)) = 1 := by
    calc
      (((n + 1 : ℕ) : ℝ)) - (((n : ℕ) : ℝ)) =
          (((n : ℕ) : ℝ) + 1) - (((n : ℕ) : ℝ)) := by
        exact congrArg
          (fun y : ℝ => y - (((n : ℕ) : ℝ)))
          (Nat.cast_add_one n)
      _ = 1 :=
        add_sub_cancel_left (((n : ℕ) : ℝ)) 1
  have hratio_sub :
      (((n + 1 : ℕ) : ℝ)) / (((n : ℕ) : ℝ)) - 1 =
        (((n : ℕ) : ℝ))⁻¹ := by
    calc
      (((n + 1 : ℕ) : ℝ)) / (((n : ℕ) : ℝ)) - 1 =
          (((n + 1 : ℕ) : ℝ)) / (((n : ℕ) : ℝ)) -
            (((n : ℕ) : ℝ)) / (((n : ℕ) : ℝ)) := by
        exact congrArg
          (fun y : ℝ =>
            (((n + 1 : ℕ) : ℝ)) / (((n : ℕ) : ℝ)) - y)
          hone_as_ratio
      _ =
          ((((n + 1 : ℕ) : ℝ)) - (((n : ℕ) : ℝ))) /
            (((n : ℕ) : ℝ)) := by
        exact
          (sub_div
            (((n + 1 : ℕ) : ℝ))
            (((n : ℕ) : ℝ))
            (((n : ℕ) : ℝ))).symm
      _ = 1 / (((n : ℕ) : ℝ)) := by
        exact congrArg
          (fun y : ℝ => y / (((n : ℕ) : ℝ)))
          hsucc_sub
      _ = (((n : ℕ) : ℝ))⁻¹ :=
        one_div (((n : ℕ) : ℝ))
  exact
    Eq.subst
      (motive := fun right : ℝ =>
        Real.log ((((n + 1 : ℕ) : ℝ)) / (((n : ℕ) : ℝ))) ≤ right)
      hratio_sub
      hlog_le

/-- The logarithmic phase adjacent increment has norm at most the local
reciprocal scale. -/
theorem Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase_integerIncrement_norm_le_localScale
    (t : ℝ)
    {n : ℕ}
    (hn : 0 < n) :
    ‖Complex.realPhase_integerIncrement
        (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t) n‖ ≤
      ‖t‖ / (((n : ℕ) : ℝ)) := by
  let L : ℝ :=
    Real.log ((((n + 1 : ℕ) : ℝ)) / (((n : ℕ) : ℝ)))
  have hL_lower :
      (((n + 1 : ℕ) : ℝ))⁻¹ ≤ L :=
    Complex.logarithmicPhase_successive_log_ratio_lower_bound hn
  have hnsucc_pos_nat : 0 < n + 1 :=
    Nat.succ_pos n
  have hnsucc_pos_real : (0 : ℝ) < (((n + 1 : ℕ) : ℝ)) :=
    Nat.cast_pos.mpr hnsucc_pos_nat
  have hL_nonneg : 0 ≤ L :=
    le_trans (inv_nonneg.mpr (le_of_lt hnsucc_pos_real)) hL_lower
  have hL_upper :
      L ≤ (((n : ℕ) : ℝ))⁻¹ :=
    Complex.logarithmicPhase_successive_log_ratio_upper_bound hn
  have ht_nonneg : 0 ≤ ‖t‖ :=
    norm_nonneg t
  have hmul_upper :
      ‖t‖ * L ≤ ‖t‖ * (((n : ℕ) : ℝ))⁻¹ :=
    mul_le_mul_of_nonneg_left hL_upper ht_nonneg
  have hincrement_eq :
      Complex.realPhase_integerIncrement
          (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t) n =
        -t * L :=
    Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase_integerIncrement_eq_neg_mul_log_ratio
      t hn
  have hincrement_norm :
      ‖Complex.realPhase_integerIncrement
          (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t) n‖ =
        ‖t‖ * L := by
    calc
      ‖Complex.realPhase_integerIncrement
          (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t) n‖ =
          ‖-t * L‖ := by
        exact congrArg (fun y : ℝ => ‖y‖) hincrement_eq
      _ = ‖-t‖ * ‖L‖ :=
        norm_mul (-t) L
      _ = ‖t‖ * ‖L‖ := by
        exact congrArg (fun y : ℝ => y * ‖L‖) (norm_neg t)
      _ = ‖t‖ * L := by
        exact congrArg (fun y : ℝ => ‖t‖ * y) (Real.norm_of_nonneg hL_nonneg)
  exact
    Eq.subst
      (motive := fun left : ℝ => left ≤ ‖t‖ / (((n : ℕ) : ℝ)))
      hincrement_norm.symm
      (Eq.subst
        (motive := fun right : ℝ => ‖t‖ * L ≤ right)
        (div_eq_mul_inv ‖t‖ (((n : ℕ) : ℝ))).symm
        hmul_upper)

/-- On a nonempty zero derivative-frequency terminal packet, every adjacent
increment in the terminal interval is at most one half in norm. -/
theorem Complex.logarithmicPhaseRealPhase_zeroDerivPacket_terminal_increment_norm_le_half
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    (ht_nonneg : 0 ≤ t)
    {a b : ℕ}
    (ha : 1 ≤ a)
    (hp :
      (Complex.realPhase_secondDerivative_vdc_derivPacket
        (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
        a b 0).Nonempty)
    {n : ℕ}
    (hn :
      n ∈ Finset.Ico
        ((Complex.realPhase_secondDerivative_vdc_derivPacket
          (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
          a b 0).min' hp)
        b) :
    ‖Complex.realPhase_integerIncrement
        (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t) n‖ ≤
      (1 / 2 : ℝ) := by
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
  have hc_one : 1 ≤ c :=
    le_trans ha hc_bounds.1
  have hn_bounds : c ≤ n ∧ n < b :=
    Finset.mem_Ico.mp hn
  have hn_one : 1 ≤ n :=
    le_trans hc_one hn_bounds.1
  have hn_pos_nat : 0 < n :=
    Nat.lt_of_succ_le hn_one
  have hc_pos : 0 < (c : ℝ) :=
    Nat.cast_pos.mpr (Nat.lt_of_succ_le hc_one)
  have hn_pos : 0 < (n : ℝ) :=
    Nat.cast_pos.mpr hn_pos_nat
  have hT_nonneg : 0 ≤ ‖t‖ :=
    le_trans zero_le_one ht
  have hwindow_lower_c :
      ((0 : ℤ) : ℝ) - (1 / 2 : ℝ) ≤ deriv φ c :=
    Complex.realPhase_secondDerivative_vdc_derivPacket_lower φ hc_mem
  have hzero_left :
      ((0 : ℤ) : ℝ) - (1 / 2 : ℝ) = -(1 / 2 : ℝ) := by
    calc
      ((0 : ℤ) : ℝ) - (1 / 2 : ℝ) =
          (0 : ℝ) - (1 / 2 : ℝ) := by
        exact congrArg (fun r : ℝ => r - (1 / 2 : ℝ)) Int.cast_zero
      _ = -(1 / 2 : ℝ) :=
        zero_sub (1 / 2 : ℝ)
  have hderiv_c :
      deriv φ c = -(‖t‖ / (c : ℝ)) :=
    Complex.logarithmicPhaseRealPhase_deriv_eq_neg_norm_div_parenthesized
      t ht_nonneg hc_pos
  have hneg_bound_c :
      -(1 / 2 : ℝ) ≤ -(‖t‖ / (c : ℝ)) :=
    Eq.subst
      (motive := fun right : ℝ => -(1 / 2 : ℝ) ≤ right)
      hderiv_c
      (Eq.subst
        (motive := fun left : ℝ => left ≤ deriv φ c)
        hzero_left
        hwindow_lower_c)
  have hscale_c :
      ‖t‖ / (c : ℝ) ≤ (1 / 2 : ℝ) := by
    have hflip :
        - (-(‖t‖ / (c : ℝ))) ≤ - (-(1 / 2 : ℝ)) :=
      neg_le_neg hneg_bound_c
    exact
      Eq.subst
        (motive := fun left : ℝ => left ≤ (1 / 2 : ℝ))
        (neg_neg (‖t‖ / (c : ℝ)))
        (Eq.subst
          (motive := fun right : ℝ =>
            - (-(‖t‖ / (c : ℝ))) ≤ right)
          (neg_neg (1 / 2 : ℝ))
          hflip)
  have hrecip_nc : (n : ℝ)⁻¹ ≤ (c : ℝ)⁻¹ :=
    inv_anti₀ hc_pos (Nat.cast_le.mpr hn_bounds.1)
  have hscale_n :
      ‖t‖ / (n : ℝ) ≤ ‖t‖ / (c : ℝ) := by
    have hmul :
        ‖t‖ * (n : ℝ)⁻¹ ≤ ‖t‖ * (c : ℝ)⁻¹ :=
      mul_le_mul_of_nonneg_left hrecip_nc hT_nonneg
    exact
      Eq.subst
        (motive := fun left : ℝ => left ≤ ‖t‖ / (c : ℝ))
        (div_eq_mul_inv ‖t‖ (n : ℝ)).symm
        (Eq.subst
          (motive := fun right : ℝ => ‖t‖ * (n : ℝ)⁻¹ ≤ right)
          (div_eq_mul_inv ‖t‖ (c : ℝ)).symm
          hmul)
  have hincrement_le :
      ‖Complex.realPhase_integerIncrement φ n‖ ≤ ‖t‖ / (n : ℝ) :=
    Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase_integerIncrement_norm_le_localScale
      t hn_pos_nat
  exact le_trans hincrement_le (le_trans hscale_n hscale_c)

end

end LFunctions
end Boundary
