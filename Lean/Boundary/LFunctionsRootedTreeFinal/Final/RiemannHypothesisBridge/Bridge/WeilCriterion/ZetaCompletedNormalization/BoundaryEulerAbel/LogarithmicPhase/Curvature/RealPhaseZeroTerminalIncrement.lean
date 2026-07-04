import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalization.BoundaryEulerAbel.LogarithmicPhase.Curvature.RealPhaseZeroDerivPacketTerminal

/-!
# Real-phase zero terminal increment bounds

This file owns the elementary adjacent-increment bounds on the nonempty
zero-derivative terminal packet.
-/

namespace Boundary
namespace LFunctions

noncomputable section

/-- The half-window used by the zero packet lies strictly inside the
principal `(-π, π]` interval. -/
theorem Real.logarithmicPhase_one_half_lt_pi :
    (1 / 2 : ℝ) < Real.pi := by
  have hhalf_lt_one : (1 / 2 : ℝ) < 1 :=
    one_half_lt_one
  have hone_lt_three : (1 : ℝ) < 3 :=
    Nat.one_lt_ofNat
  exact lt_trans (lt_trans hhalf_lt_one hone_lt_three) Real.pi_gt_three

/-- The negative half-window is strictly to the right of `-π`. -/
theorem Real.logarithmicPhase_neg_pi_lt_neg_one_half :
    -Real.pi < -(1 / 2 : ℝ) :=
  neg_lt_neg Real.logarithmicPhase_one_half_lt_pi

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

/-- Successive logarithmic ratios are antitone on positive indices. -/
theorem Complex.logarithmicPhase_successive_log_ratio_antitone
    {m n : ℕ}
    (hm : 0 < m)
    (hmn : m ≤ n) :
    Real.log ((((n + 1 : ℕ) : ℝ)) / (((n : ℕ) : ℝ))) ≤
      Real.log ((((m + 1 : ℕ) : ℝ)) / (((m : ℕ) : ℝ))) := by
  have hn : 0 < n :=
    lt_of_lt_of_le hm hmn
  have hm_real_pos : (0 : ℝ) < (((m : ℕ) : ℝ)) :=
    Nat.cast_pos.mpr hm
  have hn_real_pos : (0 : ℝ) < (((n : ℕ) : ℝ)) :=
    Nat.cast_pos.mpr hn
  have hnsucc_real_pos : (0 : ℝ) < (((n + 1 : ℕ) : ℝ)) :=
    Nat.cast_pos.mpr (Nat.succ_pos n)
  have hleft_pos :
      0 < (((n + 1 : ℕ) : ℝ)) / (((n : ℕ) : ℝ)) :=
    div_pos hnsucc_real_pos hn_real_pos
  have hm_le_n_real : (((m : ℕ) : ℝ)) ≤ (((n : ℕ) : ℝ)) :=
    Nat.cast_le.mpr hmn
  have hcross :
      (((n + 1 : ℕ) : ℝ)) * (((m : ℕ) : ℝ)) ≤
        (((m + 1 : ℕ) : ℝ)) * (((n : ℕ) : ℝ)) := by
    calc
      (((n + 1 : ℕ) : ℝ)) * (((m : ℕ) : ℝ)) =
          ((((n : ℕ) : ℝ) + 1) * (((m : ℕ) : ℝ))) := by
        exact congrArg
          (fun y : ℝ => y * (((m : ℕ) : ℝ)))
          (Nat.cast_add_one n)
      _ =
          (((n : ℕ) : ℝ) * ((m : ℕ) : ℝ)) +
            (1 * (((m : ℕ) : ℝ))) := by
        exact add_mul (((n : ℕ) : ℝ)) 1 (((m : ℕ) : ℝ))
      _ = (((n : ℕ) : ℝ) * ((m : ℕ) : ℝ)) + (((m : ℕ) : ℝ)) := by
        exact congrArg
          (fun y : ℝ => (((n : ℕ) : ℝ) * ((m : ℕ) : ℝ)) + y)
          (one_mul (((m : ℕ) : ℝ)))
      _ ≤ (((n : ℕ) : ℝ) * ((m : ℕ) : ℝ)) + (((n : ℕ) : ℝ)) := by
        exact add_le_add_left hm_le_n_real
          (((n : ℕ) : ℝ) * ((m : ℕ) : ℝ))
      _ = (((m : ℕ) : ℝ) * (((n : ℕ) : ℝ))) + (((n : ℕ) : ℝ)) := by
        exact congrArg
          (fun y : ℝ => y + (((n : ℕ) : ℝ)))
          (mul_comm (((n : ℕ) : ℝ)) (((m : ℕ) : ℝ)))
      _ =
          (((m : ℕ) : ℝ) * (((n : ℕ) : ℝ))) +
            (1 * (((n : ℕ) : ℝ))) := by
        exact congrArg
          (fun y : ℝ => (((m : ℕ) : ℝ) * (((n : ℕ) : ℝ))) + y)
          (one_mul (((n : ℕ) : ℝ))).symm
      _ = ((((m : ℕ) : ℝ) + 1) * (((n : ℕ) : ℝ))) := by
        exact (add_mul (((m : ℕ) : ℝ)) 1 (((n : ℕ) : ℝ))).symm
      _ = (((m + 1 : ℕ) : ℝ)) * (((n : ℕ) : ℝ)) := by
        exact congrArg
          (fun y : ℝ => y * (((n : ℕ) : ℝ)))
          (Nat.cast_add_one m).symm
  have hratio_le :
      (((n + 1 : ℕ) : ℝ)) / (((n : ℕ) : ℝ)) ≤
        (((m + 1 : ℕ) : ℝ)) / (((m : ℕ) : ℝ)) :=
    (div_le_div_iff₀ hn_real_pos hm_real_pos).mpr hcross
  exact Real.log_le_log hleft_pos hratio_le

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

/-- In the nonnegative-parameter branch, every logarithmic adjacent increment
is nonpositive. -/
theorem Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase_integerIncrement_nonpos
    (t : ℝ)
    (ht_nonneg : 0 ≤ t)
    {n : ℕ}
    (hn : 0 < n) :
    Complex.realPhase_integerIncrement
        (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t) n ≤
      0 := by
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
  have hmul_nonneg : 0 ≤ t * L :=
    mul_nonneg ht_nonneg hL_nonneg
  have hneg_mul_nonpos : -(t * L) ≤ 0 :=
    neg_nonpos.mpr hmul_nonneg
  have hleft :
      -t * L = -(t * L) :=
    neg_mul t L
  have hincrement_eq :
      Complex.realPhase_integerIncrement
          (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t) n =
        -t * L :=
    Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase_integerIncrement_eq_neg_mul_log_ratio
      t hn
  exact
    Eq.subst
      (motive := fun left : ℝ => left ≤ 0)
      hincrement_eq.symm
      (Eq.subst
        (motive := fun left : ℝ => left ≤ 0)
        hleft.symm
        hneg_mul_nonpos)

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

/-- On a nonempty zero derivative-frequency terminal packet, every adjacent
increment lies above `-1/2`. -/
theorem Complex.logarithmicPhaseRealPhase_zeroDerivPacket_terminal_increment_neg_half_le
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
    -(1 / 2 : ℝ) ≤
      Complex.realPhase_integerIncrement
        (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t) n := by
  let θ : ℝ :=
    Complex.realPhase_integerIncrement
      (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t) n
  have hnorm :
      ‖θ‖ ≤ (1 / 2 : ℝ) :=
    Complex.logarithmicPhaseRealPhase_zeroDerivPacket_terminal_increment_norm_le_half
      t ht ht_nonneg ha hp hn
  have habs :
      |θ| ≤ (1 / 2 : ℝ) :=
    Eq.subst
      (motive := fun left : ℝ => left ≤ (1 / 2 : ℝ))
      (Real.norm_eq_abs θ)
      hnorm
  exact neg_le_of_abs_le habs

/-- On a nonempty zero derivative-frequency terminal packet, every adjacent
increment is nonpositive. -/
theorem Complex.logarithmicPhaseRealPhase_zeroDerivPacket_terminal_increment_nonpos
    (t : ℝ)
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
    Complex.realPhase_integerIncrement
        (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t) n ≤
      0 := by
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
  have hn_bounds :
      ((Complex.realPhase_secondDerivative_vdc_derivPacket
          (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
          a b 0).min' hp) ≤ n ∧ n < b :=
    Finset.mem_Ico.mp hn
  have hc_pos : 0 < c :=
    Nat.lt_of_succ_le hc_one
  have hn_pos : 0 < n :=
    lt_of_lt_of_le hc_pos hn_bounds.1
  exact
    Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase_integerIncrement_nonpos
      t ht_nonneg hn_pos

/-- On a nonempty zero derivative-frequency terminal packet, every adjacent
increment lies in the principal interval `(-π, π]`. -/
theorem Complex.logarithmicPhaseRealPhase_zeroDerivPacket_terminal_increment_mem_Ioc_pi
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
    Complex.realPhase_integerIncrement
        (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t) n ∈
      Set.Ioc (-Real.pi) Real.pi := by
  let θ : ℝ :=
    Complex.realPhase_integerIncrement
      (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t) n
  have hleft_half : -(1 / 2 : ℝ) ≤ θ :=
    Complex.logarithmicPhaseRealPhase_zeroDerivPacket_terminal_increment_neg_half_le
      t ht ht_nonneg ha hp hn
  have hleft : -Real.pi < θ :=
    lt_of_lt_of_le Real.logarithmicPhase_neg_pi_lt_neg_one_half hleft_half
  have hnonpos : θ ≤ 0 :=
    Complex.logarithmicPhaseRealPhase_zeroDerivPacket_terminal_increment_nonpos
      t ht_nonneg ha hp hn
  have hright : θ ≤ Real.pi :=
    le_trans hnonpos Real.pi_pos.le
  exact And.intro hleft hright

/-- On the zero terminal packet, the reduced adjacent increment is exactly the
raw adjacent increment; there is no winding across `2πℤ`. -/
theorem Complex.logarithmicPhaseRealPhase_zeroDerivPacket_terminal_reducedIncrement_eq
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
    Complex.realPhase_reducedIntegerIncrement
        (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t) n =
      Complex.realPhase_integerIncrement
        (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t) n := by
  let θ : ℝ :=
    Complex.realPhase_integerIncrement
      (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t) n
  have hθ : θ ∈ Set.Ioc (-Real.pi) Real.pi :=
    Complex.logarithmicPhaseRealPhase_zeroDerivPacket_terminal_increment_mem_Ioc_pi
      t ht ht_nonneg ha hp hn
  show toIocMod Real.two_pi_pos (-Real.pi) θ = θ
  exact
    (toIocMod_eq_self Real.two_pi_pos).mpr
      (real_mem_Ioc_pi_to_periodic_upper_for_logarithmicPhase hθ)

/-- The raw adjacent increments are monotone, with the chosen monotone branch
made explicit. -/
theorem Complex.logarithmicPhaseRealPhase_zeroDerivPacket_terminal_integerIncrement_monotoneOn
    (t : ℝ)
    (ht_nonneg : 0 ≤ t)
    {a b : ℕ}
    (ha : 1 ≤ a)
    (hp :
      (Complex.realPhase_secondDerivative_vdc_derivPacket
        (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
        a b 0).Nonempty) :
    MonotoneOn
      (fun n : ℕ =>
        Complex.realPhase_integerIncrement
          (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t) n)
      (Finset.Ico
        ((Complex.realPhase_secondDerivative_vdc_derivPacket
          (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
          a b 0).min' hp)
        b : Set ℕ) := by
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
  have hc_pos : 0 < c :=
    Nat.lt_of_succ_le hc_one
  intro x hx y hy hxy
  have hx_bounds : c ≤ x ∧ x < b :=
    Finset.mem_Ico.mp hx
  have hx_pos : 0 < x :=
    lt_of_lt_of_le hc_pos hx_bounds.1
  have hlog_yx :
      Real.log ((((y + 1 : ℕ) : ℝ)) / (((y : ℕ) : ℝ))) ≤
        Real.log ((((x + 1 : ℕ) : ℝ)) / (((x : ℕ) : ℝ))) :=
    Complex.logarithmicPhase_successive_log_ratio_antitone hx_pos hxy
  have ht_neg_nonpos : -t ≤ 0 :=
    neg_nonpos.mpr ht_nonneg
  have hscaled :
      -t * Real.log ((((x + 1 : ℕ) : ℝ)) / (((x : ℕ) : ℝ))) ≤
        -t * Real.log ((((y + 1 : ℕ) : ℝ)) / (((y : ℕ) : ℝ))) :=
    mul_le_mul_of_nonpos_left hlog_yx ht_neg_nonpos
  have hx_eq :
      Complex.realPhase_integerIncrement φ x =
        -t * Real.log ((((x + 1 : ℕ) : ℝ)) / (((x : ℕ) : ℝ))) :=
    Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase_integerIncrement_eq_neg_mul_log_ratio
      t hx_pos
  have hy_bounds : c ≤ y ∧ y < b :=
    Finset.mem_Ico.mp hy
  have hy_pos : 0 < y :=
    lt_of_lt_of_le hc_pos hy_bounds.1
  have hy_eq :
      Complex.realPhase_integerIncrement φ y =
        -t * Real.log ((((y + 1 : ℕ) : ℝ)) / (((y : ℕ) : ℝ))) :=
    Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase_integerIncrement_eq_neg_mul_log_ratio
      t hy_pos
  exact
    Eq.subst
      (motive := fun left : ℝ =>
        left ≤ Complex.realPhase_integerIncrement φ y)
      hx_eq.symm
      (Eq.subst
        (motive := fun right : ℝ =>
          -t * Real.log ((((x + 1 : ℕ) : ℝ)) / (((x : ℕ) : ℝ))) ≤ right)
        hy_eq.symm
        hscaled)

/-- The raw adjacent increments are monotone on the zero terminal packet. -/
theorem Complex.logarithmicPhaseRealPhase_zeroDerivPacket_terminal_integerIncrementMonotoneOn
    (t : ℝ)
    (ht_nonneg : 0 ≤ t)
    {a b : ℕ}
    (ha : 1 ≤ a)
    (hp :
      (Complex.realPhase_secondDerivative_vdc_derivPacket
        (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
        a b 0).Nonempty) :
    Complex.realPhase_integerIncrementMonotoneOn
      (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
      ((Complex.realPhase_secondDerivative_vdc_derivPacket
        (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
        a b 0).min' hp)
      b :=
  Or.inl
    (Complex.logarithmicPhaseRealPhase_zeroDerivPacket_terminal_integerIncrement_monotoneOn
      t ht_nonneg ha hp)

/-- The reduced adjacent increments are monotone on the zero terminal packet. -/
theorem Complex.logarithmicPhaseRealPhase_zeroDerivPacket_terminal_reducedIntegerIncrementMonotoneOn
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    (ht_nonneg : 0 ≤ t)
    {a b : ℕ}
    (ha : 1 ≤ a)
    (hp :
      (Complex.realPhase_secondDerivative_vdc_derivPacket
        (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
        a b 0).Nonempty) :
    Complex.realPhase_reducedIntegerIncrementMonotoneOn
      (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
      ((Complex.realPhase_secondDerivative_vdc_derivPacket
        (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
        a b 0).min' hp)
      b := by
  let φ : ℝ → ℝ :=
    Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t
  let packet : Finset ℕ :=
    Complex.realPhase_secondDerivative_vdc_derivPacket φ a b 0
  let c : ℕ := packet.min' hp
  have hraw :
      MonotoneOn
        (fun n : ℕ => Complex.realPhase_integerIncrement φ n)
        (Finset.Ico c b : Set ℕ) :=
    Complex.logarithmicPhaseRealPhase_zeroDerivPacket_terminal_integerIncrement_monotoneOn
      t ht_nonneg ha hp
  have hmono :
      MonotoneOn
        (fun n : ℕ => Complex.realPhase_reducedIntegerIncrement φ n)
        (Finset.Ico c b : Set ℕ) := by
    intro x hx y hy hxy
    have hx_eq :
        Complex.realPhase_reducedIntegerIncrement φ x =
          Complex.realPhase_integerIncrement φ x :=
      Complex.logarithmicPhaseRealPhase_zeroDerivPacket_terminal_reducedIncrement_eq
        t ht ht_nonneg ha hp hx
    have hy_eq :
        Complex.realPhase_reducedIntegerIncrement φ y =
          Complex.realPhase_integerIncrement φ y :=
      Complex.logarithmicPhaseRealPhase_zeroDerivPacket_terminal_reducedIncrement_eq
        t ht ht_nonneg ha hp hy
    have hxy_raw :
        Complex.realPhase_integerIncrement φ x ≤
          Complex.realPhase_integerIncrement φ y :=
      hraw hx hy hxy
    exact
      Eq.subst
        (motive := fun left : ℝ =>
          left ≤ Complex.realPhase_reducedIntegerIncrement φ y)
        hx_eq.symm
        (Eq.subst
          (motive := fun right : ℝ =>
            Complex.realPhase_integerIncrement φ x ≤ right)
          hy_eq.symm
          hxy_raw)
  exact Or.inl hmono


end

end LFunctions
end Boundary
