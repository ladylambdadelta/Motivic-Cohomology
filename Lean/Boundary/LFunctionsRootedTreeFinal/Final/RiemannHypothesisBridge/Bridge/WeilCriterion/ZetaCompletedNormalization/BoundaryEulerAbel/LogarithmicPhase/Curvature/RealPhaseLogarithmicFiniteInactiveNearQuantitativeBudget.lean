import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalization.BoundaryEulerAbel.LogarithmicPhase.Curvature.RealPhaseLogarithmicFiniteInactiveNearModeGeometry

/-!
# Sharp quantitative budgets for near finite inactive packets

Unlike the canonical packet, the quantitative packet has a combined crossing
cost of exactly `2/3`.  The outward clipped tail vanishes on each near family,
leaving one inward tail and a central interval of length at most twice the
balanced radius.
-/

namespace Boundary
namespace LFunctions

noncomputable section

def Complex.logarithmicPhaseFiniteInactiveNearQuantitativePacketBudget
    (t : ℝ) (a b m : ℤ) : ℝ :=
  2 / 3 +
    Complex.logarithmicPhaseBProcessClippedLeftTailBudget t a m +
      2 * Complex.logarithmicPhaseBProcessRadius t m +
        Complex.logarithmicPhaseBProcessClippedRightTailBudget t b m

def Complex.logarithmicPhaseFiniteLeftNearQuantitativeBudget
    (t : ℝ) (a b : ℤ) : ℝ :=
  ∑ m ∈ Complex.logarithmicPhaseFiniteLeftNearEndpointModes t a b,
    Complex.logarithmicPhaseFiniteInactiveNearQuantitativePacketBudget t a b m

def Complex.logarithmicPhaseFiniteRightNearQuantitativeBudget
    (t : ℝ) (a b : ℤ) : ℝ :=
  ∑ m ∈ Complex.logarithmicPhaseFiniteRightNearEndpointModes t a b,
    Complex.logarithmicPhaseFiniteInactiveNearQuantitativePacketBudget t a b m

def Complex.logarithmicPhaseFiniteNearQuantitativeBudget
    (t : ℝ) (a b : ℤ) : ℝ :=
  Complex.logarithmicPhaseFiniteLeftNearQuantitativeBudget t a b +
    Complex.logarithmicPhaseFiniteRightNearQuantitativeBudget t a b

theorem Complex.norm_logarithmicPhaseQuantitativeFiniteLeftNearPacket_at_norm_le_sharpBudget
    (t : ℝ) (ht : 1 ≤ ‖t‖)
    (a b m : ℤ) (ha : 1 ≤ a) (hab : a ≤ b)
    (hm : m ∈ Complex.logarithmicPhaseFiniteLeftNearEndpointModes ‖t‖ a b) :
    ‖Complex.logarithmicPhaseQuantitativeBlockFourierPacket ‖t‖ a b m‖ ≤
      Complex.logarithmicPhaseFiniteInactiveNearQuantitativePacketBudget
        ‖t‖ a b m := by
  have hnormNonneg : 0 ≤ ‖t‖ := norm_nonneg t
  have hnormNorm : ‖‖t‖‖ = ‖t‖ :=
    Real.norm_of_nonneg hnormNonneg
  have htNorm : 1 ≤ ‖‖t‖‖ :=
    Eq.subst (motive := fun parameterNorm : ℝ => 1 ≤ parameterNorm)
      hnormNorm.symm ht
  have hbase :=
    (Complex.mem_logarithmicPhaseFiniteLeftNearEndpointModes_iff
      ‖t‖ a b m).mp hm
  have hmNeg :=
    ((Complex.mem_logarithmicPhasePoissonLeftInactiveModes_iff
      ‖t‖ a b m).mp hbase.1).2.1
  have horder :=
    Complex.logarithmicPhaseFiniteLeftNear_clippedWindow_order
      ‖t‖ htNorm a b hab hm
  have hprincipal :=
    Complex.norm_logarithmicPhaseBProcessUniversalPrincipal_le
      ‖t‖ htNorm hnormNonneg a b m ha hab hmNeg horder
  unfold Complex.logarithmicPhaseFiniteInactiveNearQuantitativePacketBudget
  have hbound :=
    Complex.norm_logarithmicPhaseQuantitativePacket_le_crossings_add_principal
      ‖t‖ a b m ha hab hprincipal
  have hreassociate :
      (2 / 3 : ℝ) +
          ((Complex.logarithmicPhaseBProcessClippedLeftTailBudget
                ‖t‖ a m +
              2 * Complex.logarithmicPhaseBProcessRadius ‖t‖ m) +
            Complex.logarithmicPhaseBProcessClippedRightTailBudget
              ‖t‖ b m) =
        ((2 / 3 +
              Complex.logarithmicPhaseBProcessClippedLeftTailBudget
                ‖t‖ a m) +
            2 * Complex.logarithmicPhaseBProcessRadius ‖t‖ m) +
          Complex.logarithmicPhaseBProcessClippedRightTailBudget
            ‖t‖ b m :=
    Real.add_reassociate_four_left _ _ _ _
  exact Eq.subst
    (motive := fun value : ℝ =>
      ‖Complex.logarithmicPhaseQuantitativeBlockFourierPacket
          ‖t‖ a b m‖ ≤ value)
    hreassociate hbound

theorem Complex.norm_logarithmicPhaseQuantitativeFiniteLeftNearPacket_le_sharpBudget
    (t : ℝ) (ht : 1 ≤ ‖t‖) (ht_nonneg : 0 ≤ t)
    (a b m : ℤ) (ha : 1 ≤ a) (hab : a ≤ b)
    (hm : m ∈ Complex.logarithmicPhaseFiniteLeftNearEndpointModes t a b) :
    ‖Complex.logarithmicPhaseQuantitativeBlockFourierPacket t a b m‖ ≤
      Complex.logarithmicPhaseFiniteInactiveNearQuantitativePacketBudget
        t a b m := by
  have hnorm : ‖t‖ = t :=
    Real.norm_of_nonneg ht_nonneg
  have hmAtNorm :
      m ∈ Complex.logarithmicPhaseFiniteLeftNearEndpointModes ‖t‖ a b :=
    Eq.subst
      (motive := fun parameter : ℝ =>
        m ∈ Complex.logarithmicPhaseFiniteLeftNearEndpointModes parameter a b)
      hnorm.symm hm
  have hcanonical :=
    Complex.norm_logarithmicPhaseQuantitativeFiniteLeftNearPacket_at_norm_le_sharpBudget
      t ht a b m ha hab hmAtNorm
  exact Eq.subst
    (motive := fun parameter : ℝ =>
      ‖Complex.logarithmicPhaseQuantitativeBlockFourierPacket
          parameter a b m‖ ≤
        Complex.logarithmicPhaseFiniteInactiveNearQuantitativePacketBudget
          parameter a b m)
    hnorm hcanonical

theorem Complex.norm_logarithmicPhaseQuantitativeFiniteRightNearPacket_at_norm_le_sharpBudget
    (t : ℝ) (ht : 1 ≤ ‖t‖)
    (a b m : ℤ) (ha : 1 ≤ a) (hab : a ≤ b)
    (hm : m ∈ Complex.logarithmicPhaseFiniteRightNearEndpointModes ‖t‖ a b) :
    ‖Complex.logarithmicPhaseQuantitativeBlockFourierPacket ‖t‖ a b m‖ ≤
      Complex.logarithmicPhaseFiniteInactiveNearQuantitativePacketBudget
        ‖t‖ a b m := by
  have hnormNonneg : 0 ≤ ‖t‖ := norm_nonneg t
  have hnormNorm : ‖‖t‖‖ = ‖t‖ :=
    Real.norm_of_nonneg hnormNonneg
  have htNorm : 1 ≤ ‖‖t‖‖ :=
    Eq.subst (motive := fun parameterNorm : ℝ => 1 ≤ parameterNorm)
      hnormNorm.symm ht
  have hbase :=
    (Complex.mem_logarithmicPhaseFiniteRightNearEndpointModes_iff
      ‖t‖ a b m).mp hm
  have hmNeg :=
    ((Complex.mem_logarithmicPhasePoissonRightInactiveModes_iff
      ‖t‖ a b m).mp hbase.1).2.1
  have horder :=
    Complex.logarithmicPhaseFiniteRightNear_clippedWindow_order
      ‖t‖ htNorm a b hab hm
  have hprincipal :=
    Complex.norm_logarithmicPhaseBProcessUniversalPrincipal_le
      ‖t‖ htNorm hnormNonneg a b m ha hab hmNeg horder
  unfold Complex.logarithmicPhaseFiniteInactiveNearQuantitativePacketBudget
  have hbound :=
    Complex.norm_logarithmicPhaseQuantitativePacket_le_crossings_add_principal
      ‖t‖ a b m ha hab hprincipal
  have hreassociate :
      (2 / 3 : ℝ) +
          ((Complex.logarithmicPhaseBProcessClippedLeftTailBudget
                ‖t‖ a m +
              2 * Complex.logarithmicPhaseBProcessRadius ‖t‖ m) +
            Complex.logarithmicPhaseBProcessClippedRightTailBudget
              ‖t‖ b m) =
        ((2 / 3 +
              Complex.logarithmicPhaseBProcessClippedLeftTailBudget
                ‖t‖ a m) +
            2 * Complex.logarithmicPhaseBProcessRadius ‖t‖ m) +
          Complex.logarithmicPhaseBProcessClippedRightTailBudget
            ‖t‖ b m :=
    Real.add_reassociate_four_left _ _ _ _
  exact Eq.subst
    (motive := fun value : ℝ =>
      ‖Complex.logarithmicPhaseQuantitativeBlockFourierPacket
          ‖t‖ a b m‖ ≤ value)
    hreassociate hbound

theorem Complex.norm_logarithmicPhaseQuantitativeFiniteRightNearPacket_le_sharpBudget
    (t : ℝ) (ht : 1 ≤ ‖t‖) (ht_nonneg : 0 ≤ t)
    (a b m : ℤ) (ha : 1 ≤ a) (hab : a ≤ b)
    (hm : m ∈ Complex.logarithmicPhaseFiniteRightNearEndpointModes t a b) :
    ‖Complex.logarithmicPhaseQuantitativeBlockFourierPacket t a b m‖ ≤
      Complex.logarithmicPhaseFiniteInactiveNearQuantitativePacketBudget
        t a b m := by
  have hnorm : ‖t‖ = t :=
    Real.norm_of_nonneg ht_nonneg
  have hmAtNorm :
      m ∈ Complex.logarithmicPhaseFiniteRightNearEndpointModes ‖t‖ a b :=
    Eq.subst
      (motive := fun parameter : ℝ =>
        m ∈ Complex.logarithmicPhaseFiniteRightNearEndpointModes parameter a b)
      hnorm.symm hm
  have hcanonical :=
    Complex.norm_logarithmicPhaseQuantitativeFiniteRightNearPacket_at_norm_le_sharpBudget
      t ht a b m ha hab hmAtNorm
  exact Eq.subst
    (motive := fun parameter : ℝ =>
      ‖Complex.logarithmicPhaseQuantitativeBlockFourierPacket
          parameter a b m‖ ≤
        Complex.logarithmicPhaseFiniteInactiveNearQuantitativePacketBudget
          parameter a b m)
    hnorm hcanonical

theorem Complex.logarithmicPhaseFiniteLeftNear_clippedLeftTail_eq_zero
    {t : ℝ} {a b : ℕ} {m : ℤ}
    (ht : 1 ≤ ‖t‖)
    (hm : m ∈ Complex.logarithmicPhaseFiniteLeftNearEndpointModes
      t (a : ℤ) (b : ℤ)) :
    Complex.logarithmicPhaseBProcessClippedLeftTailBudget t (a : ℤ) m = 0 := by
  have hbase :=
    (Complex.mem_logarithmicPhaseFiniteLeftNearEndpointModes_iff
      t (a : ℤ) (b : ℤ) m).mp hm
  have hcenter :=
    ((Complex.mem_logarithmicPhasePoissonLeftInactiveModes_iff
      t (a : ℤ) (b : ℤ) m).mp hbase.1).2.2
  have hmNeg :=
    ((Complex.mem_logarithmicPhasePoissonLeftInactiveModes_iff
      t (a : ℤ) (b : ℤ) m).mp hbase.1).2.1
  have hwindow : Complex.logarithmicPhaseBProcessWindowLeft t m < (a : ℝ) := by
    unfold Complex.logarithmicPhaseBProcessWindowLeft
    exact lt_of_le_of_lt (sub_le_self _
      (Complex.logarithmicPhaseBProcessRadius_nonneg t ht hmNeg)) hcenter
  unfold Complex.logarithmicPhaseBProcessClippedLeftTailBudget
  exact if_neg (not_le_of_gt hwindow)

theorem Complex.logarithmicPhaseFiniteRightNear_clippedRightTail_eq_zero
    {t : ℝ} {a b : ℕ} {m : ℤ}
    (ht : 1 ≤ ‖t‖)
    (hm : m ∈ Complex.logarithmicPhaseFiniteRightNearEndpointModes
      t (a : ℤ) (b : ℤ)) :
    Complex.logarithmicPhaseBProcessClippedRightTailBudget t (b : ℤ) m = 0 := by
  have hbase :=
    (Complex.mem_logarithmicPhaseFiniteRightNearEndpointModes_iff
      t (a : ℤ) (b : ℤ) m).mp hm
  have hcenter :=
    ((Complex.mem_logarithmicPhasePoissonRightInactiveModes_iff
      t (a : ℤ) (b : ℤ) m).mp hbase.1).2.2
  have hmNeg :=
    ((Complex.mem_logarithmicPhasePoissonRightInactiveModes_iff
      t (a : ℤ) (b : ℤ) m).mp hbase.1).2.1
  have hwindow : (b : ℝ) <
      Complex.logarithmicPhaseBProcessWindowRight t m := by
    unfold Complex.logarithmicPhaseBProcessWindowRight
    exact lt_of_lt_of_le hcenter
      (le_add_of_nonneg_right
        (Complex.logarithmicPhaseBProcessRadius_nonneg t ht hmNeg))
  unfold Complex.logarithmicPhaseBProcessClippedRightTailBudget
  exact if_neg (not_le_of_gt hwindow)

theorem Complex.logarithmicPhaseFiniteNear_radius_le_scale_div_six
    {t : ℝ} {m : ℤ}
    (hm : m < 0) :
    Complex.logarithmicPhaseBProcessRadius t m ≤
      Complex.logarithmicPhaseBProcessScale t / 6 := by
  unfold Complex.logarithmicPhaseBProcessRadius
  have hcenter :=
    Complex.logarithmicPhaseFourierStationaryPoint_le_norm_div_six t hm
  have hscalePos := Complex.logarithmicPhaseBProcessScale_pos t
  have hdivision := div_le_div_of_nonneg_right hcenter hscalePos.le
  have hnormScale :=
    Complex.logarithmicPhaseBProcess_norm_div_scale_le_scale t
  have hscaled := div_le_div_of_nonneg_right hnormScale (Nat.cast_nonneg 6)
  have hnormalize :
      (‖t‖ / 6) / Complex.logarithmicPhaseBProcessScale t =
        (‖t‖ / Complex.logarithmicPhaseBProcessScale t) / 6 := by
    exact Eq.trans
      (div_div ‖t‖ 6 (Complex.logarithmicPhaseBProcessScale t))
      (Eq.trans
        (congrArg (fun denominator : ℝ => ‖t‖ / denominator)
          (mul_comm 6 (Complex.logarithmicPhaseBProcessScale t)))
        (div_div ‖t‖
          (Complex.logarithmicPhaseBProcessScale t) 6).symm)
  have hdivisionNormalized :
      Complex.logarithmicPhaseFourierStationaryPoint t m /
          Complex.logarithmicPhaseBProcessScale t ≤
        (‖t‖ / Complex.logarithmicPhaseBProcessScale t) / 6 :=
    Eq.subst
      (motive := fun value : ℝ =>
        Complex.logarithmicPhaseFourierStationaryPoint t m /
            Complex.logarithmicPhaseBProcessScale t ≤ value)
      hnormalize hdivision
  exact le_trans hdivisionNormalized hscaled

theorem Complex.logarithmicPhaseFiniteNear_crossing_le_two_thirds_scale
    (t : ℝ) :
    (2 / 3 : ℝ) ≤
      (2 / 3) * Complex.logarithmicPhaseBProcessScale t := by
  have hone := Complex.logarithmicPhaseBProcessScale_one_le t
  have hscaled := mul_le_mul_of_nonneg_left hone
    (div_nonneg (Nat.cast_nonneg 2) (Nat.cast_nonneg 3))
  exact Eq.subst (motive := fun value : ℝ => value ≤ _)
    (mul_one (2 / 3 : ℝ)) hscaled

theorem Complex.logarithmicPhaseFiniteNear_two_radius_le_one_third_scale
    {t : ℝ} {m : ℤ} (hm : m < 0) :
    2 * Complex.logarithmicPhaseBProcessRadius t m ≤
      (1 / 3 : ℝ) * Complex.logarithmicPhaseBProcessScale t := by
  have hradius :=
    Complex.logarithmicPhaseFiniteNear_radius_le_scale_div_six
      (t := t) hm
  have hscaled := mul_le_mul_of_nonneg_left hradius (Nat.cast_nonneg 2)
  have hnormalize :
      2 * (Complex.logarithmicPhaseBProcessScale t / 6) =
        (1 / 3 : ℝ) * Complex.logarithmicPhaseBProcessScale t := by
    have hsixNe : (6 : ℝ) ≠ 0 :=
      ne_of_gt (Nat.cast_pos.mpr (Nat.succ_pos 5))
    have hthreeNe : (3 : ℝ) ≠ 0 :=
      ne_of_gt (Nat.cast_pos.mpr (Nat.succ_pos 2))
    have hleftProduct : (2 : ℝ) * 3 = 6 :=
      Real.endpoint_nat_cast_mul 2 3 6 rfl
    have hcrossProduct : (2 : ℝ) * 3 = 1 * 6 :=
      Eq.trans hleftProduct (one_mul (6 : ℝ)).symm
    have hcoefficient : (2 / 6 : ℝ) = 1 / 3 :=
      (div_eq_div_iff hsixNe hthreeNe).mpr hcrossProduct
    calc
      (2 : ℝ) * (Complex.logarithmicPhaseBProcessScale t / 6) =
          (2 * Complex.logarithmicPhaseBProcessScale t) / 6 :=
        (mul_div_assoc (2 : ℝ)
          (Complex.logarithmicPhaseBProcessScale t) 6).symm
      _ = (2 / 6 : ℝ) * Complex.logarithmicPhaseBProcessScale t :=
        (div_mul_eq_mul_div 2 6
          (Complex.logarithmicPhaseBProcessScale t)).symm
      _ = (1 / 3 : ℝ) * Complex.logarithmicPhaseBProcessScale t :=
        congrArg
          (fun coefficient : ℝ =>
            coefficient * Complex.logarithmicPhaseBProcessScale t)
          hcoefficient
  exact le_trans hscaled (le_of_eq hnormalize)

end

end LFunctions
end Boundary
